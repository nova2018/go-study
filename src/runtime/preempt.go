// Copyright 2019 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Goroutine preemption
//
// A goroutine can be preempted at any safe-point. Currently, there
// are a few categories of safe-points:
//
// 1. A blocked safe-point occurs for the duration that a goroutine is
//    descheduled, blocked on synchronization, or in a system call.
//
// 2. Synchronous safe-points occur when a running goroutine checks
//    for a preemption request.
//
// 3. Asynchronous safe-points occur at any instruction in user code
//    where the goroutine can be safely paused and a conservative
//    stack and register scan can find stack roots. The runtime can
//    stop a goroutine at an async safe-point using a signal.
//
// At both blocked and synchronous safe-points, a goroutine's CPU
// state is minimal and the garbage collector has complete information
// about its entire stack. This makes it possible to deschedule a
// goroutine with minimal space, and to precisely scan a goroutine's
// stack.
//
// Synchronous safe-points are implemented by overloading the stack
// bound check in function prologues. To preempt a goroutine at the
// next synchronous safe-point, the runtime poisons the goroutine's
// stack bound to a value that will cause the next stack bound check
// to fail and enter the stack growth implementation, which will
// detect that it was actually a preemption and redirect to preemption
// handling.
//
// Preemption at asynchronous safe-points is implemented by suspending
// the thread using an OS mechanism (e.g., signals) and inspecting its
// state to determine if the goroutine was at an asynchronous
// safe-point. Since the thread suspension itself is generally
// asynchronous, it also checks if the running goroutine wants to be
// preempted, since this could have changed. If all conditions are
// satisfied, it adjusts the signal context to make it look like the
// signaled thread just called asyncPreempt and resumes the thread.
// asyncPreempt spills all registers and enters the scheduler.
//
// (An alternative would be to preempt in the signal handler itself.
// This would let the OS save and restore the register state and the
// runtime would only need to know how to extract potentially
// pointer-containing registers from the signal context. However, this
// would consume an M for every preempted G, and the scheduler itself
// is not designed to run from a signal handler, as it tends to
// allocate memory and start threads in the preemption path.)

package runtime

import (
	"internal/abi"
	"internal/goarch"
)

type suspendGState struct {
	g *g

	// dead indicates the goroutine was not suspended because it
	// is dead. This goroutine could be reused after the dead
	// state was observed, so the caller must not assume that it
	// remains dead.
	dead bool

	// stopped indicates that this suspendG transitioned the G to
	// _Gwaiting via g.preemptStop and thus is responsible for
	// readying it when done.
	stopped bool
}

// suspendG suspends goroutine gp at a safe-point and returns the
// state of the suspended goroutine. The caller gets read access to
// the goroutine until it calls resumeG.
// 译：suspendG将goroutine gp挂起在一个安全点，并返回挂起的goroutine的状态。
// 译：调用方获得对goroutine的读取访问权限，直到调用resumeG为止。
//
// It is safe for multiple callers to attempt to suspend the same
// goroutine at the same time. The goroutine may execute between
// subsequent successful suspend operations. The current
// implementation grants exclusive access to the goroutine, and hence
// multiple callers will serialize. However, the intent is to grant
// shared read access, so please don't depend on exclusive access.
// 译：多个调用方尝试同时挂起同一个goroutine是安全的。
// 译：goroutine可以在后续成功的挂起操作之间执行。
// 译：当前实现授予对goroutine的独占访问权限，因此多个调用方将进行序列化。
// 译：但是，其目的是授予共享读取访问权限，因此请不要依赖于独占访问。
//
// This must be called from the system stack and the user goroutine on
// the current M (if any) must be in a preemptible state. This
// prevents deadlocks where two goroutines attempt to suspend each
// other and both are in non-preemptible states. There are other ways
// to resolve this deadlock, but this seems simplest.
// 译：这必须从系统堆栈调用，并且当前M上的用户goroutine（如果有的话）必须处于可抢占状态。
// 译：这可以防止两个goroutine试图挂起对方并且都处于不可抢占状态的死锁。
// 译：还有其他方法可以解决这个僵局，但这似乎是最简单的。
//
// TODO(austin): What if we instead required this to be called from a
// user goroutine? Then we could deschedule the goroutine while
// waiting instead of blocking the thread. If two goroutines tried to
// suspend each other, one of them would win and the other wouldn't
// complete the suspend until it was resumed. We would have to be
// careful that they couldn't actually queue up suspend for each other
// and then both be suspended. This would also avoid the need for a
// kernel context switch in the synchronous case because we could just
// directly schedule the waiter. The context switch is unavoidable in
// the signal case.
// 译：TODO（austin）：如果我们要求从用户goroutine调用它呢？
// 译：然后我们可以在等待时取消goroutine的调度，而不是阻塞线程。
// 译：如果两个goroutines试图暂停对方，其中一个会赢，另一个在恢复之前不会完成暂停。
// 译：我们必须小心，他们不能真正排队为对方暂停，然后两者都被暂停。
// 译：这也将避免在同步情况下需要内核上下文切换，因为我们可以直接调度服务生。
// 译：上下文切换在信号情况下是不可避免的。
//
//go:systemstack
func suspendG(gp *g) suspendGState {
	if mp := getg().m; mp.curg != nil && readgstatus(mp.curg) == _Grunning {
		// 注：如果当前g存在，那么当前g的状态必须不能是_Grunning

		// Since we're on the system stack of this M, the user
		// G is stuck at an unsafe point. If another goroutine
		// were to try to preempt m.curg, it could deadlock.
		throw("suspendG from non-preemptible goroutine")
	}

	// See https://golang.org/cl/21503 for justification of the yield delay.
	const yieldDelay = 10 * 1000
	var nextYield int64

	// Drive the goroutine to a preemption point.
	stopped := false
	var asyncM *m
	var asyncGen uint32
	var nextPreemptM int64
	for i := 0; ; i++ {
		switch s := readgstatus(gp); s {
		default:
			if s&_Gscan != 0 {
				// Someone else is suspending it. Wait
				// for them to finish.
				//
				// TODO: It would be nicer if we could
				// coalesce suspends.
				break
			}

			dumpgstatus(gp)
			throw("invalid g status")

		case _Gdead: // 注：g已被释放/空闲
			// Nothing to suspend.
			//
			// preemptStop may need to be cleared, but
			// doing that here could race with goroutine
			// reuse. Instead, goexit0 clears it.
			return suspendGState{dead: true}

		case _Gcopystack: // 注：栈正在被复制
			// The stack is being copied. We need to wait
			// until this is done.

		case _Gpreempted: // 注：g被抢占
			// We (or someone else) suspended the G. Claim
			// ownership of it by transitioning it to
			// _Gwaiting.
			// 译：我们（或其他人）暂停了G.通过将其转换为_Gwaiting来声明其所有权。
			if !casGFromPreempted(gp, _Gpreempted, _Gwaiting) { // 注：修改g的状态 _Gpreempted -> _Gwaiting
				break
			}

			// We stopped the G, so we have to ready it later.
			// 译：我们停止了G，所以我们必须稍后准备。
			stopped = true

			s = _Gwaiting // 注：转为_Gwaiting然后走_Gwaiting的流程
			fallthrough

		case _Grunnable, _Gsyscall, _Gwaiting: // 注：当前未执行的g
			// Claim goroutine by setting scan bit.
			// This may race with execution or readying of gp.
			// The scan bit keeps it from transition state.
			if !castogscanstatus(gp, s, s|_Gscan) { // 注：增加扫描状态 _Gscan
				break
			}

			// Clear the preemption request. It's safe to
			// reset the stack guard because we hold the
			// _Gscan bit and thus own the stack.
			gp.preemptStop = false
			gp.preempt = false
			gp.stackguard0 = gp.stack.lo + _StackGuard

			// The goroutine was already at a safe-point
			// and we've now locked that in.
			// 译：goroutine已经处于安全点，我们现在已经锁定了它。
			//
			// TODO: It would be much better if we didn't
			// leave it in _Gscan, but instead gently
			// prevented its scheduling until resumption.
			// Maybe we only use this to bump a suspended
			// count and the scheduler skips suspended
			// goroutines? That wouldn't be enough for
			// {_Gsyscall,_Gwaiting} -> _Grunning. Maybe
			// for all those transitions we need to check
			// suspended and deschedule?
			// 译：TODO:如果我们不把它留在_Gscan中，而是温和地阻止它的调度，直到恢复，那会更好。
			// 译：也许我们只使用它来提升挂起的计数，而调度器则跳过挂起的goroutines？
			// 译：这对于{_Gsyscall，_Gwaiting}->_Grunning来说还不够。
			// 译：也许对于所有这些转换，我们需要检查暂停和取消计划？
			return suspendGState{g: gp, stopped: stopped}

		case _Grunning: // 注：当前运行中的g
			// Optimization: if there is already a pending preemption request
			// (from the previous loop iteration), don't bother with the atomics.
			// 译：优化：如果已经存在挂起的抢占请求（来自上一次循环迭代），不要为原子性而烦恼。
			if gp.preemptStop && gp.preempt && gp.stackguard0 == stackPreempt && asyncM == gp.m && asyncM.preemptGen.Load() == asyncGen {
				break
			}

			// Temporarily block state transitions.
			if !castogscanstatus(gp, _Grunning, _Gscanrunning) { // 注：切换至_Gscanrunning，同时加锁
				break
			}

			// Request synchronous preemption.
			// 译：请求同步抢占。
			gp.preemptStop = true
			gp.preempt = true
			gp.stackguard0 = stackPreempt

			// Prepare for asynchronous preemption.
			// 译：准备异步抢占。
			asyncM2 := gp.m
			asyncGen2 := asyncM2.preemptGen.Load()
			needAsync := asyncM != asyncM2 || asyncGen != asyncGen2
			asyncM = asyncM2
			asyncGen = asyncGen2

			casfrom_Gscanstatus(gp, _Gscanrunning, _Grunning) // 注：切换至_Grunning，同时释放锁

			// Send asynchronous preemption. We do this
			// after CASing the G back to _Grunning
			// because preemptM may be synchronous and we
			// don't want to catch the G just spinning on
			// its status.
			// 译：发送异步抢占。我们在将G CASing返回_Grunning之后这样做，
			// 译：因为preemptM可能是同步的，并且我们不想捕捉到G只是在其状态上旋转。
			if preemptMSupported && debug.asyncpreemptoff == 0 && needAsync {
				// Rate limit preemptM calls. This is
				// particularly important on Windows
				// where preemptM is actually
				// synchronous and the spin loop here
				// can lead to live-lock.
				// 译：速率限制抢占M个呼叫。这在Windows上尤其重要，
				// 译：因为preemptM实际上是同步的，这里的旋转循环可能导致实时锁定。
				now := nanotime()
				if now >= nextPreemptM {
					nextPreemptM = now + yieldDelay/2
					preemptM(asyncM)
				}
			}
		}

		// TODO: Don't busy wait. This loop should really only
		// be a simple read/decide/CAS loop that only fails if
		// there's an active race. Once the CAS succeeds, we
		// should queue up the preemption (which will require
		// it to be reliable in the _Grunning case, not
		// best-effort) and then sleep until we're notified
		// that the goroutine is suspended.
		if i == 0 {
			nextYield = nanotime() + yieldDelay
		}
		if nanotime() < nextYield {
			procyield(10)
		} else {
			osyield()
			nextYield = nanotime() + yieldDelay/2
		}
	}
}

// resumeG undoes the effects of suspendG, allowing the suspended
// goroutine to continue from its current safe-point.
func resumeG(state suspendGState) {
	if state.dead {
		// We didn't actually stop anything.
		return
	}

	gp := state.g
	switch s := readgstatus(gp); s {
	default:
		dumpgstatus(gp)
		throw("unexpected g status")

	case _Grunnable | _Gscan,
		_Gwaiting | _Gscan,
		_Gsyscall | _Gscan:
		casfrom_Gscanstatus(gp, s, s&^_Gscan)
	}

	if state.stopped {
		// We stopped it, so we need to re-schedule it.
		ready(gp, 0, true)
	}
}

// canPreemptM reports whether mp is in a state that is safe to preempt.
//
// It is nosplit because it has nosplit callers.
//
//go:nosplit
func canPreemptM(mp *m) bool {
	return mp.locks == 0 && mp.mallocing == 0 && mp.preemptoff == "" && mp.p.ptr().status == _Prunning
}

//go:generate go run mkpreempt.go

// asyncPreempt saves all user registers and calls asyncPreempt2.
//
// When stack scanning encounters an asyncPreempt frame, it scans that
// frame and its parent frame conservatively.
//
// asyncPreempt is implemented in assembly.
func asyncPreempt()

//go:nosplit
func asyncPreempt2() {
	gp := getg()
	gp.asyncSafePoint = true
	if gp.preemptStop {
		mcall(preemptPark)
	} else {
		mcall(gopreempt_m)
	}
	gp.asyncSafePoint = false
}

// asyncPreemptStack is the bytes of stack space required to inject an
// asyncPreempt call.
var asyncPreemptStack = ^uintptr(0)

func init() {
	f := findfunc(abi.FuncPCABI0(asyncPreempt))
	total := funcMaxSPDelta(f)
	f = findfunc(abi.FuncPCABIInternal(asyncPreempt2))
	total += funcMaxSPDelta(f)
	// Add some overhead for return PCs, etc.
	asyncPreemptStack = uintptr(total) + 8*goarch.PtrSize
	if asyncPreemptStack > _StackLimit {
		// We need more than the nosplit limit. This isn't
		// unsafe, but it may limit asynchronous preemption.
		//
		// This may be a problem if we start using more
		// registers. In that case, we should store registers
		// in a context object. If we pre-allocate one per P,
		// asyncPreempt can spill just a few registers to the
		// stack, then grab its context object and spill into
		// it. When it enters the runtime, it would allocate a
		// new context for the P.
		print("runtime: asyncPreemptStack=", asyncPreemptStack, "\n")
		throw("async stack too large")
	}
}

// wantAsyncPreempt returns whether an asynchronous preemption is
// queued for gp.
func wantAsyncPreempt(gp *g) bool {
	// Check both the G and the P.
	return (gp.preempt || gp.m.p != 0 && gp.m.p.ptr().preempt) && readgstatus(gp)&^_Gscan == _Grunning
}

// isAsyncSafePoint reports whether gp at instruction PC is an
// asynchronous safe point. This indicates that:
//
// 1. It's safe to suspend gp and conservatively scan its stack and
// registers. There are no potentially hidden pointer values and it's
// not in the middle of an atomic sequence like a write barrier.
//
// 2. gp has enough stack space to inject the asyncPreempt call.
//
// 3. It's generally safe to interact with the runtime, even if we're
// in a signal handler stopped here. For example, there are no runtime
// locks held, so acquiring a runtime lock won't self-deadlock.
//
// In some cases the PC is safe for asynchronous preemption but it
// also needs to adjust the resumption PC. The new PC is returned in
// the second result.
func isAsyncSafePoint(gp *g, pc, sp, lr uintptr) (bool, uintptr) {
	mp := gp.m

	// Only user Gs can have safe-points. We check this first
	// because it's extremely common that we'll catch mp in the
	// scheduler processing this G preemption.
	if mp.curg != gp {
		return false, 0
	}

	// Check M state.
	if mp.p == 0 || !canPreemptM(mp) {
		return false, 0
	}

	// Check stack space.
	if sp < gp.stack.lo || sp-gp.stack.lo < asyncPreemptStack {
		return false, 0
	}

	// Check if PC is an unsafe-point.
	f := findfunc(pc)
	if !f.valid() {
		// Not Go code.
		return false, 0
	}
	if (GOARCH == "mips" || GOARCH == "mipsle" || GOARCH == "mips64" || GOARCH == "mips64le") && lr == pc+8 && funcspdelta(f, pc, nil) == 0 {
		// We probably stopped at a half-executed CALL instruction,
		// where the LR is updated but the PC has not. If we preempt
		// here we'll see a seemingly self-recursive call, which is in
		// fact not.
		// This is normally ok, as we use the return address saved on
		// stack for unwinding, not the LR value. But if this is a
		// call to morestack, we haven't created the frame, and we'll
		// use the LR for unwinding, which will be bad.
		return false, 0
	}
	up, startpc := pcdatavalue2(f, _PCDATA_UnsafePoint, pc)
	if up == _PCDATA_UnsafePointUnsafe {
		// Unsafe-point marked by compiler. This includes
		// atomic sequences (e.g., write barrier) and nosplit
		// functions (except at calls).
		return false, 0
	}
	if fd := funcdata(f, _FUNCDATA_LocalsPointerMaps); fd == nil || f.flag&funcFlag_ASM != 0 {
		// This is assembly code. Don't assume it's well-formed.
		// TODO: Empirically we still need the fd == nil check. Why?
		//
		// TODO: Are there cases that are safe but don't have a
		// locals pointer map, like empty frame functions?
		// It might be possible to preempt any assembly functions
		// except the ones that have funcFlag_SPWRITE set in f.flag.
		return false, 0
	}
	name := funcname(f)
	if inldata := funcdata(f, _FUNCDATA_InlTree); inldata != nil {
		inltree := (*[1 << 20]inlinedCall)(inldata)
		ix := pcdatavalue(f, _PCDATA_InlTreeIndex, pc, nil)
		if ix >= 0 {
			name = funcnameFromNameOff(f, inltree[ix].nameOff)
		}
	}
	if hasPrefix(name, "runtime.") ||
		hasPrefix(name, "runtime/internal/") ||
		hasPrefix(name, "reflect.") {
		// For now we never async preempt the runtime or
		// anything closely tied to the runtime. Known issues
		// include: various points in the scheduler ("don't
		// preempt between here and here"), much of the defer
		// implementation (untyped info on stack), bulk write
		// barriers (write barrier check),
		// reflect.{makeFuncStub,methodValueCall}.
		//
		// TODO(austin): We should improve this, or opt things
		// in incrementally.
		return false, 0
	}
	switch up {
	case _PCDATA_Restart1, _PCDATA_Restart2:
		// Restartable instruction sequence. Back off PC to
		// the start PC.
		if startpc == 0 || startpc > pc || pc-startpc > 20 {
			throw("bad restart PC")
		}
		return true, startpc
	case _PCDATA_RestartAtEntry:
		// Restart from the function entry at resumption.
		return true, f.entry()
	}
	return true, pc
}
