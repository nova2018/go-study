// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector (GC).
//
// The GC runs concurrently with mutator threads, is type accurate (aka precise), allows multiple
// GC thread to run in parallel. It is a concurrent mark and sweep that uses a write barrier. It is
// non-generational and non-compacting. Allocation is done using size segregated per P allocation
// areas to minimize fragmentation while eliminating locks in the common case.
//
// The algorithm decomposes into several steps.
// This is a high level description of the algorithm being used. For an overview of GC a good
// place to start is Richard Jones' gchandbook.org.
//
// The algorithm's intellectual heritage includes Dijkstra's on-the-fly algorithm, see
// Edsger W. Dijkstra, Leslie Lamport, A. J. Martin, C. S. Scholten, and E. F. M. Steffens. 1978.
// On-the-fly garbage collection: an exercise in cooperation. Commun. ACM 21, 11 (November 1978),
// 966-975.
// For journal quality proofs that these steps are complete, correct, and terminate see
// Hudson, R., and Moss, J.E.B. Copying Garbage Collection without stopping the world.
// Concurrency and Computation: Practice and Experience 15(3-5), 2003.
//
// 1. GC performs sweep termination.
//
//    a. Stop the world. This causes all Ps to reach a GC safe-point.
//
//    b. Sweep any unswept spans. There will only be unswept spans if
//    this GC cycle was forced before the expected time.
//
// 2. GC performs the mark phase.
//
//    a. Prepare for the mark phase by setting gcphase to _GCmark
//    (from _GCoff), enabling the write barrier, enabling mutator
//    assists, and enqueueing root mark jobs. No objects may be
//    scanned until all Ps have enabled the write barrier, which is
//    accomplished using STW.
//
//    b. Start the world. From this point, GC work is done by mark
//    workers started by the scheduler and by assists performed as
//    part of allocation. The write barrier shades both the
//    overwritten pointer and the new pointer value for any pointer
//    writes (see mbarrier.go for details). Newly allocated objects
//    are immediately marked black.
//
//    c. GC performs root marking jobs. This includes scanning all
//    stacks, shading all globals, and shading any heap pointers in
//    off-heap runtime data structures. Scanning a stack stops a
//    goroutine, shades any pointers found on its stack, and then
//    resumes the goroutine.
//
//    d. GC drains the work queue of grey objects, scanning each grey
//    object to black and shading all pointers found in the object
//    (which in turn may add those pointers to the work queue).
//
//    e. Because GC work is spread across local caches, GC uses a
//    distributed termination algorithm to detect when there are no
//    more root marking jobs or grey objects (see gcMarkDone). At this
//    point, GC transitions to mark termination.
//
// 3. GC performs mark termination.
//
//    a. Stop the world.
//
//    b. Set gcphase to _GCmarktermination, and disable workers and
//    assists.
//
//    c. Perform housekeeping like flushing mcaches.
//
// 4. GC performs the sweep phase.
//
//    a. Prepare for the sweep phase by setting gcphase to _GCoff,
//    setting up sweep state and disabling the write barrier.
//
//    b. Start the world. From this point on, newly allocated objects
//    are white, and allocating sweeps spans before use if necessary.
//
//    c. GC does concurrent sweeping in the background and in response
//    to allocation. See description below.
//
// 5. When sufficient allocation has taken place, replay the sequence
// starting with 1 above. See discussion of GC rate below.

// Concurrent sweep.
//
// The sweep phase proceeds concurrently with normal program execution.
// The heap is swept span-by-span both lazily (when a goroutine needs another span)
// and concurrently in a background goroutine (this helps programs that are not CPU bound).
// At the end of STW mark termination all spans are marked as "needs sweeping".
//
// The background sweeper goroutine simply sweeps spans one-by-one.
//
// To avoid requesting more OS memory while there are unswept spans, when a
// goroutine needs another span, it first attempts to reclaim that much memory
// by sweeping. When a goroutine needs to allocate a new small-object span, it
// sweeps small-object spans for the same object size until it frees at least
// one object. When a goroutine needs to allocate large-object span from heap,
// it sweeps spans until it frees at least that many pages into heap. There is
// one case where this may not suffice: if a goroutine sweeps and frees two
// nonadjacent one-page spans to the heap, it will allocate a new two-page
// span, but there can still be other one-page unswept spans which could be
// combined into a two-page span.
//
// It's critical to ensure that no operations proceed on unswept spans (that would corrupt
// mark bits in GC bitmap). During GC all mcaches are flushed into the central cache,
// so they are empty. When a goroutine grabs a new span into mcache, it sweeps it.
// When a goroutine explicitly frees an object or sets a finalizer, it ensures that
// the span is swept (either by sweeping it, or by waiting for the concurrent sweep to finish).
// The finalizer goroutine is kicked off only when all spans are swept.
// When the next GC starts, it sweeps all not-yet-swept spans (if any).

// GC rate.
// Next GC is after we've allocated an extra amount of memory proportional to
// the amount already in use. The proportion is controlled by GOGC environment variable
// (100 by default). If GOGC=100 and we're using 4M, we'll GC again when we get to 8M
// (this mark is computed by the gcController.heapGoal method). This keeps the GC cost in
// linear proportion to the allocation cost. Adjusting GOGC just changes the linear constant
// (and also the amount of extra memory used).

// Oblets
//
// In order to prevent long pauses while scanning large objects and to
// improve parallelism, the garbage collector breaks up scan jobs for
// objects larger than maxObletBytes into "oblets" of at most
// maxObletBytes. When scanning encounters the beginning of a large
// object, it scans only the first oblet and enqueues the remaining
// oblets as new scan jobs.

package runtime

import (
	"internal/cpu"
	"runtime/internal/atomic"
	"unsafe"
)

const (
	_DebugGC         = 0
	_ConcurrentSweep = true
	_FinBlockSize    = 4 * 1024

	// debugScanConservative enables debug logging for stack
	// frames that are scanned conservatively.
	debugScanConservative = false

	// sweepMinHeapDistance is a lower bound on the heap distance
	// (in bytes) reserved for concurrent sweeping between GC
	// cycles.
	sweepMinHeapDistance = 1024 * 1024
)

func gcinit() {
	if unsafe.Sizeof(workbuf{}) != _WorkbufSize {
		throw("size of Workbuf is suboptimal")
	}
	// No sweep on the first cycle.
	sweep.active.state.Store(sweepDrainedMask) // 注：第一轮sweep状态

	// Initialize GC pacer state.
	// Use the environment variable GOGC for the initial gcPercent value.
	// Use the environment variable GOMEMLIMIT for the initial memoryLimit value.
	gcController.init(readGOGC(), readGOMEMLIMIT())

	work.startSema = 1
	work.markDoneSema = 1
	lockInit(&work.sweepWaiters.lock, lockRankSweepWaiters)
	lockInit(&work.assistQueue.lock, lockRankAssistQueue)
	lockInit(&work.wbufSpans.lock, lockRankWbufSpans)
}

// gcenable is called after the bulk of the runtime initialization,
// just before we're about to start letting user code run.
// It kicks off the background sweeper goroutine, the background
// scavenger goroutine, and enables GC.
func gcenable() {
	// Kick off sweeping and scavenging.
	c := make(chan int, 2)
	go bgsweep(c)
	go bgscavenge(c)
	<-c
	<-c
	memstats.enablegc = true // now that runtime is initialized, GC is okay
}

// Garbage collector phase.
// Indicates to write barrier and synchronization task to perform.
var gcphase uint32

// The compiler knows about this variable.
// If you change it, you must change builtin/runtime.go, too.
// If you change the first four bytes, you must also change the write
// barrier insertion code.
var writeBarrier struct {
	enabled bool    // compiler emits a check of this before calling write barrier
	pad     [3]byte // compiler uses 32-bit load for "enabled" field
	needed  bool    // whether we need a write barrier for current GC phase
	cgo     bool    // whether we need a write barrier for a cgo check
	alignme uint64  // guarantee alignment so that compiler can use a 32 or 64-bit load
}

// gcBlackenEnabled is 1 if mutator assists and background mark
// workers are allowed to blacken objects. This must only be set when
// gcphase == _GCmark.
// 如果允许Mutator助手和背景标记工作人员将对象变黑，则gcBlackenEnabled为1
// 这必须仅在gcase==_GCmark时设置。
var gcBlackenEnabled uint32

const (
	_GCoff = iota // GC not running; sweeping in background, write barrier disabled
	// GC标记根目录和工作区：分配黑色，启用写屏障
	_GCmark            // GC marking roots and workbufs: allocate black, write barrier ENABLED
	_GCmarktermination // GC mark termination: allocate black, P's help GC, write barrier ENABLED
)

//go:nosplit
func setGCPhase(x uint32) {
	atomic.Store(&gcphase, x)
	writeBarrier.needed = gcphase == _GCmark || gcphase == _GCmarktermination
	writeBarrier.enabled = writeBarrier.needed || writeBarrier.cgo
}

// gcMarkWorkerMode represents the mode that a concurrent mark worker
// should operate in.
// 译：gcMarkWorkerMode表示并发标记工作进程应该在的模式下操作。
//
// Concurrent marking happens through four different mechanisms. One
// is mutator assists, which happen in response to allocations and are
// not scheduled. The other three are variations in the per-P mark
// workers and are distinguished by gcMarkWorkerMode.
// 译：并发标记通过四种不同的机制发生。
// 译：一种是变种人助攻，这是根据分配情况而发生的，并不是计划的。
// 译：其他三个是per-P标记工作进程的变体，由gcMarkWorkerMode区分。
type gcMarkWorkerMode int

const (
	// gcMarkWorkerNotWorker indicates that the next scheduled G is not
	// starting work and the mode should be ignored.
	// 译：gcMarkWorkerNotWorker表示下一个调度的G没有开始工作，应该忽略该模式。
	gcMarkWorkerNotWorker gcMarkWorkerMode = iota

	// gcMarkWorkerDedicatedMode indicates that the P of a mark
	// worker is dedicated to running that mark worker. The mark
	// worker should run without preemption.
	// 译：gcMarkWorkerDedicatedMode表示标记Worker的P专用于运行该标记Worker。
	// 译：标记进程应该在没有抢占的情况下运行。
	gcMarkWorkerDedicatedMode

	// gcMarkWorkerFractionalMode indicates that a P is currently
	// running the "fractional" mark worker. The fractional worker
	// is necessary when GOMAXPROCS*gcBackgroundUtilization is not
	// an integer and using only dedicated workers would result in
	// utilization too far from the target of gcBackgroundUtilization.
	// The fractional worker should run until it is preempted and
	// will be scheduled to pick up the fractional part of
	// GOMAXPROCS*gcBackgroundUtilization.
	// 译：gcMarkWorkerFractionalMode表示P当前正在运行“小数”标记Worker。
	// 译：如果GOMAXPROCS*gcBackgroundUtilization不是整数， 并且仅使用专用工作线程会导致利用率
	// 译：与gcBackgroundUtilization的目标相距太远，则必须使用小数辅助进程。
	// 译：分数工作器应该一直运行，直到它被抢占，并将被调度来获取GOMAXPROCS*gcBackgroundUtilization的分数部分。
	gcMarkWorkerFractionalMode

	// gcMarkWorkerIdleMode indicates that a P is running the mark
	// worker because it has nothing else to do. The idle worker
	// should run until it is preempted and account its time
	// against gcController.idleMarkTime.
	// 译：gcMarkWorkerIdleMode表示P正在运行标记Worker，因为它没有其他事情可做。
	// 译：空闲的工作线程应该运行，直到它被抢占，并根据gcController.idleMarkTime计算它的时间。
	gcMarkWorkerIdleMode
)

// gcMarkWorkerModeStrings are the strings labels of gcMarkWorkerModes
// to use in execution traces.
var gcMarkWorkerModeStrings = [...]string{
	"Not worker",
	"GC (dedicated)",
	"GC (fractional)",
	"GC (idle)",
}

// pollFractionalWorkerExit reports whether a fractional mark worker
// should self-preempt. It assumes it is called from the fractional
// worker.
func pollFractionalWorkerExit() bool {
	// This should be kept in sync with the fractional worker
	// scheduler logic in findRunnableGCWorker.
	now := nanotime()
	delta := now - gcController.markStartTime
	if delta <= 0 {
		return true
	}
	p := getg().m.p.ptr()
	selfTime := p.gcFractionalMarkTime + (now - p.gcMarkWorkerStartTime)
	// Add some slack to the utilization goal so that the
	// fractional worker isn't behind again the instant it exits.
	return float64(selfTime)/float64(delta) > 1.2*gcController.fractionalUtilizationGoal
}

var work workType

type workType struct {
	full  lfstack          // lock-free list of full blocks workbuf
	empty lfstack          // lock-free list of empty blocks workbuf
	pad0  cpu.CacheLinePad // prevents false-sharing between full/empty and nproc/nwait

	wbufSpans struct {
		lock mutex
		// free is a list of spans dedicated to workbufs, but
		// that don't currently contain any workbufs.
		free mSpanList
		// busy is a list of all spans containing workbufs on
		// one of the workbuf lists.
		busy mSpanList
	}

	// Restore 64-bit alignment on 32-bit.
	_ uint32

	// bytesMarked is the number of bytes marked this cycle. This
	// includes bytes blackened in scanned objects, noscan objects
	// that go straight to black, and permagrey objects scanned by
	// markroot during the concurrent scan phase. This is updated
	// atomically during the cycle. Updates may be batched
	// arbitrarily, since the value is only read at the end of the
	// cycle.
	//
	// Because of benign races during marking, this number may not
	// be the exact number of marked bytes, but it should be very
	// close.
	//
	// Put this field here because it needs 64-bit atomic access
	// (and thus 8-byte alignment even on 32-bit architectures).
	bytesMarked uint64

	markrootNext uint32 // next markroot job
	markrootJobs uint32 // number of markroot jobs

	nproc  uint32
	tstart int64
	nwait  uint32

	// Number of roots of various root types. Set by gcMarkRootPrepare.
	//
	// nStackRoots == len(stackRoots), but we have nStackRoots for
	// consistency.
	nDataRoots, nBSSRoots, nSpanRoots, nStackRoots int

	// Base indexes of each root type. Set by gcMarkRootPrepare.
	baseData, baseBSS, baseSpans, baseStacks, baseEnd uint32

	// stackRoots is a snapshot of all of the Gs that existed
	// before the beginning of concurrent marking. The backing
	// store of this must not be modified because it might be
	// shared with allgs.
	stackRoots []*g

	// Each type of GC state transition is protected by a lock.
	// Since multiple threads can simultaneously detect the state
	// transition condition, any thread that detects a transition
	// condition must acquire the appropriate transition lock,
	// re-check the transition condition and return if it no
	// longer holds or perform the transition if it does.
	// Likewise, any transition must invalidate the transition
	// condition before releasing the lock. This ensures that each
	// transition is performed by exactly one thread and threads
	// that need the transition to happen block until it has
	// happened.
	// 译：每种类型的GC状态转换都由锁保护。
	// 译：由于多个线程可以同时检测状态转换条件，因此任何检测到转换条件的线程都必须获取适当的转换锁，
	// 译：重新检查转换条件，如果不再保持，则返回，如果保持，则执行转换。
	// 译：同样，在释放锁之前，任何转换都必须使转换条件无效。
	// 译：这确保每个转换只由一个线程执行，需要转换的线程会阻塞，直到转换发生为止。
	//
	// startSema protects the transition from "off" to mark or
	// mark termination.
	// 译：startSema保护从“关闭”到标记或标记终止的转换。
	startSema uint32 // 初值是1
	// markDoneSema protects transitions from mark to mark termination.
	// 译：markDoneSema保护从标记到标记终止的过渡。
	markDoneSema uint32 // 初值是1

	bgMarkReady note   // 译：信号背景标记工作人员已启动 // signal background mark worker has started
	bgMarkDone  uint32 // cas to 1 when at a background mark completion point
	// Background mark completion signaling

	// mode is the concurrency mode of the current GC cycle.
	mode gcMode

	// userForced indicates the current GC cycle was forced by an
	// explicit user call.
	userForced bool

	// initialHeapLive is the value of gcController.heapLive at the
	// beginning of this GC cycle.
	initialHeapLive uint64

	// assistQueue is a queue of assists that are blocked because
	// there was neither enough credit to steal or enough work to
	// do.
	assistQueue struct {
		lock mutex
		q    gQueue
	}

	// sweepWaiters is a list of blocked goroutines to wake when
	// we transition from mark termination to sweep.
	sweepWaiters struct {
		lock mutex
		list gList
	}

	// cycles is the number of completed GC cycles, where a GC
	// cycle is sweep termination, mark, mark termination, and
	// sweep. This differs from memstats.numgc, which is
	// incremented at mark termination.
	cycles atomic.Uint32

	// Timing/utilization stats for this cycle.
	stwprocs, maxprocs                 int32
	tSweepTerm, tMark, tMarkTerm, tEnd int64 // nanotime() of phase start

	pauseNS    int64 // total STW time this cycle
	pauseStart int64 // nanotime() of last STW

	// debug.gctrace heap sizes for this cycle.
	heap0, heap1, heap2 uint64

	// Cumulative estimated CPU usage.
	cpuStats
}

// GC runs a garbage collection and blocks the caller until the
// garbage collection is complete. It may also block the entire
// program.
func GC() {
	// We consider a cycle to be: sweep termination, mark, mark
	// termination, and sweep. This function shouldn't return
	// until a full cycle has been completed, from beginning to
	// end. Hence, we always want to finish up the current cycle
	// and start a new one. That means:
	//
	// 1. In sweep termination, mark, or mark termination of cycle
	// N, wait until mark termination N completes and transitions
	// to sweep N.
	//
	// 2. In sweep N, help with sweep N.
	//
	// At this point we can begin a full cycle N+1.
	//
	// 3. Trigger cycle N+1 by starting sweep termination N+1.
	//
	// 4. Wait for mark termination N+1 to complete.
	//
	// 5. Help with sweep N+1 until it's done.
	//
	// This all has to be written to deal with the fact that the
	// GC may move ahead on its own. For example, when we block
	// until mark termination N, we may wake up in cycle N+2.

	// Wait until the current sweep termination, mark, and mark
	// termination complete.
	n := work.cycles.Load()
	gcWaitOnMark(n)

	// We're now in sweep N or later. Trigger GC cycle N+1, which
	// will first finish sweep N if necessary and then enter sweep
	// termination N+1.
	gcStart(gcTrigger{kind: gcTriggerCycle, n: n + 1})

	// Wait for mark termination N+1 to complete.
	gcWaitOnMark(n + 1)

	// Finish sweep N+1 before returning. We do this both to
	// complete the cycle and because runtime.GC() is often used
	// as part of tests and benchmarks to get the system into a
	// relatively stable and isolated state.
	for work.cycles.Load() == n+1 && sweepone() != ^uintptr(0) {
		sweep.nbgsweep++
		Gosched()
	}

	// Callers may assume that the heap profile reflects the
	// just-completed cycle when this returns (historically this
	// happened because this was a STW GC), but right now the
	// profile still reflects mark termination N, not N+1.
	//
	// As soon as all of the sweep frees from cycle N+1 are done,
	// we can go ahead and publish the heap profile.
	//
	// First, wait for sweeping to finish. (We know there are no
	// more spans on the sweep queue, but we may be concurrently
	// sweeping spans, so we have to wait.)
	for work.cycles.Load() == n+1 && !isSweepDone() {
		Gosched()
	}

	// Now we're really done with sweeping, so we can publish the
	// stable heap profile. Only do this if we haven't already hit
	// another mark termination.
	mp := acquirem()
	cycle := work.cycles.Load()
	if cycle == n+1 || (gcphase == _GCmark && cycle == n+2) {
		mProf_PostSweep()
	}
	releasem(mp)
}

// gcWaitOnMark blocks until GC finishes the Nth mark phase. If GC has
// already completed this mark phase, it returns immediately.
// 译：gcWaitOnMark阻塞，直到GC完成第N个标记阶段。如果GC已经完成了这个标记阶段，它将立即返回。
func gcWaitOnMark(n uint32) {
	for {
		// Disable phase transitions.
		lock(&work.sweepWaiters.lock)
		nMarks := work.cycles.Load()
		if gcphase != _GCmark {
			// We've already completed this cycle's mark.
			nMarks++
		}
		if nMarks > n {
			// We're done.
			unlock(&work.sweepWaiters.lock)
			return
		}

		// Wait until sweep termination, mark, and mark
		// termination of cycle N complete.
		// 译：等待，直到循环N的扫描终止、标记和标记终止完成。
		work.sweepWaiters.list.push(getg())
		goparkunlock(&work.sweepWaiters.lock, waitReasonWaitForGCCycle, traceEvGoBlock, 1)
	}
}

// gcMode indicates how concurrent a GC cycle should be.
type gcMode int

const (
	gcBackgroundMode gcMode = iota // concurrent GC and sweep
	gcForceMode                    // stop-the-world GC now, concurrent sweep
	gcForceBlockMode               // stop-the-world GC now and STW sweep (forced by user)
)

// A gcTrigger is a predicate for starting a GC cycle. Specifically,
// it is an exit condition for the _GCoff phase.
type gcTrigger struct {
	kind gcTriggerKind
	now  int64  // gcTriggerTime: current time
	n    uint32 // gcTriggerCycle: cycle number to start
}

type gcTriggerKind int

const (
	// gcTriggerHeap indicates that a cycle should be started when
	// the heap size reaches the trigger heap size computed by the
	// controller.
	// 译：gcTriggerHeap表示当堆大小达到控制器计算的触发器堆大小时应该开始一个周期。
	gcTriggerHeap gcTriggerKind = iota

	// gcTriggerTime indicates that a cycle should be started when
	// it's been more than forcegcperiod nanoseconds since the
	// previous GC cycle.
	// 译：gcTriggerTime表示自上一个GC周期以来超过forcegcperiod纳秒时，应启动一个周期。
	gcTriggerTime

	// gcTriggerCycle indicates that a cycle should be started if
	// we have not yet started cycle number gcTrigger.n (relative
	// to work.cycles).
	// 译：gcTriggerCycle表示，如果我们还没有启动周期编号gcTrigger.n（相对于work.cycles），则应该启动一个周期。
	gcTriggerCycle
)

// test reports whether the trigger condition is satisfied, meaning
// that the exit condition for the _GCoff phase has been met. The exit
// condition should be tested when allocating.
func (t gcTrigger) test() bool {
	if !memstats.enablegc || panicking.Load() != 0 || gcphase != _GCoff {
		return false
	}
	switch t.kind {
	case gcTriggerHeap:
		// Non-atomic access to gcController.heapLive for performance. If
		// we are going to trigger on this, this thread just
		// atomically wrote gcController.heapLive anyway and we'll see our
		// own write.
		trigger, _ := gcController.trigger()
		return gcController.heapLive.Load() >= trigger
	case gcTriggerTime:
		if gcController.gcPercent.Load() < 0 {
			return false
		}
		lastgc := int64(atomic.Load64(&memstats.last_gc_nanotime))
		return lastgc != 0 && t.now-lastgc > forcegcperiod
	case gcTriggerCycle:
		// t.n > work.cycles, but accounting for wraparound.
		return int32(t.n-work.cycles.Load()) > 0
	}
	return true
}

// gcStart starts the GC. It transitions from _GCoff to _GCmark (if
// debug.gcstoptheworld == 0) or performs all of GC (if
// debug.gcstoptheworld != 0).
// 译：gcStart启动GC。它从_GCoff转换到_GCmark(如果debug.gcstoptheworld==0)或执行所有GC(如果debug.gcstoptheworld=0)。
//
// This may return without performing this transition in some cases,
// such as when called on a system stack or with locks held.
// 译：在某些情况下，这可能会在不执行此转换的情况下返回，例如在系统堆栈上调用或在持有锁的情况下。
func gcStart(trigger gcTrigger) {
	// Since this is called from malloc and malloc is called in
	// the guts of a number of libraries that might be holding
	// locks, don't attempt to start GC in non-preemptible or
	// potentially unstable situations.
	// 译：因为这是从malloc调用的，并且是在许多可能持有锁的库的内部调用的，
	// 译：所以不要尝试在不可抢占或可能不稳定的情况下启动GC。
	mp := acquirem()
	if gp := getg(); gp == mp.g0 || mp.locks > 1 || mp.preemptoff != "" {
		releasem(mp)
		return
	}
	releasem(mp)
	mp = nil

	// Pick up the remaining unswept/not being swept spans concurrently
	// 译：同时拾取剩余的未扫描/未被扫描的span
	//
	// This shouldn't happen if we're being invoked in background
	// mode since proportional sweep should have just finished
	// sweeping everything, but rounding errors, etc, may leave a
	// few spans unswept. In forced mode, this is necessary since
	// GC can be forced at any point in the sweeping cycle.
	// 译：如果我们在后台模式下被调用这不应该发生，因为比例扫描应该刚刚完成所有的扫描，但是舍入误差等可能会留下一些未扫描的span。
	// 译：在强制模式下，这是必要的，因为可以在扫描周期的任何点强制GC。
	//
	// We check the transition condition continuously here in case
	// this G gets delayed in to the next GC cycle.
	// 译：我们在这里连续检查转换条件，以防这个G延迟到下一个GC周期。
	for trigger.test() && sweepone() != ^uintptr(0) { // 注：当前应该gc，但是上次清扫还未结束
		sweep.nbgsweep++
	}

	// Perform GC initialization and the sweep termination
	// transition.
	// 译：执行GC初始化和扫描终止转换。
	semacquire(&work.startSema) // 注：取得锁
	// Re-check transition condition under transition lock.
	if !trigger.test() {
		semrelease(&work.startSema) // 注：释放锁
		return
	}

	// In gcstoptheworld debug mode, upgrade the mode accordingly.
	// We do this after re-checking the transition condition so
	// that multiple goroutines that detect the heap trigger don't
	// start multiple STW GCs.
	// 译：在gcstoptheworld调试模式中，相应地升级该模式。
	// 译：我们在重新检查转换条件后这样做，这样检测堆触发器的多个goroutine就不会启动多个STW GC。
	mode := gcBackgroundMode
	if debug.gcstoptheworld == 1 {
		mode = gcForceMode
	} else if debug.gcstoptheworld == 2 {
		mode = gcForceBlockMode
	}

	// Ok, we're doing it! Stop everybody else
	semacquire(&gcsema)    // 注：对gcsema加锁
	semacquire(&worldsema) // 注：对worldsema加锁

	// For stats, check if this GC was forced by the user.
	// Update it under gcsema to avoid gctrace getting wrong values.
	// 译：有关统计信息，请检查此GC是否是由用户强制执行的。
	// 译：在gcsema下更新它，以避免gctrace得到错误的值。
	work.userForced = trigger.kind == gcTriggerCycle

	if trace.enabled {
		traceGCStart()
	}

	// Check that all Ps have finished deferred mcache flushes.
	// 译：检查所有P是否已完成延迟的mcache刷新。
	for _, p := range allp {
		if fg := p.mcache.flushGen.Load(); fg != mheap_.sweepgen { // 注：完成上一轮清扫？
			println("runtime: p", p.id, "flushGen", fg, "!= sweepgen", mheap_.sweepgen)
			throw("p mcache not flushed")
		}
	}

	gcBgMarkStartWorkers()

	systemstack(gcResetMarkState)

	work.stwprocs, work.maxprocs = gomaxprocs, gomaxprocs
	if work.stwprocs > ncpu {
		// This is used to compute CPU time of the STW phases,
		// so it can't be more than ncpu, even if GOMAXPROCS is.
		// 译：这是用来计算STW阶段的CPU时间的，所以它不能超过ncpu，即使GOMAXPROCS是。
		work.stwprocs = ncpu
	}
	work.heap0 = gcController.heapLive.Load()
	work.pauseNS = 0
	work.mode = mode

	now := nanotime()
	work.tSweepTerm = now
	work.pauseStart = now
	if trace.enabled {
		traceGCSTWStart(1)
	}
	systemstack(stopTheWorldWithSema) // 注：STW
	// Finish sweep before we start concurrent scan.
	systemstack(func() {
		finishsweep_m() // 注：如果清扫未完成，则迅速完成
	})

	// clearpools before we start the GC. If we wait they memory will not be
	// reclaimed until the next GC cycle.
	// 译：在启动GC之前清除池。如果我们等待，它们的内存将不会被回收，直到下一个GC循环。
	clearpools()

	work.cycles.Add(1)

	// Assists and workers can start the moment we start
	// the world.
	gcController.startCycle(now, int(gomaxprocs), trigger)

	// Notify the CPU limiter that assists may begin.
	gcCPULimiter.startGCTransition(true, now)

	// In STW mode, disable scheduling of user Gs. This may also
	// disable scheduling of this goroutine, so it may block as
	// soon as we start the world again.
	if mode != gcBackgroundMode {
		schedEnableUser(false)
	}

	// Enter concurrent mark phase and enable
	// write barriers.
	// 译：进入并发标记阶段并启用写入屏障。
	//
	// Because the world is stopped, all Ps will
	// observe that write barriers are enabled by
	// the time we start the world and begin
	// scanning.
	// 译：因为世界停止了，所有P都会观察到，当我们启动世界并开始扫描时，写入障碍已经启用。
	//
	// Write barriers must be enabled before assists are
	// enabled because they must be enabled before
	// any non-leaf heap objects are marked. Since
	// allocations are blocked until assists can
	// happen, we want enable assists as early as
	// possible.
	// 译：在启用辅助之前必须启用写屏障，因为必须在标记任何非叶堆对象之前启用写屏障。
	// 译：由于在助攻发生之前分配是被阻止的，我们希望尽早启用助攻。
	setGCPhase(_GCmark) // 注：设置gc标记位，即将开始标记，启动写屏障

	gcBgMarkPrepare()   // Must happen before assist enable.
	gcMarkRootPrepare() // 注：记录此时根的快照，即将其加入根扫描队列

	// Mark all active tinyalloc blocks. Since we're
	// allocating from these, they need to be black like
	// other allocations. The alternative is to blacken
	// the tiny block on every allocation from it, which
	// would slow down the tiny allocator.
	gcMarkTinyAllocs() // 注：标记mcache的tiny地址区

	// At this point all Ps have enabled the write
	// barrier, thus maintaining the no white to
	// black invariant. Enable mutator assists to
	// put back-pressure on fast allocating
	// mutators.
	// 注：在这一点上，所有P都启用了写入屏障，从而保持了无白到黑不变。
	// 注：启用突变子辅助，以减轻快速分配突变子的压力。
	atomic.Store(&gcBlackenEnabled, 1) // 注：启用gc任务

	// In STW mode, we could block the instant systemstack
	// returns, so make sure we're not preemptible.
	mp = acquirem()

	// Concurrent mark.
	systemstack(func() {
		now = startTheWorldWithSema(trace.enabled) // 注：世界恢复，结束STW
		work.pauseNS += now - work.pauseStart
		work.tMark = now
		memstats.gcPauseDist.record(now - work.pauseStart)

		// Release the CPU limiter.
		gcCPULimiter.finishGCTransition(now)
	})

	// Release the world sema before Gosched() in STW mode
	// because we will need to reacquire it later but before
	// this goroutine becomes runnable again, and we could
	// self-deadlock otherwise.
	semrelease(&worldsema)
	releasem(mp)

	// Make sure we block instead of returning to user code
	// in STW mode.
	if mode != gcBackgroundMode {
		Gosched()
	}

	semrelease(&work.startSema)
}

// gcMarkDoneFlushed counts the number of P's with flushed work.
//
// Ideally this would be a captured local in gcMarkDone, but forEachP
// escapes its callback closure, so it can't capture anything.
//
// This is protected by markDoneSema.
var gcMarkDoneFlushed uint32

// gcMarkDone transitions the GC from mark to mark termination if all
// reachable objects have been marked (that is, there are no grey
// objects and can be no more in the future). Otherwise, it flushes
// all local work to the global queues where it can be discovered by
// other workers.
//
// This should be called when all local mark work has been drained and
// there are no remaining workers. Specifically, when
//
//	work.nwait == work.nproc && !gcMarkWorkAvailable(p)
//
// The calling context must be preemptible.
//
// Flushing local work is important because idle Ps may have local
// work queued. This is the only way to make that work visible and
// drive GC to completion.
//
// It is explicitly okay to have write barriers in this function. If
// it does transition to mark termination, then all reachable objects
// have been marked, so the write barrier cannot shade any more
// objects.
func gcMarkDone() {
	// Ensure only one thread is running the ragged barrier at a
	// time.
	semacquire(&work.markDoneSema)

top:
	// Re-check transition condition under transition lock.
	//
	// It's critical that this checks the global work queues are
	// empty before performing the ragged barrier. Otherwise,
	// there could be global work that a P could take after the P
	// has passed the ragged barrier.
	if !(gcphase == _GCmark && work.nwait == work.nproc && !gcMarkWorkAvailable(nil)) {
		semrelease(&work.markDoneSema)
		return
	}

	// forEachP needs worldsema to execute, and we'll need it to
	// stop the world later, so acquire worldsema now.
	semacquire(&worldsema)

	// Flush all local buffers and collect flushedWork flags.
	gcMarkDoneFlushed = 0
	systemstack(func() {
		gp := getg().m.curg
		// Mark the user stack as preemptible so that it may be scanned.
		// Otherwise, our attempt to force all P's to a safepoint could
		// result in a deadlock as we attempt to preempt a worker that's
		// trying to preempt us (e.g. for a stack scan).
		casGToWaiting(gp, _Grunning, waitReasonGCMarkTermination)
		forEachP(func(pp *p) {
			// Flush the write barrier buffer, since this may add
			// work to the gcWork.
			wbBufFlush1(pp) // 注；将写屏障的buffer刷入gcWork

			// Flush the gcWork, since this may create global work
			// and set the flushedWork flag.
			//
			// TODO(austin): Break up these workbufs to
			// better distribute work.
			pp.gcw.dispose() // 注：强制flush目标p的gcWork的buff
			// Collect the flushedWork flag.
			if pp.gcw.flushedWork {
				atomic.Xadd(&gcMarkDoneFlushed, 1)
				pp.gcw.flushedWork = false
			}
		})
		casgstatus(gp, _Gwaiting, _Grunning)
	})

	if gcMarkDoneFlushed != 0 { // 注：如果存在新的标记任务(flush过)，则返回继续标记
		// More grey objects were discovered since the
		// previous termination check, so there may be more
		// work to do. Keep going. It's possible the
		// transition condition became true again during the
		// ragged barrier, so re-check it.
		semrelease(&worldsema)
		goto top
	}

	// There was no global work, no local work, and no Ps
	// communicated work since we took markDoneSema. Therefore
	// there are no grey objects and no more objects can be
	// shaded. Transition to mark termination.
	now := nanotime()
	work.tMarkTerm = now
	work.pauseStart = now
	getg().m.preemptoff = "gcing"
	if trace.enabled {
		traceGCSTWStart(0)
	}
	systemstack(stopTheWorldWithSema) // 注：STW
	// The gcphase is _GCmark, it will transition to _GCmarktermination
	// below. The important thing is that the wb remains active until
	// all marking is complete. This includes writes made by the GC.

	// There is sometimes work left over when we enter mark termination due
	// to write barriers performed after the completion barrier above.
	// Detect this and resume concurrent mark. This is obviously
	// unfortunate.
	//
	// See issue #27993 for details.
	//
	// Switch to the system stack to call wbBufFlush1, though in this case
	// it doesn't matter because we're non-preemptible anyway.
	restart := false
	systemstack(func() {
		for _, p := range allp {
			wbBufFlush1(p)      // 注：再次flush写屏障
			if !p.gcw.empty() { // 注：如果依然有新的未扫描数据，则再次重启扫描任务
				restart = true
				break
			}
		}
	})
	if restart {
		getg().m.preemptoff = ""
		systemstack(func() {
			now := startTheWorldWithSema(trace.enabled)
			work.pauseNS += now - work.pauseStart
			memstats.gcPauseDist.record(now - work.pauseStart)
		})
		semrelease(&worldsema)
		goto top // 注：再次返回扫描任务
	}

	gcComputeStartingStackSize()

	// Disable assists and background workers. We must do
	// this before waking blocked assists.
	atomic.Store(&gcBlackenEnabled, 0) // 注：终止扫描任务

	// Notify the CPU limiter that GC assists will now cease.
	gcCPULimiter.startGCTransition(false, now)

	// Wake all blocked assists. These will run when we
	// start the world again.
	gcWakeAllAssists() // 注：唤醒gc辅助

	// Likewise, release the transition lock. Blocked
	// workers and assists will run when we start the
	// world again.
	semrelease(&work.markDoneSema)

	// In STW mode, re-enable user goroutines. These will be
	// queued to run after we start the world.
	schedEnableUser(true)

	// endCycle depends on all gcWork cache stats being flushed.
	// The termination algorithm above ensured that up to
	// allocations since the ragged barrier.
	gcController.endCycle(now, int(gomaxprocs), work.userForced)

	// Perform mark termination. This will restart the world.
	gcMarkTermination() // 注：标记终止，恢复world
}

// World must be stopped and mark assists and background workers must be
// disabled.
func gcMarkTermination() {
	// Start marktermination (write barrier remains enabled for now).
	setGCPhase(_GCmarktermination) // 注：进入标记终止阶段，依然保持写屏障

	work.heap1 = gcController.heapLive.Load()
	startTime := nanotime()

	mp := acquirem()
	mp.preemptoff = "gcing"
	mp.traceback = 2
	curgp := mp.curg
	casGToWaiting(curgp, _Grunning, waitReasonGarbageCollection)

	// Run gc on the g0 stack. We do this so that the g stack
	// we're currently running on will no longer change. Cuts
	// the root set down a bit (g0 stacks are not scanned, and
	// we don't need to scan gc's internal state).  We also
	// need to switch to g0 so we can shrink the stack.
	systemstack(func() {
		gcMark(startTime)
		// Must return immediately.
		// The outer function's stack may have moved
		// during gcMark (it shrinks stacks, including the
		// outer function's stack), so we must not refer
		// to any of its variables. Return back to the
		// non-system stack to pick up the new addresses
		// before continuing.
	})

	systemstack(func() {
		work.heap2 = work.bytesMarked
		if debug.gccheckmark > 0 {
			// Run a full non-parallel, stop-the-world
			// mark using checkmark bits, to check that we
			// didn't forget to mark anything during the
			// concurrent mark process.
			startCheckmarks()
			gcResetMarkState()
			gcw := &getg().m.p.ptr().gcw
			gcDrain(gcw, 0)
			wbBufFlush1(getg().m.p.ptr())
			gcw.dispose()
			endCheckmarks()
		}

		// marking is complete so we can turn the write barrier off
		setGCPhase(_GCoff) // 注：状态置为GCOFF，关闭写屏障
		gcSweep(work.mode) // 注：启动清扫任务
	})

	mp.traceback = 0
	casgstatus(curgp, _Gwaiting, _Grunning)

	if trace.enabled {
		traceGCDone()
	}

	// all done
	mp.preemptoff = ""

	if gcphase != _GCoff {
		throw("gc done but gcphase != _GCoff")
	}

	// Record heapInUse for scavenger.
	memstats.lastHeapInUse = gcController.heapInUse.load()

	// Update GC trigger and pacing, as well as downstream consumers
	// of this pacing information, for the next cycle.
	systemstack(gcControllerCommit)

	// Update timing memstats
	now := nanotime()
	sec, nsec, _ := time_now()
	unixNow := sec*1e9 + int64(nsec)
	work.pauseNS += now - work.pauseStart
	work.tEnd = now
	memstats.gcPauseDist.record(now - work.pauseStart)
	atomic.Store64(&memstats.last_gc_unix, uint64(unixNow)) // must be Unix time to make sense to user
	atomic.Store64(&memstats.last_gc_nanotime, uint64(now)) // monotonic time for us
	memstats.pause_ns[memstats.numgc%uint32(len(memstats.pause_ns))] = uint64(work.pauseNS)
	memstats.pause_end[memstats.numgc%uint32(len(memstats.pause_end))] = uint64(unixNow)
	memstats.pause_total_ns += uint64(work.pauseNS)

	sweepTermCpu := int64(work.stwprocs) * (work.tMark - work.tSweepTerm)
	// We report idle marking time below, but omit it from the
	// overall utilization here since it's "free".
	markAssistCpu := gcController.assistTime.Load()
	markDedicatedCpu := gcController.dedicatedMarkTime.Load()
	markFractionalCpu := gcController.fractionalMarkTime.Load()
	markIdleCpu := gcController.idleMarkTime.Load()
	markTermCpu := int64(work.stwprocs) * (work.tEnd - work.tMarkTerm)
	scavAssistCpu := scavenge.assistTime.Load()
	scavBgCpu := scavenge.backgroundTime.Load()

	// Update cumulative GC CPU stats.
	work.cpuStats.gcAssistTime += markAssistCpu
	work.cpuStats.gcDedicatedTime += markDedicatedCpu + markFractionalCpu
	work.cpuStats.gcIdleTime += markIdleCpu
	work.cpuStats.gcPauseTime += sweepTermCpu + markTermCpu
	work.cpuStats.gcTotalTime += sweepTermCpu + markAssistCpu + markDedicatedCpu + markFractionalCpu + markIdleCpu + markTermCpu

	// Update cumulative scavenge CPU stats.
	work.cpuStats.scavengeAssistTime += scavAssistCpu
	work.cpuStats.scavengeBgTime += scavBgCpu
	work.cpuStats.scavengeTotalTime += scavAssistCpu + scavBgCpu

	// Update total CPU.
	work.cpuStats.totalTime = sched.totaltime + (now-sched.procresizetime)*int64(gomaxprocs)
	work.cpuStats.idleTime += sched.idleTime.Load()

	// Compute userTime. We compute this indirectly as everything that's not the above.
	//
	// Since time spent in _Pgcstop is covered by gcPauseTime, and time spent in _Pidle
	// is covered by idleTime, what we're left with is time spent in _Prunning and _Psyscall,
	// the latter of which is fine because the P will either go idle or get used for something
	// else via sysmon. Meanwhile if we subtract GC time from whatever's left, we get non-GC
	// _Prunning time. Note that this still leaves time spent in sweeping and in the scheduler,
	// but that's fine. The overwhelming majority of this time will be actual user time.
	work.cpuStats.userTime = work.cpuStats.totalTime - (work.cpuStats.gcTotalTime +
		work.cpuStats.scavengeTotalTime + work.cpuStats.idleTime)

	// Compute overall GC CPU utilization.
	// Omit idle marking time from the overall utilization here since it's "free".
	memstats.gc_cpu_fraction = float64(work.cpuStats.gcTotalTime-work.cpuStats.gcIdleTime) / float64(work.cpuStats.totalTime)

	// Reset assist time and background time stats.
	//
	// Do this now, instead of at the start of the next GC cycle, because
	// these two may keep accumulating even if the GC is not active.
	scavenge.assistTime.Store(0)
	scavenge.backgroundTime.Store(0)

	// Reset idle time stat.
	sched.idleTime.Store(0)

	// Reset sweep state.
	sweep.nbgsweep = 0
	sweep.npausesweep = 0

	if work.userForced {
		memstats.numforcedgc++
	}

	// Bump GC cycle count and wake goroutines waiting on sweep.
	lock(&work.sweepWaiters.lock)
	memstats.numgc++
	injectglist(&work.sweepWaiters.list) // 注：非手动GC，work.sweepWaiters.list应该是空的，do nothing
	unlock(&work.sweepWaiters.lock)

	// Release the CPU limiter.
	gcCPULimiter.finishGCTransition(now)

	// Finish the current heap profiling cycle and start a new
	// heap profiling cycle. We do this before starting the world
	// so events don't leak into the wrong cycle.
	mProf_NextCycle()

	// There may be stale spans in mcaches that need to be swept.
	// Those aren't tracked in any sweep lists, so we need to
	// count them against sweep completion until we ensure all
	// those spans have been forced out.
	// 译：可能有mcache中陈旧的span需要清理。在任何清理列表中都不会跟踪这些数据，
	// 译：因此我们需要将其计数为清理完成数，直到我们确保所有这些span都已被强制清除。
	sl := sweep.active.begin() // 注：启动清扫任务？
	if !sl.valid {
		throw("failed to set sweep barrier")
	}

	systemstack(func() { startTheWorldWithSema(trace.enabled) }) // 注：世界恢复了

	// Flush the heap profile so we can start a new cycle next GC.
	// This is relatively expensive, so we don't do it with the
	// world stopped.
	mProf_Flush()

	// Prepare workbufs for freeing by the sweeper. We do this
	// asynchronously because it can take non-trivial time.
	prepareFreeWorkbufs() // 注：准备释放workBuf的内存

	// Free stack spans. This must be done between GC cycles.
	systemstack(freeStackSpans) // 注：释放空闲的栈

	// Ensure all mcaches are flushed. Each P will flush its own
	// mcache before allocating, but idle Ps may not. Since this
	// is necessary to sweep all spans, we need to ensure all
	// mcaches are flushed before we start the next GC cycle.
	// 译：确保所有mcaches都被冲干净。每个P在分配之前会刷新自己的mcache，
	// 译：但空闲的P可能不会。因为这是清理所有span所必需的，
	// 译：所以我们需要确保在开始下一个GC循环之前清空所有的mcaches。
	systemstack(func() {
		forEachP(func(pp *p) {
			pp.mcache.prepareForSweep() // 注：清理mcache
		})
	})
	// Now that we've swept stale spans in mcaches, they don't
	// count against unswept spans.
	// 译：既然我们已经把陈旧的span扫了一遍，他们就不算未扫过的范围了。
	sweep.active.end(sl)

	// Print gctrace before dropping worldsema. As soon as we drop
	// worldsema another cycle could start and smash the stats
	// we're trying to print.
	if debug.gctrace > 0 {
		util := int(memstats.gc_cpu_fraction * 100)

		var sbuf [24]byte
		printlock()
		print("gc ", memstats.numgc,
			" @", string(itoaDiv(sbuf[:], uint64(work.tSweepTerm-runtimeInitTime)/1e6, 3)), "s ",
			util, "%: ")
		prev := work.tSweepTerm
		for i, ns := range []int64{work.tMark, work.tMarkTerm, work.tEnd} {
			if i != 0 {
				print("+")
			}
			print(string(fmtNSAsMS(sbuf[:], uint64(ns-prev))))
			prev = ns
		}
		print(" ms clock, ")
		for i, ns := range []int64{
			sweepTermCpu,
			gcController.assistTime.Load(),
			gcController.dedicatedMarkTime.Load() + gcController.fractionalMarkTime.Load(),
			gcController.idleMarkTime.Load(),
			markTermCpu,
		} {
			if i == 2 || i == 3 {
				// Separate mark time components with /.
				print("/")
			} else if i != 0 {
				print("+")
			}
			print(string(fmtNSAsMS(sbuf[:], uint64(ns))))
		}
		print(" ms cpu, ",
			work.heap0>>20, "->", work.heap1>>20, "->", work.heap2>>20, " MB, ",
			gcController.lastHeapGoal>>20, " MB goal, ",
			gcController.lastStackScan.Load()>>20, " MB stacks, ",
			gcController.globalsScan.Load()>>20, " MB globals, ",
			work.maxprocs, " P")
		if work.userForced {
			print(" (forced)")
		}
		print("\n")
		printunlock()
	}

	// Set any arena chunks that were deferred to fault.
	lock(&userArenaState.lock)
	faultList := userArenaState.fault
	userArenaState.fault = nil
	unlock(&userArenaState.lock)
	for _, lc := range faultList {
		lc.mspan.setUserArenaChunkToFault()
	}

	semrelease(&worldsema)
	semrelease(&gcsema)
	// Careful: another GC cycle may start now.

	releasem(mp)
	mp = nil

	// now that gc is done, kick off finalizer thread if needed
	if !concurrentSweep {
		// give the queued finalizers, if any, a chance to run
		Gosched()
	}
}

// gcBgMarkStartWorkers prepares background mark worker goroutines. These
// goroutines will not run until the mark phase, but they must be started while
// the work is not stopped and from a regular G stack. The caller must hold
// worldsema.
// 译：gcBgMarkStartWorkers准备背景标记worker goroutines。
// 译：这些goroutines直到标记阶段才会运行，但它们必须在工作未停止时从常规G栈启动。
// 译：调用方必须持有worldsema。
func gcBgMarkStartWorkers() {
	// Background marking is performed by per-P G's. Ensure that each P has
	// a background GC G.
	// 译：背景标记是由每个P G执行的。确保每个P都有一个背景GC G。
	//
	// Worker Gs don't exit if gomaxprocs is reduced. If it is raised
	// again, we can reuse the old workers; no need to create new workers.
	// 译：如果gomaxpros减少，worker G不会退出。
	// 译：如果再次提高，我们可以重新使用旧的worker，不需要创造新的worker。
	for gcBgMarkWorkerCount < gomaxprocs { // 注：gcBgMarkWorker只增不减
		go gcBgMarkWorker()

		notetsleepg(&work.bgMarkReady, -1)
		noteclear(&work.bgMarkReady)
		// The worker is now guaranteed to be added to the pool before
		// its P's next findRunnableGCWorker.

		gcBgMarkWorkerCount++
	}
}

// gcBgMarkPrepare sets up state for background marking.
// Mutator assists must not yet be enabled.
func gcBgMarkPrepare() {
	// Background marking will stop when the work queues are empty
	// and there are no more workers (note that, since this is
	// concurrent, this may be a transient state, but mark
	// termination will clean it up). Between background workers
	// and assists, we don't really know how many workers there
	// will be, so we pretend to have an arbitrarily large number
	// of workers, almost all of which are "waiting". While a
	// worker is working it decrements nwait. If nproc == nwait,
	// there are no workers.
	work.nproc = ^uint32(0)
	work.nwait = ^uint32(0)
}

// gcBgMarkWorkerNode is an entry in the gcBgMarkWorkerPool. It points to a single
// gcBgMarkWorker goroutine.
// 译：gcBgMarkWorkerNode是gcBgMarkWorkerPool中的一个条目。它指向一个gcBgMarkWorker goroutine。
type gcBgMarkWorkerNode struct {
	// Unused workers are managed in a lock-free stack. This field must be first.
	// 译：未使用的工作线程在无锁堆栈中进行管理。此字段必须位于第一位。
	node lfnode

	// The g of this worker.
	gp guintptr

	// Release this m on park. This is used to communicate with the unlock
	// function, which cannot access the G's stack. It is unused outside of
	// gcBgMarkWorker().
	// 译：把这个m放在park里。这用于与解锁功能通信，解锁功能无法访问g的栈。它在gcBgMarkWorker()之外未使用。
	m muintptr
}

func gcBgMarkWorker() {
	gp := getg() // 注：此处的gp就是函数本身

	// We pass node to a gopark unlock function, so it can't be on
	// the stack (see gopark). Prevent deadlock from recursively
	// starting GC by disabling preemption.
	// 译：我们将节点传递给gopark解锁函数，所以它不能在栈上（请参阅gopark）。
	// 译：通过禁用抢占，防止死锁递归启动GC。
	gp.m.preemptoff = "GC worker init"
	node := new(gcBgMarkWorkerNode)
	gp.m.preemptoff = ""

	node.gp.set(gp) // 注：当前g置入node节点

	node.m.set(acquirem())
	notewakeup(&work.bgMarkReady)
	// After this point, the background mark worker is generally scheduled
	// cooperatively by gcController.findRunnableGCWorker. While performing
	// work on the P, preemption is disabled because we are working on
	// P-local work buffers. When the preempt flag is set, this puts itself
	// into _Gwaiting to be woken up by gcController.findRunnableGCWorker
	// at the appropriate time.
	// 译：在这一点之后，背景标记工作程序通常由gcController.findRunnableGCWorker协同调度。
	// 译：在对P执行工作时，由于我们正在处理P本地工作缓冲区，因此会禁用抢占。
	// 译：当设置了抢占标志时，它将自己放入_Gwaiting中，
	// 译：以便在适当的时间被gcController.findRunnableGCWorker唤醒。
	//
	// When preemption is enabled (e.g., while in gcMarkDone), this worker
	// may be preempted and schedule as a _Grunnable G from a runq. That is
	// fine; it will eventually gopark again for further scheduling via
	// findRunnableGCWorker.
	// 译：当启用抢占时（例如，在gcMarkDone中），此工作进程可能会被抢占，并从runq调度为_Grunnable g。
	// 译：这很好；它最终将再次通过findRunnableGCWorker进行gopark以进行进一步的调度。
	//
	// Since we disable preemption before notifying bgMarkReady, we
	// guarantee that this G will be in the worker pool for the next
	// findRunnableGCWorker. This isn't strictly necessary, but it reduces
	// latency between _GCmark starting and the workers starting.
	// 译：由于我们在通知bgMarkReady之前禁用了抢占，因此我们保证该G将在下一个findRunnableGCWorker的工作池中。
	// 译：这并不是绝对必要的，但它减少了_GCmark启动和工人启动之间的延迟。

	for {
		// Go to sleep until woken by
		// gcController.findRunnableGCWorker.
		gopark(func(g *g, nodep unsafe.Pointer) bool {
			node := (*gcBgMarkWorkerNode)(nodep)

			if mp := node.m.ptr(); mp != nil {
				// The worker G is no longer running; release
				// the M.
				// 译：工人G不再运行；释放M。
				//
				// N.B. it is _safe_ to release the M as soon
				// as we are no longer performing P-local mark
				// work.
				// 译：N.B.只要我们不再执行P-局部标记工作，就可以安全地释放M。
				//
				// However, since we cooperatively stop work
				// when gp.preempt is set, if we releasem in
				// the loop then the following call to gopark
				// would immediately preempt the G. This is
				// also safe, but inefficient: the G must
				// schedule again only to enter gopark and park
				// again. Thus, we defer the release until
				// after parking the G.
				// 译：然而，由于我们在设置gp.preempt时协同停止工作，如果我们在循环中释放它们，
				// 译：那么下面对gopark的调用将立即抢占G。这也是安全的，但效率低下：G必须再次调度，
				// 译：才能再次进入gopark并停车。因此，我们将释放推迟到停放G。
				releasem(mp)
			}

			// Release this G to the pool.
			gcBgMarkWorkerPool.push(&node.node) // 注：此处&node.node应该是等于&node，二者是等价的
			// Note that at this point, the G may immediately be
			// rescheduled and may be running.
			return true
		}, unsafe.Pointer(node), waitReasonGCWorkerIdle, traceEvGoBlock, 0)

		// Preemption must not occur here, or another G might see
		// p.gcMarkWorkerMode.
		// 译：此处不能发生抢占，否则另一个G可能会看到p.gcMarkWorkerMode。

		// Disable preemption so we can use the gcw. If the
		// scheduler wants to preempt us, we'll stop draining,
		// dispose the gcw, and then preempt.
		// 译：禁用抢占，这样我们就可以使用GCW了。
		// 译：如果调度程序想要抢占我们，我们将停止排出，处理GCW，然后抢占。
		node.m.set(acquirem())
		// 注：gp就是当前任务，所以pp就是当前的p
		pp := gp.m.p.ptr() // 译：在禁用抢占的情况下，P不能更改。 // P can't change with preemption disabled.

		if gcBlackenEnabled == 0 {
			println("worker mode", pp.gcMarkWorkerMode)
			throw("gcBgMarkWorker: blackening not enabled")
		}

		if pp.gcMarkWorkerMode == gcMarkWorkerNotWorker {
			throw("gcBgMarkWorker: mode not set")
		}

		startTime := nanotime()
		pp.gcMarkWorkerStartTime = startTime
		var trackLimiterEvent bool
		if pp.gcMarkWorkerMode == gcMarkWorkerIdleMode {
			trackLimiterEvent = pp.limiterEvent.start(limiterEventIdleMarkWork, startTime)
		}

		decnwait := atomic.Xadd(&work.nwait, -1)
		if decnwait == work.nproc {
			println("runtime: work.nwait=", decnwait, "work.nproc=", work.nproc)
			throw("work.nwait was > work.nproc")
		}

		systemstack(func() {
			// Mark our goroutine preemptible so its stack
			// can be scanned. This lets two mark workers
			// scan each other (otherwise, they would
			// deadlock). We must not modify anything on
			// the G stack. However, stack shrinking is
			// disabled for mark workers, so it is safe to
			// read from the G stack.
			// 译：将我们的goroutine标记为可抢占，这样它的堆栈就可以被扫描。
			// 译：这允许两个标记工作进程互相扫描(否则，它们将死锁)。
			// 译：我们不能修改G栈上的任何内容。
			// 译：但是，对标记工作线程禁用堆栈收缩，因此从G堆栈读取是安全的。
			casGToWaiting(gp, _Grunning, waitReasonGCWorkerActive)
			switch pp.gcMarkWorkerMode {
			default:
				throw("gcBgMarkWorker: unexpected gcMarkWorkerMode")
			case gcMarkWorkerDedicatedMode: // 注：专属
				gcDrain(&pp.gcw, gcDrainUntilPreempt|gcDrainFlushBgCredit) // 注：先按照可抢占模式执行标记协程
				if gp.preempt {                                            // 注：如果被抢占
					// We were preempted. This is
					// a useful signal to kick
					// everything out of the run
					// queue so it can run
					// somewhere else.
					// 译：我们被抢占了。这是一个有用的信号，可以将所有内容从运行队列中剔除，以便它可以在其他地方运行。
					if drainQ, n := runqdrain(pp); n > 0 { // 注：摘除全部未执行的g，考虑到运行的g就是我们自己，因此也就是全部的g
						lock(&sched.lock)
						globrunqputbatch(&drainQ, int32(n)) // 注：加入全局队列
						unlock(&sched.lock)
					}
				}
				// Go back to draining, this time
				// without preemption.
				gcDrain(&pp.gcw, gcDrainFlushBgCredit) // 注：以不可抢占模式执行标记协程
			case gcMarkWorkerFractionalMode: // 注：小数/分时任务
				gcDrain(&pp.gcw, gcDrainFractional|gcDrainUntilPreempt|gcDrainFlushBgCredit)
			case gcMarkWorkerIdleMode: // 注：空闲
				gcDrain(&pp.gcw, gcDrainIdle|gcDrainUntilPreempt|gcDrainFlushBgCredit)
			}
			casgstatus(gp, _Gwaiting, _Grunning)
		})

		// Account for time and mark us as stopped.
		now := nanotime()
		duration := now - startTime
		gcController.markWorkerStop(pp.gcMarkWorkerMode, duration)
		if trackLimiterEvent {
			pp.limiterEvent.stop(limiterEventIdleMarkWork, now)
		}
		if pp.gcMarkWorkerMode == gcMarkWorkerFractionalMode {
			atomic.Xaddint64(&pp.gcFractionalMarkTime, duration)
		}

		// Was this the last worker and did we run out
		// of work?
		incnwait := atomic.Xadd(&work.nwait, +1)
		if incnwait > work.nproc {
			println("runtime: p.gcMarkWorkerMode=", pp.gcMarkWorkerMode,
				"work.nwait=", incnwait, "work.nproc=", work.nproc)
			throw("work.nwait > work.nproc")
		}

		// We'll releasem after this point and thus this P may run
		// something else. We must clear the worker mode to avoid
		// attributing the mode to a different (non-worker) G in
		// traceGoStart.
		pp.gcMarkWorkerMode = gcMarkWorkerNotWorker

		// If this worker reached a background mark completion
		// point, signal the main GC goroutine.
		if incnwait == work.nproc && !gcMarkWorkAvailable(nil) { // 注：标记完成，没有新的任务
			// We don't need the P-local buffers here, allow
			// preemption because we may schedule like a regular
			// goroutine in gcMarkDone (block on locks, etc).
			releasem(node.m.ptr())
			node.m.set(nil)

			gcMarkDone()
		}
	}
}

// gcMarkWorkAvailable reports whether executing a mark worker
// on p is potentially useful. p may be nil, in which case it only
// checks the global sources of work.
func gcMarkWorkAvailable(p *p) bool { // 注：是否有gc任务
	if p != nil && !p.gcw.empty() { // 注：当前p下的work
		return true
	}
	if !work.full.empty() { // 注：全局work
		return true // global work available
	}
	if work.markrootNext < work.markrootJobs { // 注：根指针work
		return true // root scan work available
	}
	return false
}

// gcMark runs the mark (or, for concurrent GC, mark termination)
// All gcWork caches must be empty.
// STW is in effect at this point.
func gcMark(startTime int64) { // 注：此时依然STW
	if debug.allocfreetrace > 0 {
		tracegc()
	}

	if gcphase != _GCmarktermination {
		throw("in gcMark expecting to see gcphase as _GCmarktermination")
	}
	work.tstart = startTime

	// Check that there's no marking work remaining.
	if work.full != 0 || work.markrootNext < work.markrootJobs {
		print("runtime: full=", hex(work.full), " next=", work.markrootNext, " jobs=", work.markrootJobs, " nDataRoots=", work.nDataRoots, " nBSSRoots=", work.nBSSRoots, " nSpanRoots=", work.nSpanRoots, " nStackRoots=", work.nStackRoots, "\n")
		panic("non-empty mark queue after concurrent mark")
	}

	if debug.gccheckmark > 0 {
		// This is expensive when there's a large number of
		// Gs, so only do it if checkmark is also enabled.
		gcMarkRootCheck()
	}
	if work.full != 0 {
		throw("work.full != 0")
	}

	// Drop allg snapshot. allgs may have grown, in which case
	// this is the only reference to the old backing store and
	// there's no need to keep it around.
	work.stackRoots = nil

	// Clear out buffers and double-check that all gcWork caches
	// are empty. This should be ensured by gcMarkDone before we
	// enter mark termination.
	//
	// TODO: We could clear out buffers just before mark if this
	// has a non-negligible impact on STW time.
	for _, p := range allp {
		// The write barrier may have buffered pointers since
		// the gcMarkDone barrier. However, since the barrier
		// ensured all reachable objects were marked, all of
		// these must be pointers to black objects. Hence we
		// can just discard the write barrier buffer.
		if debug.gccheckmark > 0 {
			// For debugging, flush the buffer and make
			// sure it really was all marked.
			wbBufFlush1(p)
		} else {
			p.wbBuf.reset()
		}

		gcw := &p.gcw
		if !gcw.empty() {
			printlock()
			print("runtime: P ", p.id, " flushedWork ", gcw.flushedWork)
			if gcw.wbuf1 == nil {
				print(" wbuf1=<nil>")
			} else {
				print(" wbuf1.n=", gcw.wbuf1.nobj)
			}
			if gcw.wbuf2 == nil {
				print(" wbuf2=<nil>")
			} else {
				print(" wbuf2.n=", gcw.wbuf2.nobj)
			}
			print("\n")
			throw("P has cached GC work at end of mark termination")
		}
		// There may still be cached empty buffers, which we
		// need to flush since we're going to free them. Also,
		// there may be non-zero stats because we allocated
		// black after the gcMarkDone barrier.
		gcw.dispose() // 注：将空buffer归还全局空队列
	}

	// Flush scanAlloc from each mcache since we're about to modify
	// heapScan directly. If we were to flush this later, then scanAlloc
	// might have incorrect information.
	//
	// Note that it's not important to retain this information; we know
	// exactly what heapScan is at this point via scanWork.
	for _, p := range allp {
		c := p.mcache
		if c == nil {
			continue
		}
		c.scanAlloc = 0 // 注：重置mcache的信息
	}

	// Reset controller state.
	gcController.resetLive(work.bytesMarked)
}

// gcSweep must be called on the system stack because it acquires the heap
// lock. See mheap for details.
//
// The world must be stopped.
//
//go:systemstack
func gcSweep(mode gcMode) {
	assertWorldStopped()

	if gcphase != _GCoff {
		throw("gcSweep being done but phase is not GCoff")
	}

	lock(&mheap_.lock)
	mheap_.sweepgen += 2 // 注：清扫任务号+2，将全部已清扫重置为待清扫
	sweep.active.reset() // 注：清扫任务相关数据重置
	mheap_.pagesSwept.Store(0)
	mheap_.sweepArenas = mheap_.allArenas
	mheap_.reclaimIndex.Store(0)
	mheap_.reclaimCredit.Store(0)
	unlock(&mheap_.lock)

	sweep.centralIndex.clear()

	if !_ConcurrentSweep || mode == gcForceBlockMode {
		// Special case synchronous sweep.
		// Record that no proportional sweeping has to happen.
		lock(&mheap_.lock)
		mheap_.sweepPagesPerByte = 0
		unlock(&mheap_.lock)
		// Sweep all spans eagerly.
		for sweepone() != ^uintptr(0) {
			sweep.npausesweep++
		}
		// Free workbufs eagerly.
		prepareFreeWorkbufs()
		for freeSomeWbufs(false) {
		}
		// All "free" events for this mark/sweep cycle have
		// now happened, so we can make this profile cycle
		// available immediately.
		mProf_NextCycle()
		mProf_Flush()
		return
	}

	// Background sweep.
	lock(&sweep.lock)
	if sweep.parked {
		sweep.parked = false
		ready(sweep.g, 0, true) // 注：就绪后台清扫任务，安排下一个执行
	}
	unlock(&sweep.lock)
}

// gcResetMarkState resets global state prior to marking (concurrent
// or STW) and resets the stack scan state of all Gs.
//
// This is safe to do without the world stopped because any Gs created
// during or after this will start out in the reset state.
//
// gcResetMarkState must be called on the system stack because it acquires
// the heap lock. See mheap for details.
//
//go:systemstack
func gcResetMarkState() { // 注：标记状态重置
	// This may be called during a concurrent phase, so lock to make sure
	// allgs doesn't change.
	forEachG(func(gp *g) {
		gp.gcscandone = false // set to true in gcphasework
		gp.gcAssistBytes = 0
	})

	// Clear page marks. This is just 1MB per 64GB of heap, so the
	// time here is pretty trivial.
	lock(&mheap_.lock)
	arenas := mheap_.allArenas
	unlock(&mheap_.lock)
	for _, ai := range arenas {
		ha := mheap_.arenas[ai.l1()][ai.l2()]
		for i := range ha.pageMarks {
			ha.pageMarks[i] = 0
		}
	}

	work.bytesMarked = 0
	work.initialHeapLive = gcController.heapLive.Load()
}

// Hooks for other packages

var poolcleanup func()
var boringCaches []unsafe.Pointer // for crypto/internal/boring

//go:linkname sync_runtime_registerPoolCleanup sync.runtime_registerPoolCleanup
func sync_runtime_registerPoolCleanup(f func()) {
	poolcleanup = f
}

//go:linkname boring_registerCache crypto/internal/boring/bcache.registerCache
func boring_registerCache(p unsafe.Pointer) {
	boringCaches = append(boringCaches, p)
}

func clearpools() {
	// clear sync.Pools
	if poolcleanup != nil {
		poolcleanup()
	}

	// clear boringcrypto caches
	for _, p := range boringCaches {
		atomicstorep(p, nil)
	}

	// Clear central sudog cache.
	// Leave per-P caches alone, they have strictly bounded size.
	// Disconnect cached list before dropping it on the floor,
	// so that a dangling ref to one entry does not pin all of them.
	lock(&sched.sudoglock)
	var sg, sgnext *sudog
	for sg = sched.sudogcache; sg != nil; sg = sgnext {
		sgnext = sg.next
		sg.next = nil
	}
	sched.sudogcache = nil
	unlock(&sched.sudoglock)

	// Clear central defer pool.
	// Leave per-P pools alone, they have strictly bounded size.
	lock(&sched.deferlock)
	// disconnect cached list before dropping it on the floor,
	// so that a dangling ref to one entry does not pin all of them.
	var d, dlink *_defer
	for d = sched.deferpool; d != nil; d = dlink {
		dlink = d.link
		d.link = nil
	}
	sched.deferpool = nil
	unlock(&sched.deferlock)
}

// Timing

// itoaDiv formats val/(10**dec) into buf.
func itoaDiv(buf []byte, val uint64, dec int) []byte {
	i := len(buf) - 1
	idec := i - dec
	for val >= 10 || i >= idec {
		buf[i] = byte(val%10 + '0')
		i--
		if i == idec {
			buf[i] = '.'
			i--
		}
		val /= 10
	}
	buf[i] = byte(val + '0')
	return buf[i:]
}

// fmtNSAsMS nicely formats ns nanoseconds as milliseconds.
func fmtNSAsMS(buf []byte, ns uint64) []byte {
	if ns >= 10e6 {
		// Format as whole milliseconds.
		return itoaDiv(buf, ns/1e6, 0)
	}
	// Format two digits of precision, with at most three decimal places.
	x := ns / 1e3
	if x == 0 {
		buf[0] = '0'
		return buf[:1]
	}
	dec := 3
	for x >= 100 {
		x /= 10
		dec--
	}
	return itoaDiv(buf, x, dec)
}

// Helpers for testing GC.

// gcTestMoveStackOnNextCall causes the stack to be moved on a call
// immediately following the call to this. It may not work correctly
// if any other work appears after this call (such as returning).
// Typically the following call should be marked go:noinline so it
// performs a stack check.
//
// In rare cases this may not cause the stack to move, specifically if
// there's a preemption between this call and the next.
func gcTestMoveStackOnNextCall() {
	gp := getg()
	gp.stackguard0 = stackForceMove
}

// gcTestIsReachable performs a GC and returns a bit set where bit i
// is set if ptrs[i] is reachable.
func gcTestIsReachable(ptrs ...unsafe.Pointer) (mask uint64) {
	// This takes the pointers as unsafe.Pointers in order to keep
	// them live long enough for us to attach specials. After
	// that, we drop our references to them.

	if len(ptrs) > 64 {
		panic("too many pointers for uint64 mask")
	}

	// Block GC while we attach specials and drop our references
	// to ptrs. Otherwise, if a GC is in progress, it could mark
	// them reachable via this function before we have a chance to
	// drop them.
	semacquire(&gcsema)

	// Create reachability specials for ptrs.
	specials := make([]*specialReachable, len(ptrs))
	for i, p := range ptrs {
		lock(&mheap_.speciallock)
		s := (*specialReachable)(mheap_.specialReachableAlloc.alloc())
		unlock(&mheap_.speciallock)
		s.special.kind = _KindSpecialReachable
		if !addspecial(p, &s.special) {
			throw("already have a reachable special (duplicate pointer?)")
		}
		specials[i] = s
		// Make sure we don't retain ptrs.
		ptrs[i] = nil
	}

	semrelease(&gcsema)

	// Force a full GC and sweep.
	GC()

	// Process specials.
	for i, s := range specials {
		if !s.done {
			printlock()
			println("runtime: object", i, "was not swept")
			throw("IsReachable failed")
		}
		if s.reachable {
			mask |= 1 << i
		}
		lock(&mheap_.speciallock)
		mheap_.specialReachableAlloc.free(unsafe.Pointer(s))
		unlock(&mheap_.speciallock)
	}

	return mask
}

// gcTestPointerClass returns the category of what p points to, one of:
// "heap", "stack", "data", "bss", "other". This is useful for checking
// that a test is doing what it's intended to do.
//
// This is nosplit simply to avoid extra pointer shuffling that may
// complicate a test.
//
//go:nosplit
func gcTestPointerClass(p unsafe.Pointer) string {
	p2 := uintptr(noescape(p))
	gp := getg()
	if gp.stack.lo <= p2 && p2 < gp.stack.hi {
		return "stack"
	}
	if base, _, _ := findObject(p2, 0, 0); base != 0 {
		return "heap"
	}
	for _, datap := range activeModules() {
		if datap.data <= p2 && p2 < datap.edata || datap.noptrdata <= p2 && p2 < datap.enoptrdata {
			return "data"
		}
		if datap.bss <= p2 && p2 < datap.ebss || datap.noptrbss <= p2 && p2 <= datap.enoptrbss {
			return "bss"
		}
	}
	KeepAlive(p)
	return "other"
}
