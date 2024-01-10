// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector: marking and scanning

package runtime

import (
	"internal/goarch"
	"runtime/internal/atomic"
	"runtime/internal/sys"
	"unsafe"
)

const (
	fixedRootFinalizers = iota
	fixedRootFreeGStacks
	fixedRootCount

	// rootBlockBytes is the number of bytes to scan per data or
	// BSS root.
	rootBlockBytes = 256 << 10

	// maxObletBytes is the maximum bytes of an object to scan at
	// once. Larger objects will be split up into "oblets" of at
	// most this size. Since we can scan 1–2 MB/ms, 128 KB bounds
	// scan preemption at ~100 µs.
	//
	// This must be > _MaxSmallSize so that the object base is the
	// span base.
	maxObletBytes = 128 << 10 // 注：128k

	// drainCheckThreshold specifies how many units of work to do
	// between self-preemption checks in gcDrain. Assuming a scan
	// rate of 1 MB/ms, this is ~100 µs. Lower values have higher
	// overhead in the scan loop (the scheduler check may perform
	// a syscall, so its overhead is nontrivial). Higher values
	// make the system less responsive to incoming work.
	drainCheckThreshold = 100000

	// pagesPerSpanRoot indicates how many pages to scan from a span root
	// at a time. Used by special root marking.
	//
	// Higher values improve throughput by increasing locality, but
	// increase the minimum latency of a marking operation.
	//
	// Must be a multiple of the pageInUse bitmap element size and
	// must also evenly divide pagesPerArena.
	pagesPerSpanRoot = 512
)

// gcMarkRootPrepare queues root scanning jobs (stacks, globals, and
// some miscellany) and initializes scanning-related state.
// 译：gcMarkRootPrepare将根扫描作业（堆栈、全局和一些杂项）排队，并初始化与扫描相关的状态。
//
// The world must be stopped.
// 译：世界必须停止。
func gcMarkRootPrepare() {
	assertWorldStopped() // 注：断言STW

	// Compute how many data and BSS root blocks there are.
	nBlocks := func(bytes uintptr) int { // 注：对齐
		return int(divRoundUp(bytes, rootBlockBytes))
	}

	work.nDataRoots = 0
	work.nBSSRoots = 0

	// Scan globals.
	for _, datap := range activeModules() {
		nDataRoots := nBlocks(datap.edata - datap.data)
		if nDataRoots > work.nDataRoots {
			work.nDataRoots = nDataRoots // 注：最大偏移量
		}
	}

	for _, datap := range activeModules() {
		nBSSRoots := nBlocks(datap.ebss - datap.bss)
		if nBSSRoots > work.nBSSRoots {
			work.nBSSRoots = nBSSRoots // 注：最大偏移量
		}
	}

	// Scan span roots for finalizer specials.
	// 译：扫描span根目录以查找终结器特殊产品。
	//
	// We depend on addfinalizer to mark objects that get
	// finalizers after root marking.
	// 译：我们依靠addfinalizer来标记在根标记之后获得finalizer的对象。
	//
	// We're going to scan the whole heap (that was available at the time the
	// mark phase started, i.e. markArenas) for in-use spans which have specials.
	// 译：我们将扫描整个堆(在标记阶段开始时是可用的，即markArenas)，以查找有特殊用途的正在使用的范围。
	//
	// Break up the work into arenas, and further into chunks.
	// 译：把这项工作分成几个区域，然后再分成几块。
	//
	// Snapshot allArenas as markArenas. This snapshot is safe because allArenas
	// is append-only.
	// 译：将所有Arenas快照为markArenas。此快照是安全的，因为所有Arenas都是仅附加的。
	mheap_.markArenas = mheap_.allArenas[:len(mheap_.allArenas):len(mheap_.allArenas)]
	work.nSpanRoots = len(mheap_.markArenas) * (pagesPerArena / pagesPerSpanRoot) // 注：span根扫描，处理终结器special

	// Scan stacks.
	// 译：扫描堆栈。
	//
	// Gs may be created after this point, but it's okay that we
	// ignore them because they begin life without any roots, so
	// there's nothing to scan, and any roots they create during
	// the concurrent phase will be caught by the write barrier.
	// 译：g可能是在这之后创建的，但是我们可以忽略它们，因为它们开始时没有任何根，所以没有什么可扫描的，
	// 译：并且它们在并发阶段创建的任何根都将被写屏障捕获。
	work.stackRoots = allGsSnapshot()
	work.nStackRoots = len(work.stackRoots) // 注：栈扫描

	work.markrootNext = 0 // 注：从0扫描
	work.markrootJobs = uint32(fixedRootCount + work.nDataRoots + work.nBSSRoots + work.nSpanRoots + work.nStackRoots)

	// Calculate base indexes of each root type
	work.baseData = uint32(fixedRootCount)
	work.baseBSS = work.baseData + uint32(work.nDataRoots)
	work.baseSpans = work.baseBSS + uint32(work.nBSSRoots)
	work.baseStacks = work.baseSpans + uint32(work.nSpanRoots)
	work.baseEnd = work.baseStacks + uint32(work.nStackRoots)
	// 注：扫描顺序 fixedRootFinalizers -> fixedRootFreeGStacks -> fixedRootCount ->
	// 注：baseData -> baseBSS -> baseSpans -> baseStacks
}

// gcMarkRootCheck checks that all roots have been scanned. It is
// purely for debugging.
func gcMarkRootCheck() {
	if work.markrootNext < work.markrootJobs {
		print(work.markrootNext, " of ", work.markrootJobs, " markroot jobs done\n")
		throw("left over markroot jobs")
	}

	// Check that stacks have been scanned.
	//
	// We only check the first nStackRoots Gs that we should have scanned.
	// Since we don't care about newer Gs (see comment in
	// gcMarkRootPrepare), no locking is required.
	i := 0
	forEachGRace(func(gp *g) {
		if i >= work.nStackRoots {
			return
		}

		if !gp.gcscandone {
			println("gp", gp, "goid", gp.goid,
				"status", readgstatus(gp),
				"gcscandone", gp.gcscandone)
			throw("scan missed a g")
		}

		i++
	})
}

// ptrmask for an allocation containing a single pointer.
var oneptrmask = [...]uint8{1}

// markroot scans the i'th root.
// 译：markroot扫描第i个根
//
// Preemption must be disabled (because this uses a gcWork).
// 译：必须禁用抢占(因为这使用gcWork)。
//
// Returns the amount of GC work credit produced by the operation.
// If flushBgCredit is true, then that credit is also flushed
// to the background credit pool.
// 译：返回操作产生的GC工时额度。
// 译：如果flushBgCredit为真，则该信用也会被刷新到后台信用池。
//
// nowritebarrier is only advisory here.
// 译：写屏障在这里只是建议。
//
//go:nowritebarrier
func markroot(gcw *gcWork, i uint32, flushBgCredit bool) int64 {
	// 注：此时STW已经结束，因此可能存在和g同时执行的情况
	// Note: if you add a case here, please also update heapdump.go:dumproots.
	var workDone int64
	var workCounter *atomic.Int64
	switch {
	case work.baseData <= i && i < work.baseBSS: // 注：扫描nDataRoots，处理已初始化的全局变量
		workCounter = &gcController.globalsScanWork
		for _, datap := range activeModules() {
			workDone += markrootBlock(datap.data, datap.edata-datap.data, datap.gcdatamask.bytedata, gcw, int(i-work.baseData))
		}

	case work.baseBSS <= i && i < work.baseSpans: // 注：扫描nBSSRoots，处理未初始化的全局变量
		workCounter = &gcController.globalsScanWork
		for _, datap := range activeModules() {
			workDone += markrootBlock(datap.bss, datap.ebss-datap.bss, datap.gcbssmask.bytedata, gcw, int(i-work.baseBSS))
		}

	case i == fixedRootFinalizers: // 注：扫描根Finalizer
		for fb := allfin; fb != nil; fb = fb.alllink { // 注：扫描终止器
			cnt := uintptr(atomic.Load(&fb.cnt))
			scanblock(uintptr(unsafe.Pointer(&fb.fin[0])), cnt*unsafe.Sizeof(fb.fin[0]), &finptrmask[0], gcw, nil)
		}

	case i == fixedRootFreeGStacks: // 注：释放已终止的 g 的栈
		// Switch to the system stack so we can call
		// stackfree.
		systemstack(markrootFreeGStacks)

	case work.baseSpans <= i && i < work.baseStacks: // 注：扫描mspan中的special
		// mark mspan.specials
		markrootSpans(gcw, int(i-work.baseSpans)) // 注：传入span的偏移量

	default: // 注：扫描g的栈
		// the rest is scanning goroutine stacks
		workCounter = &gcController.stackScanWork
		if i < work.baseStacks || work.baseEnd <= i {
			printlock()
			print("runtime: markroot index ", i, " not in stack roots range [", work.baseStacks, ", ", work.baseEnd, ")\n")
			throw("markroot: bad index")
		}
		gp := work.stackRoots[i-work.baseStacks] // 注：遍历g

		// remember when we've first observed the G blocked
		// needed only to output in traceback
		status := readgstatus(gp) // We are not in a scan state
		if (status == _Gwaiting || status == _Gsyscall) && gp.waitsince == 0 {
			gp.waitsince = work.tstart // 注：调整gp.waitsince，延长等待时间？
		}

		// scanstack must be done on the system stack in case
		// we're trying to scan our own stack.
		systemstack(func() {
			// If this is a self-scan, put the user G in
			// _Gwaiting to prevent self-deadlock. It may
			// already be in _Gwaiting if this is a mark
			// worker or we're in mark termination.
			// 译：如果这是自扫描，请将用户G放入_Gwaiting以防止自死锁。
			// 译：如果这是一个标记工作者，或者我们正在标记终止，它可能已经在_Gwaiting中了。
			userG := getg().m.curg
			selfScan := gp == userG && readgstatus(userG) == _Grunning
			if selfScan {
				casGToWaiting(userG, _Grunning, waitReasonGarbageCollectionScan) // 注：调整g的状态为_Gwaiting
			}

			// TODO: suspendG blocks (and spins) until gp
			// stops, which may take a while for
			// running goroutines. Consider doing this in
			// two phases where the first is non-blocking:
			// we scan the stacks we can and ask running
			// goroutines to scan themselves; and the
			// second blocks.
			// 译：TODO:suspendG阻塞（和旋转）直到gp停止，这可能需要一段时间才能运行goroutines。
			// 译：考虑分两个阶段来做这件事，第一个阶段是非阻塞的：我们扫描我们可以扫描的堆栈，
			// 译：并要求运行的goroutines扫描它们自己；以及第二块。
			stopped := suspendG(gp)
			if stopped.dead { // 注：g未启用，直接跳过
				gp.gcscandone = true
				return
			}
			if gp.gcscandone {
				throw("g already scanned")
			}
			workDone += scanstack(gp, gcw) // 注：执行栈扫描，将栈指针引用的堆对象标灰
			gp.gcscandone = true
			resumeG(stopped) // 注：恢复g

			if selfScan {
				casgstatus(userG, _Gwaiting, _Grunning) // 注：恢复状态为_Grunning
			}
		})
	}
	if workCounter != nil && workDone != 0 {
		workCounter.Add(workDone)
		if flushBgCredit {
			gcFlushBgCredit(workDone)
		}
	}
	return workDone
}

// markrootBlock scans the shard'th shard of the block of memory [b0,
// b0+n0), with the given pointer mask.
// 译：markrootBlock使用给定的指针掩码扫描内存块[b0，b0+n0]的碎片。
//
// Returns the amount of work done.
//
// 译：返回已完成的工作量。
//
//go:nowritebarrier
func markrootBlock(b0, n0 uintptr, ptrmask0 *uint8, gcw *gcWork, shard int) int64 {
	if rootBlockBytes%(8*goarch.PtrSize) != 0 {
		// This is necessary to pick byte offsets in ptrmask0.
		throw("rootBlockBytes must be a multiple of 8*ptrSize")
	}

	// Note that if b0 is toward the end of the address space,
	// then b0 + rootBlockBytes might wrap around.
	// These tests are written to avoid any possible overflow.
	off := uintptr(shard) * rootBlockBytes
	if off >= n0 {
		return 0
	}
	b := b0 + off
	ptrmask := (*uint8)(add(unsafe.Pointer(ptrmask0), uintptr(shard)*(rootBlockBytes/(8*goarch.PtrSize))))
	n := uintptr(rootBlockBytes)
	if off+n > n0 {
		n = n0 - off
	}

	// Scan this shard.
	scanblock(b, n, ptrmask, gcw, nil)
	return int64(n)
}

// markrootFreeGStacks frees stacks of dead Gs.
//
// This does not free stacks of dead Gs cached on Ps, but having a few
// cached stacks around isn't a problem.
func markrootFreeGStacks() { // 注：释放栈空间
	// Take list of dead Gs with stacks.
	lock(&sched.gFree.lock)
	list := sched.gFree.stack
	sched.gFree.stack = gList{}
	unlock(&sched.gFree.lock)
	if list.empty() {
		return
	}

	// Free stacks.
	q := gQueue{list.head, list.head}
	for gp := list.head.ptr(); gp != nil; gp = gp.schedlink.ptr() {
		stackfree(gp.stack)
		gp.stack.lo = 0
		gp.stack.hi = 0
		// Manipulate the queue directly since the Gs are
		// already all linked the right way.
		q.tail.set(gp)
	}

	// Put Gs back on the free list.
	lock(&sched.gFree.lock)
	sched.gFree.noStack.pushAll(q)
	unlock(&sched.gFree.lock)
}

// markrootSpans marks roots for one shard of markArenas.
// 译：markrootSpans标记一个markArenas碎片的根。
//
//go:nowritebarrier
func markrootSpans(gcw *gcWork, shard int) {
	// Objects with finalizers have two GC-related invariants:
	// 译：具有终结器的对象有两个与GC相关的不变量：
	//
	// 1) Everything reachable from the object must be marked.
	// This ensures that when we pass the object to its finalizer,
	// everything the finalizer can reach will be retained.
	// 译：1）必须标记从物体可到达的所有东西。
	// 译：这确保了当我们将对象传递给它的终结器时，终结器所能到达的一切都将被保留。
	//
	// 2) Finalizer specials (which are not in the garbage
	// collected heap) are roots. In practice, this means the fn
	// field must be scanned.
	// 译：2）终结器特殊（不在gc堆中）是根。在实践中，这意味着必须扫描fn字段
	sg := mheap_.sweepgen

	// Find the arena and page index into that arena for this shard.
	ai := mheap_.markArenas[shard/(pagesPerArena/pagesPerSpanRoot)]
	ha := mheap_.arenas[ai.l1()][ai.l2()]
	arenaPage := uint(uintptr(shard) * pagesPerSpanRoot % pagesPerArena)

	// Construct slice of bitmap which we'll iterate over.
	specialsbits := ha.pageSpecials[arenaPage/8:]
	specialsbits = specialsbits[:pagesPerSpanRoot/8]
	for i := range specialsbits {
		// Find set bits, which correspond to spans with specials.
		specials := atomic.Load8(&specialsbits[i])
		if specials == 0 { // 注：本组span内没有special直接跳过
			continue
		}
		for j := uint(0); j < 8; j++ {
			if specials&(1<<j) == 0 { // 注：检查当前span没有special跳过
				continue
			}
			// Find the span for this bit.
			//
			// This value is guaranteed to be non-nil because having
			// specials implies that the span is in-use, and since we're
			// currently marking we can be sure that we don't have to worry
			// about the span being freed and re-used.
			s := ha.spans[arenaPage+uint(i)*8+j] // 注：取得当前span

			// The state must be mSpanInUse if the specials bit is set, so
			// sanity check that.
			if state := s.state.get(); state != mSpanInUse {
				print("s.state = ", state, "\n")
				throw("non in-use span found with specials bit set")
			}
			// Check that this span was swept (it may be cached or uncached).
			if !useCheckmark && !(s.sweepgen == sg || s.sweepgen == sg+3) {
				// sweepgen was updated (+2) during non-checkmark GC pass
				print("sweep ", s.sweepgen, " ", sg, "\n")
				throw("gc: unswept span")
			}

			// Lock the specials to prevent a special from being
			// removed from the list while we're traversing it.
			lock(&s.speciallock)
			for sp := s.specials; sp != nil; sp = sp.next { // 注：逐一检查special
				if sp.kind != _KindSpecialFinalizer { // 注：仅处理_KindSpecialFinalizer
					continue
				}
				// don't mark finalized object, but scan it so we
				// retain everything it points to.
				spf := (*specialfinalizer)(unsafe.Pointer(sp))
				// A finalizer can be set for an inner byte of an object, find object beginning.
				p := s.base() + uintptr(spf.special.offset)/s.elemsize*s.elemsize // 注：取得对象的地址

				// Mark everything that can be reached from
				// the object (but *not* the object itself or
				// we'll never collect it).
				if !s.spanclass.noscan() { // 注：含有指针
					scanobject(p, gcw) // 注：直接扫描对象
				}

				// The special itself is a root.
				// 译：special本身就是一个根
				scanblock(uintptr(unsafe.Pointer(&spf.fn)), goarch.PtrSize, &oneptrmask[0], gcw, nil) // 注：此处扫描的是spf的函数指针？
			}
			unlock(&s.speciallock)
		}
	}
}

// gcAssistAlloc performs GC work to make gp's assist debt positive.
// gp must be the calling user goroutine.
//
// This must be called with preemption enabled.
func gcAssistAlloc(gp *g) {
	// Don't assist in non-preemptible contexts. These are
	// generally fragile and won't allow the assist to block.
	if getg() == gp.m.g0 {
		return
	}
	if mp := getg().m; mp.locks > 0 || mp.preemptoff != "" {
		return
	}

	traced := false
retry:
	if go119MemoryLimitSupport && gcCPULimiter.limiting() {
		// If the CPU limiter is enabled, intentionally don't
		// assist to reduce the amount of CPU time spent in the GC.
		if traced {
			traceGCMarkAssistDone()
		}
		return
	}
	// Compute the amount of scan work we need to do to make the
	// balance positive. When the required amount of work is low,
	// we over-assist to build up credit for future allocations
	// and amortize the cost of assisting.
	assistWorkPerByte := gcController.assistWorkPerByte.Load()
	assistBytesPerWork := gcController.assistBytesPerWork.Load()
	debtBytes := -gp.gcAssistBytes
	scanWork := int64(assistWorkPerByte * float64(debtBytes))
	if scanWork < gcOverAssistWork {
		scanWork = gcOverAssistWork
		debtBytes = int64(assistBytesPerWork * float64(scanWork))
	}

	// Steal as much credit as we can from the background GC's
	// scan credit. This is racy and may drop the background
	// credit below 0 if two mutators steal at the same time. This
	// will just cause steals to fail until credit is accumulated
	// again, so in the long run it doesn't really matter, but we
	// do have to handle the negative credit case.
	bgScanCredit := gcController.bgScanCredit.Load()
	stolen := int64(0)
	if bgScanCredit > 0 {
		if bgScanCredit < scanWork {
			stolen = bgScanCredit
			gp.gcAssistBytes += 1 + int64(assistBytesPerWork*float64(stolen))
		} else {
			stolen = scanWork
			gp.gcAssistBytes += debtBytes
		}
		gcController.bgScanCredit.Add(-stolen)

		scanWork -= stolen

		if scanWork == 0 {
			// We were able to steal all of the credit we
			// needed.
			if traced {
				traceGCMarkAssistDone()
			}
			return
		}
	}

	if trace.enabled && !traced {
		traced = true
		traceGCMarkAssistStart()
	}

	// Perform assist work
	systemstack(func() {
		gcAssistAlloc1(gp, scanWork)
		// The user stack may have moved, so this can't touch
		// anything on it until it returns from systemstack.
	})

	completed := gp.param != nil
	gp.param = nil
	if completed {
		gcMarkDone()
	}

	if gp.gcAssistBytes < 0 {
		// We were unable steal enough credit or perform
		// enough work to pay off the assist debt. We need to
		// do one of these before letting the mutator allocate
		// more to prevent over-allocation.
		//
		// If this is because we were preempted, reschedule
		// and try some more.
		if gp.preempt {
			Gosched()
			goto retry
		}

		// Add this G to an assist queue and park. When the GC
		// has more background credit, it will satisfy queued
		// assists before flushing to the global credit pool.
		//
		// Note that this does *not* get woken up when more
		// work is added to the work list. The theory is that
		// there wasn't enough work to do anyway, so we might
		// as well let background marking take care of the
		// work that is available.
		if !gcParkAssist() {
			goto retry
		}

		// At this point either background GC has satisfied
		// this G's assist debt, or the GC cycle is over.
	}
	if traced {
		traceGCMarkAssistDone()
	}
}

// gcAssistAlloc1 is the part of gcAssistAlloc that runs on the system
// stack. This is a separate function to make it easier to see that
// we're not capturing anything from the user stack, since the user
// stack may move while we're in this function.
//
// gcAssistAlloc1 indicates whether this assist completed the mark
// phase by setting gp.param to non-nil. This can't be communicated on
// the stack since it may move.
//
//go:systemstack
func gcAssistAlloc1(gp *g, scanWork int64) {
	// Clear the flag indicating that this assist completed the
	// mark phase.
	gp.param = nil

	if atomic.Load(&gcBlackenEnabled) == 0 {
		// The gcBlackenEnabled check in malloc races with the
		// store that clears it but an atomic check in every malloc
		// would be a performance hit.
		// Instead we recheck it here on the non-preemptable system
		// stack to determine if we should perform an assist.

		// GC is done, so ignore any remaining debt.
		gp.gcAssistBytes = 0
		return
	}
	// Track time spent in this assist. Since we're on the
	// system stack, this is non-preemptible, so we can
	// just measure start and end time.
	//
	// Limiter event tracking might be disabled if we end up here
	// while on a mark worker.
	startTime := nanotime()
	trackLimiterEvent := gp.m.p.ptr().limiterEvent.start(limiterEventMarkAssist, startTime)

	decnwait := atomic.Xadd(&work.nwait, -1)
	if decnwait == work.nproc {
		println("runtime: work.nwait =", decnwait, "work.nproc=", work.nproc)
		throw("nwait > work.nprocs")
	}

	// gcDrainN requires the caller to be preemptible.
	casGToWaiting(gp, _Grunning, waitReasonGCAssistMarking)

	// drain own cached work first in the hopes that it
	// will be more cache friendly.
	gcw := &getg().m.p.ptr().gcw
	workDone := gcDrainN(gcw, scanWork)

	casgstatus(gp, _Gwaiting, _Grunning)

	// Record that we did this much scan work.
	//
	// Back out the number of bytes of assist credit that
	// this scan work counts for. The "1+" is a poor man's
	// round-up, to ensure this adds credit even if
	// assistBytesPerWork is very low.
	assistBytesPerWork := gcController.assistBytesPerWork.Load()
	gp.gcAssistBytes += 1 + int64(assistBytesPerWork*float64(workDone))

	// If this is the last worker and we ran out of work,
	// signal a completion point.
	incnwait := atomic.Xadd(&work.nwait, +1)
	if incnwait > work.nproc {
		println("runtime: work.nwait=", incnwait,
			"work.nproc=", work.nproc)
		throw("work.nwait > work.nproc")
	}

	if incnwait == work.nproc && !gcMarkWorkAvailable(nil) {
		// This has reached a background completion point. Set
		// gp.param to a non-nil value to indicate this. It
		// doesn't matter what we set it to (it just has to be
		// a valid pointer).
		gp.param = unsafe.Pointer(gp)
	}
	now := nanotime()
	duration := now - startTime
	pp := gp.m.p.ptr()
	pp.gcAssistTime += duration
	if trackLimiterEvent {
		pp.limiterEvent.stop(limiterEventMarkAssist, now)
	}
	if pp.gcAssistTime > gcAssistTimeSlack {
		gcController.assistTime.Add(pp.gcAssistTime)
		gcCPULimiter.update(now)
		pp.gcAssistTime = 0
	}
}

// gcWakeAllAssists wakes all currently blocked assists. This is used
// at the end of a GC cycle. gcBlackenEnabled must be false to prevent
// new assists from going to sleep after this point.
func gcWakeAllAssists() {
	lock(&work.assistQueue.lock)
	list := work.assistQueue.q.popList()
	injectglist(&list)
	unlock(&work.assistQueue.lock)
}

// gcParkAssist puts the current goroutine on the assist queue and parks.
//
// gcParkAssist reports whether the assist is now satisfied. If it
// returns false, the caller must retry the assist.
func gcParkAssist() bool {
	lock(&work.assistQueue.lock)
	// If the GC cycle finished while we were getting the lock,
	// exit the assist. The cycle can't finish while we hold the
	// lock.
	if atomic.Load(&gcBlackenEnabled) == 0 {
		unlock(&work.assistQueue.lock)
		return true
	}

	gp := getg()
	oldList := work.assistQueue.q
	work.assistQueue.q.pushBack(gp)

	// Recheck for background credit now that this G is in
	// the queue, but can still back out. This avoids a
	// race in case background marking has flushed more
	// credit since we checked above.
	if gcController.bgScanCredit.Load() > 0 {
		work.assistQueue.q = oldList
		if oldList.tail != 0 {
			oldList.tail.ptr().schedlink.set(nil)
		}
		unlock(&work.assistQueue.lock)
		return false
	}
	// Park.
	goparkunlock(&work.assistQueue.lock, waitReasonGCAssistWait, traceEvGoBlockGC, 2)
	return true
}

// gcFlushBgCredit flushes scanWork units of background scan work
// credit. This first satisfies blocked assists on the
// work.assistQueue and then flushes any remaining credit to
// gcController.bgScanCredit.
//
// Write barriers are disallowed because this is used by gcDrain after
// it has ensured that all work is drained and this must preserve that
// condition.
//
//go:nowritebarrierrec
func gcFlushBgCredit(scanWork int64) {
	if work.assistQueue.q.empty() {
		// Fast path; there are no blocked assists. There's a
		// small window here where an assist may add itself to
		// the blocked queue and park. If that happens, we'll
		// just get it on the next flush.
		gcController.bgScanCredit.Add(scanWork)
		return
	}

	assistBytesPerWork := gcController.assistBytesPerWork.Load()
	scanBytes := int64(float64(scanWork) * assistBytesPerWork)

	lock(&work.assistQueue.lock)
	for !work.assistQueue.q.empty() && scanBytes > 0 {
		gp := work.assistQueue.q.pop()
		// Note that gp.gcAssistBytes is negative because gp
		// is in debt. Think carefully about the signs below.
		if scanBytes+gp.gcAssistBytes >= 0 {
			// Satisfy this entire assist debt.
			scanBytes += gp.gcAssistBytes
			gp.gcAssistBytes = 0
			// It's important that we *not* put gp in
			// runnext. Otherwise, it's possible for user
			// code to exploit the GC worker's high
			// scheduler priority to get itself always run
			// before other goroutines and always in the
			// fresh quantum started by GC.
			ready(gp, 0, false)
		} else {
			// Partially satisfy this assist.
			gp.gcAssistBytes += scanBytes
			scanBytes = 0
			// As a heuristic, we move this assist to the
			// back of the queue so that large assists
			// can't clog up the assist queue and
			// substantially delay small assists.
			work.assistQueue.q.pushBack(gp)
			break
		}
	}

	if scanBytes > 0 {
		// Convert from scan bytes back to work.
		assistWorkPerByte := gcController.assistWorkPerByte.Load()
		scanWork = int64(float64(scanBytes) * assistWorkPerByte)
		gcController.bgScanCredit.Add(scanWork)
	}
	unlock(&work.assistQueue.lock)
}

// scanstack scans gp's stack, greying all pointers found on the stack.
// 译：scanstack扫描gp的堆栈，使堆栈上的所有指针变灰。
//
// Returns the amount of scan work performed, but doesn't update
// gcController.stackScanWork or flush any credit. Any background credit produced
// by this function should be flushed by its caller. scanstack itself can't
// safely flush because it may result in trying to wake up a goroutine that
// was just scanned, resulting in a self-deadlock.
// 译：返回已执行的扫描工作量，但不更新gcController.stackScanWork或刷新任何信用。
// 译：此函数生成的任何后台信用都应由其调用方刷新。
// 译：scanstack本身无法安全地刷新，因为它可能会导致试图唤醒刚刚扫描的goroutine，从而导致自死锁。
//
// scanstack will also shrink the stack if it is safe to do so. If it
// is not, it schedules a stack shrink for the next synchronous safe
// point.
// 译：如果安全的话，scanstack还会收缩堆栈。如果不安全，它会为下一个同步安全点安排堆栈收缩。
//
// scanstack is marked go:systemstack because it must not be preempted
// while using a workbuf.
// 译：scanstack被标记为go:systemstack，因为在使用workbuf时不能抢占它。
//
//go:nowritebarrier
//go:systemstack
func scanstack(gp *g, gcw *gcWork) int64 {
	if readgstatus(gp)&_Gscan == 0 {
		print("runtime:scanstack: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", hex(readgstatus(gp)), "\n")
		throw("scanstack - bad status")
	}

	switch readgstatus(gp) &^ _Gscan {
	default:
		print("runtime: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", readgstatus(gp), "\n")
		throw("mark - bad status")
	case _Gdead:
		return 0
	case _Grunning:
		print("runtime: gp=", gp, ", goid=", gp.goid, ", gp->atomicstatus=", readgstatus(gp), "\n")
		throw("scanstack: goroutine not stopped")
	case _Grunnable, _Gsyscall, _Gwaiting:
		// ok
	}

	if gp == getg() {
		throw("can't scan our own stack")
	}

	// scannedSize is the amount of work we'll be reporting.
	//
	// It is less than the allocated size (which is hi-lo).
	var sp uintptr
	if gp.syscallsp != 0 {
		sp = gp.syscallsp // If in a system call this is the stack pointer (gp.sched.sp can be 0 in this case on Windows).
	} else {
		sp = gp.sched.sp
	}
	scannedSize := gp.stack.hi - sp

	// Keep statistics for initial stack size calculation.
	// Note that this accumulates the scanned size, not the allocated size.
	p := getg().m.p.ptr()
	p.scannedStackSize += uint64(scannedSize)
	p.scannedStacks++

	if isShrinkStackSafe(gp) {
		// Shrink the stack if not much of it is being used.
		// 译：如果使用的堆栈不多，请收缩堆栈。
		shrinkstack(gp)
	} else {
		// Otherwise, shrink the stack at the next sync safe point.
		// 译：否则，请在下一个同步安全点收缩堆栈。
		gp.preemptShrink = true
	}

	var state stackScanState
	state.stack = gp.stack

	if stackTraceDebug {
		println("stack trace goroutine", gp.goid)
	}

	if debugScanConservative && gp.asyncSafePoint {
		print("scanning async preempted goroutine ", gp.goid, " stack [", hex(gp.stack.lo), ",", hex(gp.stack.hi), ")\n")
	}

	// Scan the saved context register. This is effectively a live
	// register that gets moved back and forth between the
	// register and sched.ctxt without a write barrier.
	// 译：扫描保存的上下文寄存器。这实际上是一个在寄存器和sched.ctxt之间来回移动的活动寄存器，没有写障碍。
	if gp.sched.ctxt != nil {
		scanblock(uintptr(unsafe.Pointer(&gp.sched.ctxt)), goarch.PtrSize, &oneptrmask[0], gcw, &state)
	}

	// Scan the stack. Accumulate a list of stack objects.
	// 译：扫描堆栈。累积堆栈对象的列表。
	scanframe := func(frame *stkframe, unused unsafe.Pointer) bool {
		scanframeworker(frame, &state, gcw)
		return true
	}
	gentraceback(^uintptr(0), ^uintptr(0), 0, gp, 0, nil, 0x7fffffff, scanframe, nil, 0)

	// Find additional pointers that point into the stack from the heap.
	// Currently this includes defers and panics. See also function copystack.

	// Find and trace other pointers in defer records.
	for d := gp._defer; d != nil; d = d.link { // 注：扫描defer
		if d.fn != nil {
			// Scan the func value, which could be a stack allocated closure.
			// See issue 30453.
			scanblock(uintptr(unsafe.Pointer(&d.fn)), goarch.PtrSize, &oneptrmask[0], gcw, &state)
		}
		if d.link != nil {
			// The link field of a stack-allocated defer record might point
			// to a heap-allocated defer record. Keep that heap record live.
			scanblock(uintptr(unsafe.Pointer(&d.link)), goarch.PtrSize, &oneptrmask[0], gcw, &state)
		}
		// Retain defers records themselves.
		// Defer records might not be reachable from the G through regular heap
		// tracing because the defer linked list might weave between the stack and the heap.
		if d.heap {
			scanblock(uintptr(unsafe.Pointer(&d)), goarch.PtrSize, &oneptrmask[0], gcw, &state)
		}
	}
	if gp._panic != nil {
		// Panics are always stack allocated.
		state.putPtr(uintptr(unsafe.Pointer(gp._panic)), false)
	}

	// Find and scan all reachable stack objects.
	//
	// The state's pointer queue prioritizes precise pointers over
	// conservative pointers so that we'll prefer scanning stack
	// objects precisely.
	state.buildIndex()
	for {
		p, conservative := state.getPtr()
		if p == 0 {
			break
		}
		obj := state.findObject(p)
		if obj == nil {
			continue
		}
		r := obj.r    // 注：栈对象信息
		if r == nil { // 注：已扫描
			// We've already scanned this object.
			continue
		}
		obj.setRecord(nil) // Don't scan it again.
		if stackTraceDebug {
			printlock()
			print("  live stkobj at", hex(state.stack.lo+uintptr(obj.off)), "of size", obj.size)
			if conservative {
				print(" (conservative)")
			}
			println()
			printunlock()
		}
		gcdata := r.gcdata()
		var s *mspan
		if r.useGCProg() {
			// This path is pretty unlikely, an object large enough
			// to have a GC program allocated on the stack.
			// We need some space to unpack the program into a straight
			// bitmask, which we allocate/free here.
			// TODO: it would be nice if there were a way to run a GC
			// program without having to store all its bits. We'd have
			// to change from a Lempel-Ziv style program to something else.
			// Or we can forbid putting objects on stacks if they require
			// a gc program (see issue 27447).
			s = materializeGCProg(r.ptrdata(), gcdata)
			gcdata = (*byte)(unsafe.Pointer(s.startAddr))
		}

		b := state.stack.lo + uintptr(obj.off) // 注：栈地址+对象偏移量，即对象地址
		if conservative {                      // 注：保守扫描
			scanConservative(b, r.ptrdata(), gcdata, gcw, &state)
		} else {
			scanblock(b, r.ptrdata(), gcdata, gcw, &state)
		}

		if s != nil {
			dematerializeGCProg(s)
		}
	}

	// Deallocate object buffers.
	// (Pointer buffers were all deallocated in the loop above.)
	for state.head != nil { // 注：释放buffer
		x := state.head
		state.head = x.next
		if stackTraceDebug {
			for i := 0; i < x.nobj; i++ {
				obj := &x.obj[i]
				if obj.r == nil { // reachable
					continue
				}
				println("  dead stkobj at", hex(gp.stack.lo+uintptr(obj.off)), "of size", obj.r.size)
				// Note: not necessarily really dead - only reachable-from-ptr dead.
			}
		}
		x.nobj = 0
		putempty((*workbuf)(unsafe.Pointer(x)))
	}
	if state.buf != nil || state.cbuf != nil || state.freeBuf != nil {
		throw("remaining pointer buffers")
	}
	return int64(scannedSize)
}

// Scan a stack frame: local variables and function arguments/results.
// 译：扫描堆栈帧：局部变量和函数参数/结果。
//
//go:nowritebarrier
func scanframeworker(frame *stkframe, state *stackScanState, gcw *gcWork) {
	if _DebugGC > 1 && frame.continpc != 0 {
		print("scanframe ", funcname(frame.fn), "\n")
	}

	isAsyncPreempt := frame.fn.valid() && frame.fn.funcID == funcID_asyncPreempt
	isDebugCall := frame.fn.valid() && frame.fn.funcID == funcID_debugCallV2
	if state.conservative || isAsyncPreempt || isDebugCall {
		if debugScanConservative {
			println("conservatively scanning function", funcname(frame.fn), "at PC", hex(frame.continpc))
		}

		// Conservatively scan the frame. Unlike the precise
		// case, this includes the outgoing argument space
		// since we may have stopped while this function was
		// setting up a call.
		// 译：保守地扫描帧。与精确的情况不同，这包括传出参数空间，因为我们可能在该函数设置调用时已经停止。
		//
		// TODO: We could narrow this down if the compiler
		// produced a single map per function of stack slots
		// and registers that ever contain a pointer.
		// 译：TODO:如果编译器为包含指针的堆栈槽和寄存器的每个函数生成一个映射，我们可以缩小范围。
		if frame.varp != 0 {
			size := frame.varp - frame.sp
			if size > 0 {
				// 注：保守扫描，将每一个可能是指针的值按照指针处理
				scanConservative(frame.sp, size, nil, gcw, state)
			}
		}

		// Scan arguments to this frame.
		if n := frame.argBytes(); n != 0 {
			// TODO: We could pass the entry argument map
			// to narrow this down further.
			// 注：保守扫描
			scanConservative(frame.argp, n, nil, gcw, state)
		}

		if isAsyncPreempt || isDebugCall {
			// This function's frame contained the
			// registers for the asynchronously stopped
			// parent frame. Scan the parent
			// conservatively.
			state.conservative = true
		} else {
			// We only wanted to scan those two frames
			// conservatively. Clear the flag for future
			// frames.
			state.conservative = false
		}
		return
	}

	locals, args, objs := frame.getStackMap(&state.cache, false)

	// Scan local variables if stack frame has been allocated.
	if locals.n > 0 {
		size := uintptr(locals.n) * goarch.PtrSize
		scanblock(frame.varp-size, size, locals.bytedata, gcw, state)
	}

	// Scan arguments.
	if args.n > 0 {
		scanblock(frame.argp, uintptr(args.n)*goarch.PtrSize, args.bytedata, gcw, state)
	}

	// Add all stack objects to the stack object list.
	if frame.varp != 0 {
		// varp is 0 for defers, where there are no locals.
		// In that case, there can't be a pointer to its args, either.
		// (And all args would be scanned above anyway.)
		for i := range objs {
			obj := &objs[i]
			off := obj.off
			base := frame.varp // locals base pointer
			if off >= 0 {
				base = frame.argp // arguments and return values base pointer
			}
			ptr := base + uintptr(off)
			if ptr < frame.sp {
				// object hasn't been allocated in the frame yet.
				continue
			}
			if stackTraceDebug {
				println("stkobj at", hex(ptr), "of size", obj.size)
			}
			state.addObject(ptr, obj)
		}
	}
}

type gcDrainFlags int

const (
	gcDrainUntilPreempt gcDrainFlags = 1 << iota
	gcDrainFlushBgCredit
	gcDrainIdle
	gcDrainFractional
)

// gcDrain scans roots and objects in work buffers, blackening grey
// objects until it is unable to get more work. It may return before
// GC is done; it's the caller's responsibility to balance work from
// other Ps.
// 译：gcDrain扫描工作缓冲区中的根和对象，使灰色对象变黑，直到无法获得更多工作。
// 译：它可能在GC完成之前返回；调用者负责平衡来自其他P的工作。
//
// If flags&gcDrainUntilPreempt != 0, gcDrain returns when g.preempt
// is set.
// 译：如果flags&gcDrainUntilPreempt!=0，则gcDrain在设置g.preempt时返回。
//
// If flags&gcDrainIdle != 0, gcDrain returns when there is other work
// to do.
// 译：如果flags&gcDrainIdle!=0，则当有其他工作要做时，gcDrain返回。
//
// If flags&gcDrainFractional != 0, gcDrain self-preempts when
// pollFractionalWorkerExit() returns true. This implies
// gcDrainNoBlock.
// 译：如果flags&gcDrainFractional != 0，则当pollFractionalWorkerExit()返回TRUE时，gcDrain自抢占。这意味着gcDrainNoBlock。
//
// If flags&gcDrainFlushBgCredit != 0, gcDrain flushes scan work
// credit to gcController.bgScanCredit every gcCreditSlack units of
// scan work.
// 译：如果flags&gcDrainFlushBgCredit != 0，则gcDrain将扫描工作信用刷新到gcController.bgScanCredit每个gcCreditSlack单位的扫描工作。
//
// gcDrain will always return if there is a pending STW.
// 译：如果存在挂起的STW，gcDrain将始终返回。
//
//go:nowritebarrier
func gcDrain(gcw *gcWork, flags gcDrainFlags) {
	if !writeBarrier.needed {
		throw("gcDrain phase incorrect")
	}

	gp := getg().m.curg
	preemptible := flags&gcDrainUntilPreempt != 0    // 注：设置gcDrainUntilPreempt
	flushBgCredit := flags&gcDrainFlushBgCredit != 0 // 注：设置gcDrainFlushBgCredit
	idle := flags&gcDrainIdle != 0                   // 注：设置gcDrainIdle

	initScanWork := gcw.heapScanWork

	// checkWork is the scan work before performing the next
	// self-preempt check.
	// 译：checkWork是在执行下一个自抢占检查之前的扫描工作。
	checkWork := int64(1<<63 - 1)
	var check func() bool
	if flags&(gcDrainIdle|gcDrainFractional) != 0 { // 注：如果设置了空闲或者小数
		checkWork = initScanWork + drainCheckThreshold
		if idle {
			check = pollWork // 注：检查空闲结束
		} else if flags&gcDrainFractional != 0 {
			check = pollFractionalWorkerExit // 注: 检查分时结束
		}
	}

	// Drain root marking jobs.
	// 译：排出??根标记作业。
	if work.markrootNext < work.markrootJobs { // 网：倘若根对象还未标记完成，则先进行根对象标记
		// Stop if we're preemptible or if someone wants to STW.
		// 译：如果我们是preemptible，或者如果有人想要STW，就停止吧。
		for !(gp.preempt && (preemptible || sched.gcwaiting.Load())) { // 注：没有被抢占
			job := atomic.Xadd(&work.markrootNext, +1) - 1
			if job >= work.markrootJobs {
				break
			}
			// 注：标记根
			markroot(gcw, job, flushBgCredit)
			if check != nil && check() {
				goto done
			}
		}
	}

	// Drain heap marking jobs.
	// Stop if we're preemptible or if someone wants to STW.
	for !(gp.preempt && (preemptible || sched.gcwaiting.Load())) { // 注：没有被抢占
		// Try to keep work available on the global queue. We used to
		// check if there were waiting workers, but it's better to
		// just keep work available than to make workers wait. In the
		// worst case, we'll do O(log(_WorkbufSize)) unnecessary
		// balances.
		if work.full == 0 {
			gcw.balance()
		}

		// 注：尝试取得一个扫描任务，一个待扫描对象指针
		b := gcw.tryGetFast()
		if b == 0 {
			b = gcw.tryGet()
			if b == 0 {
				// Flush the write barrier
				// buffer; this may create
				// more work.
				wbBufFlush(nil, 0)
				b = gcw.tryGet()
			}
		}
		if b == 0 {
			// Unable to get work.
			break
		}
		scanobject(b, gcw) // 注：扫描对象

		// Flush background scan work credit to the global
		// account if we've accumulated enough locally so
		// mutator assists can draw on it.
		if gcw.heapScanWork >= gcCreditSlack {
			gcController.heapScanWork.Add(gcw.heapScanWork)
			if flushBgCredit {
				gcFlushBgCredit(gcw.heapScanWork - initScanWork)
				initScanWork = 0
			}
			checkWork -= gcw.heapScanWork
			gcw.heapScanWork = 0

			if checkWork <= 0 {
				checkWork += drainCheckThreshold
				if check != nil && check() {
					break
				}
			}
		}
	}

done:
	// Flush remaining scan work credit.
	if gcw.heapScanWork > 0 {
		gcController.heapScanWork.Add(gcw.heapScanWork)
		if flushBgCredit {
			gcFlushBgCredit(gcw.heapScanWork - initScanWork)
		}
		gcw.heapScanWork = 0
	}
}

// gcDrainN blackens grey objects until it has performed roughly
// scanWork units of scan work or the G is preempted. This is
// best-effort, so it may perform less work if it fails to get a work
// buffer. Otherwise, it will perform at least n units of work, but
// may perform more because scanning is always done in whole object
// increments. It returns the amount of scan work performed.
//
// The caller goroutine must be in a preemptible state (e.g.,
// _Gwaiting) to prevent deadlocks during stack scanning. As a
// consequence, this must be called on the system stack.
//
//go:nowritebarrier
//go:systemstack
func gcDrainN(gcw *gcWork, scanWork int64) int64 {
	if !writeBarrier.needed {
		throw("gcDrainN phase incorrect")
	}

	// There may already be scan work on the gcw, which we don't
	// want to claim was done by this call.
	workFlushed := -gcw.heapScanWork

	// In addition to backing out because of a preemption, back out
	// if the GC CPU limiter is enabled.
	gp := getg().m.curg
	for !gp.preempt && !gcCPULimiter.limiting() && workFlushed+gcw.heapScanWork < scanWork {
		// See gcDrain comment.
		if work.full == 0 {
			gcw.balance()
		}

		b := gcw.tryGetFast()
		if b == 0 {
			b = gcw.tryGet()
			if b == 0 {
				// Flush the write barrier buffer;
				// this may create more work.
				wbBufFlush(nil, 0)
				b = gcw.tryGet()
			}
		}

		if b == 0 {
			// Try to do a root job.
			if work.markrootNext < work.markrootJobs {
				job := atomic.Xadd(&work.markrootNext, +1) - 1
				if job < work.markrootJobs {
					workFlushed += markroot(gcw, job, false)
					continue
				}
			}
			// No heap or root jobs.
			break
		}

		scanobject(b, gcw)

		// Flush background scan work credit.
		if gcw.heapScanWork >= gcCreditSlack {
			gcController.heapScanWork.Add(gcw.heapScanWork)
			workFlushed += gcw.heapScanWork
			gcw.heapScanWork = 0
		}
	}

	// Unlike gcDrain, there's no need to flush remaining work
	// here because this never flushes to bgScanCredit and
	// gcw.dispose will flush any remaining work to scanWork.

	return workFlushed + gcw.heapScanWork
}

// scanblock scans b as scanobject would, but using an explicit
// pointer bitmap instead of the heap bitmap.
// 译：scanblock像scanObject一样扫描b，但使用显式指针位图而不是堆位图。
//
// This is used to scan non-heap roots, so it does not update
// gcw.bytesMarked or gcw.heapScanWork.
// 译：用于扫描非堆根，因此不会更新gcw.bytesMarked或gcw.heapScanWork。
//
// If stk != nil, possible stack pointers are also reported to stk.putPtr.
// 译：如果stk！=nil，则还会向stk.putPtr报告可能的堆栈指针。
//
//go:nowritebarrier
func scanblock(b0, n0 uintptr, ptrmask *uint8, gcw *gcWork, stk *stackScanState) {
	// Use local copies of original parameters, so that a stack trace
	// due to one of the throws below shows the original block
	// base and extent.
	b := b0
	n := n0

	for i := uintptr(0); i < n; {
		// Find bits for the next word.
		bits := uint32(*addb(ptrmask, i/(goarch.PtrSize*8))) // 注：位图8位一组
		if bits == 0 {                                       // 注：均无指针，则跳过
			i += goarch.PtrSize * 8
			continue
		}
		for j := 0; j < 8 && i < n; j++ {
			if bits&1 != 0 { // 注：当前元素(bits最右一位)不是指针，则跳过
				// Same work as in scanobject; see comments there.
				p := *(*uintptr)(unsafe.Pointer(b + i))
				if p != 0 {
					if obj, span, objIndex := findObject(p, b, i); obj != 0 {
						// 注：如果是有效堆对象，则标灰
						greyobject(obj, b, i, span, gcw, objIndex)
					} else if stk != nil && p >= stk.stack.lo && p < stk.stack.hi {
						// 注：如果是栈地址，置入栈队列
						stk.putPtr(p, false)
					}
				}
			}
			bits >>= 1
			i += goarch.PtrSize
		}
	}
}

// scanobject scans the object starting at b, adding pointers to gcw.
// b must point to the beginning of a heap object or an oblet.
// scanobject consults the GC bitmap for the pointer mask and the
// spans for the size of the object.
//
//go:nowritebarrier
func scanobject(b uintptr, gcw *gcWork) { // 注：扫描对象
	// Prefetch object before we scan it.
	//
	// This will overlap fetching the beginning of the object with initial
	// setup before we start scanning the object.
	sys.Prefetch(b)

	// Find the bits for b and the size of the object at b.
	//
	// b is either the beginning of an object, in which case this
	// is the size of the object to scan, or it points to an
	// oblet, in which case we compute the size to scan below.
	s := spanOfUnchecked(b) // 注：取得b所在的span
	n := s.elemsize
	if n == 0 {
		throw("scanobject n == 0")
	}
	if s.spanclass.noscan() { // 注：不含指针类型不需要扫描
		// Correctness-wise this is ok, but it's inefficient
		// if noscan objects reach here.
		throw("scanobject of a noscan object")
	}

	if n > maxObletBytes { // 注：n>128k
		// Large object. Break into oblets for better
		// parallelism and lower latency.
		// 译：大型对象。分解问题以获得更好的并行性和更低的延迟。
		if b == s.base() {
			// Enqueue the other oblets to scan later.
			// Some oblets may be in b's scalar tail, but
			// these will be marked as "no more pointers",
			// so we'll drop out immediately when we go to
			// scan those.
			// 译：排队等候其他问题稍后扫描。一些问题可能在b的标量尾部，
			// 译：但这些问题将被标记为“不再有指针”，所以当我们去扫描这些问题时，我们会立即退出。
			// 注：存疑？mallocgc时，32k就已经进入大对象分配了，即单一span仅存在一个对象，此处意义何在？
			for oblet := b + maxObletBytes; oblet < s.base()+s.elemsize; oblet += maxObletBytes {
				if !gcw.putFast(oblet) { // 注：加入gc队列
					gcw.put(oblet)
				}
			}
		}

		// Compute the size of the oblet. Since this object
		// must be a large object, s.base() is the beginning
		// of the object.
		n = s.base() + s.elemsize - b
		if n > maxObletBytes {
			n = maxObletBytes
		}
	}

	hbits := heapBitsForAddr(b, n)
	var scanSize uintptr
	for {
		var addr uintptr
		if hbits, addr = hbits.nextFast(); addr == 0 { // 注：跳过无指针空间
			if hbits, addr = hbits.next(); addr == 0 {
				break
			}
		}

		// Keep track of farthest pointer we found, so we can
		// update heapScanWork. TODO: is there a better metric,
		// now that we can skip scalar portions pretty efficiently?
		scanSize = addr - b + goarch.PtrSize

		// Work here is duplicated in scanblock and above.
		// If you make changes here, make changes there too.
		obj := *(*uintptr)(unsafe.Pointer(addr)) // 注：该地址的值，即指向的堆对象地址

		// At this point we have extracted the next potential pointer.
		// Quickly filter out nil and pointers back to the current object.
		if obj != 0 && obj-b >= n { // 注：如果地址是有效的
			// Test if obj points into the Go heap and, if so,
			// mark the object.
			//
			// Note that it's possible for findObject to
			// fail if obj points to a just-allocated heap
			// object because of a race with growing the
			// heap. In this case, we know the object was
			// just allocated and hence will be marked by
			// allocation itself.
			if obj, span, objIndex := findObject(obj, b, addr-b); obj != 0 { // 注：找到目标对象并标灰
				greyobject(obj, b, addr-b, span, gcw, objIndex)
			}
		}
	}
	gcw.bytesMarked += uint64(n)
	gcw.heapScanWork += int64(scanSize)
}

// scanConservative scans block [b, b+n) conservatively, treating any
// pointer-like value in the block as a pointer.
// 译：scanConservative保守地扫描块[b，b+n），将块中任何类似指针的值视为指针。
//
// If ptrmask != nil, only words that are marked in ptrmask are
// considered as potential pointers.
// 译：如果ptrmask!=nil，只有在ptrmask中标记的单词才被视为潜在指针。
//
// If state != nil, it's assumed that [b, b+n) is a block in the stack
// and may contain pointers to stack objects.
// 译：如果state!=nil，假设[b，b+n）是堆栈中的一个块，并且可能包含指向堆栈对象的指针。
func scanConservative(b, n uintptr, ptrmask *uint8, gcw *gcWork, state *stackScanState) {
	if debugScanConservative {
		printlock()
		print("conservatively scanning [", hex(b), ",", hex(b+n), ")\n")
		hexdumpWords(b, b+n, func(p uintptr) byte {
			if ptrmask != nil {
				word := (p - b) / goarch.PtrSize
				bits := *addb(ptrmask, word/8)
				if (bits>>(word%8))&1 == 0 {
					return '$'
				}
			}

			val := *(*uintptr)(unsafe.Pointer(p))
			if state != nil && state.stack.lo <= val && val < state.stack.hi {
				return '@'
			}

			span := spanOfHeap(val)
			if span == nil {
				return ' '
			}
			idx := span.objIndex(val)
			if span.isFree(idx) {
				return ' '
			}
			return '*'
		})
		printunlock()
	}

	for i := uintptr(0); i < n; i += goarch.PtrSize {
		if ptrmask != nil { // 注：存在gc掩码
			word := i / goarch.PtrSize
			bits := *addb(ptrmask, word/8)
			if bits == 0 { // 注：不存在指针
				// Skip 8 words (the loop increment will do the 8th)
				//
				// This must be the first time we've
				// seen this word of ptrmask, so i
				// must be 8-word-aligned, but check
				// our reasoning just in case.
				if i%(goarch.PtrSize*8) != 0 {
					throw("misaligned mask")
				}
				i += goarch.PtrSize*8 - goarch.PtrSize // 注：前进8组
				continue
			}
			if (bits>>(word%8))&1 == 0 { // 注：当前无指针，直接取下一组
				continue
			}
		}
		// 注：没有传入ptrmask，则按照指针处理(保守处理)
		// 注：但是由于会有可能不是指针，因此进行合法性验证，如果通过验证，则将目标对象标灰

		val := *(*uintptr)(unsafe.Pointer(b + i)) // 注：取得当前指针的值，即目标对象

		// Check if val points into the stack.
		if state != nil && state.stack.lo <= val && val < state.stack.hi {
			// val may point to a stack object. This
			// object may be dead from last cycle and
			// hence may contain pointers to unallocated
			// objects, but unlike heap objects we can't
			// tell if it's already dead. Hence, if all
			// pointers to this object are from
			// conservative scanning, we have to scan it
			// defensively, too.
			// 译：val可以指向堆栈对象。这个对象可能从上一个循环开始就死了，
			// 译：因此可能包含指向未分配对象的指针，但与堆对象不同的是，
			// 译：我们无法判断它是否已经死了。因此，如果指向该对象的所有指针都来自保守扫描，
			// 译：我们也必须对其进行防御扫描。
			state.putPtr(val, true) // 注：如果在栈指针范围内，则按照栈指针处理，依旧是保守扫描
			continue
		}
		// 注：不是栈指针，则尝试进行堆对象标灰

		// Check if val points to a heap span.
		span := spanOfHeap(val) // 注：取得指针的span
		if span == nil {
			continue
		}

		// Check if val points to an allocated object.
		idx := span.objIndex(val) // 注：检查指针是否有效
		if span.isFree(idx) {
			continue
		}

		// val points to an allocated object. Mark it.
		obj := span.base() + idx*span.elemsize
		greyobject(obj, b, i, span, gcw, idx) // 注：如果值指向了一个堆对象，则将其标灰(尽管它可能不是指针)
	}
}

// Shade the object if it isn't already.
// The object is not nil and known to be in the heap.
// Preemption must be disabled.
//
//go:nowritebarrier
func shade(b uintptr) {
	if obj, span, objIndex := findObject(b, 0, 0); obj != 0 {
		gcw := &getg().m.p.ptr().gcw
		greyobject(obj, 0, 0, span, gcw, objIndex)
	}
}

// obj is the start of an object with mark mbits.
// If it isn't already marked, mark it and enqueue into gcw.
// base and off are for debugging only and could be removed.
//
// See also wbBufFlush1, which partially duplicates this logic.
//
//go:nowritebarrierrec
func greyobject(obj, base, off uintptr, span *mspan, gcw *gcWork, objIndex uintptr) { // 注：置为灰色
	// obj should be start of allocation, and so must be at least pointer-aligned.
	if obj&(goarch.PtrSize-1) != 0 {
		throw("greyobject: obj not pointer-aligned")
	}
	mbits := span.markBitsForIndex(objIndex) // 注：取得gc位图

	if useCheckmark {
		if setCheckmark(obj, base, off, mbits) {
			// Already marked.
			return
		}
	} else {
		if debug.gccheckmark > 0 && span.isFree(objIndex) {
			print("runtime: marking free object ", hex(obj), " found at *(", hex(base), "+", hex(off), ")\n")
			gcDumpObject("base", base, off)
			gcDumpObject("obj", obj, ^uintptr(0))
			getg().m.traceback = 2
			throw("marking free object")
		}

		// If marked we have nothing to do.
		if mbits.isMarked() { // 注：如果已标记则跳过
			return
		}
		mbits.setMarked() // 注：标记为黑色

		// Mark span.
		arena, pageIdx, pageMask := pageIndexOf(span.base())
		if arena.pageMarks[pageIdx]&pageMask == 0 {
			atomic.Or8(&arena.pageMarks[pageIdx], pageMask) // 注：标记span
		}

		// If this is a noscan object, fast-track it to black
		// instead of greying it.
		if span.spanclass.noscan() { // 注：无指针区不会成为灰色
			gcw.bytesMarked += uint64(span.elemsize)
			return
		}
	}

	// We're adding obj to P's local workbuf, so it's likely
	// this object will be processed soon by the same P.
	// Even if the workbuf gets flushed, there will likely still be
	// some benefit on platforms with inclusive shared caches.
	// 译：我们正在将obj添加到P的本地工作区，因此这个对象很可能很快就会被同一个P处理。
	// 译：即使工作区被刷新，在具有包含式共享缓存的平台上仍然可能会有一些好处。
	sys.Prefetch(obj)
	// Queue the obj for scanning.
	if !gcw.putFast(obj) { // 注：加入扫描队列，即标记为灰色
		gcw.put(obj)
	}
}

// gcDumpObject dumps the contents of obj for debugging and marks the
// field at byte offset off in obj.
func gcDumpObject(label string, obj, off uintptr) {
	s := spanOf(obj)
	print(label, "=", hex(obj))
	if s == nil {
		print(" s=nil\n")
		return
	}
	print(" s.base()=", hex(s.base()), " s.limit=", hex(s.limit), " s.spanclass=", s.spanclass, " s.elemsize=", s.elemsize, " s.state=")
	if state := s.state.get(); 0 <= state && int(state) < len(mSpanStateNames) {
		print(mSpanStateNames[state], "\n")
	} else {
		print("unknown(", state, ")\n")
	}

	skipped := false
	size := s.elemsize
	if s.state.get() == mSpanManual && size == 0 {
		// We're printing something from a stack frame. We
		// don't know how big it is, so just show up to an
		// including off.
		size = off + goarch.PtrSize
	}
	for i := uintptr(0); i < size; i += goarch.PtrSize {
		// For big objects, just print the beginning (because
		// that usually hints at the object's type) and the
		// fields around off.
		if !(i < 128*goarch.PtrSize || off-16*goarch.PtrSize < i && i < off+16*goarch.PtrSize) {
			skipped = true
			continue
		}
		if skipped {
			print(" ...\n")
			skipped = false
		}
		print(" *(", label, "+", i, ") = ", hex(*(*uintptr)(unsafe.Pointer(obj + i))))
		if i == off {
			print(" <==")
		}
		print("\n")
	}
	if skipped {
		print(" ...\n")
	}
}

// gcmarknewobject marks a newly allocated object black. obj must
// not contain any non-nil pointers.
// 译：gcmarknewobject将新分配的对象标记为黑色。obj不能包含任何非零指针。
//
// This is nosplit so it can manipulate a gcWork without preemption.
// 译：这是不分割的，因此它可以在不被抢占的情况下操作gcWork。
//
//go:nowritebarrier
//go:nosplit
func gcmarknewobject(span *mspan, obj, size uintptr) {
	if useCheckmark { // The world should be stopped so this should not happen.
		throw("gcmarknewobject called while doing checkmark")
	}

	// Mark object.
	objIndex := span.objIndex(obj)
	span.markBitsForIndex(objIndex).setMarked() // 注：标记为黑色，此时对象内全部数据均为空，因此不需要标记灰

	// Mark span.
	arena, pageIdx, pageMask := pageIndexOf(span.base())
	if arena.pageMarks[pageIdx]&pageMask == 0 { // 注：如果span没有标记为黑色，则标记为黑色
		atomic.Or8(&arena.pageMarks[pageIdx], pageMask)
	}

	gcw := &getg().m.p.ptr().gcw
	gcw.bytesMarked += uint64(size)
}

// gcMarkTinyAllocs greys all active tiny alloc blocks.
//
// The world must be stopped.
func gcMarkTinyAllocs() { // 注：对tiny分配区进行标记
	assertWorldStopped()

	for _, p := range allp {
		c := p.mcache
		if c == nil || c.tiny == 0 {
			continue
		}
		// 注：tiny地址区不扫码，直接标记为黑色
		_, span, objIndex := findObject(c.tiny, 0, 0)
		gcw := &p.gcw
		// 注：此处虽然标灰，但是由于tiny区属于无指针区不会被扫描，因此仅会成为黑色
		greyobject(c.tiny, 0, 0, span, gcw, objIndex)
	}
}
