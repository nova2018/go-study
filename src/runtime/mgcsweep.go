// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Garbage collector: sweeping

// The sweeper consists of two different algorithms:
//
// * The object reclaimer finds and frees unmarked slots in spans. It
//   can free a whole span if none of the objects are marked, but that
//   isn't its goal. This can be driven either synchronously by
//   mcentral.cacheSpan for mcentral spans, or asynchronously by
//   sweepone, which looks at all the mcentral lists.
//
// * The span reclaimer looks for spans that contain no marked objects
//   and frees whole spans. This is a separate algorithm because
//   freeing whole spans is the hardest task for the object reclaimer,
//   but is critical when allocating new spans. The entry point for
//   this is mheap_.reclaim and it's driven by a sequential scan of
//   the page marks bitmap in the heap arenas.
//
// Both algorithms ultimately call mspan.sweep, which sweeps a single
// heap span.

package runtime

import (
	"runtime/internal/atomic"
	"unsafe"
)

var sweep sweepdata

// State of background sweep.
type sweepdata struct {
	lock   mutex
	g      *g
	parked bool

	nbgsweep    uint32
	npausesweep uint32

	// active tracks outstanding sweepers and the sweep
	// termination condition.
	active activeSweep

	// centralIndex is the current unswept span class.
	// It represents an index into the mcentral span
	// sets. Accessed and updated via its load and
	// update methods. Not protected by a lock.
	//
	// Reset at mark termination.
	// Used by mheap.nextSpanForSweep.
	centralIndex sweepClass
}

// sweepClass is a spanClass and one bit to represent whether we're currently
// sweeping partial or full spans.
type sweepClass uint32

const (
	numSweepClasses            = numSpanClasses * 2
	sweepClassDone  sweepClass = sweepClass(^uint32(0))
)

func (s *sweepClass) load() sweepClass {
	return sweepClass(atomic.Load((*uint32)(s)))
}

func (s *sweepClass) update(sNew sweepClass) {
	// Only update *s if its current value is less than sNew,
	// since *s increases monotonically.
	sOld := s.load()
	for sOld < sNew && !atomic.Cas((*uint32)(s), uint32(sOld), uint32(sNew)) {
		sOld = s.load()
	}
	// TODO(mknyszek): This isn't the only place we have
	// an atomic monotonically increasing counter. It would
	// be nice to have an "atomic max" which is just implemented
	// as the above on most architectures. Some architectures
	// like RISC-V however have native support for an atomic max.
}

func (s *sweepClass) clear() {
	atomic.Store((*uint32)(s), 0)
}

// split returns the underlying span class as well as
// whether we're interested in the full or partial
// unswept lists for that class, indicated as a boolean
// (true means "full").
func (s sweepClass) split() (spc spanClass, full bool) {
	return spanClass(s >> 1), s&1 == 0
}

// nextSpanForSweep finds and pops the next span for sweeping from the
// central sweep buffers. It returns ownership of the span to the caller.
// Returns nil if no such span exists.
func (h *mheap) nextSpanForSweep() *mspan { // 注：从mcentral返回一个待清扫的span
	sg := h.sweepgen
	for sc := sweep.centralIndex.load(); sc < numSweepClasses; sc++ {
		spc, full := sc.split()
		c := &h.central[spc].mcentral
		var s *mspan
		if full {
			s = c.fullUnswept(sg).pop()
		} else {
			s = c.partialUnswept(sg).pop()
		}
		if s != nil {
			// Write down that we found something so future sweepers
			// can start from here.
			sweep.centralIndex.update(sc)
			return s
		}
	}
	// Write down that we found nothing.
	sweep.centralIndex.update(sweepClassDone)
	return nil
}

const sweepDrainedMask = 1 << 31

// activeSweep is a type that captures whether sweeping
// is done, and whether there are any outstanding sweepers.
// 译：ActiveSweep是一种类型，它捕获是否完成了清扫，以及是否有未完成的清扫器
//
// Every potential sweeper must call begin() before they look
// for work, and end() after they've finished sweeping.
// 译：每个潜在的清扫者在寻找工作之前都必须调用Begin()，在完成清扫之后必须调用end()。
type activeSweep struct {
	// state is divided into two parts.
	// 译：状态分为两部分
	//
	// The top bit (masked by sweepDrainedMask) is a boolean
	// value indicating whether all the sweep work has been
	// drained from the queue.
	// 译：高位(由sweepDrainedMask掩码)是一个布尔值，指示是否所有清理工作都已从队列中排出
	//
	// The rest of the bits are a counter, indicating the
	// number of outstanding concurrent sweepers.
	// 译：其余的位是计数器，表示未完成的并发清扫器的数量。
	state atomic.Uint32
}

// begin registers a new sweeper. Returns a sweepLocker
// for acquiring spans for sweeping. Any outstanding sweeper blocks
// sweep termination.
// 译：begin注册新的清扫器。返回用于获取清扫span的SweepLocker。任何未完成的清扫器都会阻止清扫终止
//
// If the sweepLocker is invalid, the caller can be sure that all
// outstanding sweep work has been drained, so there is nothing left
// to sweep. Note that there may be sweepers currently running, so
// this does not indicate that all sweeping has completed.
// 译：如果SweepLocker无效，调用方可以确保所有未完成的清除工作都已耗尽，因此没有剩余的清除工作。
// 译：请注意，当前可能有清扫器正在运行，因此这并不表示所有清扫器都已完成
//
// Even if the sweepLocker is invalid, its sweepGen is always valid.
// 译：即使SweepLocker无效，其SweepGen也始终有效。
func (a *activeSweep) begin() sweepLocker {
	for {
		state := a.state.Load()
		if state&sweepDrainedMask != 0 { // 注：没有剩余清扫任务
			return sweepLocker{mheap_.sweepgen, false}
		}
		if a.state.CompareAndSwap(state, state+1) { // 注：增加一个清扫器
			return sweepLocker{mheap_.sweepgen, true}
		}
	}
}

// end deregisters a sweeper. Must be called once for each time
// begin is called if the sweepLocker is valid.
func (a *activeSweep) end(sl sweepLocker) {
	if sl.sweepGen != mheap_.sweepgen {
		throw("sweeper left outstanding across sweep generations")
	}
	for {
		state := a.state.Load()
		if (state&^sweepDrainedMask)-1 >= sweepDrainedMask {
			throw("mismatched begin/end of activeSweep")
		}
		if a.state.CompareAndSwap(state, state-1) {
			if state != sweepDrainedMask {
				return
			}
			if debug.gcpacertrace > 0 {
				live := gcController.heapLive.Load()
				print("pacer: sweep done at heap size ", live>>20, "MB; allocated ", (live-mheap_.sweepHeapLiveBasis)>>20, "MB during sweep; swept ", mheap_.pagesSwept.Load(), " pages at ", mheap_.sweepPagesPerByte, " pages/byte\n")
			}
			return
		}
	}
}

// markDrained marks the active sweep cycle as having drained
// all remaining work. This is safe to be called concurrently
// with all other methods of activeSweep, though may race.
//
// Returns true if this call was the one that actually performed
// the mark.
func (a *activeSweep) markDrained() bool {
	for {
		state := a.state.Load()
		if state&sweepDrainedMask != 0 { // 还有剩余清扫器
			return false
		}
		if a.state.CompareAndSwap(state, state|sweepDrainedMask) { // 标记清扫结束
			return true
		}
	}
}

// sweepers returns the current number of active sweepers.
func (a *activeSweep) sweepers() uint32 {
	return a.state.Load() &^ sweepDrainedMask
}

// isDone returns true if all sweep work has been drained and no more
// outstanding sweepers exist. That is, when the sweep phase is
// completely done.
func (a *activeSweep) isDone() bool {
	return a.state.Load() == sweepDrainedMask
}

// reset sets up the activeSweep for the next sweep cycle.
//
// The world must be stopped.
func (a *activeSweep) reset() {
	assertWorldStopped()
	a.state.Store(0) // 注：准备下一轮清扫
}

// finishsweep_m ensures that all spans are swept.
//
// The world must be stopped. This ensures there are no sweeps in
// progress.
//
//go:nowritebarrier
func finishsweep_m() {
	assertWorldStopped()

	// Sweeping must be complete before marking commences, so
	// sweep any unswept spans. If this is a concurrent GC, there
	// shouldn't be any spans left to sweep, so this should finish
	// instantly. If GC was forced before the concurrent sweep
	// finished, there may be spans to sweep.
	for sweepone() != ^uintptr(0) { // 注：完成清扫任务
		sweep.npausesweep++
	}

	// Make sure there aren't any outstanding sweepers left.
	// At this point, with the world stopped, it means one of two
	// things. Either we were able to preempt a sweeper, or that
	// a sweeper didn't call sweep.active.end when it should have.
	// Both cases indicate a bug, so throw.
	if sweep.active.sweepers() != 0 {
		throw("active sweepers found at start of mark phase")
	}

	// Reset all the unswept buffers, which should be empty.
	// Do this in sweep termination as opposed to mark termination
	// so that we can catch unswept spans and reclaim blocks as
	// soon as possible.
	sg := mheap_.sweepgen
	for i := range mheap_.central { // 注：重置待清扫列表
		c := &mheap_.central[i].mcentral
		c.partialUnswept(sg).reset()
		c.fullUnswept(sg).reset()
	}

	// Sweeping is done, so if the scavenger isn't already awake,
	// wake it up. There's definitely work for it to do at this
	// point.
	scavenger.wake()

	nextMarkBitArenaEpoch()
}

func bgsweep(c chan int) {
	sweep.g = getg()

	lockInit(&sweep.lock, lockRankSweep)
	lock(&sweep.lock)
	sweep.parked = true
	c <- 1
	goparkunlock(&sweep.lock, waitReasonGCSweepWait, traceEvGoBlock, 1)

	for {
		// bgsweep attempts to be a "low priority" goroutine by intentionally
		// yielding time. It's OK if it doesn't run, because goroutines allocating
		// memory will sweep and ensure that all spans are swept before the next
		// GC cycle. We really only want to run when we're idle.
		//
		// However, calling Gosched after each span swept produces a tremendous
		// amount of tracing events, sometimes up to 50% of events in a trace. It's
		// also inefficient to call into the scheduler so much because sweeping a
		// single span is in general a very fast operation, taking as little as 30 ns
		// on modern hardware. (See #54767.)
		//
		// As a result, bgsweep sweeps in batches, and only calls into the scheduler
		// at the end of every batch. Furthermore, it only yields its time if there
		// isn't spare idle time available on other cores. If there's available idle
		// time, helping to sweep can reduce allocation latencies by getting ahead of
		// the proportional sweeper and having spans ready to go for allocation.
		const sweepBatchSize = 10
		nSwept := 0
		for sweepone() != ^uintptr(0) {
			sweep.nbgsweep++
			nSwept++
			if nSwept%sweepBatchSize == 0 {
				goschedIfBusy()
			}
		}
		for freeSomeWbufs(true) {
			// N.B. freeSomeWbufs is already batched internally.
			goschedIfBusy()
		}
		lock(&sweep.lock)
		if !isSweepDone() {
			// This can happen if a GC runs between
			// gosweepone returning ^0 above
			// and the lock being acquired.
			unlock(&sweep.lock)
			continue
		}
		sweep.parked = true
		goparkunlock(&sweep.lock, waitReasonGCSweepWait, traceEvGoBlock, 1)
	}
}

// sweepLocker acquires sweep ownership of spans.
type sweepLocker struct {
	// sweepGen is the sweep generation of the heap.
	sweepGen uint32
	valid    bool
}

// sweepLocked represents sweep ownership of a span.
type sweepLocked struct {
	*mspan
}

// tryAcquire attempts to acquire sweep ownership of span s. If it
// successfully acquires ownership, it blocks sweep completion.
// 译：tryAcquire试图获取span的清扫所有权。如果成功获取所有权，它将阻止清扫完成。
func (l *sweepLocker) tryAcquire(s *mspan) (sweepLocked, bool) {
	if !l.valid {
		throw("use of invalid sweepLocker")
	}
	// Check before attempting to CAS.
	if atomic.Load(&s.sweepgen) != l.sweepGen-2 {
		return sweepLocked{}, false
	}
	// Attempt to acquire sweep ownership of s.
	if !atomic.Cas(&s.sweepgen, l.sweepGen-2, l.sweepGen-1) {
		return sweepLocked{}, false
	}
	return sweepLocked{s}, true
}

// sweepone sweeps some unswept heap span and returns the number of pages returned
// to the heap, or ^uintptr(0) if there was nothing to sweep.
func sweepone() uintptr { // 注：处理清扫
	gp := getg()

	// Increment locks to ensure that the goroutine is not preempted
	// in the middle of sweep thus leaving the span in an inconsistent state for next GC
	gp.m.locks++

	// TODO(austin): sweepone is almost always called in a loop;
	// lift the sweepLocker into its callers.
	sl := sweep.active.begin() // 注：增加清扫器
	if !sl.valid {             // 注：没有可执行的任务
		gp.m.locks--
		return ^uintptr(0)
	}

	// Find a span to sweep.
	npages := ^uintptr(0)
	var noMoreWork bool
	for {
		s := mheap_.nextSpanForSweep() // 注：取得下一个待清扫的span
		if s == nil {                  // 注：没有新的span，则清扫完成
			noMoreWork = sweep.active.markDrained()
			break
		}
		if state := s.state.get(); state != mSpanInUse {
			// This can happen if direct sweeping already
			// swept this span, but in that case the sweep
			// generation should always be up-to-date.
			if !(s.sweepgen == sl.sweepGen || s.sweepgen == sl.sweepGen+3) {
				print("runtime: bad span s.state=", state, " s.sweepgen=", s.sweepgen, " sweepgen=", sl.sweepGen, "\n")
				throw("non in-use span in unswept list")
			}
			continue
		}
		if s, ok := sl.tryAcquire(s); ok { // 注：尝试获取清扫锁
			// Sweep the span we found.
			npages = s.npages
			if s.sweep(false) { // 注：清扫
				// 注：span已被释放
				// Whole span was freed. Count it toward the
				// page reclaimer credit since these pages can
				// now be used for span allocation.
				mheap_.reclaimCredit.Add(npages)
			} else {
				// 注：span未被释放
				// Span is still in-use, so this returned no
				// pages to the heap and the span needs to
				// move to the swept in-use list.
				npages = 0
			}
			break
		}
	}
	sweep.active.end(sl)

	if noMoreWork {
		// The sweep list is empty. There may still be
		// concurrent sweeps running, but we're at least very
		// close to done sweeping.

		// Move the scavenge gen forward (signaling
		// that there's new work to do) and wake the scavenger.
		//
		// The scavenger is signaled by the last sweeper because once
		// sweeping is done, we will definitely have useful work for
		// the scavenger to do, since the scavenger only runs over the
		// heap once per GC cycle. This update is not done during sweep
		// termination because in some cases there may be a long delay
		// between sweep done and sweep termination (e.g. not enough
		// allocations to trigger a GC) which would be nice to fill in
		// with scavenging work.
		if debug.scavtrace > 0 {
			systemstack(func() {
				lock(&mheap_.lock)
				released := atomic.Loaduintptr(&mheap_.pages.scav.released)
				printScavTrace(released, false)
				atomic.Storeuintptr(&mheap_.pages.scav.released, 0)
				unlock(&mheap_.lock)
			})
		}
		scavenger.ready()
	}

	gp.m.locks--
	return npages
}

// isSweepDone reports whether all spans are swept.
//
// Note that this condition may transition from false to true at any
// time as the sweeper runs. It may transition from true to false if a
// GC runs; to prevent that the caller must be non-preemptible or must
// somehow block GC progress.
func isSweepDone() bool {
	return sweep.active.isDone()
}

// Returns only when span s has been swept.
//
//go:nowritebarrier
func (s *mspan) ensureSwept() {
	// Caller must disable preemption.
	// Otherwise when this function returns the span can become unswept again
	// (if GC is triggered on another goroutine).
	gp := getg()
	if gp.m.locks == 0 && gp.m.mallocing == 0 && gp != gp.m.g0 {
		throw("mspan.ensureSwept: m is not locked")
	}

	// If this operation fails, then that means that there are
	// no more spans to be swept. In this case, either s has already
	// been swept, or is about to be acquired for sweeping and swept.
	sl := sweep.active.begin()
	if sl.valid {
		// The caller must be sure that the span is a mSpanInUse span.
		if s, ok := sl.tryAcquire(s); ok {
			s.sweep(false)
			sweep.active.end(sl)
			return
		}
		sweep.active.end(sl)
	}

	// Unfortunately we can't sweep the span ourselves. Somebody else
	// got to it first. We don't have efficient means to wait, but that's
	// OK, it will be swept fairly soon.
	for {
		spangen := atomic.Load(&s.sweepgen)
		if spangen == sl.sweepGen || spangen == sl.sweepGen+3 {
			break
		}
		osyield()
	}
}

// Sweep frees or collects finalizers for blocks not marked in the mark phase.
// It clears the mark bits in preparation for the next GC round.
// Returns true if the span was returned to heap.
// If preserve=true, don't return it to heap nor relink in mcentral lists;
// caller takes care of it.
// 译：清除释放或收集在标记阶段未标记的块的终结器。
// 译：它清除标记位，为下一轮GC做准备。
// 译：如果span返回到堆，则返回TRUE。
// 译：如果preserve=true，则不将其返回到堆，也不在mCentral列表中重新链接；调用者会处理它。
func (sl *sweepLocked) sweep(preserve bool) bool { // 注：清扫span
	// It's critical that we enter this function with preemption disabled,
	// GC must not start while we are in the middle of this function.
	// 译：至关重要的是，我们在禁用抢占的情况下进入该函数，当我们处于该函数的中间时，GC不能启动。
	gp := getg()
	if gp.m.locks == 0 && gp.m.mallocing == 0 && gp != gp.m.g0 {
		throw("mspan.sweep: m is not locked")
	}

	s := sl.mspan // 注：目标span
	if !preserve {
		// We'll release ownership of this span. Nil it out to
		// prevent the caller from accidentally using it.
		// 译：我们将释放此span的所有权。去掉它以防止调用者意外使用它。
		sl.mspan = nil
	}

	sweepgen := mheap_.sweepgen
	if state := s.state.get(); state != mSpanInUse || s.sweepgen != sweepgen-1 {
		// 注：s.sweepgen == sweepgen-1 表示span正在被扫描
		print("mspan.sweep: state=", state, " sweepgen=", s.sweepgen, " mheap.sweepgen=", sweepgen, "\n")
		throw("mspan.sweep: bad span state")
	}

	if trace.enabled {
		traceGCSweepSpan(s.npages * _PageSize)
	}

	mheap_.pagesSwept.Add(int64(s.npages)) // 注：堆的扫描页数增加

	spc := s.spanclass
	size := s.elemsize

	// The allocBits indicate which unmarked objects don't need to be
	// processed since they were free at the end of the last GC cycle
	// and were not allocated since then.
	// If the allocBits index is >= s.freeindex and the bit
	// is not marked then the object remains unallocated
	// since the last GC.
	// This situation is analogous to being on a freelist.
	// 译：allocBits指示哪些未标记的对象不需要处理，因为它们在上一个GC周期结束时是空闲的，并且此后没有分配。
	// 译：如果allocBits索引>=s.freeindex并且该位未被标记，则自上次GC以来该对象保持未分配状态。
	// 译：这种情况类似于被列入自由名单。

	// Unlink & free special records for any objects we're about to free.
	// 译：取消链接并释放我们要释放的任何对象的特殊记录。
	// Two complications here:
	// 译：这里有两个并发症：
	// 1. An object can have both finalizer and profile special records.
	//    In such case we need to queue finalizer for execution,
	//    mark the object as live and preserve the profile special.
	// 译：1.一个对象可以同时具有终结器和配置文件特殊记录。
	// 译：  在这种情况下，我们需要对终结器进行排队执行，将对象标记为活动，并将配置文件保留为特殊配置文件。
	// 2. A tiny object can have several finalizers setup for different offsets.
	//    If such object is not marked, we need to queue all finalizers at once.
	// 译：2.一个小对象可以为不同的偏移设置多个终结器。
	// 译：  如果没有标记这样的对象，我们需要同时对所有终结器进行排队
	// Both 1 and 2 are possible at the same time.
	// 译：1和2同时是可能的。
	hadSpecials := s.specials != nil
	siter := newSpecialsIter(s) // 注：设置span的specials迭代器
	for siter.valid() {         // 注：迭代specials
		// A finalizer can be set for an inner byte of an object, find object beginning.
		// 译：终结器可以设置在对象的内部字节，查找对象开头。
		objIndex := uintptr(siter.s.offset) / size
		p := s.base() + objIndex*size         // 注：取得对象的指针
		mbits := s.markBitsForIndex(objIndex) // 注：跟进对象索引获取对应的gc位图
		if !mbits.isMarked() {                // 注：如果是白色的？
			// This object is not marked and has at least one special record.
			// Pass 1: see if it has at least one finalizer.
			// 译：此对象没有标记，并且至少有一个特殊记录。
			// 译：步骤1：查看它是否至少有一个终结器。
			hasFin := false
			endOffset := p - s.base() + size // 注：endOffset = objIndex*size+size, 即指向下一个对象的偏移量
			for tmp := siter.s; tmp != nil && uintptr(tmp.offset) < endOffset; tmp = tmp.next {
				// 注：循环没看懂，难道sister.s是首地址，specials链表是连续空间？需要看下specials的赋值过程
				if tmp.kind == _KindSpecialFinalizer {
					// Stop freeing of object if it has a finalizer.
					// 译：如果对象具有终结器，则停止释放该对象。
					mbits.setMarkedNonAtomic() // 注：标记为黑色？
					hasFin = true
					break
				}
			}
			// Pass 2: queue all finalizers _or_ handle profile record.
			// 译：步骤2：将所有终结器_or_处理配置文件记录排入队列。
			for siter.valid() && uintptr(siter.s.offset) < endOffset {
				// Find the exact byte for which the special was setup
				// (as opposed to object beginning).
				special := siter.s
				p := s.base() + uintptr(special.offset)
				if special.kind == _KindSpecialFinalizer || !hasFin {
					siter.unlinkAndNext()
					freeSpecial(special, unsafe.Pointer(p), size)
				} else {
					// The object has finalizers, so we're keeping it alive.
					// All other specials only apply when an object is freed,
					// so just keep the special record.
					siter.next()
				}
			}
		} else {
			// object is still live
			if siter.s.kind == _KindSpecialReachable {
				special := siter.unlinkAndNext()
				(*specialReachable)(unsafe.Pointer(special)).reachable = true
				freeSpecial(special, unsafe.Pointer(p), size)
			} else {
				// keep special record
				siter.next()
			}
		}
	}
	if hadSpecials && s.specials == nil {
		spanHasNoSpecials(s)
	}

	if debug.allocfreetrace != 0 || debug.clobberfree != 0 || raceenabled || msanenabled || asanenabled {
		// Find all newly freed objects. This doesn't have to
		// efficient; allocfreetrace has massive overhead.
		mbits := s.markBitsForBase()
		abits := s.allocBitsForIndex(0)
		for i := uintptr(0); i < s.nelems; i++ {
			if !mbits.isMarked() && (abits.index < s.freeindex || abits.isMarked()) {
				x := s.base() + i*s.elemsize
				if debug.allocfreetrace != 0 {
					tracefree(unsafe.Pointer(x), size)
				}
				if debug.clobberfree != 0 {
					clobberfree(unsafe.Pointer(x), size)
				}
				// User arenas are handled on explicit free.
				if raceenabled && !s.isUserArenaChunk {
					racefree(unsafe.Pointer(x), size)
				}
				if msanenabled && !s.isUserArenaChunk {
					msanfree(unsafe.Pointer(x), size)
				}
				if asanenabled && !s.isUserArenaChunk {
					asanpoison(unsafe.Pointer(x), size)
				}
			}
			mbits.advance()
			abits.advance()
		}
	}

	// Check for zombie objects.
	if s.freeindex < s.nelems {
		// Everything < freeindex is allocated and hence
		// cannot be zombies.
		//
		// Check the first bitmap byte, where we have to be
		// careful with freeindex.
		obj := s.freeindex
		if (*s.gcmarkBits.bytep(obj / 8)&^*s.allocBits.bytep(obj / 8))>>(obj%8) != 0 {
			s.reportZombies()
		}
		// Check remaining bytes.
		for i := obj/8 + 1; i < divRoundUp(s.nelems, 8); i++ {
			if *s.gcmarkBits.bytep(i)&^*s.allocBits.bytep(i) != 0 {
				s.reportZombies()
			}
		}
	}

	// Count the number of free objects in this span.
	nalloc := uint16(s.countAlloc()) // 注：计算span中有多少个黑色对象
	nfreed := s.allocCount - nalloc  // 注：本次释放对象个数
	if nalloc > s.allocCount {       // 注：清扫后比原来还多是不正常的
		// The zombie check above should have caught this in
		// more detail.
		print("runtime: nelems=", s.nelems, " nalloc=", nalloc, " previous allocCount=", s.allocCount, " nfreed=", nfreed, "\n")
		throw("sweep increased allocation count")
	}

	// 注：重置对象分配状态
	s.allocCount = nalloc
	s.freeindex = 0 // reset allocation index to start of span.
	s.freeIndexForScan = 0
	if trace.enabled {
		getg().m.p.ptr().traceReclaimed += uintptr(nfreed) * s.elemsize
	}

	// gcmarkBits becomes the allocBits.
	// get a fresh cleared gcmarkBits in preparation for next GC
	// 译：gcmarkBits变成allocBits。
	// 译：获取新清除的gcmarkBits，为下一次GC做准备
	s.allocBits = s.gcmarkBits
	s.gcmarkBits = newMarkBits(s.nelems)

	// Initialize alloc bits cache.
	s.refillAllocCache(0) // 注：基于新的allocBits重新计算第一组allocCache

	// The span must be in our exclusive ownership until we update sweepgen,
	// check for potential races.
	if state := s.state.get(); state != mSpanInUse || s.sweepgen != sweepgen-1 {
		print("mspan.sweep: state=", state, " sweepgen=", s.sweepgen, " mheap.sweepgen=", sweepgen, "\n")
		throw("mspan.sweep: bad span state after sweep")
	}
	if s.sweepgen == sweepgen+1 || s.sweepgen == sweepgen+3 {
		throw("swept cached span")
	}

	// We need to set s.sweepgen = h.sweepgen only when all blocks are swept,
	// because of the potential for a concurrent free/SetFinalizer.
	// 译：我们只需要在所有块都被扫描时设置s.sweepgen=h.Sweepgen，因为可能会出现并发的空闲/SetFinalizer。
	//
	// But we need to set it before we make the span available for allocation
	// (return it to heap or mcentral), because allocation code assumes that a
	// span is already swept if available for allocation.
	// 译：但是，我们需要在使span可用于分配(将其返回到堆或mCentral)之前设置它，因为分配代码假设span已被扫描(如果可用于分配)
	//
	// Serialization point.
	// At this point the mark bits are cleared and allocation ready
	// to go so release the span.
	// 译：序列化点。此时，标记位被清除，分配准备就绪，因此释放跨度
	atomic.Store(&s.sweepgen, sweepgen)

	if s.isUserArenaChunk { // 注：是否在用户内存块
		if preserve {
			// This is a case that should never be handled by a sweeper that
			// preserves the span for reuse.
			throw("sweep: tried to preserve a user arena span")
		}
		if nalloc > 0 { // 注：如果依然有剩余对象
			// There still exist pointers into the span or the span hasn't been
			// freed yet. It's not ready to be reused. Put it back on the
			// full swept list for the next cycle.
			// 译：仍然存在指向该范围的指针，或者该范围尚未释放。它还没有准备好被重复使用。把它放回下一个周期的完整扫描列表中。
			mheap_.central[spc].mcentral.fullSwept(sweepgen).push(s)
			return false
		}

		// It's only at this point that the sweeper doesn't actually need to look
		// at this arena anymore, so subtract from pagesInUse now.
		mheap_.pagesInUse.Add(-s.npages)
		s.state.set(mSpanDead)

		// The arena is ready to be recycled. Remove it from the quarantine list
		// and place it on the ready list. Don't add it back to any sweep lists.
		systemstack(func() {
			// It's the arena code's responsibility to get the chunk on the quarantine
			// list by the time all references to the chunk are gone.
			if s.list != &mheap_.userArena.quarantineList {
				throw("user arena span is on the wrong list")
			}
			lock(&mheap_.lock)
			// 注：将span从quarantineList转移至readyList
			mheap_.userArena.quarantineList.remove(s)
			mheap_.userArena.readyList.insert(s)
			unlock(&mheap_.lock)
		})
		return false
	}

	if spc.sizeclass() != 0 {
		// Handle spans for small objects.
		// 译：控制小对象的span。
		if nfreed > 0 { // 注：释放了对象
			// Only mark the span as needing zeroing if we've freed any
			// objects, because a fresh span that had been allocated into,
			// wasn't totally filled, but then swept, still has all of its
			// free slots zeroed.
			// 译：如果我们释放了任何对象，则仅将范围标记为需要清零，因为已分配的新span并未完全填满，但随后被清扫，其所有空闲插槽仍被清零。
			s.needzero = 1
			stats := memstats.heapStats.acquire()
			atomic.Xadd64(&stats.smallFreeCount[spc.sizeclass()], int64(nfreed))
			memstats.heapStats.release()

			// Count the frees in the inconsistent, internal stats.
			gcController.totalFree.Add(int64(nfreed) * int64(s.elemsize))
		}
		if !preserve { // 注：允许归还堆
			// The caller may not have removed this span from whatever
			// unswept set its on but taken ownership of the span for
			// sweeping by updating sweepgen. If this span still is in
			// an unswept set, then the mcentral will pop it off the
			// set, check its sweepgen, and ignore it.
			if nalloc == 0 { // 注：剩余对象为0
				// Free totally free span directly back to the heap.
				mheap_.freeSpan(s) // 注：空span
				return true
			}
			// Return span back to the right mcentral list.
			if uintptr(nalloc) == s.nelems { // 注：已分配完
				// 注：进入已分满，已扫描队列
				mheap_.central[spc].mcentral.fullSwept(sweepgen).push(s)
			} else {
				// 注：进入未分满，已扫描队列
				mheap_.central[spc].mcentral.partialSwept(sweepgen).push(s)
			}
		}
	} else if !preserve { // 注：允许归还堆
		// Handle spans for large objects.
		if nfreed != 0 { // 注：如果释放了对象，此处是大对象span(单一对象span)，释放了对象，说明当前span空闲，则归还堆
			// Free large object span to heap.

			// NOTE(rsc,dvyukov): The original implementation of efence
			// in CL 22060046 used sysFree instead of sysFault, so that
			// the operating system would eventually give the memory
			// back to us again, so that an efence program could run
			// longer without running out of memory. Unfortunately,
			// calling sysFree here without any kind of adjustment of the
			// heap data structures means that when the memory does
			// come back to us, we have the wrong metadata for it, either in
			// the mspan structures or in the garbage collection bitmap.
			// Using sysFault here means that the program will run out of
			// memory fairly quickly in efence mode, but at least it won't
			// have mysterious crashes due to confused memory reuse.
			// It should be possible to switch back to sysFree if we also
			// implement and then call some kind of mheap.deleteSpan.
			if debug.efence > 0 {
				s.limit = 0 // prevent mlookup from finding this span
				sysFault(unsafe.Pointer(s.base()), size)
			} else {
				mheap_.freeSpan(s)
			}

			// Count the free in the consistent, external stats.
			stats := memstats.heapStats.acquire()
			atomic.Xadd64(&stats.largeFreeCount, 1)
			atomic.Xadd64(&stats.largeFree, int64(size))
			memstats.heapStats.release()

			// Count the free in the inconsistent, internal stats.
			gcController.totalFree.Add(int64(size))

			return true
		}

		// Add a large span directly onto the full+swept list.
		mheap_.central[spc].mcentral.fullSwept(sweepgen).push(s)
	}
	return false
}

// reportZombies reports any marked but free objects in s and throws.
//
// This generally means one of the following:
//
// 1. User code converted a pointer to a uintptr and then back
// unsafely, and a GC ran while the uintptr was the only reference to
// an object.
//
// 2. User code (or a compiler bug) constructed a bad pointer that
// points to a free slot, often a past-the-end pointer.
//
// 3. The GC two cycles ago missed a pointer and freed a live object,
// but it was still live in the last cycle, so this GC cycle found a
// pointer to that object and marked it.
func (s *mspan) reportZombies() {
	printlock()
	print("runtime: marked free object in span ", s, ", elemsize=", s.elemsize, " freeindex=", s.freeindex, " (bad use of unsafe.Pointer? try -d=checkptr)\n")
	mbits := s.markBitsForBase()
	abits := s.allocBitsForIndex(0)
	for i := uintptr(0); i < s.nelems; i++ {
		addr := s.base() + i*s.elemsize
		print(hex(addr))
		alloc := i < s.freeindex || abits.isMarked()
		if alloc {
			print(" alloc")
		} else {
			print(" free ")
		}
		if mbits.isMarked() {
			print(" marked  ")
		} else {
			print(" unmarked")
		}
		zombie := mbits.isMarked() && !alloc
		if zombie {
			print(" zombie")
		}
		print("\n")
		if zombie {
			length := s.elemsize
			if length > 1024 {
				length = 1024
			}
			hexdumpWords(addr, addr+length, nil)
		}
		mbits.advance()
		abits.advance()
	}
	throw("found pointer to free object")
}

// deductSweepCredit deducts sweep credit for allocating a span of
// size spanBytes. This must be performed *before* the span is
// allocated to ensure the system has enough credit. If necessary, it
// performs sweeping to prevent going in to debt. If the caller will
// also sweep pages (e.g., for a large allocation), it can pass a
// non-zero callerSweepPages to leave that many pages unswept.
// 译：reduceSweepCredit扣除分配大小为spanBytes的span的扫描信用
// 这必须在分配span之前执行，以确保系统有足够的信用
// 如有必要，它会进行彻底的清理，以防止陷入债务
// 如果调用方还将扫描页面（例如，对于大的分配），则它可以传递一个非零的callerWeepPages，使许多页面不被扫描
//
// deductSweepCredit makes a worst-case assumption that all spanBytes
// bytes of the ultimately allocated span will be available for object
// allocation.
// 译：reduceSweepCredit做了一个最坏的假设，即最终分配的span的所有spanBytes字节都将可用于对象分配
//
// deductSweepCredit is the core of the "proportional sweep" system.
// It uses statistics gathered by the garbage collector to perform
// enough sweeping so that all pages are swept during the concurrent
// sweep phase between GC cycles.
// 译：reduceSweepCredit是“比例扫描”系统的核心。它使用垃圾收集器收集的统计信息来执行足够的扫描，
// 以便在GC周期之间的并发扫描阶段扫描所有页面
//
// mheap_ must NOT be locked.
// 译：mheap_不能被锁
func deductSweepCredit(spanBytes uintptr, callerSweepPages uintptr) {
	if mheap_.sweepPagesPerByte == 0 {
		// Proportional sweep is done or disabled.
		// 译：完成或禁用比例扫描
		return
	}

	if trace.enabled {
		traceGCSweepStart()
	}

	// Fix debt if necessary.
retry:
	sweptBasis := mheap_.pagesSweptBasis.Load()
	live := gcController.heapLive.Load()
	liveBasis := mheap_.sweepHeapLiveBasis
	newHeapLive := spanBytes
	if liveBasis < live {
		// Only do this subtraction when we don't overflow. Otherwise, pagesTarget
		// might be computed as something really huge, causing us to get stuck
		// sweeping here until the next mark phase.
		//
		// Overflow can happen here if gcPaceSweeper is called concurrently with
		// sweeping (i.e. not during a STW, like it usually is) because this code
		// is intentionally racy. A concurrent call to gcPaceSweeper can happen
		// if a GC tuning parameter is modified and we read an older value of
		// heapLive than what was used to set the basis.
		//
		// This state should be transient, so it's fine to just let newHeapLive
		// be a relatively small number. We'll probably just skip this attempt to
		// sweep.
		//
		// See issue #57523.
		newHeapLive += uintptr(live - liveBasis)
	}
	pagesTarget := int64(mheap_.sweepPagesPerByte*float64(newHeapLive)) - int64(callerSweepPages)
	for pagesTarget > int64(mheap_.pagesSwept.Load()-sweptBasis) {
		if sweepone() == ^uintptr(0) {
			mheap_.sweepPagesPerByte = 0
			break
		}
		if mheap_.pagesSweptBasis.Load() != sweptBasis {
			// Sweep pacing changed. Recompute debt.
			goto retry
		}
	}

	if trace.enabled {
		traceGCSweepDone()
	}
}

// clobberfree sets the memory content at x to bad content, for debugging
// purposes.
func clobberfree(x unsafe.Pointer, size uintptr) {
	// size (span.elemsize) is always a multiple of 4.
	for i := uintptr(0); i < size; i += 4 {
		*(*uint32)(add(x, i)) = 0xdeadbeef
	}
}

// gcPaceSweeper updates the sweeper's pacing parameters.
//
// Must be called whenever the GC's pacing is updated.
//
// The world must be stopped, or mheap_.lock must be held.
func gcPaceSweeper(trigger uint64) {
	assertWorldStoppedOrLockHeld(&mheap_.lock)

	// Update sweep pacing.
	if isSweepDone() {
		mheap_.sweepPagesPerByte = 0
	} else {
		// Concurrent sweep needs to sweep all of the in-use
		// pages by the time the allocated heap reaches the GC
		// trigger. Compute the ratio of in-use pages to sweep
		// per byte allocated, accounting for the fact that
		// some might already be swept.
		heapLiveBasis := gcController.heapLive.Load()
		heapDistance := int64(trigger) - int64(heapLiveBasis)
		// Add a little margin so rounding errors and
		// concurrent sweep are less likely to leave pages
		// unswept when GC starts.
		heapDistance -= 1024 * 1024
		if heapDistance < _PageSize {
			// Avoid setting the sweep ratio extremely high
			heapDistance = _PageSize
		}
		pagesSwept := mheap_.pagesSwept.Load()
		pagesInUse := mheap_.pagesInUse.Load()
		sweepDistancePages := int64(pagesInUse) - int64(pagesSwept)
		if sweepDistancePages <= 0 {
			mheap_.sweepPagesPerByte = 0
		} else {
			mheap_.sweepPagesPerByte = float64(sweepDistancePages) / float64(heapDistance)
			mheap_.sweepHeapLiveBasis = heapLiveBasis
			// Write pagesSweptBasis last, since this
			// signals concurrent sweeps to recompute
			// their debt.
			mheap_.pagesSweptBasis.Store(pagesSwept)
		}
	}
}
