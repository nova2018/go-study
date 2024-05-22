// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The mcentral doesn't actually contain the list of free objects; the mspan does.
// Each mcentral is two lists of mspans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

import (
	"runtime/internal/atomic"
	"runtime/internal/sys"
)

// Central list of free objects of a given size.
type mcentral struct {
	_         sys.NotInHeap
	spanclass spanClass

	// partial and full contain two mspan sets: one of swept in-use
	// spans, and one of unswept in-use spans. These two trade
	// roles on each GC cycle. The unswept set is drained either by
	// allocation or by the background sweeper in every GC cycle,
	// so only two roles are necessary.
	//
	// sweepgen is increased by 2 on each GC cycle, so the swept
	// spans are in partial[sweepgen/2%2] and the unswept spans are in
	// partial[1-sweepgen/2%2]. Sweeping pops spans from the
	// unswept set and pushes spans that are still in-use on the
	// swept set. Likewise, allocating an in-use span pushes it
	// on the swept set.
	//
	// Some parts of the sweeper can sweep arbitrary spans, and hence
	// can't remove them from the unswept set, but will add the span
	// to the appropriate swept list. As a result, the parts of the
	// sweeper and mcentral that do consume from the unswept list may
	// encounter swept spans, and these should be ignored.
	partial [2]spanSet // 译：span列表还有空闲对象 // list of spans with a free object
	full    [2]spanSet // 译：span列表没有空闲对象 // list of spans with no free objects
}

// Initialize a single central free list.
func (c *mcentral) init(spc spanClass) {
	c.spanclass = spc
	lockInit(&c.partial[0].spineLock, lockRankSpanSetSpine)
	lockInit(&c.partial[1].spineLock, lockRankSpanSetSpine)
	lockInit(&c.full[0].spineLock, lockRankSpanSetSpine)
	lockInit(&c.full[1].spineLock, lockRankSpanSetSpine)
}

// partialUnswept returns the spanSet which holds partially-filled
// unswept spans for this sweepgen.
func (c *mcentral) partialUnswept(sweepgen uint32) *spanSet {
	return &c.partial[1-sweepgen/2%2]
}

// partialSwept returns the spanSet which holds partially-filled
// swept spans for this sweepgen.
func (c *mcentral) partialSwept(sweepgen uint32) *spanSet {
	return &c.partial[sweepgen/2%2]
}

// fullUnswept returns the spanSet which holds unswept spans without any
// free slots for this sweepgen.
func (c *mcentral) fullUnswept(sweepgen uint32) *spanSet {
	return &c.full[1-sweepgen/2%2]
}

// fullSwept returns the spanSet which holds swept spans without any
// free slots for this sweepgen.
func (c *mcentral) fullSwept(sweepgen uint32) *spanSet {
	return &c.full[sweepgen/2%2]
}

// Allocate a span to use in an mcache.
// 译：分配一个span用于mcache
func (c *mcentral) cacheSpan() *mspan {
	// Deduct credit for this span allocation and sweep if necessary.
	// 译：扣除此span分配的贷项，如有必要，进行扫描。
	spanBytes := uintptr(class_to_allocnpages[c.spanclass.sizeclass()]) * _PageSize // 注：应该是页空间，即span的字节数
	deductSweepCredit(spanBytes, 0)

	traceDone := false
	if trace.enabled {
		traceGCSweepStart()
	}

	// If we sweep spanBudget spans without finding any free
	// space, just allocate a fresh span. This limits the amount
	// of time we can spend trying to find free space and
	// amortizes the cost of small object sweeping over the
	// benefit of having a full free span to allocate from. By
	// setting this to 100, we limit the space overhead to 1%.
	//
	// TODO(austin,mknyszek): This still has bad worst-case
	// throughput. For example, this could find just one free slot
	// on the 100th swept span. That limits allocation latency, but
	// still has very poor throughput. We could instead keep a
	// running free-to-used budget and switch to fresh span
	// allocation if the budget runs low.
	spanBudget := 100

	var s *mspan
	var sl sweepLocker

	// Try partial swept spans first.
	sg := mheap_.sweepgen
	// 注：先从已清扫完的未填满span中获取
	if s = c.partialSwept(sg).pop(); s != nil {
		goto havespan
	}

	sl = sweep.active.begin()
	if sl.valid { // 注：还未清扫完毕？
		// Now try partial unswept spans.
		for ; spanBudget >= 0; spanBudget-- {
			s = c.partialUnswept(sg).pop() // 注：尝试从未清扫的未填满span中获取
			if s == nil {
				break
			}
			if s, ok := sl.tryAcquire(s); ok { // 取得清扫锁
				// We got ownership of the span, so let's sweep it and use it.
				s.sweep(true) // 执行清扫
				sweep.active.end(sl)
				goto havespan
			}
			// We failed to get ownership of the span, which means it's being or
			// has been swept by an asynchronous sweeper that just couldn't remove it
			// from the unswept list. That sweeper took ownership of the span and
			// responsibility for either freeing it to the heap or putting it on the
			// right swept list. Either way, we should just ignore it (and it's unsafe
			// for us to do anything else).
			// 译：我们无法获得span的所有权，这意味着它正在或已经被一个异步清扫程序扫描，该清扫程序无法将其从未扫描列表中删除。
			// 译：那个清扫者承担了span的所有权，并负责将其释放到堆中或将其放在正确的扫描列表中。
			// 译：无论哪种方式，我们都应该忽略它(我们做任何其他事情都是不安全的)。
		}
		// Now try full unswept spans, sweeping them and putting them into the
		// right list if we fail to get a span.
		for ; spanBudget >= 0; spanBudget-- {
			s = c.fullUnswept(sg).pop() // 注：尝试从未清扫的已填满的span中获取
			if s == nil {
				break
			}
			if s, ok := sl.tryAcquire(s); ok { // 注：获取清扫锁
				// We got ownership of the span, so let's sweep it.
				s.sweep(true) // 注：执行清扫
				// Check if there's any free space.
				freeIndex := s.nextFreeIndex()
				if freeIndex != s.nelems { // 注：如果清扫后，存在剩余空间，则完成查找
					s.freeindex = freeIndex
					sweep.active.end(sl)
					goto havespan
				}
				// Add it to the swept list, because sweeping didn't give us any free space.
				c.fullSwept(sg).push(s.mspan) // 注：清扫完成后，依然没有空间，则放入已完成队列，再去寻找下一个
			}
			// See comment for partial unswept spans.
		}
		sweep.active.end(sl) // 注：结束清扫器
	}
	if trace.enabled {
		traceGCSweepDone()
		traceDone = true
	}

	// We failed to get a span from the mcentral so get one from mheap.
	s = c.grow() // 注：如果没有已存在的可用span，则扩容
	if s == nil {
		return nil
	}

	// At this point s is a span that should have free slots.
havespan:
	if trace.enabled && !traceDone {
		traceGCSweepDone()
	}
	n := int(s.nelems) - int(s.allocCount)
	if n == 0 || s.freeindex == s.nelems || uintptr(s.allocCount) == s.nelems {
		throw("span has no free objects")
	}
	freeByteBase := s.freeindex &^ (64 - 1)
	whichByte := freeByteBase / 8
	// Init alloc bits cache.
	s.refillAllocCache(whichByte)

	// Adjust the allocCache so that s.freeindex corresponds to the low bit in
	// s.allocCache.
	s.allocCache >>= s.freeindex % 64

	return s
}

// Return span from an mcache.
// 译：从mcache返回span
// s must have a span class corresponding to this
// mcentral and it must not be empty.
// 译：S必须有一个与此mCentral对应的spc，并且它不能为空。
func (c *mcentral) uncacheSpan(s *mspan) {
	if s.allocCount == 0 { // 注：已分配数量一定不为空
		throw("uncaching span but s.allocCount == 0")
	}

	sg := mheap_.sweepgen       // 注：获取堆的sweepgen
	stale := s.sweepgen == sg+1 // 注：相等表示：span在扫描开始之前已缓存，并且仍在缓存中，需要进行扫描

	// Fix up sweepgen.
	if stale {
		// Span was cached before sweep began. It's our
		// responsibility to sweep it.
		// 译：span在扫描开始之前被缓存。扫描它是我们的责任。
		//
		// Set sweepgen to indicate it's not cached but needs
		// sweeping and can't be allocated from. sweep will
		// set s.sweepgen to indicate s is swept.
		// 译：设置sweepgen以指示它没有被缓存，但需要扫描，并且不能分配。 扫描将设置s.Sweepgen，表示S已被扫描过。
		atomic.Store(&s.sweepgen, sg-1) // 注：修改状态为sg-1，意为：span正在被扫描
	} else {
		// Indicate that s is no longer cached.
		// 译：指示不再缓存s。
		atomic.Store(&s.sweepgen, sg) // 注：修改状态为sg，意为：span已经被扫描，随时可用
	}

	// Put the span in the appropriate place.
	// 译：将span放在适合的位置
	if stale {
		// It's stale, so just sweep it. Sweeping will put it on
		// the right list.
		// 译：它已经不新鲜了，所以就把它扫了吧。扫一扫就会把它放在正确的名单上。
		//
		// We don't use a sweepLocker here. Stale cached spans
		// aren't in the global sweep lists, so mark termination
		// itself holds up sweep completion until all mcaches
		// have been swept.
		// 译：我们这里不使用SweepLocker。过时的缓存span不在全局扫描列表中，
		// 译：因此标记终止本身会阻止扫描完成，直到所有mcache都已被扫描。
		ss := sweepLocked{s}
		ss.sweep(false) // 注：执行清扫
	} else {
		if int(s.nelems)-int(s.allocCount) > 0 { // 注：没有分配完毕
			// Put it back on the partial swept list.
			// 译：将其放回部分扫描列表中。
			// 注：放入已扫描队列
			c.partialSwept(sg).push(s)
		} else { // 注：已分配完毕
			// There's no free space and it's not stale, so put it on the
			// full swept list.
			// 译：没有可用的空间，而且它不会过时，所以把它放在完整的扫描列表上。
			// 注：放入已扫描队列
			c.fullSwept(sg).push(s)
		}
	}
}

// grow allocates a new empty span from the heap and initializes it for c's size class.
// 译：grow从堆中分配一个新的空span，并为mcentral的类型初始化它。
func (c *mcentral) grow() *mspan {
	npages := uintptr(class_to_allocnpages[c.spanclass.sizeclass()])
	size := uintptr(class_to_size[c.spanclass.sizeclass()])

	s := mheap_.alloc(npages, c.spanclass)
	if s == nil {
		return nil
	}

	// Use division by multiplication and shifts to quickly compute:
	// n := (npages << _PageShift) / size
	n := s.divideByElemSize(npages << _PageShift)
	s.limit = s.base() + size*n
	s.initHeapBits(false)
	return s
}
