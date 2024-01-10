// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package runtime

import (
	"runtime/internal/atomic"
	"runtime/internal/sys"
	"unsafe"
)

// Per-thread (in Go, per-P) cache for small objects.
// 每一个线程(即P)缓存，用于小对象分配
// This includes a small object cache and local allocation stats.
// No locking needed because it is per-thread (per-P).
// 这包含一个小对象缓存和本地分配状态
// 由于是单一线程(P), 因此不需要锁
//
// mcaches are allocated from non-GC'd memory, so any heap pointers
// must be specially handled.
// mCach是从非GC内存中分配的，因此任何堆指针都必须经过特殊处理。
type mcache struct {
	_ sys.NotInHeap

	// The following members are accessed on every malloc,
	// so they are grouped here for better caching.
	nextSample uintptr // trigger heap sample after allocating this many bytes
	scanAlloc  uintptr // 译：分配的可扫描堆的字节数 // bytes of scannable heap allocated

	// Allocator cache for tiny objects w/o pointers.
	// 用于不带(w/o=without)指针的微小对象的分配器缓存
	// See "Tiny allocator" comment in malloc.go.

	// tiny points to the beginning of the current tiny block, or
	// nil if there is no current tiny block.
	// Tiny指向当前极小块的开始，如果没有当前极小块，则为空。
	//
	// tiny is a heap pointer. Since mcache is in non-GC'd memory,
	// we handle it by clearing it in releaseAll during mark
	// termination.
	// Tiny是一个堆指针。由于mcache位于非GC内存中，因此我们通过在标记终止期间在releaseAll中清除它来处理它。
	//
	// tinyAllocs is the number of tiny allocations performed
	// by the P that owns this mcache.
	// TinyAllocs是拥有此mcache的P执行的微小分配数。
	tiny       uintptr
	tinyoffset uintptr
	tinyAllocs uintptr

	// The rest is not accessed on every malloc.
	// 其余部分并不是在每次malloc上都能访问的。

	alloc [numSpanClasses]*mspan // 译：要从中分配的span，按spanClass编制索引 （68*2 - 双倍） // spans to allocate from, indexed by spanClass

	stackcache [_NumStackOrders]stackfreelist // 注：空闲栈缓存

	// flushGen indicates the sweepgen during which this mcache
	// was last flushed. If flushGen != mheap_.sweepgen, the spans
	// in this mcache are stale and need to the flushed so they
	// can be swept. This is done in acquirep.
	// 译：flushGen指示上次刷新此mcache时使用的Sweepgen(变量，指的是mheap.sweepgen快照)。
	// 译：如果flushGen！=mheap_.sweepgen，则此mcache中的span是陈旧的，需要刷新才能清扫它们。这会在acquirep中完成。
	flushGen atomic.Uint32
}

// A gclink is a node in a linked list of blocks, like mlink,
// but it is opaque to the garbage collector.
// The GC does not trace the pointers during collection,
// and the compiler does not emit write barriers for assignments
// of gclinkptr values. Code should store references to gclinks
// as gclinkptr, not as *gclink.
type gclink struct {
	next gclinkptr
}

// A gclinkptr is a pointer to a gclink, but it is opaque
// to the garbage collector.
// 译：gclinkptr是指向gclink的指针，但它对gc是不透明的。
type gclinkptr uintptr

// ptr returns the *gclink form of p.
// The result should be used for accessing fields, not stored
// in other data structures.
func (p gclinkptr) ptr() *gclink {
	return (*gclink)(unsafe.Pointer(p))
}

type stackfreelist struct {
	list gclinkptr // linked list of free stacks
	size uintptr   // total size of stacks in list
}

// dummy mspan that contains no free objects.
var emptymspan mspan

func allocmcache() *mcache {
	var c *mcache
	systemstack(func() {
		lock(&mheap_.lock)
		c = (*mcache)(mheap_.cachealloc.alloc())
		c.flushGen.Store(mheap_.sweepgen)
		unlock(&mheap_.lock)
	})
	for i := range c.alloc {
		c.alloc[i] = &emptymspan
	}
	c.nextSample = nextSample()
	return c
}

// freemcache releases resources associated with this
// mcache and puts the object onto a free list.
//
// In some cases there is no way to simply release
// resources, such as statistics, so donate them to
// a different mcache (the recipient).
func freemcache(c *mcache) {
	systemstack(func() {
		c.releaseAll()
		stackcache_clear(c)

		// NOTE(rsc,rlh): If gcworkbuffree comes back, we need to coordinate
		// with the stealing of gcworkbufs during garbage collection to avoid
		// a race where the workbuf is double-freed.
		// gcworkbuffree(c.gcworkbuf)

		lock(&mheap_.lock)
		mheap_.cachealloc.free(unsafe.Pointer(c))
		unlock(&mheap_.lock)
	})
}

// getMCache is a convenience function which tries to obtain an mcache.
// getMcache是一个方便的函数，用于获取mcache
// Returns nil if we're not bootstrapping or we don't have a P. The caller's
// P must not change, so we must be in a non-preemptible state.
// 如果不是在启动中或者没有p，就会返回nil
// 调用者的p禁止改变，因此我们必须处于非抢占状态
func getMCache(mp *m) *mcache {
	// Grab the mcache, since that's where stats live.
	pp := mp.p.ptr()
	var c *mcache
	if pp == nil {
		// We will be called without a P while bootstrapping,
		// in which case we use mcache0, which is set in mallocinit.
		// mcache0 is cleared when bootstrapping is complete,
		// by procresize.
		// 如果启动时，我们无法通过p调用，此时我们使用mache0，他会在mallocinit被设置
		// mallocinit会在启动完成时，通过procresize方法被清空
		c = mcache0
	} else {
		c = pp.mcache
	}
	return c
}

// refill acquires a new span of span class spc for c. This span will
// have at least one free object. The current span in c must be full.
// 译：refill获取c的对应span class(spc)的新span。至少有一个自由对象。C中的当前span必须是满的。
//
// Must run in a non-preemptible context since otherwise the owner of
// c could change.
// 译：必须在不可抢占的上下文中运行，否则c的所有者可能会更改。
func (c *mcache) refill(spc spanClass) {
	// Return the current cached span to the central lists.
	// 译：将当前缓存的span返回到central列表。
	s := c.alloc[spc] // 注：获取mcache的当前span

	if uintptr(s.allocCount) != s.nelems { // 注：如果未分配完毕抛异常
		throw("refill of span with free space remaining")
	}
	if s != &emptymspan { // 注：不是空span的指针
		// Mark this span as no longer cached.
		// 译：将此span标记为不再缓存
		if s.sweepgen != mheap_.sweepgen+3 { // 注：相等表示 span已经被清扫，然后进行缓存，并且仍在缓存中? 费解
			throw("bad sweepgen in refill")
		}
		mheap_.central[spc].mcentral.uncacheSpan(s) // 注：放入mcentral对应的span队列 从mcache->mcetral

		// Count up how many slots were used and record it.
		// 译：计算使用了多少槽并记录下来。
		stats := memstats.heapStats.acquire()
		slotsUsed := int64(s.allocCount) - int64(s.allocCountBeforeCache) // 注：本次新增分配对象数
		atomic.Xadd64(&stats.smallAllocCount[spc.sizeclass()], slotsUsed)

		// Flush tinyAllocs.
		// 译：刷新tinyAllocs
		if spc == tinySpanClass {
			atomic.Xadd64(&stats.tinyAllocCount, int64(c.tinyAllocs))
			c.tinyAllocs = 0
		}
		memstats.heapStats.release()

		// Count the allocs in inconsistent, internal stats.
		// 译：在不一致的内部统计数据中计算分配数。
		bytesAllocated := slotsUsed * int64(s.elemsize) // 注：本次新增分配字节数
		gcController.totalAlloc.Add(bytesAllocated)

		// Clear the second allocCount just to be safe.
		// 译：为了安全起见，清除第二个allocCount。
		s.allocCountBeforeCache = 0
	}

	// Get a new cached span from the central lists.
	// 译：从central列表中获取新的缓存span。
	s = mheap_.central[spc].mcentral.cacheSpan() // 注：mcentral->mcache
	if s == nil {
		throw("out of memory")
	}

	if uintptr(s.allocCount) == s.nelems {
		throw("span has no free space")
	}

	// Indicate that this span is cached and prevent asynchronous
	// sweeping in the next sweep phase.
	s.sweepgen = mheap_.sweepgen + 3 // 注：标记为已扫描已cache

	// Store the current alloc count for accounting later.
	s.allocCountBeforeCache = s.allocCount // 注：记录上次已分配快照

	// Update heapLive and flush scanAlloc.
	//
	// We have not yet allocated anything new into the span, but we
	// assume that all of its slots will get used, so this makes
	// heapLive an overestimate.
	//
	// When the span gets uncached, we'll fix up this overestimate
	// if necessary (see releaseAll).
	//
	// We pick an overestimate here because an underestimate leads
	// the pacer to believe that it's in better shape than it is,
	// which appears to lead to more memory used. See #53738 for
	// more details.
	usedBytes := uintptr(s.allocCount) * s.elemsize
	// 注：此处写入的是新获取的span实际空闲空间大小，即页空间-已分配空间
	// 注：此处将上一个span的scanAlloc写入gcController, 同时把当前span的scanAlloc清空
	gcController.update(int64(s.npages*pageSize)-int64(usedBytes), int64(c.scanAlloc)) // 注：更新gc监控数据
	c.scanAlloc = 0

	c.alloc[spc] = s
}

// allocLarge allocates a span for a large object.
// 译：allocLarge为大型对象分配span
func (c *mcache) allocLarge(size uintptr, noscan bool) *mspan {
	if size+_PageSize < size {
		throw("out of memory")
	}
	// 注：计算所需的页数
	npages := size >> _PageShift
	if size&_PageMask != 0 {
		npages++
	}

	// Deduct credit for this span allocation and sweep if
	// necessary. mHeap_Alloc will also sweep npages, so this only
	// pays the debt down to npage pages.
	deductSweepCredit(npages*_PageSize, npages)

	spc := makeSpanClass(0, noscan) // 注：sizeclass=0为大对象span
	s := mheap_.alloc(npages, spc)  // 注：直接去堆中分配空间
	if s == nil {
		throw("out of memory")
	}

	// Count the alloc in consistent, external stats.
	stats := memstats.heapStats.acquire()
	atomic.Xadd64(&stats.largeAlloc, int64(npages*pageSize))
	atomic.Xadd64(&stats.largeAllocCount, 1)
	memstats.heapStats.release()

	// Count the alloc in inconsistent, internal stats.
	gcController.totalAlloc.Add(int64(npages * pageSize))

	// Update heapLive.
	gcController.update(int64(s.npages*pageSize), 0) // 注：更新gc监控数据

	// Put the large span in the mcentral swept list so that it's
	// visible to the background sweeper.
	// 译：将大span放在mcenter已扫描列表中，这样背景清扫器就可以看到它。
	mheap_.central[spc].mcentral.fullSwept(mheap_.sweepgen).push(s)
	s.limit = s.base() + size
	s.initHeapBits(false) // 注：初始化堆内位图？
	return s
}

func (c *mcache) releaseAll() { // 注：归还全部的span交给mcentral
	// Take this opportunity to flush scanAlloc.
	scanAlloc := int64(c.scanAlloc)
	c.scanAlloc = 0

	sg := mheap_.sweepgen
	dHeapLive := int64(0)
	for i := range c.alloc { // 注：遍历全部的span
		s := c.alloc[i]
		if s != &emptymspan {
			slotsUsed := int64(s.allocCount) - int64(s.allocCountBeforeCache)
			s.allocCountBeforeCache = 0

			// Adjust smallAllocCount for whatever was allocated.
			stats := memstats.heapStats.acquire()
			atomic.Xadd64(&stats.smallAllocCount[spanClass(i).sizeclass()], slotsUsed)
			memstats.heapStats.release()

			// Adjust the actual allocs in inconsistent, internal stats.
			// We assumed earlier that the full span gets allocated.
			gcController.totalAlloc.Add(slotsUsed * int64(s.elemsize))

			if s.sweepgen != sg+1 {
				// refill conservatively counted unallocated slots in gcController.heapLive.
				// Undo this.
				//
				// If this span was cached before sweep, then gcController.heapLive was totally
				// recomputed since caching this span, so we don't do this for stale spans.
				dHeapLive -= int64(uintptr(s.nelems)-uintptr(s.allocCount)) * int64(s.elemsize)
			}

			// Release the span to the mcentral.
			mheap_.central[i].mcentral.uncacheSpan(s) // 注：将span归还mcentral
			c.alloc[i] = &emptymspan
		}
	}
	// Clear tinyalloc pool.
	c.tiny = 0
	c.tinyoffset = 0

	// Flush tinyAllocs.
	stats := memstats.heapStats.acquire()
	atomic.Xadd64(&stats.tinyAllocCount, int64(c.tinyAllocs))
	c.tinyAllocs = 0
	memstats.heapStats.release()

	// Update heapLive and heapScan.
	gcController.update(dHeapLive, scanAlloc)
}

// prepareForSweep flushes c if the system has entered a new sweep phase
// since c was populated. This must happen between the sweep phase
// starting and the first allocation from c.
// 译：如果系统在填充c之后进入了一个新的清除阶段，则prepareForSweep刷新c。
// 译：这必须发生在扫描阶段开始和从c开始的第一次分配之间。
func (c *mcache) prepareForSweep() {
	// Alternatively, instead of making sure we do this on every P
	// between starting the world and allocating on that P, we
	// could leave allocate-black on, allow allocation to continue
	// as usual, use a ragged barrier at the beginning of sweep to
	// ensure all cached spans are swept, and then disable
	// allocate-black. However, with this approach it's difficult
	// to avoid spilling mark bits into the *next* GC cycle.
	// 译：或者，我们可以保留allocate-black，允许allocate照常进行，
	// 译：在扫描开始时使用粗糙的屏障以确保所有缓存范围都被扫描，然后禁用allocate-black，
	// 译：而不是确保在启动世界和分配该P之间对每个P都执行此操作。
	// 译：但是，使用这种方法很难避免将标记位溢出到下一个GC循环中。
	sg := mheap_.sweepgen
	flushGen := c.flushGen.Load()
	if flushGen == sg {
		return
	} else if flushGen != sg-2 {
		println("bad flushGen", flushGen, "in prepareForSweep; sweepgen", sg)
		throw("bad flushGen")
	}
	c.releaseAll()                    // 注：归还全部的span给mcentral
	stackcache_clear(c)               // 注：释放栈缓存，空闲的栈空间
	c.flushGen.Store(mheap_.sweepgen) // Synchronizes with gcStart
}
