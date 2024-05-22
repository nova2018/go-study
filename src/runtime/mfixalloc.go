// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Fixed-size object allocator. Returned memory is not zeroed.
//
// See malloc.go for overview.

package runtime

import (
	"runtime/internal/sys"
	"unsafe"
)

// FixAlloc is a simple free-list allocator for fixed size objects.
// Malloc uses a FixAlloc wrapped around sysAlloc to manage its
// mcache and mspan objects.
// 译：FixAlloc是一个用于固定大小对象的简单自由列表分配器。
// 译：Malloc使用包装在sysAlloc上的FixAlloc来管理其mcache和mspan对象。
//
// Memory returned by fixalloc.alloc is zeroed by default, but the
// caller may take responsibility for zeroing allocations by setting
// the zero flag to false. This is only safe if the memory never
// contains heap pointers.
// 译：由fixalloc.alloc返回的内存默认为零，但调用者可以通过设置将零标志设置为FALSE。
// 译：这只有在内存永远不会包含堆指针才是安全的。
//
// The caller is responsible for locking around FixAlloc calls.
// Callers can keep state in the object but the first word is
// smashed by freeing and reallocating.
// 译：调用方负责锁定FixAlloc调用。调用者可以在对象中保持状态，
// 译：但first单词是通过释放和重新分配来粉碎。
//
// Consider marking fixalloc'd types not in heap by embedding
// runtime/internal/sys.NotInHeap.
type fixalloc struct {
	size   uintptr                     // 注：单元空间
	first  func(arg, p unsafe.Pointer) // called first time p is returned
	arg    unsafe.Pointer
	list   *mlink
	chunk  uintptr // 注：块的当前指针 // use uintptr instead of unsafe.Pointer to avoid write barriers
	nchunk uint32  // 注：当前区块中剩余的字节数 // bytes remaining in current chunk
	nalloc uint32  // 注：新块的大小 // size of new chunks in bytes
	inuse  uintptr // in-use bytes now
	stat   *sysMemStat
	zero   bool // zero allocations
}

// A generic linked list of blocks.  (Typically the block is bigger than sizeof(MLink).)
// Since assignments to mlink.next will result in a write barrier being performed
// this cannot be used by some of the internal GC structures. For example when
// the sweeper is placing an unmarked object on the free list it does not want the
// write barrier to be called since that could result in the object being reachable.
type mlink struct {
	_    sys.NotInHeap
	next *mlink
}

// Initialize f to allocate objects of the given size,
// using the allocator to obtain chunks of memory.
func (f *fixalloc) init(size uintptr, first func(arg, p unsafe.Pointer), arg unsafe.Pointer, stat *sysMemStat) {
	if size > _FixAllocChunk {
		throw("runtime: fixalloc size too large")
	}
	if min := unsafe.Sizeof(mlink{}); size < min {
		size = min
	}

	f.size = size
	f.first = first
	f.arg = arg
	f.list = nil
	f.chunk = 0
	f.nchunk = 0
	f.nalloc = uint32(_FixAllocChunk / size * size) // 注：内存向下对齐 // Round _FixAllocChunk down to an exact multiple of size to eliminate tail waste
	f.inuse = 0
	f.stat = stat
	f.zero = true
}

func (f *fixalloc) alloc() unsafe.Pointer {
	if f.size == 0 {
		print("runtime: use of FixAlloc_Alloc before FixAlloc_Init\n")
		throw("runtime: internal error")
	}

	if f.list != nil {
		v := unsafe.Pointer(f.list)
		f.list = f.list.next
		f.inuse += f.size
		if f.zero {
			memclrNoHeapPointers(v, f.size)
		}
		return v
	}
	if uintptr(f.nchunk) < f.size {
		f.chunk = uintptr(persistentalloc(uintptr(f.nalloc), 0, f.stat)) // 注：申请一块内存
		f.nchunk = f.nalloc
	}

	v := unsafe.Pointer(f.chunk)
	if f.first != nil {
		f.first(f.arg, v)
	}
	f.chunk = f.chunk + f.size // 注：指针前进
	f.nchunk -= uint32(f.size)
	f.inuse += f.size
	return v
}

func (f *fixalloc) free(p unsafe.Pointer) {
	f.inuse -= f.size
	v := (*mlink)(p)
	v.next = f.list
	f.list = v
}
