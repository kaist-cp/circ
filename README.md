# CIRC: Concurrent Immediate Reference Counting

An efficient thread-safe reference-counted pointer, with the support for atomic shared mutability and weak pointers.

This library is based on the following research paper.

> Jaehwang Jung, Jeonghyeon Kim, Matthew J. Parkinson, and Jeehoon Kang. 2024. Concurrent Immediate Reference Counting. Proc. ACM Program. Lang. 8, PLDI, Article 153 (June 2024), 24 pages. <https://doi.org/10.1145/3656383>


## Concurrent reference counting with `Rc<T>` and `AtomicRc<T>`

`circ::Rc<T>` is a thread-safe reference-counted pointer to an object of type `T`, similar to `std::sync::Arc<T>`.
Unlike `std::sync::Arc<T>`, the interface of `circ::Rc<T>` is well suited for implementing non-blocking concurrent data structures.
Specifically, it
* allows tagged pointers;
* can be null (thus does not implement the `Deref` trait); and
* most importantly, can be stored in a `circ::AtomicRc<T>`, a shared mutable location supporting atomic `load`, `store`, and `compare_exchange`.

## Efficient access with `Snapshot<'g, T>`

Reference counting can incur significant overhead when accessing many objects, e.g., traversing linked lists.
To address this, CIRC offers the `Snapshot<T>` pointer type for uncounted temporary local references.
Loading a `Snapshot` from `AtomicRc` does not increment the count of the referent, avoiding the overhead.
Instead, the referent of `Snapshot` is protected with epoch-based reclamation (EBR),
using a modified version of [crossbeam-epoch](https://docs.rs/crossbeam-epoch/latest/crossbeam_epoch/).

In fact, CIRC relies on EBR to safely reclaim zero-count objects.
Therefore, all accesses to `AtomicRc` must be inside an EBR-protected critical section.
A thread can activate a critical section with `circ::cs()`,
which returns an RAII-style `Guard`.
`AtomicRc`'s methods take a reference to `Guard` to ensure that it is run in a critical section.
The critical section is deactivated when the guard is dropped.

A `Snapshot<'g, T>` is valid only inside the critical section is was created in (thus "temporary" and "local").
This is enforced by the `'g` lifetime parameter,
which is derived from the reference to the guard passed to `AtomicRc`'s methods.
To store a loaded `Snapshot` to `AtomicRc` or send it somewhere else,
first `upgrade` it to `Rc`.

## Managing cyclic structures with weak references

Cycles formed with `Rc` and `AtomicRc` references cannot be reclaimed automatically due to cyclic dependency of reclamation.
In some cases, the dependency can be broken with `circ::Weak`, CIRC's counterpart for `std::sync::Weak`.

CIRC also supports `AtomicWeak`.
In addition to storing and loading a `Weak`,
`AtomicWeak` supports directly loading a `Snapshot`
so that the user quickly obtain `deref`-able pointer without incrementing the counts twice (weak, then strong).

## Comparison with other concurrent reference counting algorithms

The key advantage of CIRC over other recent reference counting algorithms is that it can quickly reclaim long linked structures.
Reference counting algorithms equipped with uncounted local reference employ deferred decrement or deferred handling of zero-count objects.
This introduces delay between reclaiming two linked objects.
Because of this delay, the reclamation may not be able to keep up with the application's rate of creating garbage.
CIRC follows a similar approach, but
solves this problem with a novel EBR-based algorithm to quickly identify objects that can be immediately recursively reclaimed.
For in-depth discussion, see the aforementioned research paper.


## Example

```rust
use circ::{cs, AtomicRc, RcObject, Rc, Snapshot};
use std::sync::atomic::Ordering::Relaxed;

// A simple singly linked list node.
struct Node {
    item: usize,
    next: AtomicRc<Self>,
}

// The `RcObject` trait must be implemented for all reference-counted objects.
// This trait enables *immediate recursive destruction*.
// Implementation is straightforward: simply add outgoing `Rc` pointers to `out`.
unsafe impl RcObject for Node {
    fn pop_edges(&mut self, out: &mut Vec<Rc<Self>>) {
        out.push(self.next.take());
    }
}


// Let's create a root node with an item `1`.
let root = AtomicRc::new(Node {
    item: 1,
    next: AtomicRc::null(),
});

// Before accessing the shared objects, the thread must activate EBR critical section.
// This enables us to efficiently access the objects without updating the reference counters.
let guard = cs();
// Load the first node as a `Snapshot` pointer.
let first = root.load(Relaxed, &guard);
assert_eq!(first.as_ref().map(|node| &node.item), Some(&1));

// Let's install a new node after the first node.
let new_second = Rc::new(Node {
    item: 2,
    next: AtomicRc::null(),
});
let result = first.as_ref().unwrap().next.compare_exchange(
    Snapshot::null(),
    new_second,
    Relaxed,
    Relaxed,
    &guard,
);
assert!(result.is_ok());

// Let's check the secondary node is properly installed.
let second = first
    .as_ref()
    .map(|node| node.next.load(Relaxed, &guard))
    .unwrap();
assert_eq!(second.as_ref().map(|node| &node.item), Some(&2));

// Those `Snapshot` pointers we have created so far (`first` and `second`) are able to be accessed
// only within the scope of `Guard`. After the `Guard` is dropped, further accesses to the `Snapshot`
// pointers are forbidden by the Rust type system.
//
// If we want to keep pointers alive, we need to `upgrade` them to `Rc`s.
// `Rc` is independent to the EBR backend, and owns the reference count by itself.
let first_rc = first.upgrade();
drop(guard);

// Even after the `Guard` is dropped, `first_rc` is still accessible.
assert_eq!(first_rc.as_ref().map(|node| &node.item), Some(&1));
```

See `./tests` for more examples with actual data structures.


## Limitations
* Since it uses EBR, the reclamation cannot proceed if a thread does not deactivate its critical section.
* Works only for `Sized` types.
* Immediate recursive destruction works only along edges of the same type.


<!--

https://www.reddit.com/r/rust/comments/1bilk82/announcing_aarc_010_atomic_variants_of_arc_and/

https://docs.rs/arc-swap/latest/arc_swap/docs/limitations/index.html

## References

* \[1\] Jaehwang Jung, Jeonghyeon Kim, Matthew J. Parkinson, and Jeehoon Kang. 2024. Concurrent Immediate Reference Counting. Proc. ACM Program. Lang. 8, PLDI, Article 153 (June 2024), 24 pages. <https://doi.org/10.1145/3656383>
* \[2\] Maged M. Michael. 2004. Hazard Pointers: Safe Memory Reclamation for LockFree Objects. IEEE Trans. Parallel Distrib. Syst. 15, 6 (June 2004), 491–504. <https://doi.org/10.1109/TPDS.2004.8>
* \[3\] Keir Fraser. 2004. Practical lock-freedom. Ph. D. Dissertation. University of Cambridge, Computer Laboratory.
* \[4\] Charles Tripp, David Hyde, and Benjamin Grossman-Ponemon. 2018. FRC: A High-Performance Concurrent Parallel Deferred Reference Counter for C++. In Proceedings of the 2018 ACM SIGPLAN International Symposium on Memory Management (ISMM). 14–28. <https://doi.org/10.1145/3210563.3210569>
* \[5\] Andreia Correia, Pedro Ramalhete, and Pascal Felber. 2021. OrcGC: Automatic Lock-Free Memory Reclamation. In Proceedings of the 26th ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming (PPoPP). 205–218. <https://doi.org/10.1145/3437801.3441596>
* \[6\] Daniel Anderson, Guy E. Blelloch, and Yuanhao Wei. 2021. Concurrent Deferred Reference Counting with Constant-Time Overhead. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 526–541. <https://doi.org/10.1145/3453483.3454060>
* \[7\] Daniel Anderson, Guy E. Blelloch, and Yuanhao Wei. 2022. Turning Manual Concurrent Memory Reclamation into Automatic Reference Counting. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 61–75. <https://doi.org/10.1145/3519939.3523730>
* \[8\] L. Peter Deutsch and Daniel G. Bobrow. 1976. An Efficient, Incremental, Automatic Garbage Collector. Commun. ACM 19, 9 (sep 1976), 522–526. <https://doi.org/10.1145/360336.360345>
* \[9\] David F. Bacon, Clement R. Attanasio, Han B. Lee, V. T. Rajan, and Stephen Smith. 2001. Java without the Coffee Breaks: A Nonintrusive Multiprocessor Garbage Collector. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 92–103. <https://doi.org/10.1145/378795.378819>

-->

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
