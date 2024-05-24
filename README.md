# CIRC: Concurrent Immediate Reference Counting

An efficient concurrent reference counting with the support of weak pointers.

This library is based on the original research paper by Jaehwang Jung et al. \[1\].

## Usage

To use this library for your crate, add the following to your `Cargo.toml`.

```toml
[dependencies]
circ = "0.1"
```

### Concurrent Reference Counting with `Rc<T>` and `AtomicRc<T>`

`Rc<T>` is a smart pointer for reference-counted ownership of an object of type `T`. It supports `Send` and `Sync` if `T` does, allows pointer tagging, and can represent a null pointer. For a mutable field that contains an `Rc<T>` (*i.e.,* the next pointer of a node), use `AtomicRc<T>`, which provides atomic methods like `load`, `store`, and `compare_exchange`.

### Efficient Access with `Snapshot<'g, T>`

During an intensive shared object access, frequent reference count updates with `Rc<T>` and `AtomicRc<T>` can cause overhead. `Snapshot<'g, T>` addresses this by offering a local reference protected by an EBR guard with a lifetime `'g`. It avoids reference count updates during construction and destruction. Use an RAII-style EBR guard `Cs` created with `pin` function for safe access during its lifetime. As a trade-off, `Snapshot<'g, T>` cannot be sent across threads. The send the shared pointer, upgrade it to `Rc<T>` using the `upgrade` method.

### Managing Cyclic Structures with Weak References

`Rc<T>` and `AtomicRc<T>` cannot reclaim cyclic structures. `AtomicWeak<T>` and `Weak<T>` solve this by holding weak references that don't affect the strong reference count but preserve memory allocation. Create `Weak<T>` by downgrading an `Rc<T>` or `Snapshot<'g, T>`. Upgrade a `Weak<T>` to `Rc<T>` to atomically increase the strong count if the object is still valid.

### Example

More examples with actual data structures can be found in `./tests`.

```rust
use circ::{pin, AtomicRc, GraphNode, Rc};
use std::sync::atomic::Ordering::Relaxed;

// A simple singly linked list node.
struct Node {
    item: usize,
    next: AtomicRc<Self>,
}

// The `GraphNode` trait must be implemented for all reference-counted objects.
// This trait enables the *immediate recursive destruction* strategy, a novel optimization
// provided by CIRC (see the `Theoretical Introduction` section below).
//
// Implementation is straightforward: simply append outgoing `Rc` pointers to `out`.
// Notably, it remains safe even if the `pop_outgoings` method is not implemented correctly
// (e.g., returning fewer pointers than it actually has).
impl GraphNode for Node {
    fn pop_outgoings(&mut self, out: &mut Vec<Rc<Self>>) {
        out.push(self.next.take());
    }
}


// Let's create a root node with an item `1`.
let root = AtomicRc::new(Node {
    item: 1,
    next: AtomicRc::null(),
});

// Before accessing the shared objects, the thread must be pinned by the EBR backend.
// This enables us to efficiently access the objects without updating the reference counters.
let cs = pin();
// Load the first node as a `Snapshot` pointer.
let first = root.load(Relaxed, &cs);
assert_eq!(first.as_ref().map(|node| &node.item), Some(&1));

// Let's install a new node after the first node.
let new_second = Rc::new(Node {
    item: 2,
    next: AtomicRc::null(),
});
let result = first.as_ref().unwrap().next.compare_exchange(
    Rc::null(),
    new_second,
    Relaxed,
    Relaxed,
    &cs,
);
assert!(result.is_ok());

// Let's check the secondary node is properly installed.
let second = first
    .as_ref()
    .map(|node| node.next.load(Relaxed, &cs))
    .unwrap();
assert_eq!(second.as_ref().map(|node| &node.item), Some(&2));

// Those `Snapshot` pointers we have created so far (`first` and `second`) are able to be accessed
// only within the scope of `Cs`. After the `Cs` is dropped, further accesses to the `Snapshot`
// pointers are forbidden by the Rust type system.
//
// If we want to keep pointers alive, we need to `upgrade` them to `Rc`s.
// `Rc` is independent to the EBR backend, and owns the reference count by itself.
let first_rc = first.upgrade();
drop(cs);

// Even after the `Cs` is dropped, `first_rc` is still accessible.
assert_eq!(first_rc.as_ref().map(|node| &node.item), Some(&1));
```

## Theoretical Introduction

The performance and scalability of modern software systems rely on highly concurrent non-blocking data structures. These structures often face challenges in manual memory management due to their optimistic memory access patterns. *Safe memory reclamation* (SMR) algorithms like hazard pointers (HP) \[2\] and epoch-based reclamation (EBR) \[3\] address these challenges but are complex to apply and error-prone.

*Automatic reference counting* offers an easier alternative. Recently, there has been a push to optimize automatic reference counting for unmanaged languages by applying the optimizations used in garbage collectors (GCs) for managed languages to avoid eagerly counting the local references. Modern algorithms such as Fast Reference Counter (FRC) \[4\], OrcGC \[5\], and Concurrent Deferred Reference Counting (CDRC) \[6, 7\] use SMR to protect uncounted local references, replacing the GC’s role of scanning local references. Specifically, OrcGC delays the reclamation of the zero-count object protected by a hazard pointer, following Deutsch and Bobrow \[8\]; FRC delays decrements and temporarily increments objects protected by hazard pointers, following Bacon et al. \[9\]; and CDRC generalizes the deferred decrement approach to other SMRs by delaying decrements to an object until it is no longer protected by the SMR.

### Problems of Deferral-Based Methods

However, the prior deferral-based SMR methods for reference counting have some limitations:

* **Slow progress of reclamation**: Delays in reclaiming memory can lead to increased memory footprint, especially in data structures with long chains of removed nodes, such as lock-free skip lists and doubly-linked queues.
* **Performance overhead**: CDRC may incur significant performance overhead when the objects have many counted references and are updated frequently. Since CDRC schedules a deferred task for each decrement, it creates a large number of deferred tasks in such cases, imposing a non-negligible burden on the underlying SMR.

### Our Solution

We present Concurrent Immediate Reference Counting (CIRC), a new combination of epoch-based reclamation (EBR) with reference counting. CIRC generally outperforms CDRC and incurs almost none to modest overhead over the underlying EBR.

* **Automatic Reachability Tracking**: CIRC attaches the few-bit representation of the epoch number to pointer fields and reference counts, which are updated along with pointer writes and immediate decrements, respectively. This allows for *immediate recursive destruction* of unneeded nodes. For example, in a linked-based queue, if a node *a* was dequeued long ago and is being destroyed now, the successive node *b* could not have been accessed through the node *a*. This knowledge allows immediate recursive destruction of the node *b*.
* **Immediate decrement style**: CIRC handles concurrency efficiently through immediate decrements and careful tracking of reference counts. When an object’s reference count reaches zero, it must be checked for local references. However, concurrency complicates this process. If a zero-count object is incremented back to a non-zero value and then decremented to zero again while a collector is running, its destruction must be canceled to prevent missing new local references.

    To handle this, CIRC applies an additional increment if an increment moves the count away from zero. When delayed destruction is processed, if the reference count is still zero, it is safe to destruct the object. Otherwise, the destruction is canceled, and the additional reference count is removed. This ensures that objects are only destroyed when they are truly no longer referenced, maintaining safe and efficient memory management.

The combination of these techniques in CIRC allows memory to be reclaimed considerably more quickly than CDRC, ensuring high performance and scalability for concurrent data structures.

## References

1. Jaehwang Jung, Jeonghyeon Kim, Matthew J. Parkinson, and Jeehoon Kang. 2024. Concurrent Immediate Reference Counting. Proc. ACM Program. Lang. 8, PLDI, Article 153 (June 2024), 24 pages. <https://doi.org/10.1145/3656383>
2. Maged M. Michael. 2004. Hazard Pointers: Safe Memory Reclamation for LockFree Objects. IEEE Trans. Parallel Distrib. Syst. 15, 6 (June 2004), 491–504. <https://doi.org/10.1109/TPDS.2004.8>
3. Keir Fraser. 2004. Practical lock-freedom. Ph. D. Dissertation. University of Cambridge, Computer Laboratory.
4. Charles Tripp, David Hyde, and Benjamin Grossman-Ponemon. 2018. FRC: A High-Performance Concurrent Parallel Deferred Reference Counter for C++. In Proceedings of the 2018 ACM SIGPLAN International Symposium on Memory Management (ISMM). 14–28. <https://doi.org/10.1145/3210563.3210569>
5. Andreia Correia, Pedro Ramalhete, and Pascal Felber. 2021. OrcGC: Automatic Lock-Free Memory Reclamation. In Proceedings of the 26th ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming (PPoPP). 205–218. <https://doi.org/10.1145/3437801.3441596>
6. Daniel Anderson, Guy E. Blelloch, and Yuanhao Wei. 2021. Concurrent Deferred Reference Counting with Constant-Time Overhead. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 526–541. <https://doi.org/10.1145/3453483.3454060>
7. Daniel Anderson, Guy E. Blelloch, and Yuanhao Wei. 2022. Turning Manual Concurrent Memory Reclamation into Automatic Reference Counting. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 61–75. <https://doi.org/10.1145/3519939.3523730>
8. L. Peter Deutsch and Daniel G. Bobrow. 1976. An Efficient, Incremental, Automatic Garbage Collector. Commun. ACM 19, 9 (sep 1976), 522–526. <https://doi.org/10.1145/360336.360345>
9. David F. Bacon, Clement R. Attanasio, Han B. Lee, V. T. Rajan, and Stephen Smith. 2001. Java without the Coffee Breaks: A Nonintrusive Multiprocessor Garbage Collector. In ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI). 92–103. <https://doi.org/10.1145/378795.378819>

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

#### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
