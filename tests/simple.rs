fn main() {
    use circ::{pin, AtomicRc, GraphNode, Rc};
    use std::sync::atomic::Ordering;

    struct Node {
        item: usize,
        next: AtomicRc<Self>,
    }

    impl GraphNode for Node {
        fn pop_outgoings(&mut self) -> Vec<Rc<Self>> {
            vec![self.next.take()]
        }
    }

    let root = AtomicRc::new(Node {
        item: 1,
        next: AtomicRc::null(),
    });

    let cs = pin();
    let first = root.load(Ordering::Relaxed, &cs);
    assert_eq!(first.as_ref().map(|node| &node.item), Some(&1));

    let new_second = Rc::new(Node {
        item: 2,
        next: AtomicRc::null(),
    });
    let result = first.as_ref().unwrap().next.compare_exchange(
        Rc::null(),
        new_second,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &cs,
    );
    assert!(result.is_ok());
    let second = first
        .as_ref()
        .map(|node| node.next.load(Ordering::Relaxed, &cs))
        .unwrap();
    assert_eq!(second.as_ref().map(|node| &node.item), Some(&2));

    let first_rc = first.upgrade();
    drop(cs);
    assert_eq!(first_rc.as_ref().map(|node| &node.item), Some(&1));
}
