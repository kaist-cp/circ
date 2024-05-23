use atomic::Ordering;
use circ::{AtomicRc, Cs, GraphNode, Rc, Snapshot};

use std::cmp::Ordering::{Equal, Greater, Less};

struct Node<K, V> {
    next: AtomicRc<Self>,
    key: K,
    value: V,
}

impl<K, V> GraphNode for Node<K, V> {
    fn pop_outgoings(&mut self, result: &mut Vec<Rc<Self>>)
    where
        Self: Sized,
    {
        result.push(self.next.swap(Rc::null(), Ordering::Relaxed));
    }
}

struct List<K, V> {
    head: AtomicRc<Node<K, V>>,
}

impl<K, V> Default for List<K, V>
where
    K: Ord + Default,
    V: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Node<K, V>
where
    K: Default,
    V: Default,
{
    /// Creates a new node.
    fn new(key: K, value: V) -> Self {
        Self {
            next: AtomicRc::null(),
            key,
            value,
        }
    }

    /// Creates a dummy head.
    /// We never deref key and value of this head node.
    fn head() -> Self {
        Self {
            next: AtomicRc::null(),
            key: K::default(),
            value: V::default(),
        }
    }
}

struct Cursor<'g, K, V> {
    // The previous node of `curr`.
    prev: Snapshot<'g, Node<K, V>>,
    // Tag of `curr` should always be zero so when `curr` is stored in a `prev`, we don't store a
    // tagged pointer and cause cleanup to fail.
    curr: Snapshot<'g, Node<K, V>>,
}

impl<'g, K: Ord, V> Cursor<'g, K, V> {
    /// Creates a cursor.
    fn new(head: &AtomicRc<Node<K, V>>, cs: &'g Cs) -> Self {
        let prev = head.load(Ordering::Relaxed, cs);
        let curr = prev.as_ref().unwrap().next.load(Ordering::Acquire, cs);
        Self { prev, curr }
    }

    /// Clean up a chain of logically removed nodes in each traversal.
    #[inline]
    fn find_harris(&mut self, key: &K, cs: &'g Cs) -> Result<Option<&'g V>, ()> {
        // Finding phase
        // - cursor.curr: first untagged node w/ key >= search key (4)
        // - cursor.prev: the ref of .next in previous untagged node (1 -> 2)
        // 1 -> 2 -x-> 3 -x-> 4 -> 5 -> ∅  (search key: 4)
        let mut prev_next = self.curr;
        let found = loop {
            let Some(curr_node) = self.curr.as_ref() else {
                break None;
            };
            let next = curr_node.next.load(Ordering::Acquire, cs);

            if next.tag() != 0 {
                // We add a 0 tag here so that `self.curr`s tag is always 0.
                self.curr = next.with_tag(0);
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    self.prev = self.curr;
                    self.curr = next;
                    prev_next = next;
                }
                Equal => break Some(&curr_node.value),
                Greater => break None,
            }
        };

        // If prev and curr WERE adjacent, no need to clean up
        if prev_next == self.curr {
            return Ok(found);
        }

        // cleanup tagged nodes between anchor and curr
        unsafe { self.prev.deref() }
            .next
            .compare_exchange(
                prev_next,
                self.curr.upgrade(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            )
            .map_err(|_| ())?;

        Ok(found)
    }

    /// Inserts a value.
    #[inline]
    pub fn insert(self, node: Rc<Node<K, V>>, cs: &Cs) -> Result<(), Rc<Node<K, V>>> {
        unsafe { node.deref() }
            .next
            .swap(self.curr.upgrade(), Ordering::Relaxed);

        match unsafe { self.prev.deref() }.next.compare_exchange(
            self.curr,
            node,
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        ) {
            Ok(_) => Ok(()),
            Err(e) => Err(e.desired),
        }
    }

    /// removes the current node.
    #[inline]
    pub fn remove(self, cs: &Cs) -> Result<(), ()> {
        let curr_node = unsafe { self.curr.deref() };

        let next = curr_node.next.load(Ordering::Acquire, cs);
        if curr_node
            .next
            .compare_exchange_tag(next.with_tag(0), 1, Ordering::AcqRel, Ordering::Relaxed, cs)
            .is_err()
        {
            return Err(());
        }

        let _ = unsafe { self.prev.deref() }.next.compare_exchange(
            self.curr,
            next.upgrade(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        Ok(())
    }
}

impl<K, V> List<K, V>
where
    K: Ord + Default,
    V: Default,
{
    /// Creates a new list.
    pub fn new() -> Self {
        List {
            head: AtomicRc::new(Node::head()),
        }
    }

    #[inline]
    fn get<'g, F>(&'g self, key: &K, find: F, cs: &'g Cs) -> (Option<&'g V>, Cursor<'g, K, V>)
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Cs) -> Result<Option<&'g V>, ()>,
    {
        loop {
            let mut cursor = Cursor::new(&self.head, cs);
            if let Ok(r) = find(&mut cursor, key, cs) {
                return (r, cursor);
            }
        }
    }

    #[inline]
    fn insert<'g, F>(&'g self, key: K, value: V, find: F, cs: &'g Cs) -> Option<&'g V>
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Cs) -> Result<Option<&'g V>, ()>,
    {
        let mut node = Rc::new(Node::new(key, value));
        loop {
            let (found, cursor) = self.get(&unsafe { node.deref() }.key, &find, cs);
            if found.is_some() {
                return found;
            }

            match cursor.insert(node, cs) {
                Err(n) => node = n,
                Ok(()) => return None,
            }
        }
    }

    #[inline]
    fn remove<'g, F>(&'g self, key: &K, find: F, cs: &'g Cs) -> Option<&'g V>
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Cs) -> Result<Option<&'g V>, ()>,
    {
        loop {
            let (found, cursor) = self.get(key, &find, cs);
            found?;

            match cursor.remove(cs) {
                Err(()) => continue,
                Ok(_) => return found,
            }
        }
    }

    pub fn harris_get<'g>(&'g self, key: &K, cs: &'g Cs) -> Option<&'g V> {
        self.get(key, Cursor::find_harris, cs).0
    }

    pub fn harris_insert<'g>(&'g self, key: K, value: V, cs: &'g Cs) -> Option<&'g V> {
        self.insert(key, value, Cursor::find_harris, cs)
    }

    pub fn harris_remove<'g>(&'g self, key: &K, cs: &'g Cs) -> Option<&'g V> {
        self.remove(key, Cursor::find_harris, cs)
    }
}

#[test]
fn smoke() {
    extern crate rand;
    use circ::pin;
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    let map = &List::new();

    thread::scope(|s| {
        for t in 0..THREADS {
            s.spawn(move |_| {
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                for i in keys {
                    assert!(map.harris_insert(i, i.to_string(), &pin()).is_none());
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in 0..(THREADS / 2) {
            s.spawn(move |_| {
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let mut cs = pin();
                for i in keys {
                    assert_eq!(i.to_string(), *map.harris_remove(&i, &cs).unwrap());
                    cs = pin();
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in (THREADS / 2)..THREADS {
            s.spawn(move |_| {
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let mut cs = pin();
                for i in keys {
                    assert_eq!(i.to_string(), *map.harris_get(&i, &cs).unwrap());
                    cs = pin();
                }
            });
        }
    })
    .unwrap();
}
