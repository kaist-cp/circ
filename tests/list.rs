use atomic::Ordering;
use circ::{AtomicRc, Cs, Pointer, Rc, Snapshot, StrongPtr, TaggedCnt};

use std::cmp::Ordering::{Equal, Greater, Less};

/// Some or executing the given expression.
macro_rules! some_or {
    ($e:expr, $err:expr) => {{
        match $e {
            Some(r) => r,
            None => $err,
        }
    }};
}

struct Node<K, V, C: Cs> {
    next: AtomicRc<Self, C>,
    key: K,
    value: V,
}

struct List<K, V, C: Cs> {
    head: AtomicRc<Node<K, V, C>, C>,
}

impl<K, V, C> Default for List<K, V, C>
where
    K: Ord + Default,
    V: Default,
    C: Cs,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, C> Node<K, V, C>
where
    K: Default,
    V: Default,
    C: Cs,
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

struct Cursor<K, V, C: Cs> {
    // `Snapshot`s are used only for traversing the list.
    prev: Snapshot<Node<K, V, C>, C>,
    // We don't have to protect the next pointer of `prev`.
    prev_next: TaggedCnt<Node<K, V, C>>,
    // Tag of `curr` should always be zero so when `curr` is stored in a `prev`, we don't store a
    // tagged pointer and cause cleanup to fail.
    curr: Snapshot<Node<K, V, C>, C>,
    next: Snapshot<Node<K, V, C>, C>,
}

impl<K: Ord, V, C: Cs> Cursor<K, V, C> {
    fn new() -> Self {
        Self {
            prev: Snapshot::new(),
            prev_next: TaggedCnt::null(),
            curr: Snapshot::new(),
            next: Snapshot::new(),
        }
    }

    /// Initializes a cursor.
    fn initialize(&mut self, head: &AtomicRc<Node<K, V, C>, C>, cs: &C) {
        self.prev.load(head, cs);
        self.curr.load(&unsafe { self.prev.deref() }.next, cs);
        self.prev_next = self.curr.as_ptr();
    }

    /// Clean up a chain of logically removed nodes in each traversal.
    #[inline]
    fn find_harris(&mut self, key: &K, cs: &C) -> Result<bool, ()> {
        // Finding phase
        // - cursor.curr: first untagged node w/ key >= search key (4)
        // - cursor.prev: the ref of .next in previous untagged node (1 -> 2)
        // 1 -> 2 -x-> 3 -x-> 4 -> 5 -> ∅  (search key: 4)
        let found = loop {
            let curr_node = some_or!(self.curr.as_ref(), break false);
            self.next.load(&curr_node.next, cs);

            // - finding stage is done if cursor.curr advancement stops
            // - advance cursor.curr if (.next is tagged) || (cursor.curr < key)
            // - stop cursor.curr if (not tagged) && (cursor.curr >= key)
            // - advance cursor.prev if not tagged

            if self.next.tag() != 0 {
                // We add a 0 tag here so that `self.curr`s tag is always 0.
                self.next.set_tag(0);
                Snapshot::swap(&mut self.next, &mut self.curr);
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    Snapshot::swap(&mut self.prev, &mut self.curr);
                    Snapshot::swap(&mut self.curr, &mut self.next);
                    self.prev_next = self.curr.as_ptr();
                }
                Equal => break true,
                Greater => break false,
            }
        };

        // If prev and curr WERE adjacent, no need to clean up
        if self.prev_next == self.curr.as_ptr() {
            return Ok(found);
        }

        // cleanup tagged nodes between prev and curr
        unsafe { self.prev.deref() }
            .next
            .compare_exchange(
                self.prev_next,
                &self.curr,
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            )
            .map_err(|_| ())?;

        Ok(found)
    }

    /// Inserts a value.
    #[inline]
    pub fn insert(
        &mut self,
        node: Rc<Node<K, V, C>, C>,
        cs: &C,
    ) -> Result<(), Rc<Node<K, V, C>, C>> {
        unsafe { node.deref() }
            .next
            .swap(Rc::from_snapshot(&self.curr), Ordering::Relaxed, cs);

        match unsafe { self.prev.deref() }.next.compare_exchange(
            self.curr.as_ptr(),
            node,
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        ) {
            Ok(_) => Ok(()),
            Err(e) => Err(e.desired()),
        }
    }

    /// removes the current node.
    #[inline]
    pub fn remove(&mut self, cs: &C) -> Result<(), ()> {
        let curr_node = unsafe { self.curr.deref() };

        self.next.load(&curr_node.next, cs);
        if curr_node
            .next
            .compare_exchange(
                self.next.with_tag(0).as_ptr(),
                self.next.with_tag(1),
                Ordering::AcqRel,
                Ordering::Relaxed,
                cs,
            )
            .is_err()
        {
            return Err(());
        }

        let _ = unsafe { self.prev.deref() }.next.compare_exchange(
            self.curr.as_ptr(),
            &self.next,
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        Ok(())
    }
}

impl<K, V, C> List<K, V, C>
where
    K: Ord + Default,
    V: Default,
    C: Cs,
{
    /// Creates a new list.
    pub fn new() -> Self {
        List {
            head: AtomicRc::new(Node::head()),
        }
    }

    #[inline]
    fn get<F>(&self, key: &K, find: F, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool
    where
        F: Fn(&mut Cursor<K, V, C>, &K, &C) -> Result<bool, ()>,
    {
        loop {
            cursor.initialize(&self.head, cs);
            if let Ok(r) = find(cursor, key, cs) {
                return r;
            }
        }
    }

    #[inline]
    fn insert<F>(&self, key: K, value: V, find: F, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool
    where
        F: Fn(&mut Cursor<K, V, C>, &K, &C) -> Result<bool, ()>,
    {
        let mut node = Rc::new(Node::new(key, value));
        loop {
            let found = self.get(&unsafe { node.deref() }.key, &find, cursor, cs);
            if found {
                return false;
            }

            match cursor.insert(node, cs) {
                Err(n) => node = n,
                Ok(()) => return true,
            }
        }
    }

    #[inline]
    fn remove<F>(&self, key: &K, find: F, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool
    where
        F: Fn(&mut Cursor<K, V, C>, &K, &C) -> Result<bool, ()>,
    {
        loop {
            let found = self.get(key, &find, cursor, cs);
            if !found {
                return false;
            }

            match cursor.remove(cs) {
                Err(()) => continue,
                Ok(_) => return true,
            }
        }
    }

    /// Omitted
    pub fn harris_get(&self, key: &K, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        self.get(key, Cursor::find_harris, cursor, cs)
    }

    /// Omitted
    pub fn harris_insert(&self, key: K, value: V, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        self.insert(key, value, Cursor::find_harris, cursor, cs)
    }

    /// Omitted
    pub fn harris_remove(&self, key: &K, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        self.remove(key, Cursor::find_harris, cursor, cs)
    }
}

#[cfg(test)]
fn smoke<C: Cs>() {
    extern crate rand;
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    let map = &List::new();

    thread::scope(|s| {
        for t in 0..THREADS {
            s.spawn(move |_| {
                let cursor = &mut Cursor::new();
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                for i in keys {
                    assert!(map.harris_insert(i, i.to_string(), cursor, &C::new()));
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in 0..(THREADS / 2) {
            s.spawn(move |_| {
                let cursor = &mut Cursor::new();
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let cs = &mut C::new();
                for i in keys {
                    assert!(map.harris_remove(&i, cursor, cs));
                    assert_eq!(i.to_string(), unsafe { cursor.curr.deref() }.value);
                    cs.clear();
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in (THREADS / 2)..THREADS {
            s.spawn(move |_| {
                let cursor = &mut Cursor::new();
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let cs = &mut C::new();
                for i in keys {
                    assert!(map.harris_get(&i, cursor, cs));
                    assert_eq!(i.to_string(), unsafe { cursor.curr.deref() }.value);
                    cs.clear();
                }
            });
        }
    })
    .unwrap();
}

#[test]
fn smoke_ebr() {
    smoke::<circ::CsEBR>();
}

#[test]
fn smoke_hp() {
    smoke::<circ::CsHP>();
}
