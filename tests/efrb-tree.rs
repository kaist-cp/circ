use bitflags::bitflags;
use circ::{AtomicRc, Cs, GraphNode, Pointer, Rc, Snapshot, Weak};
use std::sync::atomic::Ordering;

/// Some or executing the given expression.
macro_rules! some_or {
    ($e:expr, $err:expr) => {{
        match $e {
            Some(r) => r,
            None => $err,
        }
    }};
}

bitflags! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct UpdateTag: usize {
        const CLEAN = 0usize;
        const DFLAG = 1usize;
        const IFLAG = 2usize;
        const MARK = 3usize;
    }
}

#[derive(Clone, Copy)]
pub enum Direction {
    L,
    R,
}

#[derive(Clone, PartialEq, Eq, Ord, Debug)]
pub enum Key<K> {
    Fin(K),
    Inf1,
    Inf2,
}

impl<K> PartialOrd for Key<K>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Key::Fin(k1), Key::Fin(k2)) => k1.partial_cmp(k2),
            (Key::Fin(_), Key::Inf1) => Some(std::cmp::Ordering::Less),
            (Key::Fin(_), Key::Inf2) => Some(std::cmp::Ordering::Less),
            (Key::Inf1, Key::Fin(_)) => Some(std::cmp::Ordering::Greater),
            (Key::Inf1, Key::Inf1) => Some(std::cmp::Ordering::Equal),
            (Key::Inf1, Key::Inf2) => Some(std::cmp::Ordering::Less),
            (Key::Inf2, Key::Fin(_)) => Some(std::cmp::Ordering::Greater),
            (Key::Inf2, Key::Inf1) => Some(std::cmp::Ordering::Greater),
            (Key::Inf2, Key::Inf2) => Some(std::cmp::Ordering::Equal),
        }
    }
}

impl<K> PartialEq<K> for Key<K>
where
    K: PartialEq,
{
    fn eq(&self, rhs: &K) -> bool {
        match self {
            Key::Fin(k) => k == rhs,
            _ => false,
        }
    }
}

impl<K> PartialOrd<K> for Key<K>
where
    K: PartialOrd,
{
    fn partial_cmp(&self, rhs: &K) -> Option<std::cmp::Ordering> {
        match self {
            Key::Fin(k) => k.partial_cmp(rhs),
            _ => Some(std::cmp::Ordering::Greater),
        }
    }
}

impl<K> Key<K>
where
    K: Ord,
{
    fn cmp(&self, rhs: &K) -> std::cmp::Ordering {
        match self {
            Key::Fin(k) => k.cmp(rhs),
            _ => std::cmp::Ordering::Greater,
        }
    }
}

pub struct Node<K, V> {
    key: Key<K>,
    value: Option<V>,
    // tag on low bits: {Clean, DFlag, IFlag, Mark}
    update: AtomicRc<Update<K, V>>,
    left: AtomicRc<Node<K, V>>,
    right: AtomicRc<Node<K, V>>,
}

impl<K, V> GraphNode for Node<K, V> {
    #[inline]
    fn pop_outgoings(&mut self, _: &mut Vec<Rc<Self>>)
    where
        Self: Sized,
    {
    }
}

pub struct Update<K, V> {
    gp: Weak<Node<K, V>>,
    p: Weak<Node<K, V>>,
    l: Rc<Node<K, V>>,
    pupdate: Rc<Update<K, V>>,
    new_internal: Rc<Node<K, V>>,
}

impl<K, V> GraphNode for Update<K, V> {
    #[inline]
    fn pop_outgoings(&mut self, _: &mut Vec<Rc<Self>>)
    where
        Self: Sized,
    {
    }
}

impl<K, V> Node<K, V> {
    pub fn internal(key: Key<K>, value: Option<V>, left: Self, right: Self) -> Self {
        Self {
            key,
            value,
            update: AtomicRc::null(),
            left: AtomicRc::new(left),
            right: AtomicRc::new(right),
        }
    }

    pub fn leaf(key: Key<K>, value: Option<V>) -> Self {
        Self {
            key,
            value,
            update: AtomicRc::null(),
            left: AtomicRc::null(),
            right: AtomicRc::null(),
        }
    }

    pub fn child(&self, dir: Direction) -> &AtomicRc<Node<K, V>> {
        match dir {
            Direction::L => &self.left,
            Direction::R => &self.right,
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.left.load_raw(Ordering::Acquire).is_null()
    }
}

pub struct Cursor<'g, K, V> {
    gp: Snapshot<'g, Node<K, V>>,
    p: Snapshot<'g, Node<K, V>>,
    l: Snapshot<'g, Node<K, V>>,
    pupdate: Snapshot<'g, Update<K, V>>,
    gpupdate: Snapshot<'g, Update<K, V>>,
}

impl<'g, K, V> Cursor<'g, K, V> {
    fn new(root: &AtomicRc<Node<K, V>>, cs: &'g Cs) -> Self {
        let l = root.load(Ordering::Relaxed, cs);
        Self {
            gp: Snapshot::null(),
            p: Snapshot::null(),
            l,
            pupdate: Snapshot::null(),
            gpupdate: Snapshot::null(),
        }
    }
}

impl<'g, K, V> Cursor<'g, K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    /// Used by Insert, Delete and Find to traverse a branch of the BST.
    ///
    /// # Safety
    /// It satisfies following postconditions:
    ///
    /// 1. l points to a Leaf node and p points to an Internal node
    /// 2. Either p → left has contained l (if k<p → key) or p → right has contained l (if k ≥ p → key)
    /// 3. p → update has contained pupdate
    /// 4. if l → key != Inf1, then the following three statements hold:
    ///     - gp points to an Internal node
    ///     - either gp → left has contained p (if k < gp → key) or gp → right has contained p (if k ≥ gp → key)
    ///     - gp → update has contained gpupdate
    #[inline]
    fn search(&mut self, key: &K, cs: &'g Cs) {
        loop {
            let l_node = unsafe { self.l.deref() };
            if l_node.is_leaf() {
                break;
            }
            self.gp = self.p;
            self.p = self.l;
            self.gpupdate = self.pupdate;
            self.pupdate = l_node.update.load(Ordering::Acquire, cs);
            self.l = match l_node.key.cmp(key) {
                std::cmp::Ordering::Greater => l_node.left.load(Ordering::Acquire, cs),
                _ => l_node.right.load(Ordering::Acquire, cs),
            }
        }
    }

    #[inline]
    fn leaf_value(&self) -> Option<&'g V> {
        self.l.as_ref().and_then(|node| node.value.as_ref())
    }
}

pub struct Helper<'g, K, V> {
    gp: Snapshot<'g, Node<K, V>>,
    p: Snapshot<'g, Node<K, V>>,
}

impl<'g, K, V> Helper<'g, K, V> {
    fn new() -> Self {
        Self {
            gp: Snapshot::null(),
            p: Snapshot::null(),
        }
    }

    fn load_delete(&mut self, op: Snapshot<Update<K, V>>, cs: &'g Cs) -> bool {
        let op_ref = unsafe { op.deref() };

        if let Some(gp) = op_ref.gp.as_snapshot(cs) {
            self.gp = gp;
        } else {
            return false;
        };

        if let Some(p) = op_ref.p.as_snapshot(cs) {
            self.p = p;
        } else {
            // Unflag to preserve lock-freedom.
            let _ = self.gp.as_ref().unwrap().update.compare_exchange_tag(
                op.with_tag(UpdateTag::DFLAG.bits()),
                UpdateTag::CLEAN.bits(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            );
            return false;
        };

        true
    }
}

pub struct EFRBTree<K, V> {
    root: AtomicRc<Node<K, V>>,
}

impl<K, V> EFRBTree<K, V> {
    pub fn new() -> Self {
        Self {
            root: AtomicRc::new(Node::internal(
                Key::Inf2,
                None,
                Node::leaf(Key::Inf1, None),
                Node::leaf(Key::Inf2, None),
            )),
        }
    }
}

impl<K, V> EFRBTree<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    pub fn find<'g>(&'g self, key: &K, cs: &'g Cs) -> Option<&'g V> {
        let mut cursor = Cursor::new(&self.root, cs);
        cursor.search(key, cs);
        let l_node = cursor.l.as_ref().unwrap();
        if l_node.key.eq(key) {
            Some(cursor.leaf_value().unwrap())
        } else {
            None
        }
    }

    pub fn insert<'g>(&'g self, key: K, value: V, cs: &'g Cs) -> Option<&'g V> {
        loop {
            let mut cursor = Cursor::new(&self.root, cs);
            cursor.search(&key, cs);
            let l_node = cursor.l.as_ref().unwrap();
            let p_node = cursor.p.as_ref().unwrap();

            if l_node.key == key {
                return Some(cursor.leaf_value().unwrap());
            } else if cursor.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(cursor.pupdate, cs);
            } else {
                let new = Node::leaf(Key::Fin(key.clone()), Some(value.clone()));
                let new_sibling = Node::leaf(l_node.key.clone(), l_node.value.clone());

                let (left, right) = match new.key.partial_cmp(&new_sibling.key) {
                    Some(std::cmp::Ordering::Less) => (new, new_sibling),
                    _ => (new_sibling, new),
                };

                let new_internal = Rc::new(Node::internal(
                    // key field max(k, l → key)
                    right.key.clone(),
                    None,
                    // two child fields equal to new and newSibling
                    // (the one with the smaller key is the left child)
                    left,
                    right,
                ));

                let op = Update {
                    p: cursor.p.downgrade(),
                    l: cursor.l.upgrade(),
                    new_internal,
                    gp: Weak::null(),
                    pupdate: Rc::null(),
                };

                let new_pupdate = Rc::new(op).with_tag(UpdateTag::IFLAG.bits());
                let new_update_ss = new_pupdate.as_snapshot(cs);

                match p_node.update.compare_exchange(
                    cursor.pupdate,
                    new_pupdate,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        self.help_insert(new_update_ss, cs);
                        return None;
                    }
                    Err(e) => self.help(e.current, cs),
                }
            }
        }
    }

    pub fn delete<'g>(&'g self, key: &K, cs: &'g Cs) -> Option<&'g V> {
        loop {
            let mut cursor = Cursor::new(&self.root, cs);
            cursor.search(key, cs);

            if cursor.gp.is_null() {
                // The tree is empty. There's no more things to do.
                return None;
            }

            let l_node = cursor.l.as_ref().unwrap();

            if l_node.key != Key::Fin(key.clone()) {
                return None;
            }
            if cursor.gpupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(cursor.gpupdate, cs);
            } else if cursor.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(cursor.pupdate, cs);
            } else {
                let op = Update {
                    gp: cursor.gp.downgrade(),
                    p: cursor.p.downgrade(),
                    l: cursor.l.upgrade(),
                    pupdate: cursor.pupdate.upgrade(),
                    new_internal: Rc::null(),
                };

                let new_update = Rc::new(op).with_tag(UpdateTag::DFLAG.bits());
                cursor.pupdate = new_update.as_snapshot(cs);

                match cursor.gp.as_ref().unwrap().update.compare_exchange(
                    cursor.gpupdate,
                    new_update,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        if self.help_delete(cursor.pupdate, cs) {
                            return Some(cursor.leaf_value().unwrap());
                        }
                    }
                    Err(e) => self.help(e.current, cs),
                }
            }
        }
    }

    #[inline]
    fn help<'g>(&self, op: Snapshot<Update<K, V>>, cs: &'g Cs) {
        match UpdateTag::from_bits_truncate(op.tag()) {
            UpdateTag::IFLAG => self.help_insert(op, cs),
            UpdateTag::MARK => self.help_marked(op, cs),
            UpdateTag::DFLAG => {
                let _ = self.help_delete(op, cs);
            }
            _ => {}
        }
    }

    fn help_delete<'g>(&self, op: Snapshot<Update<K, V>>, cs: &'g Cs) -> bool {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let mut helper = Helper::new();
        if !helper.load_delete(op, cs) {
            return false;
        }

        let op_ref = unsafe { op.deref() };
        let p_ref = unsafe { helper.p.deref() };
        let gp_ref = unsafe { helper.gp.deref() };

        match p_ref.update.compare_exchange(
            op_ref.pupdate.as_snapshot(cs),
            op.upgrade().with_tag(UpdateTag::MARK.bits()),
            Ordering::Release,
            Ordering::Acquire,
            cs,
        ) {
            Ok(_) => {
                // (prev value) = op → pupdate
                self.help_marked(op, cs);
                return true;
            }
            Err(e) => {
                if e.current.as_ptr() == op.as_ptr().with_tag(UpdateTag::MARK.bits()) {
                    // (prev value) = <Mark, op>
                    self.help_marked(op, cs);
                    return true;
                } else {
                    let _ = gp_ref.update.compare_exchange_tag(
                        op.with_tag(UpdateTag::DFLAG.bits()),
                        UpdateTag::CLEAN.bits(),
                        Ordering::Release,
                        Ordering::Relaxed,
                        cs,
                    );
                    self.help(e.current, cs);
                    return false;
                }
            }
        }
    }

    fn help_marked<'g>(&self, op: Snapshot<Update<K, V>>, cs: &'g Cs) {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let mut helper = Helper::new();
        if !helper.load_delete(op, cs) {
            return;
        }

        let p_ref = unsafe { helper.p.deref() };
        let gp_ref = unsafe { helper.gp.deref() };

        let other = if p_ref.right.load_raw(Ordering::Acquire) == unsafe { op.deref() }.l.as_ptr() {
            &p_ref.left
        } else {
            &p_ref.right
        };
        // Splice the node to which op → p points out of the tree, replacing it by other
        let other_sh = other.load(Ordering::Acquire, cs);

        // dchild CAS
        self.cas_child(helper.gp, helper.p, other_sh, cs);

        // dunflag CAS
        let _ = gp_ref.update.compare_exchange_tag(
            op.with_tag(UpdateTag::DFLAG.bits()),
            UpdateTag::CLEAN.bits(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }

    fn help_insert<'g>(&self, op: Snapshot<Update<K, V>>, cs: &'g Cs) {
        // Precondition: op points to a IInfo record (i.e., it is not ⊥)
        let op_ref = unsafe { op.deref() };
        let p = some_or!(op_ref.p.as_snapshot(cs), return);

        let l = op_ref.l.as_snapshot(cs);
        let new_internal = op_ref.new_internal.as_snapshot(cs);

        let p_ref = p.as_ref().unwrap();

        // ichild CAS
        self.cas_child(p, l, new_internal, cs);

        // iunflag CAS
        let _ = p_ref.update.compare_exchange_tag(
            op.with_tag(UpdateTag::IFLAG.bits()),
            UpdateTag::CLEAN.bits(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }

    fn cas_child<'g>(
        &self,
        parent: Snapshot<Node<K, V>>,
        old: Snapshot<Node<K, V>>,
        new: Snapshot<Node<K, V>>,
        cs: &'g Cs,
    ) -> bool {
        let new_node = unsafe { new.deref() };
        let parent_node = unsafe { parent.deref() };
        let node_to_cas = if new_node.key < parent_node.key {
            &parent_node.left
        } else {
            &parent_node.right
        };
        node_to_cas
            .compare_exchange(old, new.upgrade(), Ordering::Release, Ordering::Relaxed, cs)
            .is_ok()
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

    let map = &EFRBTree::new();

    thread::scope(|s| {
        for t in 0..THREADS {
            s.spawn(move |_| {
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                for i in keys {
                    assert!(map.insert(i, i.to_string(), &pin()).is_none());
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
                    assert_eq!(i.to_string(), *map.delete(&i, &cs).unwrap());
                    drop(cs);
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
                    assert_eq!(i.to_string(), *map.find(&i, &cs).unwrap());
                    drop(cs);
                    cs = pin();
                }
            });
        }
    })
    .unwrap();
}
