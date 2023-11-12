use bitflags::bitflags;
use circ::{AtomicRc, CsEBR, GraphNode, Pointer, Rc, Snapshot, StrongPtr, Weak};
use std::sync::atomic::Ordering;

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
    update: AtomicRc<Update<K, V>, CsEBR>,
    left: AtomicRc<Node<K, V>, CsEBR>,
    right: AtomicRc<Node<K, V>, CsEBR>,
}

impl<K, V> GraphNode<CsEBR> for Node<K, V> {
    const UNIQUE_OUTDEGREE: bool = false;

    #[inline]
    fn pop_outgoings(&self, _: &mut Vec<Rc<Self, CsEBR>>)
    where
        Self: Sized,
    {
    }

    #[inline]
    fn pop_unique(&self) -> Rc<Self, CsEBR>
    where
        Self: Sized,
    {
        unimplemented!()
    }
}

pub struct Update<K, V> {
    gp: Weak<Node<K, V>, CsEBR>,
    p: Weak<Node<K, V>, CsEBR>,
    l: Rc<Node<K, V>, CsEBR>,
    pupdate: Rc<Update<K, V>, CsEBR>,
    new_internal: Rc<Node<K, V>, CsEBR>,
}

impl<K, V> GraphNode<CsEBR> for Update<K, V> {
    const UNIQUE_OUTDEGREE: bool = false;

    #[inline]
    fn pop_outgoings(&self, _: &mut Vec<Rc<Self, CsEBR>>)
    where
        Self: Sized,
    {
    }

    #[inline]
    fn pop_unique(&self) -> Rc<Self, CsEBR>
    where
        Self: Sized,
    {
        unimplemented!()
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

    pub fn child(&self, dir: Direction) -> &AtomicRc<Node<K, V>, CsEBR> {
        match dir {
            Direction::L => &self.left,
            Direction::R => &self.right,
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.left.load(Ordering::Acquire).is_null()
    }
}

pub struct Cursor<K, V> {
    gp: Snapshot<Node<K, V>, CsEBR>,
    p: Snapshot<Node<K, V>, CsEBR>,
    l: Snapshot<Node<K, V>, CsEBR>,
    pupdate: Snapshot<Update<K, V>, CsEBR>,
    gpupdate: Snapshot<Update<K, V>, CsEBR>,
}

impl<K, V> Cursor<K, V> {
    fn new(root: &AtomicRc<Node<K, V>, CsEBR>, cs: &CsEBR) -> Self {
        let l = root.load_ss(cs);
        Self {
            gp: Snapshot::new(),
            p: Snapshot::new(),
            l,
            pupdate: Snapshot::new(),
            gpupdate: Snapshot::new(),
        }
    }
}

impl<K, V> Cursor<K, V>
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
    fn search(&mut self, key: &K, cs: &CsEBR) {
        loop {
            let l_node = unsafe { self.l.deref() };
            if l_node.is_leaf() {
                break;
            }
            self.gp = self.p;
            self.p = self.l;
            self.gpupdate = self.pupdate;
            self.pupdate = l_node.update.load_ss(cs);
            self.l = match l_node.key.cmp(key) {
                std::cmp::Ordering::Greater => l_node.left.load_ss(cs),
                _ => l_node.right.load_ss(cs),
            }
        }
    }
}

pub struct Helper<K, V> {
    gp: Snapshot<Node<K, V>, CsEBR>,
    p: Snapshot<Node<K, V>, CsEBR>,
}

impl<K, V> Helper<K, V> {
    fn new() -> Self {
        Self {
            gp: Snapshot::new(),
            p: Snapshot::new(),
        }
    }

    fn load_delete(&mut self, op: Snapshot<Update<K, V>, CsEBR>, cs: &CsEBR) -> bool {
        let op_ref = unsafe { op.deref() };

        let gp_ref = if self.gp.protect_weak(&op_ref.gp, cs) {
            self.gp.as_ref().unwrap()
        } else {
            return false;
        };

        if !self.p.protect_weak(&op_ref.p, cs) {
            // Unflag to preserve lock-freedom.
            let _ = gp_ref.update.compare_exchange_tag(
                op.with_tag(UpdateTag::DFLAG.bits()),
                UpdateTag::CLEAN.bits(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            );
            return false;
        }

        true
    }
}

pub struct EFRBTree<K, V> {
    root: AtomicRc<Node<K, V>, CsEBR>,
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
    pub fn find(&self, key: &K, cs: &CsEBR) -> Option<Snapshot<Node<K, V>, CsEBR>> {
        let mut cursor = Cursor::new(&self.root, cs);
        cursor.search(key, cs);
        let l_node = cursor.l.as_ref().unwrap();
        if l_node.key.eq(key) {
            Some(cursor.l)
        } else {
            None
        }
    }

    pub fn insert(&self, key: K, value: V, cs: &CsEBR) -> bool {
        loop {
            let mut cursor = Cursor::new(&self.root, cs);
            cursor.search(&key, cs);
            let l_node = cursor.l.as_ref().unwrap();
            let p_node = cursor.p.as_ref().unwrap();

            if l_node.key == key {
                return false;
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
                    p: cursor.p.upgrade().downgrade(),
                    l: cursor.l.upgrade(),
                    new_internal,
                    gp: Weak::null(),
                    pupdate: Rc::null(),
                };

                let new_pupdate = Rc::new(op).with_tag(UpdateTag::IFLAG.bits());
                let mut new_update_ss = Snapshot::new();
                let mut helping = Snapshot::new();
                new_update_ss.protect(&new_pupdate, cs);

                match p_node.update.compare_exchange_protecting_current(
                    cursor.pupdate.as_ptr(),
                    new_pupdate,
                    &mut helping,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        self.help_insert(new_update_ss, cs);
                        return true;
                    }
                    Err(e) => unsafe {
                        let new_pupdate = e.desired.into_inner().unwrap();
                        drop(new_pupdate.new_internal.into_inner().unwrap());
                        self.help(helping, cs);
                    },
                }
            }
        }
    }

    pub fn delete(&self, key: &K, cs: &CsEBR) -> Option<Snapshot<Node<K, V>, CsEBR>> {
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
                    gp: cursor.gp.upgrade().downgrade(),
                    p: cursor.p.upgrade().downgrade(),
                    l: cursor.l.upgrade(),
                    pupdate: cursor.pupdate.upgrade(),
                    new_internal: Rc::null(),
                };

                let new_update = Rc::new(op).with_tag(UpdateTag::DFLAG.bits());
                cursor.pupdate.protect(&new_update, cs);
                let mut helping = Snapshot::new();

                match cursor
                    .gp
                    .as_ref()
                    .unwrap()
                    .update
                    .compare_exchange_protecting_current(
                        cursor.gpupdate.as_ptr(),
                        new_update,
                        &mut helping,
                        Ordering::Release,
                        Ordering::Relaxed,
                        cs,
                    ) {
                    Ok(_) => {
                        if self.help_delete(cursor.pupdate, cs) {
                            return Some(cursor.l);
                        }
                    }
                    Err(e) => unsafe {
                        drop(e.desired.into_inner().unwrap());
                        self.help(helping, cs);
                    },
                }
            }
        }
    }

    #[inline]
    fn help(&self, op: Snapshot<Update<K, V>, CsEBR>, cs: &CsEBR) {
        match UpdateTag::from_bits_truncate(op.tag()) {
            UpdateTag::IFLAG => self.help_insert(op, cs),
            UpdateTag::MARK => self.help_marked(op, cs),
            UpdateTag::DFLAG => {
                let _ = self.help_delete(op, cs);
            }
            _ => {}
        }
    }

    fn help_delete(&self, op: Snapshot<Update<K, V>, CsEBR>, cs: &CsEBR) -> bool {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let mut helper = Helper::new();
        if !helper.load_delete(op, cs) {
            return false;
        }

        let op_ref = unsafe { op.deref() };
        let p_ref = unsafe { helper.p.deref() };
        let gp_ref = unsafe { helper.gp.deref() };

        let mut aux = Snapshot::new();
        match p_ref.update.compare_exchange_protecting_current(
            op_ref.pupdate.as_ptr(),
            op.upgrade().with_tag(UpdateTag::MARK.bits()),
            &mut aux,
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
                if e.current == op.as_ptr().with_tag(UpdateTag::MARK.bits()) {
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
                    self.help(aux, cs);
                    return false;
                }
            }
        }
    }

    fn help_marked(&self, op: Snapshot<Update<K, V>, CsEBR>, cs: &CsEBR) {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let mut helper = Helper::new();
        if !helper.load_delete(op, cs) {
            return;
        }

        let p_ref = unsafe { helper.p.deref() };
        let gp_ref = unsafe { helper.gp.deref() };

        let other = if p_ref.right.load(Ordering::Acquire) == unsafe { op.deref() }.l.as_ptr() {
            &p_ref.left
        } else {
            &p_ref.right
        };
        // Splice the node to which op → p points out of the tree, replacing it by other
        let other_sh = other.load_ss(cs);

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

    fn help_insert(&self, op: Snapshot<Update<K, V>, CsEBR>, cs: &CsEBR) {
        // Precondition: op points to a IInfo record (i.e., it is not ⊥)
        let op_ref = unsafe { op.deref() };
        let mut p = Snapshot::new();
        if !p.protect_weak(&op_ref.p, cs) {
            return;
        }

        let mut l = Snapshot::new();
        l.protect(&op_ref.l, cs);
        let mut new_internal = Snapshot::new();
        new_internal.protect(&op_ref.new_internal, cs);

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

    fn cas_child(
        &self,
        parent: Snapshot<Node<K, V>, CsEBR>,
        old: Snapshot<Node<K, V>, CsEBR>,
        new: Snapshot<Node<K, V>, CsEBR>,
        cs: &CsEBR,
    ) -> bool {
        let new_node = unsafe { new.deref() };
        let parent_node = unsafe { parent.deref() };
        let node_to_cas = if new_node.key < parent_node.key {
            &parent_node.left
        } else {
            &parent_node.right
        };
        node_to_cas
            .compare_exchange(
                old.as_ptr(),
                new.upgrade(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            )
            .is_ok()
    }
}

#[test]
fn smoke() {
    extern crate rand;
    use circ::Cs;
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
                    assert!(map.insert(i, i.to_string(), &Cs::new()));
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
                let cs = &mut Cs::new();
                for i in keys {
                    assert_eq!(
                        i.to_string(),
                        *unsafe { map.delete(&i, cs).unwrap().deref() }
                            .value
                            .as_ref()
                            .unwrap()
                    );
                    cs.clear();
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
                let cs = &mut Cs::new();
                for i in keys {
                    assert_eq!(
                        i.to_string(),
                        *unsafe { map.find(&i, cs).unwrap().deref() }
                            .value
                            .as_ref()
                            .unwrap()
                    );
                    cs.clear();
                }
            });
        }
    })
    .unwrap();
}
