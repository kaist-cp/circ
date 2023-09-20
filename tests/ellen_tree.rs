use bitflags::bitflags;
use circ::{AtomicRc, AtomicWeak, Cs, Pointer, Rc, Snapshot, StrongPtr, Weak};
use std::{mem::swap, sync::atomic::Ordering};

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

pub struct Node<K, V, C: Cs> {
    key: Key<K>,
    value: Option<V>,
    // tag on low bits: {Clean, DFlag, IFlag, Mark}
    update: AtomicRc<Update<K, V, C>, C>,
    left: AtomicRc<Node<K, V, C>, C>,
    right: AtomicRc<Node<K, V, C>, C>,
    is_leaf: bool,
}

pub struct Update<K, V, C: Cs> {
    gp: AtomicWeak<Node<K, V, C>, C>,
    gp_p_dir: Direction,
    p: AtomicWeak<Node<K, V, C>, C>,
    p_l_dir: Direction,
    l: AtomicWeak<Node<K, V, C>, C>,
    l_other: AtomicWeak<Node<K, V, C>, C>,
    pupdate: AtomicWeak<Update<K, V, C>, C>,
    new_internal: AtomicWeak<Node<K, V, C>, C>,
}

impl<K, V, C: Cs> Node<K, V, C> {
    pub fn internal(key: Key<K>, value: Option<V>, left: Self, right: Self, cs: &C) -> Self {
        Self {
            key,
            value,
            update: AtomicRc::null(),
            left: AtomicRc::new(left, cs),
            right: AtomicRc::new(right, cs),
            is_leaf: false,
        }
    }

    pub fn leaf(key: Key<K>, value: Option<V>) -> Self {
        Self {
            key,
            value,
            update: AtomicRc::null(),
            left: AtomicRc::null(),
            right: AtomicRc::null(),
            is_leaf: true,
        }
    }

    pub fn child(&self, dir: Direction) -> &AtomicRc<Node<K, V, C>, C> {
        match dir {
            Direction::L => &self.left,
            Direction::R => &self.right,
        }
    }
}

pub struct Finder<K, V, C: Cs> {
    gp: Snapshot<Node<K, V, C>, C>,
    gp_p_dir: Direction,
    p: Snapshot<Node<K, V, C>, C>,
    p_l_dir: Direction,
    l: Snapshot<Node<K, V, C>, C>,
    l_other: Snapshot<Node<K, V, C>, C>,
    pupdate: Snapshot<Update<K, V, C>, C>,
    gpupdate: Snapshot<Update<K, V, C>, C>,
    new_update: Snapshot<Update<K, V, C>, C>,
}

impl<K, V, C> Finder<K, V, C>
where
    K: Ord + Clone,
    V: Clone,
    C: Cs,
{
    fn new() -> Self {
        Self {
            gp: Snapshot::new(),
            gp_p_dir: Direction::L,
            p: Snapshot::new(),
            p_l_dir: Direction::L,
            l: Snapshot::new(),
            l_other: Snapshot::new(),
            pupdate: Snapshot::new(),
            gpupdate: Snapshot::new(),
            new_update: Snapshot::new(),
        }
    }

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
    fn search(&mut self, root: &AtomicRc<Node<K, V, C>, C>, key: &K, cs: &C) {
        self.l.load(root, cs);
        loop {
            let l_node = unsafe { self.l.deref() };
            if l_node.is_leaf {
                break;
            }
            swap(&mut self.gp, &mut self.p);
            swap(&mut self.gp_p_dir, &mut self.p_l_dir);
            swap(&mut self.p, &mut self.l);
            swap(&mut self.gpupdate, &mut self.pupdate);
            self.pupdate.load(&l_node.update, cs);
            let (l, l_other, dir) = match l_node.key.cmp(key) {
                std::cmp::Ordering::Greater => (&l_node.left, &l_node.right, Direction::L),
                _ => (&l_node.right, &l_node.left, Direction::R),
            };
            self.l.load(l, cs);
            self.l_other.load(l_other, cs);
            self.p_l_dir = dir;
        }
    }
}

pub struct Helper<K, V, C: Cs> {
    gp: Snapshot<Node<K, V, C>, C>,
    p: Snapshot<Node<K, V, C>, C>,
    l: Snapshot<Node<K, V, C>, C>,
    l_other: Snapshot<Node<K, V, C>, C>,
    new_internal: Snapshot<Node<K, V, C>, C>,
    pupdate: Snapshot<Update<K, V, C>, C>,
}

impl<K, V, C: Cs> Helper<K, V, C> {
    fn new() -> Self {
        Self {
            gp: Snapshot::new(),
            p: Snapshot::new(),
            l: Snapshot::new(),
            l_other: Snapshot::new(),
            new_internal: Snapshot::new(),
            pupdate: Snapshot::new(),
        }
    }

    fn load_insert<'g>(&'g mut self, op: &'g Update<K, V, C>, cs: &C) -> bool {
        self.p.load_from_weak(&op.p, cs)
            && self.l.load_from_weak(&op.l, cs)
            && self.l_other.load_from_weak(&op.l_other, cs)
            && self.new_internal.load_from_weak(&op.new_internal, cs)
    }

    fn load_delete<'g>(&'g mut self, op: &'g Update<K, V, C>, cs: &C) -> bool {
        self.gp.load_from_weak(&op.gp, cs)
            && self.p.load_from_weak(&op.p, cs)
            && self.l.load_from_weak(&op.l, cs)
            && self.l_other.load_from_weak(&op.l_other, cs)
            && self.pupdate.load_from_weak(&op.pupdate, cs)
    }
}

pub struct Cursor<K, V, C: Cs>(Finder<K, V, C>, Helper<K, V, C>);

pub struct EFRBTree<K, V, C: Cs> {
    root: AtomicRc<Node<K, V, C>, C>,
}

impl<K, V, C> EFRBTree<K, V, C>
where
    K: Ord + Clone,
    V: Clone,
    C: Cs,
{
    pub fn new(cs: &C) -> Self {
        Self {
            root: AtomicRc::new(
                Node::internal(
                    Key::Inf2,
                    None,
                    Node::leaf(Key::Inf1, None),
                    Node::leaf(Key::Inf2, None),
                    cs,
                ),
                cs,
            ),
        }
    }

    pub fn find(&self, key: &K, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        cursor.0.search(&self.root, key, cs);
        let l_node = cursor.0.l.as_ref().unwrap();
        l_node.key.eq(key)
    }

    pub fn insert(&self, key: K, value: V, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        loop {
            let finder = &mut cursor.0;
            finder.search(&self.root, &key, cs);
            let l_node = finder.l.as_ref().unwrap();
            let p_node = finder.p.as_ref().unwrap();

            if l_node.key == key {
                return false;
            } else if finder.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(&finder.pupdate, &mut cursor.1, cs);
            } else {
                let new = Node::leaf(Key::Fin(key.clone()), Some(value.clone()));
                let new_sibling = Node::leaf(l_node.key.clone(), l_node.value.clone());

                let (left, right) = match new.key.partial_cmp(&new_sibling.key) {
                    Some(std::cmp::Ordering::Less) => (new, new_sibling),
                    _ => (new_sibling, new),
                };

                let new_internal = Rc::new(
                    Node::internal(
                        // key field max(k, l → key)
                        right.key.clone(),
                        None,
                        // two child fields equal to new and newSibling
                        // (the one with the smaller key is the left child)
                        left,
                        right,
                        cs,
                    ),
                    cs,
                );

                let op = Update {
                    p: AtomicWeak::from(Weak::from_strong(&finder.p, cs)),
                    p_l_dir: finder.p_l_dir,
                    l: AtomicWeak::from(Weak::from_strong(&finder.l, cs)),
                    l_other: AtomicWeak::from(Weak::from_strong(&finder.l_other, cs)),
                    new_internal: AtomicWeak::from(Weak::from_strong(&new_internal, cs)),
                    gp: AtomicWeak::null(),
                    gp_p_dir: Direction::L,
                    pupdate: AtomicWeak::null(),
                };

                let new_pupdate = Rc::new(op, cs).with_tag(UpdateTag::IFLAG.bits());
                finder.new_update.protect(&new_pupdate, cs);

                match p_node.update.compare_exchange(
                    finder.pupdate.as_ptr(),
                    new_pupdate,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        self.help_insert(&finder.new_update, &mut cursor.1, cs);
                        return true;
                    }
                    Err(_) => {}
                }
            }
        }
    }

    pub fn delete(&self, key: &K, cursor: &mut Cursor<K, V, C>, cs: &C) -> bool {
        loop {
            let finder = &mut cursor.0;
            finder.search(&self.root, key, cs);

            if finder.gp.is_null() {
                // The tree is empty. There's no more things to do.
                return false;
            }

            let l_node = finder.l.as_ref().unwrap();

            if l_node.key != Key::Fin(key.clone()) {
                return false;
            }
            if finder.gpupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(&finder.gpupdate, &mut cursor.1, cs);
            } else if finder.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(&finder.pupdate, &mut cursor.1, cs);
            } else {
                let op = Update {
                    gp: AtomicWeak::from(Weak::from_strong(&finder.gp, cs)),
                    gp_p_dir: finder.gp_p_dir,
                    p: AtomicWeak::from(Weak::from_strong(&finder.p, cs)),
                    p_l_dir: finder.p_l_dir,
                    l: AtomicWeak::from(Weak::from_strong(&finder.l, cs)),
                    l_other: AtomicWeak::from(Weak::from_strong(&finder.l_other, cs)),
                    pupdate: AtomicWeak::from(Weak::from_strong(&finder.pupdate, cs)),
                    new_internal: AtomicWeak::null(),
                };

                let new_update = Rc::new(op, cs).with_tag(UpdateTag::DFLAG.bits());
                finder.pupdate.protect(&new_update, cs);

                match finder.gp.as_ref().unwrap().update.compare_exchange(
                    finder.gpupdate.as_ptr(),
                    new_update,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        if self.help_delete(&finder.pupdate, &mut cursor.1, cs) {
                            return true;
                        }
                    }
                    Err(_) => {}
                }
            }
        }
    }

    #[inline]
    fn help(&self, op: &Snapshot<Update<K, V, C>, C>, helper: &mut Helper<K, V, C>, cs: &C) {
        match UpdateTag::from_bits_truncate(op.tag()) {
            UpdateTag::IFLAG => self.help_insert(op, helper, cs),
            UpdateTag::MARK => self.help_marked(op, helper, cs),
            UpdateTag::DFLAG => {
                let _ = self.help_delete(op, helper, cs);
            }
            _ => unreachable!(),
        }
    }

    fn help_delete(
        &self,
        op: &Snapshot<Update<K, V, C>, C>,
        helper: &mut Helper<K, V, C>,
        cs: &C,
    ) -> bool {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        if !helper.load_delete(unsafe { op.deref() }, cs) {
            return false;
        }

        let gp_ref = helper.gp.as_ref().unwrap();
        let p_ref = helper.p.as_ref().unwrap();

        match p_ref.update.compare_exchange(
            helper.pupdate.as_ptr(),
            op.with_tag(UpdateTag::MARK.bits()),
            Ordering::Release,
            Ordering::Acquire,
            cs,
        ) {
            Ok(_) => {
                // (prev value) = op → pupdate
                self.help_marked(op, helper, cs);
                return true;
            }
            Err(e) => {
                if e.current == op.with_tag(UpdateTag::MARK.bits()).as_ptr() {
                    // (prev value) = <Mark, op>
                    self.help_marked(op, helper, cs);
                    return true;
                } else {
                    let _ = gp_ref.update.compare_exchange(
                        op.with_tag(UpdateTag::DFLAG.bits()).as_ptr(),
                        op.with_tag(UpdateTag::CLEAN.bits()),
                        Ordering::Release,
                        Ordering::Relaxed,
                        cs,
                    );
                    return false;
                }
            }
        }
    }

    fn help_marked(&self, op: &Snapshot<Update<K, V, C>, C>, helper: &mut Helper<K, V, C>, cs: &C) {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let op_ref = unsafe { op.deref() };
        if !helper.load_delete(op_ref, cs) {
            return;
        }

        let gp_ref = helper.gp.as_ref().unwrap();

        // dchild CAS
        let _ = gp_ref.child(op_ref.gp_p_dir).compare_exchange(
            helper.p.as_ptr(),
            &helper.l_other,
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        // dunflag CAS
        let _ = gp_ref.update.compare_exchange(
            op.with_tag(UpdateTag::DFLAG.bits()).as_ptr(),
            op.with_tag(UpdateTag::CLEAN.bits()),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }

    fn help_insert(&self, op: &Snapshot<Update<K, V, C>, C>, helper: &mut Helper<K, V, C>, cs: &C) {
        // Precondition: op points to a IInfo record (i.e., it is not ⊥)
        let op_ref = unsafe { op.deref() };
        if !helper.load_insert(op_ref, cs) {
            return;
        }

        let p_ref = helper.p.as_ref().unwrap();

        // ichild CAS
        let _ = p_ref.child(op_ref.p_l_dir).compare_exchange(
            helper.l.as_ptr(),
            &helper.new_internal,
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        // iunflag CAS
        let _ = p_ref.update.compare_exchange(
            op.with_tag(UpdateTag::IFLAG.bits()).as_ptr(),
            op.with_tag(UpdateTag::CLEAN.bits()),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }
}

#[cfg(test)]
fn smoke<C: Cs>() {
    extern crate rand;
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    let map = &{
        let cs = &C::new();
        EFRBTree::new(cs)
    };

    thread::scope(|s| {
        for t in 0..THREADS {
            s.spawn(move |_| {
                let cursor = &mut Cursor(Finder::new(), Helper::new());
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                for i in keys {
                    assert!(map.insert(i, i.to_string(), cursor, &C::new()));
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in 0..(THREADS / 2) {
            s.spawn(move |_| {
                let cursor = &mut Cursor(Finder::new(), Helper::new());
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let cs = &mut C::new();
                for i in keys {
                    assert!(map.delete(&i, cursor, cs));
                    assert_eq!(
                        i.to_string(),
                        *unsafe { cursor.0.l.deref() }.value.as_ref().unwrap()
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
                let cursor = &mut Cursor(Finder::new(), Helper::new());
                let rng = &mut rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(rng);
                let cs = &mut C::new();
                for i in keys {
                    assert!(map.find(&i, cursor, cs));
                    assert_eq!(
                        i.to_string(),
                        *unsafe { cursor.0.l.deref() }.value.as_ref().unwrap()
                    );
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
