use bitflags::bitflags;
use circ::{AtomicRc, CsHP, GraphNode, Pointer, Rc, Snapshot, StrongPtr, Weak};
use std::{mem::swap, sync::atomic::Ordering};

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
    update: AtomicRc<Update<K, V>, CsHP>,
    left: AtomicRc<Node<K, V>, CsHP>,
    right: AtomicRc<Node<K, V>, CsHP>,
    is_leaf: bool,
}

impl<K, V> GraphNode<CsHP> for Node<K, V> {
    const UNIQUE_OUTDEGREE: bool = false;

    #[inline]
    fn pop_outgoings(&self, _: &mut Vec<Rc<Self, CsHP>>)
    where
        Self: Sized,
    {
    }

    #[inline]
    fn pop_unique(&self) -> Rc<Self, CsHP>
    where
        Self: Sized,
    {
        unimplemented!()
    }
}

pub struct Update<K, V> {
    gp: Weak<Node<K, V>, CsHP>,
    gp_p_dir: Direction,
    p: Weak<Node<K, V>, CsHP>,
    p_l_dir: Direction,
    l: Rc<Node<K, V>, CsHP>,
    l_other: Rc<Node<K, V>, CsHP>,
    pupdate: Rc<Update<K, V>, CsHP>,
    new_internal: Rc<Node<K, V>, CsHP>,
}

impl<K, V> GraphNode<CsHP> for Update<K, V> {
    const UNIQUE_OUTDEGREE: bool = false;

    #[inline]
    fn pop_outgoings(&self, _: &mut Vec<Rc<Self, CsHP>>)
    where
        Self: Sized,
    {
    }

    #[inline]
    fn pop_unique(&self) -> Rc<Self, CsHP>
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

    pub fn child(&self, dir: Direction) -> &AtomicRc<Node<K, V>, CsHP> {
        match dir {
            Direction::L => &self.left,
            Direction::R => &self.right,
        }
    }
}

pub struct Finder<K, V> {
    gp: Snapshot<Node<K, V>, CsHP>,
    gp_p_dir: Direction,
    p: Snapshot<Node<K, V>, CsHP>,
    p_l_dir: Direction,
    l: Snapshot<Node<K, V>, CsHP>,
    l_other: Snapshot<Node<K, V>, CsHP>,
    pupdate: Snapshot<Update<K, V>, CsHP>,
    gpupdate: Snapshot<Update<K, V>, CsHP>,
    new_update: Snapshot<Update<K, V>, CsHP>,
}

impl<K, V> Finder<K, V> {
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
}

impl<K, V> Finder<K, V>
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
    fn search(&mut self, root: &AtomicRc<Node<K, V>, CsHP>, key: &K, cs: &CsHP) {
        self.l.load(root, cs);
        loop {
            let l_node = unsafe { self.l.deref() };
            if l_node.is_leaf {
                break;
            }
            Snapshot::swap(&mut self.gp, &mut self.p);
            swap(&mut self.gp_p_dir, &mut self.p_l_dir);
            Snapshot::swap(&mut self.p, &mut self.l);
            Snapshot::swap(&mut self.gpupdate, &mut self.pupdate);
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

pub struct Helper<K, V> {
    gp: Snapshot<Node<K, V>, CsHP>,
    p: Snapshot<Node<K, V>, CsHP>,
}

impl<K, V> Helper<K, V> {
    fn new() -> Self {
        Self {
            gp: Snapshot::new(),
            p: Snapshot::new(),
        }
    }

    fn load_delete(
        &mut self,
        op: &Snapshot<Update<K, V>, CsHP>,
        cs: &CsHP,
    ) -> Option<(&Update<K, V>, &Node<K, V>, &Node<K, V>)> {
        let op_ref = unsafe { op.deref() };

        let gp_ref = if self.gp.protect_weak(&op_ref.gp, cs) {
            self.gp.as_ref().unwrap()
        } else {
            return None;
        };

        let p_ref = if self.p.protect_weak(&op_ref.p, cs) {
            self.p.as_ref().unwrap()
        } else {
            // Unflag to preserve lock-freedom.
            let _ = gp_ref.update.compare_exchange_tag(
                op.with_tag(UpdateTag::DFLAG.bits()),
                UpdateTag::CLEAN.bits(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            );
            return None;
        };

        Some((op_ref, gp_ref, p_ref))
    }
}

pub struct Cursor<K, V> {
    finder: Finder<K, V>,
    helper: Helper<K, V>,
    helping_op1: Snapshot<Update<K, V>, CsHP>,
    helping_op2: Snapshot<Update<K, V>, CsHP>,
}

impl<K, V> Cursor<K, V> {
    fn default() -> Self {
        Self {
            finder: Finder::new(),
            helper: Helper::new(),
            helping_op1: Snapshot::new(),
            helping_op2: Snapshot::new(),
        }
    }

    fn output(&self) -> &V {
        unsafe { self.finder.l.deref() }.value.as_ref().unwrap()
    }
}

pub struct EFRBTree<K, V> {
    root: AtomicRc<Node<K, V>, CsHP>,
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
    pub fn find(&self, key: &K, cursor: &mut Cursor<K, V>, cs: &CsHP) -> bool {
        cursor.finder.search(&self.root, key, cs);
        let l_node = cursor.finder.l.as_ref().unwrap();
        l_node.key.eq(key)
    }

    pub fn insert(&self, key: K, value: V, cursor: &mut Cursor<K, V>, cs: &CsHP) -> bool {
        loop {
            let finder = &mut cursor.finder;
            finder.search(&self.root, &key, cs);
            let l_node = finder.l.as_ref().unwrap();
            let p_node = finder.p.as_ref().unwrap();

            if l_node.key == key {
                return false;
            } else if finder.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(
                    &mut finder.pupdate,
                    &mut cursor.helping_op2,
                    &mut cursor.helper,
                    cs,
                );
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
                    p: finder.p.upgrade().downgrade(),
                    p_l_dir: finder.p_l_dir,
                    l: finder.l.upgrade(),
                    l_other: finder.l_other.upgrade(),
                    new_internal,
                    gp: Weak::null(),
                    gp_p_dir: Direction::L,
                    pupdate: Rc::null(),
                };

                let new_pupdate = Rc::new(op).with_tag(UpdateTag::IFLAG.bits());
                finder.new_update.protect(&new_pupdate, cs);

                match p_node.update.compare_exchange_protecting_current(
                    finder.pupdate.as_ptr(),
                    new_pupdate,
                    &mut cursor.helping_op1,
                    Ordering::Release,
                    Ordering::Relaxed,
                    cs,
                ) {
                    Ok(_) => {
                        self.help_insert(&finder.new_update, &mut cursor.helper, cs);
                        return true;
                    }
                    Err(e) => unsafe {
                        let new_pupdate = e.desired.into_inner().unwrap();
                        drop(new_pupdate.new_internal.into_inner().unwrap());
                        self.help(
                            &mut cursor.helping_op1,
                            &mut cursor.helping_op2,
                            &mut cursor.helper,
                            cs,
                        );
                    },
                }
            }
        }
    }

    pub fn delete(&self, key: &K, cursor: &mut Cursor<K, V>, cs: &CsHP) -> bool {
        loop {
            let finder = &mut cursor.finder;
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
                self.help(
                    &mut finder.gpupdate,
                    &mut cursor.helping_op2,
                    &mut cursor.helper,
                    cs,
                );
            } else if finder.pupdate.tag() != UpdateTag::CLEAN.bits() {
                self.help(
                    &mut finder.pupdate,
                    &mut cursor.helping_op2,
                    &mut cursor.helper,
                    cs,
                );
            } else {
                let op = Update {
                    gp: finder.gp.upgrade().downgrade(),
                    gp_p_dir: finder.gp_p_dir,
                    p: finder.p.upgrade().downgrade(),
                    p_l_dir: finder.p_l_dir,
                    l: finder.l.upgrade(),
                    l_other: finder.l_other.upgrade(),
                    pupdate: finder.pupdate.upgrade(),
                    new_internal: Rc::null(),
                };

                let new_update = Rc::new(op).with_tag(UpdateTag::DFLAG.bits());
                finder.pupdate.protect(&new_update, cs);

                match finder
                    .gp
                    .as_ref()
                    .unwrap()
                    .update
                    .compare_exchange_protecting_current(
                        finder.gpupdate.as_ptr(),
                        new_update,
                        &mut cursor.helping_op1,
                        Ordering::Release,
                        Ordering::Relaxed,
                        cs,
                    ) {
                    Ok(_) => {
                        if self.help_delete(
                            &mut finder.pupdate,
                            &mut cursor.helping_op1,
                            &mut cursor.helper,
                            cs,
                        ) {
                            return true;
                        }
                    }
                    Err(e) => unsafe {
                        drop(e.desired.into_inner().unwrap());
                        self.help(
                            &mut cursor.helping_op1,
                            &mut cursor.helping_op2,
                            &mut cursor.helper,
                            cs,
                        );
                    },
                }
            }
        }
    }

    #[inline]
    fn help(
        &self,
        op: &mut Snapshot<Update<K, V>, CsHP>,
        aux: &mut Snapshot<Update<K, V>, CsHP>,
        helper: &mut Helper<K, V>,
        cs: &CsHP,
    ) {
        match UpdateTag::from_bits_truncate(op.tag()) {
            UpdateTag::IFLAG => self.help_insert(op, helper, cs),
            UpdateTag::MARK => self.help_marked(op, helper, cs),
            UpdateTag::DFLAG => {
                let _ = self.help_delete(op, aux, helper, cs);
            }
            _ => {}
        }
    }

    fn help_delete(
        &self,
        op: &mut Snapshot<Update<K, V>, CsHP>,
        aux: &mut Snapshot<Update<K, V>, CsHP>,
        helper: &mut Helper<K, V>,
        cs: &CsHP,
    ) -> bool {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let (op_ref, gp_ref, p_ref) = some_or!(helper.load_delete(op, cs), return false);

        match p_ref.update.compare_exchange_protecting_current(
            op_ref.pupdate.as_ptr(),
            op.upgrade().with_tag(UpdateTag::MARK.bits()),
            aux,
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
                if e.current == op.as_ptr().with_tag(UpdateTag::MARK.bits()) {
                    // (prev value) = <Mark, op>
                    self.help_marked(op, helper, cs);
                    return true;
                } else {
                    let _ = gp_ref.update.compare_exchange_tag(
                        op.with_tag(UpdateTag::DFLAG.bits()),
                        UpdateTag::CLEAN.bits(),
                        Ordering::Release,
                        Ordering::Relaxed,
                        cs,
                    );
                    self.help(aux, op, helper, cs);
                    return false;
                }
            }
        }
    }

    fn help_marked(&self, op: &Snapshot<Update<K, V>, CsHP>, helper: &mut Helper<K, V>, cs: &CsHP) {
        // Precondition: op points to a DInfo record (i.e., it is not ⊥)
        let (op_ref, gp_ref, _) = some_or!(helper.load_delete(op, cs), return);

        // dchild CAS
        let _ = gp_ref.child(op_ref.gp_p_dir).compare_exchange(
            op_ref.p.as_ptr(),
            op_ref.l_other.clone(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        // dunflag CAS
        let _ = gp_ref.update.compare_exchange_tag(
            op.with_tag(UpdateTag::DFLAG.bits()),
            UpdateTag::CLEAN.bits(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }

    fn help_insert(&self, op: &Snapshot<Update<K, V>, CsHP>, helper: &mut Helper<K, V>, cs: &CsHP) {
        // Precondition: op points to a IInfo record (i.e., it is not ⊥)
        let op_ref = unsafe { op.deref() };
        if !helper.p.protect_weak(&op_ref.p, cs) {
            return;
        }

        let p_ref = helper.p.as_ref().unwrap();

        // ichild CAS
        let _ = p_ref.child(op_ref.p_l_dir).compare_exchange(
            op_ref.l.as_ptr(),
            op_ref.new_internal.clone(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );

        // iunflag CAS
        let _ = p_ref.update.compare_exchange_tag(
            op.with_tag(UpdateTag::IFLAG.bits()),
            UpdateTag::CLEAN.bits(),
            Ordering::Release,
            Ordering::Relaxed,
            cs,
        );
    }
}

#[test]
fn smoke() {
    extern crate rand;
    use circ::{Cs, CsHP};
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    let map = &EFRBTree::new();

    thread::scope(|s| {
        for t in 0..THREADS {
            s.spawn(move |_| {
                let output = &mut Cursor::default();
                let mut rng = rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(&mut rng);
                for i in keys {
                    assert!(map.insert(i, i.to_string(), output, &CsHP::new()));
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in 0..(THREADS / 2) {
            s.spawn(move |_| {
                let output = &mut Cursor::default();
                let mut rng = rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(&mut rng);
                let cs = &mut CsHP::new();
                for i in keys {
                    assert!(map.delete(&i, output, cs));
                    assert_eq!(i.to_string(), *output.output());
                    cs.clear();
                }
            });
        }
    })
    .unwrap();

    thread::scope(|s| {
        for t in (THREADS / 2)..THREADS {
            s.spawn(move |_| {
                let output = &mut Cursor::default();
                let mut rng = rand::thread_rng();
                let mut keys: Vec<i32> =
                    (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                keys.shuffle(&mut rng);
                let cs = &mut CsHP::new();
                for i in keys {
                    assert!(map.find(&i, output, cs));
                    assert_eq!(i.to_string(), *output.output());
                    cs.clear();
                }
            });
        }
    })
    .unwrap();
}
