use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};
use std::mem::{self, MaybeUninit};

const DATA_WORDS: usize = 3;
type DeferredData = [usize; DATA_WORDS];

#[derive(Debug, Clone, Copy)]
pub(crate) struct Retired {
    pub(crate) ptr: *mut u8,
    data: MaybeUninit<DeferredData>,
    call: unsafe fn(*mut u8),
}

// TODO: require <T: Send> in retire
unsafe impl Send for Retired {}

impl Retired {
    pub(crate) fn new<F: FnOnce()>(ptr: *mut u8, f: F) -> Self {
        let size = mem::size_of::<F>();
        let align = mem::align_of::<F>();

        unsafe {
            if size <= mem::size_of::<DeferredData>() && align <= mem::align_of::<DeferredData>() {
                let mut data = MaybeUninit::<DeferredData>::uninit();
                ptr::write(data.as_mut_ptr().cast::<F>(), f);

                unsafe fn call<F: FnOnce()>(raw: *mut u8) {
                    let f: F = ptr::read(raw.cast::<F>());
                    f();
                }

                Self {
                    ptr,
                    data,
                    call: call::<F>,
                }
            } else {
                let b: Box<F> = Box::new(f);
                let mut data = MaybeUninit::<DeferredData>::uninit();
                ptr::write(data.as_mut_ptr().cast::<Box<F>>(), b);

                unsafe fn call<F: FnOnce()>(raw: *mut u8) {
                    // It's safe to cast `raw` from `*mut u8` to `*mut Box<F>`, because `raw` is
                    // originally derived from `*mut Box<F>`.
                    let b: Box<F> = ptr::read(raw.cast::<Box<F>>());
                    (*b)();
                }

                Self {
                    ptr,
                    data,
                    call: call::<F>,
                }
            }
        }
    }

    pub(crate) unsafe fn call(mut self) {
        let call = self.call;
        unsafe { call(self.data.as_mut_ptr().cast::<u8>()) };
    }
}

#[derive(Debug)]
pub(crate) struct RetiredList {
    head: AtomicPtr<RetiredListNode>,
}

#[derive(Debug)]
struct RetiredListNode {
    retireds: Vec<Retired>,
    next: *const RetiredListNode,
}

impl RetiredList {
    pub(crate) const fn new() -> Self {
        Self {
            head: AtomicPtr::new(core::ptr::null_mut()),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }

    pub(crate) fn push(&self, retireds: Vec<Retired>) {
        let new = Box::leak(Box::new(RetiredListNode {
            retireds,
            next: ptr::null_mut(),
        }));

        let mut head = self.head.load(Ordering::Relaxed);
        loop {
            new.next = head;
            match self
                .head
                .compare_exchange(head, new, Ordering::Release, Ordering::Relaxed)
            {
                Ok(_) => return,
                Err(head_new) => head = head_new,
            }
        }
    }

    pub(crate) fn pop_all(&self) -> Vec<Retired> {
        let mut cur = self.head.swap(core::ptr::null_mut(), Ordering::Acquire);
        let mut retireds = Vec::new();
        while !cur.is_null() {
            let mut cur_box = unsafe { Box::from_raw(cur) };
            retireds.append(&mut cur_box.retireds);
            cur = cur_box.next.cast_mut();
        }
        retireds
    }
}
