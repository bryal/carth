use libc::*;

#[link(name = "sigsegv")]
extern "C" {
    pub fn stackoverflow_install_handler(
        handler: stackoverflow_handler_t,
        extra_stack: *mut c_void,
        extra_stack_size: usize,
    ) -> c_int;
}

#[link(name = "gc")]
extern "C" {
    pub fn GC_malloc(size: size_t) -> *mut c_void;
}

pub type stackoverflow_context_t = *mut c_void;

pub type stackoverflow_handler_t = extern "C" fn(emergency: c_int, scp: stackoverflow_context_t);
