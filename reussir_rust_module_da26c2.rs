#![feature(linkage)]
#![allow(nonstandard_style, unused, unsafe_op_in_unsafe_fn)]
extern crate reussir_rt;

    extern crate leanrt;
    use reussir_rt::rc::Rc;
    use reussir_rt::collections::vec::Vec as RVecImpl;

#[linkage = "weak_odr"]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _RC11l2r_fs_read_ffi(r#h: ::reussir_rt::rc::Rc<::std::boxed::Box<dyn std::any::Any>>, r#n: u64) -> ::reussir_rt::collections::vec::Vec<u8> { leanrt::fs::owned::read(h, n) }
