#![feature(linkage)]
#![allow(nonstandard_style, unused, unsafe_op_in_unsafe_fn)]
extern crate reussir_rt;

    extern crate leanrt;
    use reussir_rt::rc::Rc;
    use reussir_rt::collections::vec::Vec as RVecImpl;

#[linkage = "weak_odr"]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _RC16l2r_fs_hard_link_ffi(r#a: ::reussir_rt::rc::Rc<::std::vec::Vec<u8>>, r#b: ::reussir_rt::rc::Rc<::std::vec::Vec<u8>>) -> u64 { { leanrt::fs::hard_link(&a, &b); leanrt::rc_release(a); leanrt::rc_release(b); 0 } }
