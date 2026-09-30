#![feature(linkage)]
#![allow(nonstandard_style, unused, unsafe_op_in_unsafe_fn)]
extern crate reussir_rt;

    extern crate leanrt;
    use reussir_rt::rc::Rc;
    use reussir_rt::collections::vec::Vec as RVecImpl;

#[linkage = "weak_odr"]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _RC22lean_string_capitalize_ffi(r#s: ::reussir_rt::rc::Rc<::std::vec::Vec<u8>>) -> ::reussir_rt::rc::Rc<::std::vec::Vec<u8>> { leanrt::string::capitalize(s) }
