#![feature(linkage)]
#![allow(nonstandard_style, unused, unsafe_op_in_unsafe_fn)]
extern crate reussir_rt;

    extern crate leanrt;
    use reussir_rt::rc::Rc;
    use reussir_rt::collections::vec::Vec as RVecImpl;

#[linkage = "weak_odr"]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _RC16l2r_getenv_value_ffi(r#name: ::reussir_rt::rc::Rc<::std::vec::Vec<u8>>) -> ::reussir_rt::rc::Rc<::std::vec::Vec<u8>> {
    {
        let v = std::env::var_os(std::ffi::OsStr::new(std::str::from_utf8(&name).unwrap_or("\0"))).unwrap_or_default();
        leanrt::string::from_bytes_lossy(std::os::unix::ffi::OsStrExt::as_bytes(v.as_os_str()))
    }
}
