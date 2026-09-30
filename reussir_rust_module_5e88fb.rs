#![feature(linkage)]
#![allow(nonstandard_style, unused, unsafe_op_in_unsafe_fn)]
extern crate reussir_rt;

    extern crate leanrt;
    use reussir_rt::rc::Rc;
    use reussir_rt::collections::vec::Vec as RVecImpl;

#[repr(C)]
struct __ReussirArgs(::reussir_rt::collections::vec::Vec<u8>, u64, u64, ::reussir_rt::collections::vec::Vec<u8>, u64, u64);
#[linkage = "weak_odr"]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _RC17l2r_byteslice_beq_ffi(__reussir_args: *mut __ReussirArgs) -> bool {
    let __ReussirArgs(r#a, r#sa, r#ea, r#b, r#sb, r#eb) = unsafe { __reussir_args.read() };
    {
    {
        let x = leanrt::array::as_slice(&a).get(sa as usize..ea as usize).unwrap_or(&[]);
        let y = leanrt::array::as_slice(&b).get(sb as usize..eb as usize).unwrap_or(&[]);
        let r = x == y;
        leanrt::array::release(a);
        leanrt::array::release(b);
        r
    }
}
}
