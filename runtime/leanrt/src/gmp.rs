//! Raw bindings to the parts of GMP the bignum code uses.
//!
//! GMP is linked statically (Lean's toolchain ships `libgmp.a`; Lean's own
//! runtime uses the same library for its big numbers). The `mpn` layer works
//! on little-endian limb slices owned by Rust; the `mpz` layer is used for
//! the rarer operations, with inputs viewed through `mpz_roinit_n` (no copy)
//! and outputs copied back into Rust vectors.

#![allow(non_camel_case_types, dead_code)]

pub type mp_limb_t = u64;
pub type mp_size_t = i64;

/// `__mpz_struct`.
#[repr(C)]
pub struct Mpz {
    pub alloc: i32,
    pub size: i32,
    pub d: *mut mp_limb_t,
}

extern "C" {
    pub fn __gmpn_add(rp: *mut u64, s1p: *const u64, s1n: i64, s2p: *const u64, s2n: i64) -> u64;
    pub fn __gmpn_add_1(rp: *mut u64, s1p: *const u64, n: i64, b: u64) -> u64;
    pub fn __gmpn_sub(rp: *mut u64, s1p: *const u64, s1n: i64, s2p: *const u64, s2n: i64) -> u64;
    pub fn __gmpn_sub_1(rp: *mut u64, s1p: *const u64, n: i64, b: u64) -> u64;
    pub fn __gmpn_cmp(s1p: *const u64, s2p: *const u64, n: i64) -> i32;
    pub fn __gmpn_mul(rp: *mut u64, s1p: *const u64, s1n: i64, s2p: *const u64, s2n: i64) -> u64;
    pub fn __gmpn_mul_1(rp: *mut u64, s1p: *const u64, n: i64, b: u64) -> u64;
    pub fn __gmpn_sqr(rp: *mut u64, s1p: *const u64, n: i64);
    pub fn __gmpn_tdiv_qr(qp: *mut u64, rp: *mut u64, qxn: i64, np: *const u64, nn: i64, dp: *const u64, dn: i64);
    pub fn __gmpn_divrem_1(qp: *mut u64, qxn: i64, np: *const u64, nn: i64, d: u64) -> u64;
    pub fn __gmpn_mod_1(np: *const u64, nn: i64, d: u64) -> u64;
    pub fn __gmpn_get_str(s: *mut u8, base: i32, s1p: *mut u64, s1n: i64) -> usize;
    pub fn __gmpn_set_str(rp: *mut u64, s: *const u8, len: usize, base: i32) -> i64;
    pub fn __gmpn_sizeinbase(xp: *const u64, n: i64, base: i32) -> usize;
    pub fn __gmpn_lshift(rp: *mut u64, up: *const u64, n: i64, cnt: u32) -> u64;
    pub fn __gmpn_rshift(rp: *mut u64, up: *const u64, n: i64, cnt: u32) -> u64;
    pub fn __gmpn_and_n(rp: *mut u64, s1p: *const u64, s2p: *const u64, n: i64);
    pub fn __gmpn_ior_n(rp: *mut u64, s1p: *const u64, s2p: *const u64, n: i64);
    pub fn __gmpn_xor_n(rp: *mut u64, s1p: *const u64, s2p: *const u64, n: i64);

    pub fn __gmpz_init(x: *mut Mpz);
    pub fn __gmpz_clear(x: *mut Mpz);
    pub fn __gmpz_roinit_n(x: *mut Mpz, xp: *const u64, xs: i64) -> *const Mpz;
    pub fn __gmpz_add(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_sub(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_mul(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_neg(r: *mut Mpz, a: *const Mpz);
    pub fn __gmpz_tdiv_q(q: *mut Mpz, n: *const Mpz, d: *const Mpz);
    pub fn __gmpz_tdiv_r(r: *mut Mpz, n: *const Mpz, d: *const Mpz);
    pub fn __gmpz_tdiv_qr(q: *mut Mpz, r: *mut Mpz, n: *const Mpz, d: *const Mpz);
    pub fn __gmpz_divexact(q: *mut Mpz, n: *const Mpz, d: *const Mpz);
    pub fn __gmpz_pow_ui(r: *mut Mpz, b: *const Mpz, e: u64);
    pub fn __gmpz_gcd(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_and(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_ior(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_xor(r: *mut Mpz, a: *const Mpz, b: *const Mpz);
    pub fn __gmpz_mul_2exp(r: *mut Mpz, a: *const Mpz, k: u64);
    pub fn __gmpz_tdiv_q_2exp(r: *mut Mpz, a: *const Mpz, k: u64);
    pub fn __gmpz_fdiv_q_2exp(r: *mut Mpz, a: *const Mpz, k: u64);
}

/// An owned `mpz_t` (cleared on drop).
pub struct OwnedMpz(pub Mpz);

impl OwnedMpz {
    pub fn new() -> Self {
        let mut z = Mpz { alloc: 0, size: 0, d: std::ptr::null_mut() };
        unsafe { __gmpz_init(&mut z) };
        OwnedMpz(z)
    }
    pub fn ptr(&mut self) -> *mut Mpz {
        &mut self.0
    }
    /// Sign and magnitude limbs of the value.
    pub fn to_parts(&self) -> (bool, Vec<u64>) {
        let n = self.0.size.unsigned_abs() as usize;
        let limbs = if n == 0 { Vec::new() } else { unsafe { std::slice::from_raw_parts(self.0.d, n) }.to_vec() };
        (self.0.size < 0, limbs)
    }
}

impl Drop for OwnedMpz {
    fn drop(&mut self) {
        unsafe { __gmpz_clear(&mut self.0) }
    }
}

/// A read-only `mpz_t` view of a sign-magnitude value. The limbs must stay
/// alive (and unmodified) while the view is used.
pub struct View(pub Mpz);

impl View {
    pub fn new(neg: bool, limbs: &[u64]) -> Self {
        let mut z = Mpz { alloc: 0, size: 0, d: std::ptr::null_mut() };
        let n = limbs.len() as i64;
        unsafe { __gmpz_roinit_n(&mut z, limbs.as_ptr(), if neg { -n } else { n }) };
        View(z)
    }
    pub fn ptr(&self) -> *const Mpz {
        &self.0
    }
}
