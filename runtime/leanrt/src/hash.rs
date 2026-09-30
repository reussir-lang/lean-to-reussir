//! Lean's hash functions (`src/runtime/hash.{h,cpp}`), bit for bit: they
//! decide `HashMap` iteration order, which programs can observe.

const M: u64 = 0xc6a4a7935bd1e995;
const R: u32 = 47;

/// MurmurHash64A, as used by `lean_string_hash` (seed 11) and
/// `ByteArray.hash`.
pub fn murmur64a(data: &[u8], seed: u64) -> u64 {
    let len = data.len();
    let mut h = seed ^ (len as u64).wrapping_mul(M);
    let mut chunks = data.chunks_exact(8);
    for c in &mut chunks {
        let mut k = u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    let rest = chunks.remainder();
    if !rest.is_empty() {
        for (i, &b) in rest.iter().enumerate().rev() {
            h ^= (b as u64) << (8 * i);
        }
        h = h.wrapping_mul(M);
    }
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// `lean_uint64_mix_hash` (`hash(u64, u64)` in `hash.h`). Note the
/// `k ^= m` step (not a multiplication), exactly as in Lean.
#[inline]
pub fn mix(h: u64, k: u64) -> u64 {
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

#[cfg(test)]
mod tests {
    #[test]
    fn empty() {
        // h = 11 ^ 0 = 11; finalization only.
        let mut h: u64 = 11;
        h ^= h >> 47;
        h = h.wrapping_mul(super::M);
        h ^= h >> 47;
        assert_eq!(super::murmur64a(b"", 11), h);
    }
}
