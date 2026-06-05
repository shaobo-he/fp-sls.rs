//! Seedable random-number generation.
//!
//! Racket's OL1V3R uses the global `(random-seed n)` / `(random)` facility.
//! We cannot bit-reproduce Racket's generator, but a seeded [`StdRng`] gives
//! deterministic, reproducible runs for a given `--seed` within this port.

use rand::rngs::StdRng;
use rand::{Rng as _, RngCore, SeedableRng};
use rug::Integer;

/// Thin wrapper around a seedable PRNG exposing the few primitives the solver
/// needs: coin flips, uniform indices, and uniform bit-vectors.
pub struct Rng {
    inner: StdRng,
}

impl Rng {
    /// Seed the generator. Mirrors `(random-seed seed)`.
    pub fn from_seed(seed: u64) -> Self {
        Rng {
            inner: StdRng::seed_from_u64(seed),
        }
    }

    /// `(coin-flip p)` — true with probability `p`.
    pub fn coin_flip(&mut self, p: f64) -> bool {
        self.inner.gen::<f64>() < p
    }

    /// Uniform index in `[0, n)`. Mirrors `(random n)`.
    pub fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0);
        self.inner.gen_range(0..n)
    }

    /// Uniform integer in `[0, 2^width)`. Mirrors `(random-natural (expt 2 w))`.
    pub fn uniform_bits(&mut self, width: u32) -> Integer {
        if width == 0 {
            return Integer::new();
        }
        let nbytes = width.div_ceil(8) as usize;
        let mut bytes = vec![0u8; nbytes];
        self.inner.fill_bytes(&mut bytes);
        let mut v = Integer::from_digits(&bytes, rug::integer::Order::Lsf);
        // Mask to the low `width` bits so the result lies in [0, 2^width).
        let mask = (Integer::from(1) << width) - Integer::from(1);
        v &= mask;
        v
    }
}
