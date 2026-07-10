# #466 R391 — the height ledger: every census relation certified by a bounded nonzero annihilator

## What landed (axiom-clean, real locked build 3339 jobs, first-try compile)

`Frontier/_R391RelationHeightLedger.lean`:

- `abs_le_of_mem_keysR`: realized keys have entries `|v_j| ≤ r`;
- `abs_sub_le_two_mul` / `relPoly_coeff_abs_le`: relation entries and polynomial
  coefficients are bounded by `2r`;
- **`relation_certificate_with_height`**: for `m = 2^k`, char `p`, `g^m = −1`, every
  vanishing nonzero relation `z` owns `N(z) = Res(X^m+1, relPoly z)` with
  `N(z) ≠ 0`, `p ∣ N(z)`, and `|N(z)| ≤ (2m)!·(2r)^{2m}`;
- **`sectorRelations_certificate_with_height`**: ditto for every member of every sector
  (entry bound extracted from any witnessing collision pair).

## The ledger is now generically complete

The r389 census identity `S = Σ_{z vanishing} M(z)` plus this brick means: at depth `r`,
dimension `m = 2^k`, EVERY contributing relation is certified by a nonzero integer of
height `≤ (2m)!·(2r)^{2m}`, divisible by the prime. This is exactly the FS1 double-count's
quantitative input (`H ≤ 2^L` shape), now available at every depth for the exact census
objects rather than depth-3 patterns only.

What the double-count yields from here (and what it cannot): summed over a prime FAMILY,
each annihilator value kills at most `log_p H ≈ (2m·log(2m) + 2m·log 2r)/log p` primes —
so almost-all-primes statements per relation family follow mechanically. What remains open
at prize scale (unchanged, stated honestly): the SINGLE-prime, ALL-relations count to
`r ≈ ln q` at `n = 2³⁰` — the number of distinct relations, not the per-relation prime
count, is where uniformity fails to be free. CORE OPEN, ON-BGK.
