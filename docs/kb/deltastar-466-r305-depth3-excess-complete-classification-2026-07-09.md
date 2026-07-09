# #466 R305 — the depth-3 excess EXACTLY classified: cyclotomic difference classes, the complete bad-prime census, and a β=4.87 exact-Wick violator

## The theory (verified exact, all tested cells)

For `n = 2^k`, represent `μ_n` exactly in `ℤ[ζ]/Φ_n`, `Φ_n = x^{n/2}+1`: every char-0 3-sum
is an integer vector `w ∈ ℤ^{n/2}`, `|w|₁ ≤ 3`. With `N₃(w)` the char-0 3-sum histogram
(K = 5504 distinct vectors at n=32; `Σ N₃(w)² = 15n³−45n²+40n` — checks the closed form):

```text
excess(p, n) = Σ_{groups c} (Σ_{w(g)≡c} N₃(w))² − Σ_w N₃(w)²
```

i.e. the excess is EXACTLY the extra ℓ² mass created when distinct char-0 vectors collide
under the mod-p evaluation `w ↦ w(g)`, `g` of order n. Equivalently
`excess(p) = Σ_{z≠0, z(g)≡0 (p)} M(z)` over difference classes `z` with pair-mass `M(z)`.

**Verification (bit-exact against the r304 scans):** n=16: p=8929→1920, p=14401→960,
p=41521→480 ✓. n=32: p=32993→391680, p=35393→46080, p=21523361→58560 (double-checked
with the independent FFT method) ✓.

**Consequences (proved by the construction):**
- a bad prime must divide `|Norm(z)| ≤ 6^{φ(n)}` for some class `z` — so the bad set is
  FINITE and fully computable per n (census below);
- the fast evaluator computes exact excess in `O(K log K)` per prime — no p-sized arrays.

## Census results

- **n=16 (COMPLETE, all β)**: 40 bad primes total; the largest is p=41521 (β=3.835) — the
  n=16 depth-3 excess is now a CLOSED finite object. All 13 exact-Wick violations have
  β < 3 (largest violating prime 641, β=2.331), so the β ≥ 3 rung at n=16 is TRUE — now by
  complete enumeration, not scan evidence. Excess quantum over all bad primes: 48.
- **n=32, scan [2·10⁶, 10⁸] (β ∈ [4.19, 5.31])**: 163 bad primes; nonzero excess persists
  through β=5.29 (excess 3840 at p=92349473) — bad primes do NOT die out at prize-shaped β.
- **n=32, the β=4.87 violator (KEY FINDING)**: `p = 21523361 = (3¹⁶+1)/2` violates exact
  Wick (excess 58560 = 1.31×headroom) at β=4.872. Mechanism, read off the collision groups:
  the ENTIRE excess is the relation web of `ζ⁵ ≡ −3 (mod 𝔭)` — p divides
  `Norm(3+ζ) = 3¹⁶+1`. So **there is no β-frontier rescue**: primes dividing small-height
  cyclotomic norms (`c^{φ(n)}+1`-type families) produce exact-Wick violations at arbitrarily
  large β below the crude norm bound, whenever the associated relation web carries mass
  above the headroom.
- **n=32 (COMPLETE census — the depth-3 landscape at n=32 is now CLOSED)**: 1,594,368
  distinct difference classes, 2,345 distinct norms (max 2.82·10¹² = 6^{φ(32)}-scale), 1,158
  bad primes in total across ALL β, 156 exact-Wick violations. Established by the exhaustive
  finite computation (`_out_466_r305_census_n32.txt`):
  - the LARGEST exact-Wick violator is `p = 21523361 = (3¹⁶+1)/2` (β = 4.872) — for every
    prime `p > 21523361`, `E₃(p, 32) ≤ 15·32³` holds;
  - the LARGEST bad prime of any kind is `p = 3487801441` (β = 6.340) — beyond it the excess
    is identically zero (E₃ = char-0 closed form exactly);
  - the violation set in `[32³, 2·10⁶]` is exactly the 19 primes r304 found by scanning —
    the two independent methods agree on every compared prime;
  - excess quantum over all 1,158 bad primes: 96.

## What this changes

1. The depth-3 rung at fixed small n is now DECIDABLE-in-practice: the census is a finite
   exact computation (in principle Lean-decidable per n; the n=16 closure is a genuine
   theorem-shaped object: "bad(16) = {explicit 40-element set}, max β = 3.835").
2. The good-prime selection criterion at depth 3 is explicit: avoid primes dividing
   small-height cyclotomic norms — precisely the FiniteObstructionGoodPrime selector shape
   (#464) with the obstruction set now EXACTLY characterized (not just bracketed).
3. At prize n=2³⁰ the census itself is infeasible (K ~ n³) — the wall is untouched — but the
   MECHANISM transfers: prize-scale bad primes are divisors of small-height norms, and the
   ABF26 deployment question becomes whether the chosen prime family provably avoids the
   obstruction divisor set. This re-routes the depth-3 lane fully into Tier-1 item 4
   (floor-bad/good-prime), now with the right invariant.

Probes: `probe_r305_depth3_excess_classification.py` (difference classes + census),
`probe_r305_fast_excess_scanner.py` (O(K log K) exact scanner),
`probe_r305_complete_census.py` (total bad-prime table);
outputs `_out_466_r305_census_n16.txt`, `_out_466_r305_n32_highbeta.txt`,
`_out_466_r305_census_n32.txt`. CORE OPEN — this round replaces scan evidence with an exact
finite theory of the depth-3 obstruction.
