# δ\* #464 — exact `canonicalRatioBadPrimes(64)` + the height-crosses-n⁴ finding

**Date:** 2026-06-27. **Status:** verified exact computation (probe), extends the in-tree exact
classification ladder one rung and independently confirms *why* the off-BGK floor route needs the
least-prime-in-AP input (TZ 12/5), not a height bound. Not a δ\* proof.

## Method (exact, validated)

`canonicalRatioBadPrimes(n) = primeFactors(Res_ℤ(Φ_n, (X⁴+1)^n − (X²+1)^n))`. For `n = 2^m`,
`Φ_n = X^{n/2}+1`, so `Res = ±det(mult-by-g)` in the order `ℤ[X]/(X^{n/2}+1)` where
`g = ((X⁴+1)^n − (X²+1)^n) mod (X^{n/2}+1)` (negacyclic, `X^{n/2}=−1`). Pure-integer Bareiss
determinant + Pollard-rho factorization (`scripts/probes/canon_badprimes.py`, in scratch).

**Validation against the in-tree exact theorems:**
- `n=16` → primitive-root lane `{17}` — matches `prime_eq_seventeen_of_polynomial_eq_zmod16`.
- `n=32` → primitive-root lane `{97, 641, 673, 1153}` — matches
  `prime_eq_97_or_641_or_673_or_1153_of_polynomial_eq_zmod32` / `canonicalN32PrimitiveBadPrimes`
  exactly (full factor list `{2,17,79,97,113,641,673,1153}` matches the Bezout-constant factors).

## New result: `canonicalRatioBadPrimes(64)` (primitive-root lane, `64 | p−1`)

```
{193, 257, 449, 641, 1153, 2689, 3137, 3457, 4993, 7937, 12161,
 156353, 697601, 7177601, 7204033, 7987009}      (16 primes)
```
(Full factor list also includes 2 and 929-class primes not ≡ 1 mod 64.)

Structural facts:
1. **Smallest bad prime = 193 = the smallest prime `≡ 1 (mod 64)`.** The floor-singleton pattern
   `min(bad) = smallestPrime(1 mod n)` persists exactly across `n = 16, 32, 64, 128`
   (`17, 97, 193, 257`; the n=128 lane was computed exactly, 41 primes, min `257`).
2. **The set grows** (`1 → 4 → 16` primes). The canonical width-four bad set is therefore a
   strictly *larger* predicate than the floor-bad singleton `{97}` (n=32) — consistent with the
   in-tree `canonicalN32PrimitiveBadPrimes_ne_singleton97`. Future floor arguments must not
   substitute the canonical local set for the modeled floor-bad predicate.
3. **`97 ∉ bad(64)`** correctly: `97 mod 64 = 33`, so `F_97` carries no primitive 64th root.

## The decision-relevant finding: max bad prime is exponential, crosses n⁴ (EXACT)

Also computed exactly at `n = 128` (full factorization; the primitive-root lane has **41** primes,
smallest `257 = smallestPrime(1 mod 128)`, largest `203712052621057`).

Max bad prime: `17, 1153, 7987009, 203712052621057` at `n = 16, 32, 64, 128`.
`ln(max) = 2.83, 7.05, 15.9, 33.0`, so `ln(max)/n ≈ 0.18, 0.22, 0.25, 0.258` — i.e.
**max bad prime ≈ exp(≈0.26·n)**, *exponential* in `n` (matching the dossier's "height is the
crude `2^n`" obstruction, §6.4/§9). Set sizes grow `1, 4, 16, 41`.

Consequence for the floor route, made concrete and **exactly confirmed** (no extrapolation):
- `n = 64`: `max = 7.99×10⁶ < 64⁴ = 1.68×10⁷` (ratio 0.48, up from 0.0003, 0.001).
- `n = 128`: `max = 2.04×10¹⁴ ≫ 128⁴ = 2.68×10⁸` (ratio ≈ 7.6×10⁵).
  **So the max bad prime crosses `n⁴` between `n=64` and `n=128` — confirmed by exact computation.**

⟹ A "every bad prime `< n⁴`" (polynomial-height) floor closure **fails**. Only the
**smallest** bad prime stays `< n⁴` — and that smallest bad prime is exactly
`smallestPrime(1 mod 2^a)`, whose `< (2^a)^{12/5}` bound is the Thorner–Zaman result confirmed in
`deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md`. This is an **independent
confirmation** that the floor route's correct analytic tool is least-prime-in-AP (TZ 12/5), not a
resultant-height bound.

## Landed Lean bricks (axiom-clean, 2026-06-27)

Two concrete witnesses now encode the bracket in Lean (both self-contained, `decide`-based):
- `Frontier/CanonicalBadPrimeHeightNoGoN128.lean` —
  `exists_canonical_badPrime_gt_n4_n128`: an explicit prime `p = 423237889 > 128⁴` with
  `128 ∣ p−1` and a primitive 128th root `ζ = 90645509` at which the canonical collision
  `(ζ⁴+1)¹²⁸ = (ζ²+1)¹²⁸` holds. **Refutes any polynomial-height floor closure.**
- `Frontier/CanonicalSmallestBadPrimeWitness.lean` —
  `smallest_ap_prime_is_canonical_bad`: at `n = 64, 128, 256` the least prime `≡ 1 (mod n)`
  (`193, 257, 257`) carries a primitive `n`-th root (`ζ = 39, 18, 3`) with the canonical
  collision, and the smallness `smallestPrime(1 mod n) = 193/257` is fully `decide`-checked.
  **Witnesses the floor-singleton lower containment** (least AP prime ∈ bad set).

Together they bracket the structure: `min(bad)` is the AP-controlled least prime (TZ 12/5),
`max(bad)` exceeds `n⁴`. Both are off-wall substrate, not a δ\* proof.

Note (n=256, 512 added): the exact primitive-root lane min at `n=256` is also `257`
(`257 = 256+1 ≡ 1 mod 256`); and a direct check (no full determinant needed) confirms
`7681 = smallestPrime(1 mod 512)` is canonical-bad (24 colliding primitive 512th roots, smallest
`ζ = 62`). So the `min(bad) = smallestPrime(1 mod n)` lower-containment pattern holds at **six rungs**
`n = 16, 32, 64, 128, 256, 512` (`17, 97, 193, 257, 257, 7681`).

This is exactly the §9 "conjugate-count no-go": the height is exponential, so only a
divisibility/existence question (does a *small* good/bad prime exist?) is tractable — never a
height bound on all bad primes.

## Honesty

This neither closes the prize nor proves the uniform-in-μ smallest-prime characterization (the
floor-bad *adjacency* predicate of §15 is a different, smaller object than this canonical
width-four resultant set; the pattern `min(bad) = smallestPrime(1 mod n)` is verified for the
canonical set at `n=16,32,64,128` but remains an empirical regularity, not a theorem). The δ\*
core stays OPEN and ON-BGK.
