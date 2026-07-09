# δ* sweep A25 — Negative-association of line-incidence indicators (Shao convex-transfer route): REFUTED

**Date:** 2026-06-14 · **Actionable:** A25 (merged 407-T22) · **Type:** numerical-probe
**Artifact:** `scripts/probes/sweep_a25_neg_assoc.py` · **Status:** REFUTED (the route), with a
sharp structural reason.

## The hypothesis (407-T22)

The prize "list-form" reduces (`FarCosetExplosion.epsMCA_ge_far_incidence`) to bounding the
worst-case far-line incidence
`inc(δ) = #{γ ∈ F_q : u₀ + γ·u₁ is δ-close to RS[k] on μ_n}`.
The provable per-witness union bound is `C(n,w)` (wall W1); the true worst incidence is `~n`.
The named-but-untested hope was:

> If the `n²` monomial-line ball-membership indicators are **negatively associated (NA)**,
> then **Shao (2000)** convex-order transfer gives the binomial tail
> `E[C(L,t)] ≤ μ^t/t!` *worst-case-included* — a **non-moment** route reaching budget `n` —
> and the **Dubhashi–Ranjan** "sampling-without-replacement" certificate (interpolation
> through a `k`-subset) is the candidate way to *prove* NA.

A25 asks to test whether NA actually holds, and to resolve the tension with the
"union-bound-forces-deep-moments" argument by checking whether NA gives the tail directly
without the union bound.

## What was measured (exact arithmetic, prize-shaped `n=16, k=4, ρ=1/4`, q ≡ 1 mod n)

The bounded (q-independent) far-line band is `w=6, δ=0.625, dir=(5,6)`, with `#bad = 32`(q=97)
/ `16`(q=193,257,353) — the object `inc ~ n`. (`n=8/k=2` has **no** bounded intermediate band
— a sharp cliff, explosion at `w=2` then `0` at `w≥3` — so the membership object only exists at
`n≥16`.) Three indicator families were tested:

**(M1) seed-included `k`-subset interpolation membership** `X_j = 1[c_T(x_j)=v_j]`, randomness =
random interpolation set `T`. Pairwise covariances are **all ≤ 0** and the disjoint-block
`Cov(ΣX_left, ΣX_right) ≈ −0.79`. *Looks NA-consistent — but this is an artifact:* `X_j=1` is
forced for `j∈T`, so the negative covariance is the **trivial DR-NA of the seed *selection***,
not of the agreement structure.

**(M1′) excess-agreement indicators (seed stripped)** `Z_j = 1[j∉T ∧ c_T(x_j)=v_j]` — the
**actual Shao-tail object** (`C(L,t)=ΣZ_j` = agreement beyond the `k`-seed). Here NA **FAILS**:
positive **exact-rational** pairwise covariance appears at every prime.

| q   | #bad | E[ΣZ]  | max Cov(Z_i,Z_j) exact | #pos pairs / 120 | P[ΣZ≥2] | Poisson tail | ratio |
|-----|-----:|-------:|------------------------|-----------------:|--------:|-------------:|------:|
| 97  | 32   | 0.1456 | **+463/473200**        | 38               | 0.0247  | 0.0096       | 2.57× |
| 193 | 16   | 0.0714 | **+251/473200**        | 15               | 0.0082  | 0.0024       | 3.39× |
| 257 | 16   | 0.0522 | **+883/1656200**       | 15               | 0.0082  | 0.0013       | 6.27× |
| 353 | 16   | 0.0549 | **+443/828100**        | 15               | 0.0082  | 0.0015       | 5.66× |

**(M2) scalar-incidence grid** (the `n²` directions × q scalars): cross-direction covariance is
**positive** (`+0.0556`, dirs `(5,6)`↔`(6,7)` at q=97). Directions are positively correlated.

## Verdict: REFUTED, three independent ways

1. **NA of the operative (excess) indicators is FALSE.** Stripping the seed-forced 1s — i.e.
   looking at the quantity Shao's transfer actually bounds — exposes **exact, provably positive**
   pairwise covariance at every prime. The seed-included negative covariance was a red herring
   (the DR-NA of subset selection, which has nothing to do with the agreement geometry).

2. **The Dubhashi–Ranjan certificate is structurally INAPPLICABLE.** DR proves NA only for a
   **fixed-size** without-replacement sample (`Σ` indicators = constant, the permutation /
   hypergeometric law). Here `ΣX_j` is **not** constant (range `[4,6]`); `ΣZ_j` ranges `{0,1,2}`.
   The number of "ones" is exactly the random quantity under study, so there is no permutation
   structure to invoke. The certificate named in A25 cannot even be *stated* for this object.

3. **The tail is HEAVIER than binomial — the diagnostic signature of POSITIVE association.**
   `P[ΣZ≥2]` exceeds the Poisson/binomial `μ^t/t!` target by `2.6×→6.3×`, **growing with q**.
   This is precisely the worst-line clustering the deep-moment hierarchy must see; an NA bound
   would *cap* the tail at binomial, but the real tail *exceeds* it. So **NA does NOT give the
   tail directly** — the opposite holds.

**Resolution of the tension (the A25 question).** The clustering is the rigidity of low-degree
interpolation: a degree-`<k` codeword agreeing with `v` on the seed makes *additional* agreements
positively correlated (they all lie on the same algebraic curve). Sampling-without-replacement
is NA because its total is *fixed*; the agreement count's total is *free and heavy-tailed*, which
is the entire phenomenon. Hence the **union-bound-forces-deep-moments argument stands**: there is
no NA-based non-moment shortcut to budget `n`. The Shao route is dead.

## Scope / honesty

- This is **numerical evidence** (exact integer arithmetic over `F_q`, `n=16` fully enumerated:
  `C(16,4)=1820` subsets × all `q−1` scalars), not a proof. It refutes the *route* (NA + Shao),
  not the underlying δ* conjecture, which remains open on the same deep-moment / generalized-Paley
  wall as faces 3↔4 of the open core.
- `n=32` (`C(32,8)=10.5M` subsets) was not enumerated; the `n=16` verdict (positive cov at every
  prime + non-constant `ΣX` + heavy tail) is structural and would only re-confirm.
- No closure is claimed. One more dead route, cleanly killed with an explicit reason.

## Cross-refs

- `scripts/probes/probe_monomial_incidence_qindependence.py` — the bounded-band object.
- `FarCosetExplosion.lean` (`epsMCA_ge_far_incidence`) — the incidence reduction.
- Memory `arklib-389-deep-moment-wall` — the union-bound-forces-deep-moments wall this confirms.
- UNFINISHED_THREADS_407.md cluster 7 (407-T22) — the lane this closes.
