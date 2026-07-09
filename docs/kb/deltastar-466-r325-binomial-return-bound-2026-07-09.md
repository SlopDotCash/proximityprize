# #466 R325 (Fable): binomial return-probability bound — the R321 hard step falls for the census class

Date: 2026-07-09 · Lane file: `Frontier/_R325BinomialRecurrenceReturnBound.lean`

## What was open

R321/R322 (`PrimitiveSaturationDichotomy`) left ONE named hard step: a uniform
return-probability / short-vector bound for the principal recurrence lattice
`L_f = f·ℤ[x]/(x^m+1)`, warned to be dangerous because "after Fourier duality it can
collapse back to the Paley spectrum — any proof must use the short/banded nature of `f`".
The R321 census: the top recurrence orbit is short in ALL 92 in-window `n=32` cells and
carries 71.7–100% (mean 95.6%) of off-diagonal collision mass; the exceptional `c=3`
violator is the binomial `3 + x^5`.

## The discovery

For the **binomial class** `f = a + b·x^s` with `|b| < |a|`, the bound is a two-line
max-coordinate argument — no cyclic-orbit unrolling, no Fourier, no Paley collapse:

> If every coordinate of the negacyclic product `g·f` is `≤ H` in absolute value, let
> `M = max_i |g_i|` be attained at `i₀`. The product coordinate there is
> `a·g_{i₀} ± b·g_{i₀−s}`, so `|a|·M ≤ H + |b|·M`, giving `M·(|a|−|b|) ≤ H`.

Hence `#(L_f ∩ [-H,H]^m) ≤ (2·⌊H/(|a|−|b|)⌋+1)^m` (multiplication by `f ≠ 0` is injective
on the domain). Against the trivial-count baseline `(2H+1)^m/|Res|` with
`|Res(x^m+1, a+b·x^s)| ∈ [(|a|−|b|)^m, (|a|+|b|)^m]`, this is exact up to the
`K^m`-type loss the dichotomy explicitly allows.

## What landed (axiom-clean)

* `banded_max_bound` — the abstract inequality for ANY single-off-diagonal banded map:
  arbitrary index map `σ`, arbitrary signed band values `|c i| ≤ b` (the negacyclic
  wraparound sign is absorbed into `c`), conclusion `∀ i, |g i|·(|a|−b) ≤ H`.
* `banded_preimage_card_le` — the short-vector count
  `≤ (2·(H/(|a|−b)).toNat + 1)^m` via injection into `piFinset (Icc (−K) K)`.

* `dominant_max_bound` — the general ℓ¹-diagonally-dominant version: ANY residual
  `|v i − a·g i| ≤ b·‖g‖_∞` with `b < |a|` gives the same conclusion — machine-checking
  that the only uncovered case of the R321 return-probability step is
  non-diagonally-dominant short `f`.
* `negacyclicBinomialMul{,_max_bound,_preimage_card_le}` — the concrete wiring on actual
  `ℤ[x]/(x^m+1)` coefficients (`a·g_i + ε_i·b·g_{i−s}`, wraparound sign `ε_i = −1` iff
  `i < s`), validated against a 60k-trial probe on the census violator `3 + x^5`, `m=16`
  (0 violations).

## R327 (same file): the fixed-prime short-relation cap, conditional only on saturation

R315 named the "genuinely hard fixed-prime counting statement" (bound relation mass at ONE
specified prize prime; FS1–FS6 only control the average over primes). Combining the two
new pieces closes it **conditional only on the R321 dyadic saturation**:

* `negacyclicBinomialMul_injective` — injectivity of dominant-binomial multiplication is
  FREE: apply the max-bound at `H = 0`.
* `saturated_kernel_card_le` — if every `d` in a height-`≤H` relation set `K` has
  `2^t·d` in the binomial recurrence lattice (`∃ g, g·(a+b·x^s) = 2^t·d` negacyclically),
  then `#K ≤ (2·(2^t·H/(|a|−|b|)).toNat + 1)^m`.

With `t ≤ 3` (census: quotient order ∈ {2,4,8} in all 92 cells, R321) and `|a|−|b| ≥ 2`
(census: all top orbits have even resultant cofactor, zero odd cofactors), the cap at
height `H = 2r` is `(2^t·2r/(|a|−|b|)·2+1)^m ≈ (2^{t+1}r)^m` — the same scale as the
unrestricted trivial count divided by the lattice index, i.e. exactly the
`exp(O(r))`-loss regime the R321 dichotomy declares acceptable.

Axiom audit: `[propext, Classical.choice, Quot.sound]` on all seven.

## What remains (the honest chain to the prize)

1. **Saturation as theorem, not census**: `PrimitiveSaturationDichotomy` (R321) — that at
   every in-window bad prime the evaluation kernel is dyadically saturated by ONE short
   (binomial/dominant) recurrence. Census-verified for all 92 `n=32` cells; general proof
   open. This is now THE single analytic gap on this route.
2. Non-diagonally-dominant short `f` (support > 2 with `|a| ≤ Σ|b_j|`): uncovered by the
   max-argument; census says such orbits carry ≤ 28.3% of mass in the worst cell.
3. Converting the relation-count cap into the DC-subtracted moment bound consumed by
   R240/R310 (bookkeeping against `relationMass`, not just relation count — mass weights
   are bounded by count × height² locally).
