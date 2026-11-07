# #466 R325 (Fable): binomial short-vector count — valid, but with a `K^m` loss that does not close the R321 hard step

> **Later status (corrected 2026-10-28, audit T129).** The max-coordinate / injection theorems
> below are valid and kernel-checked. Three claims in the original note were wrong and are
> corrected in place:
> (1) the resulting cap loses a factor exponential in the *dimension* `m = n/2`. That is not the
> `exp(O(r))` loss the R321 dichotomy allows, because the depth is only `r = Θ(log n)`.
> (2) The proposed producer `|Res| ∣ 2^t·p` is infeasible at growing thin-prize parameters.
> `Frontier/_W12BinomialBadPrimeRefuted.lean` also refutes `BinomialBadPrimeLaw` outright in the
> `n = 32` and `n = 64` census windows.
> (3) Relation count times height² does not bound collision mass.
> So this route is **not** a one-gap closure. Evidence:
> `docs/audits/repository-review-2026-10-28/kb44-binomial-count-scale-check.json`.

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
on the domain). Compare the trivial-count baseline `(2H+1)^m/|Res|`, where
`|Res(x^m+1, a+b·x^s)| ∈ [(|a|−|b|)^m, (|a|+|b|)^m]`. The cap matches it only up to a
factor `K^m`, exponential in the dimension `m`. *(Correction, audit T129: the original note said
the dichotomy "explicitly allows" this loss. It does not. `PrimitiveSaturationDichotomy` (R321)
allows a `K^r` loss, where `r = Θ(log n)` is the walk depth. A `K^m` loss with `m = n/2` is far
larger and cannot be absorbed into `exp(O(r))`.)*

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
height `H = 2r` is `(2·⌊2^t·2r/(|a|−|b|)⌋+1)^m`, at most about `(2^{t+1}r)^m`.

*(Correction, audit T129.)* The original note said this is "the same scale as the unrestricted
trivial count divided by the lattice index", and so lies in the `exp(O(r))`-loss regime.
That is false:

* **Dimension loss.** Take the census violator shape `a = 3`, `b = 1`, an odd shift `s`, `t = 3`
  and `H = 2r`. The cap is `(16r+1)^m`. The lattice-volume baseline is
  `(4r+1)^m / |Res| = (4r+1)^m / (3^m+1)`. Their ratio tends to order `12^m` as `r` grows. At
  `m = 16`, `r = 17` it is already `2^57.107`. Since `m = n/2` and `r = Θ(log n)`, this `K^m`
  loss is not `exp(O(r))`. The cap is a valid upper bound, but it is not the uniform
  return-probability bound the dichotomy needs.
* **Resultant feasibility.** Every root of `x^m+1` has modulus 1, so `|a|−|b| ≥ 2` forces
  `|Res(x^m+1, a+b·x^s)| ≥ 2^m`. The producer hypothesis `|Res| ∣ 2^t·p` therefore needs
  `m ≤ t + log₂ p`. That fails at growing thin-prize parameters, with `m = n/2`, `t = O(1)`
  and `p` polynomial in `n`. Independently, `Frontier/_W12BinomialBadPrimeRefuted.lean`
  (`no_realized_binomial_dyadic_n32`, `no_realized_binomial_dyadic_n64`) rules out every
  realized dominant binomial with `|Res| ∣ 8p` at every prime of the `n = 32` and `n = 64`
  census windows. So the `|Res| ∣ 2^t·p` producer for the `t ≤ 3` binomial saturation
  hypothesis is never met there.

Axiom audit: `[propext, Classical.choice, Quot.sound]` on all seven.

## What remains (the honest chain to the prize)

*(Corrected 2026-10-28, audit T129. The original list called item 1 "THE single analytic gap".
It also asserted a count × height² mass bound. Both claims were wrong; see items 1, 3 and 4.)*

1. **Saturation as theorem, not census**: `PrimitiveSaturationDichotomy` (R321) says that at
   every in-window bad prime the evaluation kernel is dyadically saturated by ONE short
   recurrence. Its general proof is open. In its *binomial* form, fed by `|Res| ∣ 2^t·p`, it
   is refuted in the `n = 32` and `n = 64` windows by `Frontier/_W12BinomialBadPrimeRefuted.lean`.
   It is also infeasible for growing `m`, since `|Res| ≥ 2^m`.
2. Non-diagonally-dominant short `f` (support > 2 with `|a| ≤ Σ|b_j|`) is not covered by the
   max-argument. The census says such orbits carry ≤ 28.3% of mass in the worst cell.
3. **The dimension loss**: even granting saturation, the cap `(2^{t+1}r)^m` exceeds the
   lattice-volume baseline by a factor of order `12^m` (see the R327 section). A route to the
   prize needs a count bound with only `exp(O(r))` loss, which this argument does not give.
4. Converting the relation-count cap into the DC-subtracted moment bound consumed by
   R240/R310. This must be done against the weighted `relationMass`, not the relation count.
   The original note said mass weights "are bounded by count × height² locally". That is
   unproved, and false for the actual ordered-walk carrier without further guards. At
   `n = 8`, `F_17`, `r = 4`, the nonzero kernel vector `(−2,−1,1,0)` has ℓ¹ length 4 and
   ordered depth-8 walk-fiber mass 47880. That exceeds `(2r)² = 64` by far. The relevant
   weighted bound is R322's factorial endpoint envelope
   `NR · s! · ∏|d_j|! ≤ (2r)! · m^s` (`deltastar-466-r322-signed-walk-endpoint-envelope-2026-07-09.md`).
   Unweighted lattice-vector counts are not energy counts. This small-field example does not
   refute the production prize. The Lean collision-mass theorems below avoid the false step:
   they take the per-relation mass bound `M` as an explicit hypothesis.

## R330–R331 (same file, later commits): dictionary + extraction + master pipe

* `mk_relationPoly_negacyclicBinomialMul` (r331) — negacyclic vector product = ring
  multiplication by `a + b·ρ^s` in `ℤ[x]/(x^m+1)` (`ρ^m = −1`, `Equiv.addRight` reindex).
* `binomialVec`, `exists_relationPoly_repr`, `relationPoly_mk_inj`,
  `exists_negacyclic_preimage_of_mem_span` (r330) — span membership in the binomial
  recurrence ideal yields an exact vector-level negacyclic preimage.
* `shadowCollisionMass_le_of_span_saturation` — **the master pipe**: if every realized
  relation scaled by `2^t` lies in the binomial recurrence ideal, then
  `shadowCollisionMass ≤ (2·(2^{t+1}r/(|a|−|b|)).toNat+1)^m · M`.

16 theorems in the file, all `[propext, Classical.choice, Quot.sound]`.

**Remaining glue (blocked only on the r323 olean build queue):** r329's
`card_quotient_dvd_of_patternResultant_dvd` + R321's `eight_saturation_of_card_dvd_eight`
produce the span-membership hypothesis from the pure integer fact `|Res| ∣ 2^t·p` —
after which the ONLY open input of the whole chain is **BinomialBadPrimeLaw** (see the
r329 note). *(Later status, linked 2026-10-28, audit T48: that law is refuted —
`Frontier/_W12BinomialBadPrimeRefuted.lean` proves it unsatisfiable at every prime of the
`n = 32` and `n = 64` census windows, so this chain cannot be fed through it. The kernel-checked
theorems above remain valid as stated; see the status banner at the top for their scope.)*
