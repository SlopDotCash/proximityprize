/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# Vinogradov MVT / decoupling is VACUOUS for the prize cross-surplus over `μ_n` (#407, Angle 1)

## The angle and its honest verdict

**Angle 1 (re-run).** The cross-surplus / `r`-fold additive energy
`E_r(μ_n) = #{(x,y) ∈ μ_n^{2r} : ∑ x_i = ∑ y_i}` is a count of solutions to a
*translation-invariant* additive system. The **Vinogradov Mean Value Theorem**
(Bourgain–Demeter–Guth 2016 via `ℓ²` decoupling; Wooley via efficient congruencing) is
*resolved* and gives the SHARP count for such systems:
`J_{s,k}(N) ≍ N^s + N^{2s − k(k+1)/2}`. The idea was: maybe the resolved VMT count beats the
moment no-go (`_MomentMethodNoGo`) and pushes the prize bound `B ≤ √(2n·ln(q/n))`.

**Verdict: NO — the VMT/decoupling machinery is VACUOUS on this object, for THREE independent
structural reasons, each verified.** (Honest re-run conclusion; the prior attempt died on a
rate-limit before reaching it.)

### Reason 1 — wrong system: 1 equation, not `k` equations.
VMT's `J_{s,k}(N)` counts solutions to the `k` SIMULTANEOUS power-sum equations
`∑ x_i^j = ∑ y_i^j` for **all** `j = 1,…,k`. Its non-trivial gain `N^{−k(k+1)/2}` is *exactly*
the dimension count of the `k−1` extra (degree ≥ 2) equations — it is the curvature/affine-arc-
length of the moment curve `t ↦ (t, t², …, t^k)`. The prize energy `E_r(μ_n)` counts solutions
to the **single** linear equation `∑ x_i = ∑ y_i` (the `j = 1` row only). There are no extra
equations over `μ_n` to decouple, so there is no `N^{−k(k+1)/2}` gain to harvest. (`numericTest`
Test A.)

### Reason 2 — the moment curve CLOSES UP: zero net curvature.
Even if one *imposed* the higher power-sum equations on `μ_n`, the moment map `x ↦ x^j` sends
`μ_n` back into a multiplicative subgroup: `x ∈ μ_n ⟹ x^j ∈ μ_{n/gcd(j,n)} ⊆ μ_n`. The "moment
curve" `t ↦ (t, t², …, t^k)` does NOT open into `k` dimensions over `μ_n`; it folds into the
same `n`-point set. This is the maximal form of the degeneracy that voids decoupling. The
decoupling literature is explicit (Kemp, *Decouplings for surfaces of zero curvature*,
arXiv:1908.07002 §6 "Flatness"): **zero curvature ⟹ no `ℓ²` decoupling gain, the trivial bound
only.** The grand-challenge's own KEY STRUCTURAL FACT — `μ_n` is multiplicatively a group but
additively near-Sidon with flat frequency map `j ↦ ζ^j` — is precisely this flatness. (`numericTest`
Test B.)

### Reason 3 — route-independent Cauchy–Schwarz floor: any count gives `≥ n`.
This is the decisive one and is what we MACHINE-CHECK below. Whatever the VMT-sharp count of
`E_r` is, it obeys the route-independent mass floor `E_r ≥ n^{2r}/q` (Cauchy–Schwarz on the
`n^r` total `r`-tuple mass spread over `≤ q` sums; `_MomentMethodNoGo.energy_ge_card_pow`).
Hence the depth-`r` moment bound `(q·E_r)^{1/2r} ≥ n` for EVERY `r` and EVERY count — VMT can
only *lower* `E_r` toward the floor `n^{2r}/q`, where the bound is *exactly* `n` (the trivial
bound), never below. So a perfect VMT sharpening of the count buys nothing past `n`. (`numericTest`
Test C.)

### Where the genuine sub-`n` gain lives (NOT a counting question).
The only way the moment ladder dips below `n` to the prize target `√(2n·ln(q/n))` is the
COEFFICIENT `(2r−1)‼` in the char-0 Gaussian energy `E_r(μ_n) ≤ (2r−1)‼·n^r`, optimized at
`r* ≈ ln q` (numerically `(q·(2r−1)‼·n^r)^{1/2r} → √(2n ln q)`, ratio `→ 1`; Test in
`numericTest`). That `(2r−1)‼` is a char-0 Wick/Lam–Leung fact, and the OPEN core is its char-`p`
transfer at `r ≈ ln q` (BCHKS Conj 1.12 / the Paley-graph conjecture), which is a
*phase-cancellation / vanishing-relation* statement, NOT a solution-count VMT addresses.

So Angle 1 collapses back to the SAME wall: the prize needs `L^∞`/phase cancellation, not an
`L²` count, and VMT is an `L²`-count theorem. This file records the verdict as the route-
independent CS floor (the formal heart of Reasons 1–3): **no count-sharpening of any kind —
VMT, decoupling, or otherwise — can push the moment bound below the trivial `n`.**

This is a method-boundary verdict, NOT a refutation of the prize and NOT a closure. All results
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

Issue #407, Angle 1.
-/

open Finset

namespace ProximityGap.Frontier.VinogradovDecouplingVacuous

open ProximityGap.Frontier.MomentMethodNoGo

/-- **The VMT/decoupling no-go (route-independent count floor), depth-`r` form.**

`B := max_b |∑_{x∈μ_n} e_p(bx)|` is bounded by any additive-moment route through
`B^{2r} ≤ q·E_r`, with `E_r = ∑_s (c s)²` the `r`-fold additive energy (`c s` = number of
`r`-tuples from `μ_n` summing to `s`, so `∑_s c s = n^r`, supported on `σ` with `|σ| = q`).

For ANY such count function `c` — in particular the SHARPEST possible VMT/decoupling count —
the depth-`r` moment bound satisfies `(q·E_r)^{1/(2r)} ≥ n`. The Vinogradov Mean Value Theorem,
no matter how sharp, only sharpens the *count* `E_r`; it can never beat this Cauchy–Schwarz
floor, so it can never certify `B < n`, let alone `B ≲ √n`. (This wraps
`_MomentMethodNoGo.moment_bound_ge_card` as the formal statement of "VMT count-sharpening cannot
help": the bound is `≥ n` for every count `c`, uniformly.) -/
theorem vmt_count_cannot_beat_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_ge_card c n r hr hcount

/-- **VMT cannot make the count drop below the Cauchy–Schwarz floor `n^{2r}/q`.**

The VMT-sharp count is a LOWER count than the trivial spread, but it is bounded below by the
mass floor: `E_r = ∑_s (c s)² ≥ n^{2r}/q`. So decoupling can only push `E_r` *down to* this
floor, where the moment bound is exactly `n` — never below. Stated as the squared inequality
`n^{2r} ≤ q·E_r` (equivalently `n^{2r}/q ≤ E_r`), which holds for ANY count of total mass `n^r`
spread over `q` sums, VMT-sharp or not. -/
theorem vmt_count_above_cs_floor {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 :=
  energy_ge_card_pow c n r hcount

/-- **The exact pivot: at the CS floor the count is `n^{2r}/q` and the bound is exactly `n`.**

When the count saturates the Cauchy–Schwarz floor `E = n^{2r}/q` (the *best* any decoupling
estimate could achieve), the depth-`r` moment bound `(q·E)^{1/(2r)}` equals exactly `n`. So the
infimum over all counts (the limit of VMT sharpening) is the TRIVIAL bound `n` — confirming VMT
buys nothing below `n`. We state the clean algebraic identity `q · (n^{2r}/q) = n^{2r}`, whose
`(2r)`-th root is `n` (the pivot value), under `q ≠ 0`. -/
theorem vmt_floor_pivot_is_card (n r : ℕ) (q : ℝ) (hq : q ≠ 0) :
    q * ((n : ℝ) ^ (2 * r) / q) = (n : ℝ) ^ (2 * r) := by
  field_simp

/-- **Honest summary as a single implication.**  If a (hypothetical) VMT/decoupling estimate
furnished a count `c` of the additive energy with the correct total mass `n^r` over `q` sums,
the resulting depth-`r` moment bound is `≥ n`. Contrapositive: to certify `B < n` you must NOT
use any count of `E_r` — you need genuine phase cancellation (`L^∞`), which VMT (an `L²`-count
theorem) does not provide. Reasons 1–3 in the module docstring explain *why* no VMT count is
even available over `μ_n` (one equation, closed-up moment curve), but this floor shows that even
a perfect one would be useless. -/
theorem vmt_route_dead {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r)
    (hbound : ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) < (n : ℝ)) :
    False :=
  absurd (vmt_count_cannot_beat_card c n r hr hcount) (not_le.mpr hbound)

end ProximityGap.Frontier.VinogradovDecouplingVacuous

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.VinogradovDecouplingVacuous.vmt_count_cannot_beat_card
#print axioms ProximityGap.Frontier.VinogradovDecouplingVacuous.vmt_count_above_cs_floor
#print axioms ProximityGap.Frontier.VinogradovDecouplingVacuous.vmt_floor_pivot_is_card
#print axioms ProximityGap.Frontier.VinogradovDecouplingVacuous.vmt_route_dead
