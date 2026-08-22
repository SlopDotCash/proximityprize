/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.I031SubGaussianMaxBridge

/-!
# I031: the union-bound hypothesis is EQUIVALENT to the pointwise period bound (#444, #407)

The I031 capstone (`I031LogTargetForm.i031_M_le_logTarget`) lands the prize-target sup-norm bound
`M(μ_n) ≤ √(2·(C₀·n)·log(q/n))` *conditional* on the single named-open analytic input
`SubGaussianTailBound (periodMagnitudes ψ G) (C₀·n) m` (`I031SubGaussianMaxBridge`). Separately,
the #407 file `ConstantIndexSubGaussianPeriod` isolates the SAME wall as a **pointwise** per-period
Prop `ConstantIndexSubGaussianPeriodBound : ∀ b ≠ 0, ‖η_b‖ ≤ √(2·n·log m)`. Until now these two
"named open" objects were **never connected** — a `SubGaussianTailBound` was *consumed* by I031 but
*never constructed* anywhere in the tree, and the #407 pointwise conjecture never reached the I031
consumer.

This file closes that gap with an **exact equivalence**, after a careful probe correction.

## The probe-corrected relationship (rule 2, rule 4)

`probe_subgaussian_tail_from_pointwise.py` (EXACT `F_p`, PROPER thin `μ_n`, `n=2^a`, `p ≡ 1 (n)`,
`(p−1)/n ≥ 2`, NEVER `n=q−1`, primes incl. `p > n³` and Fermat 257) shows the **full** tail Prop
`∀ s > 0, #{v > s} ≤ m·exp(−s²/2C)` (with proxy `C = n`) is *strictly stronger* than the pointwise
bound: it is **VIOLATED at small `s`** (e.g. `p=97, n=8`: `#{v>s} − m·exp(−s²/2n) = 0.45` at
`s≈0.78`), because near `s=0` almost all `m` distinct magnitudes exceed `s` while `m·exp(−s²/2n)<m`.

BUT `probe_tail_above_threshold.py` (same EXACT setup, extended to `p=40961`) shows the tail Prop
**restricted to `s ≥ s* := √(2C·log m)`** is TRUE in `13/13` configs, and is *equivalent* to the
pointwise bound `M ≤ s*`. The key structural fact that makes this matter: the consumer
`subgaussian_max_le` only ever invokes its tail hypothesis at thresholds `s ∈ (s*, v)`, i.e. at
`s > s*`. So the I031 union bound never *needs* the gratuitously-strong full-`s` Prop — it needs
only the `s ≥ s*` restriction, which is exactly the #407 pointwise bound.

## What this file proves (axiom-clean; CORE stays OPEN)

* `SubGaussianTailBoundAbove S C m`: the tail-count Prop restricted to `s ≥ s*` (the genuinely
  needed hypothesis).
* `subGaussianTailBoundAbove_iff_forall_le`: it is **logically equivalent** to the pointwise max
  bound `∀ v ∈ S, v ≤ s*` (the headline — the two named-open objects are ONE).
* `subgaussian_max_le_above`: the weakened Prop still drives the I031 max bound (the consumer only
  needed `s ≥ s*`).
* `pointwise_le_of_subGaussianTailBound`: the FULL tail Prop implies the pointwise bound (so the
  full Prop ⟹ the above-threshold Prop, consistent with "strictly stronger").

This **wires the #407 pointwise conjecture to the I031 capstone** for the first time: the I031
hypothesis can be replaced by the genuinely-equivalent pointwise period bound. It does NOT close
CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) — the pointwise bound is itself the BGK/Lamzouri wall. It removes
a *spurious over-strength* in the I031 interface and exhibits the exact equivalence the dossier
asserts informally.

NON-MOMENT (pure threshold/extreme-value real analysis on a finset of magnitudes), EXTEND-proven
(sits directly on `I031SubGaussianMaxBridge.subgaussian_max_le` + its `s*` scale). ONE sweep, ONE
commit. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.I031TailFromPointwise

open ArkLib.ProximityGap.I031SubGaussianMaxBridge

/-- **The above-threshold sub-Gaussian tail bound** — the tail-count Prop restricted to the
thresholds the union bound actually uses, `s ≥ s* := √(2·C·log m)`. Probe-shown (rule 2) to be the
genuinely-needed hypothesis: the full-`s` `SubGaussianTailBound` is strictly stronger (violated at
small `s`), but `subgaussian_max_le` only invokes the tail at `s > s*`. -/
def SubGaussianTailBoundAbove (S : Finset ℝ) (C m : ℝ) : Prop :=
  ∀ s : ℝ, Real.sqrt (2 * C * Real.log m) ≤ s →
    ((S.filter (fun v => s < v)).card : ℝ) ≤ m * Real.exp (-(s ^ 2) / (2 * C))

/-- **The headline equivalence.** For `0 < C`, `1 ≤ m`, the above-threshold tail Prop is logically
equivalent to the *pointwise* max bound `∀ v ∈ S, v ≤ √(2·C·log m)`. So the I031 named-open
`SubGaussianTailBoundAbove` and the #407 pointwise period conjecture are literally the SAME object.

*Proof.* (⟸) If every `v ≤ s*` then for any `s ≥ s*` the filter `{v ∈ S : s < v}` is EMPTY (no `v`
exceeds `s ≥ s* ≥ v`), so its card is `0 ≤ m·exp(…)` (the RHS is `≥ 0`). (⟹) Given the tail at the
single threshold `s = s*`: `#{v > s*} ≤ m·exp(−(s*)²/2C) = m·exp(−log m) = 1`. We show
`#{v > s*}` is in fact `0`: if some `v > s*` then `#{v > s*} ≥ 1`; but pushing to a
strictly larger `s ∈ (s*, v)` makes the RHS `< 1` while `v` is still counted —
contradiction (this is exactly the `subgaussian_max_le` mechanism). Hence no `v` exceeds `s*`. -/
theorem subGaussianTailBoundAbove_iff_forall_le
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m) :
    SubGaussianTailBoundAbove S C m ↔
      ∀ v ∈ S, v ≤ Real.sqrt (2 * C * Real.log m) := by
  set sstar := Real.sqrt (2 * C * Real.log m) with hsstar
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hrad : 0 ≤ 2 * C * Real.log m := by positivity
  have hsstar_nonneg : 0 ≤ sstar := Real.sqrt_nonneg _
  have hm_pos : 0 < m := lt_of_lt_of_le one_pos hm
  have h2C : 0 < 2 * C := by linarith
  constructor
  · -- (⟹) the tail at s = s* forces the filter at s* to be empty
    intro htail v hv
    by_contra hlt
    rw [not_le] at hlt
    -- pick s strictly between s* and v; tail at this s (≥ s*) is < 1 but v is counted
    set s := (sstar + v) / 2 with hs
    have hs_lo : sstar < s := by rw [hs]; linarith
    have hs_hi : s < v := by rw [hs]; linarith
    have hs_ge : sstar ≤ s := le_of_lt hs_lo
    have hs_pos : 0 < s := lt_of_le_of_lt hsstar_nonneg hs_lo
    have hsstar_sq : sstar ^ 2 = 2 * C * Real.log m := by
      rw [hsstar, Real.sq_sqrt hrad]
    have hs_sq_gt : 2 * C * Real.log m < s ^ 2 := by
      rw [← hsstar_sq]
      nlinarith [hsstar_nonneg, hs_lo, sq_nonneg (s - sstar)]
    have hexp_arg : -(s ^ 2) / (2 * C) < -Real.log m := by
      rw [div_lt_iff₀ h2C]; nlinarith [hs_sq_gt, h2C]
    have hexp_lt : Real.exp (-(s ^ 2) / (2 * C)) < Real.exp (-Real.log m) :=
      Real.exp_lt_exp.mpr hexp_arg
    have hexp_neglog : Real.exp (-Real.log m) = m⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hm_pos]
    have hbound : m * Real.exp (-(s ^ 2) / (2 * C)) < 1 := by
      have hh : m * Real.exp (-(s ^ 2) / (2 * C)) < m * Real.exp (-Real.log m) :=
        mul_lt_mul_of_pos_left hexp_lt hm_pos
      rw [hexp_neglog, mul_inv_cancel₀ (ne_of_gt hm_pos)] at hh
      exact hh
    have htail_s := htail s hs_ge
    have hcard_lt : ((S.filter (fun w => s < w)).card : ℝ) < 1 :=
      lt_of_le_of_lt htail_s hbound
    have hv_mem : v ∈ S.filter (fun w => s < w) := by
      rw [Finset.mem_filter]; exact ⟨hv, hs_hi⟩
    have hcard_pos : 1 ≤ (S.filter (fun w => s < w)).card :=
      Finset.card_pos.mpr ⟨v, hv_mem⟩
    have hc1 : (1 : ℝ) ≤ ((S.filter (fun w => s < w)).card : ℝ) := by exact_mod_cast hcard_pos
    linarith
  · -- (⟸) pointwise bound ⟹ empty filter above s* ⟹ tail trivially holds
    intro hpt s hs_ge
    have hempty : S.filter (fun v => s < v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv
      rw [not_lt]
      exact le_trans (hpt v hv) hs_ge
    rw [hempty, Finset.card_empty]
    have hrhs_nonneg : (0 : ℝ) ≤ m * Real.exp (-(s ^ 2) / (2 * C)) := by positivity
    simpa using hrhs_nonneg

/-- **The weakened tail Prop still drives the I031 max bound.** From `SubGaussianTailBoundAbove`
(the genuinely-needed `s ≥ s*` restriction), every `v ∈ S` satisfies `v ≤ √(2·C·log m)` — the same
conclusion as `subgaussian_max_le`, now from the equivalent (not gratuitously-strong) hypothesis. -/
theorem subgaussian_max_le_above
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m)
    (h : SubGaussianTailBoundAbove S C m) :
    ∀ v ∈ S, v ≤ Real.sqrt (2 * C * Real.log m) :=
  (subGaussianTailBoundAbove_iff_forall_le hC hm).mp h

/-- **Exact failure certificate for the genuinely-needed above-threshold tail.** Under the same
positivity hypotheses as the I031 bridge, `SubGaussianTailBoundAbove` fails if and only if one
member of `S` exceeds the union-bound threshold `√(2·C·log m)`.

So any distributional / EVT route that cannot rule out a single oversized period has not reached
the corrected I031 interface. -/
theorem not_SubGaussianTailBoundAbove_iff_exists_gt
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m) :
    (¬ SubGaussianTailBoundAbove S C m) ↔
      ∃ v ∈ S, Real.sqrt (2 * C * Real.log m) < v := by
  constructor
  · intro hfail
    by_contra hnone
    apply hfail
    exact (subGaussianTailBoundAbove_iff_forall_le hC hm).mpr
      (by
        intro v hv
        exact le_of_not_gt (fun hgt => hnone ⟨v, hv, hgt⟩))
  · rintro ⟨v, hv, hgt⟩ htail
    exact not_lt_of_ge ((subGaussianTailBoundAbove_iff_forall_le hC hm).mp htail v hv) hgt

/-- **The full tail Prop implies the above-threshold one** (it is strictly stronger; the small-`s`
content is the redundant part the I031 consumer never uses). Needs `1 < m` so that
`s* = √(2C·log m) > 0`, hence the inherited threshold `s ≥ s*` gives `0 < s` for the full Prop. -/
theorem subGaussianTailBoundAbove_of_subGaussianTailBound
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 < m) (h : SubGaussianTailBound S C m) :
    SubGaussianTailBoundAbove S C m := by
  intro s hs_ge
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have hrad : 0 < 2 * C * Real.log m := by positivity
  have hsstar_pos : 0 < Real.sqrt (2 * C * Real.log m) := Real.sqrt_pos.mpr hrad
  exact h s (lt_of_lt_of_le hsstar_pos hs_ge)

/-- **The full tail Prop implies the pointwise bound.** Closes the loop: `SubGaussianTailBound`
(I031's literal hypothesis) ⟹ pointwise `M ≤ √(2·C·log m)` ⟹ `SubGaussianTailBoundAbove`. So all
three are linked, with the full Prop on top and the pointwise/above-threshold pair equivalent
beneath it. -/
theorem pointwise_le_of_subGaussianTailBound
    {S : Finset ℝ} {C m : ℝ} (hC : 0 < C) (hm : 1 ≤ m)
    (h : SubGaussianTailBound S C m) :
    ∀ v ∈ S, v ≤ Real.sqrt (2 * C * Real.log m) :=
  subgaussian_max_le hC hm h

end ArkLib.ProximityGap.I031TailFromPointwise

/-! ## Axiom audit -/
open ArkLib.ProximityGap.I031TailFromPointwise in
#print axioms subGaussianTailBoundAbove_iff_forall_le
open ArkLib.ProximityGap.I031TailFromPointwise in
#print axioms subgaussian_max_le_above
open ArkLib.ProximityGap.I031TailFromPointwise in
#print axioms not_SubGaussianTailBoundAbove_iff_exists_gt
open ArkLib.ProximityGap.I031TailFromPointwise in
#print axioms subGaussianTailBoundAbove_of_subGaussianTailBound
open ArkLib.ProximityGap.I031TailFromPointwise in
#print axioms pointwise_le_of_subGaussianTailBound
