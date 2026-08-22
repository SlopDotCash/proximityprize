/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80ZArcArithmeticInstantiation

/-!
# LANE G80Y (#466, 2026-07-10): the CONVERSE arc bound — an arc-occupancy uniformity
  certificate BOUNDS the character sum; the rank-one equivalence
  `‖charSum‖ ≈_K arc-discrepancy` is now two-sided and fully machine-checked (axiom-clean).

## Position

G80/G80Z proved the forward direction: character-sum bias `≥ A` forces an arc-occupancy
deviation `≥ (A − #S·2π/K)/K`. This lane proves the CONVERSE — the positive-form consumer
that the doctrine-v2 "single missing non-Fourier certificate" would plug into:

* `charSum_le_of_arc_l1_discrepancy` (abstract): for equally spaced arcs (center sum = 0
  exactly), ANY reference mass `m ≥ 0`:
  `‖∑_x e^{iθ(x)}‖ ≤ (∑_{j<K} |n_j − m|) + #pts·wid` —
  the phase sum is controlled by the ℓ¹ arc-discrepancy plus the oscillation cost.
* `charSum_le_of_arc_uniformity` (ZMod p capstone): if every arc's occupancy is within `ε`
  of `m`, then `‖∑_{y∈S} e(val(y)/p)‖ ≤ K·ε + #S·(2π/K)`.

Together with G80Z's `exists_arc_deviation_of_charSum_bias` this makes the rank-one
equivalence TWO-SIDED, machine-checked, with explicit constants and zero analytic slack:

`(‖charSum‖ − #S·2π/K)/K ≤ max_j |n_j − m|`  and  `‖charSum‖ ≤ K·max_j|n_j − m| + #S·2π/K`.

At `S = b·μ_n` this is: `‖η_b‖ ≍_K` (arc-discrepancy of the dilated subgroup). A NON-FOURIER
proof that every dilation's every arc is `ε`-uniform now yields `M ≤ K·ε + 2πn/K` with no
further analytic work — e.g. `ε = O(√(n log q)/K)` at `K ≍ √(n/log q)` gives the prize bound.

## Honest scope

The consumer interface, not the certificate: producing the non-Fourier `ε`-uniformity input
(BGK/Cilleruelo–Garaev anti-concentration frontier) remains THE open core. No claim of
progress on it here. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse

open ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld
open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation

/-- **Abstract converse bound**: for `K ≥ 2` equally spaced arcs (whose centers sum to zero
exactly), the phase sum is bounded by the ℓ¹ arc-discrepancy against ANY reference mass `m`
plus the oscillation cost `#pts·wid`. -/
theorem charSum_le_of_arc_l1_discrepancy {α : Type*}
    (pts : Finset α) {K : ℕ} (hK : 2 ≤ K) (κ : α → ℕ)
    (hκ : ∀ x ∈ pts, κ x ∈ Finset.range K)
    (θ : α → ℝ) (wid m : ℝ)
    (hosc : ∀ x ∈ pts, |θ x - 2 * Real.pi * (κ x) / K| ≤ wid) :
    ‖∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)‖ ≤
      (∑ j ∈ Finset.range K,
        |((pts.filter (fun x => κ x = j)).card : ℝ) - m|) + (pts.card : ℝ) * wid := by
  set c : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I) with hc
  set model : ℂ := ∑ j ∈ Finset.range K,
    ((pts.filter (fun x => κ x = j)).card : ℂ) * c j with hmodel
  have happrox := grouped_phase_sum_approx pts (Finset.range K) κ hκ θ
    (fun j => 2 * Real.pi * j / K) wid hosc
  -- center sum vanishes exactly
  have hcsum : ∑ j ∈ Finset.range K, c j = 0 := sum_equally_spaced_centers_eq_zero hK
  -- recentre the model by m
  have hrecentre : model = ∑ j ∈ Finset.range K,
      (((((pts.filter (fun x => κ x = j)).card : ℝ) - m : ℝ)) : ℂ) * c j := by
    rw [hmodel]
    have hsplit : ∑ j ∈ Finset.range K,
        (((((pts.filter (fun x => κ x = j)).card : ℝ) - m : ℝ)) : ℂ) * c j
        = (∑ j ∈ Finset.range K,
            ((pts.filter (fun x => κ x = j)).card : ℂ) * c j)
          - ((m : ℝ) : ℂ) * ∑ j ∈ Finset.range K, c j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hsplit, hcsum, mul_zero, sub_zero]
  -- bound the recentred model by the ℓ¹ discrepancy
  have hmodel_le : ‖model‖ ≤ ∑ j ∈ Finset.range K,
      |((pts.filter (fun x => κ x = j)).card : ℝ) - m| := by
    rw [hrecentre]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hc,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- triangle
  calc ‖∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)‖
      ≤ ‖(∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)) - model‖ + ‖model‖ := by
        have h := norm_add_le
          ((∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)) - model) model
        simpa [sub_add_cancel] using h
    _ ≤ (pts.card : ℝ) * wid + ∑ j ∈ Finset.range K,
          |((pts.filter (fun x => κ x = j)).card : ℝ) - m| := by
        exact add_le_add happrox hmodel_le
    _ = _ := by ring

/-- **ZMod p capstone — the positive-form consumer.** If every arc's occupancy is within `ε`
of the reference mass `m`, the standard character sum over `S ⊆ ZMod p` is at most
`K·ε + #S·(2π/K)`. A non-Fourier `ε`-uniformity certificate for the dilated subgroup plugs
in here to bound `‖η_b‖` directly. -/
theorem charSum_le_of_arc_uniformity {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    {K : ℕ} (hK : 2 ≤ K) (ε m : ℝ)
    (hunif : ∀ j ∈ Finset.range K,
      |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m| ≤ ε) :
    ‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖ ≤
      (K : ℝ) * ε + (S.card : ℝ) * (2 * Real.pi / K) := by
  have hK0 : 0 < K := by omega
  have h := charSum_le_of_arc_l1_discrepancy S hK (arcIndex K)
    (fun y _ => arcIndex_mem_range K hK0 y) charPhase (2 * Real.pi / K) m
    (fun y _ => arcIndex_width K hK0 y)
  have hsum : ∑ j ∈ Finset.range K,
      |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m| ≤ (K : ℝ) * ε := by
    calc ∑ j ∈ Finset.range K,
        |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m|
        ≤ ∑ _j ∈ Finset.range K, ε := Finset.sum_le_sum hunif
      _ = (K : ℝ) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

end ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse.charSum_le_of_arc_l1_discrepancy
#print axioms
  ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse.charSum_le_of_arc_uniformity
