/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R32WeightedLagCorrelation

/-!
# LANE B2 (#466 round 33): the four-`J` correlation as a two-line corollary — pair products
  are λ-transforms of convolution weights

Three short steps complete the round-32 program:

* `lamTransform_zero_patch` — the transform is blind to `f(0)` (`λ_i(0) = 0`), so the master
  identity applies to ANY weight (`weighted_lag_correlation'`);
* `pairWeight` + **`jacobi_pair_eq_lamTransform`** — the pair product is itself a transform:
  `J_{j+a}·J_j = c_{W_a}(j)` with `W_a(z) = ∑_{x≠0} χ(1−x)·χ(1−z·x⁻¹)·λ_a(x)`;
* **`quad_correlation_via_weights`** — hence every balanced four-`J` correlation collapses:
  `∑_j J_{j+t₁}·J_{j+t₂}·conj(J_{j+s₁})·conj(J_j)`
  `  = m · ∑_{u∈G} ∑_w W_{t₂−t₁}(u·w)·conj(W_{s₁}(w))·λ_{t₁}(w)`.

The r = 3 matching decomposition's cross terms are now machine-checked exact; what remains of
`TripleConvEnergyBound` is the fully-unmatched sextic class — the named triple-correlation
input, nothing else.  Pure orthogonality throughout.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 33, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R33QuadViaWeights

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The transform is blind to the weight's value at `0`. -/
theorem lamTransform_zero_patch (hfam : SubgroupDualFamily G m lam) (f : F → ℂ) :
    lamTransform lam (fun z => if z = 0 then 0 else f z) = lamTransform lam f := by
  funext i
  unfold lamTransform
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : z = 0
  · subst hz
    rw [hfam.map_zero i]
    simp
  · dsimp only
    rw [if_neg hz]

/-- **The master identity for ARBITRARY weights** (no vanishing hypothesis): `λ_t(0) = 0`
makes the `w = 0` term vanish on both sides. -/
theorem weighted_lag_correlation' (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (f g : F → ℂ) (t : ZMod m) :
    ∑ i : ZMod m, lamTransform lam f (i + t) * (starRingEnd ℂ) (lamTransform lam g i)
      = (m : ℂ) * ∑ u ∈ G, ∑ w : F, f (u * w) * (starRingEnd ℂ) (g w) * lam t w := by
  classical
  set f' : F → ℂ := fun z => if z = 0 then 0 else f z with hf'
  have hf'0 : f' 0 = 0 := by simp [hf']
  have h := weighted_lag_correlation hfam hgrp f' g hf'0 t
  rw [lamTransform_zero_patch hfam f] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w _ => ?_))
  by_cases hw : w = 0
  · subst hw
    rw [hfam.map_zero t]
    ring
  · have hu0 : u ≠ 0 := fun h0 =>
      ArkLib.ProximityGap.Frontier.R24InvolutionNoGo.zero_notMem_of_dualFamily hfam
        (h0 ▸ hu)
    have huw : u * w ≠ 0 := mul_ne_zero hu0 hw
    simp only [hf', if_neg huw]

/-- The pair-product weight `W_a(z) = ∑_{x≠0} χ(1−x)·χ(1−z·x⁻¹)·λ_a(x)`. -/
noncomputable def pairWeight (χ : F → ℂ) (lam : ZMod m → F → ℂ) (a : ZMod m) (z : F) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset F).erase 0, χ (1 - x) * χ (1 - z * x⁻¹) * lam a x

/-- **Pair products are λ-transforms**: `J_{j+a}·J_j = c_{W_a}(j)`. -/
theorem jacobi_pair_eq_lamTransform (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (a j : ZMod m) :
    jacobiCoeff χ lam (j + a) * jacobiCoeff χ lam j
      = lamTransform lam (pairWeight χ lam a) j := by
  classical
  -- RHS: expand, swap, reindex z = x·y per x ≠ 0
  rw [lamTransform]
  have hexp : ∀ z : F, pairWeight χ lam a z * lam j z
      = ∑ x ∈ (Finset.univ : Finset F).erase 0,
          χ (1 - x) * χ (1 - z * x⁻¹) * lam a x * lam j z := by
    intro z
    rw [pairWeight, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun z _ => hexp z), Finset.sum_comm]
  -- per x ≠ 0: Σ_z χ(1−x)χ(1−z x⁻¹)λ_a(x)λ_j(z) = χ(1−x)λ_{j+a}(x)·Σ_y χ(1−y)λ_j(y)
  have hx : ∀ x ∈ (Finset.univ : Finset F).erase 0,
      ∑ z : F, χ (1 - x) * χ (1 - z * x⁻¹) * lam a x * lam j z
        = (χ (1 - x) * lam (j + a) x) * ∑ y : F, χ (1 - y) * lam j y := by
    intro x hx'
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx').1
    -- reindex z = x·y
    have hre : ∑ z : F, χ (1 - x) * χ (1 - z * x⁻¹) * lam a x * lam j z
        = ∑ y : F, χ (1 - x) * χ (1 - (x * y) * x⁻¹) * lam a x * lam j (x * y) := by
      exact (Fintype.sum_bijective (fun y => x * y) (mulLeft_bijective₀ x hx0)
        _ _ (fun y => rfl)).symm
    rw [hre]
    have hpt : ∀ y : F, χ (1 - x) * χ (1 - (x * y) * x⁻¹) * lam a x * lam j (x * y)
        = (χ (1 - x) * lam (j + a) x) * (χ (1 - y) * lam j y) := by
      intro y
      have harg : (x * y) * x⁻¹ = y := by
        field_simp
      rw [harg, hfam.map_mul j x y, hgrp.add_eq_mul j a x]
      ring
    rw [Finset.sum_congr rfl (fun y _ => hpt y), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hx]
  rw [← Finset.sum_mul]
  -- extend the x-sum back over all of F (the x = 0 term vanishes: λ_{j+a}(0) = 0)
  have hext : ∑ x ∈ (Finset.univ : Finset F).erase 0, χ (1 - x) * lam (j + a) x
      = ∑ x : F, χ (1 - x) * lam (j + a) x := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0:F))]
    rw [hfam.map_zero (j + a)]
    ring
  rw [hext]
  rw [jacobiCoeff, jacobiCoeff]
  congr 1 <;> exact Finset.sum_congr rfl (fun z _ => mul_comm _ _)

/-- **THE FOUR-`J` CORRELATION COLLAPSE (round-33 main theorem)** — corollary of the master
identity via pair-product weights.  Every balanced four-`J` correlation of the ladder's
coefficient sequence is `m` times an explicit `G`-fibered sum of pair-weight products.  The
r = 3 cross terms are machine-checked exact; only the fully-unmatched sextic class remains
open. -/
theorem quad_correlation_via_weights (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (t₁ t₂ s₁ : ZMod m) :
    ∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)
      = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          pairWeight χ lam (t₂ - t₁) (u * w)
            * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w := by
  classical
  have hL : ∀ j : ZMod m,
      jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        = lamTransform lam (pairWeight χ lam (t₂ - t₁)) (j + t₁) := by
    intro j
    have h1 : j + t₂ = (j + t₁) + (t₂ - t₁) := by ring
    rw [h1]
    have := jacobi_pair_eq_lamTransform (χ := χ) hfam hgrp (t₂ - t₁) (j + t₁)
    rw [← this]
    ring
  have hR : ∀ j : ZMod m,
      jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j
        = lamTransform lam (pairWeight χ lam s₁) j :=
    fun j => jacobi_pair_eq_lamTransform (χ := χ) hfam hgrp s₁ j
  calc ∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)
      = ∑ j : ZMod m, lamTransform lam (pairWeight χ lam (t₂ - t₁)) (j + t₁)
          * (starRingEnd ℂ) (lamTransform lam (pairWeight χ lam s₁) j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hL j, hR j]
    _ = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          pairWeight χ lam (t₂ - t₁) (u * w)
            * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w :=
        weighted_lag_correlation' hfam hgrp _ _ t₁

/-- **Named surface-correlation input for the pair weights.**  This is the analytic surface
sum exposed by `quad_correlation_via_weights`: uniform cancellation in the `G`-fibered
pair-weight correlation, for every lag triple. -/
def PairWeightCorrelationBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (B : ℝ) : Prop :=
  ∀ t₁ t₂ s₁ : ZMod m,
    ‖∑ u ∈ G, ∑ w : F,
        pairWeight χ lam (t₂ - t₁) (u * w)
          * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖ ≤ B

/-- **Four-`J` bound from the pair-weight surface input.**  The exact weighted collapse
turns the named surface-correlation estimate into a bound for every balanced four-`J`
correlation, losing only the forced quotient-duality factor `m`. -/
theorem quad_correlation_bound_of_pairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : PairWeightCorrelationBound χ lam G B) (t₁ t₂ s₁ : ZMod m) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * B := by
  rw [quad_correlation_via_weights hfam hgrp t₁ t₂ s₁]
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hB t₁ t₂ s₁) (by positivity)

/-- **All-lag four-`J` energy from the pair-weight surface input.**  The pointwise
round-33 bound summed over all lag triples gives the aggregate budget
`m³ · (mB)²`. -/
theorem quad_correlation_energy_bound_of_pairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : PairWeightCorrelationBound χ lam G B) :
    ∑ t₁ : ZMod m, ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
        ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
            * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B) ^ 2) := by
  classical
  have hpoint : ∀ t₁ t₂ s₁ : ZMod m,
      ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
          * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
        ≤ (((m : ℝ) * B) ^ 2) := by
    intro t₁ t₂ s₁
    exact pow_le_pow_left₀ (norm_nonneg _)
      (quad_correlation_bound_of_pairWeightCorrelationBound hfam hgrp hB t₁ t₂ s₁) 2
  calc ∑ t₁ : ZMod m, ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
        ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
            * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ ∑ _t₁ : ZMod m, ∑ _t₂ : ZMod m, ∑ _s₁ : ZMod m, ((m : ℝ) * B) ^ 2 := by
        refine Finset.sum_le_sum (fun t₁ _ => ?_)
        refine Finset.sum_le_sum (fun t₂ _ => ?_)
        exact Finset.sum_le_sum (fun s₁ _ => hpoint t₁ t₂ s₁)
    _ = ((m : ℝ) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B) ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
        ring

end ArkLib.ProximityGap.Frontier.R33QuadViaWeights

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R33QuadViaWeights.weighted_lag_correlation'
#print axioms ArkLib.ProximityGap.Frontier.R33QuadViaWeights.jacobi_pair_eq_lamTransform
#print axioms ArkLib.ProximityGap.Frontier.R33QuadViaWeights.quad_correlation_via_weights
open ArkLib.ProximityGap.Frontier.R33QuadViaWeights in
#print axioms quad_correlation_bound_of_pairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R33QuadViaWeights in
#print axioms quad_correlation_energy_bound_of_pairWeightCorrelationBound
