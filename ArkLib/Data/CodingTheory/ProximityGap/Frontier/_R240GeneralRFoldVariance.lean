/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.ToMathlib.FinsetChebyshev

/-!
# R240 (#466): general `r`-fold representation variance identity

Rounds 55--57 recast the depth-3 DC-subtracted energy as the flatness
variance of the three-fold representation function.  This file lifts the
pure Finset algebra to arbitrary depth `r`.

For

```text
repR G r c = #{v : G^r | Σ_i v_i = c},
```

we prove

```text
Σ_c (q * repR G r c - |G|^r)^2
  = q * (q * rEnergy G r - |G|^(2r)).
```

This is not a new analytic estimate.  It is the exact flatness interface for
the deep-r wall: proving DC-subtracted Wick at logarithmic depth is equivalent
to proving that the `r`-fold additive convolution of `1_G` is flat at Wick
scale.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.GaussPeriodOptimizedBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `r`-fold additive representation function of `G`. -/
noncomputable def repR (G : Finset F) (r : ℕ) (c : F) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
    if ∑ i, v i = c then 1 else 0

/-- Weighted regrouping by the `r`-fold sum. -/
theorem sum_vectors_weight (G : Finset F) (r : ℕ) (g : F → ℕ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), g (∑ i, v i)
      = ∑ c : F, repR G r c * g c := by
  classical
  have hc : ∀ c : F, repR G r c * g c
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          if ∑ i, v i = c then g c else 0 := by
    intro c
    unfold repR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun c _ => hc c)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (∑ i, v i) g]
  simp

/-- Total mass of the `r`-fold representation function. -/
theorem sum_repR (G : Finset F) (r : ℕ) :
    ∑ c : F, repR G r c = G.card ^ r := by
  have h := sum_vectors_weight G r (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  rw [Finset.sum_const, Fintype.card_piFinset_const, nsmul_eq_mul]
  simp

/-- `rEnergy` is the `L^2` norm of the `r`-fold representation function. -/
theorem rEnergy_eq_sum_repR_sq (G : Finset F) (r : ℕ) :
    rEnergy G r = ∑ c : F, (repR G r c) ^ 2 := by
  classical
  have hfold :
      rEnergy G r =
        ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), repR G r (∑ i, v i) := by
    unfold rEnergy repR
    refine Finset.sum_congr rfl (fun v _ => ?_)
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : ∑ i, v i = ∑ i, w i <;> simp [h, eq_comm]
  rw [hfold, sum_vectors_weight G r (repR G r)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [sq]

/-- The general flatness variance identity for the `r`-fold representation
function. -/
theorem variance_identity (G : Finset F) (r : ℕ) :
    ∑ c : F, ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2
      = (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) := by
  have hsum : ∑ c : F, (repR G r c : ℝ) = (G.card : ℝ) ^ r := by
    have := sum_repR G r
    calc ∑ c : F, (repR G r c : ℝ) = ((∑ c : F, repR G r c : ℕ) : ℝ) := by
          push_cast
          rfl
      _ = ((G.card ^ r : ℕ) : ℝ) := by rw [this]
      _ = (G.card : ℝ) ^ r := by exact_mod_cast Nat.cast_pow G.card r
  have hsq : ∑ c : F, (repR G r c : ℝ) ^ 2 = (rEnergy G r : ℝ) := by
    have := rEnergy_eq_sum_repR_sq G r
    calc ∑ c : F, (repR G r c : ℝ) ^ 2
        = ((∑ c : F, (repR G r c) ^ 2 : ℕ) : ℝ) := by
          push_cast
          rfl
      _ = ((rEnergy G r : ℕ) : ℝ) := by rw [← this]
  have hcard : ∑ _c : F, (1 : ℝ) = (Fintype.card F : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hexp : ∀ c : F,
      ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2
        = (Fintype.card F : ℝ) ^ 2 * (repR G r c : ℝ) ^ 2
          - 2 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ r * (repR G r c : ℝ)
          + (G.card : ℝ) ^ (2 * r) * 1 := by
    intro c
    rw [show (G.card : ℝ) ^ (2 * r) = ((G.card : ℝ) ^ r) ^ 2 by
      rw [Nat.mul_comm 2 r]
      rw [← pow_mul]]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hexp c)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsq, hsum, hcard]
  ring

/-- General DC floor: `|G|^(2r) ≤ q * rEnergy G r`. -/
theorem dc_floor (G : Finset F) (r : ℕ) :
    (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := by
  have hvar : (0 : ℝ) ≤ (Fintype.card F : ℝ)
      * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) := by
    rw [← variance_identity G r]
    exact Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith [hvar, hq]

/-- The arbitrary-depth variance form of the corrected DC-subtracted Wick
target. -/
theorem dcEnergyBound_iff_variance (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ c : F, ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  unfold DCEnergyBound
  rw [variance_identity G r]
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    calc (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
        ≤ (Fintype.card F : ℝ)
            * ((Fintype.card F : ℝ)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
          mul_le_mul_of_nonneg_left h (le_of_lt hq)
      _ = (Fintype.card F : ℝ) ^ 2
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by ring
  · intro h
    have h' : (Fintype.card F : ℝ)
        * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
        ≤ (Fintype.card F : ℝ)
            * ((Fintype.card F : ℝ)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
      rw [show (Fintype.card F : ℝ)
            * ((Fintype.card F : ℝ)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
          = (Fintype.card F : ℝ) ^ 2
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) from by ring]
      exact h
    exact le_of_mul_le_mul_left h' hq

/-- `DCEnergyBound` is exactly the original DC-gap Wick inequality.  This
names the unfolded form so external analytic estimates can target it directly. -/
theorem dcEnergyBound_iff_dcGap_bound (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
          ≤ (Fintype.card F : ℝ)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  rfl

/-- A budgeted DC-gap consumer: if an analytic estimate bounds the original
DC-subtracted energy gap by `B`, and `B` fits the Wick budget, then
`DCEnergyBound` follows. -/
theorem dcEnergyBound_of_dcGap_bound (G : Finset F) (r : ℕ) {B : ℝ}
    (hgap :
      (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) ≤ B)
    (hbudget :
      B ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_dcGap_bound G r).mpr (hgap.trans hbudget)

/-- `DCEnergyBound` gives the original DC-gap Wick inequality. -/
theorem dcGap_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  (dcEnergyBound_iff_dcGap_bound G r).mp hdc

/-- If the original DC-subtracted energy gap exceeds the Wick budget, then
`DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_dcGap_gt (G : Finset F) (r : ℕ)
    (hbudget :
      (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := dcGap_bound_of_dcEnergyBound G r hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate form for the original DC gap. -/
theorem not_dcEnergyBound_of_dcGap_lower_bound_gt (G : Finset F) (r : ℕ) {B : ℝ}
    (hlower :
      B ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
    (hbudget :
      (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyBound G r :=
  not_dcEnergyBound_of_dcGap_gt G r (hbudget.trans_le hlower)

/-- Constant-`K` version of the DC-subtracted Wick target:
`q * rEnergy - |G|^(2r) <= q * K^r * (2r-1)!! * |G|^r`.

The fixed `DCEnergyBound` used by the prize moment machinery is the `K = 1`
case.  The dossier's asymptotic wall is often stated in this constant-power
form. -/
def DCEnergyBoundWithConstant (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ)
        * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))

/-- All-rung constant-`K` version of the DC-subtracted Wick wall. -/
def DCEnergyWallWithConstant (G : Finset F) (K : ℝ) : Prop :=
  ∀ r : ℕ, DCEnergyBoundWithConstant G r K

/-- Finite-depth constant-`K` version of the DC-subtracted Wick wall.  This is
the operational form needed for the optimized sup-norm endpoint: only the
ceiling depth `⌈log q⌉` is consumed. -/
def DCEnergyWallWithConstantUpTo (G : Finset F) (K : ℝ) (R : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ R → DCEnergyBoundWithConstant G r K

/-- One-rung constant-`K` wall at the moment-optimal ceiling depth.  This is
the smallest DC-energy hypothesis consumed by the optimized sup-norm endpoint. -/
def DCEnergyCeilWallWithConstant (G : Finset F) (K : ℝ) : Prop :=
  DCEnergyBoundWithConstant G ⌈Real.log (Fintype.card F : ℝ)⌉₊ K

/-- The constant-`K` socket specializes to `DCEnergyBound` at `K = 1`. -/
theorem dcEnergyBoundWithConstant_one_iff (G : Finset F) (r : ℕ) :
    DCEnergyBoundWithConstant G r 1 ↔ DCEnergyBound G r := by
  unfold DCEnergyBoundWithConstant DCEnergyBound
  simp

/-- Fixed `DCEnergyBound` gives its constant-`1` version. -/
theorem dcEnergyBoundWithConstant_one_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    DCEnergyBoundWithConstant G r 1 :=
  (dcEnergyBoundWithConstant_one_iff G r).mpr hdc

/-- Constant-`1` DC-energy gives the fixed `DCEnergyBound`. -/
theorem dcEnergyBound_of_dcEnergyBoundWithConstant_one (G : Finset F) (r : ℕ)
    (h : DCEnergyBoundWithConstant G r 1) :
    DCEnergyBound G r :=
  (dcEnergyBoundWithConstant_one_iff G r).mp h

/-- Constant-`K` DC energy is exactly the constant-`K` Wick bound for the
nonzero Gauss-period moment.  This is the direct bridge from the R240
representation-variance socket to the prize-facing `η_b` moment wall. -/
theorem dcEnergyBoundWithConstant_iff_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) (K : ℝ) :
    DCEnergyBoundWithConstant G r K
      ↔ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
          ≤ (Fintype.card F : ℝ)
              * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  unfold DCEnergyBoundWithConstant
  rw [← ArkLib.ProximityGap.DCSubtractedMoment.sum_nonzero_moment hψ G r]

/-- The fixed `DCEnergyBound` is the `K = 1` nonzero Gauss-period moment
bound. -/
theorem dcEnergyBound_iff_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
          ≤ (Fintype.card F : ℝ)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  rw [← dcEnergyBoundWithConstant_one_iff G r]
  simpa using dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r (1 : ℝ)

/-- The all-rung constant-`K` wall is exactly the all-rung nonzero
Gauss-period moment bound. -/
theorem dcEnergyWallWithConstant_iff_forall_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) :
    DCEnergyWallWithConstant G K
      ↔ ∀ r : ℕ,
          ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
            ≤ (Fintype.card F : ℝ)
                * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  constructor
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r K).mp (h r)
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r K).mpr (h r)

/-- The finite-depth constant-`K` wall is exactly the finite-depth nonzero
Gauss-period moment bound. -/
theorem dcEnergyWallWithConstantUpTo_iff_forall_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) (R : ℕ) :
    DCEnergyWallWithConstantUpTo G K R
      ↔ ∀ r : ℕ, r ≤ R →
          ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
            ≤ (Fintype.card F : ℝ)
                * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  constructor
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r K).mp (h r hr)
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r K).mpr (h r hr)

/-- The one-rung ceiling wall is exactly the nonzero Gauss-period moment bound
at the ceiling depth. -/
theorem dcEnergyCeilWallWithConstant_iff_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) :
    DCEnergyCeilWallWithConstant G K
      ↔ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F),
          ‖eta ψ G b‖ ^ (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊)
          ≤ (Fintype.card F : ℝ)
              * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
                * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
                  * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) := by
  unfold DCEnergyCeilWallWithConstant
  exact dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G
    ⌈Real.log (Fintype.card F : ℝ)⌉₊ K

/-- A nonzero Gauss-period moment estimate at the ceiling depth proves the
one-rung ceiling wall. -/
theorem dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ)
    (hmoment :
      ∑ b ∈ (Finset.univ : Finset F).erase (0 : F),
          ‖eta ψ G b‖ ^ (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊)
        ≤ (Fintype.card F : ℝ)
            * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
                * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))) :
    DCEnergyCeilWallWithConstant G K :=
  (dcEnergyCeilWallWithConstant_iff_sum_nonzero_moment hψ G K).mpr hmoment

/-- The original all-rung DC wall is the all-rung `K = 1` nonzero
Gauss-period moment bound. -/
theorem dcEnergyWall_iff_forall_sum_nonzero_moment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (∀ r : ℕ, DCEnergyBound G r)
      ↔ ∀ r : ℕ,
          ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
            ≤ (Fintype.card F : ℝ)
                * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  constructor
  · intro h r
    exact (dcEnergyBound_iff_sum_nonzero_moment hψ G r).mp (h r)
  · intro h r
    exact (dcEnergyBound_iff_sum_nonzero_moment hψ G r).mpr (h r)

/-- A single over-budget nonzero moment refutes the all-rung constant wall. -/
theorem not_dcEnergyWallWithConstant_of_sum_nonzero_moment_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) {r : ℕ}
    (hgt :
      (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) :
    ¬ DCEnergyWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyWallWithConstant_iff_forall_sum_nonzero_moment hψ G K).mp hwall r
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for a single nonzero moment refutes the all-rung
constant wall. -/
theorem not_dcEnergyWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) {r : ℕ} {B : ℝ}
    (hlower :
      B ≤ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r))
    (hbudget :
      (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) < B) :
    ¬ DCEnergyWallWithConstant G K :=
  not_dcEnergyWallWithConstant_of_sum_nonzero_moment_gt hψ G K (hbudget.trans_le hlower)

/-- A single over-budget nonzero moment within the cutoff refutes the
finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) {R r : ℕ}
    (hr : r ≤ R)
    (hgt :
      (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) :
    ¬ DCEnergyWallWithConstantUpTo G K R := by
  intro hwall
  have hle :=
    (dcEnergyWallWithConstantUpTo_iff_forall_sum_nonzero_moment hψ G K R).mp hwall r hr
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for a single nonzero moment within the cutoff
refutes the finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_lower_bound_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) {R r : ℕ} {B : ℝ}
    (hr : r ≤ R)
    (hlower :
      B ≤ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G b‖ ^ (2 * r))
    (hbudget :
      (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) < B) :
    ¬ DCEnergyWallWithConstantUpTo G K R :=
  not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_gt hψ G K hr
    (hbudget.trans_le hlower)

/-- An over-budget nonzero moment at the ceiling depth refutes the one-rung
ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ)
    (hgt :
      (Fintype.card F : ℝ)
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))
        < ∑ b ∈ (Finset.univ : Finset F).erase (0 : F),
            ‖eta ψ G b‖ ^ (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :
    ¬ DCEnergyCeilWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyCeilWallWithConstant_iff_sum_nonzero_moment hψ G K).mp hwall
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for the ceiling-depth nonzero moment refutes
the one-rung ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ) {B : ℝ}
    (hlower :
      B ≤ ∑ b ∈ (Finset.univ : Finset F).erase (0 : F),
        ‖eta ψ G b‖ ^ (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊))
    (hbudget :
      (Fintype.card F : ℝ)
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) < B) :
    ¬ DCEnergyCeilWallWithConstant G K :=
  not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_gt hψ G K
    (hbudget.trans_le hlower)

/-- Constant-`K` DC energy gives the corresponding nonzero per-frequency
moment bound. -/
theorem eta_pow_le_of_dcEnergyBoundWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (h : DCEnergyBoundWithConstant G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
by
  classical
  have hbmem : b ∈ (Finset.univ : Finset F).erase (0 : F) := by simp [hb]
  have hterm :
      ‖eta ψ G b‖ ^ (2 * r)
        ≤ ∑ a ∈ (Finset.univ : Finset F).erase (0 : F), ‖eta ψ G a‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun a : F => ‖eta ψ G a‖ ^ (2 * r))
      (fun a _ => by positivity) hbmem
  exact hterm.trans ((dcEnergyBoundWithConstant_iff_sum_nonzero_moment hψ G r K).mp h)

/-- Optimized constant-`K` sup-norm square bound.  A constant-power
DC-subtracted Wick estimate at `r ≥ log q` gives
`‖η_b‖² ≤ 2e K |G| r` for every nonzero frequency. -/
theorem eta_sq_le_dcOptimizedWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (hK : 0 ≤ K)
    (h : DCEnergyBoundWithConstant G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set nc : ℝ := (G.card : ℝ) with hnc_def
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : 0 < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r
      ≤ q * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)) := by
    rw [← pow_mul]
    have := eta_pow_le_of_dcEnergyBoundWithConstant hψ h hb
    rw [hq_def, hnc_def]
    exact this
  have hbudget_nonneg :
      0 ≤ q * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)) := by
    positivity
  have hstep1 : ‖eta ψ G b‖ ^ 2
      ≤ (q * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)))
          ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hexpand :
      (q * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)))
          ^ ((r : ℝ)⁻¹)
        = q ^ ((r : ℝ)⁻¹) * K
            * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := by
    rw [Real.mul_rpow (le_of_lt hqpos) (by positivity : 0 ≤ K ^ r
        * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r)),
      Real.mul_rpow (by positivity : 0 ≤ K ^ r)
        (mul_nonneg hd0 (by positivity : 0 ≤ nc ^ r)),
      Real.mul_rpow hd0 (by positivity : 0 ≤ nc ^ r),
      Real.pow_rpow_inv_natCast hK hrne,
      Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ nc) hrne]
    ring
  rw [hexpand] at hstep1
  have hbq : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hqpos hr0 hrq
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc ‖eta ψ G b‖ ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * K
          * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := hstep1
    _ ≤ Real.exp 1 * K * (2 * (r : ℝ)) * nc := by gcongr
    _ = 2 * Real.exp 1 * K * nc * (r : ℝ) := by ring

/-- Closed-form square-root endpoint for the constant-`K` wall at the
ceiling depth `r = ⌈log q⌉`. -/
theorem eta_le_sqrt_floor_of_dcEnergyBoundWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {K : ℝ}
    (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (h : DCEnergyBoundWithConstant G r K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt
          (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  have hlog_le_r : Real.log (Fintype.card F : ℝ) ≤ r := by
    rw [hr]
    exact Nat.le_ceil _
  have hsq := eta_sq_le_dcOptimizedWithConstant hψ hr1 hlog_le_r hK h hb
  have hlogq_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq
  have hrlt : (r : ℝ) < Real.log (Fintype.card F : ℝ) + 1 := by
    rw [hr]
    exact Nat.ceil_lt_add_one hlogq_nn
  have hcoef_nn : (0 : ℝ) ≤ 2 * Real.exp 1 * K * (G.card : ℝ) := by positivity
  have hsq2 : ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * K * (G.card : ℝ)
          * (Real.log (Fintype.card F : ℝ) + 1) := by
    calc ‖eta ψ G b‖ ^ 2
        ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := hsq
      _ ≤ 2 * Real.exp 1 * K * (G.card : ℝ)
            * (Real.log (Fintype.card F : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrlt.le hcoef_nn
  rw [show ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq2

/-- All-rung constant-`K` wall gives the closed-form square-root endpoint at
the moment-optimal ceiling depth. -/
theorem eta_le_sqrt_floor_of_dcEnergyWallWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyWallWithConstant G K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt
          (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  exact eta_le_sqrt_floor_of_dcEnergyBoundWithConstant hψ G r hrdef hr1 hq1 hK
    (hwall r) hb

/-- Uniform nonzero-frequency form of
`eta_le_sqrt_floor_of_dcEnergyWallWithConstant`. -/
theorem forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyWallWithConstant G K) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  fun b hb => eta_le_sqrt_floor_of_dcEnergyWallWithConstant hψ G hq hK hwall hb

/-- Finite-depth constant-`K` wall gives the closed-form square-root endpoint
as soon as it reaches the moment-optimal ceiling depth. -/
theorem eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ} {R : ℕ}
    (hR : ⌈Real.log (Fintype.card F : ℝ)⌉₊ ≤ R)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyWallWithConstantUpTo G K R) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt
          (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  exact eta_le_sqrt_floor_of_dcEnergyBoundWithConstant hψ G r hrdef hr1 hq1 hK
    (hwall r (by simpa [hrdef] using hR)) hb

/-- Uniform nonzero-frequency form of the finite-depth constant-wall
endpoint. -/
theorem forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ} {R : ℕ}
    (hR : ⌈Real.log (Fintype.card F : ℝ)⌉₊ ≤ R)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyWallWithConstantUpTo G K R) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  fun b hb => eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo hψ G hR hq hK hwall hb

/-- The one-rung ceiling wall gives the closed-form square-root endpoint. -/
theorem eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyCeilWallWithConstant G K) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt
          (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  exact eta_le_sqrt_floor_of_dcEnergyBoundWithConstant hψ G r hrdef hr1 hq1 hK hwall hb

/-- Uniform nonzero-frequency form of the one-rung ceiling-wall endpoint. -/
theorem forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hwall : DCEnergyCeilWallWithConstant G K) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  fun b hb => eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant hψ G hq hK hwall hb

/-- A ceiling-depth nonzero-moment estimate gives the final optimized
per-frequency bound directly. -/
theorem forall_eta_le_sqrt_floor_of_sum_nonzero_moment_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hmoment :
      ∑ b ∈ (Finset.univ : Finset F).erase (0 : F),
          ‖eta ψ G b‖ ^ (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊)
        ≤ (Fintype.card F : ℝ)
            * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
                * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant hψ G hq hK
    (dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_bound hψ G K hmoment)

/-- Monotonicity of the constant-power DC-energy target, stated at the exact
level needed by applications: if `K^r ≤ K'^r`, then a `K`-bound gives a
`K'`-bound. -/
theorem DCEnergyBoundWithConstant.mono_pow (G : Finset F) (r : ℕ) {K K' : ℝ}
    (hpow : K ^ r ≤ K' ^ r) :
    DCEnergyBoundWithConstant G r K → DCEnergyBoundWithConstant G r K' := by
  intro h
  unfold DCEnergyBoundWithConstant at h ⊢
  have hwick_nonneg : 0 ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
    positivity
  have hscale_nonneg : 0 ≤ (Fintype.card F : ℝ) := by positivity
  exact h.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow hwick_nonneg)
      hscale_nonneg)

/-- Monotonicity in the constant itself, for the nonnegative constants used in
analytic applications. -/
theorem DCEnergyBoundWithConstant.mono (G : Finset F) (r : ℕ) {K K' : ℝ}
    (hK : 0 ≤ K) (hKK' : K ≤ K') :
    DCEnergyBoundWithConstant G r K → DCEnergyBoundWithConstant G r K' :=
  DCEnergyBoundWithConstant.mono_pow G r (pow_le_pow_left₀ hK hKK' r)

/-- Fixed `DCEnergyBound` implies any nonnegative constant-`K` relaxation with
`1 ≤ K`. -/
theorem dcEnergyBoundWithConstant_of_dcEnergyBound_of_one_le
    (G : Finset F) (r : ℕ) {K : ℝ} (hK : 1 ≤ K) (hdc : DCEnergyBound G r) :
    DCEnergyBoundWithConstant G r K :=
  DCEnergyBoundWithConstant.mono G r (by positivity : (0 : ℝ) ≤ 1) hK
    (dcEnergyBoundWithConstant_one_of_dcEnergyBound G r hdc)

/-- The all-rung constant-`1` wall is exactly the original all-rung
DC-subtracted wall. -/
theorem dcEnergyWallWithConstant_one_iff (G : Finset F) :
    DCEnergyWallWithConstant G 1 ↔ ∀ r : ℕ, DCEnergyBound G r := by
  constructor
  · intro h r
    exact dcEnergyBound_of_dcEnergyBoundWithConstant_one G r (h r)
  · intro h r
    exact dcEnergyBoundWithConstant_one_of_dcEnergyBound G r (h r)

/-- Wall-level monotonicity in the constant power budget. -/
theorem DCEnergyWallWithConstant.mono_pow (G : Finset F) {K K' : ℝ}
    (hpow : ∀ r : ℕ, K ^ r ≤ K' ^ r) :
    DCEnergyWallWithConstant G K → DCEnergyWallWithConstant G K' := by
  intro h r
  exact DCEnergyBoundWithConstant.mono_pow G r (hpow r) (h r)

/-- Wall-level monotonicity for nonnegative constants. -/
theorem DCEnergyWallWithConstant.mono (G : Finset F) {K K' : ℝ}
    (hK : 0 ≤ K) (hKK' : K ≤ K') :
    DCEnergyWallWithConstant G K → DCEnergyWallWithConstant G K' :=
  DCEnergyWallWithConstant.mono_pow G (fun r => pow_le_pow_left₀ hK hKK' r)

/-- The original all-rung DC wall implies any nonnegative constant-`K`
relaxation with `1 ≤ K`. -/
theorem dcEnergyWallWithConstant_of_dcEnergyWall_of_one_le
    (G : Finset F) {K : ℝ} (hK : 1 ≤ K) (hwall : ∀ r : ℕ, DCEnergyBound G r) :
    DCEnergyWallWithConstant G K := by
  intro r
  exact dcEnergyBoundWithConstant_of_dcEnergyBound_of_one_le G r hK (hwall r)

/-- An all-rung constant wall restricts to any finite-depth constant wall. -/
theorem DCEnergyWallWithConstant.to_upTo (G : Finset F) (K : ℝ) (R : ℕ)
    (hwall : DCEnergyWallWithConstant G K) :
    DCEnergyWallWithConstantUpTo G K R := by
  intro r _hr
  exact hwall r

/-- Finite-depth wall monotonicity in the depth cutoff. -/
theorem DCEnergyWallWithConstantUpTo.mono_depth (G : Finset F) (K : ℝ) {R R' : ℕ}
    (hRR' : R ≤ R') :
    DCEnergyWallWithConstantUpTo G K R' → DCEnergyWallWithConstantUpTo G K R := by
  intro hwall r hr
  exact hwall r (hr.trans hRR')

/-- Finite-depth wall monotonicity in the constant power budget. -/
theorem DCEnergyWallWithConstantUpTo.mono_pow (G : Finset F) {K K' : ℝ} (R : ℕ)
    (hpow : ∀ r : ℕ, r ≤ R → K ^ r ≤ K' ^ r) :
    DCEnergyWallWithConstantUpTo G K R → DCEnergyWallWithConstantUpTo G K' R := by
  intro hwall r hr
  exact DCEnergyBoundWithConstant.mono_pow G r (hpow r hr) (hwall r hr)

/-- An all-rung constant wall supplies the one-rung ceiling wall. -/
theorem DCEnergyWallWithConstant.to_ceil (G : Finset F) (K : ℝ)
    (hwall : DCEnergyWallWithConstant G K) :
    DCEnergyCeilWallWithConstant G K :=
  hwall ⌈Real.log (Fintype.card F : ℝ)⌉₊

/-- A finite-depth constant wall supplies the one-rung ceiling wall once its
cutoff reaches the ceiling depth. -/
theorem DCEnergyWallWithConstantUpTo.to_ceil (G : Finset F) (K : ℝ) {R : ℕ}
    (hR : ⌈Real.log (Fintype.card F : ℝ)⌉₊ ≤ R)
    (hwall : DCEnergyWallWithConstantUpTo G K R) :
    DCEnergyCeilWallWithConstant G K :=
  hwall ⌈Real.log (Fintype.card F : ℝ)⌉₊ hR

/-- The constant-`1` ceiling wall is exactly the original ceiling-depth
DC-subtracted bound. -/
theorem dcEnergyCeilWallWithConstant_one_iff (G : Finset F) :
    DCEnergyCeilWallWithConstant G 1
      ↔ DCEnergyBound G ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  unfold DCEnergyCeilWallWithConstant
  exact dcEnergyBoundWithConstant_one_iff G ⌈Real.log (Fintype.card F : ℝ)⌉₊

/-- Ceiling-wall monotonicity in the constant power budget. -/
theorem DCEnergyCeilWallWithConstant.mono_pow (G : Finset F) {K K' : ℝ}
    (hpow :
      K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
        ≤ K' ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊) :
    DCEnergyCeilWallWithConstant G K → DCEnergyCeilWallWithConstant G K' :=
  DCEnergyBoundWithConstant.mono_pow G ⌈Real.log (Fintype.card F : ℝ)⌉₊ hpow

/-- Ceiling-wall monotonicity for nonnegative constants. -/
theorem DCEnergyCeilWallWithConstant.mono (G : Finset F) {K K' : ℝ}
    (hK : 0 ≤ K) (hKK' : K ≤ K') :
    DCEnergyCeilWallWithConstant G K → DCEnergyCeilWallWithConstant G K' :=
  DCEnergyCeilWallWithConstant.mono_pow G
    (pow_le_pow_left₀ hK hKK' ⌈Real.log (Fintype.card F : ℝ)⌉₊)

/-- The original ceiling-depth DC bound implies any constant-`K` relaxation
with `1 ≤ K`. -/
theorem dcEnergyCeilWallWithConstant_of_dcEnergyBound_of_one_le
    (G : Finset F) {K : ℝ} (hK : 1 ≤ K)
    (hceil : DCEnergyBound G ⌈Real.log (Fintype.card F : ℝ)⌉₊) :
    DCEnergyCeilWallWithConstant G K :=
  DCEnergyCeilWallWithConstant.mono G (by positivity : (0 : ℝ) ≤ 1) hK
    ((dcEnergyCeilWallWithConstant_one_iff G).mpr hceil)

/-- The finite-depth constant-`1` wall is exactly the original finite-depth
DC-subtracted wall. -/
theorem dcEnergyWallWithConstantUpTo_one_iff (G : Finset F) (R : ℕ) :
    DCEnergyWallWithConstantUpTo G 1 R ↔ ∀ r : ℕ, r ≤ R → DCEnergyBound G r := by
  constructor
  · intro h r hr
    exact dcEnergyBound_of_dcEnergyBoundWithConstant_one G r (h r hr)
  · intro h r hr
    exact dcEnergyBoundWithConstant_one_of_dcEnergyBound G r (h r hr)

/-- A finite-depth original DC wall implies any constant-`K` relaxation with
`1 ≤ K`. -/
theorem dcEnergyWallWithConstantUpTo_of_dcEnergyWallUpTo_of_one_le
    (G : Finset F) (R : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hwall : ∀ r : ℕ, r ≤ R → DCEnergyBound G r) :
    DCEnergyWallWithConstantUpTo G K R := by
  intro r hr
  exact dcEnergyBoundWithConstant_of_dcEnergyBound_of_one_le G r hK (hwall r hr)

/-- Variance flatness at depth `r` gives the corrected DC-subtracted energy
bound consumed by the prize moment machinery. -/
theorem dcEnergyBound_of_variance (G : Finset F) (r : ℕ)
    (hvar : ∑ c : F,
        ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_variance G r).mpr hvar

/-- Corrected DC-subtracted energy gives arbitrary-depth variance flatness. -/
theorem variance_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    ∑ c : F, ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  (dcEnergyBound_iff_variance G r).mp hdc

/-- The arbitrary-depth flatness deviation
`d_r(c) = q * repR G r c - |G|^r`. -/
noncomputable def deviationR (G : Finset F) (r : ℕ) (c : F) : ℝ :=
  (Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r

/-- The unnormalized deviation square-sum is exactly the field size times the
cleared DC-subtracted energy gap. -/
theorem sum_deviationR_sq_eq_card_mul_dcGap (G : Finset F) (r : ℕ) :
    ∑ c : F, (deviationR G r c) ^ 2
      = (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) := by
  simpa [deviationR] using variance_identity G r

/-- Normalized form of the previous identity: the original DC gap is the
unnormalized deviation square-sum divided by the field size. -/
theorem dcGap_eq_sum_deviationR_sq_div_card (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      = (∑ c : F, (deviationR G r c) ^ 2) / (Fintype.card F : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  have h := sum_deviationR_sq_eq_card_mul_dcGap G r
  calc (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      = ((Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ)
            - (G.card : ℝ) ^ (2 * r))) / (Fintype.card F : ℝ) := by
        field_simp [hq]
    _ = (∑ c : F, (deviationR G r c) ^ 2) / (Fintype.card F : ℝ) := by
        rw [← h]

/-- The centered probability-scale representation function:
`repR(c) - |G|^r / q`. -/
noncomputable def centeredRepR (G : Finset F) (r : ℕ) (c : F) : ℝ :=
  (repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)

/-- The centered representation is the normalized deviation. -/
theorem centeredRepR_eq_deviation_div (G : Finset F) (r : ℕ) (c : F) :
    centeredRepR G r c = deviationR G r c / (Fintype.card F : ℝ) := by
  unfold centeredRepR deviationR
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  field_simp [hq]

/-- The raw deviation is the field-size multiple of the centered representation. -/
theorem deviationR_eq_card_mul_centeredRepR (G : Finset F) (r : ℕ) (c : F) :
    deviationR G r c = (Fintype.card F : ℝ) * centeredRepR G r c := by
  unfold deviationR centeredRepR
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  field_simp [hq]

/-- Square form of the deviation/centered scaling identity. -/
theorem deviationR_sq_eq_card_sq_mul_centeredRepR_sq (G : Finset F) (r : ℕ) (c : F) :
    (deviationR G r c) ^ 2
      = (Fintype.card F : ℝ) ^ 2 * (centeredRepR G r c) ^ 2 := by
  rw [deviationR_eq_card_mul_centeredRepR]
  ring

/-- Absolute-value form of the deviation/centered scaling identity. -/
theorem abs_deviationR_eq_card_mul_abs_centeredRepR (G : Finset F) (r : ℕ) (c : F) :
    |deviationR G r c| = (Fintype.card F : ℝ) * |centeredRepR G r c| := by
  rw [deviationR_eq_card_mul_centeredRepR, abs_mul]
  have hq_nonneg : 0 ≤ (Fintype.card F : ℝ) := by positivity
  rw [abs_of_nonneg hq_nonneg]

/-- Pointwise alias from centered representation to raw `repR - mean`. -/
theorem centeredRepR_eq_repR_sub_mean (G : Finset F) (r : ℕ) (c : F) :
    centeredRepR G r c
      = (repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ) := by
  rfl

/-- Pointwise square alias from centered representation to raw `repR - mean`. -/
theorem centeredRepR_sq_eq_repR_sub_mean_sq (G : Finset F) (r : ℕ) (c : F) :
    (centeredRepR G r c) ^ 2
      = ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 := by
  rfl

/-- Pointwise absolute-value alias from centered representation to raw `repR - mean`. -/
theorem abs_centeredRepR_eq_abs_repR_sub_mean (G : Finset F) (r : ℕ) (c : F) :
    |centeredRepR G r c|
      = |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| := by
  rfl

/-- The arbitrary-depth deviation is mean-zero. -/
theorem sum_deviationR_zero (G : Finset F) (r : ℕ) :
    ∑ c : F, deviationR G r c = 0 := by
  unfold deviationR
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ c : F, (repR G r c : ℝ) = (G.card : ℝ) ^ r := by
    have := sum_repR G r
    calc ∑ c : F, (repR G r c : ℝ) = ((∑ c : F, repR G r c : ℕ) : ℝ) := by
          push_cast
          rfl
      _ = ((G.card ^ r : ℕ) : ℝ) := by rw [this]
      _ = (G.card : ℝ) ^ r := by exact_mod_cast Nat.cast_pow G.card r
  have h2 : ∑ _c : F, (G.card : ℝ) ^ r
      = (Fintype.card F : ℝ) * (G.card : ℝ) ^ r := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, h2]
  ring

/-- The centered representation is mean-zero. -/
theorem sum_centeredRepR_zero (G : Finset F) (r : ℕ) :
    ∑ c : F, centeredRepR G r c = 0 := by
  rw [show (∑ c : F, centeredRepR G r c)
      = ∑ c : F, deviationR G r c / (Fintype.card F : ℝ) by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [centeredRepR_eq_deviation_div]]
  calc ∑ c : F, deviationR G r c / (Fintype.card F : ℝ)
      = (∑ c : F, deviationR G r c) / (Fintype.card F : ℝ) := by
        rw [Finset.sum_div]
    _ = 0 := by rw [sum_deviationR_zero, zero_div]

/-- Direct raw representation-function flatness is mean-zero. -/
theorem sum_repR_sub_mean_zero (G : Finset F) (r : ℕ) :
    ∑ c : F, ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) = 0 := by
  simpa [centeredRepR] using sum_centeredRepR_zero G r

/-- Square-sum of centered representation equals normalized deviation variance. -/
theorem sum_centeredRepR_sq_eq_normalized_variance (G : Finset F) (r : ℕ) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      = ∑ c : F, (deviationR G r c) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [centeredRepR_eq_deviation_div]
  ring

/-- Raw `repR - mean` square-sum equals normalized deviation variance. -/
theorem sum_repR_sub_mean_sq_eq_normalized_variance (G : Finset F) (r : ℕ) :
    ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      = ∑ c : F, (deviationR G r c) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  simpa [centeredRepR] using sum_centeredRepR_sq_eq_normalized_variance G r

/-- Unnormalized deviation square-sum is `q^2` times centered square-sum. -/
theorem sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq (G : Finset F) (r : ℕ) :
    ∑ c : F, (deviationR G r c) ^ 2
      = (Fintype.card F : ℝ) ^ 2 * ∑ c : F, (centeredRepR G r c) ^ 2 := by
  calc ∑ c : F, (deviationR G r c) ^ 2
      = ∑ c : F, (Fintype.card F : ℝ) ^ 2 * (centeredRepR G r c) ^ 2 := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact deviationR_sq_eq_card_sq_mul_centeredRepR_sq G r c
    _ = (Fintype.card F : ℝ) ^ 2 * ∑ c : F, (centeredRepR G r c) ^ 2 := by
        rw [Finset.mul_sum]

/-- Unnormalized deviation square-sum is `q^2` times raw `repR - mean`
square-sum. -/
theorem sum_deviationR_sq_eq_card_sq_mul_sum_repR_sub_mean_sq (G : Finset F) (r : ℕ) :
    ∑ c : F, (deviationR G r c) ^ 2
      = (Fintype.card F : ℝ) ^ 2
          * ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 := by
  simpa [centeredRepR] using sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq G r

/-- The original DC gap is field size times the centered probability-scale
variance. -/
theorem dcGap_eq_card_mul_sum_centeredRepR_sq (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      = (Fintype.card F : ℝ) * ∑ c : F, (centeredRepR G r c) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  calc (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      = (∑ c : F, (deviationR G r c) ^ 2) / (Fintype.card F : ℝ) :=
          dcGap_eq_sum_deviationR_sq_div_card G r
    _ = ((Fintype.card F : ℝ) ^ 2 * ∑ c : F, (centeredRepR G r c) ^ 2)
          / (Fintype.card F : ℝ) := by
        rw [sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq G r]
    _ = (Fintype.card F : ℝ) * ∑ c : F, (centeredRepR G r c) ^ 2 := by
        field_simp [hq]

/-- Direct raw `repR - mean` version of the DC-gap/probability-scale variance
identity. -/
theorem dcGap_eq_card_mul_sum_repR_sub_mean_sq (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      = (Fintype.card F : ℝ)
          * ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 := by
  simpa [centeredRepR] using dcGap_eq_card_mul_sum_centeredRepR_sq G r

/-- Constant-`K` DC energy in centered probability-scale variance language. -/
theorem dcEnergyBoundWithConstant_iff_centeredRepR_variance
    (G : Finset F) (r : ℕ) (K : ℝ) :
    DCEnergyBoundWithConstant G r K
      ↔ ∑ c : F, (centeredRepR G r c) ^ 2
          ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  unfold DCEnergyBoundWithConstant
  rw [dcGap_eq_card_mul_sum_centeredRepR_sq G r]
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by positivity
  constructor <;> intro h <;> nlinarith [h, hq]

/-- Constant-`K` DC energy in direct raw `repR - mean` variance language. -/
theorem dcEnergyBoundWithConstant_iff_repR_sub_mean_variance
    (G : Finset F) (r : ℕ) (K : ℝ) :
    DCEnergyBoundWithConstant G r K
      ↔ ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
          ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  simpa [centeredRepR] using dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K

/-- Energy-scale and probability-scale variance budgets are equivalent. -/
theorem deviation_variance_bound_iff_centered_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ} :
    (∑ c : F, (deviationR G r c) ^ 2
        ≤ (Fintype.card F : ℝ) ^ 2 * B)
      ↔ ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B := by
  rw [sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq G r]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h (by positivity)
  · intro h
    exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Energy-scale and raw `repR - mean` variance budgets are equivalent. -/
theorem deviation_variance_bound_iff_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ} :
    (∑ c : F, (deviationR G r c) ^ 2
        ≤ (Fintype.card F : ℝ) ^ 2 * B)
      ↔ ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B := by
  simpa [centeredRepR] using deviation_variance_bound_iff_centered_variance_bound G r (B := B)

/-- Constant-`K` DC energy in unnormalized deviation square-sum language. -/
theorem dcEnergyBoundWithConstant_iff_deviation_variance
    (G : Finset F) (r : ℕ) (K : ℝ) :
    DCEnergyBoundWithConstant G r K
      ↔ ∑ c : F, (deviationR G r c) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
              * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  rw [deviation_variance_bound_iff_centered_variance_bound G r]
  exact dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K

/-- The one-rung ceiling wall in centered probability-scale variance
language. -/
theorem dcEnergyCeilWallWithConstant_iff_centeredRepR_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyCeilWallWithConstant G K
      ↔ ∑ c : F, (centeredRepR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
          ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊) := by
  unfold DCEnergyCeilWallWithConstant
  exact dcEnergyBoundWithConstant_iff_centeredRepR_variance G
    ⌈Real.log (Fintype.card F : ℝ)⌉₊ K

/-- The one-rung ceiling wall in raw `repR - mean` variance language. -/
theorem dcEnergyCeilWallWithConstant_iff_repR_sub_mean_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyCeilWallWithConstant G K
      ↔ ∑ c : F,
          ((repR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c : ℝ)
            - (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              / (Fintype.card F : ℝ)) ^ 2
          ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊) := by
  unfold DCEnergyCeilWallWithConstant
  exact dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G
    ⌈Real.log (Fintype.card F : ℝ)⌉₊ K

/-- The one-rung ceiling wall in unnormalized deviation square-sum language. -/
theorem dcEnergyCeilWallWithConstant_iff_deviation_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyCeilWallWithConstant G K
      ↔ ∑ c : F, (deviationR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
            * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
                * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) := by
  unfold DCEnergyCeilWallWithConstant
  exact dcEnergyBoundWithConstant_iff_deviation_variance G
    ⌈Real.log (Fintype.card F : ℝ)⌉₊ K

/-- A centered variance estimate at the ceiling depth proves the one-rung
ceiling wall. -/
theorem dcEnergyCeilWallWithConstant_of_centered_variance_bound
    (G : Finset F) (K : ℝ)
    (hvar :
      ∑ c : F, (centeredRepR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
        ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :
    DCEnergyCeilWallWithConstant G K :=
  (dcEnergyCeilWallWithConstant_iff_centeredRepR_variance G K).mpr hvar

/-- A raw `repR - mean` variance estimate at the ceiling depth proves the
one-rung ceiling wall. -/
theorem dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_bound
    (G : Finset F) (K : ℝ)
    (hvar :
      ∑ c : F,
          ((repR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c : ℝ)
            - (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              / (Fintype.card F : ℝ)) ^ 2
        ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :
    DCEnergyCeilWallWithConstant G K :=
  (dcEnergyCeilWallWithConstant_iff_repR_sub_mean_variance G K).mpr hvar

/-- An unnormalized deviation variance estimate at the ceiling depth proves
the one-rung ceiling wall. -/
theorem dcEnergyCeilWallWithConstant_of_deviation_variance_bound
    (G : Finset F) (K : ℝ)
    (hvar :
      ∑ c : F, (deviationR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
        ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))) :
    DCEnergyCeilWallWithConstant G K :=
  (dcEnergyCeilWallWithConstant_iff_deviation_variance G K).mpr hvar

/-- A ceiling-depth centered flatness estimate gives the final optimized
per-frequency bound directly. -/
theorem forall_eta_le_sqrt_floor_of_centered_variance_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hvar :
      ∑ c : F, (centeredRepR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
        ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant hψ G hq hK
    (dcEnergyCeilWallWithConstant_of_centered_variance_bound G K hvar)

/-- A ceiling-depth raw `repR - mean` flatness estimate gives the final
optimized per-frequency bound directly. -/
theorem forall_eta_le_sqrt_floor_of_repR_sub_mean_variance_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hvar :
      ∑ c : F,
          ((repR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c : ℝ)
            - (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
              / (Fintype.card F : ℝ)) ^ 2
        ≤ K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant hψ G hq hK
    (dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_bound G K hvar)

/-- A ceiling-depth unnormalized deviation flatness estimate gives the final
optimized per-frequency bound directly. -/
theorem forall_eta_le_sqrt_floor_of_deviation_variance_bound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {K : ℝ}
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hK : 0 ≤ K)
    (hvar :
      ∑ c : F, (deviationR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2
        ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt
            (2 * Real.exp 1 * K * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant hψ G hq hK
    (dcEnergyCeilWallWithConstant_of_deviation_variance_bound G K hvar)

/-- All-rung constant-`K` wall in centered probability-scale variance
language. -/
theorem dcEnergyWallWithConstant_iff_forall_centeredRepR_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyWallWithConstant G K
      ↔ ∀ r : ℕ,
          ∑ c : F, (centeredRepR G r c) ^ 2
            ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  constructor
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mp (h r)
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mpr (h r)

/-- All-rung constant-`K` wall in raw `repR - mean` variance language. -/
theorem dcEnergyWallWithConstant_iff_forall_repR_sub_mean_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyWallWithConstant G K
      ↔ ∀ r : ℕ,
          ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
              ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  constructor
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mp (h r)
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mpr (h r)

/-- All-rung constant-`K` wall in unnormalized deviation square-sum
language. -/
theorem dcEnergyWallWithConstant_iff_forall_deviation_variance
    (G : Finset F) (K : ℝ) :
    DCEnergyWallWithConstant G K
      ↔ ∀ r : ℕ,
          ∑ c : F, (deviationR G r c) ^ 2
            ≤ (Fintype.card F : ℝ) ^ 2
                * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  constructor
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mp (h r)
  · intro h r
    exact (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mpr (h r)

/-- Finite-depth constant-`K` wall in centered probability-scale variance
language. -/
theorem dcEnergyWallWithConstantUpTo_iff_forall_centeredRepR_variance
    (G : Finset F) (K : ℝ) (R : ℕ) :
    DCEnergyWallWithConstantUpTo G K R
      ↔ ∀ r : ℕ, r ≤ R →
          ∑ c : F, (centeredRepR G r c) ^ 2
            ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  constructor
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mp (h r hr)
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mpr (h r hr)

/-- Finite-depth constant-`K` wall in raw `repR - mean` variance language. -/
theorem dcEnergyWallWithConstantUpTo_iff_forall_repR_sub_mean_variance
    (G : Finset F) (K : ℝ) (R : ℕ) :
    DCEnergyWallWithConstantUpTo G K R
      ↔ ∀ r : ℕ, r ≤ R →
          ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
              ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  constructor
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mp (h r hr)
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mpr (h r hr)

/-- Finite-depth constant-`K` wall in unnormalized deviation square-sum
language. -/
theorem dcEnergyWallWithConstantUpTo_iff_forall_deviation_variance
    (G : Finset F) (K : ℝ) (R : ℕ) :
    DCEnergyWallWithConstantUpTo G K R
      ↔ ∀ r : ℕ, r ≤ R →
          ∑ c : F, (deviationR G r c) ^ 2
            ≤ (Fintype.card F : ℝ) ^ 2
                * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  constructor
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mp (h r hr)
  · intro h r hr
    exact (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mpr (h r hr)

/-- A single over-budget centered variance refutes the all-rung constant
wall. -/
theorem not_dcEnergyWallWithConstant_of_centered_variance_gt
    (G : Finset F) (K : ℝ) {r : ℕ}
    (hgt :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F, (centeredRepR G r c) ^ 2) :
    ¬ DCEnergyWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyWallWithConstant_iff_forall_centeredRepR_variance G K).mp hwall r
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for a single centered variance refutes the
all-rung constant wall. -/
theorem not_dcEnergyWallWithConstant_of_centered_variance_lower_bound_gt
    (G : Finset F) (K : ℝ) {r : ℕ} {B : ℝ}
    (hlower : B ≤ ∑ c : F, (centeredRepR G r c) ^ 2)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyWallWithConstant G K :=
  not_dcEnergyWallWithConstant_of_centered_variance_gt G K (hbudget.trans_le hlower)

/-- A single over-budget raw `repR - mean` variance refutes the all-rung
constant wall. -/
theorem not_dcEnergyWallWithConstant_of_repR_sub_mean_variance_gt
    (G : Finset F) (K : ℝ) {r : ℕ}
    (hgt :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyWallWithConstant_iff_forall_repR_sub_mean_variance G K).mp hwall r
  exact not_le_of_gt hgt hle

/-- A single over-budget unnormalized deviation variance refutes the all-rung
constant wall. -/
theorem not_dcEnergyWallWithConstant_of_deviation_variance_gt
    (G : Finset F) (K : ℝ) {r : ℕ}
    (hgt :
      (Fintype.card F : ℝ) ^ 2
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < ∑ c : F, (deviationR G r c) ^ 2) :
    ¬ DCEnergyWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyWallWithConstant_iff_forall_deviation_variance G K).mp hwall r
  exact not_le_of_gt hgt hle

/-- A single over-budget centered variance within the cutoff refutes the
finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_centered_variance_gt
    (G : Finset F) (K : ℝ) {R r : ℕ} (hr : r ≤ R)
    (hgt :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F, (centeredRepR G r c) ^ 2) :
    ¬ DCEnergyWallWithConstantUpTo G K R := by
  intro hwall
  have hle :=
    (dcEnergyWallWithConstantUpTo_iff_forall_centeredRepR_variance G K R).mp hwall r hr
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for centered variance within the cutoff refutes
the finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_centered_variance_lower_bound_gt
    (G : Finset F) (K : ℝ) {R r : ℕ} {B : ℝ} (hr : r ≤ R)
    (hlower : B ≤ ∑ c : F, (centeredRepR G r c) ^ 2)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyWallWithConstantUpTo G K R :=
  not_dcEnergyWallWithConstantUpTo_of_centered_variance_gt G K hr (hbudget.trans_le hlower)

/-- A single over-budget raw `repR - mean` variance within the cutoff refutes
the finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_repR_sub_mean_variance_gt
    (G : Finset F) (K : ℝ) {R r : ℕ} (hr : r ≤ R)
    (hgt :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyWallWithConstantUpTo G K R := by
  intro hwall
  have hle :=
    (dcEnergyWallWithConstantUpTo_iff_forall_repR_sub_mean_variance G K R).mp hwall r hr
  exact not_le_of_gt hgt hle

/-- A single over-budget unnormalized deviation variance within the cutoff
refutes the finite-depth constant wall. -/
theorem not_dcEnergyWallWithConstantUpTo_of_deviation_variance_gt
    (G : Finset F) (K : ℝ) {R r : ℕ} (hr : r ≤ R)
    (hgt :
      (Fintype.card F : ℝ) ^ 2
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < ∑ c : F, (deviationR G r c) ^ 2) :
    ¬ DCEnergyWallWithConstantUpTo G K R := by
  intro hwall
  have hle :=
    (dcEnergyWallWithConstantUpTo_iff_forall_deviation_variance G K R).mp hwall r hr
  exact not_le_of_gt hgt hle

/-- An over-budget centered variance at the ceiling depth refutes the
one-rung ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_centered_variance_gt
    (G : Finset F) (K : ℝ)
    (hgt :
      K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)
        < ∑ c : F, (centeredRepR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2) :
    ¬ DCEnergyCeilWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyCeilWallWithConstant_iff_centeredRepR_variance G K).mp hwall
  exact not_le_of_gt hgt hle

/-- A lower-bound certificate for centered variance at the ceiling depth
refutes the one-rung ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_centered_variance_lower_bound_gt
    (G : Finset F) (K : ℝ) {B : ℝ}
    (hlower : B ≤ ∑ c : F, (centeredRepR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2)
    (hbudget :
      K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊) < B) :
    ¬ DCEnergyCeilWallWithConstant G K :=
  not_dcEnergyCeilWallWithConstant_of_centered_variance_gt G K (hbudget.trans_le hlower)

/-- An over-budget raw `repR - mean` variance at the ceiling depth refutes the
one-rung ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_gt
    (G : Finset F) (K : ℝ)
    (hgt :
      K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
          * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
            * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊)
        < ∑ c : F,
            ((repR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c : ℝ)
              - (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
                / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyCeilWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyCeilWallWithConstant_iff_repR_sub_mean_variance G K).mp hwall
  exact not_le_of_gt hgt hle

/-- An over-budget unnormalized deviation variance at the ceiling depth
refutes the one-rung ceiling wall. -/
theorem not_dcEnergyCeilWallWithConstant_of_deviation_variance_gt
    (G : Finset F) (K : ℝ)
    (hgt :
      (Fintype.card F : ℝ) ^ 2
          * (K ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊
            * ((Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F : ℝ)⌉₊ - 1) : ℝ)
              * (G.card : ℝ) ^ ⌈Real.log (Fintype.card F : ℝ)⌉₊))
        < ∑ c : F, (deviationR G ⌈Real.log (Fintype.card F : ℝ)⌉₊ c) ^ 2) :
    ¬ DCEnergyCeilWallWithConstant G K := by
  intro hwall
  have hle := (dcEnergyCeilWallWithConstant_iff_deviation_variance G K).mp hwall
  exact not_le_of_gt hgt hle

/-- A budgeted unnormalized deviation consumer for the constant-`K` target. -/
theorem dcEnergyBoundWithConstant_of_deviation_variance_bound
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hvar : ∑ c : F, (deviationR G r c) ^ 2 ≤ B)
    (hbudget :
      B ≤ (Fintype.card F : ℝ) ^ 2
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    DCEnergyBoundWithConstant G r K :=
  (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mpr (hvar.trans hbudget)

/-- If the unnormalized deviation square-sum exceeds the constant-`K` Wick
budget, then the constant-`K` DC-energy target is impossible. -/
theorem not_dcEnergyBoundWithConstant_of_deviation_variance_gt
    (G : Finset F) (r : ℕ) (K : ℝ)
    (hbudget :
      (Fintype.card F : ℝ) ^ 2
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        < ∑ c : F, (deviationR G r c) ^ 2) :
    ¬ DCEnergyBoundWithConstant G r K := by
  intro hdc
  have hle := (dcEnergyBoundWithConstant_iff_deviation_variance G r K).mp hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate obstruction for the constant-`K` target. -/
theorem not_dcEnergyBoundWithConstant_of_deviation_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hlower : B ≤ ∑ c : F, (deviationR G r c) ^ 2)
    (hbudget :
      (Fintype.card F : ℝ) ^ 2
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) < B) :
    ¬ DCEnergyBoundWithConstant G r K :=
  not_dcEnergyBoundWithConstant_of_deviation_variance_gt G r K (hbudget.trans_le hlower)

/-- A budgeted centered-variance consumer for the constant-`K` target. -/
theorem dcEnergyBoundWithConstant_of_centered_variance_bound
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    (hbudget :
      B ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBoundWithConstant G r K :=
  (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mpr (hvar.trans hbudget)

/-- A budgeted raw `repR - mean` variance consumer for the constant-`K` target. -/
theorem dcEnergyBoundWithConstant_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hvar : ∑ c : F,
      ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (hbudget :
      B ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBoundWithConstant G r K :=
  (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mpr (hvar.trans hbudget)

/-- If centered variance exceeds the constant-`K` Wick budget, then the
constant-`K` DC-energy target is impossible. -/
theorem not_dcEnergyBoundWithConstant_of_centered_variance_gt
    (G : Finset F) (r : ℕ) (K : ℝ)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F, (centeredRepR G r c) ^ 2) :
    ¬ DCEnergyBoundWithConstant G r K := by
  intro hdc
  have hle := (dcEnergyBoundWithConstant_iff_centeredRepR_variance G r K).mp hdc
  exact not_le_of_gt hbudget hle

/-- If raw `repR - mean` variance exceeds the constant-`K` Wick budget, then
the constant-`K` DC-energy target is impossible. -/
theorem not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_gt
    (G : Finset F) (r : ℕ) (K : ℝ)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyBoundWithConstant G r K := by
  intro hdc
  have hle := (dcEnergyBoundWithConstant_iff_repR_sub_mean_variance G r K).mp hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate obstruction in centered variance language for the
constant-`K` target. -/
theorem not_dcEnergyBoundWithConstant_of_centered_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hlower : B ≤ ∑ c : F, (centeredRepR G r c) ^ 2)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyBoundWithConstant G r K :=
  not_dcEnergyBoundWithConstant_of_centered_variance_gt G r K (hbudget.trans_le hlower)

/-- Lower-bound certificate obstruction in raw `repR - mean` variance language
for the constant-`K` target. -/
theorem not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) (K : ℝ) {B : ℝ}
    (hlower : B ≤ ∑ c : F,
      ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2)
    (hbudget :
      K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyBoundWithConstant G r K :=
  not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_gt G r K (hbudget.trans_le hlower)

/-- Energy-scale variance bound gives probability-scale centered variance. -/
theorem centered_variance_bound_of_deviation_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * B) :
    ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B :=
  (deviation_variance_bound_iff_centered_variance_bound G r).mp hvar

/-- Probability-scale centered variance gives the corresponding energy-scale
deviation variance bound. -/
theorem deviation_variance_bound_of_centered_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) :
    ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * B :=
  (deviation_variance_bound_iff_centered_variance_bound G r).mpr hvar

/-- Energy-scale variance bound gives raw `repR - mean` variance. -/
theorem repR_sub_mean_variance_bound_of_deviation_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * B) :
    ∑ c : F,
      ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B :=
  (deviation_variance_bound_iff_repR_sub_mean_variance_bound G r).mp hvar

/-- Raw `repR - mean` variance gives the corresponding energy-scale
deviation variance bound. -/
theorem deviation_variance_bound_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F,
      ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B) :
    ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2 * B :=
  (deviation_variance_bound_iff_repR_sub_mean_variance_bound G r).mpr hvar

/-- The centered and raw `repR - mean` square-sums are identical. -/
theorem sum_centeredRepR_sq_eq_sum_repR_sub_mean_sq (G : Finset F) (r : ℕ) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      = ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 := by
  rfl

/-- Centered and raw `repR - mean` variance budgets are the same hypothesis. -/
theorem centered_variance_bound_iff_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) {B : ℝ} :
    (∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
      ↔ ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B := by
  rfl

/-- Multiplicative invariance of the `r`-fold representation function. -/
theorem repR_smul (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    repR G r (a * c) = repR G r c := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hainv : a⁻¹ ∈ G := hinv ha
  have hmemA : ∀ x : F, a * x ∈ G ↔ x ∈ G := by
    intro x
    constructor
    · intro hx
      have : a⁻¹ * (a * x) ∈ G := hmul hainv hx
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
    · intro hx
      exact hmul ha hx
  have hreindex : ∀ f : (Fin r → F) → ℕ,
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), f (fun i => a * v i)
        = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), f v := by
    intro f
    refine Finset.sum_nbij' (i := fun v j => a * v j) (j := fun v j => a⁻¹ * v j)
      (fun v hv => ?_) (fun v hv => ?_) (fun v _ => ?_) (fun v _ => ?_) (fun v _ => rfl)
    · rw [Fintype.mem_piFinset] at hv ⊢
      intro j
      exact (hmemA (v j)).mpr (hv j)
    · rw [Fintype.mem_piFinset] at hv ⊢
      intro j
      exact hmul hainv (hv j)
    · funext j
      change a⁻¹ * (a * v j) = v j
      rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    · funext j
      change a * (a⁻¹ * v j) = v j
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  unfold repR
  rw [← hreindex (fun v => if ∑ i, v i = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [show (∑ i, a * v i) = a * ∑ i, v i by rw [Finset.mul_sum]]
  simp only [mul_right_inj' ha0]

/-- The general variance summand is constant on multiplicative `G`-orbits. -/
theorem varianceSummand_smul (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    ((Fintype.card F : ℝ) * (repR G r (a * c) : ℝ) - (G.card : ℝ) ^ r) ^ 2
      = ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2 := by
  rw [repR_smul G r hmul hinv h0 ha c]

/-- The arbitrary-depth deviation inherits multiplicative invariance. -/
theorem deviationR_smul (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    deviationR G r (a * c) = deviationR G r c := by
  unfold deviationR
  rw [repR_smul G r hmul hinv h0 ha c]

/-- The centered representation inherits multiplicative invariance. -/
theorem centeredRepR_smul (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    centeredRepR G r (a * c) = centeredRepR G r c := by
  rw [centeredRepR_eq_deviation_div, centeredRepR_eq_deviation_div,
    deviationR_smul G r hmul hinv h0 ha c]

/-- The raw `repR - mean` representation inherits multiplicative invariance. -/
theorem repR_sub_mean_smul (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    (repR G r (a * c) : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)
      = (repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ) := by
  simpa [centeredRepR] using centeredRepR_smul G r hmul hinv h0 ha c

/-- Arbitrary-depth orbit multiplicity for the flatness deficit. -/
theorem deficit_ge_orbit (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (deviationR G r b) ^ 2 ≤ ∑ c : F, (deviationR G r c) ^ 2 := by
  classical
  set orbit : Finset F := G.image (fun a => a * b) with horbit
  have hcard : orbit.card = G.card := by
    rw [horbit, Finset.card_image_of_injective _ (fun x y h => by
      exact mul_right_cancel₀ hb h)]
  have hconst : ∀ c ∈ orbit, (deviationR G r c) ^ 2 = (deviationR G r b) ^ 2 := by
    intro c hc
    rw [horbit, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [show a * b = a * b from rfl, deviationR_smul G r hmul hinv h0 ha b]
  calc (G.card : ℝ) * (deviationR G r b) ^ 2
      = ∑ _c ∈ orbit, (deviationR G r b) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = ∑ c ∈ orbit, (deviationR G r c) ^ 2 :=
        (Finset.sum_congr rfl hconst).symm
    _ ≤ ∑ c : F, (deviationR G r c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => sq_nonneg _)

/-- Orbit multiplicity for the centered probability-scale representation. -/
theorem centered_deficit_ge_orbit (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (centeredRepR G r b) ^ 2
      ≤ ∑ c : F, (centeredRepR G r c) ^ 2 := by
  classical
  set orbit : Finset F := G.image (fun a => a * b) with horbit
  have hcard : orbit.card = G.card := by
    rw [horbit, Finset.card_image_of_injective _ (fun x y h => by
      exact mul_right_cancel₀ hb h)]
  have hconst : ∀ c ∈ orbit, (centeredRepR G r c) ^ 2 = (centeredRepR G r b) ^ 2 := by
    intro c hc
    rw [horbit, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [show a * b = a * b from rfl, centeredRepR_smul G r hmul hinv h0 ha b]
  calc (G.card : ℝ) * (centeredRepR G r b) ^ 2
      = ∑ _c ∈ orbit, (centeredRepR G r b) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = ∑ c ∈ orbit, (centeredRepR G r c) ^ 2 :=
        (Finset.sum_congr rfl hconst).symm
    _ ≤ ∑ c : F, (centeredRepR G r c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => sq_nonneg _)

/-- Orbit multiplicity for the raw `repR - mean` variance. -/
theorem repR_sub_mean_variance_ge_orbit (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ)
        * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 := by
  simpa [centeredRepR] using centered_deficit_ge_orbit G r hmul hinv h0 hb

/-- Orbit multiplicity in DC-energy form. -/
theorem energy_ge_orbit (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (deviationR G r b) ^ 2
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) := by
  have h := deficit_ge_orbit G r hmul hinv h0 hb
  rwa [show (∑ c : F, (deviationR G r c) ^ 2)
      = ∑ c : F, ((Fintype.card F : ℝ) * (repR G r c : ℝ) - (G.card : ℝ) ^ r) ^ 2 from rfl,
    variance_identity G r] at h

/-- Under the corrected DC-subtracted Wick bound, each nonzero deviation
gets the orbit-multiplicity budget. -/
theorem orbit_deviation_budget_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (deviationR G r b) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  have horbit := energy_ge_orbit G r hmul hinv h0 hb
  unfold DCEnergyBound at hdc
  calc (G.card : ℝ) * (deviationR G r b) ^ 2
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) :=
        horbit
    _ ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :=
        mul_le_mul_of_nonneg_left hdc (by positivity)
    _ = (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by ring

/-- Divided pointwise deviation budget, exposing the `/ |G|` saving. -/
theorem deviation_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (deviationR G r b) ^ 2
      ≤ ((Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
          / (G.card : ℝ) := by
  have hbudget := orbit_deviation_budget_of_dcEnergyBound G r hmul hinv h0 hdc hb
  have hcard_pos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGpos
  have hbudget' :
      (deviationR G r b) ^ 2 * (G.card : ℝ)
        ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
    simpa [mul_comm] using hbudget
  exact (le_div_iff₀ hcard_pos).mpr hbudget'

/-- Normalized pointwise deviation budget.  Dividing the pointwise orbit
budget by `q^2` exposes the variance scale:
`(d_r(b) / q)^2 <= (2r-1)!! * |G|^r / |G|`. -/
theorem normalized_deviation_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (deviationR G r b) ^ 2 / (Fintype.card F : ℝ) ^ 2
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ) := by
  have hdiv := deviation_sq_le_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb
  have hq2pos : 0 < (Fintype.card F : ℝ) ^ 2 := by positivity
  calc (deviationR G r b) ^ 2 / (Fintype.card F : ℝ) ^ 2
      ≤ (((Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
          / (G.card : ℝ)) / (Fintype.card F : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hdiv (le_of_lt hq2pos)
    _ = ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ) := by
        field_simp [ne_of_gt hq2pos]

/-- Global normalized flatness from `DCEnergyBound`.  This is the
probability-scale version of the arbitrary-depth variance bound:
`Σ_c (d_r(c)^2 / q^2) <= (2r-1)!! * |G|^r`. -/
theorem normalized_variance_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    ∑ c : F, (deviationR G r c) ^ 2 / (Fintype.card F : ℝ) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hvar := variance_bound_of_dcEnergyBound G r hdc
  have hvar' : ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
    simpa [deviationR] using hvar
  have hq2pos : 0 < (Fintype.card F : ℝ) ^ 2 := by positivity
  calc ∑ c : F, (deviationR G r c) ^ 2 / (Fintype.card F : ℝ) ^ 2
      = (∑ c : F, (deviationR G r c) ^ 2) / (Fintype.card F : ℝ) ^ 2 := by
        rw [Finset.sum_div]
    _ ≤ ((Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
          / (Fintype.card F : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hvar' (le_of_lt hq2pos)
    _ = (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
        field_simp [ne_of_gt hq2pos]

/-- The normalized flatness condition is equivalent to `DCEnergyBound`. -/
theorem dcEnergyBound_iff_normalized_variance (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ c : F, (deviationR G r c) ^ 2 / (Fintype.card F : ℝ) ^ 2
          ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  constructor
  · exact normalized_variance_bound_of_dcEnergyBound G r
  · intro hnorm
    apply dcEnergyBound_of_variance G r
    have hq2pos : 0 < (Fintype.card F : ℝ) ^ 2 := by positivity
    have hsum :
        (∑ c : F, (deviationR G r c) ^ 2) / (Fintype.card F : ℝ) ^ 2
          ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
      simpa [Finset.sum_div] using hnorm
    have hmul := (div_le_iff₀ hq2pos).mp hsum
    have hraw :
        ∑ c : F, (deviationR G r c) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [deviationR] using hraw

/-- `DCEnergyBound` in centered probability-scale representation language. -/
theorem dcEnergyBound_iff_centeredRepR_variance (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ c : F, (centeredRepR G r c) ^ 2
          ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  rw [dcEnergyBound_iff_normalized_variance G r]
  rw [sum_centeredRepR_sq_eq_normalized_variance G r]

/-- `DCEnergyBound` in unnormalized deviation square-sum language. -/
theorem dcEnergyBound_iff_deviation_variance (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ c : F, (deviationR G r c) ^ 2
          ≤ (Fintype.card F : ℝ) ^ 2
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  rw [deviation_variance_bound_iff_centered_variance_bound G r]
  exact dcEnergyBound_iff_centeredRepR_variance G r

/-- Unnormalized energy-scale deviation variance gives `DCEnergyBound`. -/
theorem dcEnergyBound_of_deviation_variance (G : Finset F) (r : ℕ)
    (hvar : ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_deviation_variance G r).mpr hvar

/-- A budgeted energy-scale flatness consumer: if an analytic estimate bounds
the unnormalized deviation square-sum by `B`, and `B` fits the Wick energy
budget, then `DCEnergyBound` follows. -/
theorem dcEnergyBound_of_deviation_variance_bound (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (deviationR G r c) ^ 2 ≤ B)
    (hbudget : B ≤ (Fintype.card F : ℝ) ^ 2
      * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    DCEnergyBound G r :=
  dcEnergyBound_of_deviation_variance G r (hvar.trans hbudget)

/-- `DCEnergyBound` gives the unnormalized energy-scale deviation variance
bound. -/
theorem deviation_variance_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    ∑ c : F, (deviationR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  (dcEnergyBound_iff_deviation_variance G r).mp hdc

/-- If the unnormalized deviation square-sum exceeds the Wick energy budget,
then `DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_deviation_variance_gt (G : Finset F) (r : ℕ)
    (hbudget :
      (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < ∑ c : F, (deviationR G r c) ^ 2) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := deviation_variance_bound_of_dcEnergyBound G r hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate form: if some certified lower bound `B` for the
unnormalized deviation square-sum already exceeds the Wick energy budget, then
`DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_deviation_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hlower : B ≤ ∑ c : F, (deviationR G r c) ^ 2)
    (hbudget :
      (Fintype.card F : ℝ) ^ 2
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) < B) :
    ¬ DCEnergyBound G r :=
  not_dcEnergyBound_of_deviation_variance_gt G r (hbudget.trans_le hlower)

/-- `DCEnergyBound` gives centered probability-scale variance flatness. -/
theorem centered_variance_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  (dcEnergyBound_iff_centeredRepR_variance G r).mp hdc

/-- Centered probability-scale variance flatness gives `DCEnergyBound`. -/
theorem dcEnergyBound_of_centered_variance (G : Finset F) (r : ℕ)
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_centeredRepR_variance G r).mpr hvar

/-- If the centered probability-scale variance exceeds the Wick budget, then
`DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_centered_variance_gt (G : Finset F) (r : ℕ)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < ∑ c : F, (centeredRepR G r c) ^ 2) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := centered_variance_bound_of_dcEnergyBound G r hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate form: if a certified lower bound `B` for centered
variance already exceeds the Wick variance budget, then `DCEnergyBound` is
impossible. -/
theorem not_dcEnergyBound_of_centered_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hlower : B ≤ ∑ c : F, (centeredRepR G r c) ^ 2)
    (hbudget : (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r < B) :
    ¬ DCEnergyBound G r :=
  not_dcEnergyBound_of_centered_variance_gt G r (hbudget.trans_le hlower)

/-- `DCEnergyBound` stated directly as raw representation-function flatness:
the square-sum of `repR(G,r,c) - |G|^r/q` is at most the Wick budget. -/
theorem dcEnergyBound_iff_repR_sub_mean_variance (G : Finset F) (r : ℕ) :
    DCEnergyBound G r
      ↔ ∑ c : F,
          ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
          ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  simpa [centeredRepR] using dcEnergyBound_iff_centeredRepR_variance G r

/-- `DCEnergyBound` gives raw representation-function variance flatness. -/
theorem repR_sub_mean_variance_bound_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) :
    ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  (dcEnergyBound_iff_repR_sub_mean_variance G r).mp hdc

/-- Raw representation-function variance flatness gives `DCEnergyBound`. -/
theorem dcEnergyBound_of_repR_sub_mean_variance (G : Finset F) (r : ℕ)
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  (dcEnergyBound_iff_repR_sub_mean_variance G r).mpr hvar

/-- If the raw `repR - mean` variance exceeds the Wick budget, then
`DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_repR_sub_mean_variance_gt (G : Finset F) (r : ℕ)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < ∑ c : F,
            ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := repR_sub_mean_variance_bound_of_dcEnergyBound G r hdc
  exact not_le_of_gt hbudget hle

/-- Lower-bound certificate form: if a certified lower bound `B` for raw
`repR - mean` variance already exceeds the Wick variance budget, then
`DCEnergyBound` is impossible. -/
theorem not_dcEnergyBound_of_repR_sub_mean_variance_lower_bound_gt
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hlower : B ≤ ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2)
    (hbudget : (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r < B) :
    ¬ DCEnergyBound G r :=
  not_dcEnergyBound_of_repR_sub_mean_variance_gt G r (hbudget.trans_le hlower)

/-- A budgeted raw `L^2` flatness consumer: if an analytic estimate bounds the
raw `repR - mean` square-sum by `B`, and `B` fits the Wick budget, then
`DCEnergyBound` follows. -/
theorem dcEnergyBound_of_repR_sub_mean_variance_bound (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (hbudget : B ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_repR_sub_mean_variance G r (hvar.trans hbudget)

/-- Tail-count form of centered flatness: the number of offsets with centered
representation at least `a` is bounded by the centered second moment divided by
`a^2`. -/
theorem card_filter_abs_centeredRepR_ge_le_variance_div (G : Finset F) (r : ℕ)
    {a : ℝ} (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ (∑ c : F, (centeredRepR G r c) ^ 2) / a ^ 2 := by
  simpa [sub_zero] using
    (ArkLib.card_filter_abs_sub_ge_le_sum_sq_div
      (X := fun c : F => centeredRepR G r c) (μ := 0) (a := a) ha)

/-- Tail-count form from a direct centered variance hypothesis. -/
theorem card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ B / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  calc (((Finset.univ : Finset F).filter (fun c => a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ (∑ c : F, (centeredRepR G r c) ^ 2) / a ^ 2 :=
        card_filter_abs_centeredRepR_ge_le_variance_div G r ha
    _ ≤ B / a ^ 2 :=
        div_le_div_of_nonneg_right hvar (le_of_lt ha2)

/-- Tail-count form from `DCEnergyBound`. -/
theorem card_filter_abs_centeredRepR_ge_le_of_dcEnergyBound
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) {a : ℝ} (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / a ^ 2 :=
  card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound G r
    (centered_variance_bound_of_dcEnergyBound G r hdc) ha

/-- Nonzero-tail count form from a direct centered variance hypothesis. -/
theorem card_filter_nonzero_abs_centeredRepR_ge_le_of_centered_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (ha : 0 < a) :
    (((Finset.univ : Finset F).filter
        (fun c => c ≠ 0 ∧ a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ B / a ^ 2 := by
  have hsubset :
      (Finset.univ : Finset F).filter (fun c => c ≠ 0 ∧ a ≤ |centeredRepR G r c|)
        ⊆ (Finset.univ : Finset F).filter (fun c => a ≤ |centeredRepR G r c|) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.2⟩
  calc (((Finset.univ : Finset F).filter
        (fun c => c ≠ 0 ∧ a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ (((Finset.univ : Finset F).filter
        (fun c => a ≤ |centeredRepR G r c|)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
    _ ≤ B / a ^ 2 :=
        card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound G r hvar ha

/-- Nonzero-tail count form from `DCEnergyBound`. -/
theorem card_filter_nonzero_abs_centeredRepR_ge_le_of_dcEnergyBound
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) {a : ℝ} (ha : 0 < a) :
    (((Finset.univ : Finset F).filter
        (fun c => c ≠ 0 ∧ a ≤ |centeredRepR G r c|)).card : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / a ^ 2 :=
  card_filter_nonzero_abs_centeredRepR_ge_le_of_centered_variance_bound G r
    (centered_variance_bound_of_dcEnergyBound G r hdc) ha

/-- Direct representation-function version of the finite Chebyshev consumer:
large deviations of `repR` from its mean are controlled by the centered
variance budget. -/
theorem card_filter_abs_repR_sub_mean_ge_le_of_centered_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c =>
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ B / a ^ 2 := by
  simpa [centeredRepR] using
    card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound G r hvar ha

/-- Tail-count consumer from a direct raw `repR - mean` square-sum bound. -/
theorem card_filter_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c =>
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ B / a ^ 2 := by
  exact card_filter_abs_repR_sub_mean_ge_le_of_centered_variance_bound G r
    (by simpa [centeredRepR] using hvar) ha

/-- Direct representation-function version of the `DCEnergyBound` tail-count
consumer. -/
theorem card_filter_abs_repR_sub_mean_ge_le_of_dcEnergyBound
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) {a : ℝ} (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c =>
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / a ^ 2 := by
  simpa [centeredRepR] using
    card_filter_abs_centeredRepR_ge_le_of_dcEnergyBound G r hdc ha

/-- Direct representation-function version of the nonzero tail-count consumer
from a centered variance budget. -/
theorem card_filter_nonzero_abs_repR_sub_mean_ge_le_of_centered_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => c ≠ 0 ∧
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ B / a ^ 2 := by
  simpa [centeredRepR] using
    card_filter_nonzero_abs_centeredRepR_ge_le_of_centered_variance_bound G r hvar ha

/-- Nonzero tail-count consumer from a direct raw `repR - mean` square-sum
bound. -/
theorem card_filter_nonzero_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ) {B a : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => c ≠ 0 ∧
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ B / a ^ 2 := by
  exact card_filter_nonzero_abs_repR_sub_mean_ge_le_of_centered_variance_bound G r
    (by simpa [centeredRepR] using hvar) ha

/-- Direct representation-function version of the nonzero `DCEnergyBound`
tail-count consumer. -/
theorem card_filter_nonzero_abs_repR_sub_mean_ge_le_of_dcEnergyBound
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) {a : ℝ} (ha : 0 < a) :
    (((Finset.univ : Finset F).filter (fun c => c ≠ 0 ∧
      a ≤ |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)).card : ℝ)
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) / a ^ 2 := by
  simpa [centeredRepR] using
    card_filter_nonzero_abs_centeredRepR_ge_le_of_dcEnergyBound G r hdc ha

/-- A global centered variance bound controls every individual offset, without
using multiplicative orbit structure.  The orbit lemmas below improve this by
`/ |G|` for nonzero offsets when `G` is subgroup-shaped. -/
theorem centered_sq_le_of_centered_variance_bound_global (G : Finset F) (r : ℕ)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (c : F) :
    (centeredRepR G r c) ^ 2 ≤ B := by
  calc (centeredRepR G r c) ^ 2
      = ∑ x ∈ ({c} : Finset F), (centeredRepR G r x) ^ 2 := by simp
    _ ≤ ∑ x : F, (centeredRepR G r x) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun x _ _ => sq_nonneg _)
    _ ≤ B := hvar

/-- Absolute-value form of the global centered variance consumer. -/
theorem abs_centeredRepR_le_sqrt_of_centered_variance_bound_global (G : Finset F) (r : ℕ)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (c : F) :
    |centeredRepR G r c| ≤ Real.sqrt B := by
  calc |centeredRepR G r c| = Real.sqrt ((centeredRepR G r c) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt B :=
        Real.sqrt_le_sqrt (centered_sq_le_of_centered_variance_bound_global G r hvar c)

/-- Direct representation-function version of the global pointwise square
bound from a centered variance budget, with no subgroup hypothesis. -/
theorem repR_sub_mean_sq_le_of_centered_variance_bound_global
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (c : F) :
    ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B := by
  simpa [centeredRepR] using
    centered_sq_le_of_centered_variance_bound_global G r hvar c

/-- Direct representation-function global pointwise square bound from a raw
`repR - mean` square-sum budget. -/
theorem repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound_global
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (c : F) :
    ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B := by
  exact repR_sub_mean_sq_le_of_centered_variance_bound_global G r
    (by simpa [centeredRepR] using hvar) c

/-- Direct representation-function absolute-value form of the global
pointwise bound from a centered variance budget. -/
theorem abs_repR_sub_mean_le_sqrt_of_centered_variance_bound_global
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) (c : F) :
    |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ Real.sqrt B := by
  simpa [centeredRepR] using
    abs_centeredRepR_le_sqrt_of_centered_variance_bound_global G r hvar c

/-- Direct representation-function global absolute-value pointwise bound from
a raw `repR - mean` square-sum budget. -/
theorem abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound_global
    (G : Finset F) (r : ℕ) {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (c : F) :
    |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ Real.sqrt B := by
  exact abs_repR_sub_mean_le_sqrt_of_centered_variance_bound_global G r
    (by simpa [centeredRepR] using hvar) c

/-- `DCEnergyBound` controls every individual centered offset, without using
multiplicative orbit structure. -/
theorem centered_sq_le_of_dcEnergyBound_global (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) (c : F) :
    (centeredRepR G r c) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  exact centered_sq_le_of_centered_variance_bound_global G r
    (centered_variance_bound_of_dcEnergyBound G r hdc) c

/-- Absolute-value global pointwise bound from `DCEnergyBound`. -/
theorem abs_centeredRepR_le_sqrt_of_dcEnergyBound_global (G : Finset F) (r : ℕ)
    (hdc : DCEnergyBound G r) (c : F) :
    |centeredRepR G r c|
      ≤ Real.sqrt ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  exact abs_centeredRepR_le_sqrt_of_centered_variance_bound_global G r
    (centered_variance_bound_of_dcEnergyBound G r hdc) c

/-- Direct representation-function version of the global pointwise square
bound from `DCEnergyBound`, with no subgroup hypothesis. -/
theorem repR_sub_mean_sq_le_of_dcEnergyBound_global
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) (c : F) :
    ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  simpa [centeredRepR] using
    centered_sq_le_of_dcEnergyBound_global G r hdc c

/-- Direct representation-function absolute-value global pointwise bound from
`DCEnergyBound`, with no subgroup hypothesis. -/
theorem abs_repR_sub_mean_le_sqrt_of_dcEnergyBound_global
    (G : Finset F) (r : ℕ) (hdc : DCEnergyBound G r) (c : F) :
    |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      ≤ Real.sqrt ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  simpa [centeredRepR] using
    abs_centeredRepR_le_sqrt_of_dcEnergyBound_global G r hdc c

/-- Centered orbit budget from a centered variance hypothesis. -/
theorem centered_orbit_budget_of_centered_variance_bound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (centeredRepR G r b) ^ 2 ≤ B := by
  calc (G.card : ℝ) * (centeredRepR G r b) ^ 2
      ≤ ∑ c : F, (centeredRepR G r c) ^ 2 :=
        centered_deficit_ge_orbit G r hmul hinv h0 hb
    _ ≤ B := hvar

/-- Direct representation-function orbit budget from a centered variance
hypothesis. -/
theorem repR_sub_mean_orbit_budget_of_centered_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ)
        * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ B := by
  simpa [centeredRepR] using
    centered_orbit_budget_of_centered_variance_bound G r hmul hinv h0 hvar hb

/-- Direct representation-function orbit budget from a raw `repR - mean`
square-sum bound. -/
theorem repR_sub_mean_orbit_budget_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ)
        * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ B := by
  exact repR_sub_mean_orbit_budget_of_centered_variance_bound G r hmul hinv h0
    (by simpa [centeredRepR] using hvar) hb

/-- Exact fixed-fiber obstruction to a centered variance budget, in direct
`repR - mean` language. -/
theorem not_centered_variance_bound_of_repR_sub_mean_orbit_budget_gt
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B : ℝ} {b : F} (hb : b ≠ 0)
    (hbudget :
      B < (G.card : ℝ)
          * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B := by
  intro hvar
  have hle := repR_sub_mean_orbit_budget_of_centered_variance_bound
    G r hmul hinv h0 hvar hb
  exact not_le_of_gt hbudget hle

/-- Exact fixed-fiber obstruction to a raw `repR - mean` variance budget. -/
theorem not_repR_sub_mean_variance_bound_of_orbit_budget_gt
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B : ℝ} {b : F} (hb : b ≠ 0)
    (hbudget :
      B < (G.card : ℝ)
          * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B := by
  intro hvar
  have hle := repR_sub_mean_orbit_budget_of_repR_sub_mean_variance_bound
    G r hmul hinv h0 hvar hb
  exact not_le_of_gt hbudget hle

/-- A single large nonzero centered offset forces an entire multiplicative
orbit of variance. -/
theorem orbit_budget_of_large_abs_centeredRepR
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B a : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0) (hlarge : a ≤ |centeredRepR G r b|) :
    (G.card : ℝ) * a ^ 2 ≤ B := by
  have hsqa : a ^ 2 ≤ (centeredRepR G r b) ^ 2 := by
    have hsq := pow_le_pow_left₀ ha_nonneg hlarge 2
    rwa [sq_abs] at hsq
  calc (G.card : ℝ) * a ^ 2
      ≤ (G.card : ℝ) * (centeredRepR G r b) ^ 2 :=
        mul_le_mul_of_nonneg_left hsqa (by positivity)
    _ ≤ B :=
        centered_orbit_budget_of_centered_variance_bound G r hmul hinv h0 hvar hb

/-- Under `DCEnergyBound`, a single large nonzero centered offset must fit the
Wick orbit budget. -/
theorem orbit_budget_of_large_abs_centeredRepR_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0) (hlarge : a ≤ |centeredRepR G r b|) :
    (G.card : ℝ) * a ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  exact orbit_budget_of_large_abs_centeredRepR G r hmul hinv h0
    (centered_variance_bound_of_dcEnergyBound G r hdc) ha_nonneg hb hlarge

/-- Contrapositive obstruction form: a single too-large nonzero centered
offset refutes `DCEnergyBound`. -/
theorem not_dcEnergyBound_of_large_abs_centeredRepR
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0) (hlarge : a ≤ |centeredRepR G r b|)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < (G.card : ℝ) * a ^ 2) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := orbit_budget_of_large_abs_centeredRepR_of_dcEnergyBound
    G r hmul hinv h0 hdc ha_nonneg hb hlarge
  exact not_le_of_gt hbudget hle

/-- Exclusion form: under `DCEnergyBound`, no nonzero centered offset can exceed
a threshold whose orbit cost is above the Wick budget. -/
theorem no_large_abs_centeredRepR_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < (G.card : ℝ) * a ^ 2) :
    ¬ ∃ b : F, b ≠ 0 ∧ a ≤ |centeredRepR G r b| := by
  rintro ⟨b, hb, hlarge⟩
  exact not_dcEnergyBound_of_large_abs_centeredRepR
    G r hmul hinv h0 ha_nonneg hb hlarge hbudget hdc

/-- Direct representation-function version of the orbit budget: one large
nonzero deviation of `repR` from its mean costs a full multiplicative orbit. -/
theorem orbit_budget_of_large_abs_repR_sub_mean
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B a : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0)
    (hlarge : a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|) :
    (G.card : ℝ) * a ^ 2 ≤ B :=
  orbit_budget_of_large_abs_centeredRepR G r hmul hinv h0 hvar ha_nonneg hb
    (by simpa [centeredRepR] using hlarge)

/-- Direct representation-function orbit budget from a raw `repR - mean`
square-sum bound. -/
theorem orbit_budget_of_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B a : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0)
    (hlarge : a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|) :
    (G.card : ℝ) * a ^ 2 ≤ B :=
  orbit_budget_of_large_abs_repR_sub_mean G r hmul hinv h0
    (by simpa [centeredRepR] using hvar) ha_nonneg hb hlarge

/-- Exclusion form from a raw `repR - mean` square-sum budget: if the orbit
cost of threshold `a` exceeds the raw variance budget `B`, then no nonzero
fiber can have raw deviation at least `a`. -/
theorem no_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B a : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    (ha_nonneg : 0 ≤ a)
    (hbudget : B < (G.card : ℝ) * a ^ 2) :
    ¬ ∃ b : F, b ≠ 0 ∧
      a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| := by
  rintro ⟨b, hb, hlarge⟩
  have hle := orbit_budget_of_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
    G r hmul hinv h0 hvar ha_nonneg hb hlarge
  exact not_le_of_gt hbudget hle

/-- Exclusion form from a centered variance budget in direct `repR - mean`
language. -/
theorem no_large_abs_repR_sub_mean_of_centered_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {B a : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    (ha_nonneg : 0 ≤ a)
    (hbudget : B < (G.card : ℝ) * a ^ 2) :
    ¬ ∃ b : F, b ≠ 0 ∧
      a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| := by
  rintro ⟨b, hb, hlarge⟩
  have hle := orbit_budget_of_large_abs_repR_sub_mean
    G r hmul hinv h0 hvar ha_nonneg hb hlarge
  exact not_le_of_gt hbudget hle

/-- Direct representation-function version of the orbit budget under
`DCEnergyBound`. -/
theorem orbit_budget_of_large_abs_repR_sub_mean_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0)
    (hlarge : a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|) :
    (G.card : ℝ) * a ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  orbit_budget_of_large_abs_centeredRepR_of_dcEnergyBound G r hmul hinv h0 hdc ha_nonneg hb
    (by simpa [centeredRepR] using hlarge)

/-- Direct representation-function obstruction form: a single too-large
nonzero deviation of `repR` from its mean refutes `DCEnergyBound`. -/
theorem not_dcEnergyBound_of_large_abs_repR_sub_mean
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    {b : F} (hb : b ≠ 0)
    (hlarge : a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < (G.card : ℝ) * a ^ 2) :
    ¬ DCEnergyBound G r :=
  not_dcEnergyBound_of_large_abs_centeredRepR G r hmul hinv h0 ha_nonneg hb
    (by simpa [centeredRepR] using hlarge) hbudget

/-- Direct representation-function exclusion form: under `DCEnergyBound`, no
nonzero `repR` fiber can exceed a threshold whose orbit cost is above the Wick
budget. -/
theorem no_large_abs_repR_sub_mean_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < (G.card : ℝ) * a ^ 2) :
    ¬ ∃ b : F, b ≠ 0 ∧
      a ≤ |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| := by
  rintro ⟨b, hb, hlarge⟩
  exact not_dcEnergyBound_of_large_abs_repR_sub_mean
    G r hmul hinv h0 ha_nonneg hb hlarge hbudget hdc

/-- Divided centered pointwise budget from a centered variance hypothesis,
exposing the `/ |G|` orbit saving. -/
theorem centered_sq_le_of_centered_variance_bound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    (centeredRepR G r b) ^ 2 ≤ B / (G.card : ℝ) := by
  have hbudget := centered_orbit_budget_of_centered_variance_bound G r hmul hinv h0 hvar hb
  have hcard_pos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGpos
  have hbudget' :
      (centeredRepR G r b) ^ 2 * (G.card : ℝ) ≤ B := by
    simpa [mul_comm] using hbudget
  exact (le_div_iff₀ hcard_pos).mpr hbudget'

/-- Absolute-value form of the centered orbit-saved pointwise budget. -/
theorem abs_centeredRepR_le_sqrt_of_centered_variance_bound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    |centeredRepR G r b| ≤ Real.sqrt (B / (G.card : ℝ)) := by
  calc |centeredRepR G r b| = Real.sqrt ((centeredRepR G r b) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (B / (G.card : ℝ)) :=
        Real.sqrt_le_sqrt
          (centered_sq_le_of_centered_variance_bound G r hmul hinv h0 hGpos hvar hb)

/-- Centered orbit budget from `DCEnergyBound`. -/
theorem centered_orbit_budget_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ) * (centeredRepR G r b) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  exact centered_orbit_budget_of_centered_variance_bound G r hmul hinv h0
    (centered_variance_bound_of_dcEnergyBound G r hdc) hb

/-- Direct representation-function orbit budget from `DCEnergyBound`. -/
theorem repR_sub_mean_orbit_budget_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (G.card : ℝ)
        * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  exact repR_sub_mean_orbit_budget_of_centered_variance_bound G r hmul hinv h0
    (centered_variance_bound_of_dcEnergyBound G r hdc) hb

/-- Exact fixed-fiber obstruction to `DCEnergyBound`, in direct
`repR - mean` language. -/
theorem not_dcEnergyBound_of_repR_sub_mean_orbit_budget_gt
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {b : F} (hb : b ≠ 0)
    (hbudget :
      (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        < (G.card : ℝ)
          * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :
    ¬ DCEnergyBound G r := by
  intro hdc
  have hle := repR_sub_mean_orbit_budget_of_dcEnergyBound G r hmul hinv h0 hdc hb
  exact not_le_of_gt hbudget hle

/-- Divided centered pointwise budget, exposing the `/ |G|` saving on the
probability-scale representation function. -/
theorem centered_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    (centeredRepR G r b) ^ 2
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ) := by
  exact centered_sq_le_of_centered_variance_bound G r hmul hinv h0 hGpos
    (centered_variance_bound_of_dcEnergyBound G r hdc) hb

/-- Direct representation-function square bound from a centered variance
hypothesis, exposing the `/ |G|` orbit saving without unfolding
`centeredRepR` at the call site. -/
theorem repR_sub_mean_sq_le_of_centered_variance_bound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ B / (G.card : ℝ) := by
  simpa [centeredRepR] using
    centered_sq_le_of_centered_variance_bound G r hmul hinv h0 hGpos hvar hb

/-- Direct representation-function absolute-value bound from a centered
variance hypothesis, exposing the `/ |G|` orbit saving without unfolding
`centeredRepR` at the call site. -/
theorem abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      ≤ Real.sqrt (B / (G.card : ℝ)) := by
  calc |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      = Real.sqrt (((repR G r b : ℝ)
          - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (B / (G.card : ℝ)) :=
        Real.sqrt_le_sqrt
          (repR_sub_mean_sq_le_of_centered_variance_bound G r
            hmul hinv h0 hGpos hvar hb)

/-- Direct representation-function square bound from a raw `repR - mean`
square-sum budget, exposing the `/ |G|` orbit saving. -/
theorem repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ B / (G.card : ℝ) := by
  exact repR_sub_mean_sq_le_of_centered_variance_bound G r hmul hinv h0 hGpos
    (by simpa [centeredRepR] using hvar) hb

/-- Direct representation-function square bound from `DCEnergyBound`, exposing
the `/ |G|` orbit saving. -/
theorem repR_sub_mean_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ) := by
  simpa [centeredRepR] using
    centered_sq_le_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- Absolute-value form of the centered `/ |G|` pointwise budget from
`DCEnergyBound`. -/
theorem abs_centeredRepR_le_sqrt_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    |centeredRepR G r b|
      ≤ Real.sqrt (((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ)) := by
  exact abs_centeredRepR_le_sqrt_of_centered_variance_bound G r hmul hinv h0 hGpos
    (centered_variance_bound_of_dcEnergyBound G r hdc) hb

/-- Absolute-value form of the raw `repR - mean` orbit-saved pointwise budget
from a raw square-sum hypothesis. -/
theorem abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B)
    {b : F} (hb : b ≠ 0) :
    |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      ≤ Real.sqrt (B / (G.card : ℝ)) := by
  calc |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      = Real.sqrt (((repR G r b : ℝ)
          - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (B / (G.card : ℝ)) :=
        Real.sqrt_le_sqrt
          (repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound G r
            hmul hinv h0 hGpos hvar hb)

/-- Uniform nonzero-offset square bound from `DCEnergyBound`, in centered
probability-scale language. -/
theorem forall_nonzero_centered_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r) :
    ∀ b : F, b ≠ 0 →
      (centeredRepR G r b) ^ 2
        ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
            / (G.card : ℝ) := by
  intro b hb
  exact centered_sq_le_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- Uniform nonzero-offset absolute bound from a centered variance hypothesis,
in direct representation-function language. -/
theorem forall_nonzero_abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ} (hvar : ∑ c : F, (centeredRepR G r c) ^ 2 ≤ B) :
    ∀ b : F, b ≠ 0 →
      |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
        ≤ Real.sqrt (B / (G.card : ℝ)) := by
  intro b hb
  exact abs_repR_sub_mean_le_sqrt_of_centered_variance_bound G r
    hmul hinv h0 hGpos hvar hb

/-- Uniform nonzero-offset square bound from a raw `repR - mean` square-sum
hypothesis, in direct representation-function language. -/
theorem forall_nonzero_repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B) :
    ∀ b : F, b ≠ 0 →
      ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
        ≤ B / (G.card : ℝ) := by
  intro b hb
  exact repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound G r
    hmul hinv h0 hGpos hvar hb

/-- Uniform nonzero-offset square bound from `DCEnergyBound`, in direct
representation-function language. -/
theorem forall_nonzero_repR_sub_mean_sq_le_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r) :
    ∀ b : F, b ≠ 0 →
      ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
        ≤ ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
            / (G.card : ℝ) := by
  intro b hb
  exact repR_sub_mean_sq_le_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- Uniform nonzero-offset raw orbit budget from `DCEnergyBound`. -/
theorem forall_nonzero_repR_sub_mean_orbit_budget_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hdc : DCEnergyBound G r) :
    ∀ b : F, b ≠ 0 →
      (G.card : ℝ)
          * ((repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  intro b hb
  exact repR_sub_mean_orbit_budget_of_dcEnergyBound G r hmul hinv h0 hdc hb

/-- Uniform nonzero-offset absolute bound from `DCEnergyBound`, in centered
probability-scale language. -/
theorem forall_nonzero_abs_centeredRepR_le_sqrt_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r) :
    ∀ b : F, b ≠ 0 →
      |centeredRepR G r b|
        ≤ Real.sqrt (((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
            / (G.card : ℝ)) := by
  intro b hb
  exact abs_centeredRepR_le_sqrt_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- Uniform nonzero-offset absolute bound from a raw `repR - mean` square-sum
hypothesis, in direct representation-function language. -/
theorem forall_nonzero_abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    {B : ℝ}
    (hvar : ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ B) :
    ∀ b : F, b ≠ 0 →
      |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
        ≤ Real.sqrt (B / (G.card : ℝ)) := by
  intro b hb
  exact abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound G r
    hmul hinv h0 hGpos hvar hb

/-- The nonzero orbit-saved flatness bound in direct representation-function
language: `repR(c)` is close to its flat mean `|G|^r / q`. -/
theorem abs_repR_sub_mean_le_sqrt_of_dcEnergyBound (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r)
    {b : F} (hb : b ≠ 0) :
    |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      ≤ Real.sqrt (((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          / (G.card : ℝ)) := by
  simpa [centeredRepR] using
    abs_centeredRepR_le_sqrt_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- Uniform nonzero orbit-saved flatness in direct representation-function
language. -/
theorem forall_nonzero_abs_repR_sub_mean_le_sqrt_of_dcEnergyBound
    (G : Finset F) (r : ℕ)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hdc : DCEnergyBound G r) :
    ∀ b : F, b ≠ 0 →
      |(repR G r b : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
        ≤ Real.sqrt (((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
            / (G.card : ℝ)) := by
  intro b hb
  exact abs_repR_sub_mean_le_sqrt_of_dcEnergyBound G r hmul hinv h0 hGpos hdc hb

/-- A uniform absolute flatness bound on the centered representation controls
the centered variance by `q * A^2`. -/
theorem centered_variance_bound_of_uniform_abs_centeredRepR (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, |centeredRepR G r c| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) * A ^ 2 := by
  calc ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ ∑ _c : F, A ^ 2 := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        have hAc := hA c
        nlinarith [sq_abs (centeredRepR G r c), abs_nonneg (centeredRepR G r c)]
    _ = (Fintype.card F : ℝ) * A ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Uniform absolute flatness implies `DCEnergyBound` once its square budget
fits the Wick variance budget. -/
theorem dcEnergyBound_of_uniform_abs_centeredRepR (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, |centeredRepR G r c| ≤ A)
    (hbudget : (Fintype.card F : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_centered_variance G r
    ((centered_variance_bound_of_uniform_abs_centeredRepR G r hA).trans hbudget)

/-- Uniform representation-function flatness controls centered variance. -/
theorem centered_variance_bound_of_uniform_abs_repR_sub_mean (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F,
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (Fintype.card F : ℝ) * A ^ 2 := by
  exact centered_variance_bound_of_uniform_abs_centeredRepR G r (fun c => by
    simpa [centeredRepR] using hA c)

/-- Uniform representation-function flatness controls the raw `repR - mean`
variance by `q * A^2`. -/
theorem repR_sub_mean_variance_bound_of_uniform_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F,
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (Fintype.card F : ℝ) * A ^ 2 := by
  simpa [centeredRepR] using
    centered_variance_bound_of_uniform_abs_repR_sub_mean G r hA

/-- Uniform representation-function flatness implies `DCEnergyBound` once its
square budget fits the Wick variance budget. -/
theorem dcEnergyBound_of_uniform_abs_repR_sub_mean (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F,
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A)
    (hbudget : (Fintype.card F : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_repR_sub_mean_variance G r
    ((repR_sub_mean_variance_bound_of_uniform_abs_repR_sub_mean G r hA).trans hbudget)

/-- A zero/nonzero split for centered flatness: control the zero offset by `Z`
and all nonzero offsets by a uniform absolute bound `A`. -/
theorem centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR
    (G : Finset F) (r : ℕ) {Z A : ℝ}
    (hzero : (centeredRepR G r 0) ^ 2 ≤ Z)
    (hA : ∀ c : F, c ≠ 0 → |centeredRepR G r c| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ Z + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 := by
  rw [← Finset.add_sum_erase Finset.univ (fun c => (centeredRepR G r c) ^ 2)
    (Finset.mem_univ (0 : F))]
  apply add_le_add hzero
  calc ∑ c ∈ (Finset.univ : Finset F).erase 0, (centeredRepR G r c) ^ 2
      ≤ ∑ _c ∈ (Finset.univ : Finset F).erase 0, A ^ 2 := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        have hc0 : c ≠ 0 := Finset.ne_of_mem_erase hc
        have hAc := hA c hc0
        nlinarith [sq_abs (centeredRepR G r c), abs_nonneg (centeredRepR G r c)]
    _ = ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
          Finset.card_univ, nsmul_eq_mul]

/-- The zero/nonzero centered flatness split implies `DCEnergyBound` when its
variance budget fits the Wick bound. -/
theorem dcEnergyBound_of_zero_and_nonzero_abs_centeredRepR
    (G : Finset F) (r : ℕ) {Z A : ℝ}
    (hzero : (centeredRepR G r 0) ^ 2 ≤ Z)
    (hA : ∀ c : F, c ≠ 0 → |centeredRepR G r c| ≤ A)
    (hbudget : Z + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_centered_variance G r
    ((centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR G r hzero hA).trans hbudget)

/-- Direct representation-function version of the zero/nonzero split: control
the zero fiber's deviation from its mean by `Z` and all nonzero fibers by a
uniform bound `A`. -/
theorem centered_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {Z A : ℝ}
    (hzero :
      ((repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ Z)
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ Z + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 :=
  centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR G r
    (by simpa [centeredRepR] using hzero)
    (fun c hc => by simpa [centeredRepR] using hA c hc)

/-- Direct raw `repR - mean` variance version of the zero/nonzero split. -/
theorem repR_sub_mean_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {Z A : ℝ}
    (hzero :
      ((repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ Z)
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ Z + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 := by
  simpa [centeredRepR] using
    centered_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean G r hzero hA

/-- Direct representation-function version of the zero/nonzero split route to
`DCEnergyBound`. -/
theorem dcEnergyBound_of_zero_and_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {Z A : ℝ}
    (hzero :
      ((repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2 ≤ Z)
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A)
    (hbudget : Z + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_repR_sub_mean_variance G r
    ((repR_sub_mean_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean G r hzero hA).trans
      hbudget)

/-- A nonzero-offset uniform absolute bound also controls the zero offset,
because the centered representation is mean-zero. -/
theorem abs_centeredRepR_zero_le_card_sub_one_mul_of_nonzero_abs
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 → |centeredRepR G r c| ≤ A) :
    |centeredRepR G r 0|
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * A := by
  have hsum := sum_centeredRepR_zero G r
  rw [← Finset.add_sum_erase Finset.univ (fun c => centeredRepR G r c)
    (Finset.mem_univ (0 : F))] at hsum
  have hzeroeq :
      centeredRepR G r 0
        = -∑ c ∈ (Finset.univ : Finset F).erase 0, centeredRepR G r c := by
    linarith
  calc |centeredRepR G r 0|
      = |∑ c ∈ (Finset.univ : Finset F).erase 0, centeredRepR G r c| := by
        rw [hzeroeq, abs_neg]
    _ ≤ ∑ c ∈ (Finset.univ : Finset F).erase 0, |centeredRepR G r c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ (Finset.univ : Finset F).erase 0, A := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        exact hA c (Finset.ne_of_mem_erase hc)
    _ = ((Fintype.card F - 1 : ℕ) : ℝ) * A := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
          Finset.card_univ, nsmul_eq_mul]

/-- Direct representation-function version: a nonzero-only raw deviation
bound controls the zero fiber's raw deviation by mean-zero. -/
theorem abs_repR_sub_mean_zero_le_card_sub_one_mul_of_nonzero_abs
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    |(repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)|
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * A := by
  simpa [centeredRepR] using
    abs_centeredRepR_zero_le_card_sub_one_mul_of_nonzero_abs G r
      (fun c hc => by simpa [centeredRepR] using hA c hc)

/-- Squared form of the raw zero-fiber control from nonzero raw deviations. -/
theorem repR_sub_mean_zero_sq_le_card_sub_one_mul_sq_of_nonzero_abs
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ((repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2 := by
  have hzero_abs := abs_repR_sub_mean_zero_le_card_sub_one_mul_of_nonzero_abs G r hA
  nlinarith [sq_abs ((repR G r 0 : ℝ)
    - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)),
    abs_nonneg ((repR G r 0 : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ))]

/-- A nonzero-only uniform absolute bound controls the whole centered
variance, with the zero offset paid for by mean-zero. -/
theorem centered_variance_bound_of_nonzero_abs_centeredRepR
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 → |centeredRepR G r c| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2
        + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 := by
  have hzero_abs := abs_centeredRepR_zero_le_card_sub_one_mul_of_nonzero_abs G r hA
  have hzero :
      (centeredRepR G r 0) ^ 2 ≤ (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2 := by
    nlinarith [sq_abs (centeredRepR G r 0), abs_nonneg (centeredRepR G r 0)]
  exact centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR G r hzero hA

/-- The nonzero-only centered flatness route to `DCEnergyBound`. -/
theorem dcEnergyBound_of_nonzero_abs_centeredRepR
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 → |centeredRepR G r c| ≤ A)
    (hbudget : (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2
        + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_centered_variance G r
    ((centered_variance_bound_of_nonzero_abs_centeredRepR G r hA).trans hbudget)

/-- Direct representation-function version of the nonzero-only sup-norm
consumer.  The zero offset is paid for by the centered mean-zero identity. -/
theorem centered_variance_bound_of_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F, (centeredRepR G r c) ^ 2
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2
        + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 :=
  centered_variance_bound_of_nonzero_abs_centeredRepR G r
    (fun c hc => by simpa [centeredRepR] using hA c hc)

/-- Direct raw `repR - mean` variance version of the nonzero-only sup-norm
consumer.  The zero offset is paid for by the centered mean-zero identity. -/
theorem repR_sub_mean_variance_bound_of_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A) :
    ∑ c : F,
        ((repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)) ^ 2
      ≤ (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2
        + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2 := by
  simpa [centeredRepR] using
    centered_variance_bound_of_nonzero_abs_repR_sub_mean G r hA

/-- Direct representation-function version of the nonzero-only route to
`DCEnergyBound`. -/
theorem dcEnergyBound_of_nonzero_abs_repR_sub_mean
    (G : Finset F) (r : ℕ) {A : ℝ}
    (hA : ∀ c : F, c ≠ 0 →
      |(repR G r c : ℝ) - (G.card : ℝ) ^ r / (Fintype.card F : ℝ)| ≤ A)
    (hbudget : (((Fintype.card F - 1 : ℕ) : ℝ) * A) ^ 2
        + ((Fintype.card F - 1 : ℕ) : ℝ) * A ^ 2
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :
    DCEnergyBound G r :=
  dcEnergyBound_of_repR_sub_mean_variance G r
    ((repR_sub_mean_variance_bound_of_nonzero_abs_repR_sub_mean G r hA).trans hbudget)

end ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_vectors_weight
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_repR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.rEnergy_eq_sum_repR_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.variance_identity
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dc_floor
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_dcGap_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_dcGap_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcGap_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_dcGap_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_dcGap_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_one_iff
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_one_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_dcEnergyBoundWithConstant_one
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_iff_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_iff_forall_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_iff_forall_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_iff_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWall_iff_forall_sum_nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_sum_nonzero_moment_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_sum_nonzero_moment_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_sum_nonzero_moment_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_pow_le_of_dcEnergyBoundWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_sq_le_dcOptimizedWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_le_sqrt_floor_of_dcEnergyBoundWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_le_sqrt_floor_of_dcEnergyWallWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_dcEnergyWallWithConstantUpTo
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_dcEnergyCeilWallWithConstant
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_sum_nonzero_moment_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_eta_le_sqrt_floor_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyBoundWithConstant.mono_pow
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyBoundWithConstant.mono
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_of_dcEnergyBound_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_one_iff
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstant.mono_pow
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstant.mono
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_of_dcEnergyWall_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstant.to_upTo
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstantUpTo.mono_depth
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstantUpTo.mono_pow
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstant.to_ceil
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyWallWithConstantUpTo.to_ceil
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_one_iff
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyCeilWallWithConstant.mono_pow
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.DCEnergyCeilWallWithConstant.mono
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_of_dcEnergyBound_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_one_iff
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_of_dcEnergyWallUpTo_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.variance_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_deviationR_sq_eq_card_mul_dcGap
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcGap_eq_sum_deviationR_sq_div_card
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centeredRepR_eq_deviation_div
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviationR_eq_card_mul_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviationR_sq_eq_card_sq_mul_centeredRepR_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_deviationR_eq_card_mul_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centeredRepR_eq_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centeredRepR_sq_eq_repR_sub_mean_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_eq_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_deviationR_zero
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_centeredRepR_zero
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_repR_sub_mean_zero
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_centeredRepR_sq_eq_normalized_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_repR_sub_mean_sq_eq_normalized_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_deviationR_sq_eq_card_sq_mul_sum_centeredRepR_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_deviationR_sq_eq_card_sq_mul_sum_repR_sub_mean_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcGap_eq_card_mul_sum_centeredRepR_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcGap_eq_card_mul_sum_repR_sub_mean_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_iff_centeredRepR_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_iff_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_variance_bound_iff_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_variance_bound_iff_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_iff_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_iff_centeredRepR_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_iff_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_iff_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyCeilWallWithConstant_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_iff_forall_centeredRepR_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_iff_forall_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstant_iff_forall_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_iff_forall_centeredRepR_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_iff_forall_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyWallWithConstantUpTo_iff_forall_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_centered_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_centered_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_repR_sub_mean_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstant_of_deviation_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_centered_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_centered_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_repR_sub_mean_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyWallWithConstantUpTo_of_deviation_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_centered_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_centered_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_repR_sub_mean_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyCeilWallWithConstant_of_deviation_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_deviation_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_deviation_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBoundWithConstant_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_centered_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_centered_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBoundWithConstant_of_repR_sub_mean_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_variance_bound_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_bound_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_variance_bound_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.sum_centeredRepR_sq_eq_sum_repR_sub_mean_sq
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_iff_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_smul
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.varianceSummand_smul
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviationR_smul
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centeredRepR_smul
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_smul
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deficit_ge_orbit
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_deficit_ge_orbit
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_ge_orbit
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.energy_ge_orbit
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_deviation_budget_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.normalized_deviation_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.normalized_variance_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_normalized_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_centeredRepR_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_deviation_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_deviation_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.deviation_variance_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_deviation_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_deviation_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_centered_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_centered_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_centered_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_iff_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_bound_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_repR_sub_mean_variance
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_repR_sub_mean_variance_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_repR_sub_mean_variance_lower_bound_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_centeredRepR_ge_le_variance_div
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_centeredRepR_ge_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_centeredRepR_ge_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_nonzero_abs_centeredRepR_ge_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_nonzero_abs_centeredRepR_ge_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_repR_sub_mean_ge_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_abs_repR_sub_mean_ge_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_nonzero_abs_repR_sub_mean_ge_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_nonzero_abs_repR_sub_mean_ge_le_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.card_filter_nonzero_abs_repR_sub_mean_ge_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_sq_le_of_centered_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_le_sqrt_of_centered_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_centered_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_centered_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_sq_le_of_dcEnergyBound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_le_sqrt_of_dcEnergyBound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_dcEnergyBound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_dcEnergyBound_global
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_orbit_budget_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_orbit_budget_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_orbit_budget_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_centered_variance_bound_of_repR_sub_mean_orbit_budget_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_repR_sub_mean_variance_bound_of_orbit_budget_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_budget_of_large_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_budget_of_large_abs_centeredRepR_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_large_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.no_large_abs_centeredRepR_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_budget_of_large_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_budget_of_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.no_large_abs_repR_sub_mean_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.no_large_abs_repR_sub_mean_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.orbit_budget_of_large_abs_repR_sub_mean_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_large_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.no_large_abs_repR_sub_mean_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_sq_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_le_sqrt_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_orbit_budget_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_le_sqrt_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_centered_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_abs_repR_sub_mean_le_sqrt_of_centered_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_repR_sub_mean_sq_le_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_repR_sub_mean_sq_le_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_orbit_budget_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.not_dcEnergyBound_of_repR_sub_mean_orbit_budget_gt
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_repR_sub_mean_orbit_budget_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_abs_centeredRepR_le_sqrt_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_abs_repR_sub_mean_le_sqrt_of_repR_sub_mean_variance_bound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_le_sqrt_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.forall_nonzero_abs_repR_sub_mean_le_sqrt_of_dcEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_uniform_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_uniform_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_uniform_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_bound_of_uniform_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_uniform_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_zero_and_nonzero_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_zero_and_nonzero_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_bound_of_zero_and_nonzero_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_zero_and_nonzero_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_centeredRepR_zero_le_card_sub_one_mul_of_nonzero_abs
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.abs_repR_sub_mean_zero_le_card_sub_one_mul_of_nonzero_abs
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_zero_sq_le_card_sub_one_mul_sq_of_nonzero_abs
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_nonzero_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_nonzero_abs_centeredRepR
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.centered_variance_bound_of_nonzero_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.repR_sub_mean_variance_bound_of_nonzero_abs_repR_sub_mean
#print axioms ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance.dcEnergyBound_of_nonzero_abs_repR_sub_mean
