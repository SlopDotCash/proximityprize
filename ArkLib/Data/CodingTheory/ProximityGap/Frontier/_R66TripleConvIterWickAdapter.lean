/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30IterConvEnergyRecursion

/-!
# LANE B2 (#466 round 66): the r = 3 adapter between R23 and the full tower

R23 names the calibrated sextic core as `TripleConvEnergyBound`, while R27/R30 name the
full ladder as `IterConvEnergyWick`.  This file records the exact r = 3 identification and
the corresponding constant conversion.  It is bookkeeping, but useful bookkeeping: any future
proof of the calibrated r = 3 input can now be fed into the full-tower interface without
unfolding the convolution definitions again.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter

open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

variable {m : ℕ} [NeZero m]

/-- The first iterated convolution is the coefficient sequence on nonzero indices, and vanishes
at zero. -/
theorem iterConv_one_eq (J : ZMod m → ℂ) (c : ZMod m) :
    iterConv J 1 c = if c = 0 then 0 else J c := by
  classical
  simp only [iterConv]
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro b hb hbc
      simp only [ite_mul, one_mul, zero_mul]
      by_cases hcb : c - b = 0
      · have hbc' : b = c := (sub_eq_zero.mp hcb).symm
        exact (hbc hbc').elim
      · simp [hcb]
    · intro hc_mem
      exact (hc_mem (by simp [hc])).elim

/-- The second iterated convolution is R21's punctured self-convolution. -/
theorem iterConv_two_eq_selfConv (J : ZMod m → ℂ) (c : ZMod m) :
    iterConv J 2 c = selfConv J c := by
  classical
  unfold selfConv
  change (∑ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J 1 (c - j) * J j)
      = ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0),
          J j * J (c - j)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [iterConv_one_eq]
  by_cases hcj : c - j = 0
  · simp [hcj]
  · simp [hcj, mul_comm]

/-- R23's `tripleConv` is exactly R27's third iterated convolution. -/
theorem iterConv_three_eq_tripleConv (J : ZMod m → ℂ) (d : ZMod m) :
    iterConv J 3 d = tripleConv J d := by
  classical
  unfold tripleConv
  change (∑ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J 2 (d - j) * J j)
      = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, selfConv J (d - j) * J j
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [iterConv_two_eq_selfConv]

/-- The calibrated R23 energy bound implies the r = 3 full-tower Wick bound whenever the
R23 constant fits inside the Wick normalization `6*C^3`. -/
theorem iterConvEnergyWick_three_of_tripleConvEnergyBound
    (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q 3 C := by
  classical
  unfold TripleConvEnergyBound at h
  unfold IterConvEnergyWick
  calc ∑ c : ZMod m, ‖iterConv J 3 c‖ ^ 2
      = ∑ c : ZMod m, ‖tripleConv J c‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [iterConv_three_eq_tripleConv]
    _ ≤ B * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := h
    _ ≤ (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)) * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        have hmq : 0 ≤ (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hBC hmq]
    _ = C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 3 := by ring

/-- Conversely, an r = 3 full-tower Wick bound is an R23 triple-convolution bound at the
corresponding constant `6*C^3`. -/
theorem tripleConvEnergyBound_of_iterConvEnergyWick_three
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : IterConvEnergyWick J q 3 C) :
    TripleConvEnergyBound J q (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)) := by
  classical
  unfold IterConvEnergyWick at h
  unfold TripleConvEnergyBound
  calc ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      = ∑ d : ZMod m, ‖iterConv J 3 d‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [iterConv_three_eq_tripleConv]
    _ ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 3 := h
    _ = (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)) * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

/-- Exact r = 3 equivalence between the calibrated R23 bound and the full-tower Wick
normalization. -/
theorem tripleConvEnergyBound_iff_iterConvEnergyWick_three
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ} :
    TripleConvEnergyBound J q (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
      ↔ IterConvEnergyWick J q 3 C := by
  constructor
  · intro h
    exact iterConvEnergyWick_three_of_tripleConvEnergyBound J q (le_rfl) h
  · intro h
    exact tripleConvEnergyBound_of_iterConvEnergyWick_three J q h

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.iterConv_one_eq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.iterConv_two_eq_selfConv
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.iterConv_three_eq_tripleConv
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.iterConvEnergyWick_three_of_tripleConvEnergyBound
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.tripleConvEnergyBound_of_iterConvEnergyWick_three
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter.tripleConvEnergyBound_iff_iterConvEnergyWick_three

end ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
