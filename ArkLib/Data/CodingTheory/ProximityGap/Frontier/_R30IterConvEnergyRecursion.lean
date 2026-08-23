/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R29BaselineToWickBudget

/-!
# LANE B2 (#466 round 30): a one-step energy recursion for the full Jacobi tower

Round 27 made every rung an iterated-convolution energy.  Round 28 gave the full triangle
baseline.  This brick lands the sharper reusable recursion:

  `E_{r+1} ≤ m² q · E_r`, where `E_r = ∑_c ‖J^{∗r}(c)‖²`

assuming only the standard Jacobi-size pointwise input `‖J_j‖² ≤ q`.

The proof is the exact Cauchy-Schwarz mechanism behind the R23 sextic refinement, now for all
rungs.  It is not the prize cancellation by itself — iterating it recovers the R28 baseline —
but it is the right bootstrap interface: any future saving at one rung can be propagated through
the deep tower with explicit loss.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 30, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion

open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

variable {m : ℕ} [NeZero m]

/-- The `L²` energy of the `r`-fold convolution. -/
noncomputable def iterConvEnergy (J : ZMod m → ℂ) (r : ℕ) : ℝ :=
  ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2

/-- **One-step tower recursion.**  If `‖J_j‖² ≤ q`, then
`E_{r+1} ≤ m² q E_r`. -/
theorem iterConvEnergy_succ_le_card_sq_mul (J : ZMod m → ℂ) (q r : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) :
    iterConvEnergy J (r + 1) ≤ iterConvEnergy J r * (m : ℝ) ^ 2 * (q : ℝ) := by
  classical
  let S : Finset (ZMod m) := Finset.univ \ {(0 : ZMod m)}
  have hJsum : ∑ j ∈ S, ‖J j‖ ^ 2 ≤ (m : ℝ) * (q : ℝ) := by
    calc ∑ j ∈ S, ‖J j‖ ^ 2
        ≤ ∑ _j ∈ S, (q : ℝ) := Finset.sum_le_sum (fun j _ => hJ j)
      _ = (S.card : ℝ) * (q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (q : ℝ) := by
          have hcard : (S.card : ℝ) ≤ (m : ℝ) := by
            have hle : S.card ≤ (Finset.univ : Finset (ZMod m)).card :=
              Finset.card_le_card (by intro j _hj; exact Finset.mem_univ j)
            simpa [S, ZMod.card] using (Nat.cast_le.mpr hle : _)
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hpoint : ∀ d : ZMod m,
      ‖iterConv J (r + 1) d‖ ^ 2 ≤ iterConvEnergy J r * ((m : ℝ) * (q : ℝ)) := by
    intro d
    have hnorm : ‖iterConv J (r + 1) d‖
        ≤ ∑ j ∈ S, ‖iterConv J r (d - j)‖ * ‖J j‖ := by
      calc ‖iterConv J (r + 1) d‖
          ≤ ∑ j ∈ S, ‖iterConv J r (d - j) * J j‖ := by
              simp only [iterConv, S]
              exact norm_sum_le _ _
        _ = ∑ j ∈ S, ‖iterConv J r (d - j)‖ * ‖J j‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [norm_mul]
    have hsqnorm :
        ‖iterConv J (r + 1) d‖ ^ 2
          ≤ (∑ j ∈ S, ‖iterConv J r (d - j)‖ * ‖J j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs :
        (∑ j ∈ S, ‖iterConv J r (d - j)‖ * ‖J j‖) ^ 2
          ≤ (∑ j ∈ S, ‖iterConv J r (d - j)‖ ^ 2) * ∑ j ∈ S, ‖J j‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S
        (fun j => ‖iterConv J r (d - j)‖) (fun j => ‖J j‖)
    have hself :
        ∑ j ∈ S, ‖iterConv J r (d - j)‖ ^ 2 ≤ iterConvEnergy J r := by
      have hsub :
          ∑ j ∈ S, ‖iterConv J r (d - j)‖ ^ 2
            ≤ ∑ j : ZMod m, ‖iterConv J r (d - j)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro j _hj; exact Finset.mem_univ j)
          (by intro j _ _; positivity)
      have hbij : Function.Bijective (fun j : ZMod m => d - j) := by
        refine ⟨?_, ?_⟩
        · intro a b hab
          linear_combination -hab
        · intro c
          refine ⟨d - c, ?_⟩
          ring
      have hreindex :
          ∑ j : ZMod m, ‖iterConv J r (d - j)‖ ^ 2 = iterConvEnergy J r := by
        unfold iterConvEnergy
        exact Fintype.sum_bijective (fun j : ZMod m => d - j) hbij _ _ (fun j => rfl)
      exact hsub.trans_eq hreindex
    calc ‖iterConv J (r + 1) d‖ ^ 2
        ≤ (∑ j ∈ S, ‖iterConv J r (d - j)‖ * ‖J j‖) ^ 2 := hsqnorm
      _ ≤ (∑ j ∈ S, ‖iterConv J r (d - j)‖ ^ 2) * ∑ j ∈ S, ‖J j‖ ^ 2 := hcs
      _ ≤ iterConvEnergy J r * ((m : ℝ) * (q : ℝ)) :=
          mul_le_mul hself hJsum
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
            (by unfold iterConvEnergy; positivity)
  calc iterConvEnergy J (r + 1)
      = ∑ d : ZMod m, ‖iterConv J (r + 1) d‖ ^ 2 := rfl
    _ ≤ ∑ _d : ZMod m, iterConvEnergy J r * ((m : ℝ) * (q : ℝ)) :=
        Finset.sum_le_sum (fun d _ => hpoint d)
    _ = (m : ℝ) * (iterConvEnergy J r * ((m : ℝ) * (q : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [ZMod.card]
    _ = iterConvEnergy J r * (m : ℝ) ^ 2 * (q : ℝ) := by ring

/-- **Depth-zero energy is exactly one.**  This is the delta mass at `0`, recorded in the
same `iterConvEnergy` API used by the tower recursion. -/
theorem iterConvEnergy_zero (J : ZMod m → ℂ) :
    iterConvEnergy J 0 = 1 := by
  classical
  unfold iterConvEnergy iterConv
  rw [show (∑ c : ZMod m, ‖(if c = 0 then (1 : ℂ) else 0)‖ ^ 2)
      = ∑ c : ZMod m, if c = 0 then (1 : ℝ) else 0 by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        by_cases hc : c = 0
        · simp [hc]
        · simp [hc]]
  rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod m) (fun _ => (1 : ℝ))]
  simp

/-- **The Wick ladder has a closed depth-zero base case for every constant.** -/
theorem iterConvEnergyWick_zero (J : ZMod m → ℂ) (q : ℕ) {C : ℝ} :
    IterConvEnergyWick J q 0 C := by
  unfold IterConvEnergyWick
  rw [show (∑ c : ZMod m, ‖iterConv J 0 c‖ ^ 2) = iterConvEnergy J 0 by rfl]
  rw [iterConvEnergy_zero]
  norm_num

/-- **Depth-one convolution is the coefficient sequence with the zero slot removed.** -/
theorem iterConv_one (J : ZMod m → ℂ) (c : ZMod m) :
    iterConv J 1 c = if c = 0 then 0 else J c := by
  classical
  unfold iterConv
  by_cases hc : c = 0
  · have hnone :
        ∀ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J 0 (c - j) * J j = 0 := by
      intro j hj
      have hj0 : j ≠ 0 := by
        intro hzero
        exact (Finset.mem_sdiff.mp hj).2 (by simp [hzero])
      have hcj : c - j ≠ 0 := by
        intro h
        rw [hc, zero_sub] at h
        exact hj0 (neg_eq_zero.mp h)
      simp [iterConv, hcj]
    rw [Finset.sum_eq_zero hnone]
    simp [hc]
  · have hmem : c ∈ Finset.univ \ {(0 : ZMod m)} := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using hc⟩
    have hsplit :
        ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J 0 (c - j) * J j
          = iterConv J 0 (c - c) * J c
            + ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).erase c,
                iterConv J 0 (c - j) * J j := by
      rw [Finset.sum_eq_sum_diff_singleton_add hmem]
      simp [Finset.sdiff_singleton_eq_erase, add_comm]
    rw [hsplit]
    have hrest :
        ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).erase c,
            iterConv J 0 (c - j) * J j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjc : j ≠ c := by
        exact (Finset.mem_erase.mp hj).1
      have hcj : c - j ≠ 0 := by
        intro h
        apply hjc
        exact sub_eq_zero.mp h |>.symm
      simp [iterConv, hcj]
    rw [hrest]
    simp [iterConv, hc, sub_self]

/-- **Depth-one Wick bound from the standard Jacobi coefficient square bound.**
This is the formal `r = 1` base of the full tower: no cancellation is needed before the
first convolution. -/
theorem iterConvEnergyWick_one_of_uniform_sq_bound (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) (hC : 1 ≤ C) :
    IterConvEnergyWick J q 1 C := by
  classical
  unfold IterConvEnergyWick
  have hsum : ∑ c : ZMod m, ‖iterConv J 1 c‖ ^ 2 ≤ (m : ℝ) * (q : ℝ) := by
    calc ∑ c : ZMod m, ‖iterConv J 1 c‖ ^ 2
        ≤ ∑ _c : ZMod m, (q : ℝ) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            rw [iterConv_one]
            split_ifs
            · simp
            · exact hJ c
      _ = (m : ℝ) * (q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [ZMod.card]
  calc ∑ c : ZMod m, ‖iterConv J 1 c‖ ^ 2
      ≤ (m : ℝ) * (q : ℝ) := hsum
    _ = 1 * ((m : ℝ) * (q : ℝ)) := by ring
    _ ≤ C * ((m : ℝ) * (q : ℝ)) := by
        have hmq : 0 ≤ (m : ℝ) * (q : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right hC hmq
    _ = C ^ 1 * ((Nat.factorial 1 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 1 := by
        norm_num

/-- **Depth two is exactly the punctured self-convolution.**  This identifies the
round-27 full-tower API with the round-21/23 quartic-convolution API at `r = 2`. -/
theorem iterConv_two_eq_selfConv (J : ZMod m → ℂ) (c : ZMod m) :
    iterConv J 2 c = selfConv J c := by
  classical
  unfold iterConv selfConv
  calc
    ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J 1 (c - j) * J j
        = ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
            if c - j ≠ 0 then J j * J (c - j) else 0 := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          by_cases hcj : c - j = 0
          · simp [iterConv_one, hcj]
          · simp [iterConv_one, hcj, mul_comm]
    _ = ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0),
          J j * J (c - j) := by
          rw [Finset.sum_filter]

/-- **Quartic/self-convolution energy input ⇒ depth-two Wick rung.**  The only numerical
loss is the formal `2` from `2!`; hence a `SelfConvEnergyBound` with constant `C₂` proves
`IterConvEnergyWick` at `r = 2` for any `C` with `C₂ ≤ 2C²`. -/
theorem iterConvEnergyWick_two_of_selfConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) {C C₂ : ℝ}
    (hself : SelfConvEnergyBound J q C₂) (hC : C₂ ≤ 2 * C ^ 2) :
    IterConvEnergyWick J q 2 C := by
  classical
  unfold SelfConvEnergyBound at hself
  unfold ArkLib.ProximityGap.Frontier.R27FullTowerCollapse.IterConvEnergyWick
  rw [show (∑ c : ZMod m, ‖iterConv J 2 c‖ ^ 2)
      = ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [iterConv_two_eq_selfConv]]
  refine le_trans hself ?_
  calc C₂ * (m : ℝ) * (q : ℝ) ^ 2
      ≤ (2 * C ^ 2) * (m : ℝ) * (q : ℝ) ^ 2 := by
        have hfactor : 0 ≤ (m : ℝ) * (q : ℝ) ^ 2 := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hC hfactor
    _ ≤ C ^ 2 * ((Nat.factorial 2 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 2 := by
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne m)))
        have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm1]
        have hfactor : 0 ≤ 2 * C ^ 2 * (q : ℝ) ^ 2 := by positivity
        calc (2 * C ^ 2) * (m : ℝ) * (q : ℝ) ^ 2
            = (2 * C ^ 2 * (q : ℝ) ^ 2) * (m : ℝ) := by ring
          _ ≤ (2 * C ^ 2 * (q : ℝ) ^ 2) * (m : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hm_sq hfactor
          _ = C ^ 2 * ((Nat.factorial 2 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 2 := by
              norm_num
              ring

/-- **Quartic face moment input ⇒ depth-two Wick rung.**  This is the direct bridge from
the round-21 quartic-collapse consumer to the final round-27 tower API. -/
theorem iterConvEnergyWick_two_of_pureFaceQuarticMomentBound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {lam : ZMod m → F → ℂ} {G : Finset F}
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {C C₂ : ℝ}
    (hquartic : PureFaceQuarticMomentBound J lam C₂) (hC : C₂ ≤ 2 * C ^ 2) :
    IterConvEnergyWick J (Fintype.card F) 2 C :=
  iterConvEnergyWick_two_of_selfConvEnergyBound J (Fintype.card F)
    (selfConvEnergyBound_of_pureFaceQuarticMomentBound hfam hgrp J hquartic) hC

/-- **Depth three is exactly the punctured triple convolution.**  This identifies the
round-27 full-tower API with the round-22/23 sextic-convolution API at `r = 3`. -/
theorem iterConv_three_eq_tripleConv (J : ZMod m → ℂ) (d : ZMod m) :
    iterConv J 3 d = tripleConv J d := by
  classical
  unfold iterConv tripleConv
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [iterConv_two_eq_selfConv]

/-- **Triple-convolution energy input ⇒ depth-three Wick rung.**
This is the exact consumer bridge from the calibrated R23 open input into the final R27 tower.
The numerical condition is just the factorial normalization:
`C₃ ≤ 6C³`. -/
theorem iterConvEnergyWick_three_of_tripleConvEnergyBound
    (J : ZMod m → ℂ) (q : ℕ) {C C₃ : ℝ}
    (htriple : TripleConvEnergyBound J q C₃) (hC : C₃ ≤ 6 * C ^ 3) :
    IterConvEnergyWick J q 3 C := by
  classical
  unfold TripleConvEnergyBound at htriple
  unfold ArkLib.ProximityGap.Frontier.R27FullTowerCollapse.IterConvEnergyWick
  rw [show (∑ c : ZMod m, ‖iterConv J 3 c‖ ^ 2)
      = ∑ c : ZMod m, ‖tripleConv J c‖ ^ 2 by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [iterConv_three_eq_tripleConv]]
  refine le_trans htriple ?_
  calc C₃ * (m : ℝ) ^ 3 * (q : ℝ) ^ 3
      ≤ (6 * C ^ 3) * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        have hfactor : 0 ≤ (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hC hfactor
    _ = C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 3 := by
        norm_num
        ring

/-- **Depth-three Wick rung ⇒ triple-convolution energy input.**
This is the converse adapter to `iterConvEnergyWick_three_of_tripleConvEnergyBound`, with the
constant normalized exactly as `3! * C^3`. -/
theorem tripleConvEnergyBound_of_iterConvEnergyWick_three
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : IterConvEnergyWick J q 3 C) :
    TripleConvEnergyBound J q (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)) := by
  classical
  unfold TripleConvEnergyBound
  unfold ArkLib.ProximityGap.Frontier.R27FullTowerCollapse.IterConvEnergyWick at h
  rw [show (∑ c : ZMod m, ‖tripleConv J c‖ ^ 2)
      = ∑ c : ZMod m, ‖iterConv J 3 c‖ ^ 2 by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [iterConv_three_eq_tripleConv]]
  calc ∑ c : ZMod m, ‖iterConv J 3 c‖ ^ 2
      ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ) * ((m : ℝ) * (q : ℝ)) ^ 3 := h
    _ = (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)) * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        ring

/-- **Quartic face moment input ⇒ depth-three Wick rung via the R23 Young/Cauchy bridge.**
This packages the already-proven quartic-to-sextic formal implication in the final tower API. -/
theorem iterConvEnergyWick_three_of_pureFaceQuarticMomentBound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {lam : ZMod m → F → ℂ} {G : Finset F}
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {C C₃ : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hquartic : PureFaceQuarticMomentBound J lam C₃) (hC : C₃ ≤ 6 * C ^ 3) :
    IterConvEnergyWick J (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound J (Fintype.card F)
    (tripleConvEnergyBound_of_pureFaceQuarticMomentBound hfam hgrp J hJ hquartic) hC

/-- **One-step Wick propagation under the exact remaining budget.**
If rung `r` is already at Wick scale and the Cauchy recursion's leftover factor satisfies
`m ≤ C·(r+1)`, then rung `r+1` is also at the same Wick constant.

Thus the purely formal recursion pinpoints the missing arithmetic input: every step needs
one factor of `m` to be absorbed into the factorial/constant budget. -/
theorem iterConvEnergyWick_succ_of_prev_of_budget (J : ZMod m → ℂ) (q r : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC : 0 ≤ C)
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + 1) C := by
  classical
  unfold IterConvEnergyWick at hprev ⊢
  have hrec := iterConvEnergy_succ_le_card_sq_mul J q r hJ
  unfold iterConvEnergy at hrec
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hmq_nonneg : 0 ≤ (m : ℝ) * (q : ℝ) := by positivity
  have hfactor_nonneg : 0 ≤ (m : ℝ) * (q : ℝ) := by positivity
  have hpref_nonneg :
      0 ≤ (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r) *
          ((m : ℝ) * (q : ℝ)) := by positivity
  have hstep :
      (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r) *
          ((m : ℝ) * (q : ℝ)) * (m : ℝ)
        ≤ (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r) *
          ((m : ℝ) * (q : ℝ)) * (C * ((r + 1 : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hbudget hpref_nonneg
  have hprevE :
      iterConvEnergy J r ≤ C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r := by
    unfold iterConvEnergy
    exact hprev
  calc ∑ c : ZMod m, ‖iterConv J (r + 1) c‖ ^ 2
      = iterConvEnergy J (r + 1) := rfl
    _ ≤ iterConvEnergy J r * (m : ℝ) ^ 2 * (q : ℝ) := hrec
    _ ≤ (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r)
          * (m : ℝ) ^ 2 * (q : ℝ) := by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_right hprevE (by positivity : 0 ≤ (m : ℝ) ^ 2 * (q : ℝ))
    _ = (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r)
          * ((m : ℝ) * (q : ℝ)) * (m : ℝ) := by ring
    _ ≤ (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r)
          * ((m : ℝ) * (q : ℝ)) * (C * ((r + 1 : ℕ) : ℝ)) := hstep
    _ = C ^ (r + 1) * ((r + 1).factorial : ℝ)
          * ((m : ℝ) * (q : ℝ)) ^ (r + 1) := by
        have hfact : (((r + 1).factorial : ℕ) : ℝ)
            = ((r + 1 : ℕ) : ℝ) * (r.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          norm_cast
        rw [hfact, pow_succ, pow_succ]
        ring

end ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergy_succ_le_card_sq_mul
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergy_zero
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_zero
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConv_one
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_one_of_uniform_sq_bound
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConv_two_eq_selfConv
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_two_of_selfConvEnergyBound
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_two_of_pureFaceQuarticMomentBound
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConv_three_eq_tripleConv
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_three_of_tripleConvEnergyBound
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms tripleConvEnergyBound_of_iterConvEnergyWick_three
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_three_of_pureFaceQuarticMomentBound
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion in
#print axioms iterConvEnergyWick_succ_of_prev_of_budget
