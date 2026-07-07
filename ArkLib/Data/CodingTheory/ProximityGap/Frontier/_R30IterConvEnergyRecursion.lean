/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
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
#print axioms
  ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion.iterConvEnergy_succ_le_card_sq_mul
#print axioms
  ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion.iterConvEnergyWick_succ_of_prev_of_budget
