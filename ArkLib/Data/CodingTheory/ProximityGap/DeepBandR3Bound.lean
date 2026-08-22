/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors

STANDALONE VERIFIED PROOF-OF-RECORD (O172 Facet B).
This is the exact file that was scratch-verified axiom-clean with
  cd /home/nubs/Git/ArkLib && lake env lean <this>
producing, for ALL named theorems, axioms: [propext, Classical.choice, Quot.sound]
(no sorryAx, no native_decide).  It inlines a copy of the in-tree Vieta pin
(SinglePencilSharper.witness_pin_eq_neg_sum) so it depends ONLY on Mathlib (no heavy
ProximityGap olean needed for verification).  The in-tree deliverable `DeepBandR3Bound.lean`
is identical EXCEPT it imports the real `DeepBandSubsetSumSpectrum` and calls the real
`witness_pin_eq_neg_sum` (adding the `[Fintype F] [DecidableEq F]` instances that lemma carries).
-/
import Mathlib

/-! ## Inlined Vieta pin (mirror of in-tree witness_pin_eq_neg_sum, Mathlib-only deps). -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace ScratchVerify

open Finset Polynomial


private theorem prodXsubC_dvd_of_roots {F : Type*} [Field F] (P : F[X]) (S : Finset F)
    (hS : ∀ ζ ∈ S, P.eval ζ = 0) : (∏ ζ ∈ S, (X - C ζ)) ∣ P := by
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id (by simpa using hab)
  · intro ζ hζ; rw [Polynomial.dvd_iff_isRoot]; simpa using hS ζ hζ

private theorem prodXsubC_natDegree {F : Type*} [Field F] (S : Finset F) :
    (∏ ζ ∈ S, (X - C ζ)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ (fun ζ _ => X_sub_C_ne_zero ζ),
    Finset.sum_congr rfl (fun ζ _ => Polynomial.natDegree_X_sub_C ζ),
    Finset.sum_const, smul_eq_mul, mul_one]

theorem witness_pin_eq_neg_sum {F : Type*} [Field F] (S : Finset F) (k : ℕ) (hScard : S.card = k + 1)
    (γ : F) (W : F[X]) (hWdeg : W.natDegree < k)
    (hvanish : ∀ ζ ∈ S, (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0) :
    γ = -∑ ζ ∈ S, ζ := by
  classical
  set m := ∏ ζ ∈ S, (X - C ζ) with hmdef
  have hdvd : m ∣ (X ^ (k + 1) + C γ * X ^ k - W) :=
    prodXsubC_dvd_of_roots _ S hvanish
  have hmmonic : m.Monic := monic_prod_of_monic _ _ (fun ζ _ => monic_X_sub_C ζ)
  have hmdeg : m.natDegree = k + 1 := by rw [hmdef, prodXsubC_natDegree, hScard]
  set P := X ^ (k + 1) + C γ * X ^ k - W with hPdef
  obtain ⟨c, hc⟩ := hdvd
  have hPdeg_le : P.natDegree ≤ k + 1 := by
    rw [hPdef]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Nat.max_le]
    refine ⟨le_trans (Polynomial.natDegree_add_le _ _) ?_, by omega⟩
    rw [Nat.max_le]
    refine ⟨by rw [Polynomial.natDegree_X_pow], ?_⟩
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X_pow]; omega)
  have hPcoeff_top : P.coeff (k + 1) = 1 := by
    rw [hPdef]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero, add_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : W.natDegree < k + 1), sub_zero]
  have hPcoeff_k : P.coeff k = γ := by
    rw [hPdef]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
      zero_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one,
      Polynomial.coeff_eq_zero_of_natDegree_lt hWdeg, sub_zero]
  have hPne : P ≠ 0 := by
    intro h; rw [h, Polynomial.coeff_zero] at hPcoeff_top; exact one_ne_zero hPcoeff_top.symm
  have hPdeg : P.natDegree = k + 1 :=
    le_antisymm hPdeg_le (Polynomial.le_natDegree_of_ne_zero (by rw [hPcoeff_top]; exact one_ne_zero))
  have hcne : c ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc; exact hPne hc
  have hmne : m ≠ 0 := hmmonic.ne_zero
  have hdeg_add : P.natDegree = m.natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul hmne hcne]
  have hcdeg : c.natDegree = 0 := by omega
  obtain ⟨cc, rfl⟩ := Polynomial.natDegree_eq_zero.mp hcdeg
  have hm_top : m.coeff (k + 1) = 1 := by
    have := hmmonic; rw [Polynomial.Monic, Polynomial.leadingCoeff, hmdeg] at this; exact this
  have hcc1 : cc = 1 := by
    have h := congrArg (fun q => Polynomial.coeff q (k + 1)) hc
    simp only at h
    rw [hPcoeff_top, Polynomial.coeff_mul_C, hm_top, one_mul] at h
    exact h.symm
  subst hcc1
  have hm_k : m.coeff k = -∑ ζ ∈ S, ζ := by
    have hpred : (∏ ζ ∈ S, (X - C ζ)).coeff (S.card - 1) = -∑ ζ ∈ S, ζ := by
      have := Polynomial.prod_X_sub_C_coeff_card_pred S (id : F → F) (by rw [hScard]; omega)
      simpa using this
    rw [hmdef]; rw [hScard] at hpred; simpa using hpred
  have h := congrArg (fun q => Polynomial.coeff q k) hc
  simp only at h
  rw [hPcoeff_k, Polynomial.coeff_mul_C, hm_k, mul_one] at h
  exact h

end ScratchVerify

namespace ArkLib.ProximityGap.DeepBandR3

open Finset

def deepBandBadCount (g : ℕ) : ℕ := 2 * g ^ 2 * (g - 1) + 1
def deepBandBudget (g : ℕ) : ℕ := 2 ^ 3 * (2 * g).choose 3

theorem deepBandBadCount_eq_choose (g : ℕ) :
    deepBandBadCount g = 4 * g * g.choose 2 + 1 := by
  rw [deepBandBadCount, Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · simp
  · obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
    have he1 : e + 1 - 1 = e := by omega
    rw [he1]
    have hdvd : 2 ∣ (e + 1) * e := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self e).two_dvd
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
    nlinarith [hc]

theorem six_mul_choose_three (g : ℕ) (hg : 1 ≤ g) :
    6 * (2 * g).choose 3 = (2 * g) * (2 * g - 1) * (2 * g - 2) := by
  have h3 : (2 * g).choose 3 = (2 * g).descFactorial 3 / Nat.factorial 3 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 3 ∣ (2 * g).descFactorial 3 := Nat.factorial_dvd_descFactorial _ _
  have hfac : Nat.factorial 3 = 6 := by decide
  rw [hfac] at hdvd
  rw [h3, hfac, Nat.mul_div_cancel' hdvd]
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.descFactorial_zero, mul_one, Nat.sub_zero]
  have a1 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
  have a2 : 2 * (e + 1) - 2 = 2 * e := by omega
  rw [a1, a2]
  ring

theorem twelve_budget_eq (g : ℕ) (hg : 2 ≤ g) :
    12 * deepBandBudget g
      = 12 * deepBandBadCount g + ((2 * g - 2) * (2 * g) * (13 * (2 * g) - 16) - 12) := by
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 2 := ⟨g - 2, by omega⟩
  have hc : 6 * (2 * (e + 2)).choose 3 = (2 * (e + 2)) * (2 * (e + 2) - 1) * (2 * (e + 2) - 2) :=
    six_mul_choose_three (e + 2) (by omega)
  have e1 : 2 * (e + 2) - 1 = 2 * e + 3 := by omega
  have e2 : 2 * (e + 2) - 2 = 2 * e + 2 := by omega
  have e3 : 13 * (2 * (e + 2)) - 16 = 26 * e + 36 := by omega
  have e5 : e + 2 - 1 = e + 1 := by omega
  rw [e1, e2] at hc
  rw [deepBandBudget, deepBandBadCount, e2, e3, e5]
  set Ch := (2 * (e + 2)).choose 3 with hChdef
  have hLHS : 12 * (2 ^ 3 * Ch) = 16 * (6 * Ch) := by ring
  rw [hLHS, hc]
  have hge : 12 ≤ (2 * e + 2) * (2 * (e + 2)) * (26 * e + 36) := by nlinarith [Nat.zero_le e]
  set P := (2 * e + 2) * (2 * (e + 2)) * (26 * e + 36) with hPdef
  obtain ⟨Q, hQval⟩ : ∃ Q, P = Q + 12 := ⟨P - 12, by omega⟩
  rw [hQval, Nat.add_sub_cancel]
  rw [hQval] at hPdef
  nlinarith [hPdef, Nat.zero_le e]

theorem twelve_mul_budget_sub_count (g : ℕ) (hg : 2 ≤ g) :
    12 * (deepBandBudget g - deepBandBadCount g)
      = (2 * g - 2) * (2 * g) * (13 * (2 * g) - 16) - 12 := by
  have h := twelve_budget_eq g hg
  omega

theorem deepBandBadCount_le_budget (g : ℕ) (hg : 2 ≤ g) :
    deepBandBadCount g ≤ deepBandBudget g := by
  have h := twelve_budget_eq g hg
  omega

theorem badscalar_eq_neg_subset_sum {F : Type*} [Field F]
    (S : Finset F) (γ : F) (W : Polynomial F) (hScard : S.card = 3)
    (hWdeg : W.natDegree < 2)
    (hvanish : ∀ ζ ∈ S, (Polynomial.X ^ 3 + Polynomial.C γ * Polynomial.X ^ 2 - W).eval ζ = 0) :
    γ = -∑ ζ ∈ S, ζ :=
  ScratchVerify.witness_pin_eq_neg_sum S 2 hScard γ W hWdeg (by simpa using hvanish)

def R3CensusCountValue (badScalarCount : ℕ → ℕ) : Prop :=
  ∀ g, badScalarCount g = deepBandBadCount g

theorem r3_censusDomination_of_countValue {badScalarCount : ℕ → ℕ}
    (hcount : R3CensusCountValue badScalarCount) (g : ℕ) (hg : 2 ≤ g) :
    badScalarCount g ≤ deepBandBudget g := by
  rw [hcount g]; exact deepBandBadCount_le_budget g hg

theorem rung_n16 : deepBandBadCount 4 = 97 ∧ deepBandBudget 4 = 448 := ⟨by decide, by decide⟩
theorem rung_n32 : deepBandBadCount 8 = 897 ∧ deepBandBudget 8 = 4480 := ⟨by decide, by decide⟩
theorem rung_n64 : deepBandBadCount 16 = 7681 ∧ deepBandBudget 16 = 39680 := ⟨by decide, by decide⟩

end ArkLib.ProximityGap.DeepBandR3

#print axioms ArkLib.ProximityGap.DeepBandR3.deepBandBadCount_eq_choose
#print axioms ArkLib.ProximityGap.DeepBandR3.deepBandBadCount_le_budget
#print axioms ArkLib.ProximityGap.DeepBandR3.twelve_mul_budget_sub_count
#print axioms ArkLib.ProximityGap.DeepBandR3.badscalar_eq_neg_subset_sum
#print axioms ArkLib.ProximityGap.DeepBandR3.r3_censusDomination_of_countValue
