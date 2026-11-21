/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Hab25CaptureKernelUD

/-!
# An exact small-scale over-budget stack at `n = 16` over `F_17`

The SYZ52 sampled stack lift records a genuine `(4,4,4; t=3)` support configuration
for the smooth order-16 domain in `F_17` with 17 finite MCA-bad scalars, exceeding
the small-scale budget `n - 1 = 15`.  This file turns one sampled stack into a
kernel-checked certificate: every scalar in `F_17` has a degree-`<8` folded
codeword agreeing on at least 11 coordinates, and the corresponding support is
not jointly explained by two Reed--Solomon codewords.

This refutes a uniform `n-1` stack-incidence cap at this finite instance.  It does
not refute the production-scale `2^30` claim or prove anything about an exhaustive
maximum at other parameters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxErrors 30

open Finset Polynomial
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.SYZ52F17ExplicitOverbudget

attribute [local instance] Classical.propDecidable

abbrev F17 := ZMod 17

local instance localInstance_F17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A generator of the order-16 subgroup `F_17ˣ`. -/
def omega : F17 := 3

/-- The powers of `3`, listed in the same coordinate order as the finite-field probe. -/
def domainValues : Fin 16 → F17 := ![
  1, 3, 9, 10, 13, 5, 15, 11,
  16, 14, 8, 7, 4, 12, 2, 6]

/-- The smooth evaluation domain `mu_16` in `F_17`. -/
def dom : Fin 16 ↪ F17 := ⟨domainValues, by decide⟩

theorem domainValues_eq_pow (e : Fin 16) : domainValues e = omega ^ (e : ℕ) := by
  fin_cases e <;> decide

theorem omega_pow_sixteen : omega ^ 16 = (1 : F17) := by decide

/-- First received word of the explicit rate-half stack. -/
def u0 : Fin 16 → F17 := ![
  13, 1, 16, 15, 10, 6, 13, 15,
  8, 10, 3, 2, 5, 6, 6, 14]

/-- Second received word of the explicit rate-half stack. -/
def u1 : Fin 16 → F17 := ![
  15, 10, 8, 8, 6, 15, 6, 15,
  6, 13, 16, 4, 1, 15, 14, 15]

def u : WordStack F17 (Fin 2) (Fin 16) := ![u0, u1]

@[simp] theorem u_zero : u 0 = u0 := rfl
@[simp] theorem u_one : u 1 = u1 := rfl

/-! ## Seventeen literal folded-codeword and non-jointness certificates -/

/-- The scalar being certified. -/
def gamma (j : Fin 17) : F17 := j.val

/-- Agreement supports obtained by exact decoding of the displayed stack. -/
def support : Fin 17 → Finset (Fin 16) := ![
  {0, 1, 2, 3, 4, 6, 7, 8, 9, 12, 14},
  {0, 1, 2, 3, 5, 6, 8, 11, 12, 13, 14},
  {1, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14},
  {0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 14, 15},
  {0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 13},
  {0, 1, 3, 4, 7, 8, 11, 12, 13, 14, 15},
  {0, 3, 4, 6, 7, 8, 9, 10, 12, 13, 15},
  {1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 14},
  {1, 2, 4, 5, 6, 7, 9, 10, 11, 12, 15},
  {0, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14},
  {0, 1, 2, 3, 7, 8, 10, 12, 13, 14, 15},
  {0, 1, 2, 3, 4, 5, 6, 8, 11, 12, 13, 15},
  {0, 1, 2, 6, 7, 8, 9, 10, 11, 14, 15},
  {0, 1, 2, 3, 4, 6, 7, 9, 11, 12, 14},
  {0, 1, 2, 3, 4, 6, 7, 9, 12, 14, 15},
  {0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13},
  {0, 1, 2, 8, 9, 10, 11, 12, 13, 14, 15}]

/-- Write an evaluation polynomial from its eight coefficient values. -/
noncomputable def poly8 (c : Fin 8 → F17) : F17[X] :=
  ∑ i : Fin 8, C (c i) * X ^ (i : ℕ)

theorem poly8_natDegree_le_seven (c : Fin 8 → F17) : (poly8 c).natDegree ≤ 7 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_X_pow_le (c i) (i : ℕ)).trans (by omega)

theorem degree_lt_eight_of_natDegree_le_seven {p : F17[X]} (hp : p.natDegree ≤ 7) :
    p.degree < 8 := by
  by_cases hzero : p = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe 8
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp (lt_of_le_of_lt hp (by norm_num))

/-- Coefficients of the 17 decoded folded words, in increasing degree order. -/
def qCoeffs : Fin 17 → Fin 8 → F17 := ![
  ![10, 14, 8, 9, 16, 5, 2, 0],
  ![13, 8, 7, 6, 14, 7, 4, 3],
  ![8, 8, 8, 5, 12, 14, 6, 4],
  ![10, 15, 3, 16, 12, 11, 0, 8],
  ![13, 2, 3, 4, 13, 2, 15, 4],
  ![9, 14, 14, 11, 1, 3, 5, 14],
  ![5, 13, 3, 7, 12, 7, 11, 11],
  ![9, 16, 0, 4, 16, 8, 6, 4],
  ![0, 9, 13, 13, 1, 15, 12, 6],
  ![15, 8, 14, 8, 6, 4, 2, 6],
  ![3, 12, 12, 0, 3, 0, 4, 10],
  ![13, 5, 5, 5, 5, 13, 1, 12],
  ![7, 10, 3, 3, 10, 0, 6, 1],
  ![1, 4, 3, 2, 0, 0, 13, 15],
  ![16, 15, 0, 8, 4, 14, 6, 7],
  ![13, 14, 11, 8, 15, 12, 10, 2],
  ![0, 4, 3, 1, 11, 14, 3, 13]]

/-- The degree-`<8` polynomial agreeing with the folded word on `support j`. -/
noncomputable def q (j : Fin 17) : F17[X] := poly8 (qCoeffs j)

/-! The no-joint certificates use an eight-point interpolation core and a
fresh coordinate where its unique polynomial fails to match one component. -/

def noJointCore : Fin 17 → Finset (Fin 16) := ![
  {0, 1, 2, 3, 4, 6, 7, 8}, {0, 1, 2, 3, 5, 6, 8, 11},
  {1, 4, 5, 6, 7, 8, 9, 11}, {0, 1, 2, 3, 4, 5, 8, 9},
  {0, 1, 2, 3, 5, 6, 8, 9}, {0, 1, 3, 4, 7, 8, 11, 12},
  {0, 3, 4, 6, 7, 8, 9, 10}, {1, 2, 3, 5, 6, 7, 8, 9},
  {1, 2, 4, 5, 6, 7, 9, 10}, {0, 4, 5, 6, 7, 8, 9, 11},
  {0, 1, 2, 3, 7, 8, 10, 12}, {0, 1, 2, 3, 4, 5, 6, 8},
  {0, 1, 2, 6, 7, 8, 9, 10}, {0, 1, 2, 3, 4, 6, 7, 9},
  {0, 1, 2, 3, 4, 6, 7, 9}, {0, 1, 2, 3, 5, 6, 7, 8},
  {0, 1, 2, 8, 9, 10, 11, 12}]

def fresh : Fin 17 → Fin 16 := ![
  9, 14, 12, 10, 11, 13, 12, 10, 11, 12, 14, 11, 11, 11, 15, 10, 13]

def side : Fin 17 → Fin 2 := ![
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The received component used to obstruct a joint explanation. -/
def received (j : Fin 17) : Fin 16 → F17 := if side j = 0 then u0 else u1

/-- Coefficients of the obstructing interpolant, in increasing degree order. -/
def interpolantCoeffs : Fin 17 → Fin 8 → F17 := ![
  ![13, 3, 0, 6, 15, 1, 8, 3], ![13, 10, 14, 1, 3, 3, 6, 14],
  ![7, 11, 14, 5, 15, 0, 4, 16], ![0, 7, 3, 4, 16, 1, 0, 16],
  ![6, 0, 3, 3, 8, 2, 2, 6], ![13, 3, 11, 11, 13, 16, 16, 15],
  ![13, 3, 7, 12, 0, 0, 16, 13], ![11, 13, 6, 8, 13, 13, 8, 13],
  ![16, 6, 3, 16, 3, 5, 0, 2], ![5, 5, 1, 13, 10, 7, 3, 3],
  ![0, 8, 14, 1, 13, 10, 9, 9], ![4, 2, 12, 6, 7, 9, 13, 11],
  ![3, 12, 8, 2, 14, 6, 11, 8], ![10, 14, 8, 9, 16, 5, 2, 0],
  ![10, 14, 8, 9, 16, 5, 2, 0], ![15, 8, 5, 15, 4, 13, 12, 9],
  ![12, 6, 13, 10, 4, 7, 7, 5]]

/-- The degree-`<8` interpolant of the obstructing component on `noJointCore`. -/
noncomputable def interpolant (j : Fin 17) : F17[X] := poly8 (interpolantCoeffs j)

theorem support_card_lower (j : Fin 17) : 11 ≤ (support j).card := by
  fin_cases j <;> decide

theorem q_degree_lt_eight (j : Fin 17) : (q j).degree < (8 : ℕ) := by
  exact degree_lt_eight_of_natDegree_le_seven (poly8_natDegree_le_seven (qCoeffs j))

set_option maxHeartbeats 20000000 in
set_option linter.flexible false in
/-- Each listed polynomial agrees with its folded word on its displayed support. -/
theorem support_agreement (j : Fin 17) (i : Fin 16) (hi : i ∈ support j) :
    (q j).eval (dom i) = u0 i + gamma j * u1 i := by
  fin_cases j <;> fin_cases i <;> simp [support] at hi
  all_goals simp [q, poly8, qCoeffs, gamma, dom, domainValues, u0, u1, Fin.sum_univ_succ]
  all_goals decide

theorem noJointCore_card (j : Fin 17) : (noJointCore j).card = 8 := by
  fin_cases j <;> decide

theorem noJointCore_subset_support (j : Fin 17) : noJointCore j ⊆ support j := by
  fin_cases j <;> decide

theorem fresh_mem_support (j : Fin 17) : fresh j ∈ support j := by
  fin_cases j <;> decide

theorem fresh_not_mem_noJointCore (j : Fin 17) : fresh j ∉ noJointCore j := by
  fin_cases j <;> decide

set_option maxHeartbeats 20000000 in
set_option linter.flexible false in
/-- The interpolation polynomial matches the selected received component on its eight-point core. -/
theorem interpolant_agreement (j : Fin 17) (i : Fin 16) (hi : i ∈ noJointCore j) :
    (interpolant j).eval (dom i) = received j i := by
  fin_cases j <;> fin_cases i <;> simp [noJointCore] at hi
  all_goals simp [interpolant, poly8, interpolantCoeffs, received, side, dom, domainValues, u0, u1,
    Fin.sum_univ_succ]
  all_goals decide

set_option maxHeartbeats 20000000 in
set_option linter.flexible false in
/-- At the listed fresh coordinate, the unique core interpolant disagrees with that component. -/
theorem interpolant_fresh_mismatch (j : Fin 17) :
    (interpolant j).eval (dom (fresh j)) ≠ received j (fresh j) := by
  fin_cases j <;>
    simp [interpolant, poly8, interpolantCoeffs, fresh, received, side, dom, domainValues, u0, u1,
      Fin.sum_univ_succ] <;> decide

theorem interpolant_degree_lt_eight (j : Fin 17) : (interpolant j).degree < (8 : ℕ) := by
  exact degree_lt_eight_of_natDegree_le_seven (poly8_natDegree_le_seven (interpolantCoeffs j))

/-- Eight matching evaluation points force any candidate RS word to equal the listed
interpolant.  The extra fresh coordinate then rules out agreement on the full support. -/
theorem no_codeword_agrees_on_support (j : Fin 17) :
    ¬ ∃ c ∈ ReedSolomon.code dom 8,
      ∀ i ∈ support j, c i = received j i := by
  rintro ⟨c, hc, hagree⟩
  change c ∈ ReedSolomon.code dom 8 at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨p, hp, hrepresentation⟩ := hc
  have hpoly : p = interpolant j := by
    apply sub_eq_zero.mp
    apply eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt hp (interpolant_degree_lt_eight j)))
      (noJointCore j) (by rw [noJointCore_card])
    intro i hi
    have h := hagree i (noJointCore_subset_support j hi)
    rw [hrepresentation] at h
    have heval : p.eval (dom i) = received j i := by
      simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply] using h
    rw [eval_sub, heval, interpolant_agreement j i hi, sub_self]
  have hfresh := hagree (fresh j) (fresh_mem_support j)
  rw [hrepresentation] at hfresh
  have heval : p.eval (dom (fresh j)) = received j (fresh j) := by
    simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply] using hfresh
  rw [hpoly] at heval
  exact (interpolant_fresh_mismatch j) heval

/-- The same support cannot admit a joint Reed--Solomon explanation: one component
already fails to have any degree-`<8` codeword agreeing on the support. -/
theorem support_not_joint (j : Fin 17) :
    ¬ pairJointAgreesOn
      ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
      (support j) u0 u1 := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  by_cases hside : side j = 0
  · apply no_codeword_agrees_on_support j
    refine ⟨v0, hv0, ?_⟩
    intro i hi
    simpa [received, hside] using (hagree i hi).1
  · apply no_codeword_agrees_on_support j
    refine ⟨v1, hv1, ?_⟩
    intro i hi
    simpa [received, hside] using (hagree i hi).2

theorem radius_product_eq_eleven :
    ((1 : ℝ≥0) - (5 / 16 : ℝ≥0)) * (Fintype.card (Fin 16) : ℝ≥0) = 11 := by
  have hcard : Fintype.card (Fin 16) = 16 := Fintype.card_fin 16
  have hδ : (5 / 16 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 16)]
    norm_num
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub hδ, hcard]
  push_cast
  norm_num

/-- An explicit `mcaEvent` witness for every finite scalar of `F_17`. -/
noncomputable def decode (j : Fin 17) : McaDecode dom 8 (5 / 16) u (gamma j) where
  S := support j
  P := q j
  hdeg := q_degree_lt_eight j
  hcard := by
    rw [radius_product_eq_eleven]
    exact_mod_cast support_card_lower j
  hagree := by
    intro i hi
    simpa only [u_zero, u_one, smul_eq_mul] using support_agreement j i hi
  hnjp := support_not_joint j

theorem mcaEvent_index (j : Fin 17) :
    mcaEvent
      ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
      (5 / 16) (u 0) (u 1) (gamma j) :=
  (decode j).mcaEvent

/-- All 17 elements of `F_17` occur in the explicit scalar certificate. -/
def gammaEmbedding : Fin 17 ↪ F17 := ⟨gamma, by decide⟩

def G : Finset F17 := Finset.univ.map gammaEmbedding

theorem G_card : G.card = 17 := by simp [G]

theorem G_subset_badScalar_filter :
    G ⊆ Finset.univ.filter fun z : F17 =>
      mcaEvent
        ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
        (5 / 16) (u 0) (u 1) z := by
  intro z hz
  rw [G, Finset.mem_map] at hz
  obtain ⟨j, _, rfl⟩ := hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mcaEvent_index j

/-- The exhibited stack has at least 17 finite bad scalars, exceeding `n - 1 = 15`. -/
theorem seventeen_le_badScalar_filter_card :
    17 ≤ (Finset.univ.filter fun z : F17 =>
      mcaEvent
        ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
        (5 / 16) (u 0) (u 1) z).card := by
  calc
    17 = G.card := G_card.symm
    _ ≤ _ := Finset.card_le_card G_subset_badScalar_filter

theorem badScalar_filter_card_eq_17 :
    (Finset.univ.filter fun z : F17 =>
      mcaEvent
        ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
        (5 / 16) (u 0) (u 1) z).card = 17 := by
  apply le_antisymm
  · calc
      _ ≤ (Finset.univ : Finset F17).card := Finset.card_le_univ _
      _ = 17 := by simp [F17, ZMod.card]
  · exact seventeen_le_badScalar_filter_card

theorem fifteen_lt_badScalar_filter_card :
    15 < (Finset.univ.filter fun z : F17 =>
      mcaEvent
        ((ReedSolomon.code dom 8 : Submodule F17 (Fin 16 → F17)) : Set (Fin 16 → F17))
        (5 / 16) (u 0) (u 1) z).card :=
  lt_of_lt_of_le (by norm_num) seventeen_le_badScalar_filter_card

end ArkLib.ProximityGap.Frontier.SYZ52F17ExplicitOverbudget

open ArkLib.ProximityGap.Frontier.SYZ52F17ExplicitOverbudget
#print axioms mcaEvent_index
#print axioms seventeen_le_badScalar_filter_card
#print axioms badScalar_filter_card_eq_17
#print axioms fifteen_lt_badScalar_filter_card
