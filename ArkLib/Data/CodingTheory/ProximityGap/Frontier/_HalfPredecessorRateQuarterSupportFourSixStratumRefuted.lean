/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization

/-!
# Rate-quarter support-four: the proposed `t = 6` cap four is false

This file checks a concrete counterexample over `F_17` on the smooth domain
`F_17^* = {1,...,16}`.  The direction is supported on the first four
coordinates.  Five distinct degree-`<4` codewords each agree with the offset
on exactly six of the remaining twelve coordinates and, at a displayed
scalar, on three of the four moving coordinates.  They therefore all belong
to the `t = 6` zero-agreement stratum.

The counterexample is genuinely zero-direction safe.  On the twelve fixed
coordinates the offset is the evaluation of

```text
W(X) = X^8 + 7 X^7 + 14 X^6 + 10 X^5 + 3 X^4.
```

For every degree-`<4` polynomial `p`, the nonzero polynomial `W-p` has degree
eight, so it has at most eight evaluation-domain roots.  In particular no
Reed--Solomon codeword agrees with the offset on nine fixed coordinates.

The certificate was generated and exhaustively checked by
`scripts/probes/probe_rate_quarter_support4_t6_f17.py`.  Its full `17^4`
census has no appearing strata other than these five `t = 6` codewords; the
bad scalars are exactly `{2,5,10,12,15}`.  The Lean refutation only needs the
five explicit lower-bound witnesses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSixStratumRefuted

open _root_.ProximityGap _root_.ProximityGap.Ownership
open _root_.ProximityGap.SpikeFloor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

attribute [local instance] Classical.propDecidable

abbrev F17 := ZMod 17

local instance localInstance_HalfPredecessorRateQuarterSupportFourSixStratumRefuted_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The canonical smooth length-sixteen domain `F_17^*`. -/
def domainValues : Fin 16 → F17 := ![
  1, 2, 3, 4, 5, 6, 7, 8,
  9, 10, 11, 12, 13, 14, 15, 16]

def dom : Fin 16 ↪ F17 := ⟨domainValues, by decide⟩

theorem domainValues_pow_sixteen (i : Fin 16) :
    domainValues i ^ 16 = (1 : F17) := by
  fin_cases i <;> decide

/-- The received offset. -/
def u0 : Fin 16 → F17 := ![
  0, 4, 12, 5, 4, 2, 8, 11,
  12, 11, 6, 9, 12, 2, 1, 1]

/-- The support-four direction. -/
def u1 : Fin 16 → F17 := ![
  1, 12, 8, 6, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0]

/-- The degree-eight polynomial supplying `u0` on every fixed coordinate. -/
noncomputable def receivedPolynomial : F17[X] :=
  X ^ 8 + C 7 * X ^ 7 + C 14 * X ^ 6 + C 10 * X ^ 5 + C 3 * X ^ 4

/-- Five explicit degree-`<4` polynomials. -/
noncomputable def witnessPolynomial : Fin 5 → F17[X] := ![
  C 0 + C 3 * X + C 8 * X ^ 2 + C 1 * X ^ 3,
  C 3 + C 12 * X + C 9 * X ^ 2 + C 8 * X ^ 3,
  C 7 + C 9 * X + C 1 * X ^ 2 + C 2 * X ^ 3,
  C 12 + C 0 * X + C 2 * X ^ 2 + C 13 * X ^ 3,
  C 12 + C 9 * X + C 14 * X ^ 2 + C 4 * X ^ 3]

/-- The corresponding Reed--Solomon codewords. -/
noncomputable def witnessCodeword (j : Fin 5) : Fin 16 → F17 :=
  fun i ↦ (witnessPolynomial j).eval (dom i)

/-- Heavy scalar for each codeword. -/
def witnessScalar : Fin 5 → F17 := ![12, 15, 2, 10, 5]

/-- Its six fixed-coordinate agreements with `u0`. -/
def zeroTrace : Fin 5 → Finset (Fin 16) := ![
  {6, 7, 9, 11, 13, 14},
  {5, 6, 7, 10, 12, 13},
  {4, 5, 7, 8, 11, 12},
  {4, 5, 8, 13, 14, 15},
  {6, 8, 9, 10, 12, 14}]

/-- Three moving coordinates agreeing at the heavy scalar. -/
def movingTriple : Fin 5 → Finset (Fin 16) := ![
  {0, 1, 2},
  {0, 2, 3},
  {0, 1, 3},
  {0, 1, 2},
  {0, 2, 3}]

def agreementWitness (j : Fin 5) : Finset (Fin 16) :=
  zeroTrace j ∪ movingTriple j

theorem directionSupportSet_eq : directionSupportSet u1 = {0, 1, 2, 3} := by
  ext i
  fin_cases i <;>
    simp [directionSupportSet, u1] <;>
    decide

theorem directionSupportSet_card : (directionSupportSet u1).card = 4 := by
  rw [directionSupportSet_eq]
  decide

theorem zeroTrace_card (j : Fin 5) : (zeroTrace j).card = 6 := by
  fin_cases j <;> decide

theorem agreementWitness_card (j : Fin 5) : (agreementWitness j).card = 9 := by
  fin_cases j <;> decide

theorem receivedPolynomial_natDegree : receivedPolynomial.natDegree = 8 := by
  rw [receivedPolynomial]
  compute_degree!

theorem cubic_degree_lt_four (a0 a1 a2 a3 : F17) :
    (C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3).degree < 4 := by
  have h0 : (C a0).natDegree ≤ 3 := by
    simpa using (Polynomial.natDegree_C_mul_X_pow_le a0 0).trans (by omega)
  have h1 : (C a1 * X).natDegree ≤ 3 := by
    simpa using (Polynomial.natDegree_C_mul_X_pow_le a1 1).trans (by omega)
  have h2 : (C a2 * X ^ 2).natDegree ≤ 3 :=
    (Polynomial.natDegree_C_mul_X_pow_le a2 2).trans (by omega)
  have h3 : (C a3 * X ^ 3).natDegree ≤ 3 :=
    Polynomial.natDegree_C_mul_X_pow_le a3 3
  have hn :
      (C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3).natDegree ≤ 3 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        exact max_le h0 h1
      · exact h2
    · exact h3
  calc
    (C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3).degree ≤
        ((C a0 + C a1 * X + C a2 * X ^ 2 + C a3 * X ^ 3).natDegree :
          WithBot Nat) := Polynomial.degree_le_natDegree
    _ ≤ (3 : Nat) := by exact_mod_cast hn
    _ < (4 : Nat) := by norm_num

theorem witnessPolynomial_degree_lt_four (j : Fin 5) :
    (witnessPolynomial j).degree < 4 := by
  fin_cases j <;> exact cubic_degree_lt_four _ _ _ _

set_option maxHeartbeats 1000000 in
/-- Closed check of the degree-eight received polynomial on fixed coordinates. -/
theorem receivedPolynomial_eval_eq_u0_of_u1_eq_zero
    (i : Fin 16) (hi : u1 i = 0) :
    receivedPolynomial.eval (dom i) = u0 i := by
  fin_cases i <;> revert hi <;>
    norm_num [receivedPolynomial, dom, domainValues, u0, u1] <;>
    decide

set_option maxHeartbeats 1000000 in
/-- The six displayed fixed-coordinate agreements are exact. -/
theorem directionZeroAgreementSet_witnessCodeword
    (j : Fin 5) :
    directionZeroAgreementSet (witnessCodeword j) u0 u1 = zeroTrace j := by
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [directionZeroAgreementSet, directionZeroSet, witnessCodeword,
      witnessPolynomial, dom, domainValues, zeroTrace, u0, u1] <;>
    decide

set_option maxHeartbeats 1000000 in
/-- Closed check of all nine displayed agreements for every witness. -/
theorem witness_agreement
    (j : Fin 5) (i : Fin 16) (hi : i ∈ agreementWitness j) :
    witnessCodeword j i = u0 i + witnessScalar j * u1 i := by
  fin_cases j <;> fin_cases i <;>
    simp [agreementWitness, zeroTrace, movingTriple] at hi
  all_goals norm_num [witnessCodeword, witnessPolynomial, witnessScalar,
    dom, domainValues, u0, u1]
  all_goals decide

theorem witnessCodeword_mem_rsCode (j : Fin 5) :
    witnessCodeword j ∈
      (rsCode dom 4 : Submodule F17 (Fin 16 → F17)) := by
  exact ⟨witnessPolynomial j, witnessPolynomial_degree_lt_four j, rfl⟩

theorem witnessCodeword_mem_lineAppearingCodewords (j : Fin 5) :
    witnessCodeword j ∈ lineAppearingCodewords dom 4 9 u0 u1 := by
  rw [lineAppearingCodewords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, witnessCodeword_mem_rsCode j,
    witnessScalar j, ?_⟩
  have hsub : agreementWitness j ⊆
      agreeSet (witnessCodeword j)
        (fun i ↦ u0 i + witnessScalar j • u1 i) := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [smul_eq_mul] using witness_agreement j i hi
  have hcard := Finset.card_le_card hsub
  rw [agreementWitness_card] at hcard
  exact hcard

theorem witnessCodeword_mem_sixStratum (j : Fin 5) :
    witnessCodeword j ∈ zeroAgreementStratum dom 4 9 u0 u1 6 := by
  rw [zeroAgreementStratum, Finset.mem_filter]
  refine ⟨witnessCodeword_mem_lineAppearingCodewords j, ?_⟩
  rw [directionZeroAgreementSet_witnessCodeword, zeroTrace_card]

/-! ## Algebraic zero-direction safety -/

theorem natDegree_lt_four_of_degree_lt_four
    {p : F17[X]} (hp : p.degree < 4) : p.natDegree < 4 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp

theorem receivedPolynomial_ne_of_degree_lt_four
    {p : F17[X]} (hp : p.degree < 4) : receivedPolynomial ≠ p := by
  intro heq
  have hpNat := natDegree_lt_four_of_degree_lt_four hp
  have hdeg := congrArg Polynomial.natDegree heq
  rw [receivedPolynomial_natDegree] at hdeg
  omega

/-- The explicit line is safe from a nine-coordinate fixed-part saturation. -/
theorem zeroDirectionSafeLine : ZeroDirectionSafeLine dom 4 9 u0 u1 := by
  rintro c ⟨p, hp, rfl⟩
  let D := directionZeroAgreementSet
    (fun i ↦ p.eval (dom i)) u0 u1
  let Q := receivedPolynomial - p
  have hpNat := natDegree_lt_four_of_degree_lt_four hp
  have hQ0 : Q ≠ 0 := by
    apply sub_ne_zero.mpr
    exact receivedPolynomial_ne_of_degree_lt_four hp
  have hQdeg : Q.natDegree ≤ 8 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    rw [receivedPolynomial_natDegree]
    omega
  have hsub : D ⊆ domainRootSet dom Q := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    have hiZero : u1 i = 0 := by
      simpa only [directionZeroSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hiData.1
    have hiAgree : p.eval (dom i) = u0 i := hiData.2
    simp only [domainRootSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Q, eval_sub]
    rw [receivedPolynomial_eval_eq_u0_of_u1_eq_zero i hiZero,
      hiAgree, sub_self]
  have hroots : (domainRootSet dom Q).card ≤ Q.natDegree := by
    simpa only [domainRootSet] using
      ArkLib.CS25.card_domain_roots_le dom Q hQ0
  change D.card < 9
  calc
    D.card ≤ (domainRootSet dom Q).card := Finset.card_le_card hsub
    _ ≤ Q.natDegree := hroots
    _ ≤ 8 := hQdeg
    _ < 9 := by omega

/-! ## Five distinct members and the refutation -/

theorem witnessCodeword_injective : Function.Injective witnessCodeword := by
  let e : Fin 5 ↪ F17 := ⟨witnessScalar, by decide⟩
  have hvalue : ∀ j : Fin 5, witnessCodeword j 0 = witnessScalar j := by
    intro j
    have h := witness_agreement j 0 (by fin_cases j <;> decide)
    simpa [u0, u1] using h
  intro i j hij
  apply e.injective
  change witnessScalar i = witnessScalar j
  rw [← hvalue i, ← hvalue j, hij]

noncomputable def stratumEmbedding :
    Fin 5 ↪ {c : Fin 16 → F17 //
      c ∈ zeroAgreementStratum dom 4 9 u0 u1 6} where
  toFun j := ⟨witnessCodeword j, witnessCodeword_mem_sixStratum j⟩
  inj' := fun _ _ h ↦ witnessCodeword_injective (congrArg Subtype.val h)

theorem five_le_sixStratum_card :
    5 ≤ (zeroAgreementStratum dom 4 9 u0 u1 6).card := by
  have hcard := Fintype.card_le_of_injective
    stratumEmbedding stratumEmbedding.injective
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

theorem not_sixStratum_card_le_four :
    ¬ (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 4 := by
  have hfive := five_le_sixStratum_card
  omega

/-- **Bundled concrete refutation.**  Even on a zero-safe smooth-domain line,
support four does not force the `t = 6` stratum to have cardinality at most
four. -/
theorem supportFour_sixStratum_cap_four_refuted :
    ZeroDirectionSafeLine dom 4 9 u0 u1 ∧
      (directionSupportSet u1).card = 4 ∧
      4 < (zeroAgreementStratum dom 4 9 u0 u1 6).card := by
  exact ⟨zeroDirectionSafeLine, directionSupportSet_card, by
    have hfive := five_le_sixStratum_card
    omega⟩

#print axioms zeroDirectionSafeLine
#print axioms five_le_sixStratum_card
#print axioms supportFour_sixStratum_cap_four_refuted

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSixStratumRefuted
