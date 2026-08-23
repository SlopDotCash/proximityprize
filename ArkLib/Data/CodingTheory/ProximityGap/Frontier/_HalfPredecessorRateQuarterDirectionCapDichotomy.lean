/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterObtuse
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD

/-!
# Rate-quarter direction cap: exact dichotomy and a finite countermodel

The successor direction cap used by the obtuse-vector argument is **not** an
automatic consequence of the canonical bad-scalar rich-point family.  What
the no-joint clause really gives is the following punctured-core statement.
For every degree-`< k` direction polynomial `r`, every selected full agreement
has a coordinate outside the agreement core of `r` with the received
direction.

Consequently there is an exact, unconditional dichotomy:

* either every direction core has size at most `k+1`, so the obtuse-vector
  theorem applies;
* or some direction core has size at least `k+2`, and every selected bad
  scalar has a certified fresh coordinate outside that same core.

The final section proves that the first alternative cannot be inferred merely
from being at the rate-quarter half predecessor.  Over `F_5`, with length
`4`, dimension `1`, and threshold `3`, an explicit stack has an MCA-bad scalar
while its direction agrees with the zero polynomial on three coordinates.
Thus `DirectionAgreementCapSucc`, whose bound here is `2`, fails for the
literal canonical rich-point family.  The near-direction alternative is a
genuine branch, not a normalization one may assume without proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The coordinates on which a degree-bounded polynomial explains the
received direction row. -/
def directionAgreement (dom : ι ↪ F) (u1 : ι → F) (r : F[X]) : Finset ι :=
  Finset.univ.filter fun i => r.eval (dom i) = u1 i

/-- If a selected full agreement were contained in a direction agreement
core, then `q gamma - gamma*r` and `r` would jointly explain the two received
rows there.  The rich-family no-joint clause therefore supplies a coordinate
outside every such core. -/
theorem fullAgreement_not_subset_directionAgreement
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (r : F[X]) (hr : r.natDegree < k) :
    ¬ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ⊆
      directionAgreement dom (u 1) r := by
  intro hsubset
  let a : F[X] := family.q gamma - C gamma * r
  have hCr : (C gamma * r).natDegree ≤ r.natDegree :=
    natDegree_C_mul_le gamma r
  have ha : a.natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (family.degree_lt gamma hgamma)
        (lt_of_le_of_lt hCr hr))
  have hnotCore := not_subset_jointCore_of_not_pairJointAgreesOn
    dom (u 0) (u 1)
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    a r ha hr (family.noJoint gamma hgamma)
  apply hnotCore
  intro i hi
  have hdir := hsubset hi
  simp only [fullAgreement, directionAgreement, jointCore,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hdir ⊢
  refine ⟨?_, hdir⟩
  simp only [a, eval_sub, eval_mul, eval_C]
  rw [hi, hdir]
  ring

/-- Element form of `fullAgreement_not_subset_directionAgreement`. -/
theorem exists_fullAgreement_outside_directionAgreement
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (r : F[X]) (hr : r.natDegree < k) :
    ∃ i : ι,
      i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      i ∉ directionAgreement dom (u 1) r := by
  by_contra h
  push Not at h
  exact fullAgreement_not_subset_directionAgreement family hgamma r hr h

/-- **Exact direction-core dichotomy.**  Failure of the successor cap yields
one common exceptional core of size at least `k+2`; no-jointness certifies a
fresh coordinate outside it for every selected scalar. -/
theorem directionAgreementCapSucc_or_exceptionalCore
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    DirectionAgreementCapSucc dom (u 1) k ∨
      ∃ r : F[X], r.natDegree < k ∧
        k + 2 ≤ (directionAgreement dom (u 1) r).card ∧
        ∀ gamma ∈ family.G, ∃ i : ι,
          i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
          i ∉ directionAgreement dom (u 1) r := by
  by_cases hcap : DirectionAgreementCapSucc dom (u 1) k
  · exact Or.inl hcap
  · right
    rw [DirectionAgreementCapSucc] at hcap
    push Not at hcap
    obtain ⟨r, hr, hlarge⟩ := hcap
    refine ⟨r, hr, ?_, ?_⟩
    · simpa only [directionAgreement] using (show k + 2 ≤
          (Finset.univ.filter fun i => r.eval (dom i) = u 1 i).card by
        omega)
    · intro gamma hgamma
      exact exists_fullAgreement_outside_directionAgreement
        family hgamma r hr

/-! ## A literal finite rate-quarter countermodel -/

namespace Counterexample

/-- The five-element field used by the countermodel. -/
abbrev F5 := ZMod 5

local instance localInstance_HalfPredecessorRateQuarterDirectionCapDichotomy_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Four distinct evaluation points in `F_5`. -/
def dom : Fin 4 ↪ F5 :=
  ⟨![0, 1, 2, 3], by decide⟩

/-- A direction which agrees with the zero degree-`<1` polynomial on the
first three coordinates, but is nonconstant. -/
def uDir : Fin 4 → F5 := ![0, 0, 0, 1]

/-- The base row is identically zero. -/
def uBase : Fin 4 → F5 := 0

/-- The concrete received stack. -/
def u : WordStack F5 (Fin 2) (Fin 4) := ![uBase, uDir]

@[simp] theorem u_zero : u 0 = uBase := rfl
@[simp] theorem u_one : u 1 = uDir := rfl

/-- A three-coordinate witness has exactly the half-predecessor cardinality
at radius `1/4` and length four. -/
theorem card_condition {S : Finset (Fin 4)} (hS : S.card = 3) :
    ((1 : ℝ≥0) - (1 / 4 : ℝ≥0)) *
        (Fintype.card (Fin 4) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
  have hquarter : (1 / 4 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
    norm_num
  have hcalc :
      ((1 : ℝ≥0) - (1 / 4 : ℝ≥0)) *
          (Fintype.card (Fin 4) : ℝ≥0) = 3 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub hquarter]
    push_cast [Fintype.card_fin]
    norm_num
  rw [hcalc, hS]
  norm_num

/-- A degree-`<1` Reed--Solomon codeword is constant. -/
theorem codeword_eq_at
    {v : Fin 4 → F5}
    (hv : v ∈ ReedSolomon.code dom 1) (i j : Fin 4) :
    v i = v j := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  have hp0 : p.natDegree ≤ 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_le_zero hp0]
  simp [ReedSolomon.evalOnPoints]

/-- The direction is not jointly explainable on `{0,1,3}`. -/
theorem not_pairJoint_on_witness :
    ¬ pairJointAgreesOn
      ((ReedSolomon.code dom 1 : Submodule F5 (Fin 4 → F5)) :
        Set (Fin 4 → F5))
      {0, 1, 3} uBase uDir := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  have heq : v1 (0 : Fin 4) = v1 (3 : Fin 4) :=
    codeword_eq_at hv1 0 3
  have h0 := (hagree (0 : Fin 4) (by decide)).2
  have h3 := (hagree (3 : Fin 4) (by decide)).2
  exact (by decide : uDir 0 ≠ uDir 3) (h0.symm.trans (heq.trans h3))

/-- Scalar zero is genuinely MCA-bad at the rate-quarter half predecessor. -/
theorem mcaEvent_zero :
    mcaEvent
      ((ReedSolomon.code dom 1 : Submodule F5 (Fin 4 → F5)) :
        Set (Fin 4 → F5))
      (1 / 4) uBase uDir (0 : F5) := by
  refine ⟨{0, 1, 3}, card_condition (by decide),
    ⟨0, Submodule.zero_mem _, ?_⟩, not_pairJoint_on_witness⟩
  intro i hi
  simp [uBase]

/-- The successor direction cap fails: the zero polynomial agrees with
`uDir` on three coordinates, while `k+1=2`. -/
theorem not_directionAgreementCapSucc :
    ¬ DirectionAgreementCapSucc dom uDir 1 := by
  intro hcap
  have h := hcap (0 : F5[X]) (by norm_num)
  have hset :
      (Finset.univ.filter fun i : Fin 4 =>
        (0 : F5[X]).eval (dom i) = uDir i) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp [uDir]
  rw [hset] at h
  have hcard : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
  omega

/-- **Concrete refutation of automatic cap derivation.**  All rate-quarter
half-predecessor arithmetic holds, scalar zero belongs to the literal
canonical bad-scalar family, yet `DirectionAgreementCapSucc` fails. -/
theorem canonical_family_counterexample :
    let family := canonicalBadScalarRichPointFamily dom (1 / 4) u
      (by norm_num : 1 ≤ 1)
    Fintype.card (Fin 4) = 2 * 2 ∧
      2 * 1 ≤ 2 ∧
      ⌈((1 : ℝ≥0) - (1 / 4 : ℝ≥0)) *
        (Fintype.card (Fin 4) : ℝ≥0)⌉₊ = 2 + 1 ∧
      (0 : F5) ∈ family.G ∧
      ¬ DirectionAgreementCapSucc dom (u 1) 1 := by
  dsimp only
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have hquarter : (1 / 4 : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
      norm_num
    have hcalc :
        ((1 : ℝ≥0) - (1 / 4 : ℝ≥0)) *
            (Fintype.card (Fin 4) : ℝ≥0) = 3 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_mul, NNReal.coe_sub hquarter]
      push_cast [Fintype.card_fin]
      norm_num
    rw [hcalc]
    norm_num
  · rw [(canonicalBadScalarRichPointFamily dom (1 / 4) u
      (by norm_num : 1 ≤ 1)).mem_G_iff]
    simpa only [u_zero, u_one] using mcaEvent_zero
  · simpa only [u_one] using not_directionAgreementCapSucc

end Counterexample

/-! ## A relevant-secant countermodel at `n=8`, `k=2`

The preceding example has only one exhibited bad scalar.  The next example
rules out the stronger hope that the cap might automatically hold merely for
secant slopes between distinct members of the canonical family.  Three bad
scalars have the same forced decoded polynomial.  Hence their secant slope is
zero, whose direction core has cardinality four, namely `k+2`.
-/

namespace SecantCounterexample

open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

abbrev F11 := ZMod 11

local instance localInstance_HalfPredecessorRateQuarterDirectionCapDichotomy_2 : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Eight distinct evaluation points in `F_11`. -/
def dom : Fin 8 ↪ F11 :=
  ⟨![0, 1, 2, 3, 4, 5, 6, 7], by decide⟩

/-- Probe-found base row. -/
def uBase : Fin 8 → F11 := ![0, 5, 5, 6, 7, 3, 7, 0]

/-- The near-code direction.  Its zero core is `{3,5,6,7}`. -/
def uDir : Fin 8 → F11 := ![1, 10, 7, 0, 2, 0, 0, 0]

def u : WordStack F11 (Fin 2) (Fin 8) := ![uBase, uDir]

@[simp] theorem u_zero : u 0 = uBase := rfl
@[simp] theorem u_one : u 1 = uDir := rfl

/-- The common forced decoded polynomial `5+4X`. -/
noncomputable def q0 : F11[X] := C 5 + C 4 * X

def S5 : Finset (Fin 8) := {0, 3, 5, 6, 7}
def S7 : Finset (Fin 8) := {1, 3, 4, 5, 6, 7}
def S9 : Finset (Fin 8) := {2, 3, 5, 6, 7}

theorem threshold_eq_five :
    ⌈((1 : ℝ≥0) - (3 / 8 : ℝ≥0)) *
      (Fintype.card (Fin 8) : ℝ≥0)⌉₊ = 5 := by
  have h38 : (3 / 8 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  have hcalc :
      ((1 : ℝ≥0) - (3 / 8 : ℝ≥0)) *
          (Fintype.card (Fin 8) : ℝ≥0) = 5 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub h38]
    push_cast [Fintype.card_fin]
    norm_num
  rw [hcalc]
  norm_num

theorem witness_card_condition
    {S : Finset (Fin 8)} (hS : 5 ≤ S.card) :
    ((1 : ℝ≥0) - (3 / 8 : ℝ≥0)) *
        (Fintype.card (Fin 8) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
  rw [← Nat.ceil_le]
  simpa only [threshold_eq_five] using hS

/-- A degree-`<2` codeword which vanishes at coordinates `3` and `5` is
identically zero. -/
theorem codeword_eq_zero_of_eq_zero_at_three_five
    {v : Fin 8 → F11} (hv : v ∈ ReedSolomon.code dom 2)
    (h3 : v 3 = 0) (h5 : v 5 = 0) : v = 0 := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv
  obtain ⟨p, hp, hv⟩ := hv
  have hp0 : p = 0 :=
    eq_zero_of_degree_lt_of_vanishes_on hp ({3, 5} : Finset (Fin 8))
      (by decide) (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [hv, ReedSolomon.evalOnPoints] using h3
        · simpa [hv, ReedSolomon.evalOnPoints] using h5)
  rw [hv, hp0]
  funext i
  simp [ReedSolomon.evalOnPoints]

/-- Any witness containing the zero-core anchors `3,5` and one nonzero
direction coordinate is non-joint. -/
theorem not_pairJoint_of_mem_core_and_nonzero
    (S : Finset (Fin 8)) (j : Fin 8)
    (h3S : (3 : Fin 8) ∈ S) (h5S : (5 : Fin 8) ∈ S)
    (hjS : j ∈ S) (hj : uDir j ≠ 0) :
    ¬ pairJointAgreesOn
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) S uBase uDir := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  have hv13 : v1 3 = 0 := by
    simpa [uDir] using (hagree 3 h3S).2
  have hv15 : v1 5 = 0 := by
    simpa [uDir] using (hagree 5 h5S).2
  have hv1zero := codeword_eq_zero_of_eq_zero_at_three_five hv1 hv13 hv15
  have hvj := (hagree j hjS).2
  rw [hv1zero] at hvj
  exact hj (by simpa using hvj.symm)

theorem q0_degree_lt_two : q0.degree < (2 : ℕ) := by
  have hle : q0.degree ≤ (1 : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_add_le _ _) ?_
    refine max_le (le_trans Polynomial.degree_C_le (by norm_num)) ?_
    refine le_trans (Polynomial.degree_mul_le _ _) ?_
    refine le_trans
      (add_le_add Polynomial.degree_C_le Polynomial.degree_X_le) ?_
    norm_num
  exact lt_of_le_of_lt hle (by norm_num)

/-- Explicit decode at scalar `5`. -/
noncomputable def decode5 : McaDecode dom 2 (3 / 8) u (5 : F11) where
  S := S5
  P := q0
  hdeg := q0_degree_lt_two
  hcard := witness_card_condition (by decide : 5 ≤ S5.card)
  hagree := by
    intro i hi
    fin_cases i <;> simp [S5] at hi
    all_goals simp [q0, u, uBase, uDir, dom]
    all_goals decide
  hnjp := by
    simpa only [u_zero, u_one] using
      not_pairJoint_of_mem_core_and_nonzero S5 0
        (by decide) (by decide) (by decide) (by decide)

/-- Explicit decode at scalar `7`. -/
noncomputable def decode7 : McaDecode dom 2 (3 / 8) u (7 : F11) where
  S := S7
  P := q0
  hdeg := q0_degree_lt_two
  hcard := witness_card_condition (by decide : 5 ≤ S7.card)
  hagree := by
    intro i hi
    fin_cases i <;> simp [S7] at hi
    all_goals simp [q0, u, uBase, uDir, dom]
    all_goals decide
  hnjp := by
    simpa only [u_zero, u_one] using
      not_pairJoint_of_mem_core_and_nonzero S7 1
        (by decide) (by decide) (by decide) (by decide)

/-- Explicit decode at scalar `9`. -/
noncomputable def decode9 : McaDecode dom 2 (3 / 8) u (9 : F11) where
  S := S9
  P := q0
  hdeg := q0_degree_lt_two
  hcard := witness_card_condition (by decide : 5 ≤ S9.card)
  hagree := by
    intro i hi
    fin_cases i <;> simp [S9] at hi
    all_goals simp [q0, u, uBase, uDir, dom]
    all_goals decide
  hnjp := by
    simpa only [u_zero, u_one] using
      not_pairJoint_of_mem_core_and_nonzero S9 2
        (by decide) (by decide) (by decide) (by decide)

theorem mcaEvent5 :
    mcaEvent ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
      Set (Fin 8 → F11)) (3 / 8) (u 0) (u 1) (5 : F11) :=
  decode5.mcaEvent

theorem mcaEvent7 :
    mcaEvent ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
      Set (Fin 8 → F11)) (3 / 8) (u 0) (u 1) (7 : F11) :=
  decode7.mcaEvent

theorem mcaEvent9 :
    mcaEvent ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
      Set (Fin 8 → F11)) (3 / 8) (u 0) (u 1) (9 : F11) :=
  decode9.mcaEvent

/-- At this threshold, the decoded polynomial of each scalar is unique. -/
theorem decode_window :
    Fintype.card (Fin 8) + 2 ≤
      2 * ⌈((1 : ℝ≥0) - (3 / 8 : ℝ≥0)) *
        (Fintype.card (Fin 8) : ℝ≥0)⌉₊ := by
  rw [threshold_eq_five]
  norm_num [Fintype.card_fin]

/-- Any canonical selection at scalar `5` is forced to be `q0`. -/
theorem canonical_q5_eq_q0 :
    (canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)).q 5 = q0 := by
  have hbad : (5 : F11) ∈ badScalars dom 2 (3 / 8) u :=
    (mem_badScalars_iff dom 2 (3 / 8) u 5).mpr mcaEvent5
  change selectedPolynomial dom 2 (3 / 8) u 5 = q0
  rw [selectedPolynomial_eq dom 2 (3 / 8) u hbad]
  exact mcaDecode_P_eq_of_window decode_window
    (selectedDecode dom 2 (3 / 8) u 5 hbad) decode5

/-- Any canonical selection at scalar `7` is forced to be `q0`. -/
theorem canonical_q7_eq_q0 :
    (canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)).q 7 = q0 := by
  have hbad : (7 : F11) ∈ badScalars dom 2 (3 / 8) u :=
    (mem_badScalars_iff dom 2 (3 / 8) u 7).mpr mcaEvent7
  change selectedPolynomial dom 2 (3 / 8) u 7 = q0
  rw [selectedPolynomial_eq dom 2 (3 / 8) u hbad]
  exact mcaDecode_P_eq_of_window decode_window
    (selectedDecode dom 2 (3 / 8) u 7 hbad) decode7

/-- Any canonical selection at scalar `9` is forced to be `q0`. -/
theorem canonical_q9_eq_q0 :
    (canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)).q 9 = q0 := by
  have hbad : (9 : F11) ∈ badScalars dom 2 (3 / 8) u :=
    (mem_badScalars_iff dom 2 (3 / 8) u 9).mpr mcaEvent9
  change selectedPolynomial dom 2 (3 / 8) u 9 = q0
  rw [selectedPolynomial_eq dom 2 (3 / 8) u hbad]
  exact mcaDecode_P_eq_of_window decode_window
    (selectedDecode dom 2 (3 / 8) u 9 hbad) decode9

theorem fullAgreement5_eq :
    fullAgreement dom (u 0) (u 1) 5 q0 = S5 := by
  ext i
  fin_cases i <;> simp [fullAgreement, S5, q0, u, uBase, uDir, dom]
  all_goals decide

theorem fullAgreement7_eq :
    fullAgreement dom (u 0) (u 1) 7 q0 = S7 := by
  ext i
  fin_cases i <;> simp [fullAgreement, S7, q0, u, uBase, uDir, dom]
  all_goals decide

/-- **Relevant-secant refutation.**  Scalars `5` and `7` lie in the literal
canonical family, and their selected full agreements meet in four coordinates
(`k+2`), not at most `k+1=3`.  Their selected polynomials are equal, so the
offending direction polynomial is exactly their canonical secant slope zero. -/
theorem canonical_pair_intersection_eq_four :
    let family := canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)
    (5 : F11) ∈ family.G ∧
      (7 : F11) ∈ family.G ∧
      family.q 5 = family.q 7 ∧
      (fullAgreement dom (u 0) (u 1) 5 (family.q 5) ∩
        fullAgreement dom (u 0) (u 1) 7 (family.q 7)).card = 4 := by
  dsimp only
  refine ⟨?_, ?_, canonical_q5_eq_q0.trans canonical_q7_eq_q0.symm, ?_⟩
  · rw [(canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)).mem_G_iff]
    exact mcaEvent5
  · rw [(canonicalBadScalarRichPointFamily dom (3 / 8) u
      (by norm_num : 1 ≤ 2)).mem_G_iff]
    exact mcaEvent7
  · rw [canonical_q5_eq_q0, canonical_q7_eq_q0,
      fullAgreement5_eq, fullAgreement7_eq]
    decide

end SecantCounterexample

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
#print axioms fullAgreement_not_subset_directionAgreement
#print axioms exists_fullAgreement_outside_directionAgreement
#print axioms directionAgreementCapSucc_or_exceptionalCore
#print axioms Counterexample.mcaEvent_zero
#print axioms Counterexample.not_directionAgreementCapSucc
#print axioms Counterexample.canonical_family_counterexample
#print axioms SecantCounterexample.decode5
#print axioms SecantCounterexample.decode7
#print axioms SecantCounterexample.decode9
#print axioms SecantCounterexample.canonical_q5_eq_q0
#print axioms SecantCounterexample.canonical_q7_eq_q0
#print axioms SecantCounterexample.canonical_q9_eq_q0
#print axioms SecantCounterexample.canonical_pair_intersection_eq_four
