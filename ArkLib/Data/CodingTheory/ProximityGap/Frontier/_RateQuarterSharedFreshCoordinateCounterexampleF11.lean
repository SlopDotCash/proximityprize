/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CAPairExtractionEngine
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# A small Reed--Solomon shared-fresh-coordinate counterexample

This file kernel-checks the exact `RS[8,2]` configuration found by
`scripts/probes/probe_rate_quarter_p1_shared_fresh_coordinate.py`.  Over `F_11`, three distinct
MCA-bad scalars at radius `1/2` have explicit four-coordinate witnesses which all contain
coordinate `4`.  A known joint codeword pair agrees on exactly `{0,1,2,3}`, so coordinate `4`
is genuinely fresh for that pair.

This refutes a universal Reed--Solomon lemma saying that three bad scalars can never share one
fresh coordinate, even at rate `2/8 = 1/4`.  It does **not** refute or prove the open P1
predecessor statement: the P1 length, threshold, field, and domain hypotheses are absent here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open Round17CAPair
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.RateQuarterSharedFreshCoordinateCounterexampleF11

abbrev F11 := ZMod 11
abbrev I8 := Fin 8

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The eight distinct evaluation points `0,1,...,7` in `F_11`. -/
def dom : I8 ↪ F11 := ⟨fun i ↦ (i : F11), by decide⟩

/-- The literal degree-`<2` Reed--Solomon code on `dom`. -/
noncomputable abbrev C : Submodule F11 (I8 → F11) := ReedSolomon.code dom 2

/-- Evaluation of the affine polynomial `a + b X`. -/
def lineEval (a b : F11) : I8 → F11 := fun i ↦ a + b * dom i

theorem lineEval_mem (a b : F11) : lineEval a b ∈ C := by
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
    (Polynomial.C b * Polynomial.X + Polynomial.C a)
  · exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by norm_num)
  · intro i
    simp [lineEval]
    ring

/-- Membership in this concrete code is exactly affinity on the evaluation domain. -/
theorem mem_C_iff_affine (w : I8 → F11) :
    w ∈ C ↔ ∃ a b : F11, ∀ i, w i = lineEval a b i := by
  constructor
  · intro hw
    change w ∈ ReedSolomon.code dom 2 at hw
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    refine ⟨p.coeff 0, p.coeff 1, fun i ↦ ?_⟩
    have hp' : p.natDegree ≤ 1 := by omega
    have hpEq : p = Polynomial.C (p.coeff 1) * Polynomial.X +
        Polynomial.C (p.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one hp'
    change p.eval (dom i) = p.coeff 0 + p.coeff 1 * dom i
    conv_lhs => rw [hpEq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  · rintro ⟨a, b, hw⟩
    have hfun : w = lineEval a b := funext hw
    rw [hfun]
    exact lineEval_mem a b

/-- Explainability of one received row by an affine polynomial on a coordinate set. -/
def ExplainableOn (S : Finset I8) (u : I8 → F11) : Prop :=
  ∃ a b : F11, ∀ i ∈ S, lineEval a b i = u i

instance (S : Finset I8) (u : I8 → F11) : Decidable (ExplainableOn S u) := by
  unfold ExplainableOn
  infer_instance

/-- Failure to explain the first row already forbids a joint Reed--Solomon explanation. -/
theorem not_pairJointAgreesOn_of_row0
    {S : Finset I8} {u₀ u₁ : I8 → F11} (h : ¬ ExplainableOn S u₀) :
    ¬ pairJointAgreesOn (C : Set (I8 → F11)) S u₀ u₁ := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  obtain ⟨a, b, hv⟩ := (mem_C_iff_affine v₀).mp hv₀
  apply h
  exact ⟨a, b, fun i hi ↦ (hv i).symm.trans (hagree i hi).1⟩

def u₀ : I8 → F11 := ![1, 3, 5, 7, 1, 10, 2, 3]
def u₁ : I8 → F11 := ![3, 4, 5, 6, 1, 8, 10, 7]

def q₀ : I8 → F11 := lineEval 1 2
def q₁ : I8 → F11 := lineEval 3 1

def J : Finset I8 := {0, 1, 2, 3}
def shared : I8 := 4

def S₁ : Finset I8 := {0, 4, 5, 6}
def S₂ : Finset I8 := {1, 4, 5, 7}
def S₃ : Finset I8 := {2, 4, 6, 7}

def w₁ : I8 → F11 := lineEval 4 5
def w₂ : I8 → F11 := lineEval 10 1
def w₃ : I8 → F11 := lineEval 3 3

/-- The reference pair jointly explains the stack on the four-coordinate set `J`. -/
theorem knownJointAgreement :
    pairJointAgreesOn (C : Set (I8 → F11)) J u₀ u₁ := by
  refine ⟨q₀, by simpa [q₀] using lineEval_mem 1 2,
    q₁, by simpa [q₁] using lineEval_mem 3 1, ?_⟩
  decide

/-- `J` is exactly, rather than merely a subset of, the reference pair's joint-agreement set. -/
theorem maximalJointSet_eq_J : jointAgreeSet u₀ u₁ q₀ q₁ = J := by
  decide

theorem half_mass :
    (1 - (1 / 2 : ℝ≥0)) * Fintype.card I8 = 4 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
  norm_num [I8]

theorem not_joint_S₁ :
    ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₁ u₀ u₁ :=
  not_pairJointAgreesOn_of_row0 (by decide)

theorem not_joint_S₂ :
    ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₂ u₀ u₁ :=
  not_pairJointAgreesOn_of_row0 (by decide)

theorem not_joint_S₃ :
    ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₃ u₀ u₁ :=
  not_pairJointAgreesOn_of_row0 (by decide)

/-- The first explicit half-radius witness. -/
theorem witness_one :
    (S₁.card : ℝ≥0) ≥ (1 - (1 / 2 : ℝ≥0)) * Fintype.card I8 ∧
      w₁ ∈ C ∧ (∀ i ∈ S₁, w₁ i = u₀ i + (1 : F11) • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₁ u₀ u₁ := by
  refine ⟨by rw [half_mass, show S₁.card = 4 by decide]; norm_num,
    by simpa [w₁] using lineEval_mem 4 5,
    by decide, not_joint_S₁⟩

/-- The second explicit half-radius witness. -/
theorem witness_two :
    (S₂.card : ℝ≥0) ≥ (1 - (1 / 2 : ℝ≥0)) * Fintype.card I8 ∧
      w₂ ∈ C ∧ (∀ i ∈ S₂, w₂ i = u₀ i + (2 : F11) • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₂ u₀ u₁ := by
  refine ⟨by rw [half_mass, show S₂.card = 4 by decide]; norm_num,
    by simpa [w₂] using lineEval_mem 10 1,
    by decide, not_joint_S₂⟩

/-- The third explicit half-radius witness. -/
theorem witness_three :
    (S₃.card : ℝ≥0) ≥ (1 - (1 / 2 : ℝ≥0)) * Fintype.card I8 ∧
      w₃ ∈ C ∧ (∀ i ∈ S₃, w₃ i = u₀ i + (3 : F11) • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (I8 → F11)) S₃ u₀ u₁ := by
  refine ⟨by rw [half_mass, show S₃.card = 4 by decide]; norm_num,
    by simpa [w₃] using lineEval_mem 3 3,
    by decide, not_joint_S₃⟩

theorem mcaEvent_one :
    mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 1 := by
  obtain ⟨hcard, hmem, hagree, hno⟩ := witness_one
  exact ⟨S₁, hcard, ⟨w₁, hmem, hagree⟩, hno⟩

theorem mcaEvent_two :
    mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 2 := by
  obtain ⟨hcard, hmem, hagree, hno⟩ := witness_two
  exact ⟨S₂, hcard, ⟨w₂, hmem, hagree⟩, hno⟩

theorem mcaEvent_three :
    mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 3 := by
  obtain ⟨hcard, hmem, hagree, hno⟩ := witness_three
  exact ⟨S₃, hcard, ⟨w₃, hmem, hagree⟩, hno⟩

/-- Three distinct bad scalars have literal witnesses containing the same coordinate outside the
maximal joint-agreement set of the known pair. -/
theorem shared_fresh_triple :
    (1 : F11) ≠ 2 ∧ (1 : F11) ≠ 3 ∧ (2 : F11) ≠ 3 ∧
      shared ∉ J ∧ shared ∈ S₁ ∧ shared ∈ S₂ ∧ shared ∈ S₃ ∧
      pairJointAgreesOn (C : Set (I8 → F11)) J u₀ u₁ ∧
      jointAgreeSet u₀ u₁ q₀ q₁ = J ∧
      mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 1 ∧
      mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 2 ∧
      mcaEvent (F := F11) (C : Set (I8 → F11)) (1 / 2) u₀ u₁ 3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    knownJointAgreement, maximalJointSet_eq_J, mcaEvent_one, mcaEvent_two, mcaEvent_three⟩

end ArkLib.ProximityGap.Frontier.RateQuarterSharedFreshCoordinateCounterexampleF11

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterSharedFreshCoordinateCounterexampleF11
#print axioms knownJointAgreement
#print axioms maximalJointSet_eq_J
#print axioms mcaEvent_one
#print axioms mcaEvent_two
#print axioms mcaEvent_three
#print axioms shared_fresh_triple
