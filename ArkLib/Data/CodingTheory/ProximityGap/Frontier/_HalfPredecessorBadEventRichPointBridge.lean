/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel

/-!
# Bad MCA events as rich lifted Reed--Solomon points

This file is the event-to-incidence bridge for the rate-`1/16`
half-predecessor argument.  For every bad scalar `gamma`, it chooses one
`McaDecode` witness and replaces its witness support by the polynomial's full
agreement set.  The enlargement preserves both facts needed downstream:

* the full agreement set still has at least
  `ceil ((1-delta) * n)` coordinates;
* it is still not jointly explained by two Reed--Solomon codewords.

`BadScalarRichPointFamily` packages the resulting finite family of lifted
points `(gamma, q gamma)`.  Its scalar set is exactly the bad-event filter, so
counting bad scalars is definitionally reduced to counting this rich-point
family.  The final lemmas turn its richness and no-joint clauses into the
`hlarge` and `hproper` hypotheses of
`HalfPredecessorLineCoreGeometry.line_card_mul_max_add_core_le` on every
polynomial-line subfamily.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The finite set of scalars for which the MCA bad event holds. -/
noncomputable def badScalars (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) : Finset F :=
  Finset.univ.filter fun gamma : F =>
    mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
      delta (u 0) (u 1) gamma

@[simp]
theorem mem_badScalars_iff (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (gamma : F) :
    gamma ∈ badScalars dom k delta u ↔
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma := by
  simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and]

/-- One decoded polynomial witness, selected for a bad scalar. -/
noncomputable def selectedDecode (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (gamma : F)
    (hgamma : gamma ∈ badScalars dom k delta u) :
    McaDecode dom k delta u gamma :=
  Classical.choice <| exists_mcaDecode_of_mcaEvent <|
    (mem_badScalars_iff dom k delta u gamma).mp hgamma

/-- The selected decoded polynomial on bad scalars, extended by zero elsewhere. -/
noncomputable def selectedPolynomial (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (gamma : F) : F[X] :=
  if hgamma : gamma ∈ badScalars dom k delta u then
    (selectedDecode dom k delta u gamma hgamma).P
  else
    0

theorem selectedPolynomial_eq (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    selectedPolynomial dom k delta u gamma =
      (selectedDecode dom k delta u gamma hgamma).P := by
  simp only [selectedPolynomial, dif_pos hgamma]

/-- The full coordinate set on which the selected polynomial agrees with the
received affine word. -/
noncomputable def selectedFullAgreement (dom : ι ↪ F) (k : ℕ)
    (delta : ℝ≥0) (u : WordStack F (Fin 2) ι) (gamma : F) : Finset ι :=
  fullAgreement dom (u 0) (u 1) gamma
    (selectedPolynomial dom k delta u gamma)

/-- The original decode support is contained in the selected polynomial's full
agreement set. -/
theorem selectedDecode_support_subset_fullAgreement
    (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    (selectedDecode dom k delta u gamma hgamma).S ⊆
      selectedFullAgreement dom k delta u gamma := by
  intro i hi
  rw [selectedFullAgreement, fullAgreement, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [selectedPolynomial_eq dom k delta u hgamma]
  simpa only [smul_eq_mul] using
    (selectedDecode dom k delta u gamma hgamma).hagree i hi

/-- A selected polynomial has the Reed--Solomon degree bound in `degree` form. -/
theorem selectedPolynomial_degree_lt
    (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    (selectedPolynomial dom k delta u gamma).degree < k := by
  rw [selectedPolynomial_eq dom k delta u hgamma]
  exact (selectedDecode dom k delta u gamma hgamma).hdeg

/-- For positive dimension, a selected polynomial also has `natDegree < k`. -/
theorem selectedPolynomial_natDegree_lt
    (dom : ι ↪ F) {k : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    (selectedPolynomial dom k delta u gamma).natDegree < k := by
  by_cases hzero : selectedPolynomial dom k delta u gamma = 0
  · simp only [hzero, natDegree_zero]
    exact hk
  · rw [natDegree_lt_iff_degree_lt hzero]
    exact selectedPolynomial_degree_lt dom k delta u hgamma

/-- The full agreement set retains the ceiling threshold from the original bad
event witness. -/
theorem threshold_le_selectedFullAgreement_card
    (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ ≤
      (selectedFullAgreement dom k delta u gamma).card := by
  calc
    ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ ≤
        (selectedDecode dom k delta u gamma hgamma).S.card :=
      Nat.ceil_le.mpr (selectedDecode dom k delta u gamma hgamma).hcard
    _ ≤ (selectedFullAgreement dom k delta u gamma).card :=
      Finset.card_le_card <|
        selectedDecode_support_subset_fullAgreement dom k delta u hgamma

/-- Enlarging the decode support to full agreement cannot create a joint
explanation: any explanation on the larger set would restrict to the original
witness support. -/
theorem not_pairJointAgreesOn_selectedFullAgreement
    (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) {gamma : F}
    (hgamma : gamma ∈ badScalars dom k delta u) :
    ¬ pairJointAgreesOn ((ReedSolomon.code dom k : Set (ι → F)))
      (selectedFullAgreement dom k delta u gamma) (u 0) (u 1) := by
  intro hjoint
  apply (selectedDecode dom k delta u gamma hgamma).hnjp
  obtain ⟨v0, hv0, v1, hv1, hagree⟩ := hjoint
  refine ⟨v0, hv0, v1, hv1, ?_⟩
  intro i hi
  exact hagree i <|
    selectedDecode_support_subset_fullAgreement dom k delta u hgamma hi

/-- A finite family of degree-`< k` lifted points, indexed by exactly the bad
scalars, with full agreement sets carrying the threshold and no-joint clauses. -/
structure BadScalarRichPointFamily (dom : ι ↪ F) (k : ℕ) (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) where
  /-- The selected scalar parameters. -/
  G : Finset F
  /-- The selected polynomial above each scalar. -/
  q : F → F[X]
  /-- The scalar set is exactly the MCA bad-event set. -/
  mem_G_iff : ∀ gamma : F, gamma ∈ G ↔
    mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
      delta (u 0) (u 1) gamma
  /-- Every selected polynomial has degree `< k`. -/
  degree_lt : ∀ gamma ∈ G, (q gamma).natDegree < k
  /-- Every selected point is rich at the bad-event threshold. -/
  threshold_le : ∀ gamma ∈ G,
    ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ ≤
      (fullAgreement dom (u 0) (u 1) gamma (q gamma)).card
  /-- No selected full agreement set has a joint Reed--Solomon explanation. -/
  noJoint : ∀ gamma ∈ G,
    ¬ pairJointAgreesOn ((ReedSolomon.code dom k : Set (ι → F)))
      (fullAgreement dom (u 0) (u 1) gamma (q gamma)) (u 0) (u 1)

/-- The canonical rich-point family obtained by choosing one decode for every
bad scalar. -/
noncomputable def canonicalBadScalarRichPointFamily
    (dom : ι ↪ F) {k : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k) :
    BadScalarRichPointFamily dom k delta u where
  G := badScalars dom k delta u
  q := selectedPolynomial dom k delta u
  mem_G_iff := mem_badScalars_iff dom k delta u
  degree_lt := fun _gamma hgamma =>
    selectedPolynomial_natDegree_lt dom delta u hk hgamma
  threshold_le := fun _gamma hgamma =>
    threshold_le_selectedFullAgreement_card dom k delta u hgamma
  noJoint := fun _gamma hgamma =>
    not_pairJointAgreesOn_selectedFullAgreement dom k delta u hgamma

/-- Every packaged family has the same scalar set, namely `badScalars`. -/
theorem BadScalarRichPointFamily.G_eq_badScalars
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    family.G = badScalars dom k delta u := by
  ext gamma
  exact (family.mem_G_iff gamma).trans
    (mem_badScalars_iff dom k delta u gamma).symm

/-- **Bad-count reduction.** For positive Reed--Solomon dimension, the literal
bad-event filter is the scalar projection of a finite rich-point family with
all polynomial, threshold, and no-joint witnesses exposed. -/
theorem exists_richPointFamily_with_badScalar_count
    (dom : ι ↪ F) {k : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k) :
    ∃ family : BadScalarRichPointFamily dom k delta u,
      (Finset.univ.filter fun gamma : F =>
        mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
          delta (u 0) (u 1) gamma).card = family.G.card := by
  exact ⟨canonicalBadScalarRichPointFamily dom delta u hk, rfl⟩

/-- If a coordinate set has no joint Reed--Solomon explanation, it cannot be
contained in the joint core of a degree-`< k` polynomial line. -/
theorem not_subset_jointCore_of_not_pairJointAgreesOn
    (dom : ι ↪ F) (u0 u1 : ι → F) {k : ℕ}
    (A : Finset ι) (a r : F[X])
    (ha : a.natDegree < k) (hr : r.natDegree < k)
    (hno : ¬ pairJointAgreesOn
      ((ReedSolomon.code dom k : Set (ι → F))) A u0 u1) :
    ¬ A ⊆ jointCore dom u0 u1 a r := by
  intro hsubset
  apply hno
  refine ⟨(fun i => a.eval (dom i)), ?_,
    (fun i => r.eval (dom i)), ?_, ?_⟩
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      a ha fun _ => rfl
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      r hr fun _ => rfl
  · intro i hi
    have hcore := hsubset hi
    simpa only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcore

/-- Richness supplies the `hlarge` hypothesis of line-core packing on any
subfamily whose selected polynomials lie on one polynomial line. -/
theorem BadScalarRichPointFamily.line_hlarge
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (a r : F[X]) (Gline : Finset F)
    (hG : Gline ⊆ family.G)
    (hline : ∀ gamma ∈ Gline,
      family.q gamma = a + C gamma * r) :
    ∀ gamma ∈ Gline,
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ ≤
        (fullAgreement dom (u 0) (u 1) gamma
          (a + C gamma * r)).card := by
  intro gamma hgamma
  rw [← hline gamma hgamma]
  exact family.threshold_le gamma (hG hgamma)

/-- The no-joint clause supplies the `hproper` hypothesis of line-core packing
on any degree-`< k` polynomial-line subfamily. -/
theorem BadScalarRichPointFamily.line_hproper
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (a r : F[X]) (Gline : Finset F)
    (ha : a.natDegree < k) (hr : r.natDegree < k)
    (hG : Gline ⊆ family.G)
    (hline : ∀ gamma ∈ Gline,
      family.q gamma = a + C gamma * r) :
    ∀ gamma ∈ Gline,
      ¬ fullAgreement dom (u 0) (u 1) gamma
          (a + C gamma * r) ⊆
        jointCore dom (u 0) (u 1) a r := by
  intro gamma hgamma
  rw [← hline gamma hgamma]
  exact not_subset_jointCore_of_not_pairJointAgreesOn
    dom (u 0) (u 1)
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    a r ha hr (family.noJoint gamma (hG hgamma))

/-- **Direct geometry handoff.** Every polynomial-line subfamily of the
bad-scalar rich-point family satisfies the exact fresh-fibre packing inequality
proved in `_HalfPredecessorLineCoreGeometry`. -/
theorem BadScalarRichPointFamily.line_core_packing
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (a r : F[X]) (Gline : Finset F)
    (ha : a.natDegree < k) (hr : r.natDegree < k)
    (hG : Gline ⊆ family.G)
    (hline : ∀ gamma ∈ Gline,
      family.q gamma = a + C gamma * r) :
    Gline.card *
        max 1 (⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ -
          (jointCore dom (u 0) (u 1) a r).card) +
      (jointCore dom (u 0) (u 1) a r).card ≤ Fintype.card ι := by
  exact line_card_mul_max_add_core_le dom (u 0) (u 1) a r Gline
    ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊
    (family.line_hlarge a r Gline hG hline)
    (family.line_hproper a r Gline ha hr hG hline)

end ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge.exists_richPointFamily_with_badScalar_count
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge.BadScalarRichPointFamily.line_core_packing
