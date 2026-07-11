/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceOperator
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceUnrestrictedKernelRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallSubsetRankLocalization
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointUpper

/-!
# P1 received-word witnesses to the divided-difference rank operator

The campaign naturally records one coordinate witness set `witness j` for
each decoded label.  The block-Vandermonde operator instead expects, at every
coordinate, the finite set of labels incident there.  This file gives the
exact transpose and wires supported received-word agreement into the operator
kernel.  At literal P1 size it also transports the sharp singleton-Hall census:
two gauge anchors cover every singleton exception.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterReceivedWordRankConnector

open SupportDividedDifferenceOperator
open SupportDividedDifferenceUnrestrictedKernelRefuted
open P1RateQuarterSmallSubsetRankLocalization
open P1RateQuarterAgreementOverlapGraph

/-- Transpose label-indexed witness sets into coordinate-indexed supports. -/
def transposeWitnessSupport
    {X J : Type} [Fintype J] [DecidableEq X] [DecidableEq J]
    (witness : J → Finset X) (x : X) : Finset J :=
  Finset.univ.filter fun j => x ∈ witness j

@[simp]
theorem mem_transposeWitnessSupport_iff
    {X J : Type} [Fintype J] [DecidableEq X] [DecidableEq J]
    (witness : J → Finset X) (x : X) (j : J) :
    j ∈ transposeWitnessSupport witness x ↔ x ∈ witness j := by
  simp [transposeWitnessSupport]

/-- Transposition preserves every label degree exactly. -/
theorem transposeWitnessSupport_labelDegree_eq
    {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (witness : J → Finset X) (j : J) :
    (Finset.univ.filter fun x : X =>
      j ∈ transposeWitnessSupport witness x).card = (witness j).card := by
  congr 1
  ext x
  simp

/-- Labelwise agreement with one received affine word is exactly supported
agreement for the transposed coordinate hypergraph. -/
theorem supportedAgreement_transpose_iff
    {X J F : Type} [Fintype J] [DecidableEq X] [DecidableEq J]
    [Field F]
    (domain : X → F) (witness : J → Finset X)
    (label : J → F) (q : J → F[X]) (u₀ u₁ : X → F) :
    SupportedAgreement domain (transposeWitnessSupport witness) label q u₀ u₁ ↔
      ∀ j, ∀ x ∈ witness j,
        (q j).eval (domain x) = u₀ x + label j * u₁ x := by
  constructor
  · intro h j x hx
    exact h x j (by simpa using hx)
  · intro h x j hx
    exact h j x (by simpa using hx)

/-- Direct kernel connector for the campaign's label-indexed witnesses. -/
theorem mem_dividedDifferenceKernel_of_labelwise_receivedAgreement
    {X J F : Type} [Fintype J] [DecidableEq X] [DecidableEq J]
    [Field F]
    (domain : X → F) (witness : J → Finset X)
    (label : J → F) (q : J → F[X]) (u₀ u₁ : X → F)
    (hagree : ∀ j, ∀ x ∈ witness j,
      (q j).eval (domain x) = u₀ x + label j * u₁ x) :
    q ∈ (supportDividedDifference domain
      (transposeWitnessSupport witness) label).ker := by
  apply mem_ker_of_supportedAgreement domain
    (transposeWitnessSupport witness) label q u₀ u₁
  exact (supportedAgreement_transpose_iff
    domain witness label q u₀ u₁).mpr hagree

/-- **Literal P1 anchor connector.**  For `N+1` threshold witnesses, two
labels cover every singleton Hall exception in the transposed support
hypergraph.  Every other label has at least `K` projected local rows. -/
theorem exists_anchor_pair_covering_transposed_singletonHallBad
    {J : Type} [Fintype J] [DecidableEq J]
    (witness : J → Finset (Fin N))
    (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤ (witness j).card) :
    ∃ a b : J, a ≠ b ∧ ∀ j : J, j ≠ a → j ≠ b →
      K ≤ projectedBudget (transposeWitnessSupport witness) {j} := by
  apply exists_anchor_pair_covering_singletonHallBad
    (transposeWitnessSupport witness) hcard
  intro j
  rw [transposeWitnessSupport_labelDegree_eq]
  exact hsize j

/-- **Received-word bootstrap consumer.**  A coordinate-dependent two-zero
bootstrap ordering on the transposed witness hypergraph makes the corrected
degree-restricted kernel rigid.  Therefore every decoded polynomial belongs
to the unique global polynomial pencil through the two gauge anchors. -/
theorem decodedFamily_eq_polynomialPencil_of_transposed_coordinateBootstrap
    {X J F : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J] [Field F]
    (domain : X ↪ F) (witness : J → Finset X)
    (label : J → F) (hlabel : Function.Injective label)
    (q : J → F[X]) (u₀ u₁ : X → F) {degree : Nat} [NeZero degree]
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F degree)
    (hagree : ∀ j, ∀ x ∈ witness j,
      (q j).eval (domain x) = u₀ x + label j * u₁ x)
    {a b : J} (hab : a ≠ b)
    (rank : J → Nat)
    (hrankZero : ∀ j, rank j = 0 → j = a ∨ j = b)
    (hcoverage : ∀ j, 0 < rank j → degree ≤
      (coveredByTwoZeroCoords (transposeWitnessSupport witness)
        (fun p => rank p < rank j) j).card) :
    q = polynomialPencil label
      (pencilBase label q a b) (pencilSlope label q a b) := by
  have hkernel := mem_dividedDifferenceKernel_of_labelwise_receivedAgreement
    (fun x => domain x) witness label q u₀ u₁ hagree
  have hrigid := degreeAnchoredKernelRigid_of_coordinateBootstrap
    domain (transposeWitnessSupport witness) label hlabel rank hrankZero hcoverage
  exact eq_polynomialPencil_of_degreeAnchoredKernelRigid
    (fun x => domain x) (transposeWitnessSupport witness) label
      (hlabel.ne hab) hrigid q hdegree hkernel

/-- **Two-block bootstrap obstruction.**  If every lower-rank label's witness
is contained in one coordinate block `A`, then the coordinates on which two
such labels can force the current component `j` are contained in
`witness(j) ∩ A`. -/
theorem coveredByTwoLower_subset_witness_inter_block
    {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (witness : J → Finset X) (rank : J → Nat)
    (A : Finset X) (j : J)
    (hlower : ∀ p, rank p < rank j → witness p ⊆ A) :
    coveredByTwoZeroCoords (transposeWitnessSupport witness)
        (fun p => rank p < rank j) j ⊆ witness j ∩ A := by
  classical
  intro x hx
  simp only [coveredByTwoZeroCoords, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  rcases hx with ⟨hxj, p, r, hpRank, _hrRank, _hpr, hxp, _hxr⟩
  apply Finset.mem_inter.mpr
  constructor
  · simpa using hxj
  · exact hlower p hpRank (by simpa using hxp)

/-- Cardinal form: a sub-degree block intersection makes the required
two-zero bootstrap coverage impossible at `j`. -/
theorem not_degree_le_coveredByTwoLower_of_inter_card_lt
    {X J : Type} [Fintype X] [DecidableEq X]
    [Fintype J] [DecidableEq J]
    (witness : J → Finset X) (rank : J → Nat)
    (A : Finset X) (j : J) (degree : Nat)
    (hlower : ∀ p, rank p < rank j → witness p ⊆ A)
    (hsmall : (witness j ∩ A).card < degree) :
    ¬ degree ≤ (coveredByTwoZeroCoords
      (transposeWitnessSupport witness) (fun p => rank p < rank j) j).card := by
  intro hdegree
  have hsub := coveredByTwoLower_subset_witness_inter_block
    witness rank A j hlower
  have hcard := Finset.card_le_card hsub
  omega

/-- **Repeated-support escape is already the prize conclusion.**  Two
distinct labels whose decoded Reed--Solomon polynomials agree with the affine
received stack on the same witness set produce low-degree codewords jointly
agreeing with `u₀,u₁` there. -/
theorem pairJointAgreesOn_of_two_decoded_labels_same_witness
    {X F : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : X ↪ F) {degree : Nat}
    (S : Finset X) (u₀ u₁ : X → F)
    (gamma delta : F) (hgd : gamma ≠ delta)
    (pGamma pDelta : F[X])
    (hpGamma : pGamma ∈ Polynomial.degreeLT F degree)
    (hpDelta : pDelta ∈ Polynomial.degreeLT F degree)
    (hagreeGamma : ∀ x ∈ S,
      pGamma.eval (domain x) = u₀ x + gamma * u₁ x)
    (hagreeDelta : ∀ x ∈ S,
      pDelta.eval (domain x) = u₀ x + delta * u₁ x) :
    ProximityGap.pairJointAgreesOn
      (ReedSolomon.code domain degree : Set (X → F)) S u₀ u₁ := by
  apply ProximityGap.pairJointAgreesOn_of_two_lines
    (ReedSolomon.code domain degree) hgd
    (w := fun x => pGamma.eval (domain x))
    (w' := fun x => pDelta.eval (domain x))
  · exact ⟨pGamma, hpGamma, rfl⟩
  · intro x hx
    simpa only [smul_eq_mul] using hagreeGamma x hx
  · exact ⟨pDelta, hpDelta, rfl⟩
  · intro x hx
    simpa only [smul_eq_mul] using hagreeDelta x hx

/-- Separate witnesses give the same joint-agreement conclusion on their
intersection.  Thus any rank obstruction built from repeated or heavily
overlapping support blocks must be checked first against the prize's forbidden
joint-pair branch. -/
theorem pairJointAgreesOn_on_inter_of_two_decoded_labels
    {X F : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : X ↪ F) {degree : Nat}
    (Sgamma Sdelta : Finset X) (u₀ u₁ : X → F)
    (gamma delta : F) (hgd : gamma ≠ delta)
    (pGamma pDelta : F[X])
    (hpGamma : pGamma ∈ Polynomial.degreeLT F degree)
    (hpDelta : pDelta ∈ Polynomial.degreeLT F degree)
    (hagreeGamma : ∀ x ∈ Sgamma,
      pGamma.eval (domain x) = u₀ x + gamma * u₁ x)
    (hagreeDelta : ∀ x ∈ Sdelta,
      pDelta.eval (domain x) = u₀ x + delta * u₁ x) :
    ProximityGap.pairJointAgreesOn
      (ReedSolomon.code domain degree : Set (X → F))
        (Sgamma ∩ Sdelta) u₀ u₁ := by
  apply pairJointAgreesOn_of_two_decoded_labels_same_witness
    domain (Sgamma ∩ Sdelta) u₀ u₁ gamma delta hgd
      pGamma pDelta hpGamma hpDelta
  · intro x hx
    exact hagreeGamma x (Finset.mem_inter.mp hx).1
  · intro x hx
    exact hagreeDelta x (Finset.mem_inter.mp hx).2

/-- **Two-pencil mixed-coordinate rigidity.**  If, at one coordinate, two
distinct labels from each of two polynomial pencils agree with the same
received affine line, then both pencil base evaluations and both slope
evaluations coincide at that coordinate. -/
theorem twoPencils_eval_eq_of_two_labels_each_agree
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (gamma₀ gamma₁ delta₀ delta₁ : F)
    (hgamma : gamma₀ ≠ gamma₁) (hdelta : delta₀ ≠ delta₁)
    (a r b s : F[X]) (x u₀ u₁ : F)
    (hgamma₀ : (a + C gamma₀ * r).eval x = u₀ + gamma₀ * u₁)
    (hgamma₁ : (a + C gamma₁ * r).eval x = u₀ + gamma₁ * u₁)
    (hdelta₀ : (b + C delta₀ * s).eval x = u₀ + delta₀ * u₁)
    (hdelta₁ : (b + C delta₁ * s).eval x = u₀ + delta₁ * u₁) :
    a.eval x = b.eval x ∧ r.eval x = s.eval x := by
  have hA := ProximityGap.affine_eq_of_two_smul_points hgamma
    (by simpa only [eval_add, eval_mul, eval_C, smul_eq_mul] using hgamma₀)
    (by simpa only [eval_add, eval_mul, eval_C, smul_eq_mul] using hgamma₁)
  have hB := ProximityGap.affine_eq_of_two_smul_points hdelta
    (by simpa only [eval_add, eval_mul, eval_C, smul_eq_mul] using hdelta₀)
    (by simpa only [eval_add, eval_mul, eval_C, smul_eq_mul] using hdelta₁)
  exact ⟨hA.1.trans hB.1.symm, hA.2.trans hB.2.symm⟩

/-- Degree-facing cap: genuinely distinct degree-`<k` pencils can be mixed
with two labels from each side on at most `k-1` injected coordinates. -/
theorem twoPencils_mixedCoords_card_le_pred
    {X F : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : X ↪ F) {k : Nat} (hk : 1 ≤ k)
    (a r b s : F[X])
    (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hbdeg : b.natDegree < k) (hsdeg : s.natDegree < k)
    (hne : a ≠ b ∨ r ≠ s)
    (mixed : Finset X)
    (hmixed : ∀ i ∈ mixed,
      a.eval (domain i) = b.eval (domain i) ∧
        r.eval (domain i) = s.eval (domain i)) :
    mixed.card ≤ k - 1 := by
  rcases hne with hab | hrs
  · let p := a - b
    have hp0 : p ≠ 0 := sub_ne_zero.mpr hab
    have hpdeg : p.natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hadeg hbdeg)
    have hsub : mixed ⊆ Finset.univ.filter fun i => p.eval (domain i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, eval_sub]
      exact sub_eq_zero.mpr (hmixed i hi).1
    have hroots := (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le domain p hp0)
    omega
  · let p := r - s
    have hp0 : p ≠ 0 := sub_ne_zero.mpr hrs
    have hpdeg : p.natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hrdeg hsdeg)
    have hsub : mixed ⊆ Finset.univ.filter fun i => p.eval (domain i) = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, eval_sub]
      exact sub_eq_zero.mpr (hmixed i hi).2
    have hroots := (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le domain p hp0)
    omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterReceivedWordRankConnector

open ArkLib.ProximityGap.Frontier.P1RateQuarterReceivedWordRankConnector

#print axioms mem_transposeWitnessSupport_iff
#print axioms transposeWitnessSupport_labelDegree_eq
#print axioms supportedAgreement_transpose_iff
#print axioms mem_dividedDifferenceKernel_of_labelwise_receivedAgreement
#print axioms exists_anchor_pair_covering_transposed_singletonHallBad
#print axioms decodedFamily_eq_polynomialPencil_of_transposed_coordinateBootstrap
#print axioms coveredByTwoLower_subset_witness_inter_block
#print axioms not_degree_le_coveredByTwoLower_of_inter_card_lt
#print axioms pairJointAgreesOn_of_two_decoded_labels_same_witness
#print axioms pairJointAgreesOn_on_inter_of_two_decoded_labels
#print axioms twoPencils_eval_eq_of_two_labels_each_agree
#print axioms twoPencils_mixedCoords_card_le_pred
