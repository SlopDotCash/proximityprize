/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshCoordinate

/-!
# The P1 shared-fresh-triple residual is false

The named `SharedFreshTripleFree` residual is stronger than the predecessor bad-count target and
is false even at the literal P1 parameters.  The counterexample works on every injective P1
evaluation domain.

Let `J` be an initial segment of size `T`, let `C` be its complement, and let `B` be an initial
segment of size `2T-N-1`.  Write `f_B` for the locator polynomial of `B`, and put

```text
q_0 = X f_B,   q_1 = f_B.
```

The received stack is `(q_0,q_1)` on `J` and zero on `C`.  For every `x in J \ B`, the zero
codeword witnesses scalar `gamma_x = -dom(x)` on

```text
S_x = C union B union {x}.
```

Indeed both rows vanish on `B`, while `q_0(x)+gamma_x q_1(x)=0`.  The set has exactly `T`
coordinates.  It is not jointly explainable: any explaining pair vanishes on `C`, whose size is
at least `k`, hence is the zero pair; but `q_1(x)=f_B(dom(x))` is nonzero because `x` is not in
`B`.  Thus one fixed fresh coordinate carries `|J \ B| = N-T+1 = 480946859` distinct scalars.
In particular it carries three, refuting `SharedFreshTripleFree`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1000000
set_option maxRecDepth 500000
set_option trace.profiler true

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleRefuted

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Exact coordinate blocks -/

/-- The number of extra roots added to the common zero block in one witness. -/
abbrev patchSize : ℕ := 111848108

/-- Last coordinate of the common root block. -/
def firstPatchPoint : Fin N := ⟨111848107, by norm_num [N]⟩

/-- Two further points used for the explicit three-scalar corollary. -/
def secondPatchPoint : Fin N := ⟨111848108, by norm_num [N]⟩
def thirdPatchPoint : Fin N := ⟨111848109, by norm_num [N]⟩

/-- First coordinate outside the threshold joint set; this is the shared fresh coordinate. -/
def freshPoint : Fin N := ⟨592794966, by norm_num [N]⟩

/-- Structural embedding of an initial interval.  Using an image of `Fin t` keeps all
prize-scale cardinality proofs symbolic. -/
def initialEmbedding (t : ℕ) (ht : t ≤ N) : Fin t ↪ Fin N where
  toFun x := ⟨x, x.isLt.trans_le ht⟩
  inj' := by
    intro x y h
    exact Fin.ext (congrArg Fin.val h)

/-- Initial interval of length `t`, presented without reducing a large concrete `Iio`. -/
noncomputable def initialSegment (t : ℕ) (ht : t ≤ N) : Finset (Fin N) :=
  Finset.univ.map (initialEmbedding t ht)

theorem initialSegment_card (t : ℕ) (ht : t ≤ N) :
    (initialSegment t ht).card = t := by
  rw [initialSegment, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mem_initialSegment_iff (t : ℕ) (ht : t ≤ N) (x : Fin N) :
    x ∈ initialSegment t ht ↔ (x : ℕ) < t := by
  rw [initialSegment, Finset.mem_map]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.isLt
  · intro hx
    refine ⟨⟨x, hx⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl

/-- Initial threshold joint set. -/
noncomputable def jointSet : Finset (Fin N) :=
  initialSegment 592794966 (by norm_num [N])

/-- Its final-segment complement. -/
noncomputable def outsideSet : Finset (Fin N) := Finset.univ \ jointSet

/-- Common locator roots.  One more selected point makes each witness patch have size
`2T-N`. -/
noncomputable def baseRoots : Finset (Fin N) :=
  initialSegment 111848107 (by norm_num [N])

/-- Points that can be added to the common root block. -/
def patchPoints : Finset (Fin N) := jointSet \ baseRoots

/-- Witness set belonging to `x`. -/
def witnessSet (x : Fin N) : Finset (Fin N) :=
  outsideSet ∪ insert x baseRoots

theorem jointSet_card : jointSet.card = predecessorThreshold := by
  rw [jointSet, initialSegment_card, predecessorThreshold_eq]

theorem outsideSet_card : outsideSet.card = N - predecessorThreshold := by
  rw [outsideSet, Finset.card_sdiff_of_subset (Finset.subset_univ jointSet),
    Finset.card_univ, Fintype.card_fin, jointSet_card]

theorem baseRoots_card : baseRoots.card = patchSize - 1 := by
  rw [baseRoots, initialSegment_card]
  norm_num [patchSize]

theorem baseRoots_subset_jointSet : baseRoots ⊆ jointSet := by
  intro x hx
  rw [baseRoots, mem_initialSegment_iff] at hx
  rw [jointSet, mem_initialSegment_iff]
  omega

theorem patchPoints_card : patchPoints.card = N - predecessorThreshold + 1 := by
  rw [patchPoints, Finset.card_sdiff_of_subset baseRoots_subset_jointSet,
    jointSet_card, baseRoots_card]
  norm_num [patchSize, predecessorThreshold_eq, N]

theorem patchPoints_card_value : patchPoints.card = 480946859 := by
  rw [patchPoints_card]
  norm_num [predecessorThreshold_eq, N]

theorem firstPatchPoint_mem_patchPoints : firstPatchPoint ∈ patchPoints := by
  rw [patchPoints, Finset.mem_sdiff, jointSet, mem_initialSegment_iff,
    baseRoots, mem_initialSegment_iff]
  norm_num [firstPatchPoint]

theorem secondPatchPoint_mem_patchPoints : secondPatchPoint ∈ patchPoints := by
  rw [patchPoints, Finset.mem_sdiff, jointSet, mem_initialSegment_iff,
    baseRoots, mem_initialSegment_iff]
  norm_num [secondPatchPoint]

theorem thirdPatchPoint_mem_patchPoints : thirdPatchPoint ∈ patchPoints := by
  rw [patchPoints, Finset.mem_sdiff, jointSet, mem_initialSegment_iff,
    baseRoots, mem_initialSegment_iff]
  norm_num [thirdPatchPoint]

theorem patchPoints_pairwise_ne :
    firstPatchPoint ≠ secondPatchPoint ∧ firstPatchPoint ≠ thirdPatchPoint ∧
      secondPatchPoint ≠ thirdPatchPoint := by
  norm_num [firstPatchPoint, secondPatchPoint, thirdPatchPoint]

theorem freshPoint_not_mem_jointSet : freshPoint ∉ jointSet := by
  rw [jointSet, mem_initialSegment_iff]
  norm_num [freshPoint]

theorem freshPoint_mem_outsideSet : freshPoint ∈ outsideSet := by
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, freshPoint_not_mem_jointSet⟩

theorem patch_mem_jointSet {x : Fin N} (hx : x ∈ patchPoints) : x ∈ jointSet :=
  (Finset.mem_sdiff.mp hx).1

theorem patch_not_mem_baseRoots {x : Fin N} (hx : x ∈ patchPoints) : x ∉ baseRoots :=
  (Finset.mem_sdiff.mp hx).2

theorem outsideSet_disjoint_insert_baseRoots {x : Fin N} (hx : x ∈ patchPoints) :
    Disjoint outsideSet (insert x baseRoots) := by
  rw [Finset.disjoint_left]
  intro e heOut heInsert
  have heJoint : e ∈ jointSet := by
    rcases Finset.mem_insert.mp heInsert with rfl | heB
    · exact patch_mem_jointSet hx
    · exact baseRoots_subset_jointSet heB
  exact (Finset.mem_sdiff.mp heOut).2 heJoint

theorem witnessSet_card {x : Fin N} (hx : x ∈ patchPoints) :
    (witnessSet x).card = predecessorThreshold := by
  rw [witnessSet, Finset.card_union_of_disjoint (outsideSet_disjoint_insert_baseRoots hx),
    Finset.card_insert_of_notMem (patch_not_mem_baseRoots hx), outsideSet_card,
    baseRoots_card]
  norm_num [patchSize, predecessorThreshold_eq, N]

theorem freshPoint_mem_witnessSet (x : Fin N) : freshPoint ∈ witnessSet x := by
  exact Finset.mem_union_left _ freshPoint_mem_outsideSet

/-! ## Locator polynomial and received stack -/

/-- Monic locator of the common root block. -/
noncomputable def rootPolynomial (dom : Fin N ↪ F) : F[X] :=
  ∏ b ∈ baseRoots, (X - C (dom b))

theorem rootPolynomial_natDegree (dom : Fin N ↪ F) :
    (rootPolynomial dom).natDegree = baseRoots.card := by
  rw [rootPolynomial,
    natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (dom i)]
  simp

theorem rootPolynomial_eval_eq_zero_of_mem (dom : Fin N ↪ F)
    {e : Fin N} (he : e ∈ baseRoots) :
    (rootPolynomial dom).eval (dom e) = 0 := by
  rw [rootPolynomial, eval_prod]
  apply Finset.prod_eq_zero he
  simp

theorem rootPolynomial_eval_ne_zero_of_not_mem (dom : Fin N ↪ F)
    {e : Fin N} (he : e ∉ baseRoots) :
    (rootPolynomial dom).eval (dom e) ≠ 0 := by
  rw [rootPolynomial, eval_prod]
  apply Finset.prod_ne_zero
  intro b hb
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr fun h ↦ he (dom.injective h.symm ▸ hb)

noncomputable def jointPolynomialZero (dom : Fin N ↪ F) : F[X] :=
  X * rootPolynomial dom

noncomputable def jointPolynomialOne (dom : Fin N ↪ F) : F[X] :=
  rootPolynomial dom

theorem jointPolynomialZero_natDegree_lt_k (dom : Fin N ↪ F) :
    (jointPolynomialZero dom).natDegree < k := by
  calc
    (jointPolynomialZero dom).natDegree ≤
        X.natDegree + (rootPolynomial dom).natDegree := by
      exact natDegree_mul_le
    _ = 1 + baseRoots.card := by rw [natDegree_X, rootPolynomial_natDegree]
    _ < k := by rw [baseRoots_card]; norm_num [patchSize, k]

theorem jointPolynomialOne_natDegree_lt_k (dom : Fin N ↪ F) :
    (jointPolynomialOne dom).natDegree < k := by
  rw [jointPolynomialOne, rootPolynomial_natDegree, baseRoots_card]
  norm_num [patchSize, k]

noncomputable def jointWordZero (dom : Fin N ↪ F) : Fin N → F :=
  fun e ↦ (jointPolynomialZero dom).eval (dom e)

noncomputable def jointWordOne (dom : Fin N ↪ F) : Fin N → F :=
  fun e ↦ (jointPolynomialOne dom).eval (dom e)

theorem jointWordZero_mem (dom : Fin N ↪ F) :
    jointWordZero dom ∈ predecessorCode dom := by
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
    (jointPolynomialZero dom) (jointPolynomialZero_natDegree_lt_k dom)
  intro e
  rfl

theorem jointWordOne_mem (dom : Fin N ↪ F) :
    jointWordOne dom ∈ predecessorCode dom := by
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
    (jointPolynomialOne dom) (jointPolynomialOne_natDegree_lt_k dom)
  intro e
  rfl

/-- The received stack is the locator pair on `J` and zero on its complement. -/
noncomputable def receivedZero (dom : Fin N ↪ F) : Fin N → F :=
  fun e ↦ if e ∈ jointSet then jointWordZero dom e else 0

noncomputable def receivedOne (dom : Fin N ↪ F) : Fin N → F :=
  fun e ↦ if e ∈ jointSet then jointWordOne dom e else 0

theorem joint_pair_on_jointSet (dom : Fin N ↪ F) :
    pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) jointSet
      (receivedZero dom) (receivedOne dom) := by
  refine ⟨jointWordZero dom, jointWordZero_mem dom,
    jointWordOne dom, jointWordOne_mem dom, ?_⟩
  intro e he
  simp [receivedZero, receivedOne, he]

/-! ## The large shared-fresh scalar family -/

/-- Scalar attached to the extra root `x`. -/
noncomputable def patchScalar (dom : Fin N ↪ F) (x : Fin N) : F := -dom x

theorem patchScalar_injective (dom : Fin N ↪ F) : Function.Injective (patchScalar dom) := by
  intro x y h
  apply dom.injective
  exact neg_injective h

theorem zero_agrees_on_witnessSet (dom : Fin N ↪ F)
    {x : Fin N} (hx : x ∈ patchPoints) :
    ∀ e ∈ witnessSet x,
      (0 : Fin N → F) e = receivedZero dom e + patchScalar dom x • receivedOne dom e := by
  intro e he
  rw [witnessSet, Finset.mem_union] at he
  rcases he with heOut | hePatch
  · have heNotJoint : e ∉ jointSet := by
      exact (Finset.mem_sdiff.mp heOut).2
    simp [receivedZero, receivedOne, heNotJoint]
  · have heJoint : e ∈ jointSet := by
      rcases Finset.mem_insert.mp hePatch with rfl | heB
      · exact patch_mem_jointSet hx
      · exact baseRoots_subset_jointSet heB
    rw [receivedZero, receivedOne, if_pos heJoint, if_pos heJoint]
    rcases Finset.mem_insert.mp hePatch with rfl | heB
    · simp only [jointWordZero, jointWordOne, jointPolynomialZero,
        jointPolynomialOne, patchScalar, eval_mul, eval_X, Pi.zero_apply, smul_eq_mul]
      ring
    · have hroot := rootPolynomial_eval_eq_zero_of_mem dom heB
      simp only [jointWordZero, jointWordOne, jointPolynomialZero,
        jointPolynomialOne, patchScalar, eval_mul, eval_X, Pi.zero_apply, smul_eq_mul]
      rw [hroot]
      ring

theorem not_joint_on_witnessSet (dom : Fin N ↪ F)
    {x : Fin N} (hx : x ∈ patchPoints) :
    ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F))
      (witnessSet x) (receivedZero dom) (receivedOne dom) := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  have houtSubset : outsideSet ⊆ witnessSet x := fun e he ↦
    Finset.mem_union_left _ he
  have hkOutside : k ≤ outsideSet.card := by
    rw [outsideSet_card]
    norm_num [predecessorThreshold_eq, N, k]
  have hv₀zero : v₀ = 0 := by
    apply predecessor_sep dom v₀ hv₀ 0 (predecessorCode dom).zero_mem outsideSet hkOutside
    intro e he
    have heNotJoint : e ∉ jointSet := by
      exact (Finset.mem_sdiff.mp he).2
    have hrow := (hagree e (houtSubset he)).1
    simpa [receivedZero, heNotJoint] using hrow
  have hv₁zero : v₁ = 0 := by
    apply predecessor_sep dom v₁ hv₁ 0 (predecessorCode dom).zero_mem outsideSet hkOutside
    intro e he
    have heNotJoint : e ∉ jointSet := by
      exact (Finset.mem_sdiff.mp he).2
    have hrow := (hagree e (houtSubset he)).2
    simpa [receivedOne, heNotJoint] using hrow
  have hxWitness : x ∈ witnessSet x := by
    exact Finset.mem_union_right _ (Finset.mem_insert_self x baseRoots)
  have hxJoint := patch_mem_jointSet hx
  have hrow := (hagree x hxWitness).2
  rw [hv₁zero] at hrow
  have hnonzero := rootPolynomial_eval_ne_zero_of_not_mem dom (patch_not_mem_baseRoots hx)
  apply hnonzero
  simpa [receivedOne, hxJoint, jointWordOne, jointPolynomialOne] using hrow.symm

/-- Every point of `J \ B` gives a non-joint threshold witness through the same fresh point. -/
theorem sharedWitnessAt_patchScalar (dom : Fin N ↪ F)
    {x : Fin N} (hx : x ∈ patchPoints) :
    SharedWitnessAt dom (receivedZero dom) (receivedOne dom) freshPoint
      (patchScalar dom x) := by
  refine ⟨witnessSet x, freshPoint_mem_witnessSet x,
    (witnessSet_card hx).ge, ?_, not_joint_on_witnessSet dom hx⟩
  refine ⟨(0 : Fin N → F), (predecessorCode dom).zero_mem, ?_⟩
  exact zero_agrees_on_witnessSet dom hx

/-- Exact size of the injectively labelled shared-fresh family. -/
theorem sharedFresh_family_card : patchPoints.card = 480946859 :=
  patchPoints_card_value

/-! ## Literal refutation of the named residual -/

theorem patchScalar_first_ne_second (dom : Fin N ↪ F) :
    patchScalar dom firstPatchPoint ≠ patchScalar dom secondPatchPoint := by
  exact (patchScalar_injective dom).ne (patchPoints_pairwise_ne.1)

theorem patchScalar_first_ne_third (dom : Fin N ↪ F) :
    patchScalar dom firstPatchPoint ≠ patchScalar dom thirdPatchPoint := by
  exact (patchScalar_injective dom).ne (patchPoints_pairwise_ne.2.1)

theorem patchScalar_second_ne_third (dom : Fin N ↪ F) :
    patchScalar dom secondPatchPoint ≠ patchScalar dom thirdPatchPoint := by
  exact (patchScalar_injective dom).ne (patchPoints_pairwise_ne.2.2)

/-- **Refutation.**  The P1 `SharedFreshTripleFree` residual fails on every injective
evaluation domain, even though its bad-family consumer is logically valid. -/
theorem not_sharedFreshTripleFree (dom : Fin N ↪ F) :
    ¬ SharedFreshTripleFree dom := by
  intro hfree
  apply hfree (receivedZero dom) (receivedOne dom) jointSet
    (jointSet_card.ge) (joint_pair_on_jointSet dom) freshPoint freshPoint_not_mem_jointSet
  exact ⟨patchScalar dom firstPatchPoint, patchScalar dom secondPatchPoint,
    patchScalar dom thirdPatchPoint, patchScalar_first_ne_second dom,
    patchScalar_first_ne_third dom, patchScalar_second_ne_third dom,
    sharedWitnessAt_patchScalar dom firstPatchPoint_mem_patchPoints,
    sharedWitnessAt_patchScalar dom secondPatchPoint_mem_patchPoints,
    sharedWitnessAt_patchScalar dom thirdPatchPoint_mem_patchPoints⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleRefuted

#print axioms patchPoints_card_value
#print axioms rootPolynomial_eval_ne_zero_of_not_mem
#print axioms sharedWitnessAt_patchScalar
#print axioms sharedFresh_family_card
#print axioms not_sharedFreshTripleFree
