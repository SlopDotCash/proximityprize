/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81CRelativePaddingOrderCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87MaximalCancellationAssemblyRepresentation

/-!
# G90: factorial-corrected decoder for weighted collision sectors

G88 counts all endpoint pairs at a fixed maximal-cancellation depth.  For the energy application
one must retain the defining collision equation.  This file makes that repair without requiring
the finite alphabet itself to be additively closed: labels lie in `A`, while an arbitrary weight
map `w : A → B` takes them into an additive cancellative ambient type.

The primitive core type now contains exactly the two properties inherited from a collision after
maximal common-multiset cancellation: disjoint label bags and equality of weighted sums.  Thus its
cardinality is the genuine oriented primitive-relation count needed by the analytic argument.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G90WeightedCollisionDecoderSectorBound

open ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset
open ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation

/-- The sum in the ambient additive type of the weights of a finite label word. -/
def weightedSum {A B : Type*} [AddCommMonoid B] {n : ℕ}
    (w : A → B) (word : Fin n → A) : B :=
  ((valueMultiset word).map w).sum

/-- Ordered primitive weighted relations: their label bags are disjoint and their ambient
weighted sums agree. -/
def PrimitiveRelationCore (A B : Type*) [AddCommMonoid B]
    (w : A → B) (s : ℕ) :=
  {c : (Fin s → A) × (Fin s → A) //
    Disjoint (valueMultiset c.1) (valueMultiset c.2) ∧
      weightedSum w c.1 = weightedSum w c.2}

/-- Weighted collision pairs whose maximal common-multiset cancellation leaves residual
depth `s`. -/
def CollisionCancellationSector (A B : Type*) [DecidableEq A] [AddCommMonoid B]
    (w : A → B) (r s : ℕ) :=
  {q : (Fin r → A) × (Fin r → A) //
    (leftCore (valueMultiset q.1) (valueMultiset q.2)).card = s ∧
      weightedSum w q.1 = weightedSum w q.2}

variable {A B : Type*} [Fintype A] [DecidableEq A] [AddCancelCommMonoid B]
  (w : A → B)

noncomputable instance instFintypePrimitiveRelationCore (s : ℕ) :
    Fintype (PrimitiveRelationCore A B w s) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instFintypeCollisionCancellationSector (r s : ℕ) :
    Fintype (CollisionCancellationSector A B w r s) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Equality of endpoint weighted sums descends through maximal common cancellation.  This is
valid for an arbitrary weight map: map both reconstruction identities and cancel the identical
mapped common part. -/
theorem weighted_core_sum_eq_of_weighted_sum_eq
    {left right : Multiset A}
    (hsum : (left.map w).sum = (right.map w).sum) :
    ((leftCore left right).map w).sum = ((rightCore left right).map w).sum := by
  have hleft := congrArg (fun m : Multiset A ↦ (m.map w).sum)
    (left_reconstruct left right)
  have hright := congrArg (fun m : Multiset A ↦ (m.map w).sum)
    (right_reconstruct left right)
  simp only [Multiset.map_add, Multiset.sum_add] at hleft hright
  apply add_right_cancel (b := ((commonPart left right).map w).sum)
  rw [hleft, hsum, ← hright]

/-- Decode corrected representation data to its raw ordered endpoint pair. -/
noncomputable def decodeRaw {r s : ℕ} (hsr : s ≤ r) :
    PaddingCode (PrimitiveRelationCore A B w s) A r s →
      (Fin r → A) × (Fin r → A) :=
  fun ⟨core, eLeft, eRight, padding, σ⟩ ↦
    (assemble hsr eLeft core.1.1 padding,
      assemble hsr eRight core.1.2 (padding ∘ σ))

/-- Every weighted collision in a fixed maximal-cancellation sector has a corrected-code
representation whose core is itself a primitive weighted relation. -/
theorem exists_code_representation {r s : ℕ} (hsr : s ≤ r)
    (q : CollisionCancellationSector A B w r s) :
    ∃ code : PaddingCode (PrimitiveRelationCore A B w s) A r s,
      decodeRaw w hsr code = q.1 := by
  obtain ⟨leftCoreWord, rightCoreWord, eLeft, eRight, padding, σ,
      hLeftCore, hRightCore, _, hLeft, hRight⟩ :=
    exists_maximalCancellation_assembly hsr q.1.1 q.1.2 q.2.1
  have hdisjoint :
      Disjoint (valueMultiset leftCoreWord) (valueMultiset rightCoreWord) := by
    rw [hLeftCore, hRightCore]
    exact core_disjoint (valueMultiset q.1.1) (valueMultiset q.1.2)
  have hcoreWeighted :
      weightedSum w leftCoreWord = weightedSum w rightCoreWord := by
    unfold weightedSum
    rw [hLeftCore, hRightCore]
    exact weighted_core_sum_eq_of_weighted_sum_eq w q.2.2
  let core : PrimitiveRelationCore A B w s :=
    ⟨(leftCoreWord, rightCoreWord), hdisjoint, hcoreWeighted⟩
  refine ⟨(core, eLeft, eRight, padding, σ), ?_⟩
  exact Prod.ext hLeft hRight

/-- Choose one corrected representation of each weighted collision-sector element. -/
noncomputable def encodeSector {r s : ℕ} (hsr : s ≤ r)
    (q : CollisionCancellationSector A B w r s) :
    PaddingCode (PrimitiveRelationCore A B w s) A r s :=
  Classical.choose (exists_code_representation w hsr q)

theorem decodeRaw_encodeSector {r s : ℕ} (hsr : s ≤ r)
    (q : CollisionCancellationSector A B w r s) :
    decodeRaw w hsr (encodeSector w hsr q) = q.1 :=
  Classical.choose_spec (exists_code_representation w hsr q)

theorem encodeSector_injective {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeSector w hsr) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decodeRaw_encodeSector w hsr x, ← decodeRaw_encodeSector w hsr y, hxy]

/-- **Weighted factorial-corrected collision-sector bound.**  All additive collision semantics
are now retained in the primitive-core cardinality. -/
theorem card_collisionCancellationSector_le {r s : ℕ} (hsr : s ≤ r) :
    Fintype.card (CollisionCancellationSector A B w r s) ≤
      Fintype.card (PrimitiveRelationCore A B w s) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  have hcard := Fintype.card_le_of_injective (encodeSector w hsr)
    (encodeSector_injective w hsr)
  rw [card_paddingCode] at hcard
  exact hcard

end ArkLib.ProximityGap.Frontier.G90WeightedCollisionDecoderSectorBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G90WeightedCollisionDecoderSectorBound.weighted_core_sum_eq_of_weighted_sum_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G90WeightedCollisionDecoderSectorBound.exists_code_representation
#print axioms
  ArkLib.ProximityGap.Frontier.G90WeightedCollisionDecoderSectorBound.card_collisionCancellationSector_le
