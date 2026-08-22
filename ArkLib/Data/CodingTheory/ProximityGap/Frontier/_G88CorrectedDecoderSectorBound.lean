/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81CRelativePaddingOrderCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87MaximalCancellationAssemblyRepresentation

/-!
# G88: counted factorial-corrected decoder for one maximal-cancellation sector

G87 proves that every endpoint pair whose maximal residual depth is `s` has the corrected padding
representation.  This file packages that representation as an injective encoding into G81C's
code and proves the resulting sector cardinality bound.

The core type is the exact finite type of ordered depth-`s` word pairs with disjoint value
multisets.  Hence the remaining quantitative input is isolated in its cardinality; no decoder
surjectivity hypothesis remains for the finite combinatorial step.

This does not bound the primitive-core type uniformly across growing depths and therefore does not
close the production delta-star theorem.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G88CorrectedDecoderSectorBound

open ArkLib.ProximityGap.Frontier.G81CRelativePaddingOrderCeiling
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset
open ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation

/-- Ordered primitive core pairs: maximal cancellation has made their value multisets disjoint. -/
def PrimitiveCorePair (A : Type*) (s : ℕ) :=
  {c : (Fin s → A) × (Fin s → A) // Disjoint (valueMultiset c.1) (valueMultiset c.2)}

/-- Endpoint pairs whose maximal common-multiset cancellation leaves left residual depth `s`. -/
def CancellationSector (A : Type*) [DecidableEq A] (r s : ℕ) :=
  {q : (Fin r → A) × (Fin r → A) //
    (leftCore (valueMultiset q.1) (valueMultiset q.2)).card = s}

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable instance instFintypePrimitiveCorePair (A : Type*) [Fintype A] (s : ℕ) :
    Fintype (PrimitiveCorePair A s) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instFintypeCancellationSector
    (A : Type*) [Fintype A] [DecidableEq A] (r s : ℕ) :
    Fintype (CancellationSector A r s) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Decode the corrected code to its raw ordered endpoint pair. -/
noncomputable def decodeRaw {r s : ℕ} (hsr : s ≤ r) :
    PaddingCode (PrimitiveCorePair A s) A r s →
      (Fin r → A) × (Fin r → A) :=
  fun ⟨core, eLeft, eRight, padding, σ⟩ =>
    (assemble hsr eLeft core.1.1 padding,
      assemble hsr eRight core.1.2 (padding ∘ σ))

/-- Every pair in the maximal-cancellation sector has a corrected-code representation. -/
theorem exists_code_representation {r s : ℕ} (hsr : s ≤ r)
    (q : CancellationSector A r s) :
    ∃ code : PaddingCode (PrimitiveCorePair A s) A r s,
      decodeRaw hsr code = q.1 := by
  obtain ⟨leftCoreWord, rightCoreWord, eLeft, eRight, padding, σ,
      hLeftCore, hRightCore, _, hLeft, hRight⟩ :=
    exists_maximalCancellation_assembly hsr q.1.1 q.1.2 q.2
  have hprimitive : Disjoint (valueMultiset leftCoreWord) (valueMultiset rightCoreWord) := by
    rw [hLeftCore, hRightCore]
    exact core_disjoint (valueMultiset q.1.1) (valueMultiset q.1.2)
  let core : PrimitiveCorePair A s :=
    ⟨(leftCoreWord, rightCoreWord), hprimitive⟩
  refine ⟨(core, eLeft, eRight, padding, σ), ?_⟩
  exact Prod.ext hLeft hRight

/-- Choose one corrected-code representation of each sector element. -/
noncomputable def encodeSector {r s : ℕ} (hsr : s ≤ r)
    (q : CancellationSector A r s) : PaddingCode (PrimitiveCorePair A s) A r s :=
  Classical.choose (exists_code_representation hsr q)

theorem decodeRaw_encodeSector {r s : ℕ} (hsr : s ≤ r)
    (q : CancellationSector A r s) :
    decodeRaw hsr (encodeSector hsr q) = q.1 :=
  Classical.choose_spec (exists_code_representation hsr q)

/-- The chosen corrected-code representation is injective because decoding recovers the pair. -/
theorem encodeSector_injective {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeSector (A := A) hsr) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decodeRaw_encodeSector hsr x, ← decodeRaw_encodeSector hsr y, hxy]

/-- **Factorial-corrected sector bound.**  This is G81C's intended concrete consumer, now with
the decoder representation and injectivity proved rather than hypothesized. -/
theorem card_cancellationSector_le {r s : ℕ} (hsr : s ≤ r) :
    Fintype.card (CancellationSector A r s) ≤
      Fintype.card (PrimitiveCorePair A s) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  have hcard := Fintype.card_le_of_injective (encodeSector (A := A) hsr)
    (encodeSector_injective (A := A) hsr)
  rw [card_paddingCode] at hcard
  exact hcard

end ArkLib.ProximityGap.Frontier.G88CorrectedDecoderSectorBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G88CorrectedDecoderSectorBound.exists_code_representation
#print axioms
  ArkLib.ProximityGap.Frontier.G88CorrectedDecoderSectorBound.encodeSector_injective
#print axioms
  ArkLib.ProximityGap.Frontier.G88CorrectedDecoderSectorBound.card_cancellationSector_le
