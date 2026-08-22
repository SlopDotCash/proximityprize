/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# MCA transport across equivalent coordinate types

The MCA event depends only on the labelled code, not on the particular finite
type used to enumerate its coordinates.  This file records the cross-type
version of the domain-permutation argument: witness finsets, line codewords,
and joint explanations all transport through an equivalence.

The Reed--Solomon specialization discharges the two codeword-transport
hypotheses from equality of the corresponding evaluation points.  It is the
bridge needed when a concrete construction is most naturally indexed by
fibres while the deployed code is stated on `Fin n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.MCAReindexEquiv

attribute [local instance] Classical.propDecidable

variable {source target scalar alphabet : Type}
variable [Fintype source] [Nonempty source] [DecidableEq source]
variable [Fintype target] [Nonempty target] [DecidableEq target]
variable [Field scalar] [Fintype scalar] [DecidableEq scalar]
variable [Fintype alphabet] [DecidableEq alphabet]
variable [AddCommGroup alphabet] [Module scalar alphabet]

/-- Reindex a word from the source coordinates to equivalent target
coordinates. -/
def reindexWord (e : source ≃ target) (w : source → alphabet) : target → alphabet :=
  fun y => w (e.symm y)

@[simp] theorem reindexWord_apply (e : source ≃ target)
    (w : source → alphabet) (y : target) :
    reindexWord e w y = w (e.symm y) := rfl

@[simp] theorem reindexWord_symm_reindexWord (e : source ≃ target)
    (w : source → alphabet) :
    reindexWord e.symm (reindexWord e w) = w := by
  funext x
  simp [reindexWord]

/-- One-way transport of an MCA event across equivalent coordinate types.

`hforward` transports codewords in the same direction as the stack and
line witness.  `hbackward` pulls a hypothetical target joint explanation
back to the source, where it contradicts the original witness. -/
theorem mcaEvent_reindex_mp
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (delta : ℝ≥0) (u0 u1 : source → alphabet) (gamma : scalar) :
    mcaEvent (F := scalar) sourceCode delta u0 u1 gamma →
      mcaEvent (F := scalar) targetCode delta
        (reindexWord e u0) (reindexWord e u1) gamma := by
  rintro ⟨S, hcard, ⟨w, hw, hagree⟩, hnotJoint⟩
  refine ⟨S.image e, ?_, ⟨reindexWord e w, hforward w hw, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective S e.injective,
      ← Fintype.card_congr e]
    exact hcard
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simpa [reindexWord] using hagree x hx
  · intro htargetJoint
    apply hnotJoint
    obtain ⟨v0, hv0, v1, hv1, hagree⟩ := htargetJoint
    refine ⟨(fun x : source => v0 (e x)), hbackward v0 hv0,
      (fun x : source => v1 (e x)), hbackward v1 hv1, ?_⟩
    intro x hx
    simpa [reindexWord] using
      hagree (e x) (Finset.mem_image_of_mem (f := e) hx)

/-- Pointwise equivalence of MCA events under a bijective reindexing and
two-way codeword transport. -/
theorem mcaEvent_reindex_iff
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (delta : ℝ≥0) (u0 u1 : source → alphabet) (gamma : scalar) :
    mcaEvent (F := scalar) targetCode delta
        (reindexWord e u0) (reindexWord e u1) gamma ↔
      mcaEvent (F := scalar) sourceCode delta u0 u1 gamma := by
  constructor
  · intro h
    have h' := mcaEvent_reindex_mp e.symm targetCode sourceCode
      (fun w hw => hbackward w hw) (fun w hw => hforward w hw)
      delta (reindexWord e u0) (reindexWord e u1) gamma h
    simpa using h'
  · exact mcaEvent_reindex_mp e sourceCode targetCode hforward hbackward
      delta u0 u1 gamma

/-! ## Reed--Solomon specialization -/

variable {field : Type} [Field field] [Fintype field] [DecidableEq field]

/-- MCA is invariant under a Reed--Solomon domain reindexing that preserves
the evaluation point at every coordinate. -/
theorem mcaEvent_reindex_reedSolomon_iff
    (e : source ≃ target)
    (sourceDomain : source ↪ field)
    (targetDomain : target ↪ field)
    (hdom : ∀ x : source, sourceDomain x = targetDomain (e x))
    (degree : ℕ) (delta : ℝ≥0)
    (u0 u1 : source → field) (gamma : field) :
    mcaEvent
        (ReedSolomon.code targetDomain degree : Set (target → field))
        delta (reindexWord e u0) (reindexWord e u1) gamma ↔
      mcaEvent
        (ReedSolomon.code sourceDomain degree : Set (source → field))
        delta u0 u1 gamma := by
  apply mcaEvent_reindex_iff e
  · intro w hw
    exact ReedSolomon.code_reindex_mem e hdom hw
  · intro w hw
    have hdom' : ∀ y : target,
        targetDomain y = sourceDomain (e.symm y) := by
      intro y
      simpa using (hdom (e.symm y)).symm
    simpa [reindexWord] using
      (ReedSolomon.code_reindex_mem e.symm hdom' hw)

end ArkLib.ProximityGap.Frontier.MCAReindexEquiv

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.MCAReindexEquiv
#print axioms mcaEvent_reindex_mp
#print axioms mcaEvent_reindex_iff
#print axioms mcaEvent_reindex_reedSolomon_iff
