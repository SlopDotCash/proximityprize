/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAReindexEquiv
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# MCA error and threshold under equivalent coordinate types

`_MCAReindexEquiv` transports one MCA event across a coordinate equivalence.
Here that pointwise statement is lifted through the uniform scalar
probability, the supremum over received stacks, and finally the supremum of
good radii.  The resulting Reed--Solomon specialization lets a construction
use its natural structured coordinate type while stating the operational
threshold on `Fin n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open _root_.ProximityGap Code
open scoped NNReal ENNReal ProbabilityTheory

namespace ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv

open MCAReindexEquiv
open _root_.ProximityGap.MCAThresholdLedger

attribute [local instance] Classical.propDecidable

variable {source target scalar alphabet : Type}
variable [Fintype source] [Nonempty source] [DecidableEq source]
variable [Fintype target] [Nonempty target] [DecidableEq target]
variable [Field scalar] [Fintype scalar] [DecidableEq scalar]
variable [Fintype alphabet] [DecidableEq alphabet]
variable [AddCommGroup alphabet] [Module scalar alphabet]

/-- Per-stack MCA probability is unchanged by an equivalent coordinate
reindexing with two-way codeword transport. -/
theorem prob_mcaEvent_reindex_eq
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (delta : ℝ≥0) (u0 u1 : source → alphabet) :
    Pr_{let gamma ← $ᵖ scalar}[
        mcaEvent targetCode delta (reindexWord e u0) (reindexWord e u1) gamma] =
      Pr_{let gamma ← $ᵖ scalar}[
        mcaEvent sourceCode delta u0 u1 gamma] :=
  _root_.ProximityGap.MCAEquivariance.Pr_congr_iff _ fun gamma =>
    mcaEvent_reindex_iff e sourceCode targetCode hforward hbackward
      delta u0 u1 gamma

/-- The MCA error itself is invariant under coordinate equivalence. -/
theorem epsMCA_reindex_eq
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (delta : ℝ≥0) :
    epsMCA (F := scalar) (A := alphabet) targetCode delta =
      epsMCA (F := scalar) (A := alphabet) sourceCode delta := by
  apply le_antisymm
  · unfold epsMCA
    refine iSup_le fun v => ?_
    let u : WordStack alphabet (Fin 2) source :=
      fun i => reindexWord e.symm (v i)
    have hprob := prob_mcaEvent_reindex_eq
      (scalar := scalar) (alphabet := alphabet) e sourceCode targetCode
      hforward hbackward delta (u 0) (u 1)
    have hrow0 : reindexWord e (u 0) = v 0 := by
      simp only [u]
      exact reindexWord_symm_reindexWord e.symm (v 0)
    have hrow1 : reindexWord e (u 1) = v 1 := by
      simp only [u]
      exact reindexWord_symm_reindexWord e.symm (v 1)
    rw [hrow0, hrow1] at hprob
    rw [hprob]
    exact le_iSup (fun w : WordStack alphabet (Fin 2) source =>
      Pr_{let gamma ← $ᵖ scalar}[
        mcaEvent sourceCode delta (w 0) (w 1) gamma]) u
  · unfold epsMCA
    refine iSup_le fun u => ?_
    rw [← prob_mcaEvent_reindex_eq
      (scalar := scalar) (alphabet := alphabet) e sourceCode targetCode
      hforward hbackward delta (u 0) (u 1)]
    exact le_iSup (fun v : WordStack alphabet (Fin 2) target =>
      Pr_{let gamma ← $ᵖ scalar}[
        mcaEvent targetCode delta (v 0) (v 1) gamma])
      (fun i => reindexWord e (u i))

/-- The complete set of good radii is invariant under reindexing. -/
theorem mcaGoodRadii_reindex_eq
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (epsilonStar : ℝ≥0∞) :
    mcaGoodRadii (F := scalar) (A := alphabet) targetCode epsilonStar =
      mcaGoodRadii (F := scalar) (A := alphabet) sourceCode epsilonStar := by
  ext delta
  simp only [mcaGoodRadii, Set.mem_setOf_eq]
  rw [epsMCA_reindex_eq e sourceCode targetCode hforward hbackward delta]

/-- The operational MCA threshold is invariant under reindexing. -/
theorem mcaDeltaStar_reindex_eq
    (e : source ≃ target)
    (sourceCode : Set (source → alphabet))
    (targetCode : Set (target → alphabet))
    (hforward : ∀ w ∈ sourceCode, reindexWord e w ∈ targetCode)
    (hbackward : ∀ w ∈ targetCode,
      (fun x : source => w (e x)) ∈ sourceCode)
    (epsilonStar : ℝ≥0∞) :
    mcaDeltaStar (F := scalar) (A := alphabet) targetCode epsilonStar =
      mcaDeltaStar (F := scalar) (A := alphabet) sourceCode epsilonStar := by
  unfold mcaDeltaStar
  rw [mcaGoodRadii_reindex_eq e sourceCode targetCode
    hforward hbackward epsilonStar]

/-! ## Reed--Solomon specialization -/

variable {field : Type} [Field field] [Fintype field] [DecidableEq field]

/-- Reed--Solomon MCA errors agree after reindexing an equal evaluation
domain. -/
theorem epsMCA_reindex_reedSolomon_eq
    (e : source ≃ target)
    (sourceDomain : source ↪ field)
    (targetDomain : target ↪ field)
    (hdom : ∀ x : source, sourceDomain x = targetDomain (e x))
    (degree : ℕ) (delta : ℝ≥0) :
    epsMCA (F := field) (A := field)
        (ReedSolomon.code targetDomain degree : Set (target → field)) delta =
      epsMCA (F := field) (A := field)
        (ReedSolomon.code sourceDomain degree : Set (source → field)) delta := by
  apply epsMCA_reindex_eq e
  · intro w hw
    exact ReedSolomon.code_reindex_mem e hdom hw
  · intro w hw
    have hdom' : ∀ y : target,
        targetDomain y = sourceDomain (e.symm y) := by
      intro y
      simpa using (hdom (e.symm y)).symm
    simpa [reindexWord] using
      (ReedSolomon.code_reindex_mem e.symm hdom' hw)

/-- Reed--Solomon MCA thresholds agree after reindexing an equal evaluation
domain. -/
theorem mcaDeltaStar_reindex_reedSolomon_eq
    (e : source ≃ target)
    (sourceDomain : source ↪ field)
    (targetDomain : target ↪ field)
    (hdom : ∀ x : source, sourceDomain x = targetDomain (e x))
    (degree : ℕ) (epsilonStar : ℝ≥0∞) :
    mcaDeltaStar (F := field) (A := field)
        (ReedSolomon.code targetDomain degree : Set (target → field)) epsilonStar =
      mcaDeltaStar (F := field) (A := field)
        (ReedSolomon.code sourceDomain degree : Set (source → field)) epsilonStar := by
  apply mcaDeltaStar_reindex_eq e
  · intro w hw
    exact ReedSolomon.code_reindex_mem e hdom hw
  · intro w hw
    have hdom' : ∀ y : target,
        targetDomain y = sourceDomain (e.symm y) := by
      intro y
      simpa using (hdom (e.symm y)).symm
    simpa [reindexWord] using
      (ReedSolomon.code_reindex_mem e.symm hdom' hw)

end ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv
#print axioms prob_mcaEvent_reindex_eq
#print axioms epsMCA_reindex_eq
#print axioms mcaGoodRadii_reindex_eq
#print axioms mcaDeltaStar_reindex_eq
#print axioms epsMCA_reindex_reedSolomon_eq
#print axioms mcaDeltaStar_reindex_reedSolomon_eq
