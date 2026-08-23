/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArith
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonCountWiring
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Arith

/-!
# The Hab25 Johnson discharge site (#302)

This module is the designated landing site for the unconditional below-Johnson numeric
edge `johnsonNumericBound_holds` ([Hab25] Theorem 2 for smooth Reed–Solomon codes).  It
records, as theorems, the two *exact* remaining obligations — each a single per-stack
construction hypothesis away from the unconditional statement:

* `johnsonNumericBound_holds_of_capture_production` — via the affine-capture funnel
  (`johnsonNumericBound_of_affine_capture_of_list_shape`): a per-stack list of at most
  `L` low-degree pairs capturing every bad scalar.  The per-scalar capture is already
  in-tree (`BCIKS20.Claim510Capture.affineCaptured_of_pencil_proximity`); what remains
  is its per-stack aggregation over the GS surface.
* `johnsonNumericBound_holds_of_dichotomy_production` — via the dichotomy funnel
  (`johnsonNumericBound_of_forall_dichotomy`): a per-stack dichotomy bundle within a
  budget `B` satisfying the Johnson arithmetic.
* `johnsonNumericBound_holds_of_factorData_production` — the current [BCIKS20] Claim 5.10
  funnel: a per-pair factor-family production plus the real closing arithmetic.

When either producer lands, the unconditional `johnsonNumericBound_holds` is this file's
theorem with the hypothesis replaced by the producer call.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open Polynomial _root_.ProximityGap Code
open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]


/-- **The gate statement, pinned.**  The unconditional below-Johnson numeric edge as the
final theorem `ProximityGap.johnsonNumericBound_holds` will assert it: for every smooth
evaluation domain, rate, and Johnson-range radius (with the canonical multiplicity regime),
the MCA error is inside the [Hab25] numeric budget.  Pinning the `Prop` removes the last
flip-day design decision; the discharge theorem proves exactly this. -/
def JohnsonDischargeStatement : Prop :=
  ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
    (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (η δ : ℝ≥0),
    2 ≤ k → k + 1 ≤ n → 12 ≤ m →
    δ ≤ 1 → (δ : ℝ) < _root_.gs_johnson k n m →
    ((m : ℝ) ≤ max (⌈((((k : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3) →
    JohnsonNumericBound domain k η δ

/-- **The capture-production obligation.**  The unconditional numeric edge, conditional
on exactly one input: for each word stack, a list of at most `L` low-degree pairs whose
members capture every `mcaEvent`-bad scalar.  Everything else — the funnel from capture
lists to `JohnsonNumericBound` — is in-tree and axiom-clean. -/
theorem johnsonNumericBound_holds_of_capture_production
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hk : k ≤ Fintype.card ι₀)
    (hL : (L : ℝ) ≤ (hab25M (Fintype.card ι₀) k η + 1/2) /
      hab25RhoPlus (Fintype.card ι₀) k ^ ((1 : ℝ) / 2))
    (hproduce : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ pairs : Finset (F₀[X] × F₀[X]), pairs.card ≤ L ∧
        (∀ ab ∈ pairs, ab.1.natDegree < k ∧ ab.2.natDegree < k) ∧
        ∀ γ ∈ hab25McaBadScalars domain k δ u,
          ∃ ab ∈ pairs, AffineCaptured domain k δ u γ ab) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_affine_capture_of_list_shape domain k η δ L hη hδ hk hL hproduce

open Classical in
/-- **The dichotomy-production obligation.**  The unconditional numeric edge, conditional
on exactly one input: for each word stack, a dichotomy bundle covering its bad scalars
within a budget `B` satisfying the Johnson arithmetic. -/
theorem johnsonNumericBound_holds_of_dichotomy_production
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (B : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδ,
        (Finset.univ.filter
          (fun γ : F₀ =>
            mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)
          ⊆ A.Edis) ∧
        A.ℓ * max A.T (Fintype.card ι₀) ≤ B)
    (harith : (B : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_forall_dichotomy domain k η δ hη hδ B hdata harith

open Classical in
/-- **The factor-data production obligation.**  This is the most recent canonical #302
consumer: for each word stack, produce the `PerPairFactorData` bundle from the GS/BCIKS20
surface, and prove the single real closing inequality for the uniform `(ℓ, T)` budget. -/
theorem johnsonNumericBound_holds_of_factorData_production
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (ℓ T : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      Nonempty (BCIKS20.Claim510Bundle.PerPairFactorData domain k δ u ℓ T))
    (hpos : 0 ≤ johnsonBoundReal domain k η δ)
    (hreal : ((ℓ * max T (Fintype.card ι₀) : ℕ) : ℝ)
      ≤ johnsonBoundReal domain k η δ * (Fintype.card F₀ : ℝ)) :
    JohnsonNumericBound domain k η δ :=
  BCIKS20.Claim510Bundle.johnsonNumericBound_of_perPairFactorData_real
    domain k η δ hη hδ ℓ T hdata hpos hreal

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_holds_of_capture_production
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_holds_of_dichotomy_production
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_holds_of_factorData_production
