/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Improve
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonCountWiring

/-!
# The dichotomy bundle assembly — one named production for the Johnson numeric edge (#302)

Packages the per-word-pair factor-family data into `Hab25JohnsonDichotomyData` and threads
it through the numeric bridge (`johnsonNumericBound_of_forall_dichotomy`), so that the
ENTIRE remaining [Hab25] discharge is the single named production `PerPairFactorData`:

* a factor index family of size ≤ ℓ (the GS list-size bound, S3);
* per-factor bad-scalar sets covering the pair's `mcaEvent`-bad scalars (the per-`γ`
  decoded-root factor assignment, S4);
* the per-factor dichotomy disjunct — light (`card ≤ T`) or improving pair — whose heavy
  branch is PRODUCED by `Claim510Improve.improve_disjunct_of_heavy` from the landed
  geometric arc.

## Main results

* `PerPairFactorData` — the single named per-pair production obligation.
* `dichotomyData_of_factorData` — the bundle from the data (structure assembly).
* `johnsonNumericBound_of_perPairFactorData` — **the numeric edge** from per-pair data +
  the closing arithmetic.

## References

* [BCIKS20] ePrint 2020/654 §5; [Hab25] ePrint 2025/2110.
-/

open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open _root_.ProximityGap Code
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace BCIKS20.Claim510Bundle

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

open Classical in
/-- **The single named per-pair production obligation**: a factor family of size ≤ ℓ whose
per-factor bad-scalar sets cover the pair's `mcaEvent`-bad scalars, each factor light
(`card ≤ T`) or carrying an improving pair.  The heavy branch is produced by
`Claim510Improve.improve_disjunct_of_heavy`; the cover and the factor count are the S4/S3
outputs of the per-pair GS chain. -/
structure PerPairFactorData (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : Code.WordStack F₀ (Fin 2) ι₀) (ℓ T : ℕ) where
  /-- factor index type -/
  Idx : Type
  /-- decidable equality -/
  decIdx : DecidableEq Idx
  /-- the finite factor family -/
  Index : Finset Idx
  /-- S3: the factor count is bounded by the list size -/
  hYbound : Index.card ≤ ℓ
  /-- the per-factor bad-scalar sets -/
  Efactor : Idx → Finset F₀
  /-- S4: every `mcaEvent`-bad scalar lies in some factor's set -/
  hcover : Finset.univ.filter
      (fun γ : F₀ =>
        mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)
    ⊆ Index.biUnion Efactor
  /-- the per-factor dichotomy: light, or an improving pair -/
  hdichotomy : ∀ ij ∈ Index,
    (Efactor ij).card ≤ T ∨
    ∃ d₀ d₁ : ι₀ → F₀, ∀ z ∈ Efactor ij,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0

open Classical in
/-- **The bundle from the data** — structure assembly with
`Edis := the mcaEvent-bad scalars`. -/
noncomputable def dichotomyData_of_factorData
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    {u : Code.WordStack F₀ (Fin 2) ι₀} {ℓ T : ℕ}
    (P : PerPairFactorData domain k δ u ℓ T) :
    Hab25JohnsonDichotomyData domain k η δ hη hδ where
  Idx := P.Idx
  decIdx := P.decIdx
  Index := P.Index
  ℓ := ℓ
  T := T
  hYbound := P.hYbound
  Edis := Finset.univ.filter
    (fun γ : F₀ =>
      mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)
  Efactor := P.Efactor
  hcover := P.hcover
  hdichotomy := P.hdichotomy

open Classical in
/-- **The Johnson numeric edge from the per-pair production** ([Hab25] Theorem 2 modulo
the closing arithmetic): per-pair factor data at uniform `(ℓ, T)` + the arithmetic
`ℓ·max(T,n)/|F| ≤ johnsonBoundReal` discharge `JohnsonNumericBound`. -/
theorem johnsonNumericBound_of_perPairFactorData
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (ℓ T : ℕ)
    (hdata : ∀ u : Code.WordStack F₀ (Fin 2) ι₀,
      Nonempty (PerPairFactorData domain k δ u ℓ T))
    (harith : ((ℓ * max T (Fintype.card ι₀) : ℕ) : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ := by
  refine johnsonNumericBound_of_forall_dichotomy domain k η δ hη hδ
    (ℓ * max T (Fintype.card ι₀)) (fun u => ?_) harith
  obtain ⟨P⟩ := hdata u
  exact ⟨dichotomyData_of_factorData hη hδ P, subset_rfl, le_rfl⟩

end BCIKS20.Claim510Bundle

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Bundle.dichotomyData_of_factorData
#print axioms BCIKS20.Claim510Bundle.johnsonNumericBound_of_perPairFactorData
