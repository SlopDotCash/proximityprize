/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Bad-scalar count adapters for repaired line-decoding coverage

This module routes the named repaired bad-scalar double-cover surface through the generic
finite-count lemmas in `MCABadCount.lean`.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The named repaired bad-scalar surface gives zero bad scalars via the generic
`∀ γ, ¬ mcaEvent` count lemma. -/
theorem mcaBadCount_eq_zero_of_badScalarDoubleCover_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F,
      MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 :=
  mcaBadCount_eq_zero_of_forall_not_mcaEvent C δ u₀ u₁ fun γ =>
    MCABadScalarDoubleCover.not_mcaEvent C δ u₀ u₁ γ (hcov γ)

/-- The named repaired bad-scalar surface gives `ε_mca = 0` via the generic no-event
stack-count lemma. -/
theorem epsMCA_eq_zero_of_badScalarDoubleCover_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_forall_not_mcaEvent C δ fun u γ =>
    MCABadScalarDoubleCover.not_mcaEvent C δ (u 0) (u 1) γ (hcov u γ)

/-- All-stack bad-scalar double-cover data gives zero bad-scalar counts for every stack. -/
theorem forall_mcaBadCount_eq_zero_of_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0 := by
  intro u
  exact mcaBadCount_eq_zero_of_badScalarDoubleCover C δ (u 0) (u 1) (hcov u)

/-- Per-stack zero bad-scalar counts repack as all-stack bad-scalar double-cover data. -/
theorem badScalarDoubleCover_of_forall_mcaBadCount_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hzero : ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  intro u
  exact badScalarDoubleCover_of_mcaBadCount_eq_zero C δ (u 0) (u 1) (hzero u)

/-- All-stack bad-scalar double-cover data is exact: it is equivalent to zero bad-scalar counts
for every stack. -/
theorem forall_mcaBadCount_eq_zero_iff_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) :
    (∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  constructor
  · exact badScalarDoubleCover_of_forall_mcaBadCount_eq_zero C δ
  · exact forall_mcaBadCount_eq_zero_of_badScalarDoubleCover C δ

/-- Indexed bad-scalar double-cover data gives zero bad-scalar counts at every index. This
matches all-rate prize hypotheses without specializing to `Fin 4`. -/
theorem indexed_forall_mcaBadCount_eq_zero_of_badScalarDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hcov : ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ) :
    ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0 := by
  intro j
  exact forall_mcaBadCount_eq_zero_of_badScalarDoubleCover (C j) (δ j) (hcov j)

/-- Indexed zero bad-scalar counts repack as indexed bad-scalar double-cover data. -/
theorem indexed_badScalarDoubleCover_of_forall_mcaBadCount_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hzero : ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0) :
    ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ := by
  intro j
  exact badScalarDoubleCover_of_forall_mcaBadCount_eq_zero (C j) (δ j) (hzero j)

/-- Indexed zero bad-scalar counts are exact for the indexed bad-scalar double-cover surface. -/
theorem indexed_forall_mcaBadCount_eq_zero_iff_badScalarDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0) :
    (∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0) ↔
      ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ := by
  constructor
  · exact indexed_badScalarDoubleCover_of_forall_mcaBadCount_eq_zero C δ
  · exact indexed_forall_mcaBadCount_eq_zero_of_badScalarDoubleCover C δ

/-- Indexed `MCAForallDoubleCover` data gives zero bad-scalar counts at every index. -/
theorem indexed_forall_mcaBadCount_eq_zero_of_MCAForallDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hcov : ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j)) :
    ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0 := by
  intro j
  exact (MCAForallDoubleCover_iff_forall_mcaBadCount_eq_zero (C j) (δ j)).mp (hcov j)

/-- Indexed zero bad-scalar counts repack as indexed `MCAForallDoubleCover` data. -/
theorem indexed_MCAForallDoubleCover_of_forall_mcaBadCount_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hzero : ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0) :
    ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j) := by
  intro j
  exact (MCAForallDoubleCover_iff_forall_mcaBadCount_eq_zero (C j) (δ j)).mpr (hzero j)

/-- Indexed zero bad-scalar counts are exact for indexed `MCAForallDoubleCover` data. -/
theorem indexed_forall_mcaBadCount_eq_zero_iff_MCAForallDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0) :
    (∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0) ↔
      ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j) := by
  constructor
  · exact indexed_MCAForallDoubleCover_of_forall_mcaBadCount_eq_zero C δ
  · exact indexed_forall_mcaBadCount_eq_zero_of_MCAForallDoubleCover C δ

/-- Indexed vanishing MCA error gives zero bad-scalar counts at every index. -/
theorem indexed_forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (heps : ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) :
    ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0 := by
  intro j
  exact (epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero (C j) (δ j)).mp (heps j)

/-- Indexed zero bad-scalar counts give vanishing MCA error at every index. -/
theorem indexed_epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hzero : ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0) :
    ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0 := by
  intro j
  exact (epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero (C j) (δ j)).mpr (hzero j)

/-- Indexed vanishing MCA error is exact for indexed zero bad-scalar counts. -/
theorem indexed_epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0) :
    (∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) ↔
      ∀ j : κ, ∀ u : WordStack A (Fin 2) ι,
        mcaBadCount (F := F) (C j) (δ j) (u 0) (u 1) = 0 := by
  constructor
  · exact indexed_forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero C δ
  · exact indexed_epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero C δ

/-- Indexed vanishing MCA error repacks as indexed `MCAForallDoubleCover` data. -/
theorem indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (heps : ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) :
    ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j) := by
  intro j
  exact (epsMCA_eq_zero_iff_MCAForallDoubleCover (C j) (δ j)).mp (heps j)

/-- Indexed `MCAForallDoubleCover` data gives vanishing MCA error at every index. -/
theorem indexed_epsMCA_eq_zero_of_MCAForallDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hcov : ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j)) :
    ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0 := by
  intro j
  exact (epsMCA_eq_zero_iff_MCAForallDoubleCover (C j) (δ j)).mpr (hcov j)

/-- Indexed vanishing MCA error is exact for indexed `MCAForallDoubleCover` data. -/
theorem indexed_epsMCA_eq_zero_iff_MCAForallDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0) :
    (∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) ↔
      ∀ j : κ, MCAForallDoubleCover (F := F) (A := A) (C j) (δ j) := by
  constructor
  · exact indexed_MCAForallDoubleCover_of_epsMCA_eq_zero C δ
  · exact indexed_epsMCA_eq_zero_of_MCAForallDoubleCover C δ

/-- Indexed vanishing MCA error repacks as indexed bad-scalar double-cover data. -/
theorem indexed_badScalarDoubleCover_of_epsMCA_eq_zero
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (heps : ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) :
    ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ := by
  intro j
  exact (epsMCA_eq_zero_iff_badScalarDoubleCover (C j) (δ j)).mp (heps j)

/-- Indexed bad-scalar double-cover data gives vanishing MCA error at every index. -/
theorem indexed_epsMCA_eq_zero_of_badScalarDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0)
    (hcov : ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ) :
    ∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0 := by
  intro j
  exact (epsMCA_eq_zero_iff_badScalarDoubleCover (C j) (δ j)).mpr (hcov j)

/-- Indexed vanishing MCA error is exact for indexed bad-scalar double-cover data. -/
theorem indexed_epsMCA_eq_zero_iff_badScalarDoubleCover
    {κ : Type} (C : κ → Set (ι → A)) (δ : κ → ℝ≥0) :
    (∀ j : κ, epsMCA (F := F) (C j) (δ j) = 0) ↔
      ∀ j : κ, ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) (C j) (δ j) (u 0) (u 1) γ := by
  constructor
  · exact indexed_badScalarDoubleCover_of_epsMCA_eq_zero C δ
  · exact indexed_epsMCA_eq_zero_of_badScalarDoubleCover C δ

set_option linter.style.longLine false in
#print axioms ProximityGap.mcaBadCount_eq_zero_of_badScalarDoubleCover_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.epsMCA_eq_zero_of_badScalarDoubleCover_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.forall_mcaBadCount_eq_zero_of_badScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.badScalarDoubleCover_of_forall_mcaBadCount_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.forall_mcaBadCount_eq_zero_iff_badScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_forall_mcaBadCount_eq_zero_of_badScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_badScalarDoubleCover_of_forall_mcaBadCount_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_forall_mcaBadCount_eq_zero_iff_badScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_forall_mcaBadCount_eq_zero_of_MCAForallDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_MCAForallDoubleCover_of_forall_mcaBadCount_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_forall_mcaBadCount_eq_zero_iff_MCAForallDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_iff_forall_mcaBadCount_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_of_MCAForallDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_iff_MCAForallDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_badScalarDoubleCover_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_of_badScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.indexed_epsMCA_eq_zero_iff_badScalarDoubleCover

end

end ProximityGap


