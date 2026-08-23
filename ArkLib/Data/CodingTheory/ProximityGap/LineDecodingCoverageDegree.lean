/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Degree-cover adapters for repaired line decoding

`CoveragePigeonhole.lean` supplies the incidence-counting side of the GG25 multi-`γ` extraction:
large total agreement mass forces coordinates with many covering scalars.  This module connects
that degree language to the repaired #140 double-cover predicates from `LineDecodingCoverage.lean`.

The declarations here are deliberately local: a coordinate degree `> 1` gives two distinct
scalars, and pointwise degree `> 1` on a witness set gives `MCADoubleCoverOn`.  They do not
construct the Guruswami--Sudan cover or prove global `MCAForallDoubleCover`.
-/

namespace ProximityGap

open Finset
open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

omit [Fintype ι] [Nonempty ι] [Field F] [DecidableEq F] in
/-- A coordinate with scalar-cover degree greater than one has two distinct covering scalars. -/
theorem exists_two_scalars_of_degree_gt_one
    (T : F → Finset ι) {i : ι}
    (hdeg : 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card) :
    ∃ a a' : F, a ≠ a' ∧ i ∈ T a ∧ i ∈ T a' := by
  rcases Finset.one_lt_card.mp hdeg with ⟨a, ha, a', ha', hne⟩
  simp only [mem_filter, mem_univ, true_and] at ha ha'
  exact ⟨a, a', hne, ha, ha'⟩

omit [Nonempty ι] [Field F] [DecidableEq F] in
/-- Total scalar-cover mass above `|ι|` produces at least one doubly covered coordinate. -/
theorem exists_coordinate_two_scalars_of_total_card_gt
    (T : F → Finset ι)
    (hmass : Fintype.card ι < ∑ a : F, (T a).card) :
    ∃ i : ι, ∃ a a' : F, a ≠ a' ∧ i ∈ T a ∧ i ∈ T a' := by
  rcases ArkLib.Coverage.exists_degree_gt (S := T) (k := 1) (by simpa using hmass)
      with ⟨i, hdeg⟩
  exact ⟨i, exists_two_scalars_of_degree_gt_one T hdeg⟩

/-- Pointwise scalar-cover degree `> 1` pins the pair on the whole witness set. -/
theorem pairJointAgreesOn_of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ v₁ v₂ : ι → A)
    (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    pairJointAgreesOn C S u₀ u₁ := by
  refine pairJointAgreesOn_of_double_cover (F := F) (A := A) C S u₀ u₁ v₁ v₂ hv₁ hv₂ ?_
  intro i hi
  rcases exists_two_scalars_of_degree_gt_one T (hdeg i hi) with ⟨a, a', hne, ha, ha'⟩
  exact ⟨a, a', hne, hagree a i ha, hagree a' i ha'⟩

omit [Fintype ι] [Nonempty ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- Convert pointwise scalar-cover degree `> 1` into the repaired local `MCADoubleCoverOn`
surface. -/
theorem MCADoubleCoverOn.of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ v₁ v₂ : ι → A)
    (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    MCADoubleCoverOn (F := F) C u₀ u₁ S := by
  refine ⟨v₁, hv₁, v₂, hv₂, ?_⟩
  intro i hi
  rcases exists_two_scalars_of_degree_gt_one T (hdeg i hi) with ⟨a, a', hne, ha, ha'⟩
  exact ⟨a, a', hne, hagree a i ha, hagree a' i ha'⟩

/-- A bad-event witness body contradicts pointwise scalar-cover degree `> 1` on that body. -/
theorem not_mcaEventBody_of_scalarCover_degree_gt_one
    (C : Set (ι → A)) (u₀ u₁ : ι → A) (S : Finset ι)
    {v₁ v₂ : ι → A} (T : F → Finset ι)
    (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hdeg : ∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card)
    (hagree : ∀ (a : F) (i : ι), i ∈ T a →
      v₁ i + a • v₂ i = u₀ i + a • u₁ i) :
    False :=
  hpair (pairJointAgreesOn_of_scalarCover_degree_gt_one C S u₀ u₁ v₁ v₂ T
    hv₁ hv₂ hdeg hagree)

/-- **Per-bad-scalar scalar-degree cover obligation.** This is the incidence-degree version of
`MCABadScalarDoubleCover`: for every exposed bad-event witness set, it supplies a candidate
codeword pair and a scalar-indexed coordinate cover whose degree is `> 1` on the whole witness
set. -/
def MCABadScalarDegreeCover (C : Set (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) : Prop :=
  mcaEvent C δ u₀ u₁ γ →
    ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ¬ pairJointAgreesOn C S u₀ u₁ →
      ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∃ T : F → Finset ι,
        (∀ i ∈ S, 1 < (Finset.univ.filter (fun a : F => i ∈ T a)).card) ∧
        (∀ (a : F) (i : ι), i ∈ T a →
          v₁ i + a • v₂ i = u₀ i + a • u₁ i)

omit [Nonempty ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- A scalar-degree cover obligation supplies the named repaired bad-scalar double-cover
obligation. -/
theorem MCABadScalarDoubleCover.of_degreeCover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hcov : MCABadScalarDegreeCover (F := F) (A := A) C δ u₀ u₁ γ) :
    MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ := by
  intro hγ S hsize hwit hpair
  rcases hcov hγ S hsize hwit hpair with
    ⟨v₁, hv₁, v₂, hv₂, T, hdeg, hagree⟩
  exact MCADoubleCoverOn.of_scalarCover_degree_gt_one C S u₀ u₁ v₁ v₂ T
    hv₁ hv₂ hdeg hagree

/-- A per-stack/per-scalar family of scalar-degree cover obligations supplies the global repaired
T4.21 double-cover hypothesis. -/
theorem MCAForallDoubleCover.of_forall_degreeCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDegreeCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  MCAForallDoubleCover.of_badScalarDoubleCover C δ fun u γ =>
    MCABadScalarDoubleCover.of_degreeCover C δ (u 0) (u 1) γ (hcov u γ)

/-- A scalar-degree cover obligation rules out the corresponding MCA bad event. -/
theorem MCABadScalarDegreeCover.not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hcov : MCABadScalarDegreeCover (F := F) (A := A) C δ u₀ u₁ γ) :
    ¬ mcaEvent C δ u₀ u₁ γ :=
  MCABadScalarDoubleCover.not_mcaEvent C δ u₀ u₁ γ
    (MCABadScalarDoubleCover.of_degreeCover C δ u₀ u₁ γ hcov)

omit [Nonempty ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- A direct no-event certificate supplies the local scalar-degree cover obligation,
vacuously. -/
theorem MCABadScalarDegreeCover.of_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hno : ¬ mcaEvent C δ u₀ u₁ γ) :
    MCABadScalarDegreeCover (F := F) (A := A) C δ u₀ u₁ γ := by
  intro hγ
  exact False.elim (hno hγ)

/-- The local scalar-degree cover obligation is exact: it is equivalent to ruling out that
scalar's `mcaEvent`. -/
theorem MCABadScalarDegreeCover_iff_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    MCABadScalarDegreeCover (F := F) (A := A) C δ u₀ u₁ γ ↔
      ¬ mcaEvent C δ u₀ u₁ γ := by
  constructor
  · exact MCABadScalarDegreeCover.not_mcaEvent C δ u₀ u₁ γ
  · exact MCABadScalarDegreeCover.of_not_mcaEvent C δ u₀ u₁ γ

/-- Named all-stack/all-scalar scalar-degree cover frontier. This packages the family form used
by the repaired T4.21 wrappers. -/
def MCAForallDegreeCover (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin 2) ι) (γ : F),
    MCABadScalarDegreeCover (F := F) (A := A) C δ (u 0) (u 1) γ

/-- A global scalar-degree cover supplies the repaired double-cover frontier. -/
theorem MCAForallDegreeCover.to_doubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDegreeCover (F := F) (A := A) C δ) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  MCAForallDoubleCover.of_forall_degreeCover C δ hcov

/-- A global scalar-degree cover rules out every MCA bad event. -/
theorem MCAForallDegreeCover.not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDegreeCover (F := F) (A := A) C δ) :
    ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ := by
  intro u γ
  exact (MCABadScalarDegreeCover_iff_not_mcaEvent C δ (u 0) (u 1) γ).mp (hcov u γ)

/-- Repack direct no-bad-event data as the named global scalar-degree cover frontier. -/
theorem MCAForallDegreeCover.of_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hno : ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ) :
    MCAForallDegreeCover (F := F) (A := A) C δ :=
  fun u γ => (MCABadScalarDegreeCover_iff_not_mcaEvent C δ (u 0) (u 1) γ).mpr (hno u γ)

/-- The global scalar-degree cover surface is exact: it is equivalent to ruling out every bad
scalar event. -/
theorem MCAForallDegreeCover_iff_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDegreeCover (F := F) (A := A) C δ ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · exact MCAForallDegreeCover.not_mcaEvent C δ
  · exact MCAForallDegreeCover.of_forall_not_mcaEvent C δ

/-- The repaired double-cover frontier supplies the named scalar-degree cover frontier,
vacuously after ruling out every bad event. -/
theorem MCAForallDegreeCover.of_doubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    MCAForallDegreeCover (F := F) (A := A) C δ :=
  MCAForallDegreeCover.of_forall_not_mcaEvent C δ
    (MCAForallDoubleCover.not_mcaEvent C δ hcov)

/-- The named scalar-degree and double-cover global frontiers are equivalent. -/
theorem MCAForallDegreeCover_iff_doubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDegreeCover (F := F) (A := A) C δ ↔
      MCAForallDoubleCover (F := F) (A := A) C δ := by
  constructor
  · exact MCAForallDegreeCover.to_doubleCover C δ
  · exact MCAForallDegreeCover.of_doubleCover C δ

/-- A per-stack/per-scalar scalar-degree cover family kills every repaired bad-count. -/
theorem mcaBadCount_eq_zero_of_forall_degreeCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDegreeCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    ∀ u : WordStack A (Fin 2) ι, mcaBadCount (F := F) C δ (u 0) (u 1) = 0 :=
  MCAForallDoubleCover.forall_mcaBadCount_eq_zero C δ
    (MCAForallDoubleCover.of_forall_degreeCover C δ hcov)

/-- A per-stack/per-scalar scalar-degree cover family forces `ε_mca = 0`. -/
theorem epsMCA_eq_zero_of_forall_degreeCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDegreeCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_MCAForallDoubleCover C δ
    (MCAForallDoubleCover.of_forall_degreeCover C δ hcov)

/-- A named global scalar-degree cover kills every repaired bad-count. -/
theorem mcaBadCount_eq_zero_of_MCAForallDegreeCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDegreeCover (F := F) (A := A) C δ) :
    ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0 :=
  mcaBadCount_eq_zero_of_forall_degreeCover C δ hcov

/-- A named global scalar-degree cover forces `ε_mca = 0`. -/
theorem epsMCA_eq_zero_of_MCAForallDegreeCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDegreeCover (F := F) (A := A) C δ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_forall_degreeCover C δ hcov

/-- Vanishing MCA error repacks as the named global scalar-degree cover frontier. -/
theorem MCAForallDegreeCover.of_epsMCA_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0)
    (heps : epsMCA (F := F) C δ = 0) :
    MCAForallDegreeCover (F := F) (A := A) C δ :=
  (MCAForallDegreeCover_iff_doubleCover C δ).mpr
    ((epsMCA_eq_zero_iff_MCAForallDoubleCover C δ).mp heps)

/-- The named global scalar-degree cover surface is exact at `ε_mca = 0`. -/
theorem epsMCA_eq_zero_iff_MCAForallDegreeCover
    (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ = 0 ↔
      MCAForallDegreeCover (F := F) (A := A) C δ := by
  constructor
  · exact MCAForallDegreeCover.of_epsMCA_eq_zero C δ
  · exact epsMCA_eq_zero_of_MCAForallDegreeCover C δ

end

end ProximityGap

namespace CodingTheory

open ProximityGap
open NNReal Code
open scoped NNReal ProbabilityTheory

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section RepairedDegreeCoverTarget

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Repaired T4.21 front door from scalar-degree cover data. -/
theorem lineDecodable_imp_epsMCA_le_target_of_forall_degreeCover
    (C : ModuleCode ι F A) (δ a : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDegreeCover (F := F) (A := A) (C : Set (ι → A)) δ (u 0) (u 1) γ) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  exact lineDecodable_imp_epsMCA_le_target C δ a
    (MCAForallDoubleCover.of_forall_degreeCover (C : Set (ι → A)) δ hcov)

/-- Repaired T4.21 front door from the named global scalar-degree cover frontier. -/
theorem lineDecodable_imp_epsMCA_le_target_of_MCAForallDegreeCover
    (C : ModuleCode ι F A) (δ a : ℝ≥0)
    (hcov : MCAForallDegreeCover (F := F) (A := A) (C : Set (ι → A)) δ) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  exact lineDecodable_imp_epsMCA_le_target_of_forall_degreeCover C δ a hcov

end RepairedDegreeCoverTarget

end CodingTheory

#print axioms ProximityGap.exists_two_scalars_of_degree_gt_one
#print axioms ProximityGap.exists_coordinate_two_scalars_of_total_card_gt
set_option linter.style.longLine false in
#print axioms ProximityGap.pairJointAgreesOn_of_scalarCover_degree_gt_one
set_option linter.style.longLine false in
#print axioms ProximityGap.MCADoubleCoverOn.of_scalarCover_degree_gt_one
set_option linter.style.longLine false in
#print axioms ProximityGap.not_mcaEventBody_of_scalarCover_degree_gt_one
set_option linter.style.longLine false in
#print axioms ProximityGap.MCABadScalarDegreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCABadScalarDoubleCover.of_degreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDoubleCover.of_forall_degreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCABadScalarDegreeCover.not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCABadScalarDegreeCover.of_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCABadScalarDegreeCover_iff_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover.to_doubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover.not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover.of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover_iff_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover.of_doubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover_iff_doubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.mcaBadCount_eq_zero_of_forall_degreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.epsMCA_eq_zero_of_forall_degreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.mcaBadCount_eq_zero_of_MCAForallDegreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.epsMCA_eq_zero_of_MCAForallDegreeCover
set_option linter.style.longLine false in
#print axioms ProximityGap.MCAForallDegreeCover.of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.epsMCA_eq_zero_iff_MCAForallDegreeCover
set_option linter.style.longLine false in
#print axioms CodingTheory.lineDecodable_imp_epsMCA_le_target_of_forall_degreeCover
set_option linter.style.longLine false in
#print axioms CodingTheory.lineDecodable_imp_epsMCA_le_target_of_MCAForallDegreeCover
