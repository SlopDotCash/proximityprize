/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientSupport
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveWorstCaseIncidence

/-!
# Standard linear-algebra API for quotient rank-two pencils

The production incidence reduction uses `RowsIndependentModCode`, an elementary relation predicate
on two words.  This module identifies it with Mathlib's `LinearIndependent` predicate on the two
quotient classes and with the basis-free quotient pencil having finrank two.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open ProximityGap

namespace ProximityGap.ProjectiveRankTwoAPI

open ProjectiveQuotientSupport
open ProjectiveWorstCaseIncidence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The two row classes as a `Fin 2`-indexed family in the quotient by the code. -/
def quotientRows (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    Fin 2 → ((ι → A) ⧸ C) :=
  ![Submodule.Quotient.mk (p := C) u₀, Submodule.Quotient.mk (p := C) u₁]

/-- A nontrivial row relation modulo the code is exactly linear dependence of the two quotient
classes. -/
theorem rowsDependentModCode_iff_not_linearIndependent
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    RowsDependentModCode C u₀ u₁ ↔
      ¬ LinearIndependent F (quotientRows C u₀ u₁) := by
  classical
  constructor
  · rintro ⟨a, b, hab, hmem⟩ hli
    have hmk :
        Submodule.Quotient.mk (p := C) (a • u₀ + b • u₁) = 0 :=
      (Submodule.Quotient.mk_eq_zero C).2 hmem
    have hsum :
        ∑ i : Fin 2, (![a, b] : Fin 2 → F) i • quotientRows C u₀ u₁ i = 0 := by
      simpa [quotientRows, Fin.sum_univ_two, ← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_add] using hmk
    have hcoeff := (Fintype.linearIndependent_iff.mp hli) (![a, b] : Fin 2 → F) hsum
    have ha0 : a = 0 := by simpa using hcoeff 0
    have hb0 : b = 0 := by simpa using hcoeff 1
    exact hab.elim (fun ha => ha ha0) (fun hb => hb hb0)
  · intro hnli
    obtain ⟨g, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
    have hab : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    have hmk :
        Submodule.Quotient.mk (p := C) (g 0 • u₀ + g 1 • u₁) = 0 := by
      simpa [quotientRows, Fin.sum_univ_two, ← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_add] using hsum
    exact ⟨g 0, g 1, hab, (Submodule.Quotient.mk_eq_zero C).1 hmk⟩

/-- The campaign's quotient-rank predicate is Mathlib linear independence of the two quotient
classes. -/
theorem rowsIndependentModCode_iff_linearIndependent
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    RowsIndependentModCode C u₀ u₁ ↔
      LinearIndependent F (quotientRows C u₀ u₁) := by
  classical
  unfold RowsIndependentModCode
  rw [rowsDependentModCode_iff_not_linearIndependent]
  simp

/-- The range of `quotientRows` is the unordered pair used by `quotientPencil`. -/
theorem range_quotientRows (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    Set.range (quotientRows C u₀ u₁) =
      {Submodule.Quotient.mk (p := C) u₀, Submodule.Quotient.mk (p := C) u₁} := by
  ext q
  simp [quotientRows, or_comm]

/-- A genuine rank-two quotient pencil has dimension exactly two. -/
theorem finrank_quotientPencil_eq_two
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A)
    (hind : RowsIndependentModCode C u₀ u₁) :
    Module.finrank F (quotientPencil C u₀ u₁) = 2 := by
  have hli := (rowsIndependentModCode_iff_linearIndependent C u₀ u₁).mp hind
  rw [quotientPencil, ← range_quotientRows C u₀ u₁,
    finrank_span_eq_card hli, Fintype.card_fin]

/-- Rank-two independence is equivalently the basis-free quotient pencil having dimension two. -/
theorem rowsIndependentModCode_iff_finrank_quotientPencil_eq_two
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    RowsIndependentModCode C u₀ u₁ ↔
      Module.finrank F (quotientPencil C u₀ u₁) = 2 := by
  rw [rowsIndependentModCode_iff_linearIndependent,
    linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin,
    range_quotientRows C u₀ u₁]
  change 2 = Module.finrank F (quotientPencil C u₀ u₁) ↔ _
  rw [eq_comm]

end ProximityGap.ProjectiveRankTwoAPI

/-! ## Axiom audit -/
#print axioms
  ProximityGap.ProjectiveRankTwoAPI.rowsDependentModCode_iff_not_linearIndependent
#print axioms ProximityGap.ProjectiveRankTwoAPI.rowsIndependentModCode_iff_linearIndependent
#print axioms ProximityGap.ProjectiveRankTwoAPI.range_quotientRows
#print axioms ProximityGap.ProjectiveRankTwoAPI.finrank_quotientPencil_eq_two
#print axioms
  ProximityGap.ProjectiveRankTwoAPI.rowsIndependentModCode_iff_finrank_quotientPencil_eq_two
