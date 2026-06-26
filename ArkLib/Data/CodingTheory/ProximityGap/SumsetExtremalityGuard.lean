/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SumsetExtremalityReduction

/-!
# Guarded sumset extremality

`SumsetExtremalityReduction.lean` packages the useful monomial-family reduction:
if every stack is dominated by a selected family `M`, and every member of `M` is budgeted,
then the open core `WorstCaseIncidenceBounded` follows.

This file records the corrected guarded shape.  A future extremality theorem may only cover a
window/far/large-field class of stacks.  To consume it for the open core, one must also bound the
complement of that guard.  The file also gives the reusable strict-counterexample theorem: one
stack beating every selected representative refutes the guard-free extremality hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.OpenCoreConditionalPin Code

namespace ProximityGap.SumsetExtremality

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- A stack-restricted incidence budget.  `G` is the guard selecting the part of stack space
where a proposed extremality or line-list theorem is meant to apply. -/
def StackIncidenceBoundedOn (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (G : WordStack A (Fin 2) ι → Prop) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, G u → incCount (F := F) C δ u ≤ B

open Classical in
/-- Guarded family extremality: every stack satisfying `G` is dominated by some member of the
selected family `M`.  The guard can encode the prize window, a far-line condition, or any other
side condition needed to exclude known low-field/near-line counterexamples. -/
def FamilyExtremalOn (C : Set (ι → A)) (δ : ℝ≥0)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, G u →
    ∃ v ∈ M, incCount (F := F) C δ u ≤ incCount (F := F) C δ v

open Classical in
/-- The guard-free `SumsetExtremal` is the special case of `FamilyExtremalOn` with the trivial
guard. -/
theorem familyExtremalOn_true_iff_sumsetExtremal
    (C : Set (ι → A)) (δ : ℝ≥0) (M : Set (WordStack A (Fin 2) ι)) :
    FamilyExtremalOn (F := F) C δ M (fun _ => True) ↔
      SumsetExtremal (F := F) C δ M := by
  constructor
  · intro h u
    exact h u trivial
  · intro h u _hu
    exact h u

open Classical in
/-- The open core is the special case of `StackIncidenceBoundedOn` with the trivial guard. -/
theorem stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) :
    StackIncidenceBoundedOn (F := F) C δ B (fun _ => True) ↔
      WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  rw [worstCaseIncidenceBounded_iff]
  constructor
  · intro h u
    exact h u trivial
  · intro h u _hu
    exact h u

open Classical in
/-- A guarded family-extremality theorem plus a budget on the selected family budgets every stack
inside the guard. -/
theorem stackIncidenceBoundedOn_of_familyExtremalOn
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : FamilyExtremalOn (F := F) C δ M G) :
    StackIncidenceBoundedOn (F := F) C δ B G := by
  intro u hu
  obtain ⟨v, hvM, hle⟩ := hext u hu
  exact le_trans hle (hM v hvM)

open Classical in
/-- Split consumer for the corrected extremality route.  If the selected family dominates the
guarded branch and the complementary branch is budgeted separately, then the full open-core
incidence budget follows. -/
theorem worstCaseIncidenceBounded_of_split_familyExtremalOn
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : FamilyExtremalOn (F := F) C δ M G)
    (houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u)) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  rw [← stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded]
  intro u _hu
  by_cases hG : G u
  · exact stackIncidenceBoundedOn_of_familyExtremalOn C δ B M G hM hext u hG
  · exact houtside u hG

/-- The split guarded route plugged into the conditional `δ*` pin. -/
theorem mcaDeltaStar_pin_of_split_familyExtremalOn
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hδ : δ ≤ 1)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : FamilyExtremalOn (F := F) C δ M G)
    (houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_split_familyExtremalOn C δ B M G hM hext houtside)
    hbudget

open Classical in
/-- Failure of a guarded stack budget is exactly an over-budget stack satisfying the guard. -/
theorem not_stackIncidenceBoundedOn_iff_exists_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (G : WordStack A (Fin 2) ι → Prop) :
    ¬ StackIncidenceBoundedOn (F := F) C δ B G ↔
      ∃ u : WordStack A (Fin 2) ι, G u ∧ B < incCount (F := F) C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u hu
    exact le_of_not_gt (fun hgt => hnone ⟨u, hu, hgt⟩)
  · rintro ⟨u, hu, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded u hu)) hgt

open Classical in
/-- Failure of guarded family extremality is exactly a guarded stack that strictly beats every
selected representative. -/
theorem not_familyExtremalOn_iff_exists_strict_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop) :
    ¬ FamilyExtremalOn (F := F) C δ M G ↔
      ∃ u : WordStack A (Fin 2) ι, G u ∧
        ∀ v ∈ M, incCount (F := F) C δ v < incCount (F := F) C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u hu
    by_contra hnoRep
    apply hnone
    refine ⟨u, hu, ?_⟩
    intro v hvM
    exact lt_of_not_ge (fun huv => hnoRep ⟨v, hvM, huv⟩)
  · rintro ⟨u, hu, hgt⟩ hext
    obtain ⟨v, hvM, hle⟩ := hext u hu
    exact (not_lt_of_ge hle) (hgt v hvM)

open Classical in
/-- Failure of the full open-core incidence budget is exactly an over-budget stack. -/
theorem not_worstCaseIncidenceBounded_iff_exists_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) :
    ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B ↔
      ∃ u : WordStack A (Fin 2) ι, B < incCount (F := F) C δ u := by
  rw [← stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded]
  constructor
  · intro hnot
    obtain ⟨u, _hu, hgt⟩ :=
      (not_stackIncidenceBoundedOn_iff_exists_counterexample
        (F := F) C δ B (fun _ : WordStack A (Fin 2) ι => True)).mp hnot
    exact ⟨u, hgt⟩
  · rintro ⟨u, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded u trivial)) hgt

open Classical in
/-- If a selected family is budgeted and the complement branch is budgeted, then any failure of the
full incidence budget produces a guarded stack that strictly beats every selected representative. -/
theorem exists_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u))
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    ∃ u : WordStack A (Fin 2) ι, G u ∧
      ∀ v ∈ M, incCount (F := F) C δ v < incCount (F := F) C δ u := by
  have hnotExt : ¬ FamilyExtremalOn (F := F) C δ M G := by
    intro hext
    exact hnot (worstCaseIncidenceBounded_of_split_familyExtremalOn
      C δ B M G hM hext houtside)
  exact (not_familyExtremalOn_iff_exists_strict_counterexample C δ M G).mp hnotExt

open Classical in
/-- If a selected family is budgeted and guarded domination holds, then any failure of the full
incidence budget produces an over-budget stack outside the guard. -/
theorem exists_outside_counterexample_of_not_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hext : FamilyExtremalOn (F := F) C δ M G)
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    ∃ u : WordStack A (Fin 2) ι, ¬ G u ∧ B < incCount (F := F) C δ u := by
  have hnotOutside :
      ¬ StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u) := by
    intro houtside
    exact hnot (worstCaseIncidenceBounded_of_split_familyExtremalOn
      C δ B M G hM hext houtside)
  exact (not_stackIncidenceBoundedOn_iff_exists_counterexample
    (F := F) C δ B (fun u => ¬ G u)).mp hnotOutside

open Classical in
/-- Scanner form for a failed guarded split.  Once the selected family itself is budgeted, a
counterexample to the full open-core incidence budget is either outside the guard or is a guarded
stack that strictly beats every selected representative. -/
theorem outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hM : MonomialIncidenceBounded (F := F) C δ B M)
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    (∃ u : WordStack A (Fin 2) ι, ¬ G u ∧ B < incCount (F := F) C δ u) ∨
      ∃ u : WordStack A (Fin 2) ι, G u ∧
        ∀ v ∈ M, incCount (F := F) C δ v < incCount (F := F) C δ u := by
  by_cases houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u)
  · exact Or.inr
      (exists_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
        C δ B M G hM houtside hnot)
  · exact Or.inl
      ((not_stackIncidenceBoundedOn_iff_exists_counterexample
        (F := F) C δ B (fun u => ¬ G u)).mp houtside)

open Classical in
/-- One guarded stack that strictly beats every selected representative refutes guarded
family extremality. -/
theorem not_familyExtremalOn_of_strict_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0)
    (M : Set (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (u : WordStack A (Fin 2) ι)
    (hu : G u)
    (hgt : ∀ v ∈ M, incCount (F := F) C δ v < incCount (F := F) C δ u) :
    ¬ FamilyExtremalOn (F := F) C δ M G := by
  intro hext
  obtain ⟨v, hvM, hle⟩ := hext u hu
  exact (not_lt_of_ge hle) (hgt v hvM)

open Classical in
/-- Guard-free specialization: one stack beating every selected representative refutes the old
unqualified `SumsetExtremal` hypothesis. -/
theorem not_sumsetExtremal_of_strict_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0)
    (M : Set (WordStack A (Fin 2) ι)) (u : WordStack A (Fin 2) ι)
    (hgt : ∀ v ∈ M, incCount (F := F) C δ v < incCount (F := F) C δ u) :
    ¬ SumsetExtremal (F := F) C δ M := by
  rw [← familyExtremalOn_true_iff_sumsetExtremal]
  exact not_familyExtremalOn_of_strict_counterexample C δ M (fun _ => True) u trivial hgt

open Classical in
/-- A single over-budget stack refutes the full open-core incidence budget. -/
theorem not_worstCaseIncidenceBounded_of_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) (u : WordStack A (Fin 2) ι)
    (hgt : B < incCount (F := F) C δ u) :
    ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  rw [← stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded]
  intro hbounded
  exact (not_lt_of_ge (hbounded u trivial)) hgt

/-! ## Finite-family scanner surface -/

open Classical in
/-- Finite-family form of the selected-family budget.  This is the scanner-facing version of
`MonomialIncidenceBounded` when the proposed extremal catalogue is an explicit `Finset`. -/
theorem monomialIncidenceBounded_finset_coe_iff
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (R : Finset (WordStack A (Fin 2) ι)) :
    MonomialIncidenceBounded (F := F) C δ B (R : Set (WordStack A (Fin 2) ι)) ↔
      ∀ r : WordStack A (Fin 2) ι, r ∈ R → incCount (F := F) C δ r ≤ B := by
  constructor
  · intro h r hr
    exact h r (by simpa using hr)
  · intro h r hr
    exact h r (by simpa using hr)

open Classical in
/-- Finite-family form of guarded extremality.  A guarded stack must be dominated by one member of
the explicit catalogue `R`. -/
theorem familyExtremalOn_finset_coe_iff
    (C : Set (ι → A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop) :
    FamilyExtremalOn (F := F) C δ (R : Set (WordStack A (Fin 2) ι)) G ↔
      ∀ u : WordStack A (Fin 2) ι, G u →
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧
          incCount (F := F) C δ u ≤ incCount (F := F) C δ r := by
  constructor
  · intro h u hu
    rcases h u hu with ⟨r, hr, hle⟩
    exact ⟨r, by simpa using hr, hle⟩
  · intro h u hu
    rcases h u hu with ⟨r, hr, hle⟩
    exact ⟨r, by simpa using hr, hle⟩

open Classical in
/-- Finite-family guarded consumer: a budget on an explicit catalogue and guarded domination by
that catalogue budget every stack satisfying the guard. -/
theorem stackIncidenceBoundedOn_of_finsetFamilyExtremalOn
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hR : ∀ r : WordStack A (Fin 2) ι, r ∈ R → incCount (F := F) C δ r ≤ B)
    (hext : ∀ u : WordStack A (Fin 2) ι, G u →
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧
        incCount (F := F) C δ u ≤ incCount (F := F) C δ r) :
    StackIncidenceBoundedOn (F := F) C δ B G := by
  intro u hu
  rcases hext u hu with ⟨r, hr, hle⟩
  exact le_trans hle (hR r hr)

open Classical in
/-- Split consumer for an explicit finite catalogue.  The full open-core incidence budget follows
from finite-family domination on the guarded branch and a separate complement budget. -/
theorem worstCaseIncidenceBounded_of_split_finsetFamilyExtremalOn
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hR : ∀ r : WordStack A (Fin 2) ι, r ∈ R → incCount (F := F) C δ r ≤ B)
    (hext : ∀ u : WordStack A (Fin 2) ι, G u →
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧
        incCount (F := F) C δ u ≤ incCount (F := F) C δ r)
    (houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u)) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  exact worstCaseIncidenceBounded_of_split_familyExtremalOn
    C δ B (R : Set (WordStack A (Fin 2) ι)) G
    ((monomialIncidenceBounded_finset_coe_iff C δ B R).mpr hR)
    ((familyExtremalOn_finset_coe_iff C δ R G).mpr hext)
    houtside

/-- The finite-catalogue guarded split plugged into the conditional `δ*` pin. -/
theorem mcaDeltaStar_pin_of_split_finsetFamilyExtremalOn
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hδ : δ ≤ 1)
    (hR : ∀ r : WordStack A (Fin 2) ι, r ∈ R → incCount (F := F) C δ r ≤ B)
    (hext : ∀ u : WordStack A (Fin 2) ι, G u →
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧
        incCount (F := F) C δ u ≤ incCount (F := F) C δ r)
    (houtside : StackIncidenceBoundedOn (F := F) C δ B (fun u => ¬ G u))
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_split_finsetFamilyExtremalOn
      C δ B R G hR hext houtside)
    hbudget

open Classical in
/-- Failure of finite-catalogue guarded domination is exactly a guarded stack that strictly beats
every catalogue member. -/
theorem not_finsetFamilyExtremalOn_iff_exists_strict_counterexample
    (C : Set (ι → A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop) :
    (¬ ∀ u : WordStack A (Fin 2) ι, G u →
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧
          incCount (F := F) C δ u ≤ incCount (F := F) C δ r) ↔
      ∃ u : WordStack A (Fin 2) ι, G u ∧
        ∀ r : WordStack A (Fin 2) ι, r ∈ R →
          incCount (F := F) C δ r < incCount (F := F) C δ u := by
  rw [← familyExtremalOn_finset_coe_iff C δ R G]
  constructor
  · intro hnot
    rcases (not_familyExtremalOn_iff_exists_strict_counterexample
      C δ (R : Set (WordStack A (Fin 2) ι)) G).mp hnot with ⟨u, hu, hbeat⟩
    exact ⟨u, hu, fun r hr => hbeat r (by simpa using hr)⟩
  · rintro ⟨u, hu, hbeat⟩
    exact (not_familyExtremalOn_iff_exists_strict_counterexample
      C δ (R : Set (WordStack A (Fin 2) ι)) G).mpr
      ⟨u, hu, fun r hr => hbeat r (by simpa using hr)⟩

open Classical in
/-- Scanner form for a failed guarded split with an explicit finite catalogue.  Once every
catalogue member is budgeted, a full open-core counterexample is either outside the guard or is a
guarded stack beating every catalogue member. -/
theorem outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded_finset
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (R : Finset (WordStack A (Fin 2) ι)) (G : WordStack A (Fin 2) ι → Prop)
    (hR : ∀ r : WordStack A (Fin 2) ι, r ∈ R → incCount (F := F) C δ r ≤ B)
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    (∃ u : WordStack A (Fin 2) ι, ¬ G u ∧ B < incCount (F := F) C δ u) ∨
      ∃ u : WordStack A (Fin 2) ι, G u ∧
        ∀ r : WordStack A (Fin 2) ι, r ∈ R →
          incCount (F := F) C δ r < incCount (F := F) C δ u := by
  rcases outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
      C δ B (R : Set (WordStack A (Fin 2) ι)) G
      ((monomialIncidenceBounded_finset_coe_iff C δ B R).mpr hR) hnot with
    houtside | hinside
  · exact Or.inl houtside
  · rcases hinside with ⟨u, hu, hbeat⟩
    exact Or.inr ⟨u, hu, fun r hr => hbeat r (by simpa using hr)⟩

section SourceAudit

#print axioms StackIncidenceBoundedOn
#print axioms FamilyExtremalOn
#print axioms familyExtremalOn_true_iff_sumsetExtremal
#print axioms stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded
#print axioms stackIncidenceBoundedOn_of_familyExtremalOn
#print axioms worstCaseIncidenceBounded_of_split_familyExtremalOn
#print axioms mcaDeltaStar_pin_of_split_familyExtremalOn
#print axioms not_stackIncidenceBoundedOn_iff_exists_counterexample
#print axioms not_familyExtremalOn_iff_exists_strict_counterexample
#print axioms not_worstCaseIncidenceBounded_iff_exists_counterexample
#print axioms exists_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
#print axioms exists_outside_counterexample_of_not_worstCaseIncidenceBounded
#print axioms outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
#print axioms not_familyExtremalOn_of_strict_counterexample
#print axioms not_sumsetExtremal_of_strict_counterexample
#print axioms not_worstCaseIncidenceBounded_of_counterexample
#print axioms monomialIncidenceBounded_finset_coe_iff
#print axioms familyExtremalOn_finset_coe_iff
#print axioms stackIncidenceBoundedOn_of_finsetFamilyExtremalOn
#print axioms worstCaseIncidenceBounded_of_split_finsetFamilyExtremalOn
#print axioms mcaDeltaStar_pin_of_split_finsetFamilyExtremalOn
#print axioms not_finsetFamilyExtremalOn_iff_exists_strict_counterexample
#print axioms outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded_finset

end SourceAudit

end ProximityGap.SumsetExtremality
