/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Stack-orbit representative reduction for the MCA floor

`PeriodOrbitQuotientReduction` proves the frequency-side quotient fact: because Gauss periods are
constant on multiplicative subgroup orbits, one may check one representative per nonzero frequency
orbit.  The floor-localization lane needs an analogous statement on the *stack* side, since the
delta-star lower pin consumes `WorstCaseIncidenceBounded`, a bound over every `WordStack`.

This file records the exact representative-cover API.

* A relation `Rel` on stacks is useful only after proving `StackCountInvariantRel`: the actual
  bad-scalar count is invariant along `Rel`.
* A finite representative set `R` is useful only after proving `StackRelRepresentativeCover`: every
  stack is related to some representative in `R`.
* Under those two hypotheses, bounding the representatives is equivalent to bounding all stacks.

There is also a slightly weaker direct form, `StackDominatingRepresentativeCover`, where each stack's
count is bounded above by the count of some representative.  This is the honest landing site for a
"all worst-case stacks reduce to binder/floor stacks" theorem.  Without such a cover, a bound on a
selected floor stack remains obstruction removal, not a prize proof.

The last section supplies a real invariance theorem for field-valued linear codes: the combined
affine reparametrization / code-automorphism action already used by the A5 orbit probes preserves
`StackBadCount` exactly, not merely at the probability level.  This proves one side of a future
stack-orbit quotient theorem; the still-open part is a representative cover or domination theorem.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Cardinality of a filtered finite type is invariant under precomposition by an equivalence. -/
theorem card_filter_comp_equiv {α : Type} [Fintype α] [DecidableEq α]
    (P : α -> Prop) [DecidablePred P] (e : α ≃ α) :
    (Finset.univ.filter (fun x => P (e x))).card =
      (Finset.univ.filter P).card := by
  classical
  refine Finset.card_bij' (fun x _ => e x) (fun y _ => e.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro y hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hy).2⟩
  · intro x _hx
    simp
  · intro y _hy
    simp

/-- The actual bad-scalar count appearing in `WorstCaseIncidenceBounded`.  This file keeps a local
copy of the definition so it can be checked independently by `pg-iterate.sh`. -/
noncomputable def StackBadCount (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun γ : K => mcaEvent (F := K) C δ (u 0) (u 1) γ)).card

/-- A one-stack incidence budget for the actual MCA bad-scalar count. -/
def StackBounded (K : Type) [Field K] [Fintype K] [DecidableEq K]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module K A]
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (B : ℕ) : Prop :=
  StackBadCount K C δ u ≤ B

/-- A relation preserves the actual MCA bad-scalar count on stacks. -/
def StackCountInvariantRel (C : Set (ι -> A)) (δ : ℝ≥0)
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) : Prop :=
  ∀ {u v : WordStack A (Fin 2) ι}, Rel u v →
    StackBadCount F C δ u = StackBadCount F C δ v

/-- `R` contains a representative for every stack modulo `Rel`. -/
def StackRelRepresentativeCover
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, ∃ r ∈ R, Rel u r

/-- Failure of a literal representative cover is exactly an uncovered stack. -/
theorem not_stackRelRepresentativeCover_iff_exists_uncovered
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) :
    (¬ StackRelRepresentativeCover R Rel) ↔
      ∃ u : WordStack A (Fin 2) ι, ∀ r, r ∈ R -> ¬ Rel u r := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    by_contra hno
    have huncovered : ∀ r, r ∈ R -> ¬ Rel u r := by
      intro r hr hrel
      exact hno ⟨r, hr, hrel⟩
    exact hnone ⟨u, huncovered⟩
  · rintro ⟨u, huncovered⟩ hcover
    rcases hcover u with ⟨r, hr, hrel⟩
    exact huncovered r hr hrel

/-- Representative stacks are within the requested incidence budget. -/
def RepresentativeStacksBounded (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) : Prop :=
  ∀ r ∈ R, StackBounded F C δ r B

/-- Failure of representative boundedness is exactly an above-budget representative. -/
theorem not_representativeStacksBounded_iff_exists_representative_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ RepresentativeStacksBounded (F := F) (A := A) C δ R B) ↔
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro r hr
    exact le_of_not_gt (fun hgt => hnone ⟨r, hr, hgt⟩)
  · rintro ⟨r, hr, hgt⟩ hbounded
    exact (not_lt_of_ge (hbounded r hr)) hgt

/-- Failure of the local representative scanner certificate is exactly an uncovered stack or an
above-budget representative.  Invariance is a separate proof obligation; this theorem isolates the
two finite-search failures for the cover/budget half of the quotient route. -/
theorem not_stackRelRepresentativeCover_and_representativeStacksBounded_iff_exists_uncovered_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ)
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) :
    (¬ (StackRelRepresentativeCover R Rel ∧
      RepresentativeStacksBounded (F := F) (A := A) C δ R B)) ↔
      (∃ u : WordStack A (Fin 2) ι, ∀ r, r ∈ R -> ¬ Rel u r) ∨
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  rw [not_and_or]
  constructor
  · rintro (hcover | hbounded)
    · exact Or.inl ((not_stackRelRepresentativeCover_iff_exists_uncovered R Rel).mp hcover)
    · exact Or.inr
        ((not_representativeStacksBounded_iff_exists_representative_budget_lt C δ R B).mp
          hbounded)
  · rintro (huncovered | hbudget)
    · exact Or.inl ((not_stackRelRepresentativeCover_iff_exists_uncovered R Rel).mpr huncovered)
    · exact Or.inr
        ((not_representativeStacksBounded_iff_exists_representative_budget_lt C δ R B).mpr
          hbudget)

/-- Direct domination by a finite representative set.  This is weaker than exact equivalence and is
often the right target for sparse-dominance claims. -/
def StackDominatingRepresentativeCover (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ∃ r ∈ R, StackBadCount F C δ u ≤ StackBadCount F C δ r

/-- Failure of a dominating representative cover is exactly a stack that beats every proposed
representative. -/
theorem not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) :
    (¬ StackDominatingRepresentativeCover (F := F) (A := A) C δ R) ↔
      ∃ u : WordStack A (Fin 2) ι,
        ∀ r, r ∈ R -> StackBadCount F C δ r < StackBadCount F C δ u := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u
    by_contra hno
    have hbeats : ∀ r, r ∈ R -> StackBadCount F C δ r < StackBadCount F C δ u := by
      intro r hr
      exact lt_of_not_ge (fun hle => hno ⟨r, hr, hle⟩)
    exact hnone ⟨u, hbeats⟩
  · rintro ⟨u, hbeats⟩ hcover
    rcases hcover u with ⟨r, hr, hur⟩
    exact (not_lt_of_ge hur) (hbeats r hr)

/-- Failure of the direct sparse-domination scanner certificate is exactly a stack beating every
representative or an above-budget representative. -/
theorem not_stackDominatingRepresentativeCover_and_representativeStacksBounded_iff_exists_beater_or_budget_lt
    (C : Set (ι -> A)) (δ : ℝ≥0)
    (R : Finset (WordStack A (Fin 2) ι)) (B : ℕ) :
    (¬ (StackDominatingRepresentativeCover (F := F) (A := A) C δ R ∧
      RepresentativeStacksBounded (F := F) (A := A) C δ R B)) ↔
      (∃ u : WordStack A (Fin 2) ι,
        ∀ r, r ∈ R -> StackBadCount F C δ r < StackBadCount F C δ u) ∨
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  rw [not_and_or]
  constructor
  · rintro (hcover | hbounded)
    · exact Or.inl
        ((not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all C δ R).mp hcover)
    · exact Or.inr
        ((not_representativeStacksBounded_iff_exists_representative_budget_lt C δ R B).mp
          hbounded)
  · rintro (hbeater | hbudget)
    · exact Or.inl
        ((not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all C δ R).mpr hbeater)
    · exact Or.inr
        ((not_representativeStacksBounded_iff_exists_representative_budget_lt C δ R B).mpr
          hbudget)

/-- Invariance plus a representative cover gives a dominating representative cover. -/
theorem dominatingCover_of_invariantRel_cover
    (C : Set (ι -> A)) (δ : ℝ≥0)
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hinv : StackCountInvariantRel (F := F) (A := A) C δ Rel)
    (hcover : StackRelRepresentativeCover R Rel) :
    StackDominatingRepresentativeCover (F := F) (A := A) C δ R := by
  intro u
  rcases hcover u with ⟨r, hr, hur⟩
  exact ⟨r, hr, le_of_eq (hinv hur)⟩

/-- Bounding a dominating representative set proves the actual open-core incidence hypothesis. -/
theorem worstCaseIncidenceBounded_of_dominatingRepresentativeCover
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackDominatingRepresentativeCover (F := F) (A := A) C δ R)
    (hR : RepresentativeStacksBounded (F := F) (A := A) C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B := by
  intro u
  rcases hcover u with ⟨r, hr, hur⟩
  exact le_trans hur (hR r hr)

/-- Invariance and representative coverage are enough to reduce the full worst-case incidence
hypothesis to representative bounds. -/
theorem worstCaseIncidenceBounded_of_representativeStacksBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hinv : StackCountInvariantRel (F := F) (A := A) C δ Rel)
    (hcover : StackRelRepresentativeCover R Rel)
    (hR : RepresentativeStacksBounded (F := F) (A := A) C δ R B) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B :=
  worstCaseIncidenceBounded_of_dominatingRepresentativeCover C δ
    (dominatingCover_of_invariantRel_cover C δ hinv hcover) hR

/-- A full worst-case incidence bound automatically bounds every chosen representative. -/
theorem representativeStacksBounded_of_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {B : ℕ}
    {R : Finset (WordStack A (Fin 2) ι)}
    (hI : ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B) :
    RepresentativeStacksBounded (F := F) (A := A) C δ R B := by
  intro r _hr
  exact hI r

/-- Under a dominating representative cover, the full open-core incidence hypothesis is equivalent
to checking the representative set. -/
theorem worstCaseIncidenceBounded_iff_representativeStacksBounded_of_dominatingCover
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackDominatingRepresentativeCover (F := F) (A := A) C δ R) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ RepresentativeStacksBounded (F := F) (A := A) C δ R B :=
  ⟨representativeStacksBounded_of_worstCaseIncidenceBounded C δ,
    worstCaseIncidenceBounded_of_dominatingRepresentativeCover C δ hcover⟩

/-- Under a dominating representative cover, failure of the full incidence bound is exactly an
above-budget representative. -/
theorem not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_dominatingCover
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackDominatingRepresentativeCover (F := F) (A := A) C δ R) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r := by
  rw [worstCaseIncidenceBounded_iff_representativeStacksBounded_of_dominatingCover
    C δ B hcover]
  exact not_representativeStacksBounded_iff_exists_representative_budget_lt C δ R B

/-- Delta-star consumer for a direct dominating representative cover.  This is the sparse-dominance
route without packaging the cover as an invariant relation. -/
theorem deltaStar_pin_of_dominatingRepresentativeCover
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackDominatingRepresentativeCover (F := F) (A := A) C δ R)
    (hR : RepresentativeStacksBounded (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_dominatingRepresentativeCover C δ hcover hR)
    hbudget

/-- Under an invariant representative cover, failure of the full incidence bound is exactly an
above-budget representative. -/
theorem not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_invariantRel_cover
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hinv : StackCountInvariantRel (F := F) (A := A) C δ Rel)
    (hcover : StackRelRepresentativeCover R Rel) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B)
      ↔ ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ B < StackBadCount F C δ r :=
  not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_dominatingCover
    C δ B (dominatingCover_of_invariantRel_cover C δ hinv hcover)

/-- Under an invariant representative cover, checking all representatives is equivalent to checking
all stacks.  This is the stack-side analogue of the frequency-side quotient collapse. -/
theorem worstCaseIncidenceBounded_iff_representativeStacksBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hinv : StackCountInvariantRel (F := F) (A := A) C δ Rel)
    (hcover : StackRelRepresentativeCover R Rel) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ B
      ↔ RepresentativeStacksBounded (F := F) (A := A) C δ R B :=
  ⟨representativeStacksBounded_of_worstCaseIncidenceBounded C δ,
    worstCaseIncidenceBounded_of_representativeStacksBounded C δ hinv hcover⟩

/-- Delta-star consumer for a finite representative cover.  A floor/binder proof can use this only
after supplying the count-invariance and cover theorems for its proposed stack equivalence. -/
theorem deltaStar_pin_of_representativeStacksBounded
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hinv : StackCountInvariantRel (F := F) (A := A) C δ Rel)
    (hcover : StackRelRepresentativeCover R Rel)
    (hR : RepresentativeStacksBounded (F := F) (A := A) C δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
    (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_representativeStacksBounded
      C δ hinv hcover hR)
    hbudget

/-! ## Concrete count invariance for affine stack reparametrizations -/

open ProximityGap.MCAEquivariance

/-- Direction-row scaling preserves the actual bad-scalar count; the scalar set is transported by
the bijection `γ ↦ γ * s`. -/
theorem stackBadCount_smul_right
    (C : Submodule F (ι -> F)) (δ : ℝ≥0)
    (u₀ u₁ : ι -> F) {s : F} (hs : s ≠ 0) :
    StackBadCount F (C : Set (ι -> F)) δ ![u₀, s • u₁]
      = StackBadCount F (C : Set (ι -> F)) δ ![u₀, u₁] := by
  classical
  unfold StackBadCount
  have hset :
      (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι -> F)) δ
            ((![u₀, s • u₁] : WordStack F (Fin 2) ι) 0)
            ((![u₀, s • u₁] : WordStack F (Fin 2) ι) 1) γ))
        =
      (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι -> F)) δ u₀ u₁ (γ * s))) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact mcaEvent_smul_right C hs γ
  rw [hset]
  exact card_filter_comp_equiv
    (fun γ : F => mcaEvent (F := F) (C : Set (ι -> F)) δ u₀ u₁ γ)
    (mulRightEquiv s hs)

/-- Shearing the base row by the direction row preserves the actual bad-scalar count; the scalar
set is transported by `γ ↦ β + γ`. -/
theorem stackBadCount_shift
    (C : Submodule F (ι -> F)) (δ : ℝ≥0)
    (u₀ u₁ : ι -> F) (β : F) :
    StackBadCount F (C : Set (ι -> F)) δ ![u₀ + β • u₁, u₁]
      = StackBadCount F (C : Set (ι -> F)) δ ![u₀, u₁] := by
  classical
  unfold StackBadCount
  have hset :
      (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι -> F)) δ
            ((![u₀ + β • u₁, u₁] : WordStack F (Fin 2) ι) 0)
            ((![u₀ + β • u₁, u₁] : WordStack F (Fin 2) ι) 1) γ))
        =
      (Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι -> F)) δ u₀ u₁ (β + γ))) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact mcaEvent_shift C β γ
  rw [hset]
  exact card_filter_comp_equiv
    (fun γ : F => mcaEvent (F := F) (C : Set (ι -> F)) δ u₀ u₁ γ)
    (addLeftEquiv β)

/-- Scaling both rows by a nonzero scalar preserves the actual bad-scalar count. -/
theorem stackBadCount_smul_both
    (C : Submodule F (ι -> F)) (δ : ℝ≥0)
    (u₀ u₁ : ι -> F) {s : F} (hs : s ≠ 0) :
    StackBadCount F (C : Set (ι -> F)) δ ![s • u₀, s • u₁]
      = StackBadCount F (C : Set (ι -> F)) δ ![u₀, u₁] := by
  classical
  unfold StackBadCount
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact mcaEvent_smul_both C hs γ

/-- Code-preserving coordinate permutations preserve the actual bad-scalar count. -/
theorem stackBadCount_comp_perm
    (C : Submodule F (ι -> F)) (δ : ℝ≥0)
    (u₀ u₁ : ι -> F) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) :
    StackBadCount F (C : Set (ι -> F)) δ ![u₀ ∘ ⇑σ, u₁ ∘ ⇑σ]
      = StackBadCount F (C : Set (ι -> F)) δ ![u₀, u₁] := by
  classical
  unfold StackBadCount
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact mcaEvent_comp_perm_iff C σ hσ hσ' (γ := γ)

/-- The combined affine-rotation stack transform used by the A5 orbit probes. -/
def affineRotateStack (σ : Equiv.Perm ι) (a b c : F)
    (u : WordStack F (Fin 2) ι) : WordStack F (Fin 2) ι :=
  ![a • (u 0 ∘ ⇑σ) + b • (u 1 ∘ ⇑σ), c • (u 1 ∘ ⇑σ)]

/-- The actual bad-scalar count is invariant under the full affine-rotation action, provided the
coordinate permutation preserves the code and the two scaling parameters are nonzero. -/
theorem stackBadCount_affine_rotate
    (C : Submodule F (ι -> F)) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {a c : F} (ha : a ≠ 0) (hc : c ≠ 0) (b : F) :
    StackBadCount F (C : Set (ι -> F)) δ (affineRotateStack σ a b c u)
      = StackBadCount F (C : Set (ι -> F)) δ u := by
  classical
  set r₀ : ι -> F := u 0 ∘ ⇑σ with hr₀
  set r₁ : ι -> F := u 1 ∘ ⇑σ with hr₁
  have hca : (c * a⁻¹) ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hrow1 : c • r₁ = (c * a⁻¹) • (a • r₁) := by
    rw [smul_smul]
    congr 1
    field_simp
  have hrow0 : a • r₀ + b • r₁ = a • r₀ + (b * a⁻¹) • (a • r₁) := by
    congr 1
    rw [smul_smul]
    congr 1
    field_simp
  calc
    StackBadCount F (C : Set (ι -> F)) δ (affineRotateStack σ a b c u)
        = StackBadCount F (C : Set (ι -> F)) δ ![a • r₀ + b • r₁, c • r₁] := by
          rw [hr₀, hr₁]
          rfl
    _ = StackBadCount F (C : Set (ι -> F)) δ
          ![a • r₀ + (b * a⁻¹) • (a • r₁), (c * a⁻¹) • (a • r₁)] := by
          rw [← hrow0, ← hrow1]
    _ = StackBadCount F (C : Set (ι -> F)) δ
          ![a • r₀ + (b * a⁻¹) • (a • r₁), a • r₁] :=
          stackBadCount_smul_right C δ
            (a • r₀ + (b * a⁻¹) • (a • r₁)) (a • r₁) hca
    _ = StackBadCount F (C : Set (ι -> F)) δ ![a • r₀, a • r₁] :=
          stackBadCount_shift C δ (a • r₀) (a • r₁) (b * a⁻¹)
    _ = StackBadCount F (C : Set (ι -> F)) δ ![r₀, r₁] :=
          stackBadCount_smul_both C δ r₀ r₁ ha
    _ = StackBadCount F (C : Set (ι -> F)) δ ![u 0, u 1] := by
          rw [hr₀, hr₁]
          exact stackBadCount_comp_perm C δ (u 0) (u 1) σ hσ hσ'
    _ = StackBadCount F (C : Set (ι -> F)) δ u := by
          rfl

end ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.card_filter_comp_equiv
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_stackRelRepresentativeCover_iff_exists_uncovered
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_representativeStacksBounded_iff_exists_representative_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_stackRelRepresentativeCover_and_representativeStacksBounded_iff_exists_uncovered_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_stackDominatingRepresentativeCover_and_representativeStacksBounded_iff_exists_beater_or_budget_lt
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.dominatingCover_of_invariantRel_cover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.worstCaseIncidenceBounded_of_dominatingRepresentativeCover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.worstCaseIncidenceBounded_of_representativeStacksBounded
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.representativeStacksBounded_of_worstCaseIncidenceBounded
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.worstCaseIncidenceBounded_iff_representativeStacksBounded_of_dominatingCover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_dominatingCover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.deltaStar_pin_of_dominatingRepresentativeCover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_invariantRel_cover
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.worstCaseIncidenceBounded_iff_representativeStacksBounded
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.deltaStar_pin_of_representativeStacksBounded
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.stackBadCount_smul_right
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.stackBadCount_shift
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.stackBadCount_smul_both
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.stackBadCount_comp_perm
#print axioms ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction.stackBadCount_affine_rotate
