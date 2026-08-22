/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

/-!
# Cardinality obstruction for stack representative covers

`_StackOrbitRepresentativeReduction` isolates the theorem needed to reduce the MCA worst-case stack
bound to a finite representative list: every stack must be related to a representative, and the
actual bad-scalar count must be invariant or dominated along that relation.

This file records the basic counting obstruction to such a reduction.  If each representative sees
at most `K` stacks in its relation fiber, then a representative set `R` can cover the whole stack
universe only when

`Fintype.card (WordStack A (Fin 2) ι) ≤ R.card * K`.

Thus a small floor/binder list is not automatically a reduction.  It must either come with a
relation whose fibers are enormous, or with a direct domination theorem that bypasses literal
coverage.

The final section specializes the obstruction to finite action/orbit relations.  If stacks are
covered by applying a finite family of transformations `G` to representatives, then every
representative fiber has size at most `|G|`; consequently a cover requires

`Fintype.card (WordStack A (Fin 2) ι) ≤ R.card * Fintype.card G`.

This is the counting test any proposed "domain dilation / affine reparametrization / code
automorphism" stack quotient must pass before it can feed the `WorstCaseIncidenceBounded` consumer.

The exact negative lemmas below turn a failed quotient into finite scanner data: either some stack is
uncovered by the proposed representatives, or some representative fiber is larger than the claimed
cap.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackRepresentativeCoverCardinality

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## Stack-universe size -/

omit [DecidableEq A] in
/-- The two-row stack universe has size `|A|^(2*|ι|)`. -/
theorem card_wordStack_fin2_eq :
    Fintype.card (WordStack A (Fin 2) ι) = (Fintype.card A) ^ (2 * Fintype.card ι) := by
  show Fintype.card (Fin 2 -> ι -> A) = (Fintype.card A) ^ (2 * Fintype.card ι)
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul]
  rw [Nat.mul_comm]

/-- `R` contains a representative for every stack modulo `Rel`.

This is kept local rather than imported from `_StackOrbitRepresentativeReduction` so this frontier
file remains independently checkable by `scripts/pg-iterate.sh`; the definition is intentionally
the same predicate. -/
def StackRelRepresentativeCover
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, ∃ r ∈ R, Rel u r

/-- Failure of a literal representative cover is exactly an uncovered stack. -/
theorem not_stackRelRepresentativeCover_iff_exists_uncovered
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop) :
    (¬ StackRelRepresentativeCover (A := A) R Rel) ↔
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

/-- The fiber of stacks related to the representative `r`. -/
noncomputable def stackRelFiber
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop)
    (r : WordStack A (Fin 2) ι) : Finset (WordStack A (Fin 2) ι) := by
  classical
  exact Finset.univ.filter (fun u => Rel u r)

omit [DecidableEq A] in
@[simp] theorem mem_stackRelFiber
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {u r : WordStack A (Fin 2) ι} :
    u ∈ stackRelFiber Rel r ↔ Rel u r := by
  classical
  simp [stackRelFiber]

/-- Failure of a uniform relation-fiber cap is exactly one representative with a larger fiber. -/
theorem not_stackRelFiberCap_iff_exists_large_fiber
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop)
    (K : ℕ) :
    (¬ ∀ r ∈ R, (stackRelFiber Rel r).card ≤ K) ↔
      ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ K < (stackRelFiber Rel r).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro r hr
    exact Nat.le_of_not_gt (fun hgt => hnone ⟨r, hr, hgt⟩)
  · rintro ⟨r, hr, hgt⟩ hcap
    exact (not_lt_of_ge (hcap r hr)) hgt

/-- A representative cover with uniformly bounded relation fibers can cover only a universe of size
at most `R.card * K`. -/
theorem stackUniverse_card_le_reps_mul_fiberCap
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {K : ℕ}
    (hcover : StackRelRepresentativeCover (A := A) R Rel)
    (hcap : ∀ r ∈ R, (stackRelFiber Rel r).card ≤ K) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ R.card * K := by
  classical
  have hsub : (Finset.univ : Finset (WordStack A (Fin 2) ι)) ⊆
      R.biUnion (fun r => stackRelFiber Rel r) := by
    intro u _hu
    rcases hcover u with ⟨r, hr, hur⟩
    exact Finset.mem_biUnion.mpr ⟨r, hr, by simpa using hur⟩
  calc
    Fintype.card (WordStack A (Fin 2) ι)
        = (Finset.univ : Finset (WordStack A (Fin 2) ι)).card := by
          simp
    _ ≤ (R.biUnion (fun r => stackRelFiber Rel r)).card :=
        Finset.card_le_card hsub
    _ ≤ R.card * K :=
        Finset.card_biUnion_le_card_mul R (fun r => stackRelFiber Rel r) K hcap

/-- Exact scanner form for the cover-plus-fiber-cap certificate: failure is an uncovered stack or a
representative fiber above the claimed cap. -/
theorem not_stackRelRepresentativeCover_and_fiberCap_iff_exists_uncovered_or_large_fiber
    (R : Finset (WordStack A (Fin 2) ι))
    (Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop)
    (K : ℕ) :
    (¬ (StackRelRepresentativeCover (A := A) R Rel ∧
      ∀ r ∈ R, (stackRelFiber Rel r).card ≤ K)) ↔
      (∃ u : WordStack A (Fin 2) ι, ∀ r, r ∈ R -> ¬ Rel u r) ∨
        ∃ r : WordStack A (Fin 2) ι, r ∈ R ∧ K < (stackRelFiber Rel r).card := by
  rw [not_and_or]
  constructor
  · rintro (hcover | hcap)
    · exact Or.inl ((not_stackRelRepresentativeCover_iff_exists_uncovered R Rel).mp hcover)
    · exact Or.inr ((not_stackRelFiberCap_iff_exists_large_fiber R Rel K).mp hcap)
  · rintro (huncovered | hlarge)
    · exact Or.inl ((not_stackRelRepresentativeCover_iff_exists_uncovered R Rel).mpr huncovered)
    · exact Or.inr ((not_stackRelFiberCap_iff_exists_large_fiber R Rel K).mpr hlarge)

/-- If `R.card * K` is smaller than the stack universe and every representative fiber has size at
most `K`, then `R` is not a representative cover. -/
theorem no_stackRepresentativeCover_of_fiberCap
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {K : ℕ}
    (hcap : ∀ r ∈ R, (stackRelFiber Rel r).card ≤ K)
    (hsmall : R.card * K < Fintype.card (WordStack A (Fin 2) ι)) :
    ¬ StackRelRepresentativeCover (A := A) R Rel := by
  intro hcover
  exact (not_lt_of_ge
    (stackUniverse_card_le_reps_mul_fiberCap
      (A := A) (R := R) (Rel := Rel) (K := K) hcover hcap)) hsmall

/-- Conversely, any representative cover whose representative list is too small must have at least
one relation fiber larger than `K`. -/
theorem stackRepresentativeCover_forces_large_fiber
    {R : Finset (WordStack A (Fin 2) ι)}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    {K : ℕ}
    (hcover : StackRelRepresentativeCover (A := A) R Rel)
    (hsmall : R.card * K < Fintype.card (WordStack A (Fin 2) ι)) :
    ∃ r ∈ R, K < (stackRelFiber Rel r).card := by
  by_contra hno
  have hcap : ∀ r ∈ R, (stackRelFiber Rel r).card ≤ K := by
    intro r hr
    exact Nat.le_of_not_gt (fun hgt => hno ⟨r, hr, hgt⟩)
  exact (not_lt_of_ge
    (stackUniverse_card_le_reps_mul_fiberCap
      (A := A) (R := R) (Rel := Rel) (K := K) hcover hcap)) hsmall

/-- A singleton representative cover forces the one fiber to contain the whole stack universe. -/
theorem stackSingletonCover_card_le_fiber
    {r₀ : WordStack A (Fin 2) ι}
    {Rel : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop}
    (hcover : StackRelRepresentativeCover (A := A) ({r₀} : Finset (WordStack A (Fin 2) ι)) Rel) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ (stackRelFiber Rel r₀).card := by
  classical
  have hcap : ∀ r ∈ ({r₀} : Finset (WordStack A (Fin 2) ι)),
      (stackRelFiber Rel r).card ≤ (stackRelFiber Rel r₀).card := by
    intro r hr
    have hreq : r = r₀ := by simpa using hr
    rw [hreq]
  simpa using
    (stackUniverse_card_le_reps_mul_fiberCap
      (A := A) (R := ({r₀} : Finset (WordStack A (Fin 2) ι)))
      (Rel := Rel) (K := (stackRelFiber Rel r₀).card) hcover hcap)

/-! ## Finite action/orbit specialization -/

/-- Relation generated by a finite family of stack transformations.  The parameter type `G` may be
a genuine group, a finite monoid, or just a finite label set of transformations; only its cardinality
matters for the covering obstruction. -/
def StackActionRel {G : Type}
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    (u r : WordStack A (Fin 2) ι) : Prop :=
  ∃ g : G, act g r = u

/-- For an action-generated relation, cover failure is exactly a stack outside every transformed
representative orbit. -/
theorem not_stackActionRepresentativeCover_iff_exists_uncovered {G : Type}
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    (R : Finset (WordStack A (Fin 2) ι)) :
    (¬ StackRelRepresentativeCover (A := A) R (StackActionRel (A := A) act)) ↔
      ∃ u : WordStack A (Fin 2) ι, ∀ r, r ∈ R -> ∀ g : G, act g r ≠ u := by
  rw [not_stackRelRepresentativeCover_iff_exists_uncovered]
  constructor
  · rintro ⟨u, huncovered⟩
    exact ⟨u, fun r hr g hgu => huncovered r hr ⟨g, hgu⟩⟩
  · rintro ⟨u, huncovered⟩
    refine ⟨u, ?_⟩
    intro r hr hrel
    rcases hrel with ⟨g, hgu⟩
    exact huncovered r hr g hgu

/-- Each orbit fiber generated by a finite family of transformations has size at most the number of
transformation labels.  No freeness/injectivity is required; collisions only make the orbit smaller. -/
theorem stackActionRel_fiber_card_le_card {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    (r : WordStack A (Fin 2) ι) :
    (stackRelFiber (StackActionRel (A := A) act) r).card ≤ Fintype.card G := by
  classical
  have hsub : stackRelFiber (StackActionRel (A := A) act) r ⊆
      (Finset.univ.image (fun g : G => act g r)) := by
    intro u hu
    rcases (mem_stackRelFiber.mp hu) with ⟨g, hgu⟩
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, hgu⟩
  calc
    (stackRelFiber (StackActionRel (A := A) act) r).card
        ≤ (Finset.univ.image (fun g : G => act g r)).card :=
          Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset G).card := Finset.card_image_le
    _ = Fintype.card G := by simp

/-- A finite action-generated representative cover can cover the stack universe only if the number
of representatives times the number of transformations is at least the number of stacks. -/
theorem stackUniverse_card_le_reps_mul_actionCard {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackRelRepresentativeCover (A := A) R (StackActionRel (A := A) act)) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ R.card * Fintype.card G :=
  stackUniverse_card_le_reps_mul_fiberCap
    (A := A) (R := R) (Rel := StackActionRel (A := A) act)
    (K := Fintype.card G) hcover
    (fun r _hr => stackActionRel_fiber_card_le_card (A := A) act r)

/-- If the representative list times the finite transformation budget is too small, then those
transformations cannot cover all stacks. -/
theorem no_stackActionRepresentativeCover_of_card_lt {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hsmall : R.card * Fintype.card G < Fintype.card (WordStack A (Fin 2) ι)) :
    ¬ StackRelRepresentativeCover (A := A) R (StackActionRel (A := A) act) := by
  intro hcover
  exact (not_lt_of_ge
    (stackUniverse_card_le_reps_mul_actionCard
      (A := A) (G := G) act (R := R) hcover)) hsmall

/-- A singleton orbit representative can cover all stacks only when the finite transformation
family is at least as large as the whole stack universe. -/
theorem stackSingletonActionCover_card_le_actionCard {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    {r₀ : WordStack A (Fin 2) ι}
    (hcover : StackRelRepresentativeCover (A := A)
      ({r₀} : Finset (WordStack A (Fin 2) ι)) (StackActionRel (A := A) act)) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ Fintype.card G := by
  simpa using
    (stackUniverse_card_le_reps_mul_actionCard
      (A := A) (G := G) act
      (R := ({r₀} : Finset (WordStack A (Fin 2) ι))) hcover)

/-- Concrete exponential form of the finite-action cover obstruction. -/
theorem cardA_pow_le_reps_mul_actionCard_of_actionCover {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hcover : StackRelRepresentativeCover (A := A) R (StackActionRel (A := A) act)) :
    (Fintype.card A) ^ (2 * Fintype.card ι) ≤ R.card * Fintype.card G := by
  rw [← card_wordStack_fin2_eq (A := A) (ι := ι)]
  exact stackUniverse_card_le_reps_mul_actionCard (A := A) (G := G) act (R := R) hcover

/-- If `#R * #G` is below the explicit stack-universe size `|A|^(2|ι|)`, no finite-action
representative cover exists. -/
theorem no_stackActionRepresentativeCover_of_card_lt_exp {G : Type} [Fintype G]
    (act : G -> WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι)
    {R : Finset (WordStack A (Fin 2) ι)}
    (hsmall : R.card * Fintype.card G < (Fintype.card A) ^ (2 * Fintype.card ι)) :
    ¬ StackRelRepresentativeCover (A := A) R (StackActionRel (A := A) act) := by
  rw [← card_wordStack_fin2_eq (A := A) (ι := ι)] at hsmall
  exact no_stackActionRepresentativeCover_of_card_lt
    (A := A) (G := G) act (R := R) hsmall

#print axioms card_wordStack_fin2_eq
#print axioms not_stackRelRepresentativeCover_iff_exists_uncovered
#print axioms not_stackRelFiberCap_iff_exists_large_fiber
#print axioms stackUniverse_card_le_reps_mul_fiberCap
#print axioms not_stackRelRepresentativeCover_and_fiberCap_iff_exists_uncovered_or_large_fiber
#print axioms no_stackRepresentativeCover_of_fiberCap
#print axioms stackRepresentativeCover_forces_large_fiber
#print axioms stackSingletonCover_card_le_fiber
#print axioms not_stackActionRepresentativeCover_iff_exists_uncovered
#print axioms stackActionRel_fiber_card_le_card
#print axioms stackUniverse_card_le_reps_mul_actionCard
#print axioms no_stackActionRepresentativeCover_of_card_lt
#print axioms stackSingletonActionCover_card_le_actionCard
#print axioms cardA_pow_le_reps_mul_actionCard_of_actionCover
#print axioms no_stackActionRepresentativeCover_of_card_lt_exp

end ArkLib.ProximityGap.Frontier.StackRepresentativeCoverCardinality
