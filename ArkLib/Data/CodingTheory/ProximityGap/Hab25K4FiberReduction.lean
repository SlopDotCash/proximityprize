/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25FiberPigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Hab25K4Seam

/-!
# The K4 ⟸ per-component reduction: the last wiring of the Steps 5–7 surface

`bad_card_le_numeric` consumes K4 in the *factor-cell* form (a decode family whose
matching factors divide one specialized irreducible factor `R|_{Z:=γ}`). The Steps 5–7
mathematics (BCIKS20 Claims 5.8/5.9) lives one reduction deeper: on a **single
irreducible component `H(Y,Z)` of the `x₀`-fiber curve** `R(x₀,·,·)`, with the planar
points `(γ, P γ(x₀))` on it. This file closes that gap — after it, the K4 obligation *is*
the literal per-component capture statement, with no plumbing in between:

* `fiberAt_coeff_natDegree_le` — the fiber inherits the interpolant's Z-degree budget
  (evaluation at the constant `x₀` cannot raise Z-degrees);
* `card_fiber_specialization_collapse_le` — hence the fiber-degenerate scalars
  (`R(x₀,·,·)|_{Z:=γ} = 0`) number at most the budget;
* **`cell_card_le_of_component_K4`** — the reduction: a per-component capture bound `T'`
  (any sub-cell whose points sit on one irreducible component `H` has `≤ T'` members)
  bounds the whole factor cell by `(Ω+2)·max(T', T₀)`, via the proven
  `exists_fiber_component_pigeonhole`, where `T₀` is the fiber-degenerate budget and
  `Ω` the component count.

After this file the **wiring of #302 is complete**: every surviving obligation is a
self-contained mathematical statement (the per-component capture = BCIKS20 C5.8 Hensel
branch forcing + C5.9 Z-linearity, the #138/#139 kernel; its `x₀`-good-point supply is
the in-tree S5 discriminant lane).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- Evaluating the mid variable at a constant cannot raise Z-degrees: the fiber's
`F[Z]`-coefficients obey the interpolant's per-coefficient budget. -/
lemma fiberAt_coeff_natDegree_le {R : (F₀[X])[X][Y]} {B : ℕ}
    (hB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ B) (x₀ : F₀) (j : ℕ) :
    ((fiberAt x₀ R).coeff j).natDegree ≤ B := by
  have hcoeff : (fiberAt x₀ R).coeff j = (R.coeff j).eval (Polynomial.C x₀) := by
    rw [fiberAt, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coe_evalRingHom]
  rw [hcoeff, Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : ((Polynomial.C x₀ : F₀[X]) ^ a).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero]
  rw [h1, add_zero]
  exact hB j a

/-- **The fiber-degenerate scalars obey the Z-degree budget**: if the fiber is nonzero
and its coefficients have `natDegree ≤ B`, at most `B` scalars `γ` collapse it. -/
lemma card_fiber_specialization_collapse_le [Fintype F₀] {G : F₀[X][Y]}
    (hG : G ≠ 0) {B : ℕ} (hB : ∀ j : ℕ, (G.coeff j).natDegree ≤ B) :
    (Finset.univ.filter (fun γ : F₀ =>
      G.map (Polynomial.evalRingHom γ) = 0)).card ≤ B := by
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hG
  have hj' : G.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) (hB j)
  intro γ hγ
  rw [Finset.mem_val, Finset.mem_filter] at hγ
  have h1 : (G.map (Polynomial.evalRingHom γ)).coeff j = 0 := by
    rw [hγ.2]
    simp
  rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom] at h1
  exact (Polynomial.mem_roots hj').mpr h1

variable [Fintype F₀] [DecidableEq F₀]

/-- **The K4 ⟸ per-component reduction (the last wiring of the Steps 5–7 surface).**
Fix a good fiber point `x₀` (fiber nonzero). Given
* `T₀` — a bound on the fiber-degenerate scalars (supplied by the Z-degree budget via
  `card_fiber_specialization_collapse_le`), and
* `T'` — the **per-component capture bound** (any sub-cell whose planar points lie on
  one irreducible component `H` of the fiber curve has `≤ T'` members — the literal
  BCIKS20 C5.8/C5.9 statement),

every factor cell `E` (decode family + matching-factor divisibility into `R`) has
`|E| ≤ (Ω+2)·max(T', T₀)`, where `Ω` is the fiber's component count. -/
theorem cell_card_le_of_component_K4 {n k L : ℕ} [NeZero n] {domain : Fin n ↪ F₀}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) (x₀ : F₀) (E : Finset F₀) (P : F₀ → F₀[X]) (T' T₀ : ℕ)
    (hfib : fiberAt x₀ R ≠ 0)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hdvd : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hdegT : ∀ S : Finset F₀,
      (∀ γ ∈ S, (fiberAt x₀ R).map (Polynomial.evalRingHom γ) = 0) → S.card ≤ T₀)
    (hK4H : ∀ E' : Finset F₀, E' ⊆ E →
      ∀ H, H ∈ UniqueFactorizationMonoid.factors (fiberAt x₀ R) →
      (∀ γ ∈ E', ((H.map (Polynomial.evalRingHom γ)).eval ((P γ).eval x₀) = 0)) →
      E'.card ≤ T') :
    E.card ≤
      ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) * max T' T₀ := by
  classical
  obtain ⟨E', hE'sub, hE'card, hE'class⟩ :=
    exists_fiber_component_pigeonhole R x₀ E P hfib hdvd
  have hE' : E'.card ≤ max T' T₀ := by
    rcases hE'class with hdeg | ⟨H, hHmem, hH0⟩
    · exact le_trans (hdegT E' hdeg) (le_max_right _ _)
    · exact le_trans (hK4H E' hE'sub H hHmem hH0) (le_max_left _ _)
  calc E.card
      ≤ E'.card * ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) :=
        hE'card
    _ ≤ max T' T₀ * ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) :=
        Nat.mul_le_mul_right _ hE'
    _ = ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) * max T' T₀ :=
        Nat.mul_comm _ _

/-- The pair-case specialization of the reduction, in the exact `McaDecode` vocabulary
of the pair K4 seam (`Hab25K4Seam.lean`): the same statement with `McaDecode` decode
families. The decode data enters only through the divisibility surface, so this is the
`L = 2` reading of `cell_card_le_of_component_K4` with the pair structure. -/
theorem cell_card_le_of_component_K4_pair {n k : ℕ} [NeZero n] {domain : Fin n ↪ F₀}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin 2) (Fin n)}
    (R : (F₀[X])[X][Y]) (x₀ : F₀) (E : Finset F₀) (P : F₀ → F₀[X]) (T' T₀ : ℕ)
    (hfib : fiberAt x₀ R ≠ 0)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hdvd : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hdegT : ∀ S : Finset F₀,
      (∀ γ ∈ S, (fiberAt x₀ R).map (Polynomial.evalRingHom γ) = 0) → S.card ≤ T₀)
    (hK4H : ∀ E' : Finset F₀, E' ⊆ E →
      ∀ H, H ∈ UniqueFactorizationMonoid.factors (fiberAt x₀ R) →
      (∀ γ ∈ E', ((H.map (Polynomial.evalRingHom γ)).eval ((P γ).eval x₀) = 0)) →
      E'.card ≤ T') :
    E.card ≤
      ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) * max T' T₀ := by
  classical
  obtain ⟨E', hE'sub, hE'card, hE'class⟩ :=
    exists_fiber_component_pigeonhole R x₀ E P hfib hdvd
  have hE' : E'.card ≤ max T' T₀ := by
    rcases hE'class with hdeg | ⟨H, hHmem, hH0⟩
    · exact le_trans (hdegT E' hdeg) (le_max_right _ _)
    · exact le_trans (hK4H E' hE'sub H hHmem hH0) (le_max_left _ _)
  calc E.card
      ≤ E'.card * ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) :=
        hE'card
    _ ≤ max T' T₀ * ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) :=
        Nat.mul_le_mul_right _ hE'
    _ = ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) * max T' T₀ :=
        Nat.mul_comm _ _

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fiberAt_coeff_natDegree_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms card_fiber_specialization_collapse_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_component_K4
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_component_K4_pair
