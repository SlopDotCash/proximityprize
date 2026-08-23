/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25BranchPinning

/-!
# The branch dichotomy: a candidate curve divides globally or captures boundedly

The Step-6 quantitative skeleton in the interpolant's own vocabulary (no function-field
machinery): for any candidate global curve `pHat ∈ F[Z][X]`, the evaluation
`R.eval pHat ∈ F[Z][X]` either vanishes — and then `(Y − C pHat) ∣ R` **globally**, the
branch exists and feeds `pinning_of_global_branch` — or it is a nonzero polynomial whose
`Z`-degree bounds the number of scalars the candidate can capture:

* `eval_specializes` — evaluation commutes with `Z`-specialization;
* `global_branch_iff_eval_zero` — the factor theorem for the monic-linear candidate;
* `card_eval_specialization_collapse_le` — the one-level collapse count;
* **`branch_capture_dichotomy`** — global branch, or `≤ Z`-budget captured scalars;
* `capture_eq_pinned_of_section` — combined with the C5.8 rigidity
  (`decode_eq_specialized_branch`): on a separable fiber with section match, the
  captured scalars are exactly the pinned ones, so the dichotomy reads: **the decode
  family is pinned globally, or `pHat` agrees with it at `≤ Z`-budget scalars**.

The remaining mathematical content of the `deg_Y ≥ 2` capture is the production of a
candidate beating this bound (the monodromy/Λ-weight input); every counting and
rigidity step around it is now in place.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- **Evaluation commutes with `Z`-specialization**: evaluating the `Y`-variable at the
candidate and then specializing `Z` equals specializing first and evaluating at the
specialized candidate. -/
lemma eval_specializes (R : (F₀[X])[X][Y]) (pHat : (F₀[X])[X]) (γ : F₀) :
    (Polynomial.eval pHat R).map (Polynomial.evalRingHom γ) =
      Polynomial.eval (pHat.map (Polynomial.evalRingHom γ))
        (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
  have h := Polynomial.hom_eval₂ R (RingHom.id ((F₀[X])[X]))
    (Polynomial.mapRingHom (Polynomial.evalRingHom γ) :
      (F₀[X])[X] →+* F₀[X]) pHat
  rw [RingHom.comp_id] at h
  rw [show Polynomial.eval pHat R =
      Polynomial.eval₂ (RingHom.id ((F₀[X])[X])) pHat R from rfl,
    Polynomial.eval_map]
  exact h

/-- **The factor theorem for the candidate**: the monic-linear `Y − C pHat` divides `R`
iff the evaluation vanishes. -/
lemma global_branch_iff_eval_zero (R : (F₀[X])[X][Y]) (pHat : (F₀[X])[X]) :
    (Polynomial.X - Polynomial.C pHat) ∣ R ↔ Polynomial.eval pHat R = 0 := by
  rw [Polynomial.dvd_iff_isRoot]
  rfl

/-- **The one-level collapse count**: a nonzero `G ∈ F[Z][X]` with `Z`-coefficient
budget `M` collapses (`G|_{Z:=γ} = 0`) at most `M` scalars. -/
lemma card_eval_specialization_collapse_le [Fintype F₀] {G : (F₀[X])[X]}
    (hG : G ≠ 0) {M : ℕ} (hM : ∀ i : ℕ, (G.coeff i).natDegree ≤ M) :
    (Finset.univ.filter (fun γ : F₀ =>
      G.map (Polynomial.evalRingHom γ) = 0)).card ≤ M := by
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hG
  have hi' : G.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) (hM i)
  intro γ hγ
  rw [Finset.mem_val, Finset.mem_filter] at hγ
  have h1 : (G.map (Polynomial.evalRingHom γ)).coeff i = 0 := by
    rw [hγ.2]; simp
  rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom] at h1
  exact (Polynomial.mem_roots hi').mpr h1

/-- **The branch dichotomy (Step-6 skeleton).** A candidate curve either divides the
factor globally — the branch exists — or its per-`γ` capture set is bounded by the
`Z`-budget of the evaluation defect. -/
theorem branch_capture_dichotomy [Fintype F₀] (R : (F₀[X])[X][Y])
    (pHat : (F₀[X])[X]) {M : ℕ}
    (hM : ∀ i : ℕ, ((Polynomial.eval pHat R).coeff i).natDegree ≤ M) :
    (Polynomial.X - Polynomial.C pHat) ∣ R ∨
      (Finset.univ.filter (fun γ : F₀ =>
        (Polynomial.X - Polynomial.C (pHat.map (Polynomial.evalRingHom γ))) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))).card ≤ M := by
  classical
  rcases eq_or_ne (Polynomial.eval pHat R) 0 with h0 | h0
  · exact Or.inl ((global_branch_iff_eval_zero R pHat).mpr h0)
  · refine Or.inr (le_trans (Finset.card_le_card ?_)
      (card_eval_specialization_collapse_le h0 hM))
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hroot := (Polynomial.dvd_iff_isRoot).mp hγ.2
    rw [eval_specializes]
    exact hroot

/-- **The dichotomy through the C5.8 rigidity**: on a separable fiber with section
match, captured = pinned, so either the decode family is **pinned globally by the
candidate** at every scalar of the cell, or the candidate pins at most `M` of them.
The open `deg_Y ≥ 2` content is exactly a candidate whose pin count beats `M`. -/
theorem pinned_dichotomy_of_section [Fintype F₀] [DecidableEq F₀]
    (R : (F₀[X])[X][Y]) (pHat : (F₀[X])[X]) {x₀ : F₀} (E : Finset F₀)
    (P : F₀ → F₀[X]) {M : ℕ}
    (hM : ∀ i : ℕ, ((Polynomial.eval pHat R).coeff i).natDegree ≤ M)
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hsep : ∀ γ ∈ E, ((R.map (Polynomial.mapRingHom
        (Polynomial.evalRingHom γ))).map (Polynomial.evalRingHom x₀)).Separable)
    (hfib : ∀ γ ∈ E, (P γ).eval x₀ = (pHat.map (Polynomial.evalRingHom γ)).eval x₀) :
    (∀ γ ∈ E, P γ = pHat.map (Polynomial.evalRingHom γ)) ∨
      (E.filter (fun γ => P γ = pHat.map (Polynomial.evalRingHom γ))).card ≤ M := by
  classical
  rcases branch_capture_dichotomy R pHat hM with hglobal | hbound
  · -- the global branch pins every cell scalar through the rigidity
    refine Or.inl fun γ hγ => ?_
    have hdvdp : (Polynomial.X - Polynomial.C
        (pHat.map (Polynomial.evalRingHom γ))) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
      obtain ⟨c, hc⟩ := hglobal
      refine ⟨c.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)), ?_⟩
      rw [hc, Polynomial.map_mul]
      congr 1
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    exact decode_eq_specialized_branch (hsep γ hγ) (hdvdP γ hγ) hdvdp (hfib γ hγ)
  · -- pinned scalars are captured scalars, so the bound transfers
    refine Or.inr (le_trans (Finset.card_le_card ?_) hbound)
    intro γ hγ
    obtain ⟨hγE, hpin⟩ := Finset.mem_filter.mp hγ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hpin ▸ hdvdP γ hγE⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms eval_specializes
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_iff_eval_zero
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms branch_capture_dichotomy
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms pinned_dichotomy_of_section
