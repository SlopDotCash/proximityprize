/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

/-!
# Instantiation lemma for the Claim-5.7 residual bundle `Claim57Residuals`

`ProximityGap.Claim57Residuals` (`Agreement.lean`) is the typed residual bundle carrying the
BCIKS20 Claim-5.7 graph-extraction data: the Claim-5.6 specialization side conditions
(`hx0`/`hsep`),
the close-proximity coefficient set largeness (`hS_nonempty`/`hlarge`), the per-`z` agreement set
`A`
with its matching bridge `hA` and the Johnson-regime counting inequality `hcount`, and the legacy
factor-list bridge `hfactor`.

This file builds that bundle from **genuine geometric / Johnson-regime hypotheses**, discharging the
two derived fields (`A`/`hA` from the canonical matching-coordinate set, `hS_nonempty` from
`hlarge`) and leaving only:

* `hx0`, `hsep` — the Claim-5.6 specialization side conditions (received-word closeness data);
* `hcount` — the **Johnson side condition**, in the form `natWeightedDegree(eval_on_Z Q z) 1 k <
  m·#matchingSet`.  Specializing `A` to the canonical matching-coordinate set
  `matching_coords_for_z` makes `hA` automatic, and `hcount` becomes the genuine Johnson-radius
  counting input (`δ ≤ δ₀(ρ, m) ⟹ enough matching coordinates`), supplied either directly or via
  the `⌈δ·n⌉` nonmatching bound;
* `hlarge` — the close-set largeness (field-size / degree-budget condition);
* `hfactor` — the legacy bridge from `pg_Rset` membership to the Eq-5.12 factorization list.

The measure of success: the hypothesis list is strictly more primitive than the raw bundle — the
agreement set `A` and `hA` are gone (canonicalized to the matching-coordinate set), `hS_nonempty` is
gone (derived from `hlarge`), and the genuine Johnson side condition is isolated in `hcount`.

Unlike the in-tree `graphExtractionHypotheses_of_*` producers (`Agreement.lean`), these lemmas do
**not** carry a spurious ambient `[Claim57Residuals]` instance: they reconstruct the
`GraphExtractionHypotheses` package directly through `GraphExtractionHypotheses.ofLarge`, so they
are
genuinely non-circular instantiation lemmas.

No `sorry`/`axiom`/`native_decide`; `#print axioms` at the bottom shows only
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claims 5.6–5.7, list-decoding agreement).
-/

-- Documentation-heavy file (BCIKS §5 prose in the docstrings); the long-line style linter is
-- disabled locally.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-! ## Step 1 — `GraphExtractionHypotheses` from the Johnson counting input

The canonical choice of agreement set `A z := matching_coords_for_z k δ h_gs z` makes the matching
bridge `hA` automatic (`mem_matching_coords_for_z`), so the only remaining per-`z` datum is the
Johnson counting inequality `hcount`.  `hS_nonempty` is derived from `hlarge`.  This is exactly the
non-circular core of the in-tree `graphExtractionHypotheses_of_matching_coords`. -/

omit [DecidableEq (RatFunc F)] in
/-- **`GraphExtractionHypotheses` from the Johnson counting input (matching-coordinate set).**

Using the canonical agreement set `A z = matching_coords_for_z k δ h_gs z`, the matching bridge `hA`
is automatic and `hS_nonempty` follows from `hlarge`.  The remaining inputs are the Claim-5.6 side
conditions `hx0`/`hsep`, the Johnson counting inequality `hcount` (the genuine Johnson side
condition: `natWeightedDegree(eval_on_Z Q z) 1 k < m·#matchingCoords`), and the close-set largeness
`hlarge`. -/
noncomputable def graphExtractionHypotheses_of_johnson
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (matching_coords_for_z k δ h_gs z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  GraphExtractionHypotheses.ofLarge (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep
    (A := fun z => matching_coords_for_z k δ h_gs z)
    (hA := by
      intro z i hi
      exact (mem_matching_coords_for_z
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z i).mp hi)
    hcount hlarge

omit [DecidableEq (RatFunc F)] in
/-- **`GraphExtractionHypotheses` from the `⌈δ·n⌉` nonmatching bound.**

The most primitive Johnson form: instead of a per-`z` matching-set bound, supply the per-`z` bound
on
the *nonmatching* coordinates implied by `δ`-closeness (`#nonmatching ≤ ⌈δ·n⌉`, proven in tree from
`δᵣ ≤ δ`), together with the degree budget `natWeightedDegree(eval_on_Z Q z) 1 k < m·(n − ⌈δ·n⌉)`.
This is the Johnson-radius regime entering literally: enough coordinates agree because few disagree.
-/
noncomputable def graphExtractionHypotheses_of_natCeil_johnson
    [NeZero n] [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) k δ x₀ h_gs :=
  graphExtractionHypotheses_of_johnson (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep
    (fun z => by
      -- `#matchingCoords = n − #nonmatchingCoords ≥ n − ⌈δn⌉`, so the degree budget transfers.
      refine lt_of_lt_of_le (hcount z) ?_
      rw [matching_coords_card_eq_sub_nonmatching_coords_card
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z]
      exact Nat.mul_le_mul_left m
        (Nat.sub_le_sub_left
          (nonmatching_coords_for_z_card_le_natCeil_delta_mul
            (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs z) n))
    hlarge

/-! ## Step 2 — the `Claim57Residuals` instance from the Johnson inputs

Feed `graphExtractionHypotheses_of_johnson` into the in-tree
`Claim57Residuals.ofGraphExtractionHypotheses`, which discharges every Claim-5.7 field from the
graph package except the legacy factor-list bridge `hfactor` (kept as a documented hypothesis). -/

omit [DecidableEq (RatFunc F)] in
/-- **The Claim-5.7 residual bundle from the Johnson counting input.**

Produces `ProximityGap.Claim57Residuals (F := F) k δ x₀ h_gs` from genuine geometric /
Johnson-regime
hypotheses only:
* `hx0`/`hsep` — the Claim-5.6 specialization side conditions;
* `hcount` — the **Johnson side condition** `natWeightedDegree(eval_on_Z Q z) 1 k <
m·#matchingCoords`
  (the canonical agreement set `matching_coords_for_z` makes the field's `A`/`hA` automatic);
* `hlarge` — the close-set largeness / degree-budget condition (also discharges `hS_nonempty`);
* `hfactor` — the legacy bridge `R ∈ pg_Rset ⟹ R` is in the Eq-5.12 factorization list.

All other fields of `Claim57Residuals` are discharged by the bricks. -/
@[reducible]
noncomputable def claim57Residuals_of_johnson
    [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (matching_coords_for_z k δ h_gs z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  Claim57Residuals.ofGraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀)
    (graphExtractionHypotheses_of_johnson (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hcount hlarge)
    hfactor

omit [DecidableEq (RatFunc F)] in
/-- **The Claim-5.7 residual bundle from the `⌈δ·n⌉` nonmatching bound.**

The most primitive Johnson form of `claim57Residuals_of_johnson`: the per-`z` matching-set bound is
replaced by the degree budget `natWeightedDegree(eval_on_Z Q z) 1 k < m·(n − ⌈δ·n⌉)`, with the
nonmatching coordinate count bounded by `⌈δ·n⌉` in tree from `δ`-closeness. -/
@[reducible]
noncomputable def claim57Residuals_of_natCeil_johnson
    [NeZero n] [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
        m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  Claim57Residuals.ofGraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀)
    (graphExtractionHypotheses_of_natCeil_johnson (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hcount hlarge)
    hfactor

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityGap.graphExtractionHypotheses_of_johnson
#print axioms ProximityGap.graphExtractionHypotheses_of_natCeil_johnson
#print axioms ProximityGap.claim57Residuals_of_johnson
#print axioms ProximityGap.claim57Residuals_of_natCeil_johnson
