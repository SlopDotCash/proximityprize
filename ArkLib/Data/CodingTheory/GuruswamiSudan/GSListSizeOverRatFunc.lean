/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSOverRatFunc
import ArkLib.Data.CodingTheory.ProximityGap.GSFactorExtract

/-!
# Guruswami–Sudan list-size / `Y`-degree bound over `K = F(Z)` (Hab25 §3 Step S3)

This file discharges **Step S3** of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`): the bound `D_Y < ℓ` on the
`Y`-degree of the Guruswami–Sudan interpolant over `K = F(Z)`, which controls the **number of
irreducible factors** (and hence the list size) the factorisation step S4 may produce.

Building on the S2 interpolant from `GSOverRatFunc.gs_existence_over_ratfunc`, the
`(1, k-1)`-weighted degree bound recorded in its `Conditions` (`Q_deg`) converts — via the
in-tree, field-generic
`GuruswamiSudan.natDegree_le_of_natWeightedDegree` — into the classical Guruswami–Sudan output-list
bound `D_Y = deg_Y Q ≤ D / (k-1)`, where `D = gs_degree_bound k n m`. This is exactly the
`[BCIKS20] Claim 5.4` `D_Y < ℓ` consequence the paper's Step S3 consumes, now established over the
rational-function field `K`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`); the entire content is the S2 interpolant
plus a weighted-degree→`Y`-degree division bound.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **Hab25 §3, Step S3 — the GS interpolant over `K = F(Z)` has `Y`-degree `≤ D / (k-1)`.**

For received words `f₀, f₁ : Fin n → F`, evaluation domain `ωs : Fin n ↪ F`, and parameters
`1 < k`, `n ≠ 0`, `1 ≤ m`, `0 < k - 1`, there is a Guruswami–Sudan interpolant
`Q ∈ (RatFunc F)[X][Y]` of the generic fold (the S2 output, satisfying `Conditions`) whose
`Y`-degree obeys

  `Q.natDegree ≤ gs_degree_bound k n m / (k - 1)`.

This `D_Y` bound caps the number of irreducible factors the factorisation step (S4) can produce —
the `[BCIKS20] Claim 5.4` list-size input to the Theorem-2 union bound. -/
theorem genericInterpolant_yDegree_le {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      Q.natDegree ≤ gs_degree_bound k n m / (k - 1) := by
  obtain ⟨Q, hQ⟩ := gs_existence_over_ratfunc k m ωs f₀ f₁ hk1 hn hm
  refine ⟨Q, hQ, ?_⟩
  have hnat : natWeightedDegree Q 1 (k - 1) ≤ gs_degree_bound k n m := by
    have h := hQ.Q_deg
    rw [weightedDegree_eq_natWeightedDegree] at h
    exact_mod_cast h
  exact GuruswamiSudan.natDegree_le_of_natWeightedDegree hk hnat

/-- **Hab25 §3, Step S4 — the decoded list / factor count over `K = F(Z)` is `≤ D / (k-1)`.**

Combining the S2 interpolant `Q` over `K` with its S3 `Y`-degree bound and the field-generic
distinct-linear-factor count `GSFactorExtract.gs_list_size_le` (`# {p : (X - C p) ∣ Q} ≤ deg_Y Q`):
*any* finite family `Ps` of decoded message-polynomials over `K` whose linear factors `Y - C p`
all divide `Q` has

  `Ps.card ≤ gs_degree_bound k n m / (k - 1)`.

This is the `[BCIKS20]` Claim 5.4 *list-size* statement (`#factors < ℓ`) over the rational-function
field — the `hYbound` input that the Hab25 Theorem-2 union bound consumes to cap `|E| ≤ ℓ·n`. The
per-factor *unique affine pair* it ranges over is still produced by the deep Hensel step S6; this
lemma supplies only the cardinality cap on the factor index set. -/
theorem decodedList_card_le {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      ∀ Ps : Finset (RatFunc F)[X], (∀ p ∈ Ps, (X - C p) ∣ Q) →
        Ps.card ≤ gs_degree_bound k n m / (k - 1) := by
  obtain ⟨Q, hQ, hdeg⟩ := genericInterpolant_yDegree_le k m ωs f₀ f₁ hk1 hn hm hk
  refine ⟨Q, hQ, fun Ps hdvd => ?_⟩
  exact le_trans (GSFactorExtract.gs_list_size_le Q hQ.Q_ne_0 Ps hdvd) hdeg

end GuruswamiSudan.OverRatFunc
