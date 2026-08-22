/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25UniformShareBudget
import ArkLib.Data.CodingTheory.ProximityGap.Hab25MatchingSetSupply

/-!
# The surface-supply residual and the grand composition (#304, the lane's single residual)

Legs 2–4 of the share-producer frontier are landed.  This file pins leg 1 — the LAST
open input of the strict-Johnson lane — as one named `Prop`, and proves the **grand
conditional composition**: that Prop alone implies the full share-shaped coefficient
extraction.

**Why the residual must carry the fold data** (the honest fence): the bare statement
"an irreducible factor catching many specializations admits a section `(Y − C w) ∣ R`"
is FALSE — `R = Y² − C Z` (constants in `X`) is irreducible, has the root `√γ` at every
square `γ` (about `q/2` catching specializations), and admits no section.  The genuine
Prop 5.5 argument uses that the roots are DECODES of one curve stack (column-wise
low-degree readings) — this is the §5 Hensel/power-series core, in-tree as the
S10-converse / `gammaGenuine` lane.  Accordingly `HeavyCellSurfaceSupply` quantifies
over exactly the data the pipeline provides: the divisibility, the decoded closeness,
and the cell mass.

* `HeavyCellSurfaceSupply` — the named residual: every heavy cell of decoded roots
  admits a surface of bounded degrees;
* **`share_extraction_of_surfaceSupply`** — the grand composition: the residual +
  Johnson-radius hypotheses + the (purely arithmetic) parameter regime imply, for ANY
  decoded family on ANY scalar set beating the explicit budget, the full share-shaped
  coefficient family — wiring `exists_heavy_factor_cell_uniform` (legs 3+4) →
  the supply (leg 1) → `exists_matching_sets_of_decoded` (leg 2) →
  `strict_coeffPolys_of_cell` (SK1).

After this file, #304's strict-Johnson lane IS `HeavyCellSurfaceSupply`: any proof of it
mechanically completes the curve correlated-agreement keystone through the landed chain.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Finset
open GuruswamiSudan GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The surface-supply residual (#304, leg 1 — the lane's single remaining open
input).**  Every irreducible factor whose specializations catch the decodes of one curve
stack on a cell of mass `≥ Nmin` admits a surface `(Y − C w) ∣ R` of `Z`-degree `≤ Wdeg`
and coefficient `X`-degrees `≤ Bw`.

The decoded-closeness leg is essential: without it the statement is FALSE
(`R = Y² − C Z` catches `√γ` at every square `γ` and has no section); with it this is
BCIKS20 Proposition 5.5's many-fibers⟹section core (§5 Hensel machinery, the in-tree
S10-converse lane). -/
def HeavyCellSurfaceSupply {n L : ℕ} (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (k Nmin Wdeg Bw : ℕ) : Prop :=
  ∀ R : Polynomial (Polynomial (Polynomial F₀)), Irreducible R →
    ∀ (G' : Finset F₀) (P : F₀ → F₀[X]),
      (∀ γ ∈ G', (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      (∀ γ ∈ G', (P γ).natDegree < k ∧
        δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ) →
      Nmin ≤ G'.card →
      ∃ w : Polynomial (Polynomial F₀),
        (Polynomial.X - Polynomial.C w) ∣ R ∧
        w.natDegree ≤ Wdeg ∧
        ∀ i, (w.coeff i).natDegree ≤ Bw

/-- **The grand composition (#304): the surface-supply residual implies the full
share-shaped extraction.**  Wiring legs 3+4 (`exists_heavy_factor_cell_uniform`) → the
supply (leg 1) → leg 2 (`exists_matching_sets_of_decoded`) → SK1
(`strict_coeffPolys_of_cell`): under the Johnson-radius hypotheses and the purely
arithmetic parameter regime `hreg`, any decoded family on a scalar set beating the
explicit budget admits a `1/gs_degree_bound` share `G′` carrying ONE coefficient family
`B` with `deg(B j) < k' + 1` and `(P γ).coeff j = (B j).eval γ` on all of `G′` — the
conclusion shape of `StrictCoeffPolysResidualShare (gs_degree_bound k n m) B`. -/
theorem share_extraction_of_surfaceSupply {n k m L k' : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    {Nmin Wdeg Bw : ℕ}
    (hsupply : HeavyCellSurfaceSupply domain u δ k Nmin Wdeg Bw)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hLk : L - 1 ≤ k')
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hP : ∀ γ ∈ G, (P γ).natDegree < k ∧
      δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ)
    (hnja : ¬ jointAgreement
      (C := (ReedSolomon.code domain k : Set (Fin n → F₀))) (δ := δ) (W := u))
    (hbig : (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) <
      G.card)
    -- the parameter regime: any share size compatible with the heavy-cell count is
    -- both `≥ Nmin` and large enough for the matching-set double count
    (hreg : ∀ c : ℕ,
      G.card ≤
        (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) +
          gs_degree_bound k n m * c →
      Nmin ≤ c ∧
        Wdeg * c + n * (max Bw k') < (n - Nat.floor (δ * n)) * c) :
    ∃ B : ℕ → F₀[X],
      (∀ j, (B j).natDegree < k' + 1) ∧
      ∃ G' : Finset F₀,
        G' ⊆ G ∧
        G.card ≤
          (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) +
            gs_degree_bound k n m * G'.card ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  -- legs 3+4: the uniform heavy cell
  obtain ⟨R, hRirr, G', hG'sub, hcount, hdvd⟩ :=
    exists_heavy_factor_cell_uniform domain u δ hk2 hkn hm hδ1 hδJ G P hP hnja hbig
  obtain ⟨hNmin, hregG'⟩ := hreg G'.card hcount
  -- leg 1: the surface
  obtain ⟨w, hwdvd, hwdeg, hwB⟩ :=
    hsupply R hRirr G' P hdvd (fun γ hγ => hP γ (hG'sub hγ)) hNmin
  -- leg 2: the matching sets on the share, at `W := Wdeg ≥ deg w`, `M := max Bw k'`
  obtain ⟨T, hTcard, hTheavy⟩ :=
    exists_matching_sets_of_decoded domain u δ G' P
      (fun γ hγ => (hP γ (hG'sub hγ)).2) (M := max Bw k') (W := Wdeg) hregG'
  -- SK1: the coefficient family on the share
  obtain ⟨B, hBdeg, hBid⟩ :=
    BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
      (domain := domain) (u := u) hRirr hwdvd hLk hwB G' P hdvd
      T (lt_of_le_of_lt hwdeg hTcard)
      (fun t => G'.filter (fun z =>
        (P z).eval (domain t) = (foldSectionAt u t).eval z))
      (fun t _ => Finset.filter_subset _ _)
      (fun t ht => hTheavy t ht)
      (fun t _ z hz => (Finset.mem_filter.mp hz).2)
  exact ⟨B, hBdeg, G', hG'sub, hcount, hBid⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.HeavyCellSurfaceSupply
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.share_extraction_of_surfaceSupply
