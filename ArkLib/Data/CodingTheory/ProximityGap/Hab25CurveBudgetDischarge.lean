/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCurveInterpolantZDegree
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ShareGoodSetWeld

/-!
# The budget discharge: unconditional heavy-cell attribution (#304, legs 3+4 composed)

`exists_curve_cell_production_total` was parametrized on a degenerate-set budget;
`gs_existence_curve_zDegree_card` (leg 3) now produces the interpolant WITH the explicit
budget `B := n·|constraintIndices m|·(gs_degree_bound·(L−1))`.  Composing it with the
leg-4 decoded-set capstone gives the **fully unconditional** heavy-cell attribution:

* **`exists_heavy_factor_cell_on_decoded_set_budgeted`** — under `¬ jointAgreement` and
  the Johnson-radius hypotheses alone, ANY decoded family `P` on ANY scalar set `G` with
  `B < |G|` admits a GS interpolant `Q₀ ≠ 0` and an irreducible factor `R` of `Q₀`
  carrying a `1/#factors(Q₀)` share of `G`:
  `|G| ≤ B + #factors(Q₀)·|G′|` with `(X − C (P γ)) ∣ R|_{Z:=γ}` on all of `G′ ⊆ G`.

No parametrized hypotheses remain: the degenerate budget is explicit, the decode
witnesses come from the residual's own closeness data, and the attribution is the SK4
pigeonhole.  The strict-Johnson lane's remaining open inputs are now exactly the per-rich-cell
surface supply and the heavy-coordinate matching sets (legs 1–2), plus a bound on
`#factors(Q₀)` if a `(ℓ, T)`-uniform `StrictCoeffPolysResidualShare` instance is desired.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan GuruswamiSudan.OverRatFunc GuruswamiSudan.OverRatFunc.ZDegree
open _root_.ProximityGap Code
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The unconditional budgeted heavy-cell attribution (#304, legs 3+4 composed).**
Under `¬ jointAgreement` and the Johnson-radius hypotheses, any decoded family on a
scalar set beating the explicit degenerate budget
`B = n·|constraintIndices m|·(gs_degree_bound·(L−1))` admits an irreducible factor of a
(produced, nonzero) GS curve interpolant carrying a `1/#factors` share of the set with
the family's divisibility on all of it.  No parametrized budget hypothesis remains. -/
theorem exists_heavy_factor_cell_on_decoded_set_budgeted {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hP : ∀ γ ∈ G, (P γ).natDegree < k ∧
      δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ)
    (hnja : ¬ jointAgreement
      (C := (ReedSolomon.code domain k : Set (Fin n → F₀))) (δ := δ) (W := u))
    (hbig : (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) <
      G.card) :
    ∃ Q₀ : (F₀[X])[X][Y],
      Q₀ ≠ 0 ∧
      ∃ R : (F₀[X])[X][Y],
        R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
        Irreducible R ∧
        ∃ G' : Finset F₀,
          G' ⊆ G ∧
          G.card ≤
            (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) +
            (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
          ∀ γ ∈ G',
            Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
            (Polynomial.X - Polynomial.C (P γ)) ∣
              R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  -- leg 3: the interpolant with the explicit degenerate budget
  obtain ⟨Q₀, hQ₀0, hcond, _hYdeg, hbadz⟩ :=
    gs_existence_curve_zDegree_badz (F := F₀) (n := n) (L := L) k m domain
      (fun j i => u j i) (by omega) (NeZero.ne n) hm
  -- the trivial integer representative: `dd = 1`
  have hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) (1 : F₀[X]))) *
        (Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀)))) := by
    rw [map_one, Polynomial.C_1, Polynomial.C_1, one_mul]
  -- leg 4: the decoded-set heavy cell at the explicit budget
  obtain ⟨R, hRmem, hRirr, G', hG'sub, hcount, hdvd⟩ :=
    exists_heavy_factor_cell_on_decoded_set domain u δ
      ((n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)))
      hcond hrep hQ₀0 hkn hm hδ1 hδJ hbadz G P hP hnja hbig
  exact ⟨Q₀, hQ₀0, R, hRmem, hRirr, G', hG'sub, hcount, hdvd⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_on_decoded_set_budgeted
