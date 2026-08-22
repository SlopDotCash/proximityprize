/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GenuineMonicCapstone

/-!
# Issue #304 — the graded GS bundle: side conditions (iii)–(v) discharged

The genuine-monic capstone
(`GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic`) consumes a GS-factor
bundle `b : GSFactorData.Bundle x₀` together with five graded side conditions:

| | condition | status here |
|-|-----------|-------------|
| (i)   | `hmonic : b.H.Monic`                                              | **residual** |
| (ii)  | `hd2 : 2 ≤ Bivariate.natDegreeY b.R`                              | **residual** |
| (iii) | `hdHD : b.H.natDegree ≤ b.D`                                      | **proven, for EVERY bundle** |
| (iv)  | `hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (C x₀) b.R)` | **proven, by re-grading `D`** |
| (v)   | `hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j`             | **proven, by re-grading `D`** |

The key observation is that the `Bundle` interface constrains `D` only from below
(`hD : D ≥ Bivariate.totalDegree H`), so `D` may be re-chosen freely above the canonical
self-grading degree

`gradedD x₀ R H = max (totalDegree H) (max (totalDegree (evalX (C x₀) R)) (selfGrade R))`,

where `selfGrade R = R.support.sup (fun j => degreeX (R.coeff j) + j)` is exactly the smallest
`D` validating the paper grading (v) (the `(1,1)`-weighted-degree shape of the GS interpolant
bound).  Conditions (iii)–(v) then hold *definitionally* for the re-graded bundle:

* `bundle_hdHD` — (iii) holds for **every** `Bundle` as stated, since
  `H.natDegree ≤ totalDegree H ≤ D` (no re-grading needed);
* (iv)/(v) hold for the re-graded `D` by `le_max_*` and `Finset.le_sup`.

`GradedBundle` packages a `Bundle` with proven (iii)–(v); `GradedBundle.ofBundle` re-grades any
bundle; `GradedBundle.of_section5Inputs` is the honest constructor from the same §5 standing
inputs as `GSFactorData.of_section5Inputs` (the proven graph family `R_graph`/`H_graph`).

## The honest residual

Conditions (i) and (ii) are genuinely **not** derivable from the graph-extraction specification
(`exists_pg_factors_with_large_common_root_set_of_graph_conditions`):

* (i) `H.Monic`: `H_graph` is an irreducible factor of `evalX (C x₀) R_graph` chosen from
  `UniqueFactorizationMonoid.normalizedFactors`; over the coefficient ring `F[X]` (not a field),
  normalization makes `leadingCoeffY H` a *monic element of* `F[X]` — not the constant `1`.
  Monicity of `H` in `Y` needs the monicization/`clearDenomY` route (the non-monic A.4 wall).
* (ii) `2 ≤ natDegreeY R`: `pg_Rset` members are arbitrary irreducible factors of the GS
  interpolant; factors with `natDegreeY R ≤ 1` exist (they are the §5 "affine"/direct-agreement
  case handled by a different pathway, cf. `FaithfulCurveExtraction.no_linRep_of_nonaffine`).

They are isolated as the named residual `MonicHighYResidual` whose consumer
`section5DataOffcentreFin_of_gradedBundle_residual` is **proven**: together with the per-`P`
producers it yields the full satisfiable off-centre §5 bundle, with (iii)–(v) discharged by the
graded bundle and *only* (i)–(ii) remaining as the GS-factor residual.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, Appendix A.2/A.4.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory Trivariate
open ProximityPrize.BCIKS20.GammaGenuine
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace GSFactorData

open BetaRecGenuineBridge OffcentreKeystone BetaToCurveCoeffPolys

variable {F : Type} [Field F]

/-! ## (iii) — provable for every bundle -/

/-- **Side condition (iii) holds for every GS-factor bundle.**  `H.natDegree ≤ totalDegree H`
(the leading `Y`-monomial contributes at least `natDegree` to the total degree), and
`totalDegree H ≤ D` is the bundle's own `hD`. -/
theorem bundle_hdHD {x₀ : F} (b : Bundle (F := F) x₀) : b.H.natDegree ≤ b.D := by
  have hne : b.H ≠ 0 := fun h => by simpa [h] using b.hH
  have hmem : b.H.natDegree ∈ b.H.support :=
    Polynomial.natDegree_mem_support_of_nonzero hne
  have h1 : (b.H.coeff b.H.natDegree).natDegree + b.H.natDegree
      ≤ Bivariate.totalDegree b.H :=
    Polynomial.Bivariate.coeff_totalDegree_le b.H hmem
  exact le_trans (le_trans (Nat.le_add_left _ _) h1) b.hD

/-! ## The self-grading degree -/

/-- The smallest `D` validating the paper grading (v) for `R`: the maximum of
`degreeX (R.coeff j) + j` over the `Y`-support of `R` — the `(1,1)`-weighted-degree shape of
the GS interpolant bound. -/
noncomputable def selfGrade (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun j => Bivariate.degreeX (R.coeff j) + j)

/-- Any `D ≥ selfGrade R` validates the paper grading (v). -/
theorem hR_of_selfGrade_le {R : F[X][X][Y]} {D : ℕ} (hD : selfGrade R ≤ D) :
    ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j := by
  intro j
  by_cases hj : j ∈ R.support
  · have h1 : Bivariate.degreeX (R.coeff j) + j ≤ selfGrade R :=
      Finset.le_sup (f := fun j => Bivariate.degreeX (R.coeff j) + j) hj
    exact Nat.le_sub_of_add_le (le_trans h1 hD)
  · have h0 : R.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    rw [h0]
    simp [Polynomial.Bivariate.degreeX]

/-- The canonical graded degree bound for the GS-factor pair `(R, H)` at centre `x₀`: the
smallest `D` simultaneously validating `hD` (`≥ totalDegree H`), (iv)
(`≥ totalDegree (evalX (C x₀) R)`) and (v) (the paper grading). -/
noncomputable def gradedD (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H)
    (max (Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) (selfGrade R))

theorem totalDegree_le_gradedD (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ gradedD x₀ R H :=
  le_max_left _ _

theorem totalDegree_evalX_le_gradedD (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ gradedD x₀ R H :=
  le_max_of_le_right (le_max_left _ _)

theorem selfGrade_le_gradedD (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) :
    selfGrade R ≤ gradedD x₀ R H :=
  le_max_of_le_right (le_max_right _ _)

/-! ## The graded bundle -/

/-- A GS-factor `Bundle` whose degree bound `D` additionally satisfies the graded side
conditions (iii)–(v) of the genuine-monic capstone:

* `hdHD` — (iii) `H.natDegree ≤ D`;
* `hD_Rx0` — (iv) `D ≥ totalDegree (evalX (C x₀) R)`;
* `hR` — (v) the paper grading `degreeX (R.coeff j) ≤ D - j`. -/
structure GradedBundle (x₀ : F) extends Bundle (F := F) x₀ where
  hdHD : H.natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)
  hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j

/-- **Re-grading.**  Every GS-factor bundle yields a graded bundle with the same `(R, H)` data
by enlarging `D` to `max b.D (gradedD x₀ b.R b.H)`: conditions (iii)–(v) all hold at the
re-graded degree. -/
noncomputable def GradedBundle.ofBundle {x₀ : F} (b : Bundle (F := F) x₀) :
    GradedBundle (F := F) x₀ where
  R := b.R
  H := b.H
  hIrr := b.hIrr
  hPos := b.hPos
  hHyp := b.hHyp
  hH := b.hH
  D := max b.D (gradedD x₀ b.R b.H)
  hD := le_trans b.hD (le_max_left _ _)
  hdHD := le_trans (bundle_hdHD b) (le_max_left _ _)
  hD_Rx0 := le_trans (totalDegree_evalX_le_gradedD x₀ b.R b.H) (le_max_right _ _)
  hR := hR_of_selfGrade_le
    (le_trans (selfGrade_le_gradedD x₀ b.R b.H) (le_max_right _ _))

@[simp] theorem GradedBundle.ofBundle_R {x₀ : F} (b : Bundle (F := F) x₀) :
    (GradedBundle.ofBundle b).R = b.R := rfl

@[simp] theorem GradedBundle.ofBundle_H {x₀ : F} (b : Bundle (F := F) x₀) :
    (GradedBundle.ofBundle b).H = b.H := rfl

@[simp] theorem GradedBundle.ofBundle_D {x₀ : F} (b : Bundle (F := F) x₀) :
    (GradedBundle.ofBundle b).D = max b.D (gradedD x₀ b.R b.H) := rfl

/-! ## The constructor from the honest §5 standing inputs

Identical input list to `GSFactorData.of_section5Inputs` (the proven graph family
`R_graph`/`H_graph` on top of the GS interpolant `ModifiedGuruswami`); the output additionally
carries the proven graded side conditions (iii)–(v). -/

/-- The graded GS-factor bundle from the §5 standing inputs: `R_graph`/`H_graph` with the
re-graded degree bound.  Discharges (iii)–(v) of the genuine-monic capstone for the graph
bundle. -/
noncomputable def GradedBundle.of_section5Inputs
    [DecidableEq F] [Finite F]
    [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)]
    {n m : ℕ} (k : ℕ) {δ : ℚ} (x₀ : F)
    {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    GradedBundle (F := F) x₀ :=
  GradedBundle.ofBundle
    (GSFactorData.of_section5Inputs (m := m) (n := n) k x₀ h_gs
      hx0 hsep hS_nonempty A hA hcount hlarge)

/-- The graded constructor keeps the proven graph factor `R_graph` verbatim. -/
theorem GradedBundle.of_section5Inputs_R
    [DecidableEq F] [Finite F]
    [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)]
    {n m : ℕ} (k : ℕ) {δ : ℚ} (x₀ : F)
    {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    (GradedBundle.of_section5Inputs (m := m) (n := n) k x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge).R
      = R_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge := rfl

/-- The graded constructor keeps the proven graph factor `H_graph` verbatim. -/
theorem GradedBundle.of_section5Inputs_H
    [DecidableEq F] [Finite F]
    [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)]
    {n m : ℕ} (k : ℕ) {δ : ℚ} (x₀ : F)
    {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    (GradedBundle.of_section5Inputs (m := m) (n := n) k x₀ h_gs
        hx0 hsep hS_nonempty A hA hcount hlarge).H
      = H_graph (F := F) (m := m) (n := n) k δ x₀ h_gs
          hx0 hsep hS_nonempty A hA hcount hlarge := rfl

/-! ## The honest residual: (i) monicity and (ii) the Y-degree dichotomy -/

/-- **The GS-factor residual of the genuine-monic capstone.**  Exactly the two side conditions
*not* derivable from the graph-extraction specification:

* `hmonic` — (i): `H_graph` comes from `normalizedFactors` over `F[X]`-coefficients, where
  normalization only makes `leadingCoeffY H` monic *as an element of `F[X]`*, not `1`; monicity
  in `Y` is the monicization/`clearDenomY` wall.
* `hd2` — (ii): `pg_Rset` factors of `Y`-degree `≤ 1` exist (the §5 affine/direct-agreement
  pathway); the curve machinery needs the non-affine `2 ≤ natDegreeY R` branch.

This is a residual *strictly below* the capstone goal: its consumer
`section5DataOffcentreFin_of_gradedBundle_residual` is proven. -/
structure MonicHighYResidual {x₀ : F} (b : Bundle (F := F) x₀) : Prop where
  hmonic : b.H.Monic
  hd2 : 2 ≤ Bivariate.natDegreeY b.R

/-! ## The proven consumer -/

variable {ι : Type} [Fintype ι]
variable [Fintype F] [DecidableEq F]

/-- **The capstone with (iii)–(v) discharged.**  The satisfiable per-`P` off-centre §5 bundle
from a graded GS bundle plus *only* the `MonicHighYResidual` (conditions (i)–(ii)) and the
per-`P` producers: `hdHD`/`hD_Rx0`/`hR` are supplied by the graded bundle, monicity and the
`Y`-degree dichotomy by the residual.  This is the proven consumer pinning the residual as
exactly the remaining GS-factor gap. -/
noncomputable def section5DataOffcentreFin_of_gradedBundle_residual
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (gb : GradedBundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible gb.H)] [_inst_hPos : Fact (0 < gb.H.natDegree)]
    (hres : MonicHighYResidual gb.toBundle)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' gb.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 gb.H Ppoly = gammaGenuine x₀ gb.R gb.H gb.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ gb.R gb.H gb.hHyp
        (BcoeffSigned gb.H x₀ gb.R) t z (root z))
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY gb.R) gb.D gb.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (hHensel : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 gb.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaGenuine x₀ gb.R gb.H gb.hHyp) :
            Polynomial (𝕃 gb.H)) : PowerSeries (𝕃 gb.H)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P
        (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁))
    (hdeg : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 gb.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaGenuine x₀ gb.R gb.H gb.hHyp) :
            Polynomial (𝕃 gb.H)) : PowerSeries (𝕃 gb.H)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    gb.toBundle matchingSet root Ppoly
    hres.hmonic hrep hdegX mpPoint
    hres.hd2 gb.hdHD gb.hD_Rx0 gb.hR
    hdisc hcover hbig hHensel hdeg

end GSFactorData

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.GSFactorData.bundle_hdHD
#print axioms ArkLib.GSFactorData.selfGrade
#print axioms ArkLib.GSFactorData.hR_of_selfGrade_le
#print axioms ArkLib.GSFactorData.gradedD
#print axioms ArkLib.GSFactorData.totalDegree_le_gradedD
#print axioms ArkLib.GSFactorData.totalDegree_evalX_le_gradedD
#print axioms ArkLib.GSFactorData.selfGrade_le_gradedD
#print axioms ArkLib.GSFactorData.GradedBundle
#print axioms ArkLib.GSFactorData.GradedBundle.ofBundle
#print axioms ArkLib.GSFactorData.GradedBundle.ofBundle_R
#print axioms ArkLib.GSFactorData.GradedBundle.ofBundle_H
#print axioms ArkLib.GSFactorData.GradedBundle.ofBundle_D
#print axioms ArkLib.GSFactorData.GradedBundle.of_section5Inputs
#print axioms ArkLib.GSFactorData.GradedBundle.of_section5Inputs_R
#print axioms ArkLib.GSFactorData.GradedBundle.of_section5Inputs_H
#print axioms ArkLib.GSFactorData.MonicHighYResidual
#print axioms ArkLib.GSFactorData.section5DataOffcentreFin_of_gradedBundle_residual
