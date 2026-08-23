/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffProducer
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Pigeonhole
import ArkLib.ToMathlib.ConditionDiscProduct
import ArkLib.ToMathlib.RationalRootSupply

/-!
# Issue #304 — producing `LocalSeriesDatumOn` from raw GS output.

The landed `StrictCoeffProducer.lean` discharges the issue-named
`ProximityGap.StrictCoeffPolysResidual` from the satisfiable per-`(u, P)` restricted-root
analytic §5 datum `FaithfulCurveExtraction.LocalSeriesDatumOn`.  The remaining core is the
*production* of that datum from the raw Guruswami–Sudan output.  This file builds the
producer field-by-field from the two just-landed GS surfaces:

* `GSFactorAssignment.exists_specialized_factor_assignment` /
  `Claim57Pigeonhole.claim57_pigeonhole` — the per-`z` factor assignment and the
  `x₀`-fiber incidence cells `S_{x₀,R,H} = {z : (Y − C q_z) ∣ R|_{Z:=z} ∧ H(q_z(x₀), z) = 0}`;
* the Hensel-side machinery (`GammaGenuine`, `localSeries`, `coeffHom_loc`, `π̂_z`).

## What is DERIVED here (new welds)

1. **The cell ⟹ Hensel-hypotheses weld**: `Claim57.fiberX x₀ R = Bivariate.evalX (C x₀) R`
   (`fiberX_eq_evalX`), so a claim57 fiber component `H` of the interpolant gives BOTH
   `Irreducible H` and the `dvd_evalX` half of `ClaimA2.Hypotheses x₀ R H`
   (`hypotheses_of_mem_factors_fiber`, `irreducible_of_mem_factors_fiber`).
2. **The cell ⟹ restricted-root weld**: claim57 cell membership at `z` is literally
   `evalEval z (q_z(x₀)) H = 0` (`pointEval_eq_evalEval`, `cell_conditions_of_mem`), which
   `rationalRoot_of_evalEval` turns into the `rootOn` field (`rootOnOfFiber`), with value
   `lc_H(z)·q_z(x₀)` (`= q_z(x₀)` for monic `H`).
3. **The unit condition from `elimPoly` avoidance**: `hx` holds at every `z` avoiding the
   roots of the elimination discriminant `elimPoly (ξ)`, which is PROVEN nonzero
   (`elimPoly_ξ_ne_zero`), so the avoidance demand is cofinite-honest.
4. **The specialization bridge (the new mathematics of this file)**: the localized place
   composite `π̂_z ∘ coeffHom_loc` IS the plain `Z := z` specialization followed by the
   `x₀`-recentering coercion `F[X] → F⟦X⟧` (`map_πhat_coeffHom_loc`); hence the raw GS
   matching-factor divisibility `(Y − C (P z)) ∣ R|_{Z:=z}` transports to the
   power-series-level `hdvd` field with root `taylor x₀ (P z)`
   (`matching_dvd_loc_of_specialized_dvd`), which at the curve centre `x₀ = 0` is the
   EXACT `LocalSeriesDatumOn.hdvd` shape (the landed field coerces `P z` un-recentered,
   so it is the `x₀ = 0` reading — recorded honestly below).
5. **The order-0 congruence is free at the centre**: `π_z(βHensel 0) = root.1`
   (`π_z_βHensel_zero`), and the constructed root value at monic `H`, `x₀ = 0` is
   `(P z).eval 0 = (P z).coeff 0`, so `hcong` is DERIVED (`hcong_of_fiber_monic`).

## The capstone

`localSeriesDatumOn_of_rawGS` — `LocalSeriesDatumOn` from: the fiber-factor cargo
(`hHyp`, monic `hlc`, `R.Separable`), the per-good-`z` claim57 cell membership
(`hfiber` + `hdvdRaw` — exactly `cell_conditions_of_mem` output at `qz := P`), the
cofinite `elimPoly` avoidance, and the two recognized deep residuals (`hvanish` — which has
in-tree producers `localSeriesDatumOn_of_matching_gradedDisc` / `_of_SβLarge` supply chains —
and the §5 Claim-5.9 base-rational reading `htrunc`, here named `TruncReadingOn`).
`localSeriesDatumOn_of_cell` then consumes a single claim57 cell directly.

## Honest scope

* The genuinely deep §5 content is NOT claimed: `TruncReadingOn` (Claim 5.9 / Prop 5.5
  base-rationality of the truncated local series) and the `αGenuine` tail vanishing remain
  the open inputs, now isolated against *constructed* (not assumed) root families.
* The landed `hdvd`/`hcong`/`htrunc` field shapes coerce `P z` into `F⟦X⟧` without
  recentering while `coeffHom_loc` Taylor-recenters at `x₀`; the two readings agree exactly
  at `x₀ = 0` (`taylor_zero`).  The general-`x₀` bridge is proven with the honest
  `taylor x₀ (P z)` root; the capstone is stated at the faithful centre `x₀ = 0`.
* The pigeonhole gives a LARGE CELL inside the good set; the capstone demands the cell
  conditions on the whole good set (the landed `LocalSeriesDatumOn` interface demands its
  cargo at every good `z`).  Restricting the §5 argument to the large cell — or migrating
  the interface to a sub-good-set — is the remaining BCIKS20 Steps-5–7 content, not claimed.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal ProbabilityTheory

namespace ArkLib

namespace RawGS304

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-! ## Part 1 — the Claim-5.7 ⟹ Hensel-side welds -/

/-- The claim57 `x₀`-fiber is the `ClaimA2` specialization `evalX (C x₀)`. -/
theorem fiberX_eq_evalX (x₀ : F) (A : (F[X])[X][Y]) :
    GuruswamiSudan.OverRatFunc.Claim57.fiberX x₀ A = Bivariate.evalX (Polynomial.C x₀) A := by
  rw [GuruswamiSudan.OverRatFunc.Claim57.fiberX, Bivariate.evalX_eq_map]

/-- The claim57 point evaluation is `evalEval` with the arguments swapped. -/
theorem pointEval_eq_evalEval (y z : F) (G : F[X][Y]) :
    GuruswamiSudan.OverRatFunc.Claim57.pointEval y z G = Polynomial.evalEval z y G := by
  rw [GuruswamiSudan.OverRatFunc.Claim57.pointEval_apply, ← evalEval_eq_eval_map]

/-- **The claim57 cell cargo, in the Hensel-side shapes.**  Membership in the incidence
cell `S_{x₀,R,H}` is exactly: the raw matching-factor divisibility at `Z := z` AND the
fiber-component root fact `evalEval z (q_z(x₀)) H = 0`. -/
theorem cell_conditions_of_mem {ι' : Type} {rep : ι' → (F[X])[X][Y]} {x₀ : F}
    {qz : F → F[X]} {S : Finset F} {c : ι' × F[X][Y]} {z : F}
    (hz : z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep x₀ qz S c) :
    ((Polynomial.X - Polynomial.C (qz z)) ∣
        (rep c.1).map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ∧
      Polynomial.evalEval z ((qz z).eval x₀) c.2 = 0 := by
  obtain ⟨-, hdvd, hpt⟩ := GuruswamiSudan.OverRatFunc.Claim57.mem_cell.mp hz
  exact ⟨hdvd, by rwa [pointEval_eq_evalEval] at hpt⟩

/-- A claim57 fiber component is irreducible. -/
theorem irreducible_of_mem_factors_fiber {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hmem : H ∈ (UniqueFactorizationMonoid.factors
      (GuruswamiSudan.OverRatFunc.Claim57.fiberX x₀ R)).toFinset) :
    Irreducible H :=
  UniqueFactorizationMonoid.irreducible_of_factor H (Multiset.mem_toFinset.mp hmem)

/-- **The Hensel hypotheses from the claim57 fiber-component cargo.**  A fiber component
`H` of the interpolant `R` at `x₀` divides the `x₀`-specialization (`dvd_evalX`); with the
S5 separable-specialization fact this is the full `ClaimA2.Hypotheses`. -/
theorem hypotheses_of_mem_factors_fiber {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hmem : H ∈ (UniqueFactorizationMonoid.factors
      (GuruswamiSudan.OverRatFunc.Claim57.fiberX x₀ R)).toFinset)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    Hypotheses x₀ R H :=
  ⟨by
    rw [← fiberX_eq_evalX]
    exact UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hmem),
   hsep⟩

/-! ## Part 2 — the restricted-root family from the fiber cell -/

/-- **The `rootOn` field from the claim57 fiber condition.**  At each member of `S`, the
decoded fiber value `q_z(x₀) = (P z).eval x₀` lies on the curve `H`, so its monicization
carries the rational root `lc_H(z) · (P z).eval x₀`. -/
noncomputable def rootOnOfFiber {H : F[X][Y]} (hH : 0 < H.natDegree)
    {P : F → Polynomial F} {x₀ : F} {S : Finset F}
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval x₀) H = 0) :
    (z : F) → z ∈ S → rationalRoot (H_tilde' H) z :=
  fun z hz => RationalRootSupply.rationalRoot_of_evalEval hH (hfiber z hz)

@[simp]
theorem rootOnOfFiber_val {H : F[X][Y]} (hH : 0 < H.natDegree)
    {P : F → Polynomial F} {x₀ : F} {S : Finset F}
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval x₀) H = 0)
    {z : F} (hz : z ∈ S) :
    (rootOnOfFiber hH hfiber z hz).1 = (H.coeff H.natDegree).eval z * (P z).eval x₀ := rfl

/-- For monic `H` the constructed root IS the decoded fiber value. -/
theorem rootOnOfFiber_val_monic {H : F[X][Y]} (hH : 0 < H.natDegree)
    {P : F → Polynomial F} {x₀ : F} {S : Finset F}
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval x₀) H = 0)
    (hlc : H.leadingCoeff = 1) {z : F} (hz : z ∈ S) :
    (rootOnOfFiber hH hfiber z hz).1 = (P z).eval x₀ := by
  rw [rootOnOfFiber_val, show H.coeff H.natDegree = 1 from hlc, Polynomial.eval_one, one_mul]

/-! ## Part 3 — the unit condition `hx` from cofinite `elimPoly` avoidance -/

/-- The `ξ`-elimination discriminant is a NONZERO polynomial, so the avoidance demand in
`hx_of_elimPoly_avoidance` is over a cofinite set — an honest raw-GS-shaped condition. -/
theorem elimPoly_ξ_ne_zero {H : F[X][Y]} [Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    elimPoly hPos.out (ξ x₀ R H hHyp) ≠ 0 :=
  Match304.elimPoly_ne_zero_of_ne_zero hPos.out (Match304.ξ_ne_zero H x₀ R hHyp)

/-- **The `hx` field**: at every `z` avoiding the roots of `elimPoly (ξ)`, the place
reading of `ξ` is nonzero at EVERY rational root — in particular at the constructed
`rootOn` family. -/
theorem hx_of_elimPoly_avoidance {H : F[X][Y]} [Fact (Irreducible H)]
    [hPos : Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) {S : Finset F}
    (havoid : ∀ z ∈ S, (elimPoly hPos.out (ξ x₀ R H hHyp)).eval z ≠ 0)
    (rootOn : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z) :
    ∀ z (hz : z ∈ S), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0 :=
  fun z hz =>
    Match304.π_z_ne_zero_of_elimPoly_eval_ne_zero hPos.out (ξ x₀ R H hHyp)
      (havoid z hz) (rootOn z hz)

/-! ## Part 4 — the specialization bridge: `π̂_z ∘ coeffHom_loc` IS `Z := z` + recentered
coercion

This is the new mathematical content of this file: the localized place composite used by
`localSeries`/`LocalSeriesDatumOn` agrees, on the interpolant's coefficient ring, with the
plain claim57 specialization `Z := z` followed by the Taylor recentering at `x₀` and the
`F[X] ↪ F⟦X⟧` coercion.  Consequence: the raw GS matching-factor divisibility
`(Y − C (P z)) ∣ R|_{Z:=z}` transports to the power-series matching polynomial. -/

section Bridge

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The recentering coercion `F[X] →+* F⟦X⟧`: Taylor-shift at `x₀`, then the `X`-adic
embedding.  At `x₀ = 0` this is the plain polynomial-to-power-series coercion. -/
noncomputable def recenterCoe (x₀ : F) : F[X] →+* PowerSeries F :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.taylorAlgHom x₀).toRingHom

theorem recenterCoe_apply (x₀ : F) (a : F[X]) :
    recenterCoe x₀ a = ((Polynomial.taylor x₀ a : F[X]) : PowerSeries F) := by
  rw [recenterCoe, RingHom.comp_apply]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.taylorAlgHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply]

/-- **The coefficient-ring specialization bridge.**  On the interpolant's `Y`-coefficient
ring, the localized place composite `π̂_z ∘ coeffHom_loc` equals the plain `Z := z`
specialization followed by the recentering coercion.  Coefficientwise:
`coeff n` of the left side is `((taylor (C x₀) p).coeff n).eval z` (via `π_hat_z_comp`,
`π_z_mk`, `evalEval_C`), and `taylor` commutes with the coefficientwise evaluation map
(`map_taylor`). -/
theorem map_πhat_coeffHom_loc {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (p : F[X][Y]) :
    PowerSeries.map (π_hat_z hHyp z root hx) (coeffHom_loc x₀ hHyp p)
      = recenterCoe x₀ (p.map (Polynomial.evalRingHom z)) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_coeffHom_loc, recenterCoe_apply, Polynomial.coeff_coe]
  have hloc : (π_hat_z hHyp z root hx)
      (locLift hHyp ((Polynomial.taylor (Polynomial.C x₀) p).coeff n))
      = ((Polynomial.taylor (Polynomial.C x₀) p).coeff n).eval z := by
    have h1 : locLift hHyp ((Polynomial.taylor (Polynomial.C x₀) p).coeff n)
        = algebraMap (𝒪 H) (Localization.Away (ξ x₀ R H hHyp))
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (Polynomial.C ((Polynomial.taylor (Polynomial.C x₀) p).coeff n))) := rfl
    rw [h1, π_hat_z_comp, π_z_mk, Polynomial.evalEval_C]
  rw [hloc]
  have htay : (Polynomial.taylor (Polynomial.C x₀) p).map (Polynomial.evalRingHom z)
      = Polynomial.taylor x₀ (p.map (Polynomial.evalRingHom z)) := by
    rw [Polynomial.map_taylor]
    simp
  rw [← htay, Polynomial.coeff_map]
  rfl

/-- **The matching-polynomial factorization.**  The `LocalSeriesDatumOn` matching polynomial
`(R.map coeffHom_loc).map (map π̂_z)` IS the claim57 specialization `R|_{Z:=z}` pushed
through the recentering coercion. -/
theorem map_map_coeffHom_loc_eq {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    (R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx))
      = (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).map (recenterCoe x₀) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, map_πhat_coeffHom_loc hHyp z root hx p,
    Polynomial.coe_mapRingHom]

/-- **The `hdvd` transport (general centre).**  The raw GS matching-factor divisibility at
`Z := z` (the claim57 cell condition / `exists_specialized_factor_assignment` output)
transports to the power-series matching polynomial, with the honest recentered root
`taylor x₀ q`. -/
theorem matching_dvd_loc_of_specialized_dvd {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {q : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C q) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    (Polynomial.X - Polynomial.C ((Polynomial.taylor x₀ q : F[X]) : PowerSeries F)) ∣
      (R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx)) := by
  rw [map_map_coeffHom_loc_eq hHyp z root hx]
  have h2 := Polynomial.map_dvd (recenterCoe x₀) hdvd
  rwa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, recenterCoe_apply] at h2

/-- **The `hdvd` field at the curve centre `x₀ = 0`** — the exact `LocalSeriesDatumOn.hdvd`
shape (the landed field coerces `P z` without recentering; `taylor 0 = id`). -/
theorem matching_dvd_loc_of_specialized_dvd_centred {R : F[X][X][Y]}
    (hHyp : Hypotheses (0 : F) R H) (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ 0 R H hHyp) ≠ 0) {q : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C q) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    (Polynomial.X - Polynomial.C ((q : F[X]) : PowerSeries F)) ∣
      (R.map (coeffHom_loc 0 hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx)) := by
  have h := matching_dvd_loc_of_specialized_dvd hHyp z root hx hdvd
  rwa [Polynomial.taylor_zero] at h

end Bridge

/-! ## Part 5 — the order-0 congruence is free at the centre -/

section Congruence

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The place reading of the order-0 Hensel numerator is the root value itself:
`βHensel 0 = T mod H̃ = mk Y`, and `π_z (mk Y) = root.1`. -/
theorem π_z_βHensel_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0) = root.1 := by
  rw [BCIKS20.HenselNumerator.βHensel_zero, π_z_mk, Polynomial.evalEval_X]

/-- **The `hcong` field, derived** (monic `H`, centre `x₀ = 0`): the constructed fiber root
has value `(P z).eval 0 = (P z).coeff 0`, so the order-0 congruence
`↑(P z) − C (π_z (βHensel 0)) ∈ (X)` is the tautological constant-term fact. -/
theorem hcong_of_fiber_monic {R : F[X][X][Y]} (hHyp : Hypotheses (0 : F) R H)
    (hlc : H.leadingCoeff = 1) {P : F → Polynomial F} {S : Finset F}
    (hfiber : ∀ z ∈ S, Polynomial.evalEval z ((P z).eval 0) H = 0)
    {z : F} (hz : z ∈ S) :
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z
        (rootOnOfFiber (Fact.out (p := 0 < H.natDegree)) hfiber z hz))
        (BCIKS20.HenselNumerator.βHensel H 0 R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [π_z_βHensel_zero,
    rootOnOfFiber_val_monic (Fact.out (p := 0 < H.natDegree)) hfiber hlc hz,
    ← Polynomial.coeff_zero_eq_eval_zero]
  exact FaithfulCurveExtraction.coe_sub_C_coeff_zero_mem_span_X (P z)

end Congruence

/-! ## Part 6 — the isolated deep residual -/

section Residual

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The §5 base-rational reading (Claim 5.9 / Prop. 5.5 content) — the genuinely deep
residual isolated by this file, stated against the CONSTRUCTED root family**: the
`n`-truncation of the local Hensel series at each good place, taken at the fiber-cell
root produced by `rootOnOfFiber`, is the curve specialization with codeword-polynomial
coefficients `c`.  Everything else in `LocalSeriesDatumOn` is derived from raw GS output
(this file) or has its own in-tree production lane (`hvanish`). -/
def TruncReadingOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    {H : F[X][Y]} [Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {R : F[X][X][Y]} (hHyp : Hypotheses (0 : F) R H) (n : ℕ) (c : ℕ → F[X])
    (hfiber : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Polynomial.evalEval z ((P z).eval 0) H = 0) : Prop :=
  ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (hx : (π_z z (rootOnOfFiber hPos.out hfiber z hz)) (ξ 0 R H hHyp) ≠ 0),
    (PowerSeries.trunc n (localSeries hHyp z (rootOnOfFiber hPos.out hfiber z hz) hx) :
      Polynomial F) = ∑ t ∈ Finset.range n, (z - 0) ^ t • c t

end Residual

/-! ## Part 7 — the capstone: `LocalSeriesDatumOn` from raw GS output -/

section Capstone

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`LocalSeriesDatumOn` from raw GS output** (the issue-#304 remaining-core producer),
at the faithful curve centre `x₀ = 0`.  Inputs:

* `hHyp`/`hlc`/`hR` — the fiber-factor cargo (derivable from claim57 cell shape via
  `hypotheses_of_mem_factors_fiber` + the S5 separable-specialization fact; `hlc` is the
  monicization residual);
* `hfiber`/`hdvdRaw` — the per-good-`z` claim57 cell membership, in exactly the
  `cell_conditions_of_mem` output shapes;
* `havoid` — cofinite `elimPoly (ξ)` avoidance (the discriminant is PROVEN nonzero:
  `elimPoly_ξ_ne_zero`);
* `hvanish` — the `αGenuine` tail (in-tree production lanes:
  `localSeriesDatumOn_of_matching_gradedDisc` / `_of_SβLarge` supply chains);
* `htrunc` — the isolated deep §5 residual `TruncReadingOn`.

DERIVED here: `hξ` (proven), `rootOn` (from `hfiber`), `hx` (from `havoid`), `hdvd` (from
`hdvdRaw` via the specialization bridge), `hcong` (free at the centre, monic). -/
noncomputable def localSeriesDatumOn_of_rawGS
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {R : F[X][X][Y]} {H : F[X][Y]}
    [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses (0 : F) R H)
    (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (hfiber : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Polynomial.evalEval z ((P z).eval 0) H = 0)
    (hdvdRaw : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (havoid : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (elimPoly hPos.out (ξ 0 R H hHyp)).eval z ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine H 0 R hHyp t = 0)
    (htrunc : TruncReadingOn u P hHyp n c hfiber) :
    FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := 0, R := R, H := H, hIrr := hIrr, hPos := hPos, hHyp := hHyp,
    hξ := Match304.ξ_ne_zero H 0 R hHyp,
    hlc := hlc, hR := hR, n := n, hn := hn, c := c,
    rootOn := rootOnOfFiber hPos.out hfiber,
    hx := hx_of_elimPoly_avoidance hHyp havoid (rootOnOfFiber hPos.out hfiber),
    hvanish := hvanish,
    htrunc := fun z hz => htrunc z hz _,
    hdvd := fun z hz =>
      matching_dvd_loc_of_specialized_dvd_centred hHyp z _ _ (hdvdRaw z hz),
    hcong := fun _ hz => hcong_of_fiber_monic hHyp hlc hfiber hz }

/-- **The producer from a single Claim-5.7 incidence cell covering the good set.**  If
every good `z` lies in one `(factor, fiber-component)` cell of `claim57_pigeonhole` at
the centre `x₀ = 0` (the §5 "pass to the most common cell" step — the remaining
Steps-5–7 content is exactly that the LARGE cell can replace the good set), then both
per-`z` raw inputs of `localSeriesDatumOn_of_rawGS` are extracted from cell membership. -/
noncomputable def localSeriesDatumOn_of_cell
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {ι' : Type} {rep : ι' → (F[X])[X][Y]} {S : Finset F} {cc : ι' × F[X][Y]}
    [hIrr : Fact (Irreducible cc.2)] [hPos : Fact (0 < cc.2.natDegree)]
    (hcell : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      z ∈ GuruswamiSudan.OverRatFunc.Claim57.cell rep 0 P S cc)
    (hHyp : Hypotheses (0 : F) (rep cc.1) cc.2)
    (hlc : cc.2.leadingCoeff = 1) (hR : (rep cc.1).Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (havoid : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (elimPoly hPos.out (ξ 0 (rep cc.1) cc.2 hHyp)).eval z ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine cc.2 0 (rep cc.1) hHyp t = 0)
    (htrunc : TruncReadingOn u P hHyp n c
      (fun z hz => (cell_conditions_of_mem (hcell z hz)).2)) :
    FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  localSeriesDatumOn_of_rawGS hHyp hlc hR hn c
    (fun z hz => (cell_conditions_of_mem (hcell z hz)).2)
    (fun z hz => (cell_conditions_of_mem (hcell z hz)).1)
    havoid hvanish htrunc

end Capstone

/-! ## Part 8 — the bundled raw cargo and the weld to the issue-named residual -/

section Weld

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The per-`(u, P)` raw GS cargo bundle**: every field is either a raw GS output shape
(claim57 cell membership, factor separability, cofinite discriminant avoidance) or one of
the two recognized deep residuals (`hvanish`, `htrunc`).  No field is a `LocalSeriesDatumOn`
field taken on faith: the analytic fields (`rootOn`, `hx`, `hξ`, `hdvd`, `hcong`) are all
DERIVED by `localSeriesDatumOn_of_rawGSCargo`. -/
structure RawGSCargo {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the GS interpolant (integer model). -/
  R : F[X][X][Y]
  /-- the chosen irreducible fiber component at the centre. -/
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  /-- `H` divides the `x₀ = 0` fiber of `R`, and the fiber is separable. -/
  hHyp : Hypotheses (0 : F) R H
  /-- the monicization residual. -/
  hlc : H.leadingCoeff = 1
  /-- GS interpolant separability. -/
  hR : R.Separable
  /-- number of curve coefficients. -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- claim57 cell condition (fiber half) on the good set. -/
  hfiber : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    Polynomial.evalEval z ((P z).eval 0) H = 0
  /-- claim57 cell condition (matching-factor half) on the good set. -/
  hdvdRaw : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Polynomial.X - Polynomial.C (P z)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  /-- cofinite discriminant avoidance (`elimPoly_ξ_ne_zero` proves the discriminant
  nonzero). -/
  havoid : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (elimPoly hPos.out (ξ 0 R H hHyp)).eval z ≠ 0
  /-- deep residual 1: the `αGenuine` tail (in-tree production lanes exist). -/
  hvanish : ∀ t, n ≤ t → αGenuine H 0 R hHyp t = 0
  /-- deep residual 2: the §5 Claim-5.9 base-rational reading. -/
  htrunc : TruncReadingOn u P hHyp n c hfiber

/-- A producer for raw Guruswami-Sudan cargo in the reduced large-good-set branch of issue #304.
The small-good-set branch is handled separately by interpolation, so this producer is only asked
to build cargo when `k + 1 < |RS_goodCoeffsCurve|`. -/
def RawGSCargoLargeProducer {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Type :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    k + 1 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      RawGSCargo (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-- The bundled raw cargo produces the landed `LocalSeriesDatumOn`. -/
noncomputable def localSeriesDatumOn_of_rawGSCargo
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : RawGSCargo (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    FaithfulCurveExtraction.LocalSeriesDatumOn
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := d.hIrr
  haveI := d.hPos
  localSeriesDatumOn_of_rawGS d.hHyp d.hlc d.hR d.hn d.c d.hfiber d.hdvdRaw d.havoid
    d.hvanish d.htrunc

omit [Nonempty ι] [DecidableEq ι] in
/-- **End-to-end: the issue-named `StrictCoeffPolysResidual` from per-`(u, P)` raw GS
cargo** — the composition of this file's producer with the landed
`strictCoeffPolysResidual_of_localSeriesDatumOn`. -/
theorem strictCoeffPolysResidual_of_rawGSCargo
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        RawGSCargo (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain)
      (δ := δ) :=
  FaithfulCurveExtraction.strictCoeffPolysResidual_of_localSeriesDatumOn
    (fun hk u hprob hJ hsqrt P hP =>
      localSeriesDatumOn_of_rawGSCargo (hInput hk u hprob hJ hsqrt P hP))

omit [Nonempty ι] [DecidableEq ι] in
/-- **End-to-end large-sector form:** per-`(u, P)` raw GS cargo discharges the reduced
`StrictCoeffPolysLargeResidual` surface directly.  This is the producer-facing shape of the
remaining #304 core after the small-good-set sector is removed. -/
theorem strictCoeffPolysLargeResidual_of_rawGSCargo
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      k + 1 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        RawGSCargo (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ProximityGap.StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain)
      (δ := δ) :=
  FaithfulCurveExtraction.strictCoeffPolysLargeResidual_of_localSeriesDatumOn
    (fun hk u hprob hJ hsqrt hcard P hP =>
      localSeriesDatumOn_of_rawGSCargo (hInput hk u hprob hJ hsqrt hcard P hP))

/-- Named-predicate version of `strictCoeffPolysLargeResidual_of_rawGSCargo`. -/
theorem strictCoeffPolysLargeResidual_of_rawGSCargoProducer
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : RawGSCargoLargeProducer (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain)
      (δ := δ) :=
  strictCoeffPolysLargeResidual_of_rawGSCargo
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (fun hk u hprob hJ hsqrt hcard P hP => hInput hk u hprob hJ hsqrt hcard P hP)

/-- **Raw-GS producer package for the named issue-#304 core.**  Two large-sector raw-cargo
producers, one at the target radius and one at the floor-matched working radius, assemble the
single `BCIKS20RemainingCore` Prop consumed by WHIR/STIR/BCIKS wiring. -/
theorem remainingCore_of_rawGSCargoLarge
    {k deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ : RawGSCargoLargeProducer (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ' : RawGSCargoLargeProducer (k := k) (deg := deg) (domain := domain) (δ := δ')) :
    ProximityGap.BCIKS20RemainingCore k deg domain δ δ' :=
  ⟨strictCoeffPolysLargeResidual_of_rawGSCargoProducer hδ,
    strictCoeffPolysLargeResidual_of_rawGSCargoProducer hδ'⟩

end Weld

end RawGS304

end ArkLib

/-! ## Axiom audit (Part 1–3) -/
#print axioms ArkLib.RawGS304.fiberX_eq_evalX
#print axioms ArkLib.RawGS304.pointEval_eq_evalEval
#print axioms ArkLib.RawGS304.cell_conditions_of_mem
#print axioms ArkLib.RawGS304.irreducible_of_mem_factors_fiber
#print axioms ArkLib.RawGS304.hypotheses_of_mem_factors_fiber
#print axioms ArkLib.RawGS304.rootOnOfFiber
#print axioms ArkLib.RawGS304.rootOnOfFiber_val_monic
#print axioms ArkLib.RawGS304.elimPoly_ξ_ne_zero
#print axioms ArkLib.RawGS304.hx_of_elimPoly_avoidance

/-! ## Axiom audit (Part 4–5) -/
#print axioms ArkLib.RawGS304.map_πhat_coeffHom_loc
#print axioms ArkLib.RawGS304.map_map_coeffHom_loc_eq
#print axioms ArkLib.RawGS304.matching_dvd_loc_of_specialized_dvd
#print axioms ArkLib.RawGS304.matching_dvd_loc_of_specialized_dvd_centred
#print axioms ArkLib.RawGS304.π_z_βHensel_zero
#print axioms ArkLib.RawGS304.hcong_of_fiber_monic

/-! ## Axiom audit (Part 6–8) -/
#print axioms ArkLib.RawGS304.TruncReadingOn
#print axioms ArkLib.RawGS304.localSeriesDatumOn_of_rawGS
#print axioms ArkLib.RawGS304.localSeriesDatumOn_of_cell
#print axioms ArkLib.RawGS304.RawGSCargo
#print axioms ArkLib.RawGS304.RawGSCargoLargeProducer
#print axioms ArkLib.RawGS304.localSeriesDatumOn_of_rawGSCargo
#print axioms ArkLib.RawGS304.strictCoeffPolysResidual_of_rawGSCargo
#print axioms ArkLib.RawGS304.strictCoeffPolysLargeResidual_of_rawGSCargo
#print axioms ArkLib.RawGS304.strictCoeffPolysLargeResidual_of_rawGSCargoProducer
#print axioms ArkLib.RawGS304.remainingCore_of_rawGSCargoLarge
