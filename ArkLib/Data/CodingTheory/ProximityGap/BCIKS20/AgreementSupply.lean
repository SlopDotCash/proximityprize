/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedProximateRoot
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.TailWiring

/-!
# Seam B: the per-place agreement supply (#302) — the LAST open input of hlin

The hlin capstone (`Claim58TailWiring.natDegree_eq_one_of_graded_disc_agreement`) consumes
the per-place agreement `∑_{t<n} π_z(aPre t)·e_jᵗ = u₀ j + z·u₁ j` at the heavy places.
This file PRODUCES it from the decoded lane — BCIKS20 Step 6 (Hensel-lift uniqueness from
the common simple starting root), at the in-tree genuine objects:

* `pi_z_aPre_eq_coeff_localSeries` — **the normalization identification**: `π_z(aPre t)` is
  the `t`-th coefficient of the canonical local Hensel series (both satisfy
  `· × π_z(ξ)^{2t−1} = π_z(βHensel t)`, and `π_z(ξ) ≠ 0`);
* `localSeries_eq_aPDecoded` — **Hensel uniqueness (Step 6)**: the local Hensel series and
  the decoded surface's place-image are both roots of the specialized matching polynomial,
  congruent mod `X` to the common simple approximation — hence EQUAL
  (`specialization_eq_proximate_root_of_hensel` on `placeGeometry_of_localSeries`);
* `pi_z_aPre_eq_taylor_coeff` — the composed coefficient reading:
  `π_z(aPre t) = ((taylor x₀ w).coeff t).eval z`;
* `aPre_sum_eq_decode_eval` — the node sum collapses to the decoded surface's value
  (`Polynomial.eval_eq_sum_range'` + `taylor_eval`);
* **`hagree_of_decoded`** — the capstone's `hagree` input, end-to-end: at every matching
  place where the decoded surface reads the affine fold value at the node, the agreement
  sum holds;
* **`natDegree_eq_one_of_decoded_fold`** — **THE GRAND COMPOSITION (hlin from GS-side data
  only)**: `H.natDegree = 1` from the GS surface factor, the base-point geometry, the
  separability/discriminant certificates, the graded degree budgets, the fold readings at
  `n` nodes, the `ξ`-weight bound, and the heavy cardinality — every hypothesis a named,
  finitely-checkable GS-side fact; **no open mathematical input remains**.

## References
* [BCIKS20] ePrint 2020/654 — §5.2.6 Step 6 (the Hensel uniqueness `π_z(γ) = P_z`),
  §5.2.7 (Claims 5.9–5.10); App. A.4–A.5.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ArkLib ArkLib.DecodedProximateRoot

namespace BCIKS20.Claim510AgreementSupply

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The normalization identification**: `π_z(aPre t)` is the `t`-th coefficient of the
canonical local Hensel series — both clear to `π_z(βHensel t)` against `π_z(ξ)^{2t−1}`. -/
theorem pi_z_aPre_eq_coeff_localSeries {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (t : ℕ) :
    (π_z z root) (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t)
      = PowerSeries.coeff t (localSeries hHyp z root hx) := by
  have hclear := coeff_localSeries_mul hHyp z root hx t
  have hpin := congrArg (π_z z root)
    (BCIKS20.Claim510Supply.betaHensel_eq_aPre_mul_xi_pow H x₀ R hHyp hlc t)
  rw [map_mul, map_pow] at hpin
  have hxp : (π_z z root) (ξ x₀ R H hHyp) ^ (2 * t - 1) ≠ 0 := pow_ne_zero _ hx
  apply mul_right_cancel₀ hxp
  rw [← hpin, ← hclear]

/-- **Hensel uniqueness (BCIKS20 Step 6)**: the canonical local Hensel series equals the
decoded surface's place-image — both are roots of the specialized matching polynomial,
congruent mod `X` to the common simple approximation. -/
theorem localSeries_eq_aPDecoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) :
    localSeries hHyp z root hx = aPDecoded hHyp z root hx w := by
  set g := placeGeometry_of_localSeries hHyp hξ hlc z root hx
    (aPDecoded hHyp z root hx w)
    (Polynomial.dvd_iff_isRoot.mp (aPDecoded_dvd hHyp z root hx hdvd))
    (aPDecoded_cong hHyp z root hx hbase)
    hsepZ with hg
  exact ArkLib.IngredientC.specialization_eq_proximate_root_of_hensel
    g.f g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv

/-- The composed coefficient reading: `π_z(aPre t)` is the `t`-th Taylor coefficient of the
decoded surface at the centre, read at the place. -/
theorem pi_z_aPre_eq_taylor_coeff {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) (t : ℕ) :
    (π_z z root) (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t)
      = ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z := by
  rw [pi_z_aPre_eq_coeff_localSeries hHyp hlc z root hx t,
    localSeries_eq_aPDecoded hHyp hξ hlc z root hx hdvd hbase hsepZ,
    coeff_aPDecoded hHyp z root hx w t]

/-- **The node sum collapses to the decoded surface's value**: with the degree bound
`w.natDegree < n`, the truncated coefficient sum at a node `e` is the full Taylor
evaluation `w((C e) + (C x₀))`, read at the place. -/
theorem aPre_sum_eq_decode_eval {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {n : ℕ} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) (e : F) :
    ∑ t ∈ Finset.range n,
        (π_z z root) (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t) * e ^ t
      = (w.eval (Polynomial.C e + Polynomial.C x₀)).eval z := by
  have hsum : ∀ t ∈ Finset.range n,
      (π_z z root) (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t) * e ^ t
        = (((Polynomial.taylor (Polynomial.C x₀) w).coeff t)
            * (Polynomial.C e) ^ t).eval z := by
    intro t _
    rw [pi_z_aPre_eq_taylor_coeff hHyp hξ hlc z root hx hdvd hbase hsepZ t,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  rw [Finset.sum_congr rfl hsum, ← Polynomial.eval_finset_sum]
  congr 1
  have hdeg' : (Polynomial.taylor (Polynomial.C x₀) w).natDegree < n := by
    rwa [Polynomial.natDegree_taylor]
  rw [← Polynomial.eval_eq_sum_range' hdeg', Polynomial.taylor_eval]

/-- **THE SEAM-B DELIVERABLE: the capstone's `hagree` input, end-to-end from the decoded
lane.**  At every matching place (with its base-point root and the fold reading of the
decoded surface at the node), the agreement sum holds. -/
theorem hagree_of_decoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {n : ℕ} (e : Fin n → F) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z : F, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepZ : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z)))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j) :
    ∀ j, ∀ z ∈ matchingSet j, ∃ r : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        (π_z z r) (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t) * (e j) ^ t)
        = u₀ j + z * u₁ j := by
  intro j z hz
  refine ⟨root z, ?_⟩
  rw [aPre_sum_eq_decode_eval hHyp hξ hlc z (root z) (hx z) hdeg hdvd
    (hbase j z hz) (hsepZ j z hz) (e j)]
  exact hfold j z hz

/-! ## The monic `ξ`-nonvanishing suppliers (free legs) -/

/-- For monic `H`, `ξ` is a unit of `𝒪`, so every place reading is nonzero — the `hx` legs
are FREE. -/
theorem pi_z_xi_ne_zero_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (ξ x₀ R H hHyp) ≠ 0 :=
  ((BCIKS20.HenselNumerator.isUnit_ξ_of_monic (H := H) x₀ R hHyp hlc).map (π_z z root)).ne_zero

/-- `𝒪 H` is nontrivial: `H̃'` has positive degree, so its span is proper. -/
theorem nontrivial_𝒪 : Nontrivial (𝒪 H) := by
  refine Ideal.Quotient.nontrivial ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [natDegree_H_tilde' (Fact.out (p := 0 < H.natDegree))] at hdeg
  have hH := Fact.out (p := 0 < H.natDegree)
  omega

/-- For monic `H`, `ξ ≠ 0` outright. -/
theorem xi_ne_zero_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    ξ x₀ R H hHyp ≠ 0 :=
  haveI := nontrivial_𝒪 (H := H)
  (BCIKS20.HenselNumerator.isUnit_ξ_of_monic (H := H) x₀ R hHyp hlc).ne_zero

/-! ## The grand composition: hlin from GS-side data only -/

variable [Fintype F] [DecidableEq F]

/-- **THE GRAND COMPOSITION — hlin from GS-side data only.**  `H.natDegree = 1` from:
the GS surface factor `(Y′ − C w) ∣ R` (degree `< n`), the base-point geometry on the
truncation and heavy sets, `R.Separable`, the §6 discriminant counting, the graded degree
budgets, the Prop-5.5 genuine representative, the fold readings at `n` injective nodes, the
`ξ`-weight bound, and the heavy cardinality at the explicit `killBudget`.  Every hypothesis
is a named, finitely-checkable GS-side fact: **the agreement leg (Seam B) and the
truncation leg are both produced by the decoded lane from THE SAME surface data**; the
`π_z(ξ) ≠ 0` legs are free (monic `ξ`-unit).  No open mathematical input remains. -/
theorem natDegree_eq_one_of_decoded_fold {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D n : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)  -- (truncation lane only; agreement lane takes the SLICED form)
    -- the truncation lane: the §6 discriminant cover with base-point geometry
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the agreement lane: heavy sets with base-point geometry and fold readings
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepZ : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (pi_z_xi_ne_zero_of_monic hHyp hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    -- the numerics
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hξ : ξ x₀ R H hHyp ≠ 0 := xi_ne_zero_of_monic hHyp hlc
  -- the coefficient tail from the decoded truncation capstone
  have htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
      (ArkLib.DecodedProximateRoot.gammaGenuine_eq_trunc_of_decoded hHyp hξ hD hH hmonic
        hd2 hdHD hD_Rx0 hRgrade hrepG root
        (fun z _ => pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
        hdeg hdvd hbaseT hR hdisc hcover hbig)
  -- the agreement from Seam B
  have hagree := hagree_of_decoded hHyp hξ hlc e u₀ u₁ matchingSet root
    (fun z => pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
    hdeg hdvd hbaseA hsepZ hfold
  -- the weight bound from the kill-budget supply
  have hweight := fun j => BCIKS20.Claim510Supply.weight_killTarget_le H x₀ R hHyp hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (e j) (u₀ j) (u₁ j)
  exact BCIKS20.Claim510Supply.natDegree_eq_one_of_heavy_agreement H x₀ R hHyp hlc
    htail e he u₀ u₁ hD matchingSet hagree hweight hcard

/-- **hlin, GS-side contradiction form**: no `Y`-degree ≥ 2 monic branch admits the
decoded-fold package. -/
theorem false_of_decoded_fold_of_two_le {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hdeg2 : 2 ≤ H.natDegree)
    {D n : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepZ : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (pi_z_xi_ne_zero_of_monic hHyp hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card) :
    False := by
  have h1 := natDegree_eq_one_of_decoded_fold hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
    hrepG root hdeg hdvd hR hbaseT hdisc hcover hbig e he u₀ u₁ matchingSet hbaseA hsepZ
    hfold hξw hcard
  omega

end BCIKS20.Claim510AgreementSupply

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_coeff_localSeries
#print axioms BCIKS20.Claim510AgreementSupply.localSeries_eq_aPDecoded
#print axioms BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_taylor_coeff
#print axioms BCIKS20.Claim510AgreementSupply.aPre_sum_eq_decode_eval
#print axioms BCIKS20.Claim510AgreementSupply.hagree_of_decoded
#print axioms BCIKS20.Claim510AgreementSupply.natDegree_eq_one_of_decoded_fold
#print axioms BCIKS20.Claim510AgreementSupply.false_of_decoded_fold_of_two_le
