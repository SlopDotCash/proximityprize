/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.SlicedComposition
import ArkLib.ToMathlib.GSSurfaceRadicalSupply
import ArkLib.ToMathlib.GSResidueSliceWeld
import ArkLib.ToMathlib.BivariateGradedDvd
import ArkLib.ToMathlib.CoverageSelection

/-!
# The fully-sliced grand composition, INSTANTIATED at the decoded GS factor (#302)

`Claim510SlicedComposition.natDegree_eq_one_of_decoded_fold_sliced` is the grand interior
composition of the below-Johnson program: `H.natDegree = 1` with **no trivariate
separability anywhere** — both lanes consume only per-place specialized separability on
their matching loci.  This file applies it to the one concrete surface the in-tree GS chain
actually produces — the decoded factor `decodedSurface …` of the integer representative
`Q₀` of the `K = F(Z)` GS interpolant (`GSSurfaceSupply` §3) — and discharges every input
that has an in-tree supplier:

* **`w` / `hdvd` / `hdeg` — DISCHARGED** from the GS decoding chain:
  `decodedSurface` + `decodedSurface_dvd` + `decodedSurface_natDegree_lt`
  (`gs_divisibility_over_ratfunc` + `affine_pair_of_hammingDist` +
  `integer_representative_eval_eq_zero`, end-to-end), with the node budget `k ≤ N`.
* **`hRgrade` — DISCHARGED** from the honest support-form graded budget of the interpolant
  via `Polynomial.Bivariate.degreeX_coeff_le_of_dvd` (graded budgets descend to divisors;
  here instantiated reflexively at `Q₀`, so the input is the *support-form* budget the GS
  construction actually provides, not the subtraction-form consumer artifact).
* **`hsepT` / `hsepA` — DISCHARGED** down to leading-coefficient nonvanishing: the
  per-place specialized separability on both loci is produced by
  `MappedSeparability.mappedSliceSeparabilityOn_of_slice_leadingCoeff` (the residue
  computation exposes the separability already contained in `hHyp.separable_evalX`); what
  remains per place is only the counted condition
  `(evalX (C x₀) Q₀).leadingCoeff.eval z ≠ 0` plus the centre degree-preservation leg
  (the Schwartz–Zippel-counted goods of `exists_good_centre_slice_discr_ne_zero`).
* **`Ppoly` / `hrepG` — RESHAPED** through the proven monic Faà-di-Bruno match
  (`βHenselAssembled_eq_gammaGenuine_of_monic`): the genuine-representative
  input is now stated against the *constructive* assembled Hensel series
  `βHenselAssembled` rather than the abstract `gammaGenuine`.
* **`e` / `he` / `matchingSet` / `hcard` — DISCHARGED** (in the coverage form) by the
  node-selection double count `Finset.exists_covered_nodes_emb`: an incidence system whose
  scalars each miss at most `A` nodes yields `N` injective nodes each covered by more than
  the `killBudget · H.natDegree` bound — the heavy sets are *constructed*, not assumed.

What remains is parameterized as named hypotheses, each with an honest docstring:
the centre supply `hHyp` for `Q₀` (open `IntegerRepCentreSupply` content — the graph
bundle's `hHyp` cannot carry the surface by F8), the global root supply `root` with its
base-point readings (per-place producible via `DecodedRootSupply.rootDecoded` /
`BranchValuePigeonhole.incidenceRootFn`, but a *total* section has no in-tree producer),
the assembled-series polynomial representative, the discriminant cover, the fold readings,
and the finite numerics.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).

## References
* [BCIKS20] ePrint 2020/654 — §5.2.6–5.2.7, Appendix A; the #302/#304 ledgers.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ProximityPrize.BCIKS20.GammaGenuine
open ProximityGap
open ArkLib ArkLib.GSSurfaceSupply ArkLib.MappedSeparability

attribute [local instance] Classical.propDecidable

namespace ArkLib

namespace SlicedCompositionInstance

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable [Fintype F] [DecidableEq F]

/-- **THE FULLY-SLICED GRAND COMPOSITION AT THE DECODED GS FACTOR.**  `H.natDegree = 1`
with the surface `w := decodedSurface …` produced end-to-end by the in-tree GS chain
(`hdvd`, `hdeg` internal), the graded budget in honest support form (`hRgrade` internal via
divisor descent), the genuine representative stated against the constructive assembled
Hensel series (`hrepG` internal via the proven monic Faà-di-Bruno match), and BOTH
separability lanes discharged down to per-place leading-coefficient nonvanishing
(`hsepT`/`hsepA` internal via the residue computation).

Residual inputs, each named and honest:
* `hHyp` — the open `IntegerRepCentreSupply` content for `Q₀` (the centre curve with
  separable centre slice; producible for the *graph* objects via
  `integerRepCentreSupply_of_bundle`, but the graph `R` cannot carry the surface — F8);
* `root` / `hbaseT` / `hbaseA` — the global root section with its base-point readings
  (per-place producible from branch certificates via `DecodedRootSupply.rootDecoded`;
  no in-tree *total* section exists);
* `hrepB` — the polynomial representative of the assembled Hensel series (the documented
  `GenuinePpolyConverter` loop, reshaped through `βHenselAssembled`);
* `hcdeg` / `hlcT` / `hlcA` — the centre degree preservation and the per-place
  leading-coefficient nonvanishing (the Schwartz–Zippel-counted goods of
  `exists_good_centre_slice_discr_ne_zero` / `c56_evalC_bad_set_card_le`);
* `hdisc` / `hcover` / `hbig` — the §6 discriminant cover and the field-size budget;
* `hfold` — the fold readings of the decoded surface at the `N` nodes (the §5 proximity
  data);
* `hξw` / `hcard` — the `ξ`-weight bound and the heavy cardinality. -/
theorem natDegree_eq_one_of_decoded_GS_factor
    -- the GS decoded-factor chain (supplies `w`, `hdvd`, `hdeg`)
    {n k m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n)
    -- the centre data (open `IntegerRepCentreSupply` content for `Q₀`)
    {x₀ : F} (hHyp : Hypotheses x₀ Q₀ H)
    -- the degree budgets (the graded budget in honest SUPPORT form)
    {D N : ℕ} (hkN : k ≤ N)
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY Q₀)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) Q₀))
    (hbudget : ∀ j ∈ Q₀.support, Bivariate.degreeX (Q₀.coeff j) + j ≤ D)
    -- the genuine representative, against the CONSTRUCTIVE assembled series
    {Ppoly : F[X][Y]}
    (hrepB : polyToPowerSeries𝕃 H Ppoly = βHenselAssembled H x₀ Q₀ hHyp)
    -- the root section and the centre slice goods
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = Q₀.natDegree)
    -- the truncation lane
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)).eval z = (root z).1)
    (hlcT : ∀ z ∈ truncSet,
      (Bivariate.evalX (Polynomial.C x₀) Q₀).leadingCoeff.eval z ≠ 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY Q₀) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the agreement lane
    (e : Fin N → F) (he : Function.Injective e) (u₀ u₁ : Fin N → F)
    (matchingSet : Fin N → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)).eval z = (root z).1)
    (hlcA : ∀ j, ∀ z ∈ matchingSet j,
      (Bivariate.evalX (Polynomial.C x₀) Q₀).leadingCoeff.eval z ≠ 0)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    -- the numerics
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ Q₀ H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget N D H.natDegree
        (Bivariate.natDegreeY Q₀) xw * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  -- `Q₀ ≠ 0` and `0 < natDegree Q₀` from the capstone's own regime `hd2`
  have hd2' : 2 ≤ Q₀.natDegree := hd2
  have hQ0ne : Q₀ ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hd2'
    omega
  have hRdeg : 0 < Q₀.natDegree := by omega
  -- `hRgrade` from the honest support-form budget (graded descent, reflexive instance)
  have hRgrade : ∀ j, Bivariate.degreeX (Q₀.coeff j) ≤ D - j :=
    Polynomial.Bivariate.degreeX_coeff_le_of_dvd hQ0ne dvd_rfl hbudget
  -- `hrepG` through the proven monic Faà-di-Bruno match
  have hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ Q₀ H hHyp :=
    hrepB.trans
      (βHenselAssembled_eq_gammaGenuine_of_monic H x₀ Q₀ hHyp hmonic.leadingCoeff)
  -- both separability lanes from per-place leading-coefficient nonvanishing
  have hsepOnT : MappedSliceSeparabilityOn truncSet hHyp :=
    mappedSliceSeparabilityOn_of_slice_leadingCoeff hHyp hRdeg hcdeg hlcT
  have hsepOnA : ∀ j, MappedSliceSeparabilityOn (matchingSet j) hHyp := fun j =>
    mappedSliceSeparabilityOn_of_slice_leadingCoeff hHyp hRdeg hcdeg (hlcA j)
  -- the grand composition at the decoded surface
  exact BCIKS20.Claim510SlicedComposition.natDegree_eq_one_of_decoded_fold_sliced
    hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepG root
    (lt_of_lt_of_le
      (decodedSurface_natDegree_lt ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close) hkN)
    (decodedSurface_dvd ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close)
    hbaseT
    (fun z hz => hsepOnT z hz (root z)
      (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
        hmonic.leadingCoeff z (root z)))
    hdisc hcover hbig
    e he u₀ u₁ matchingSet hbaseA
    (fun j z hz => hsepOnA j z hz (root z)
      (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
        hmonic.leadingCoeff z (root z)))
    hfold hξw hcard

/-- **The coverage form: the heavy sets are CONSTRUCTED, not assumed.**  As
`natDegree_eq_one_of_decoded_GS_factor`, but the agreement-lane data `e`/`he`/
`matchingSet`/`hcard` are produced by the node-selection double count
`Finset.exists_covered_nodes_emb` from an incidence system `(C, Xs, S)`: scalars `z ∈ C`
each read the fold correctly at all but at most `A` of the candidate nodes `Xs`, and the
double-count budget `|C|·A ≤ (|Xs| − N)·(|C| − killBudget·dH)` selects `N` injective nodes
each covered by more than the kill budget.  The per-place hypotheses are now quantified
over the *incidence system* (`hbaseC`/`hlcC` on `C`, `hfoldC` on the incidences), and the
fold values are read off node functions `U₀, U₁ : F → F`. -/
theorem natDegree_eq_one_of_decoded_coverage
    -- the GS decoded-factor chain
    {n k m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n)
    -- the centre data
    {x₀ : F} (hHyp : Hypotheses x₀ Q₀ H)
    -- the degree budgets
    {D N : ℕ} (hkN : k ≤ N)
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY Q₀)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) Q₀))
    (hbudget : ∀ j ∈ Q₀.support, Bivariate.degreeX (Q₀.coeff j) + j ≤ D)
    -- the genuine representative
    {Ppoly : F[X][Y]}
    (hrepB : polyToPowerSeries𝕃 H Ppoly = βHenselAssembled H x₀ Q₀ hHyp)
    -- the root section and the centre slice goods
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) Q₀).natDegree = Q₀.natDegree)
    -- the truncation lane
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)).eval z = (root z).1)
    (hlcT : ∀ z ∈ truncSet,
      (Bivariate.evalX (Polynomial.C x₀) Q₀).leadingCoeff.eval z ≠ 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY Q₀) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the incidence system replacing the agreement-lane data
    {xw : ℕ} (C Xs : Finset F) (S : F → Finset F) (U₀ U₁ : F → F)
    (hS : ∀ z ∈ C, S z ⊆ Xs)
    {A : ℕ} (hA : ∀ z ∈ C, Xs.card - (S z).card ≤ A)
    (hB : BCIKS20.Claim510Supply.killBudget N D H.natDegree
        (Bivariate.natDegreeY Q₀) xw * H.natDegree < C.card)
    (hbigCov : C.card * A ≤ (Xs.card - N) * (C.card
        - BCIKS20.Claim510Supply.killBudget N D H.natDegree
            (Bivariate.natDegreeY Q₀) xw * H.natDegree))
    (hNX : N ≤ Xs.card)
    (hbaseC : ∀ z ∈ C,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)).eval z = (root z).1)
    (hlcC : ∀ z ∈ C,
      (Bivariate.evalX (Polynomial.C x₀) Q₀).leadingCoeff.eval z ≠ 0)
    (hfoldC : ∀ z ∈ C, ∀ x ∈ S z,
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x + Polynomial.C x₀)).eval z = U₀ x + z * U₁ x)
    -- the remaining numeric
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ Q₀ H hHyp) D ≤ (WithBot.some xw : WithBot ℕ)) :
    H.natDegree = 1 := by
  -- select the heavy nodes by the double count
  obtain ⟨eEmb, hcov⟩ := Finset.exists_covered_nodes_emb C Xs S hS hA hB hbigCov hNX
  -- the constructed heavy sets
  exact natDegree_eq_one_of_decoded_GS_factor ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close
    hHyp hkN hD hH hmonic hd2 hdHD hD_Rx0 hbudget hrepB root hcdeg
    hbaseT hlcT hdisc hcover hbig
    (fun j => eEmb j) eEmb.injective
    (fun j => U₀ (eEmb j)) (fun j => U₁ (eEmb j))
    (fun j => C.filter (fun z => eEmb j ∈ S z))
    (fun j z hz => hbaseC z (Finset.mem_filter.mp hz).1)
    (fun j z hz => hlcC z (Finset.mem_filter.mp hz).1)
    (fun j z hz => hfoldC z (Finset.mem_filter.mp hz).1 (eEmb j)
      (Finset.mem_filter.mp hz).2)
    hξw
    (fun j => (hcov j).2)

end SlicedCompositionInstance

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SlicedCompositionInstance.natDegree_eq_one_of_decoded_GS_factor
#print axioms ArkLib.SlicedCompositionInstance.natDegree_eq_one_of_decoded_coverage
