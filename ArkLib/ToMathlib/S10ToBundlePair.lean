/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.InterpolatedRepresentativeDependentRoot
import ArkLib.ToMathlib.DoubleAssignmentChain

/-!
# Issue #304 — S10-converse to bundle pair: the production chain composed

The end-to-end composition of the per-`z` production chain at the decoded **line** family:
from the Claim-5.7 assignment data + per-good-place S10-converse divisibilities at the full
interpolant `Q₀` + per-representative centre factorizations + per-branch numeric supplies,
through `DoubleAssignmentChain.double_assignment` (the two pigeonholes) into
`exists_representative_pair_of_matching_counting` (the single-counting front door), producing
the keystone bundle's terminal `(Ppoly, hrep, hdegX)` pair **at some pigeonholed
representative and branch** — with no per-place side condition anywhere: the `ξ` and
separability places are carved out internally by Bézout bounds.

The per-branch supplies (`BranchSupply`) are quantified over the finitely many `(R', i)` the
pigeonhole can select — the honest shape, since the choice is existential.  Each field is
in-tree-producible: `Hypotheses`/monic/irreducible from
`PigeonholeFactorSupply.exists_factorization_with_hypotheses`, the grading from the GS
bundle data, `htailα` from the Brick-T producers.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace S10ToBundlePair

open InterpolatedRepresentativeWiring InterpolatedRepresentativeDependentRoot
  DoubleAssignmentChain

variable {F : Type} [Field F]

/-- **The per-branch supply package**: everything the single-counting front door demands of a
selectable representative/branch pair `(R, H)`, with the `Fact` instances carried as fields
(`Fact` is a `Prop`-class, so any two instances are definitionally interchangeable by proof
irrelevance). -/
structure BranchSupply (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) (D k n : ℕ) : Prop where
  hIrr : Irreducible H
  hpos : 0 < H.natDegree
  hmonic : H.Monic
  hHyp : Hypotheses x₀ R H
  hD : Bivariate.totalDegree H ≤ D
  hd2 : 2 ≤ Bivariate.natDegreeY R
  hdHD : H.natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)
  hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j
  hRdeg : 0 < R.natDegree
  hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree
  hξ : letI := Fact.mk hIrr; letI := Fact.mk hpos;
    ξ x₀ R H hHyp ≠ 0
  hbudget : letI := Fact.mk hIrr; letI := Fact.mk hpos;
    clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      + (XiAtIncidenceSupply.xiResultant hpos x₀ R hHyp).natDegree
      + (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.natDegree
      < n
  htailα : letI := Fact.mk hIrr; letI := Fact.mk hpos;
    ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0

/-- **The `hξ`-free constructor**: `ξ ≠ 0` holds unconditionally
(`XiCertReduction.xi_ne_zero`), so the supply package needs only the remaining fields. -/
theorem BranchSupply.of_core {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} {D k n : ℕ}
    (hIrr : Irreducible H) (hpos : 0 < H.natDegree) (hmonic : H.Monic)
    (hHyp : Hypotheses x₀ R H)
    (hD : Bivariate.totalDegree H ≤ D)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hRdeg : 0 < R.natDegree)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    (hbudget : letI := Fact.mk hIrr; letI := Fact.mk hpos;
      clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
        + (XiAtIncidenceSupply.xiResultant hpos x₀ R hHyp).natDegree
        + (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.natDegree
        < n)
    (htailα : letI := Fact.mk hIrr; letI := Fact.mk hpos;
      ∀ t, k ≤ t →
        BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    BranchSupply x₀ R H D k n := by
  haveI : Fact (Irreducible H) := ⟨hIrr⟩
  haveI : Fact (0 < H.natDegree) := ⟨hpos⟩
  exact ⟨hIrr, hpos, hmonic, hHyp, hD, hd2, hdHD, hD_Rx0, hRgrade, hRdeg, hcdeg,
    XiCertReduction.xi_ne_zero x₀ R hHyp, hbudget, htailα⟩

/-- **The production chain, composed.**  S10-converse divisibilities on the good set route
through the double pigeonhole to ONE representative/branch pair `(rep R', H)`, whose matching
set feeds the single-counting front door; the bundle's terminal pair exists at that pair. -/
theorem exists_bundle_pair_of_S10_converse
    [DecidableEq F] [DecidableEq ((RatFunc F)[X][Y])]
    {Q : (RatFunc F)[X][Y]} {Q₀ : (F[X])[X][Y]} {x₀ : F}
    (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X])
    (hassign : ∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
      (Polynomial.X - Polynomial.C q) ∣
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          (Polynomial.X - Polynomial.C q) ∣
            (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hfne : (UniqueFactorizationMonoid.factors Q).toFinset.Nonempty)
    (nF : (RatFunc F)[X][Y] → ℕ)
    (HfF : (R' : (RatFunc F)[X][Y]) → Fin (nF R') → F[X][Y])
    (hfacF : ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      Bivariate.evalX (Polynomial.C x₀) (rep R') = ∏ i, HfF R' i)
    (hnF : ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset, 0 < nF R')
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {goodSet : Finset F}
    (hgood_bad : ∀ z ∈ goodSet, bad.eval z ≠ 0)
    (hdvd : ∀ z ∈ goodSet, (Polynomial.X - Polynomial.C (u₀ + z • u₁)) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    {n : ℕ}
    (hcount : (UniqueFactorizationMonoid.factors Q).toFinset.card
        * ((Finset.univ.sup (fun R'' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset}
            => nF R''.1)) * n) ≤ goodSet.card)
    {D : ℕ}
    (hbranch : ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset, ∀ i : Fin (nF R'),
      BranchSupply x₀ (rep R') (HfF R' i) D k n) :
    ∃ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset, ∃ i : Fin (nF R'),
      ∃ (hIrr : Irreducible (HfF R' i)) (hpos : 0 < (HfF R' i).natDegree),
        letI := Fact.mk hIrr
        letI := Fact.mk hpos
        ∃ (hHyp : Hypotheses x₀ (rep R') (HfF R' i)) (Ppoly : F[X][Y]),
          polyToPowerSeries𝕃 (HfF R' i) Ppoly
              = BetaToCurveCoeffPolys.gammaLocal x₀ (rep R') (HfF R' i) hHyp
                  (BetaRecGenuineBridge.BcoeffSigned (HfF R' i) x₀ (rep R'))
            ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
            ∧ Ppoly.natDegree < k := by
  classical
  -- fire the double pigeonhole at the line family
  obtain ⟨R', hR', i, matchingSet, hms_sub, hms_card, hms_dvd, hms_inc⟩ :=
    double_assignment (Q := Q) (Q₀ := Q₀) (x₀ := x₀) rep bad hassign hfne nF HfF hfacF hnF
      (Pz := fun z => u₀ + z • u₁) hgood_bad hdvd hcount
  -- unpack the branch supplies at the selected pair
  obtain ⟨hIrr, hpos, hmonic, hHyp, hD, hd2, hdHD, hD_Rx0, hRgrade, hRdeg, hcdeg,
    hξ, hbudget, htailα⟩ := hbranch R' hR' i
  haveI : Fact (Irreducible (HfF R' i)) := ⟨hIrr⟩
  haveI : Fact (0 < (HfF R' i).natDegree) := ⟨hpos⟩
  refine ⟨R', hR', i, hIrr, hpos, hHyp, ?_⟩
  -- the front door at the matching set
  exact exists_representative_pair_of_matching_counting x₀ (rep R') (HfF R' i) hHyp hD
    hpos hmonic hd2 hdHD hD_Rx0 hRgrade hξ hRdeg hcdeg h₀ h₁
    (matchingSet := matchingSet)
    (fun z hz => hms_inc z hz) hms_dvd
    (lt_of_lt_of_le hbudget hms_card) htailα

end S10ToBundlePair

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.S10ToBundlePair.BranchSupply.of_core
#print axioms ArkLib.S10ToBundlePair.exists_bundle_pair_of_S10_converse
