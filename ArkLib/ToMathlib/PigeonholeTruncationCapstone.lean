/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PerZProximateRoot
import ArkLib.ToMathlib.GenuinePpolyConverter

/-!
# Issue #304 — the pigeonhole truncation capstone: Claim 5.8′ assembled over the
F7/F8-evading matching lane

The grand assembly of the lane built across `BranchValuePigeonhole`, `CentreVanishingSupply`,
and `PerZProximateRoot`, with the numeric counting in **direct-cardinality** form (no covering
discriminant needed — the pigeonhole supplies the cardinality lower bound directly):

* `gradedConcreteFin_of_card` — the finite-range concrete cardinality family from a direct
  lower bound `gradedCardBudget(T) < n ≤ |matchingSet|` (monotone collapse).
* `SβLargeAtFin_of_card` — the finite-range §5 largeness from per-point vanishing + the
  direct cardinality bound (the disc-free mirror of
  `GenuineTruncationFin.SβLargeAtFin_of_graded_disc`).
* `hvanish_of_pigeonhole` — the per-point vanishing from the pigeonhole `MatchingPoint`
  families (membership-dependent roots suffice: the conclusion is existential).
* `gammaGenuine_eq_trunc_of_pigeonhole` — **THE CAPSTONE**: the Claim 5.8′ truncation identity
  `gammaGenuine = trunc k gammaGenuine` from
  1. per-place data on a pigeonhole matching set: H-incidence at the decoded values,
     specialized matching divisibilities (S10-converse outputs), decoded degree bounds,
     `ξ`-nonvanishing at the incidence roots;
  2. global facts: `Hypotheses x₀ R H`, monic `H`, `ξ ≠ 0`, `R.Separable`, the graded side
     conditions;
  3. the numeric chain: `gradedCardBudget(T) < n ≤ |matchingSet|` (the pigeonhole's output);
  4. the corrected representative `hrepT` (F6-satisfiable, tail index
     `T := max (deg P₀) (deg P₁)`).

  Every hypothesis is a named per-place or global finite fact; the per-place ones are exactly
  the outputs of `CentreVanishingSupply.matching_supply_of_specialized_dvd` +
  `scalar_fold_decoded_divides_specialization`.

## References
* [BCIKS20] §5 (Claims 5.8/5.8′), §5.2.6, §6, Appendix A; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace PigeonholeTruncationCapstone

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The direct-cardinality counting -/

omit [Field F] [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The finite-range concrete cardinality family from a direct lower bound (monotone
collapse; the disc-free mirror of `gradedConcreteFin_of_disc`). -/
theorem gradedConcreteFin_of_card {dY D dH k T n : ℕ} {matchingSet : Finset F}
    (hbudget : gradedCardBudget dY D dH T < n) (hcard : n ≤ matchingSet.card) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > ((((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * t - 1)
            + (D - dH + 1)) * dH : ℕ) : WithBot ℕ) := by
  intro t _hkt htT
  have ht : gradedCardBudget dY D dH t < matchingSet.card :=
    lt_of_le_of_lt (gradedCardBudget_mono dY D dH htT) (lt_of_lt_of_le hbudget hcard)
  have : (gradedCardBudget dY D dH t : WithBot ℕ) < (matchingSet.card : WithBot ℕ) := by
    exact_mod_cast ht
  simpa [gradedCardBudget] using this

section Counting

variable [Fintype F] [DecidableEq F]

/-- **The finite-range §5 largeness, direct-cardinality form** (the disc-free mirror of
`GenuineTruncationFin.SβLargeAtFin_of_graded_disc`): per-point vanishing + the direct
cardinality bound give `SβLargeAt` on `[k, T]`. -/
theorem SβLargeAtFin_of_card {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T < n)
    (hcard : n ≤ matchingSet.card) :
    ∀ t, k ≤ t → t ≤ T → SβLargeAt H x₀ R hHyp t := by
  intro t hkt htT
  have hcardW : (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
        * H.natDegree :=
    GenuineMonicCapstone.hcardFin_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD
      hD_Rx0 hR (gradedConcreteFin_of_card hbudget hcard) t hkt htT
  rw [BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t] at hcardW
  have hsub : (↑matchingSet : Set F) ⊆ S_β (βHensel H x₀ R hHyp t) := by
    intro z hz
    exact hvanish t hkt htT z (by simpa using hz)
  have hncard : matchingSet.card ≤ Set.ncard (S_β (βHensel H x₀ R hHyp t)) := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  refine ⟨D, hD, lt_of_lt_of_le hcardW ?_⟩
  exact_mod_cast hncard

end Counting

/-! ## The per-point vanishing from the pigeonhole MatchingPoint families -/

section Vanish

/-- **The per-point vanishing from the pigeonhole supply.**  The membership-dependent
incidence roots suffice: the conclusion is existential. -/
theorem hvanish_of_pigeonhole {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {Pz : F → F[X]} {k : ℕ}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z ((Pz z).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz)))
        (ClaimA2.ξ x₀ R H hHyp) ≠ 0)
    (hR : R.Separable) (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt htT z hz
  refine ⟨BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz), ?_⟩
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact (PerZProximateRoot.mpFin_of_pigeonhole_supply hHyp hξ hlc hinc hdvd hdeg hx hR T
    t hkt htT z hz).pi_z_eq_zero

end Vanish

/-! ## THE CAPSTONE -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The pigeonhole truncation capstone: Claim 5.8′ over the F7/F8-evading matching lane.**
`gammaGenuine = trunc k gammaGenuine` from per-place pigeonhole data + global GS facts + the
direct numeric chain + the corrected representative.  Every hypothesis is a named output of
the assembled production lanes. -/
theorem gammaGenuine_eq_trunc_of_pigeonhole {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
      = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F} {Pz : F → F[X]}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z ((Pz z).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz)))
        (ClaimA2.ξ x₀ R H hHyp) ≠ 0)
    (hR : R.Separable)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) < n)
    (hcard : n ≤ matchingSet.card) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.claim58prime_genuine_fin_of_monic H hHyp hmonic.leadingCoeff
    (SβLargeAtFin_of_card H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
      (hvanish_of_pigeonhole H hHyp hξ hmonic.leadingCoeff hinc hdvd hdeg hx hR
        (max P₀.natDegree P₁.natDegree))
      hbudget hcard)
    (GenuinePpolyConverter.htailDeg_genuine_of_corrected_representative H hrepT)

end Capstone

end PigeonholeTruncationCapstone

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.PigeonholeTruncationCapstone.gradedConcreteFin_of_card
#print axioms ArkLib.PigeonholeTruncationCapstone.SβLargeAtFin_of_card
#print axioms ArkLib.PigeonholeTruncationCapstone.hvanish_of_pigeonhole
#print axioms ArkLib.PigeonholeTruncationCapstone.gammaGenuine_eq_trunc_of_pigeonhole
