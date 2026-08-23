/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5GenuineMonic
import ArkLib.ToMathlib.GenuineMonicCapstone

/-!
# Issue #304 — the F5 repair on the GENUINE side: finite-range Claim 5.8′ + the `SβLargeAt`
supply from the signed graded collapse

`S5Genuine`/`S5GenuineMonic` prove the genuine truncation `γ = γ_k` (Claim 5.8′) from the §5
largeness hypothesis `hlarge : ∀ t ≥ k, SβLargeAt …` — quantified over **every** tail index.
That is the same over-strong shape the F5 finding repaired on the capsule side
(`HcardDischarge.lean`): the genuine production of `SβLargeAt t` is the counting argument
(`|S_β| > Λ(β_t)·d_H` against a *fixed* agreement set), which is honestly available only on a
finite range `k ≤ t ≤ T`; beyond `T` the vanishing is *algebraic* (the bounded degree of the
Prop-5.5 representative), not combinatorial.  Asking for `∀ t ≥ k` makes the hypothesis
production-circular: for large `t` one would already need the vanishing to bound the weight.

This file is the genuine-side mirror of the F5 repair, wired to the proven signed graded
collapse:

* `claim58prime_genuine_fin_of_monic` — **the finite-range Claim 5.8′ (monic)**:
  `gammaGenuine = trunc k gammaGenuine` from `SβLargeAt` on the *finite* range `[k, T]` plus the
  explicit algebraic tail datum `htailDeg : ∀ t > T, αGenuine t = 0`.
* `htailDeg_genuine_of_representative` — the tail datum **produced** from the genuine Prop-5.5
  representative `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine …` (pure coefficient
  reading, `T := Ppoly.natDegree`).
* `weight_βHensel_le_graded` — `Λ(βHensel t) ≤` the graded budget, by transporting the signed
  graded collapse through the recursion bridge `betaRec (BcoeffSigned) = βHensel`.
* `SβLargeAtFin_of_graded_disc` — **the finite-range largeness supply**: `SβLargeAt t` for every
  `t ∈ [k, T]`, from the per-point vanishing `∃ root, π_z (βHensel t) = 0` on a matching set
  covering the non-vanishing locus of a discriminant, with `|F|` beyond the graded budget — the
  weight side discharged by `weight_βHensel_le_graded`, the cardinality side by the proven
  discriminant counting.
* `gammaGenuine_eq_trunc_of_graded_disc` — **the capstone**: the genuine truncation identity
  `γ = γ_k` from finite geometric data only (per-point vanishing + discriminant counting + the
  genuine representative); no unbounded-range largeness anywhere.

The remaining genuine input `hvanish` (per-point vanishing of `βHensel t` at matching places) is
exactly what the in-flight per-place machinery (`PlaceSeriesCanonical`/`AssembledRootDescent`)
produces — this file gives it a satisfiable landing pad on the genuine route.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claims 5.8/5.8′, Prop 5.5), Appendix A (Lemma A.1 counting, Claim A.2 weight bound).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace GenuineTruncationFin

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Part 1 — the finite-range Claim 5.8′ (the genuine-side F5 repair) -/

/-- **Finite-range genuine tail vanishing (monic).**  `αGenuine t = 0` for all `t ≥ k`, from the
counting branch on the finite range `[k, T]` plus the algebraic tail datum beyond `T`.  Pure
case split — the genuine content is in the two honest sources. -/
theorem alphaGenuine_tail_zero_of_fin {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k T : ℕ}
    (hlargeFin : ∀ t, k ≤ t → t ≤ T → SβLargeAt H x₀ R hHyp t)
    (htailDeg : ∀ t, T < t → αGenuine H x₀ R hHyp t = 0) :
    ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  intro t hkt
  rcases le_or_gt t T with htT | htT
  · exact claim58_genuine_of_monic H hHyp hlc (hlargeFin t hkt htT)
  · exact htailDeg t htT

/-- **The finite-range Claim 5.8′ (genuine, monic) — the F5-repaired truncation identity.**
`gammaGenuine = trunc k gammaGenuine` from `SβLargeAt` on the **finite** range `[k, T]` plus the
explicit algebraic tail datum.  This is the satisfiable replacement for
`claim58prime_genuine_of_monic`'s unbounded-range `hlarge`. -/
theorem claim58prime_genuine_fin_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k T : ℕ}
    (hlargeFin : ∀ t, k ≤ t → t ≤ T → SβLargeAt H x₀ R hHyp t)
    (htailDeg : ∀ t, T < t → αGenuine H x₀ R hHyp t = 0) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  have htail : ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    alphaGenuine_tail_zero_of_fin H hHyp hlc hlargeFin htailDeg
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases ht : t < k
  · rw [if_pos ht]
  · rw [if_neg ht]
    have hcoeff : PowerSeries.coeff t (gammaGenuine x₀ R H hHyp)
        = αGenuine H x₀ R hHyp t := rfl
    rw [hcoeff, htail t (not_lt.mp ht)]

/-! ## Part 2 — the algebraic tail datum from the genuine representative -/

/-- **The genuine `htailDeg` producer.**  From the genuine Prop-5.5 representative
`hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine …` alone, the genuine Hensel coefficients
vanish past the representative's degree (`T := Ppoly.natDegree`) — pure coefficient reading. -/
theorem htailDeg_genuine_of_representative {x₀ : F} {R : F[X][X][Y]}
    {hHyp : ClaimA2.Hypotheses x₀ R H} {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp) :
    ∀ t, Ppoly.natDegree < t → αGenuine H x₀ R hHyp t = 0 := by
  intro t ht
  have hα : αGenuine H x₀ R hHyp t
      = PowerSeries.coeff t (polyToPowerSeries𝕃 H Ppoly) := by
    rw [hrepG]; rfl
  rw [hα, coeff_polyToPowerSeries𝕃, Polynomial.coeff_eq_zero_of_natDegree_lt ht, map_zero]

/-! ## Part 3 — the weight bound on `βHensel` from the signed graded collapse -/

/-- **The graded weight bound on the concrete `(A.1)` numerators.**  Transporting the signed
graded collapse (`GenuineMonicCapstone.betaRec_weight_le_graded_signed`) through the recursion
bridge (`betaRec (BcoeffSigned) = βHensel`): the genuine `βHensel` numerators obey the graded
slack budget. -/
theorem weight_βHensel_le_graded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact GenuineMonicCapstone.betaRec_weight_le_graded_signed x₀ R H hHyp hD hH hmonic hd2
    hdHD hD_Rx0 hR t

/-! ## Part 4 — the finite-range `SβLargeAt` supply -/

section Supply

variable [Fintype F] [DecidableEq F]

/-- **The finite-range `SβLargeAt` supply (monic, discriminant-counted).**  For every
`t ∈ [k, T]`, the §5 largeness `SβLargeAt` holds, given:
* `hvanish` — the per-point vanishing: at every matching place `z` there is a rational root
  with `π_z (βHensel t) = 0` (i.e. `matchingSet ⊆ S_β (βHensel t)`) — the honest per-place
  geometric input, finite-range only;
* the §6 discriminant counting (`hdisc`/`hcover`/`hbig`) — making the matching set beat the
  graded budget;
* the graded side conditions — discharging the weight side via `weight_βHensel_le_graded`.

The witness `D` of `SβLargeAt` is the supplied graded degree bound. -/
theorem SβLargeAtFin_of_graded_disc {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T
        + disc.natDegree < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → SβLargeAt H x₀ R hHyp t := by
  intro t hkt htT
  -- the discriminant-counted cardinality bound at the signed family
  have hcard : (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
        * H.natDegree :=
    GenuineMonicCapstone.hcardFin_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
      (gradedConcreteFin_of_disc hdisc hcover hbig) t hkt htT
  -- transport to the concrete βHensel numerator
  rw [BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t] at hcard
  -- the matching set sits inside S_β (βHensel t)
  have hsub : (↑matchingSet : Set F) ⊆ S_β (βHensel H x₀ R hHyp t) := by
    intro z hz
    exact hvanish t hkt htT z (by simpa using hz)
  have hncard : matchingSet.card ≤ Set.ncard (S_β (βHensel H x₀ R hHyp t)) := by
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at h
  -- assemble the SβLargeAt witness
  refine ⟨D, hD, lt_of_lt_of_le hcard ?_⟩
  exact_mod_cast hncard

end Supply

/-! ## Part 5 — the capstone: the genuine truncation from finite geometric data -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The genuine truncation identity from finite geometric data (monic).**  Claim 5.8′
`gammaGenuine = trunc k gammaGenuine` from:
* the per-point vanishing of `βHensel t` at matching places, finite range `[k, deg Ppoly]`;
* the §6 discriminant counting;
* the graded side conditions;
* the genuine Prop-5.5 representative `hrepG` (supplying the algebraic tail beyond
  `T := Ppoly.natDegree`).

No unbounded-range largeness hypothesis anywhere — every input is finitely producible. -/
theorem gammaGenuine_eq_trunc_of_graded_disc {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  claim58prime_genuine_fin_of_monic H hHyp hmonic.leadingCoeff
    (SβLargeAtFin_of_graded_disc H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR hvanish
      hdisc hcover hbig)
    (htailDeg_genuine_of_representative H hrepG)

end Capstone

end GenuineTruncationFin

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GenuineTruncationFin.alphaGenuine_tail_zero_of_fin
#print axioms ArkLib.GenuineTruncationFin.claim58prime_genuine_fin_of_monic
#print axioms ArkLib.GenuineTruncationFin.htailDeg_genuine_of_representative
#print axioms ArkLib.GenuineTruncationFin.weight_βHensel_le_graded
#print axioms ArkLib.GenuineTruncationFin.SβLargeAtFin_of_graded_disc
#print axioms ArkLib.GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc
