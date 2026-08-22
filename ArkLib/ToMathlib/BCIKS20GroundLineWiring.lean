/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BCIKS20GroundLine
import ArkLib.ToMathlib.InterpolatedRepresentativeWiring
import ArkLib.ToMathlib.InterpolatedRepresentativeSliced
import ArkLib.ToMathlib.GenuineMonicCapstone
import ArkLib.ToMathlib.BCIKS20CorrelatedAgreement

/-!
# Claim 5.9 (ground line): the per-place package from the matching lane's native currency

The ground-line capstone `Claim59GroundLine.claim59_of_counting` consumes, per coordinate `x`
and place `z`, the reading package

  `∃ p, p.natDegree ≤ k ∧ (∀ t ≤ k, π_z(β_t) = p.coeff t · π_z(ξ)^{2t−1}) ∧ p(x−x₀) = u₀x + z·u₁x`.

This file produces that package from the **matching lane's native currency** (the S10-converse
output): the per-`z` decoded polynomial `P` with

* the matching divisibility `(X − C P) ∣ R|_{Z:=z}`,
* the incidence value `P.eval x₀ = t_z`,
* `ξ`-nonvanishing at the place, `R.Separable`, monic `H`, and `deg P ≤ k`,
* the §5 good-pair word match `P.eval x = u₀ x + z·u₁ x`.

The witness is `p := taylor x₀ P`:

* the reading identity composes `localSeries_eq_aPTaylor` (per-`z` Hensel uniqueness, landed
  in `InterpolatedRepresentativeWiring`) with `coeff_localSeries_mul` (the multiplied-out L12
  identity) and `coeff_taylorCoerce`;
* the word match transports through `Polynomial.taylor_eval_sub`;
* the degree budget through `Polynomial.natDegree_taylor`.

`claim59_of_matching_currency` then restates the full ground-line Claim 5.9 (+ curve collapse
+ the #138 weight invariant) with the per-place hypothesis in matching-lane currency. The
remaining external inputs are exactly the lanes already under fleet contention: per-`(x,z)`
good-pair data at scale, `R.Separable`, tail vanishing, and the GS numeric accounting.

Axiom-clean.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5.2.7 (good pairs, Claims 5.9–5.11).
-/

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ArkLib.ClearedGammaDefect

namespace ArkLib.Claim59GroundLineWiring

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The per-place reading identity at the Taylor-shifted decoded polynomial.**
From the matching divisibility, the incidence value, `ξ`-nonvanishing, separability and
monicity: `π_z(β_t) = (taylor x₀ P).coeff t · π_z(ξ)^{2t−1}` for every `t`. -/
theorem pi_z_βHensel_eq_taylor_coeff {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : P.eval x₀ = root.1)
    (hRsep : R.Separable) (t : ℕ) :
    (π_z z root) (βHensel H x₀ R hHyp t)
      = (Polynomial.taylor x₀ P).coeff t
          * ((π_z z root) (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  have hser := ArkLib.InterpolatedRepresentativeWiring.localSeries_eq_aPTaylor hHyp hξ hlc
    z root hx hdvd hval hRsep
  have hmul := ArkLib.coeff_localSeries_mul hHyp z root hx t
  rw [hser] at hmul
  have hcoeff : PowerSeries.coeff t (ArkLib.PerZProximateRoot.aPTaylor x₀ P)
      = (Polynomial.taylor x₀ P).coeff t :=
    ArkLib.PerZProximateRoot.coeff_taylorCoerce x₀ P t
  rw [← hmul, hcoeff]

/-- **The per-place package, from matching-lane currency.**  The Claim-5.10 capstone's
per-`z` existential, with witness `p := taylor x₀ P`. -/
theorem perPlace_package_of_matching {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (k : ℕ) (x z : F) (u₀ u₁ : F → F)
    (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : P.eval x₀ = root.1)
    (hRsep : R.Separable)
    (hPdeg : P.natDegree ≤ k)
    (hword : P.eval x = u₀ x + z * u₁ x) :
    ∃ root' : rationalRoot (H_tilde' H) z, ∃ p : F[X],
      p.natDegree ≤ k
        ∧ (∀ t ∈ Finset.range (k + 1),
            π_z z root' (βHensel H x₀ R hHyp t)
              = p.coeff t * (π_z z root' (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
        ∧ p.eval (x - x₀) = u₀ x + z * u₁ x := by
  refine ⟨root, Polynomial.taylor x₀ P, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_taylor]; exact hPdeg
  · intro t _
    exact pi_z_βHensel_eq_taylor_coeff H hHyp hξ hlc z root hx hdvd hval hRsep t
  · rw [Polynomial.taylor_eval_sub, hword]

/-- **The tail bridge.**  The truncation capstones (Claim 5.8′:
`gammaGenuine = ↑(trunc k gammaGenuine)`, produced by `GenuineTruncationFin` /
`DecodedCapstonesCorrected` / the residue welds) supply the ground-line capstone's `htail`
input verbatim: every genuine coefficient at order `≥ k` vanishes. -/
theorem htail_of_trunc {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) {k : ℕ}
    (h : ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H))) :
    ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  intro t ht
  show PowerSeries.coeff t (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp) = 0
  rw [h, Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_degree_lt
    (lt_of_lt_of_le (PowerSeries.degree_trunc_lt _ _) (by exact_mod_cast ht))

/-- **The per-place reading identity, sliced form.**  `pi_z_βHensel_eq_taylor_coeff` with the
(generically unsatisfiable) trivariate `R.Separable` replaced by the per-place mapped
separability — the producible currency of the discriminant lanes (F-series sliced weld). -/
theorem pi_z_βHensel_eq_taylor_coeff_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : P.eval x₀ = root.1)
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) (t : ℕ) :
    (π_z z root) (βHensel H x₀ R hHyp t)
      = (Polynomial.taylor x₀ P).coeff t
          * ((π_z z root) (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  have hser := ArkLib.InterpolatedRepresentativeSliced.localSeries_eq_aPTaylor_sliced hHyp hξ
    hlc z root hx hdvd hval hsep
  have hmul := ArkLib.coeff_localSeries_mul hHyp z root hx t
  rw [hser] at hmul
  have hcoeff : PowerSeries.coeff t (ArkLib.PerZProximateRoot.aPTaylor x₀ P)
      = (Polynomial.taylor x₀ P).coeff t :=
    ArkLib.PerZProximateRoot.coeff_taylorCoerce x₀ P t
  rw [← hmul, hcoeff]

/-- **Claim 5.9 (ground line) from matching-lane currency, sliced form.**  The per-place
package with per-place mapped separability in place of the trivariate Bézout. -/
theorem perPlace_package_of_matching_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (k : ℕ) (x z : F) (u₀ u₁ : F → F)
    (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : P.eval x₀ = root.1)
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (hPdeg : P.natDegree ≤ k)
    (hword : P.eval x = u₀ x + z * u₁ x) :
    ∃ root' : rationalRoot (H_tilde' H) z, ∃ p : F[X],
      p.natDegree ≤ k
        ∧ (∀ t ∈ Finset.range (k + 1),
            π_z z root' (βHensel H x₀ R hHyp t)
              = p.coeff t * (π_z z root' (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
        ∧ p.eval (x - x₀) = u₀ x + z * u₁ x := by
  refine ⟨root, Polynomial.taylor x₀ P, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_taylor]; exact hPdeg
  · intro t _
    exact pi_z_βHensel_eq_taylor_coeff_sliced H hHyp hξ hlc z root hx hdvd hval hsep t
  · rw [Polynomial.taylor_eval_sub, hword]

/-- **Claim 5.9 (ground line) from matching-lane currency (the composed front door).**
Per-coordinate good-pair data — at each of `k+1` coordinates `x`, a counted set `Sx x` of
places each carrying the S10-converse divisibility, the incidence value, `ξ`-nonvanishing,
the decoded degree budget, and the word match — plus the loose weight budgets, tail
vanishing, and `R.Separable`, produce the ground-line Claim 5.9, the curve collapse
`H.natDegree = 1`, and the #138 weight invariant. -/
theorem claim59_of_matching_currency (hlc : H.leadingCoeff = 1)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0) (hRsep : R.Separable)
    (wβ : ℕ → ℕ) (bξ N : ℕ)
    (hwβ : ∀ t ∈ Finset.range (k + 1),
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D ≤ (WithBot.some (wβ t) : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hN1 : ∀ t ≤ k, wβ t + (eClear k - eClear t) * bξ ≤ N)
    (hN2 : 1 + eClear k * bξ ≤ N)
    (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (Sx : F → Finset F)
    (hS : ∀ x ∈ xs, ∀ z ∈ Sx x, ∃ root : rationalRoot (H_tilde' H) z,
      (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0 ∧ ∃ P : F[X],
        (Polynomial.X - Polynomial.C P ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
          ∧ P.eval x₀ = root.1
          ∧ P.natDegree ≤ k
          ∧ P.eval x = u₀ x + z * u₁ x)
    (hcard : ∀ x ∈ xs, N * H.natDegree < (Sx x).card)
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    (∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
        ∀ t, αGenuine H x₀ R hHyp t
          = fieldTo𝕃 (v₀.coeff t)
            + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (v₁.coeff t))
      ∧ H.natDegree = 1
      ∧ BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  refine ArkLib.Claim59GroundLine.claim59_of_counting H hlc hD hH x₀ R hHyp k
    wβ bξ N hwβ hbξ hN1 hN2 xs hxs u₀ u₁ Sx ?_ hcard htail
  intro x hx z hz
  obtain ⟨root, hxν, P, hdvd, hval, hPdeg, hword⟩ := hS x hx z hz
  exact perPlace_package_of_matching H hHyp hξ hlc k x z u₀ u₁ root hxν hdvd hval hRsep
    hPdeg hword

/-- **The sliced composed front door.**  `claim59_of_matching_currency` with the trivariate
`R.Separable` replaced by per-coordinate `MappedSliceSeparabilityOn` — every hypothesis now
in producible currency (discriminant lanes for the slices, S10-converse for the
divisibilities, Claim 5.11 for the counting). -/
theorem claim59_of_matching_currency_sliced (hlc : H.leadingCoeff = 1)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0)
    (wβ : ℕ → ℕ) (bξ N : ℕ)
    (hwβ : ∀ t ∈ Finset.range (k + 1),
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D ≤ (WithBot.some (wβ t) : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hN1 : ∀ t ≤ k, wβ t + (eClear k - eClear t) * bξ ≤ N)
    (hN2 : 1 + eClear k * bξ ≤ N)
    (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (Sx : F → Finset F)
    (hsepOn : ∀ x ∈ xs, ArkLib.MappedSeparability.MappedSliceSeparabilityOn (Sx x) hHyp)
    (hS : ∀ x ∈ xs, ∀ z ∈ Sx x, ∃ root : rationalRoot (H_tilde' H) z,
      (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0 ∧ ∃ P : F[X],
        (Polynomial.X - Polynomial.C P ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
          ∧ P.eval x₀ = root.1
          ∧ P.natDegree ≤ k
          ∧ P.eval x = u₀ x + z * u₁ x)
    (hcard : ∀ x ∈ xs, N * H.natDegree < (Sx x).card)
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    (∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
        ∀ t, αGenuine H x₀ R hHyp t
          = fieldTo𝕃 (v₀.coeff t)
            + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (v₁.coeff t))
      ∧ H.natDegree = 1
      ∧ BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  refine ArkLib.Claim59GroundLine.claim59_of_counting H hlc hD hH x₀ R hHyp k
    wβ bξ N hwβ hbξ hN1 hN2 xs hxs u₀ u₁ Sx ?_ hcard htail
  intro x hx z hz
  obtain ⟨root, hxν, P, hdvd, hval, hPdeg, hword⟩ := hS x hx z hz
  exact perPlace_package_of_matching_sliced H hHyp hξ hlc k x z u₀ u₁ root hxν hdvd hval
    (hsepOn x hx z hz root hxν) hPdeg hword

/-! ## The concrete budget instantiation (the paper's `(2k+1)dD`-class constant)

The abstract `(wβ, bξ, N)` interface of the capstones is dischargeable at the proven graded
collapse: `wβ t := α·(2t−1) + A`, `bξ := (d−1)·A`, `N := α·e_k + A`, with `A = D−d_H+1`,
`α = d·A + D + A`, `d = natDegreeY R` — pure `ℕ`-arithmetic plus the landed
`betaRec_weight_le_graded_signed` and the `betaRec = βHensel` bridge. -/

/-- The dominance arithmetic for the cleared-term budgets: with `α ≥ (d−1)·A`,
`α·(2t−1) + A + (e_k − e_t)·(d−1)·A ≤ α·e_k + A` for all `t ≤ k`. -/
lemma budget_dominates_term {dA α A : ℕ} (hα : dA ≤ α) {t k : ℕ} (htk : t ≤ k) :
    α * (2 * t - 1) + A + (eClear k - eClear t) * dA ≤ α * eClear k + A := by
  have h2 : (eClear k - eClear t) * dA ≤ (eClear k - eClear t) * α :=
    Nat.mul_le_mul_left _ hα
  have h3 : (2 * t - 1) + (eClear k - eClear t) = eClear k := eClear_add_sub htk
  have h4 : α * (2 * t - 1) + (eClear k - eClear t) * α = α * eClear k := by
    rw [mul_comm (eClear k - eClear t) α, ← Nat.mul_add, h3]
  omega

/-- The dominance arithmetic for the section term: `1 + e_k·(d−1)·A ≤ α·e_k + A` when
`(d−1)·A ≤ α` and `1 ≤ A`. -/
lemma budget_dominates_section {dA α A : ℕ} (hα : dA ≤ α) (hA : 1 ≤ A) (k : ℕ) :
    1 + eClear k * dA ≤ α * eClear k + A := by
  have h5 : eClear k * dA ≤ eClear k * α := Nat.mul_le_mul_left _ hα
  have h6 : eClear k * α = α * eClear k := Nat.mul_comm _ _
  omega

/-- **The concrete `hwβ` supply.**  Under monicity + the paper grading, the genuine numerators
obey the graded budget `wβ t = α·(2t−1) + A` — `betaRec_weight_le_graded_signed` transported
through the `betaRec = βHensel` bridge. -/
theorem hwβ_concrete (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
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
  have hb := ArkLib.GenuineMonicCapstone.betaRec_weight_le_graded_signed x₀ R H hHyp
    hD hH hmonic hd2 hdHD hD_Rx0 hR t
  rwa [ArkLib.BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t] at hb

/-- **Claim 5.9 (ground line) at the CONCRETE graded budget — every interface number
discharged.**  Monicity, the paper grading, per-coordinate raw matching data with the explicit
count `(α·e_k + A)·d_H < |S_x|`, the per-place separability slices, and tail vanishing give
the ground-line Claim 5.9 + curve collapse + the #138 weight invariant, with
`A = D−d_H+1`, `α = d·A+D+A`, `d = natDegreeY R`. -/
theorem claim59_concrete (hlc : H.leadingCoeff = 1)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (hξ : ClaimA2.ξ x₀ R H hHyp ≠ 0)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (Sx : F → Finset F)
    (hsepOn : ∀ x ∈ xs, ArkLib.MappedSeparability.MappedSliceSeparabilityOn (Sx x) hHyp)
    (hS : ∀ x ∈ xs, ∀ z ∈ Sx x, ∃ root : rationalRoot (H_tilde' H) z,
      (π_z z root) (ClaimA2.ξ x₀ R H hHyp) ≠ 0 ∧ ∃ P : F[X],
        (Polynomial.X - Polynomial.C P ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
          ∧ P.eval x₀ = root.1
          ∧ P.natDegree ≤ k
          ∧ P.eval x = u₀ x + z * u₁ x)
    (hcard : ∀ x ∈ xs,
      ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
            * eClear k
          + (D - H.natDegree + 1)) * H.natDegree < (Sx x).card)
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    (∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
        ∀ t, αGenuine H x₀ R hHyp t
          = fieldTo𝕃 (v₀.coeff t)
            + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (v₁.coeff t))
      ∧ H.natDegree = 1
      ∧ BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  have hmonic : H.Monic := hlc
  set d := Bivariate.natDegreeY R with hd
  set A := D - H.natDegree + 1 with hA
  set α := d * A + D + A with hα
  have hdA : (d - 1) * A ≤ α := by
    have : (d - 1) * A ≤ d * A := Nat.mul_le_mul_right A (Nat.sub_le d 1)
    omega
  have hA1 : 1 ≤ A := by omega
  -- the ξ-budget from the in-tree bound.
  have hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
      ≤ (WithBot.some ((d - 1) * A) : WithBot ℕ) := by
    have h := weight_ξ_bound (H := H) (R := R) x₀ hH hHyp hd2 hD hD_Rx0
    have hbridge : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
        = (d - 1) * A := by
      have hYH : Bivariate.natDegreeY H = H.natDegree := rfl
      rw [hYH, ← hd, ← hA]
    rwa [hbridge] at h
  exact claim59_of_matching_currency_sliced H hlc hD hH x₀ R hHyp k hξ
    (fun t => α * (2 * t - 1) + A) ((d - 1) * A) (α * eClear k + A)
    (fun t _ => hwβ_concrete H x₀ R hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR t)
    hbξ
    (fun t htk => budget_dominates_term hdA htk)
    (budget_dominates_section hdA hA1 k)
    xs hxs u₀ u₁ Sx hsepOn hS hcard htail

/-! ## The Claim 5.11 coordinate supply

The capstones consume `k+1` field coordinates with counted matching sets.  Claim 5.11's
kernel-clean double-counting core (`ArkLib.Claim511`) produces exactly that over an abstract
coordinate type; this adapter transports it along the RS domain embedding `ωs : α ↪ F`,
yielding the `(xs, Sx, hcard)` triple in the capstones' shape. -/

/-- **The coordinate supply (Claim 5.11 → capstone inputs).**  From the double-counting
inputs — per-`z` nonmatching bound `E`, threshold-largeness of the close set `S`, the slack
inequality, and the coordinate bridge — produce `k+1` *field* coordinates `xs` and a
matching-set assignment `Sx` with `thr < |Sx x|` at every `x ∈ xs`, with `Sx` reading off
the given per-coordinate matching sets along the embedding. -/
theorem coordinate_supply_of_claim511
    {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (ωs : α ↪ F)
    {S : Finset β} {nonmatching : β → Finset α} (matchSet : α → Finset β)
    {E t k thr : ℕ}
    (hbad : ∀ z ∈ S, (nonmatching z).card ≤ E)
    (hthreshold : thr + t ≤ S.card)
    (hsmall : E * S.card < (Fintype.card α - k) * t)
    (hbridge : ∀ x : α,
      thr < (S.filter (fun z => x ∉ nonmatching z)).card →
      thr < (matchSet x).card) :
    ∃ xs : Finset F, xs.card = k + 1 ∧ ∃ Sx : F → Finset β,
      (∀ x ∈ xs, thr < (Sx x).card) ∧
      (∀ i : α, ωs i ∈ xs → Sx (ωs i) = matchSet i) := by
  classical
  obtain ⟨Dtop, hDcard, hDbig⟩ :=
    ArkLib.Claim511.exists_points_with_large_matching_subset_abstract
      (S := S) (nonmatching := nonmatching) (matchSet := matchSet)
      (E := E) (t := t) (k := k) (threshold := thr) hbad hthreshold hsmall hbridge
  refine ⟨Dtop.image ωs,
    by rw [Finset.card_image_of_injective _ ωs.injective, hDcard],
    fun x => if h : ∃ i : α, ωs i = x then matchSet h.choose else ∅, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hex : ∃ j : α, ωs j = ωs i := ⟨i, rfl⟩
    simp only [dif_pos hex, ωs.injective hex.choose_spec]
    exact hDbig i hi
  · intro i _
    have hex : ∃ j : α, ωs j = ωs i := ⟨i, rfl⟩
    simp only [dif_pos hex, ωs.injective hex.choose_spec]

end ArkLib.Claim59GroundLineWiring

section AxiomAudit
#print axioms ArkLib.Claim59GroundLineWiring.pi_z_βHensel_eq_taylor_coeff
#print axioms ArkLib.Claim59GroundLineWiring.perPlace_package_of_matching
#print axioms ArkLib.Claim59GroundLineWiring.claim59_of_matching_currency
#print axioms ArkLib.Claim59GroundLineWiring.pi_z_βHensel_eq_taylor_coeff_sliced
#print axioms ArkLib.Claim59GroundLineWiring.perPlace_package_of_matching_sliced
#print axioms ArkLib.Claim59GroundLineWiring.claim59_of_matching_currency_sliced
#print axioms ArkLib.Claim59GroundLineWiring.htail_of_trunc
#print axioms ArkLib.Claim59GroundLineWiring.hwβ_concrete
#print axioms ArkLib.Claim59GroundLineWiring.claim59_concrete
#print axioms ArkLib.Claim59GroundLineWiring.coordinate_supply_of_claim511
end AxiomAudit
