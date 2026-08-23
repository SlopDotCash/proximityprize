/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.OffcentreKeystoneAssembly
import ArkLib.ToMathlib.BetaRecGenuineBridge
import ArkLib.ToMathlib.WeightLambdaCalculus

/-!
# Issue #304 — the genuine-monic capstone: the off-centre bundle from `gammaGenuine` producers

`BetaRecGenuineBridge` proved that for monic `H` the off-centre keystone series at the signed
canonical coefficients **is** the genuine Hensel-lift root:
`gammaLocal … (BcoeffSigned …) = gammaGenuine …`.  This file completes the consumption of that
identification on the two remaining production fronts:

* **The weight/cardinality front at the signed family.**  The graded App-A.4 weight collapse
  (`betaRec_weight_le_graded`, proven for `B_coeff`) transports to `BcoeffSigned` because the
  `Λ`-weight is negation-invariant (`weight_Λ_over_𝒪_neg`):
  - `betaRec_weight_le_graded_signed` — the collapse `Λ(betaRec … (BcoeffSigned …) t) ≤
    (d·A + D + A)·(2t−1) + A` (same slack budget, `A = D − d_H + 1`);
  - `hcardFin_of_graded_signed` — the finite-range `hcardFin` family from a concrete graded
    cardinality bound, at the signed family.

* **The bundle capstone with genuine-object inputs.**
  `section5DataOffcentreFin_of_producers_genuineMonic` builds the satisfiable per-`P` off-centre
  bundle `Section5StrictDataOffcentreFin` from producers whose series-level hypotheses are
  stated against **`gammaGenuine` directly**: the Prop-5.5 representative
  `hrep : polyToPowerSeries𝕃 H Ppoly = gammaGenuine …`, and the per-`z` Hensel data
  `hHensel`/`hdeg` with premises against `trunc k (gammaGenuine …)`.  The `hcardFin` item is
  fully discharged by the signed graded collapse fed by the §6 discriminant counting
  (`gradedConcreteFin_of_disc`).  No recursion-capsule object (`betaRec`, `gammaLocal`,
  `αFromBeta`) appears in the hypothesis list except through the per-point matching data
  `mpPoint` (whose `betaRec` readings ARE the `βHensel` numerator readings, by the bridge).

With this capstone, the strict-Johnson §5 keystone for monic GS factors reduces to exactly:
1. the GS factor bundle (`b`, monic `H`, `2 ≤ d_R`, the paper grading `hR`);
2. the genuine Prop-5.5 representative (`Ppoly`/`hrep`/`hdegX` against `gammaGenuine`);
3. the per-point matching data `mpPoint` (ingredient C / the `hαβ` readings);
4. the per-`z` Hensel root data (`hHensel`/`hdeg` against `trunc k gammaGenuine`);
5. the §6 discriminant counting (`disc`/`hcover`/`hbig`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, §6.2, Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace GenuineMonicCapstone

open BetaRecGenuineBridge

/-! ## Part 1 — the graded weight collapse at the signed canonical family -/

section GradedSigned

variable {F : Type} [Field F]

/-- **The graded weight theorem at the signed canonical family.**  Identical statement and slack
budget to `betaRec_weight_le_graded`, with `Bcoeff := BcoeffSigned`: the `hbB` obligation is the
proven `B_coeff_weight_le_graded` transported through negation-invariance of the `Λ`-weight
(`weight_Λ_over_𝒪_neg`); every other obligation is unchanged. -/
theorem betaRec_weight_le_graded_signed (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  set d := Bivariate.natDegreeY R with hd
  set A := D - H.natDegree + 1 with hA
  set α := d * A + D + A with hα
  refine betaRec_weight_le_excl x₀ R H hHyp (BcoeffSigned H x₀ R)
    hD hH (bW := 0) (bξ := (d - 1) * A)
    (bB := fun i₁ {m} p => (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts))
    (wβ := fun t => α * (2 * t - 1) + A) ?_ ?_ ?_ ?_ ?_
  · -- hbW (monic)
    simpa using
      BCIKS20.HenselNumerator.W𝒪_weight_le_zero_of_monic H hmonic hH hD
  · -- hbξ via weight_ξ_bound
    have h := weight_ξ_bound (H := H) (R := R) x₀ hH hHyp hd2 hD hD_Rx0
    have hbridge : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
        = (d - 1) * A := by
      have : Bivariate.natDegreeY H = H.natDegree := rfl
      rw [this, ← hd, ← hA]
    rwa [hbridge] at h
  · -- hbB via B_coeff_weight_le_graded + negation-invariance of the Λ-weight
    intro i₁ m p
    have hneg : weight_Λ_over_𝒪 hH (BcoeffSigned H x₀ R i₁ p) D
        = weight_Λ_over_𝒪 hH (BCIKS20.HenselNumerator.B_coeff H x₀ R i₁ p) D := by
      rw [BcoeffSigned_apply, weight_Λ_over_𝒪_neg]
    rw [hneg]
    have h := BCIKS20.HenselNumerator.B_coeff_weight_le_graded (H := H) x₀ R i₁ p hH hD hR
    have hbridge : (Bivariate.natDegreeY R - BCIKS20.HenselNumerator.sigmaLambda p)
          * (D + 1 - Bivariate.natDegreeY H)
          + (D - BCIKS20.HenselNumerator.sigmaLambda p)
        = (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts) := by
      have h1 : Bivariate.natDegreeY H = H.natDegree := rfl
      have h2 : BCIKS20.HenselNumerator.sigmaLambda p = Multiset.card p.parts := rfl
      have h3 : D + 1 - H.natDegree = A := by omega
      rw [h1, h2, ← hd, h3]
    rwa [hbridge] at h
  · -- hβ0: weight(mk X) ≤ wβ 0 = α·0 + A = A
    have h := weight_mk_X_le (H := H) hD hH hdHD
    simpa [← hA] using h
  · -- htele (non-forbidden) — verbatim the `betaRec_weight_le_graded` arithmetic
    intro s i₁ hi₁ p hexcl
    have hi₁' : i₁ < s + 2 := Finset.mem_range.mp hi₁
    beta_reduce
    rw [partsCount_affine_sum p α A, mul_zero, zero_add,
      show betaξExp i₁ p = 2 * i₁ + Multiset.card p.parts - 2 from rfl]
    set σ := Multiset.card p.parts with hσ
    rcases Nat.eq_zero_or_pos σ with hσ0 | hσ1
    · have hcard0 : Multiset.card p.parts = 0 := by rw [← hσ]; exact hσ0
      have hp0 : p.parts = 0 := Multiset.card_eq_zero.mp hcard0
      have hm0 : s + 1 - i₁ = 0 := by
        have hps := p.parts_sum
        rw [hp0] at hps
        simp at hps
        omega
      have hi : i₁ = s + 1 := by omega
      rw [hσ0, hm0]
      simp only [Nat.sub_zero, Nat.mul_zero, mul_zero, add_zero]
      rw [show 2 * i₁ - 2 = 2 * s from by omega]
      have hstep : 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right A (Nat.sub_le d 1))
      have h1 : 2 * s * ((d - 1) * A) + (d * A + D) ≤ α * (2 * s) + α := by
        have hα_ge : d * A ≤ α := by rw [hα]; omega
        have h2 : 2 * s * ((d - 1) * A) ≤ α * (2 * s) := by
          calc 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) := hstep
            _ ≤ 2 * s * α := Nat.mul_le_mul_left _ hα_ge
            _ = α * (2 * s) := Nat.mul_comm _ _
        have h3 : d * A + D ≤ α := by rw [hα]; omega
        omega
      calc 2 * s * ((d - 1) * A) + (d * A + D)
          ≤ α * (2 * s) + α := h1
        _ = α * (2 * s + 1) := by ring
        _ ≤ α * (2 * (s + 1) - 1) + A := by
            have : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
            rw [this]
            omega
    · have hexcl' : ¬(i₁ = 0 ∧ σ = 1) := by
        rintro ⟨hi0, hσ1'⟩
        apply hexcl
        refine ⟨hi0, ?_⟩
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (hσ ▸ hσ1')
        have hsum := p.parts_sum
        rw [ha] at hsum ⊢
        simp at hsum
        rw [hsum]
        subst hi0
        norm_num
      have harith := GradedHtele.graded_htele_arith d D H.natDegree
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)) (by omega) hdHD
        i₁ σ hσ1 hexcl'
      have hσm : σ ≤ s + 1 - i₁ := by
        rw [hσ]
        exact betaRec_card_le p
      have hkey : 2 * i₁ + σ - 1 + (2 * (s + 1 - i₁) - σ) = 2 * s + 1 := by omega
      calc (2 * i₁ + σ - 2) * ((d - 1) * A)
            + ((d - σ) * A + (D - σ))
            + (α * (2 * (s + 1 - i₁) - σ) + A * σ)
          = ((2 * i₁ + σ - 2) * ((d - 1) * (D - H.natDegree + 1))
              + ((d - σ) * (D - H.natDegree + 1) + (D - σ))
              + (D - H.natDegree + 1) * σ) + α * (2 * (s + 1 - i₁) - σ) := by
            rw [← hA]; ring
        _ ≤ ((d * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)) * (2 * i₁ + σ - 1)
              + (D - H.natDegree + 1)) + α * (2 * (s + 1 - i₁) - σ) :=
            Nat.add_le_add_right harith _
        _ = α * (2 * i₁ + σ - 1) + α * (2 * (s + 1 - i₁) - σ) + A := by rw [hα, hA]; ring
        _ = α * ((2 * i₁ + σ - 1) + (2 * (s + 1 - i₁) - σ)) + A := by ring
        _ = α * (2 * s + 1) + A := by rw [hkey]
        _ = α * (2 * (s + 1) - 1) + A := by
            rw [show (2 * (s + 1) - 1 : ℕ) = 2 * s + 1 from by omega]

/-- Right-multiplication monotonicity for `WithBot ℕ` weight bounds (local copy of the
`BetaWeightGradedSupply` helper). -/
private theorem withBot_mul_right_le'' {a : WithBot ℕ} {c d : ℕ}
    (h : a ≤ (c : WithBot ℕ)) : a * (d : WithBot ℕ) ≤ ((c * d : ℕ) : WithBot ℕ) := by
  have hcd : ((c * d : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (d : WithBot ℕ) := by
    push_cast; ring
  rw [hcd]
  gcongr

variable [Fintype F] [DecidableEq F]

/-- **The graded finite-range `hcardFin` family at the signed canonical family.**  As
`hcardFin_of_graded`, with `Bcoeff := BcoeffSigned` — exactly the `hcardFin` field of
`Section5StrictDataOffcentreFin` at the signed family. -/
theorem hcardFin_of_graded_signed (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
                * (2 * t - 1)
              + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) t) D
        * H.natDegree := by
  intro t hkt htT
  have hwt := betaRec_weight_le_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR t
  have hmul : weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp (BcoeffSigned H x₀ R) t) D
        * (H.natDegree : WithBot ℕ)
      ≤ ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le'' (by simpa using hwt)
  exact lt_of_le_of_lt hmul (hconcreteFin t hkt htT)

end GradedSigned

/-! ## Part 2 — the genuine-monic bundle capstone -/

section Capstone

open OffcentreKeystone BetaToCurveCoeffPolys

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The genuine-monic capstone.**  The satisfiable per-`P` off-centre §5 bundle
`Section5StrictDataOffcentreFin`, from producers whose series-level hypotheses are stated
against the **genuine Hensel root `gammaGenuine`** (monic case):

* `hrep : polyToPowerSeries𝕃 b.H Ppoly = gammaGenuine x₀ b.R b.H b.hHyp` — the genuine
  Prop-5.5 representative;
* `hHensel`/`hdeg` — per-`z` Hensel data with premises against `trunc k (gammaGenuine …)`;
* `mpPoint` — the per-point matching data at the signed canonical family (whose `betaRec`
  readings are the `βHensel` numerator readings, by `betaRec_BcoeffSigned_eq_βHensel`);
* the §6 discriminant counting (`hdisc`/`hcover`/`hbig`) — discharging `hcardFin` through the
  signed graded collapse (`hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc`), with the
  App-A.4 weight budgets supplied by proven theorems.

The hypothesis list mentions no recursion-capsule series and no legacy `β`/`γ`: every
series-level obligation is a statement about `gammaGenuine`, the honest Hensel-lifted root
pinned by `constantCoeff = α₀` and `eval gammaGenuine Q = 0`. -/
noncomputable def section5DataOffcentreFin_of_producers_genuineMonic
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = gammaGenuine x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp
        (BcoeffSigned b.H x₀ b.R) t z (root z))
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R)
    (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (hHensel : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaGenuine x₀ b.R b.H b.hHyp) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P
        (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁))
    (hdeg : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaGenuine x₀ b.R b.H b.hHyp) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  have hbridge : gammaLocal x₀ b.R b.H b.hHyp (BcoeffSigned b.H x₀ b.R)
      = gammaGenuine x₀ b.R b.H b.hHyp :=
    gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic x₀ b.R b.hHyp hmonic
  section5DataOffcentreFin_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    b (BcoeffSigned b.H x₀ b.R) matchingSet root Ppoly
    (by rw [hbridge]; exact hrep)
    hdegX mpPoint
    (hcardFin_of_graded_signed x₀ b.R b.H b.hHyp b.hD b.hH hmonic hd2 hdHD hD_Rx0 hR
      (gradedConcreteFin_of_disc hdisc hcover hbig))
    (fun v₀ v₁ hlin => hHensel v₀ v₁ (by rwa [hbridge] at hlin))
    (fun v₀ v₁ hlin => hdeg v₀ v₁ (by rwa [hbridge] at hlin))

end Capstone

end GenuineMonicCapstone

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GenuineMonicCapstone.betaRec_weight_le_graded_signed
#print axioms ArkLib.GenuineMonicCapstone.hcardFin_of_graded_signed
#print axioms ArkLib.GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic
