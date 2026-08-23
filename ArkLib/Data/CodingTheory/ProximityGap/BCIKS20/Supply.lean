/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Weld
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality
import ArkLib.ToMathlib.GenuineTruncationFin

/-!
# Claim 5.10 supply — the kill-target weight bound and the automatic monic pinning (#302)

Discharges two of the four inputs of the hlin weld (`Claim510Weld`):

* **The weight bound** (`weight_killTarget_le`): `Λ_𝒪(killTarget n e a b) ≤ killBudget`,
  an explicit ℕ-budget, from the in-tree graded `βHensel` bound
  (`GenuineTruncationFin.weight_βHensel_le_graded`, PROVEN for monic `H` with the GS graded
  side conditions) and a `ξ`-weight bound (producer:
  `BCoeffVanishing.xi_weight_le_of_coeff_bounds`), via the `Λ_𝒪` calculus.

* **The automatic pinning** (`betaHensel_eq_aPre_mul_xi_pow` / `pi_z_pinning_of_monic`):
  for monic `H`, `ξ` is a unit of `𝒪` (`P1MonicIntegrality.isUnit_ξ_of_monic`), so
  `βHensel t = aPre t · ξ^{2t−1}` holds **in `𝒪`** with
  `aPre t := βHensel t · (ξ⁻¹)^{2t−1}` — every place `π_z` then satisfies the weld's `hpin`
  with `c t := π_z (aPre t)` **by construction**.  The deep per-place content of the weld
  thus reduces to the **agreement** `∑_t π_z (aPre t)·e^t = u₀ + z·u₁` alone (the per-place
  Hensel-uniqueness reading of the decoded lane).

## Main results

* `weight_oScalar_le`, `weight_groundAffine_le` — scalar/ground-affine weights.
* `killBudget` + `weight_killTarget_le` — the explicit weight bound for the weld's
  `hweight` input.
* `aPre` + `betaHensel_eq_aPre_mul_xi_pow` + `pi_z_pinning_of_monic` — the automatic
  pinning for the weld's `hpin` input (monic `H`).

## References

* [BCIKS20] ePrint 2020/654 — §5.2.6–5.2.7, Appendix A.
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.Claim59Lagrange
open BCIKS20.Claim510Kill

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Supply

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `Λ_𝒪(oScalar a) ≤ 0`: scalars carry no weight. -/
theorem weight_oScalar_le (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (a : F) :
    weight_Λ_over_𝒪 hH (oScalar H a) D ≤ (WithBot.some 0 : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hDH hH
    (r := Polynomial.C (Polynomial.C a)) rfl).trans ?_
  rw [weight_Λ_le_iff]
  intro n hn
  have hcoeff := Polynomial.mem_support_iff.mp hn
  rw [Polynomial.coeff_C] at hcoeff
  split_ifs at hcoeff with h0
  · subst h0
    simp
  · exact absurd rfl hcoeff

/-- `Λ_𝒪(groundAffine a b) ≤ 1`: ground-affine elements have weight at most `1`. -/
theorem weight_groundAffine_le (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (a b : F) :
    weight_Λ_over_𝒪 hH (groundAffine H a b) D ≤ (WithBot.some 1 : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_le_of_mk_eq hDH hH
    (r := Polynomial.C (Polynomial.C a + Polynomial.X * Polynomial.C b)) rfl).trans ?_
  rw [weight_Λ_le_iff]
  intro n hn
  have hcoeff := Polynomial.mem_support_iff.mp hn
  rw [Polynomial.coeff_C] at hcoeff
  split_ifs at hcoeff with h0
  · subst h0
    simp only [Nat.zero_mul, Polynomial.coeff_C, zero_add]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · simp
    · refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp
  · exact absurd rfl hcoeff

variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

/-- The explicit ℕ-budget for the kill target: the graded `βHensel` bound at top order,
plus the `ξ`-power and ground contributions. -/
def killBudget (n D dH dR xw : ℕ) : ℕ :=
  (dR * (D - dH + 1) + D + (D - dH + 1)) * (2 * n) + (D - dH + 1) + 2 * n * xw + 1

/-- **The kill-target weight bound** (the weld's `hweight` input): under the graded GS side
conditions (the in-tree `weight_βHensel_le_graded` surface) and a `ξ`-weight bound `xw`,
`Λ_𝒪(killTarget n e a b) ≤ killBudget n D d_H d_R xw`. -/
theorem weight_killTarget_le
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (n : ℕ) (e a b : F) :
    weight_Λ_over_𝒪 hH (killTarget H x₀ R hHyp n e a b) D
      ≤ (WithBot.some
          (killBudget n D H.natDegree (Bivariate.natDegreeY R) xw) : WithBot ℕ) := by
  set B : ℕ := killBudget n D H.natDegree (Bivariate.natDegreeY R) xw with hB
  -- per-term bound for the cleared sum
  have hterm : ∀ t ∈ Finset.range n,
      weight_Λ_over_𝒪 hH
        (βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))
          * oScalar H (e ^ t)) D ≤ (WithBot.some B : WithBot ℕ) := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 : weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
        ≤ (WithBot.some
            ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
                * (2 * t - 1)
              + (D - H.natDegree + 1)) : WithBot ℕ) :=
      ArkLib.GenuineTruncationFin.weight_βHensel_le_graded H hHyp hD hH hmonic hd2
        hdHD hD_Rx0 hR t
    have h2 : weight_Λ_over_𝒪 hH
        ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))) D
        ≤ (WithBot.some ((2 * n - (2 * t - 1)) * xw) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans
        (nsmul_withBot_le _ _ hξw)
    have h3 := weight_oScalar_le H hH hD (e ^ t)
    have hmul1 := weight_Λ_over_𝒪_mul_le H hH hD
      (βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1)))
      (oScalar H (e ^ t))
    have hmul2 := weight_Λ_over_𝒪_mul_le H hH hD
      (βHensel H x₀ R hHyp t) ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1)))
    refine hmul1.trans ?_
    have hsum1 : weight_Λ_over_𝒪 hH
          (βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n - (2 * t - 1))) D
          + weight_Λ_over_𝒪 hH (oScalar H (e ^ t)) D
        ≤ (WithBot.some
            (((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
                  * (2 * t - 1) + (D - H.natDegree + 1))
              + (2 * n - (2 * t - 1)) * xw) + WithBot.some 0 : WithBot ℕ) := by
      refine add_le_add ?_ h3
      refine hmul2.trans ?_
      refine le_trans (add_le_add h1 h2) ?_
      rw [← WithBot.coe_add]
    refine hsum1.trans ?_
    have harith :
        (((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1) + (D - H.natDegree + 1))
          + (2 * n - (2 * t - 1)) * xw) + 0 ≤ B := by
      rw [hB, killBudget]
      have e1 : (Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
            * (2 * t - 1)
          ≤ (Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
            * (2 * n) :=
        Nat.mul_le_mul_left _ (by omega)
      have e2 : (2 * n - (2 * t - 1)) * xw ≤ 2 * n * xw :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rw [← WithBot.coe_add]
    exact_mod_cast harith
  -- the cleared-sum bound
  have hsum : weight_Λ_over_𝒪 hH (clearedSum H x₀ R hHyp n e) D
      ≤ (WithBot.some B : WithBot ℕ) := by
    rw [clearedSum]
    refine (weight_Λ_over_𝒪_sum_le H hH hD _ _).trans ?_
    exact Finset.sup_le hterm
  -- the ground-affine·ξ^{2n} bound
  have hground : weight_Λ_over_𝒪 hH
      (groundAffine H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)) D
      ≤ (WithBot.some B : WithBot ℕ) := by
    refine (weight_Λ_over_𝒪_mul_le H hH hD _ _).trans ?_
    have h1 := weight_groundAffine_le H hH hD a b
    have h2 : weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)) D
        ≤ (WithBot.some (2 * n * xw) : WithBot ℕ) :=
      (weight_Λ_over_𝒪_pow_le H hH hD _ _).trans (nsmul_withBot_le _ _ hξw)
    calc weight_Λ_over_𝒪 hH (groundAffine H a b) D
          + weight_Λ_over_𝒪 hH ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * n)) D
        ≤ (WithBot.some 1 + WithBot.some (2 * n * xw) : WithBot ℕ) := add_le_add h1 h2
      _ = (WithBot.some (1 + 2 * n * xw) : WithBot ℕ) := by rw [← WithBot.coe_add]
      _ ≤ (WithBot.some B : WithBot ℕ) := by
          rw [hB, killBudget]
          exact_mod_cast by omega
  -- assemble: `killTarget = clearedSum − ground·ξ^{2n}`
  rw [killTarget, sub_eq_add_neg]
  refine (weight_Λ_over_𝒪_add_le H hH hD _ _).trans ?_
  refine max_le hsum ?_
  exact (weight_Λ_over_𝒪_neg H hH hD _).trans hground

/-! ## The automatic pinning (monic `H`) -/

/-- The `𝒪`-preimage of the genuine coefficient: `aPre t := βHensel t · (ξ⁻¹)^{2t−1}`,
using that `ξ` is a unit for monic `H`. -/
noncomputable def aPre (hlc : H.leadingCoeff = 1) (t : ℕ) : 𝒪 H :=
  βHensel H x₀ R hHyp t
    * (((isUnit_ξ_of_monic H x₀ R hHyp hlc).unit⁻¹ : (𝒪 H)ˣ) : 𝒪 H) ^ (2 * t - 1)

/-- **The `𝒪`-level lift identity** (monic): `βHensel t = aPre t · ξ^{2t−1}` in `𝒪 H`. -/
theorem betaHensel_eq_aPre_mul_xi_pow (hlc : H.leadingCoeff = 1) (t : ℕ) :
    βHensel H x₀ R hHyp t
      = aPre H x₀ R hHyp hlc t * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  have hu : (((isUnit_ξ_of_monic H x₀ R hHyp hlc).unit⁻¹ : (𝒪 H)ˣ) : 𝒪 H)
      * ClaimA2.ξ x₀ R H hHyp = 1 := by
    have h := (isUnit_ξ_of_monic H x₀ R hHyp hlc).unit.inv_mul
    rwa [IsUnit.unit_spec] at h
  rw [aPre, mul_assoc,
    ← mul_pow (((isUnit_ξ_of_monic H x₀ R hHyp hlc).unit⁻¹ : (𝒪 H)ˣ) : 𝒪 H)
      (ClaimA2.ξ x₀ R H hHyp) (2 * t - 1),
    hu, one_pow, mul_one]

/-- **The automatic pinning** (the weld's `hpin`, pinning conjunct): at EVERY place, the
weld's per-place pinning holds with `c t := π_z (aPre t)` — by applying the ring hom `π_z`
to the `𝒪`-level identity.  No per-place hypothesis needed. -/
theorem pi_z_pinning_of_monic (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z) (t : ℕ) :
    π_z z root (βHensel H x₀ R hHyp t)
      = π_z z root (aPre H x₀ R hHyp hlc t)
          * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  conv_lhs => rw [betaHensel_eq_aPre_mul_xi_pow H x₀ R hHyp hlc t]
  rw [map_mul, map_pow]

/-- **The agreement-only hlin weld** (monic): with the pinning automatic, `H.natDegree = 1`
follows from the coefficient tail, the per-place **agreement alone**
(`∑_t π_z (aPre t)·e^t = u₀ + z·u₁` at each matching place), the weight bound, and the
heavy cardinality. -/
theorem natDegree_eq_one_of_heavy_agreement [Fintype F] (hlc : H.leadingCoeff = 1)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (hagree : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (aPre H x₀ R hHyp hlc t) * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  classical
  refine natDegree_eq_one_of_vandermonde_values H hHyp htail e he u₀ u₁ fun j => ?_
  refine coeff_sum_eq_ground_of_large_fin H x₀ R hHyp hlc
    (fun t _ => Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t)
    (e j) (u₀ j) (u₁ j) hD ?_
  refine Claim510Weld.largeness_of_card H x₀ R hHyp (e j) (u₀ j) (u₁ j) (matchingSet j)
    (fun z hz => ?_) (hweight j) (hcard j)
  obtain ⟨root, hroot⟩ := hagree j z hz
  exact mem_S_β_killTarget_of_pin_agree H x₀ R hHyp (e j) (u₀ j) (u₁ j) z root
    (fun t => π_z z root (aPre H x₀ R hHyp hlc t))
    (fun t _ => pi_z_pinning_of_monic H x₀ R hHyp hlc z root t) hroot

/-- **hlin, agreement-only contradiction form** (monic): no `Y`-degree ≥ 2 branch admits
the heavy agreement data. -/
theorem false_of_heavy_agreement_of_two_le [Fintype F] (hlc : H.leadingCoeff = 1)
    (hdeg : 2 ≤ H.natDegree)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F)
    (hagree : ∀ j, ∀ z ∈ matchingSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (aPre H x₀ R hHyp hlc t) * (e j) ^ t) = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card) :
    False := by
  have h1 := natDegree_eq_one_of_heavy_agreement H x₀ R hHyp hlc htail e he u₀ u₁ hD
    matchingSet hagree hweight hcard
  omega

end BCIKS20.Claim510Supply

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Supply.weight_oScalar_le
#print axioms BCIKS20.Claim510Supply.weight_groundAffine_le
#print axioms BCIKS20.Claim510Supply.weight_killTarget_le
#print axioms BCIKS20.Claim510Supply.betaHensel_eq_aPre_mul_xi_pow
#print axioms BCIKS20.Claim510Supply.pi_z_pinning_of_monic
#print axioms BCIKS20.Claim510Supply.natDegree_eq_one_of_heavy_agreement
#print axioms BCIKS20.Claim510Supply.false_of_heavy_agreement_of_two_le
