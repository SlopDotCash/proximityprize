/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4GeneralStratumRepCorrelation

/-!
# DQR-4: the adjoining twist is a quotient involution, not an equidistributed sample — #466

This file attacks the remaining point-versus-all-twists discrepancy in three directions.

1. **Orbit structure.**  The mixed stratum
   `T_{k,j}(a) = sum_{b != 0} eta_b^k eta_{ba}^j` is constant on the multiplicative
   coset `aG`, and inversion interchanges `k` and `j`.  At a dyadic adjoining step
   `a^2 in G`; hence `T_{k,j}(a) = T_{j,k}(a)`.  Thus the production point is the
   order-two class in `F^*/G`, not a generic point.  This cuts the fifteen ledger strata
   to eight, but gives no equidistribution with the all-twist mean.

2. **Mean/symmetry/CS falsifier.**  `spike` is a rational four-point discrepancy field with
   exact mean zero and inversion symmetry, whose inversion-fixed point carries `3/4` of all
   L2 mass.  Therefore an all-twist mean, inversion symmetry, and one-point Cauchy--Schwarz
   cannot by themselves yield a useful dilution at the adjoining point.  The companion probe
   `probe_dqr4_adjoining_twist_discrepancy.py` gives the scalable `m`-point version, where the
   mass fraction is `(m-1)/m -> 1`, and tests actual small finite fields.

3. **Telescoping.**  The product of exact per-level moment ratios is exactly the endpoint
   moment ratio.  Telescoping the signed ledger across levels consequently returns the original
   depth-seven endpoint problem; it creates no independent cancellation input.

The orbit identities are positive data.  The falsifier and telescope are an honesty result:
DQR-4 still needs field-specific control of the distinguished involution values. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification

namespace ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A finite multiplicatively closed set of nonzero field elements is inverse-closed. -/
theorem mulClosed_inv_mem {G : Finset F} (hG : MulClosed G) {u : F} (hu : u ∈ G) :
    u⁻¹ ∈ G := by
  have hu0 : u ≠ 0 := fun h => hG.zero_not_mem (h ▸ hu)
  have hperm := image_mul_self hG hu
  have hu_image : u ∈ G.image (fun z => u * z) := hperm.symm ▸ hu
  obtain ⟨x, hx, hux⟩ := Finset.mem_image.mp hu_image
  have hx1 : x = 1 := mul_left_cancel₀ hu0 (hux.trans (mul_one u).symm)
  have h1 : (1 : F) ∈ G := hx1 ▸ hx
  have h1_image : (1 : F) ∈ G.image (fun z => u * z) := hperm.symm ▸ h1
  obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp h1_image
  exact (eq_inv_of_mul_eq_one_right huv) ▸ hv

/-- The `(k,j)` multiplicative-twist cross moment on the nonzero additive spectrum. -/
noncomputable def crossMoment (psi : AddChar F ℂ) (G : Finset F)
    (k j : ℕ) (a : F) : ℂ :=
  ∑ b ∈ Finset.univ.erase (0 : F), (eta psi G b) ^ k * (eta psi G (b * a)) ^ j

/-- **Coset orbit law.**  The twist cross moment is constant on `aG`. -/
theorem crossMoment_mul_mem {G : Finset F} (hG : MulClosed G) (psi : AddChar F ℂ)
    (k j : ℕ) (a : F) {u : F} (hu : u ∈ G) :
    crossMoment psi G k j (a * u) = crossMoment psi G k j a := by
  unfold crossMoment
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [show b * (a * u) = (b * a) * u by ring, eta_mul_right hG psi (b * a) hu]

/-- **Inversion law.**  Inverting the twist exchanges the two moment depths. -/
theorem crossMoment_inv (psi : AddChar F ℂ) (G : Finset F) (k j : ℕ)
    {a : F} (ha : a ≠ 0) :
    crossMoment psi G k j a = crossMoment psi G j k a⁻¹ := by
  unfold crossMoment
  apply Finset.sum_nbij' (i := fun b => b * a) (j := fun c => c * a⁻¹)
  · intro b hb
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hb)
    simp [Finset.mem_erase, mul_ne_zero hb0 ha]
  · intro c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hc)
    simp [Finset.mem_erase, mul_ne_zero hc0 (inv_ne_zero ha)]
  · intro b _
    rw [mul_inv_cancel_right₀ ha]
  · intro c _
    rw [inv_mul_cancel_right₀ ha]
  · intro b _
    rw [mul_inv_cancel_right₀ ha]
    ring

/-- **Adjoining-involution symmetry.**  If `a^2 in G`, the production stratum is symmetric
in its two depths: `T_{k,j}(a) = T_{j,k}(a)`. -/
theorem crossMoment_eq_swap_of_sq_mem {G : Finset F} (hG : MulClosed G)
    (psi : AddChar F ℂ) (k j : ℕ) {a : F} (ha : a ≠ 0) (hsq : a ^ 2 ∈ G) :
    crossMoment psi G k j a = crossMoment psi G j k a := by
  have hu : (a ^ 2)⁻¹ ∈ G := mulClosed_inv_mem hG hsq
  have hau : a * (a ^ 2)⁻¹ = a⁻¹ := by
    field_simp
  calc
    crossMoment psi G k j a = crossMoment psi G j k a⁻¹ := crossMoment_inv psi G k j ha
    _ = crossMoment psi G j k (a * (a ^ 2)⁻¹) := by rw [hau]
    _ = crossMoment psi G j k a := crossMoment_mul_mem hG psi j k a hu

/-! ## Mean + involution symmetry do not control the distinguished point -/

/-- Inversion on a four-point quotient, written explicitly. -/
def inv4 : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- A centered inversion-symmetric discrepancy concentrated at the nontrivial fixed point. -/
def spike : Fin 4 → ℚ := ![-1, -1, 3, -1]

theorem inv4_involutive (i : Fin 4) : inv4 (inv4 i) = i := by
  fin_cases i <;> decide

theorem spike_inv4 (i : Fin 4) : spike (inv4 i) = spike i := by
  fin_cases i <;> decide

theorem spike_two : spike (2 : Fin 4) = 3 := by
  decide

theorem spike_sum_eq_zero : ∑ i, spike i = 0 := by
  norm_num [spike, Fin.sum_univ_succ]

/-- The inversion-fixed point carries exactly three quarters of the total squared discrepancy. -/
theorem spike_fixed_point_carries_three_quarters :
    4 * spike 2 ^ 2 = 3 * ∑ i, spike i ^ 2 := by
  rw [spike_two]
  norm_num [spike, Fin.sum_univ_succ]

/-- In particular, the fixed point is above the RMS scale despite exact mean zero and symmetry. -/
theorem spike_fixed_point_exceeds_mean_square :
    spike 2 ^ 2 > (∑ i, spike i ^ 2) / 4 := by
  rw [spike_two]
  norm_num [spike, Fin.sum_univ_succ]

/-! ## Level telescoping returns the endpoint moment -/

/-- Exact products of consecutive level ratios telescope to the endpoint ratio. -/
theorem stepRatios_telescope (moment : ℕ → ℝˣ) (levels : ℕ) :
    (∏ i ∈ Finset.range levels, moment (i + 1) / moment i) =
      moment levels / moment 0 := by
  exact Finset.prod_range_div moment levels

/-- Dividing every level ratio by a fixed scale only compares the endpoint ratio with the
scale to the number of levels.  Taking `scale = 2^7` is the DQR Gaussian target. -/
theorem normalizedStepRatios_telescope (moment : ℕ → ℝˣ) (scale : ℝˣ) (levels : ℕ) :
    (∏ i ∈ Finset.range levels, (moment (i + 1) / moment i) / scale) =
      (moment levels / moment 0) / scale ^ levels := by
  calc
    (∏ i ∈ Finset.range levels, (moment (i + 1) / moment i) / scale) =
        (∏ i ∈ Finset.range levels, moment (i + 1) / moment i) /
          (∏ _i ∈ Finset.range levels, scale) := Finset.prod_div_distrib _ _
    _ = (moment levels / moment 0) / scale ^ levels := by
      rw [stepRatios_telescope]
      simp

end ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy.crossMoment_mul_mem
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy.crossMoment_inv
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy.crossMoment_eq_swap_of_sq_mem
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy.spike_fixed_point_carries_three_quarters
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4AdjoiningTwistDiscrepancy.normalizedStepRatios_telescope
