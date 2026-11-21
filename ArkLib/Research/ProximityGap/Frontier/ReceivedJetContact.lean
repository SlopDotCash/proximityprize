/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.TruncatedJetMultipliers
import ArkLib.Research.ProximityGap.Frontier.PolynomialLocalOrder
import ArkLib.Research.ProximityGap.Frontier.TameResultantOrders

/-! # A translated interpolation leader forces contact along a generic line

The jet lower-degree vanishing property suffices for the direction of the
multiplicity comparison used in the cubic incidence estimate.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.ReceivedJetContact

variable {K : Type} [Field K]

/-- If the terms below total degree r vanish, every affine direction
through the center produces a polynomial divisible by X^r. -/
theorem direction_dvd (H : K[X][X]) (r : ℕ)
    (h : ∀ i j, i+j<r → (H.coeff i).coeff j=0) (c : K) :
    (Polynomial.X : K[X])^r ∣ H.eval (C c*Polynomial.X) := by
  rw [eval_eq_sum, Polynomial.sum]
  apply Finset.dvd_sum
  intro i _
  rw [mul_pow]
  by_cases hi : r ≤ i
  · exact (pow_dvd_pow _ hi).trans (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
  · have hdiv : (Polynomial.X : K[X])^(r-i) ∣ H.coeff i := by
      rw [Polynomial.X_pow_dvd_iff]
      exact fun k hk => h i k (by omega)
    obtain ⟨w,hw⟩ := hdiv
    refine ⟨w*(C c)^i, ?_⟩
    rw [hw]
    conv_rhs => lhs; rw [← Nat.sub_add_cancel (show i ≤ r by omega), pow_add]
    ring

/-- Plane polynomial translated in the coordinate X and the received value Y. -/
def shifted (F : K[X][X]) (α l : K) : K[X][X] :=
  (F.map (Polynomial.taylorAlgHom α).toRingHom).taylor (C l)

/-- The literal Taylor leader bounds the series evaluation of the original
polynomial on every finite line of that slope. -/
theorem leader_order (F : K[X][X]) (α l c : K) (r j : ℕ)
    (hr : TruncatedJetMultipliers.Leader (shifted F α l) r j) :
    (r : ℕ∞) ≤ ((F.map (PolynomialLocalOrder.atPoint α)).eval
      (PowerSeries.C l+c • PowerSeries.X)).order := by
  let φ := Polynomial.coeToPowerSeries.ringHom (R := K)
  have hd := direction_dvd (shifted F α l) r (fun i k hik => hr.lower i k (Or.inl hik)) c
  obtain ⟨w,hw⟩ := hd
  have heq : φ ((shifted F α l).eval (C c*Polynomial.X)) =
      (F.map (PolynomialLocalOrder.atPoint α)).eval (PowerSeries.C l+c • PowerSeries.X) := by
    dsimp [shifted]
    rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, Polynomial.map_map]
    congr 1
    change ((C c*Polynomial.X+C l : K[X]) : K⟦X⟧) = _
    simp [PowerSeries.smul_eq_C_mul, add_comm]
  rw [← heq, hw, map_mul, map_pow]
  rw [show φ Polynomial.X = PowerSeries.X from Polynomial.coe_X]
  rw [PowerSeries.order_mul, PowerSeries.order_X_pow]
  exact le_self_add

/-- Direct contact charge from an interpolation leader and a given
projective sheet factorization, including all sheets over infinity. -/
theorem leader_le_projective_contacts [Infinite K] {ι : Type} [Fintype ι]
    (F : K[X][X]) (α l : K) (r j : ℕ) (hr : TruncatedJetMultipliers.Leader (shifted F α l) r j)
    {n : ℕ} (hn : n ≠ 0) (a b : ι → K⟦X⟧)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, IsCoprime (b i) (a i)) (u : K⟦X⟧) (hu : IsUnit u)
    (hF : (F.map (PolynomialLocalOrder.atPoint α)).map (PowerSeries.expand n hn (R := K)).toRingHom =
      C u*∏ i, (C (a i)*Polynomial.X-C (b i))) :
    n • (r : ℕ∞) ≤ ∑ i, min (PowerSeries.C l*a i-b i).order (n : ℕ∞) := by
  obtain ⟨c,hc⟩ := TameResultantOrders.generic_projective_line_contact
    (F.map (PolynomialLocalOrder.atPoint α)) hn a b ha hab u hu hF (PowerSeries.C l)
  rw [PowerSeries.expand_C] at hc
  rw [← hc]
  exact nsmul_le_nsmul_right (leader_order F α l c r j hr) n

#print axioms direction_dvd
#print axioms leader_order
#print axioms leader_le_projective_contacts

end ArkLib.ProximityGap.Frontier.ReceivedJetContact
