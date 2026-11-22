/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFrobeniusNorm
import ArkLib.Research.ProximityGap.Frontier.ModularResultantMultiplicity

/-! # Cyclotomic height of a product of two-error slice ratios

For a fixed pair of evaluation sites 1 and z^d, equal products of s
ratios give an integer polynomial whose cyclotomic norm has absolute
value at most 2^((2s+1)φ(n)). Equality at a primitive field root is
preserved by inversion of every site.
-/
set_option autoImplicit false
namespace ProximityGap.RatioProductNorm
open Polynomial Finset ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm
noncomputable section

/-- Factors clearing the common denominators for one tuple of sites. -/
def factors {s : ℕ} (a : Fin s → ℕ) (d : ℕ) : ℤ[X] :=
  ∏ i, (X^(a i) - X^d)

/-- The cross multiplication of the two tuple products. -/
def difference {s : ℕ} (a b : Fin s → ℕ) (d : ℕ) : ℤ[X] :=
  factors a 0 * factors b d - factors b 0 * factors a d

/-- The product for an ordered tuple, using Lean's total field division. -/
def profile {F : Type*} [Field F] {s : ℕ} (z : F) (d : ℕ) (a : Fin s → ℕ) :=
  ∏ i, (z^(a i)-1)/(z^(a i)-z^d)

theorem factors_eval {F : Type*} [Field F] {s : ℕ} (z : F) (d : ℕ) (a : Fin s → ℕ) :
    (factors a d).eval₂ (Int.castRingHom F) z = ∏ i, (z^(a i)-z^d) := by
  simp [factors, eval₂_finsetProd, eval₂_sub, eval₂_pow]

theorem profile_inverse {F : Type*} [Field F] {s : ℕ} {z : F} (nz : z ≠ 0)
    (d : ℕ) (a : Fin s → ℕ) : profile z⁻¹ d a = (z^d)^s * profile z d a := by
  have point (i : Fin s) : ((z⁻¹)^(a i)-1)/((z⁻¹)^(a i)-(z⁻¹)^d) =
      z^d*((z^(a i)-1)/(z^(a i)-z^d)) := by
    rw [inv_pow,inv_pow]
    by_cases same : z^(a i) = z^d
    · simp [same]
    have left := pow_ne_zero (a i) nz
    have right := pow_ne_zero d nz
    have den : (z^(a i))⁻¹-(z^d)⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_injective.ne same)
    field_simp [left,right,den,sub_ne_zero.mpr same]
    ring
  simp only [profile,point,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]

/-- A zero of the cleared polynomial is equivalent to equality of the two
profiles when each ratio has a nonzero denominator. -/
theorem difference_zero_iff {F : Type*} [Field F] {s : ℕ} (z : F) (d : ℕ) (a b : Fin s → ℕ)
    (ha : ∀ i, z^(a i) ≠ z^d) (hb : ∀ i, z^(b i) ≠ z^d) :
    (difference a b d).eval₂ (Int.castRingHom F) z=0 ↔ profile z d a=profile z d b := by
  have an : (∏ i, (z^(a i)-z^d)) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ha i)
  have bn : (∏ i, (z^(b i)-z^d)) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hb i)
  simp only [difference,eval₂_sub,eval₂_mul,factors_eval,pow_zero,sub_eq_zero,profile,prod_div_distrib]
  exact (div_eq_div_iff an bn).symm

private theorem factor_height {s : ℕ} {z : ℂ} (hz : ‖z‖=1) (d : ℕ) (a : Fin s → ℕ) :
    ‖valAt (factors a d) z‖ ≤ 2^s := by
  rw [valAt,factors_eval,norm_prod]
  calc
    _ ≤ ∏ _ : Fin s, (2:ℝ) := by
      apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      exact (norm_sub_le _ _).trans (by norm_num [norm_pow,hz])
    _ = _ := by simp

/-- Absolute height of the full cyclotomic norm. This uses the product over
all primitive conjugates and the triangle inequality on each monomial difference. -/
theorem norm_height {n s : ℕ} [NeZero n] (a b : Fin s → ℕ) (d : ℕ) :
    (cycloNorm n (difference a b d)).natAbs ≤ 2^((2*s+1)*n.totient) := by
  have height (z : primitiveRoots n ℂ) : ‖valAt (difference a b d) z‖ ≤ (2:ℝ)^(2*s+1) := by
    have hz := (isPrimitiveRoot_of_mem_primitiveRoots z.2).norm'_eq_one (NeZero.ne n)
    change ‖(difference a b d).eval₂ (Int.castRingHom ℂ) z‖ ≤ _
    rw [difference,eval₂_sub,eval₂_mul,eval₂_mul]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul]
    have h₁ := mul_le_mul (factor_height hz 0 a) (factor_height hz d b) (norm_nonneg _) (by positivity)
    have h₂ := mul_le_mul (factor_height hz 0 b) (factor_height hz d a) (norm_nonneg _) (by positivity)
    change _ ≤ 2^(2*s+1)
    rw [show 2*s+1=s+s+1 by omega,pow_succ,pow_add]
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  have realbound : |(cycloNorm n (difference a b d):ℝ)| ≤ (2:ℝ)^((2*s+1)*n.totient) := by
    rw [norm_eq_prod_abs]
    calc
      _ ≤ ∏ _ : primitiveRoots n ℂ, (2:ℝ)^(2*s+1) :=
        prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun z _ => height z)
      _ = _ := by simp [Complex.card_primitiveRoots, pow_mul]
  apply Int.ofNat_le.mp
  rw [Int.natCast_natAbs]
  exact_mod_cast realbound

/-- An equal pair of products in a split prime field vanishes on the
whole cyclotomic polynomial in characteristic zero under the stated height
test. Inversion supplies a second independent root modulo the prime. -/
theorem cyclotomic_dvd {p n s : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    (hn : 2<n) {z : ZMod p} (hz : IsPrimitiveRoot z n) (d : ℕ) (a b : Fin s → ℕ)
    (ha : ∀ i, z^(a i) ≠ z^d) (hb : ∀ i, z^(b i) ≠ z^d)
    (same : profile z d a = profile z d b) (large : 2^((2*s+1)*n.totient)<p^2) :
    cyclotomic n ℤ ∣ difference a b d := by
  have nz : z≠0 := by
    intro zero
    have impossible := hz.pow_eq_one
    simp [zero,NeZero.ne n] at impossible
  have distinct : z ≠ z⁻¹ := by
    intro equal
    apply hz.pow_ne_one_of_pos_of_lt (by decide : (2:ℕ)≠0) hn
    calc
      z^2 = z*z := pow_two _
      _ = z*z⁻¹ := congrArg (z * ·) equal
      _ = 1 := mul_inv_cancel₀ nz
  have φpos : 2 ≤ n.totient := by
    have positive := Nat.totient_pos.mpr (by omega : 0<n)
    by_contra! small
    rcases Nat.totient_eq_one_iff.mp (by omega : n.totient=1) with h | h <;> omega
  have rev : profile z⁻¹ d a = profile z⁻¹ d b := by
    rw [profile_inverse nz,profile_inverse nz,same]
  have div : (p:ℤ)^2 ∣ cycloNorm n (difference a b d) := by
    apply ModularResultantMultiplicity.two_roots _ _ le_rfl le_rfl
      (by rw [natDegree_cyclotomic];omega) distinct
    · rw [map_cyclotomic];exact hz.isRoot_cyclotomic (by omega)
    · rw [map_cyclotomic];exact hz.inv.isRoot_cyclotomic (by omega)
    · rw [eval_map];exact (difference_zero_iff z d a b ha hb).mpr same
    · rw [eval_map]
      apply (difference_zero_iff z⁻¹ d a b (fun i => ?_) (fun i => ?_)).mpr rev
      · simpa only [inv_pow,ne_eq,inv_inj] using ha i
      · simpa only [inv_pow,ne_eq,inv_inj] using hb i
  apply dvd_of_norm_zero
  by_contra nonzero
  have divides := Int.natAbs_dvd_natAbs.mpr div
  rw [Int.natAbs_pow,Int.natAbs_natCast] at divides
  exact (not_le_of_gt large) ((Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) divides).trans (norm_height a b d))

/-- Transfer a collision to any characteristic admitting the same primitive
roots. The target order and the exponent tuple can represent a Galois
conjugate of the original enumeration. -/
theorem transfer {p n s : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {F : Type*} [Field F] [NeZero (n : F)] (hn : 2<n)
    {z : ZMod p} {w : F} (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (d : ℕ) (a b : Fin s → ℕ)
    (ha : ∀ i, z^(a i) ≠ z^d) (hb : ∀ i, z^(b i) ≠ z^d)
    (ha' : ∀ i, w^(a i) ≠ w^d) (hb' : ∀ i, w^(b i) ≠ w^d)
    (same : profile z d a=profile z d b) (large : 2^((2*s+1)*n.totient)<p^2) :
    profile w d a = profile w d b :=
  (difference_zero_iff w d a b ha' hb').mp
    (eval_zero_of_cyclo_dvd hw (cyclotomic_dvd hn hz d a b ha hb same large))

/-- In order 128 the test for all triple products is met above 2²²⁴. -/
theorem height128 {p : ℕ} (hp : 2^224<p) : 2^((2*3+1)*Nat.totient 128)<p^2 := by
  rw [show Nat.totient 128=64 by decide,show (2:ℕ)^((2*3+1)*64)=(2^224)^2 by rw [← pow_mul]]
  exact Nat.pow_lt_pow_left hp (by decide)

end
end ProximityGap.RatioProductNorm
#print axioms ProximityGap.RatioProductNorm.profile_inverse
#print axioms ProximityGap.RatioProductNorm.norm_height
#print axioms ProximityGap.RatioProductNorm.transfer
