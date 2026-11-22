/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RatioProductNorm

/-! # A twelve-term norm bound for collisions of pairs

Three pairs of sites determine three rows with entries one, the sum of the
sites and their product. The determinant vanishes when one involution
exchanges all three pairs. Each of the three terms in the cyclic expansion
has complex absolute value at most four on the unit circle.
-/
set_option autoImplicit false
namespace ProximityGap.CyclotomicPairDeterminant
open Polynomial Finset RatioProductNorm ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm
noncomputable section

private def form {R : Type*} [CommRing R] (u v a b c d : R) : R :=
  (a+b)*(u*v-c*d) + (c+d)*(a*b-u*v) + (u+v)*(c*d-a*b)

/-- Determinant after dividing the cleared pair collision by the separation
of the two distinguished sites. -/
def determinant (d : ℕ) (a b : Fin 2 → ℕ) : ℤ[X] :=
  form 1 (X^d) (X^(a 0)) (X^(a 1)) (X^(b 0)) (X^(b 1))

theorem factor (d : ℕ) (a b : Fin 2 → ℕ) :
    difference a b d = (1-X^d)*determinant d a b := by
  simp only [difference,factors,Fin.prod_univ_two,pow_zero,determinant,form]
  ring

private theorem height {z : ℂ} (hz : ‖z‖=1) (d : ℕ) (a b : Fin 2 → ℕ) :
    ‖valAt (determinant d a b) z‖ ≤ 12 := by
  let v := z^d
  let x := z^(a 0)
  let y := z^(a 1)
  let t := z^(b 0)
  let u := z^(b 1)
  have bounds (r s t u v w : ℂ) (hr : ‖r‖=1) (hs : ‖s‖=1) (ht : ‖t‖=1)
      (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : ‖w‖=1) : ‖(r+s)*(t*u-v*w)‖ ≤ 4 := by
    rw [norm_mul]
    apply (mul_le_mul (norm_add_le r s) (norm_sub_le _ _) (norm_nonneg _) (by positivity)).trans
    norm_num [norm_mul,hr,hs,ht,hu,hv,hw]
  change ‖(determinant d a b).eval₂ (Int.castRingHom ℂ) z‖ ≤ _
  simp only [determinant,form,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_one]
  change ‖(x+y)*(1*v-t*u)+(t+u)*(x*y-1*v)+(1+v)*(t*u-x*y)‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have h₁ := bounds x y 1 v t u
  have h₂ := bounds t u x y 1 v
  have h₃ := bounds 1 v t u x y
  simp [x,y,t,u,v,norm_pow,hz] at h₁ h₂ h₃ ⊢
  linarith

/-- Bound on the absolute norm over all primitive conjugates, valid at every order. -/
theorem norm_height {n : ℕ} [NeZero n] (d : ℕ) (a b : Fin 2 → ℕ) :
    (cycloNorm n (determinant d a b)).natAbs ≤ 12^n.totient := by
  have realbound : |(cycloNorm n (determinant d a b):ℝ)| ≤ (12:ℝ)^n.totient := by
    rw [norm_eq_prod_abs]
    calc
      _ ≤ ∏ _ : primitiveRoots n ℂ, (12:ℝ) := by
        apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro z _
        exact height ((isPrimitiveRoot_of_mem_primitiveRoots z.2).norm'_eq_one (NeZero.ne n)) d a b
      _ = _ := by simp [Complex.card_primitiveRoots]
  apply Int.ofNat_le.mp
  rw [Int.natCast_natAbs]
  exact_mod_cast realbound

private theorem zero_iff {F : Type*} [Field F] {z : F} {d : ℕ} (hd : z^d ≠ 1)
    (a b : Fin 2 → ℕ) (ha : ∀ i, z^(a i) ≠ z^d) (hb : ∀ i, z^(b i) ≠ z^d) :
    (determinant d a b).eval₂ (Int.castRingHom F) z=0 ↔ profile z d a=profile z d b := by
  rw [← difference_zero_iff z d a b ha hb, factor]
  simp [eval₂_mul,eval₂_sub,eval₂_pow,sub_ne_zero.mpr (Ne.symm hd)]

/-- Transfer all equalities of pair products at distinctly separated sites. -/
theorem transfer {p n : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {F : Type*} [Field F] [NeZero (n : F)] (hn : 2<n) {z : ZMod p} {w : F}
    (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n) (d : ℕ) (hd : ¬ n ∣ d)
    (a b : Fin 2 → ℕ) (ha : ∀ i, z^(a i) ≠ z^d) (hb : ∀ i, z^(b i) ≠ z^d)
    (ha' : ∀ i, w^(a i) ≠ w^d) (hb' : ∀ i, w^(b i) ≠ w^d)
    (same : profile z d a=profile z d b) (large : 12^n.totient<p^2) :
    profile w d a=profile w d b := by
  have z₀ : z ≠ 0 := by intro eq; simpa [eq,NeZero.ne n] using hz.pow_eq_one
  apply (zero_iff (fun h => hd (hw.dvd_of_pow_eq_one d h)) a b ha' hb').mp
  apply eval_zero_of_cyclo_dvd hw
  apply dvd_of_reciprocal_roots hn hz _
    ((zero_iff (fun h => hd (hz.dvd_of_pow_eq_one d h)) a b ha hb).mpr same) _
    ((norm_height d a b).trans_lt large)
  apply (zero_iff (fun h => hd (hz.inv.dvd_of_pow_eq_one d h)) a b _ _).mpr
  · rw [profile_inverse z₀,profile_inverse z₀,same]
  · intro i; simpa only [inv_pow,ne_eq,inv_inj] using ha i
  · intro i; simpa only [inv_pow,ne_eq,inv_inj] using hb i

/-- Every prize-size prime meets the pair transfer test in order 128. -/
theorem height128 {p : ℕ} (hp : 2^128 ≤ p) : 12^(Nat.totient 128)<p^2 :=
  lt_of_lt_of_le (by decide : 12^(Nat.totient 128) < (2^128)^2) (Nat.pow_le_pow_left hp 2)

end
end ProximityGap.CyclotomicPairDeterminant
#print axioms ProximityGap.CyclotomicPairDeterminant.norm_height
#print axioms ProximityGap.CyclotomicPairDeterminant.transfer
