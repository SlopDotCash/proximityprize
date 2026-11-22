/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AbelianDyadicRadical
import ArkLib.Research.ProximityGap.Frontier.DyadicOrbitIndependence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Multiplicative independence test for an orbit of square classes

In an elementary abelian two-group, an orbit indexed by a dyadic cycle has
no nontrivial binary product relation if the product of all its members is
nonidentity. The same test applies modulo any subgroup containing all squares.
-/

namespace ProximityGap.DyadicSquareOrbit

variable {G : Type*} [CommGroup G]

private def bit (x : G) (v : ZMod 2) : G := if v = 0 then 1 else x

private lemma bit_add (x : G) (hx : x^2 = 1) (a b : ZMod 2) :
    bit x (a+b) = bit x a * bit x b := by
  have cases₂ : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have ht : (1:ZMod 2)+1=0 := by decide
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;> simp [bit, ht, ← pow_two, hx]

/-- An orbit of dyadic length in an elementary abelian two-group is
multiplicatively independent over the binary field exactly when its total
product is nonidentity. Translations of the indices act by endomorphisms. -/
theorem no_binary_product (k : ℕ) (U : ZMod (2^k) → G) (hsq : ∀ i, U i ^ 2 = 1)
    (horb : ∀ a : ZMod (2^k), ∃ f : G →* G, ∀ i, f (U i) = U (i+a))
    (ht : ∏ i, U i ≠ 1) (v : ZMod (2^k) → ZMod 2)
    (hv : (∏ i, if v i = 0 then 1 else U i) = 1) : v = 0 := by
  classical
  let R : Set (ZMod (2^k) → ZMod 2) := {w | (∏ i, bit (U i) (w i)) = 1}
  have hadd : ∀ u ∈ R, ∀ w ∈ R, u+w ∈ R := by
    intro u hu w hw
    change (∏ i, bit (U i) (u i + w i)) = 1
    simp only [bit_add _ (hsq _), Finset.prod_mul_distrib]
    change (∏ i, bit (U i) (u i)) = 1 at hu
    change (∏ i, bit (U i) (w i)) = 1 at hw
    rw [hu,hw,one_mul]
  have hs : ∀ w ∈ R, ∀ a, (fun i ↦ w (i+a)) ∈ R := by
    intro w hw a
    obtain ⟨f,hf⟩ := horb (-a)
    change (∏ i, bit (U i) (w i)) = 1 at hw
    have hw' := congrArg f hw
    rw [map_prod, map_one] at hw'
    change (∏ i, bit (U i) (w (i+a))) = 1
    rw [← hw']
    refine Fintype.prod_equiv (Equiv.addRight a) _ _ (fun i ↦ ?_)
    change bit (U i) (w (i+a)) = f (bit (U (i+a)) (w (i+a)))
    by_cases hbit : w (i+a) = 0 <;> simp [bit, hbit, hf]
  by_contra hn
  have h := DyadicOrbitIndependence.one_mem_of_nonzero k R hs hadd ⟨v,hv,hn⟩
  change (∏ i, bit (U i) 1) = 1 at h
  exact ht (by simpa [bit] using h)

/-- In an ordered field this subgroup consists of squares up to sign.
Its definition also applies to arbitrary commutative groups. -/
def squareUpToSign (G : Type*) [CommGroup G] : Subgroup G where
  carrier := {x | ∃ y : G, x^2 = y^4}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨y,hy⟩ ⟨z,hz⟩
    exact ⟨y*z, by rw [mul_pow,hy,hz,mul_pow]⟩
  inv_mem' := by
    rintro a ⟨y,hy⟩
    exact ⟨y⁻¹, by rw [inv_pow,hy,inv_pow]⟩

/-- If the total orbit product squared is not a fourth power, every binary
product which is a square up to sign is the empty product. The translating
endomorphisms may agree with the prescribed orbit only after squaring. -/
theorem no_signed_square_relation (k : ℕ) (U : ZMod (2^k) → G)
    (horb : ∀ a : ZMod (2^k), ∃ f : G →* G, ∀ i, f (U i)^2 = U (i+a)^2)
    (ht : ∀ y : G, (∏ i, U i)^2 ≠ y^4)
    (v : ZMod (2^k) → ZMod 2)
    (hv : ∃ y : G, (∏ i, if v i = 0 then 1 else U i)^2 = y^4) : v = 0 := by
  classical
  let S := squareUpToSign G
  let π := QuotientGroup.mk' S
  let V (i : ZMod (2^k)) := π (U i)
  have sq (i) : V i ^ 2 = 1 := by
    change π (U i) ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨U i, by group⟩
  have act (a : ZMod (2^k)) : ∃ f : G ⧸ S →* G ⧸ S, ∀ i, f (V i) = V (i+a) := by
    obtain ⟨f,hf⟩ := horb a
    have incl : S ≤ S.comap f := by
      rintro u ⟨y,hy⟩
      exact ⟨f y, by simpa only [map_pow] using congrArg f hy⟩
    refine ⟨QuotientGroup.map S S f incl,fun i ↦ ?_⟩
    change ((f (U i) : G) : G ⧸ S) = (U (i+a) : G ⧸ S)
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact ⟨1,by rw [div_pow,hf,div_self',one_pow]⟩
  refine no_binary_product k V sq act ?_ v ?_
  · change (∏ i, π (U i)) ≠ 1
    rw [← map_prod]
    intro h
    obtain ⟨y,hy⟩ := (QuotientGroup.eq_one_iff (∏ i, U i)).mp h
    exact ht y hy
  · have hx : π (∏ i, if v i = 0 then 1 else U i) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hv
    rw [map_prod] at hx
    simpa only [apply_ite, map_one] using hx

/-- Integer relations up to sign vanish when fourth roots of unity already
have square one, as in the multiplicative group of a real field. -/
theorem no_signed_integer_relation (k : ℕ) (U : ZMod (2^k) → G)
    (horb : ∀ a : ZMod (2^k), ∃ f : G →* G, ∀ i, f (U i)^2 = U (i+a)^2)
    (ht : ∀ y : G, (∏ i, U i)^2 ≠ y^4) (hr : ∀ y : G, y^4 = 1 → y^2 = 1)
    (e : ZMod (2^k) → ℤ) (he : (∏ i, U i ^ e i)^2 = 1) : e = 0 := by
  classical
  suffices H : ∀ B : ℕ, ∀ d : ZMod (2^k) → ℤ, (∀ i, (d i).natAbs ≤ B) →
      (∏ i, U i ^ d i)^2 = 1 → d = 0 by
    exact H (∑ i, (e i).natAbs) e (fun i ↦ Finset.single_le_sum
      (fun j _ ↦ Nat.zero_le (e j).natAbs) (Finset.mem_univ i)) he
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    intro d hb hd
    by_cases hzero : B = 0
    · exact funext fun i ↦ Int.natAbs_eq_zero.mp (by have := hb i; omega)
    let q (i) := d i / 2
    let v (i) : ZMod 2 := if d i % 2 = 0 then 0 else 1
    let P := ∏ i, U i ^ q i
    let V := ∏ i, if v i = 0 then 1 else U i
    have decomp (i) : U i ^ d i = (U i ^ q i)^2 * (if v i = 0 then 1 else U i) := by
      by_cases hi : d i % 2 = 0
      · have hi' : d i = q i * 2 := by dsimp [q]; omega
        have hbit : v i = 0 := if_pos hi
        simp only [hbit,if_true,mul_one]
        conv_lhs => rw [hi',zpow_mul]
        norm_cast
      · have hi' : d i = q i * 2+1 := by dsimp [q]; omega
        have hbit : v i ≠ 0 := by change (if d i % 2 = 0 then (0:ZMod 2) else 1) ≠ 0; simp [hi]
        simp only [hbit,if_false]
        conv_lhs => rw [hi',zpow_add,zpow_mul,zpow_one]
        norm_cast
    have fac : (∏ i, U i ^ d i) = P^2*V := by
      dsimp only [P,V]
      simp_rw [decomp, Finset.prod_mul_distrib, ← Finset.prod_pow]
    have hpv : P^4*V^2 = 1 := by simpa only [fac,mul_pow,← pow_mul] using hd
    have hv := no_signed_square_relation k U horb ht v ⟨P⁻¹,by
      change V^2 = (P⁻¹)^4
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_right (mul_comm (V^2) (P^4) ▸ hpv)⟩
    have ev (i) : d i = 2*q i := by
      have hh := congrFun hv i
      by_cases hi : d i % 2 = 0
      · dsimp [q]; omega
      · simp [v,hi] at hh
    have hv1 : V = 1 := by simp [V,hv]
    have hp : P^2 = 1 := hr P (by simpa [hv1] using hpv)
    have hq := ih (B/2) (by omega) q (fun i ↦ by
      have hh := hb i
      rw [ev i, Int.natAbs_mul] at hh
      change 2 * (q i).natAbs ≤ B at hh
      omega) hp
    exact funext fun i ↦ by rw [ev i, congrFun hq i]; simp

/-- In an ordered abelian Galois extension of the rationals, a dyadic
orbit up to sign whose squared total product is two has no signed integer
product relation. This applies to real representatives of the cyclotomic chords. -/
theorem real_abelian_orbit_independent {E : Type*} [Field E] [LinearOrder E]
    [IsStrictOrderedRing E] [Algebra ℚ E] [IsAbelianGalois ℚ E]
    (k : ℕ) (U : ZMod (2^k) → Eˣ)
    (horb : ∀ a : ZMod (2^k), ∃ f : E ≃ₐ[ℚ] E, ∀ i,
      f (U i : E)^2 = (U (i+a) : E)^2)
    (ht : (∏ i, (U i : E))^2 = 2)
    (e : ZMod (2^k) → ℤ) (he : (∏ i, (U i : E) ^ e i)^2 = 1) : e = 0 := by
  apply no_signed_integer_relation k U _ _ _ e
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      Units.val_one] using he
  · intro a
    obtain ⟨f,hf⟩ := horb a
    exact ⟨Units.map f.toRingEquiv.toMonoidHom, fun i ↦ Units.ext (hf i)⟩
  · intro y hy
    have h : (∏ i, (U i : E))^2 = (y:E)^4 := by
      simpa only [Units.val_pow_eq_pow_val, Units.coe_prod] using congrArg Units.val hy
    exact AbelianDyadicRadical.fourth_power_ne_two (y:E) (h.symm.trans ht)
  · intro y hy
    apply Units.ext
    have h : ((y:E)^2)^2 = 1 := by
      simpa only [← pow_mul, Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hy
    change (y:E)^2 = 1
    exact (sq_eq_sq₀ (sq_nonneg _) zero_le_one).mp (by simpa only [one_pow] using h)

#print axioms real_abelian_orbit_independent
#print axioms no_signed_integer_relation
#print axioms no_signed_square_relation
#print axioms no_binary_product

end ProximityGap.DyadicSquareOrbit
