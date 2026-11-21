/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# The unramified Frobenius norm gap at seven

The integer cyclotomic resultant is the product of polynomial values on primitive roots.
The auxiliary polynomial is divisible coefficientwise by seven. Its archimedean norm
then bounds the original resultant from below whenever the auxiliary resultant is nonzero.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

open Polynomial Finset
open scoped ComplexConjugate

noncomputable section

def cycloNorm (n : ℕ) (f : ℤ[X]) : ℤ := resultant (cyclotomic n ℤ) f

def valAt (f : ℤ[X]) (z : ℂ) : ℂ := f.eval₂ (Int.castRingHom ℂ) z

theorem cycloNorm_eq_prod (n : ℕ) [NeZero n] (f : ℤ[X]) :
    (cycloNorm n f : ℂ) = ∏ z : primitiveRoots n ℂ, valAt f z := by
  have h := resultant_eq_prod_eval (cyclotomic n ℂ) (f.map (Int.castRingHom ℂ))
    f.natDegree natDegree_map_le (IsAlgClosed.splits _)
  rw [(cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul,
    cyclotomic.roots_eq_primitiveRoots_val] at h
  change (Int.castRingHom ℂ) ((cyclotomic n ℤ).resultant f) = _
  rw [← resultant_map_map (cyclotomic n ℤ) f _ _ (Int.castRingHom ℂ),
    map_cyclotomic]
  rw [Finset.prod_coe_sort]
  simp only [natDegree_cyclotomic, eval_map] at h
  rw [natDegree_cyclotomic]
  exact h

def cross (f g : ℤ[X]) : ℤ[X] :=
  f^7 * expand ℤ 7 g - g^7 * expand ℤ 7 f

theorem seven_dvd_cross (f g : ℤ[X]) : C (7 : ℤ) ∣ cross f g := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let r := Int.castRingHom (ZMod 7)
  have hpow (a : (ZMod 7)[X]) : expand (ZMod 7) 7 a = a^7 := by
    have h := map_frobenius_expand a (p := 7)
    have hf : frobenius (ZMod 7) 7 = RingHom.id (ZMod 7) := by
      ext x
      exact ZMod.pow_card x
    simpa [hf] using h
  have hzero : (cross f g).map r = 0 := by
    simp [cross, Polynomial.map_expand, hpow, mul_comm]
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp
  have h := congrArg (fun a : (ZMod 7)[X] ↦ a.coeff i) hzero
  simpa [r] using h

theorem eval_cross (f g : ℤ[X]) (z : ℂ) :
    valAt (cross f g) z = valAt f z ^ 7 * valAt g (z^7) -
      valAt g z ^ 7 * valAt f (z^7) := by
  simp [cross, valAt, expand_eq_comp_X_pow, eval₂_comp, eval₂_pow]

theorem arch_prod_bound {ι : Type*} [Fintype ι] (e : ι ≃ ι) (z : ι → ℂ) :
    (∏ i, ‖z i ^ 7 * conj (z (e i)) - conj (z i) ^ 7 * z (e i)‖) ≤
      2 ^ Fintype.card ι * (∏ i, ‖z i‖) ^ 8 := by
  calc
    _ ≤ ∏ i, (2 * ‖z i‖ ^ 7 * ‖z (e i)‖) := by
      apply prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro i _
      apply (norm_sub_le _ _).trans
      simp only [norm_mul, norm_pow, Complex.norm_conj]
      linarith
    _ = _ := by
      rw [prod_mul_distrib, prod_mul_distrib, e.prod_comp (fun i ↦ ‖z i‖), prod_pow]
      simp
      ring

/-- The integer resultant of the auxiliary polynomial is divisible by one factor of seven
for each primitive complex root. -/
theorem norm_dvd (n : ℕ) (f g : ℤ[X]) :
    (7 : ℤ) ^ n.totient ∣ cycloNorm n (cross f g) := by
  obtain ⟨h,hh⟩ := seven_dvd_cross f g
  unfold cycloNorm
  rw [hh, resultant_C_mul_right, natDegree_cyclotomic]
  exact dvd_mul_right _ _

theorem norm_eq_prod_abs (n : ℕ) [NeZero n] (f : ℤ[X]) :
    |(cycloNorm n f : ℝ)| = ∏ z : primitiveRoots n ℂ, ‖valAt f z‖ := by
  have h := congrArg (fun z : ℂ ↦ ‖z‖) (cycloNorm_eq_prod n f)
  simpa [Complex.norm_intCast, norm_prod] using h

/-- A nonzero auxiliary resultant forces an exponential lower bound on the actual
integer cyclotomic norm. -/
theorem norm_gap {n : ℕ} [NeZero n] (hn : Nat.Coprime 7 n) (f g : ℤ[X])
    (hg : ∀ z : primitiveRoots n ℂ, valAt g z = conj (valAt f z))
    (hc : cycloNorm n (cross f g) ≠ 0) :
    (7 : ℝ)^n.totient ≤ 2^n.totient * |(cycloNorm n f : ℝ)|^8 := by
  classical
  let e := IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := ℂ) hn
  have harch := arch_prod_bound e (fun z ↦ valAt f z)
  have hval (z : primitiveRoots n ℂ) :
      valAt (cross f g) z =
      valAt f z ^ 7 * conj (valAt f (e z)) - conj (valAt f z) ^ 7 * valAt f (e z) := by
    rw [eval_cross, hg z, ← hg (e z)]
    rfl
  have hcard : Fintype.card (primitiveRoots n ℂ) = n.totient := by
    rw [Fintype.card_coe]
    exact (Complex.isPrimitiveRoot_exp n (NeZero.ne _)).card_primitiveRoots
  have hupper : |(cycloNorm n (cross f g) : ℝ)| ≤
      2^n.totient * |(cycloNorm n f : ℝ)|^8 := by
    rw [norm_eq_prod_abs, norm_eq_prod_abs]
    simp_rw [hval]
    simpa only [hcard] using harch
  apply le_trans _ hupper
  obtain ⟨k,hk⟩ := norm_dvd n f g
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hc
  have habs : (1 : ℝ) ≤ |(k:ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |k| from by have := abs_pos.mpr hk0; omega)
  rw [hk, Int.cast_mul, Int.cast_pow, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (7 : ℤ)^n.totient)]
  simpa using mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ (7 : ℝ)^n.totient)


theorem dvd_cyclo_of_vanishing {n : ℕ} [NeZero n] (f : ℤ[X])
    (z : primitiveRoots n ℂ) (hz : valAt f z = 0) : cyclotomic n ℤ ∣ f := by
  have hζ := isPrimitiveRoot_of_mem_primitiveRoots z.2
  rw [cyclotomic_eq_minpoly hζ (NeZero.pos n)]
  exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral (NeZero.pos _)) hz

theorem dvd_of_norm_zero {n : ℕ} [NeZero n] {f : ℤ[X]} (hf : cycloNorm n f = 0) :
    cyclotomic n ℤ ∣ f := by
  classical
  have he : (∏ z : primitiveRoots n ℂ, valAt f z) = 0 := by
    rw [← cycloNorm_eq_prod, hf, Int.cast_zero]
  obtain ⟨z, _, hz⟩ := prod_eq_zero_iff.mp he
  exact dvd_cyclo_of_vanishing f z hz

theorem eval_zero_of_cyclo_dvd {n : ℕ} {K : Type*} [Field K] [NeZero (n : K)]
    {x : K} (hx : IsPrimitiveRoot x n) {f : ℤ[X]} (hd : cyclotomic n ℤ ∣ f) :
    f.eval₂ (Int.castRingHom K) x = 0 := by
  obtain ⟨g, rfl⟩ := hd
  rw [eval₂_mul, eval₂_eq_eval_map, map_cyclotomic]
  rw [show (cyclotomic n K).eval x = 0 from isRoot_cyclotomic_iff.mpr hx, zero_mul]

theorem perm_torsion {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (x : ι → ℂ)
    (hx : ∀ i, x i ≠ 0) (he : ∀ i, x (e i) = x i ^ 7) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, x i ^ k = 1 := by
  classical
  have hit (k : ℕ) (i : ι) : x ((e^k) i) = x i ^ (7^k) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, he, ih, Nat.pow_succ, pow_mul]
  let h := orderOf e
  have hh : 0 < h := orderOf_pos e
  have hh' : 1 < 7^h := one_lt_pow₀ (by decide) hh.ne'
  refine ⟨7^h-1, by omega, fun i ↦ ?_⟩
  apply mul_right_cancel₀ (hx i)
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 7^h)]
  simpa [h, pow_orderOf_eq_one] using (hit h i).symm


/-- If the seventh-power cross-ratio vanishes on one primitive root, then some common
positive power of the two values agrees at every primitive root. -/
theorem equal_powers_of_cross_zero {n : ℕ} [NeZero n] (hn : Nat.Coprime 7 n)
    (f g : ℤ[X]) (hg : ∀ z : primitiveRoots n ℂ, valAt g z = conj (valAt f z))
    (hc : cycloNorm n (cross f g) = 0) :
    ∃ k : ℕ, 0 < k ∧ cyclotomic n ℤ ∣ f^k - g^k := by
  classical
  let I := ↥(primitiveRoots n ℂ)
  let e := IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := ℂ) hn
  let z : I := ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr
    (Complex.isPrimitiveRoot_exp n (NeZero.ne _))⟩
  by_cases hzero : ∃ w : I, valAt f w = 0
  · obtain ⟨w,hw⟩ := hzero
    refine ⟨1, by decide, dvd_cyclo_of_vanishing _ w ?_⟩
    rw [pow_one,pow_one]
    rw [show valAt (f-g) w = valAt f w - valAt g w from eval₂_sub ..]
    rw [hg w,hw,map_zero,sub_self]
  have hf (i : I) : valAt f i ≠ 0 := fun h ↦ hzero ⟨i,h⟩
  have hg0 (i : I) : valAt g i ≠ 0 := by rw [hg i]; exact (_root_.map_ne_zero _).mpr (hf i)
  let x : I → ℂ := fun i ↦ valAt f i / valAt g i
  have hrel (i : I) : x (e i) = x i ^ 7 := by
    have hv := eval_zero_of_cyclo_dvd (isPrimitiveRoot_of_mem_primitiveRoots i.2)
      (dvd_of_norm_zero hc)
    change valAt (cross f g) i = 0 at hv
    rw [eval_cross, sub_eq_zero] at hv
    change valAt f (e i) / valAt g (e i) = (valAt f i / valAt g i)^7
    rw [div_pow, div_eq_div_iff (hg0 _) (pow_ne_zero _ (hg0 i))]
    change valAt f ((i:ℂ)^7) * valAt g i ^ 7 = valAt f i ^ 7 * valAt g ((i:ℂ)^7)
    simpa only [mul_comm (valAt f ((i:ℂ)^7))] using hv.symm
  obtain ⟨k,hk,hx⟩ := perm_torsion e x (fun i ↦ div_ne_zero (hf i) (hg0 i)) hrel
  refine ⟨k,hk,dvd_cyclo_of_vanishing _ z ?_⟩
  have hp := hx z
  change (valAt f z / valAt g z)^k = 1 at hp
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ (hg0 z))] at hp
  simpa [valAt, eval₂_sub, eval₂_pow] using sub_eq_zero.mpr hp

/-- A modular relation that distinguishes the polynomial from its conjugate forces the
exponential norm inequality. This works at any conductor coprime to seven. -/
theorem split_relation_norm_gap {n : ℕ} [NeZero n] (hn : Nat.Coprime 7 n)
    (f g : ℤ[X]) (hg : ∀ z : primitiveRoots n ℂ, valAt g z = conj (valAt f z))
    {K : Type*} [Field K] [NeZero (n : K)] {x : K} (hx : IsPrimitiveRoot x n)
    (hf0 : f.eval₂ (Int.castRingHom K) x = 0) (hg0 : g.eval₂ (Int.castRingHom K) x ≠ 0) :
    (7 : ℝ)^n.totient ≤ 2^n.totient * |(cycloNorm n f : ℝ)|^8 := by
  apply norm_gap hn f g hg
  intro hc
  obtain ⟨k,hk,hd⟩ := equal_powers_of_cross_zero hn f g hg hc
  have he := eval_zero_of_cyclo_dvd hx hd
  rw [eval₂_sub, eval₂_pow, eval₂_pow, hf0, zero_pow hk.ne', zero_sub, neg_eq_zero] at he
  exact (pow_ne_zero _ hg0) he


/-- Substituting the inverse primitive root gives the conjugate evaluation. -/
theorem inverse_value {n : ℕ} [NeZero n] (f : ℤ[X]) (z : primitiveRoots n ℂ) :
    valAt (f.comp (X^(n-1))) z = conj (valAt f z) := by
  have hr := isPrimitiveRoot_of_mem_primitiveRoots z.2
  have hinv : (z:ℂ)^(n-1) = (z:ℂ)⁻¹ := by
    apply mul_right_cancel₀ (hr.ne_zero (NeZero.ne n))
    rw [inv_mul_cancel₀ (hr.ne_zero (NeZero.ne n)), ← pow_succ, Nat.sub_add_cancel (NeZero.pos n), hr.pow_eq_one]
  rw [Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hr.pow_eq_one (NeZero.ne _))] at hinv
  rw [valAt, eval₂_comp, eval₂_pow, eval₂_X, hinv, valAt, hom_eval₂]
  congr 1
  ext
  simp

/-- An arbitrary relation at a generator that survives at its inverse forces the actual
integer resultant to exceed the Frobenius threshold. -/
theorem inverse_relation_norm_gap {n : ℕ} [NeZero n] (hn : Nat.Coprime 7 n)
    (f : ℤ[X]) {K : Type*} [Field K] [NeZero (n : K)] {x : K} (hx : IsPrimitiveRoot x n)
    (hf : f.eval₂ (Int.castRingHom K) x = 0) (hi : f.eval₂ (Int.castRingHom K) (x⁻¹) ≠ 0) :
    (7 : ℝ)^n.totient ≤ 2^n.totient * |(cycloNorm n f : ℝ)|^8 := by
  apply split_relation_norm_gap hn f _ (inverse_value f) hx hf
  have hinv : x^(n-1) = x⁻¹ := by
    apply mul_right_cancel₀ (hx.ne_zero (NeZero.ne n))
    rw [inv_mul_cancel₀ (hx.ne_zero (NeZero.ne n)), ← pow_succ, Nat.sub_add_cancel (NeZero.pos n), hx.pow_eq_one]
  simpa [eval₂_comp, eval₂_pow, hinv] using hi

#print axioms inverse_relation_norm_gap
#print axioms equal_powers_of_cross_zero
#print axioms norm_gap


end
end ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm
