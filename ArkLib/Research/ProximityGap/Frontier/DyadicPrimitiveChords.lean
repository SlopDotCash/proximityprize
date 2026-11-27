/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSquareOrbit
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-! # Cyclic indexing of the primitive chords at a dyadic order -/
namespace ProximityGap.DyadicPrimitiveChords
open Finset Polynomial

/-- Odd exponents modulo sign, enumerated by powers of five. -/
def five (k : ℕ) (i : ZMod (2 ^ k)) : ZMod (2 ^ (k+2)) := 5 ^ i.val

/-- The two signs of each primitive exponent. -/
def signedFive (k : ℕ) (v : Bool × ZMod (2 ^ k)) : ZMod (2 ^ (k+2)) :=
  if v.1 then -(five k v.2) else five k v.2

theorem five_injective (k : ℕ) : Function.Injective (five k) := by
  intro a b h
  apply ZMod.val_injective
  apply pow_injOn_Iio_orderOf (x := (5 : ZMod (2^(k+2))))
  · simpa only [Set.mem_Iio, ZMod.orderOf_five] using a.val_lt
  · simpa only [Set.mem_Iio, ZMod.orderOf_five] using b.val_lt
  · exact h

private theorem incompatible (k : ℕ) (a b : ZMod (2^k)) : five k a ≠ -five k b := by
  intro h
  have hdiv : 4 ∣ 2^(k+2) := ⟨2^k, by rw [pow_add]; ring⟩
  let f := ZMod.castHom hdiv (ZMod 4)
  have one (i : ZMod (2^k)) : f (five k i) = 1 := by
    unfold five
    rw [map_pow]
    have hid : f (5 : ZMod (2^(k+2))) = (5 : ZMod 4) := map_ofNat f 5
    rw [hid, show (5 : ZMod 4) = 1 by decide, one_pow]
  have eq := congrArg f h
  rw [map_neg, one, one] at eq
  exact (by decide : (1 : ZMod 4) ≠ -1) eq

theorem signedFive_injective (k : ℕ) : Function.Injective (signedFive k) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  cases a <;> cases b
  · simpa [signedFive] using congrArg (fun z => (false,z)) (five_injective k h)
  · exact False.elim (incompatible k i j h)
  · exact False.elim (incompatible k j i h.symm)
  · have h' : five k i = five k j := neg_inj.mp h
    exact congrArg (fun z => (true,z)) (five_injective k h')

private theorem coprime_val (k : ℕ) (v : Bool × ZMod (2^k)) :
    (signedFive k v).val.Coprime (2^(k+2)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [ZMod.natCast_zmod_val]
  have hu : IsUnit (5 : ZMod (2^(k+2))) :=
    (ZMod.isUnit_iff_coprime _ _).mpr ((by decide : Nat.Coprime 5 2).pow_right _)
  unfold signedFive five
  split_ifs
  · exact (hu.pow _).neg
  · exact hu.pow _

/-- The complete primitive-root orbit, including both signs in the exponent. -/
def rootIndex {K : Type*} [Field K] {z : K} (k : ℕ) (hz : IsPrimitiveRoot z (2^(k+2)))
    (v : Bool × ZMod (2^k)) : ↥(primitiveRoots (2^(k+2)) K) :=
  ⟨z^(signedFive k v).val,
    (mem_primitiveRoots (by positivity)).mpr (hz.pow_of_coprime _ (coprime_val k v))⟩

theorem rootIndex_bijective {K : Type*} [Field K] {z : K} (k : ℕ)
    (hz : IsPrimitiveRoot z (2^(k+2))) : Function.Bijective (rootIndex k hz) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    apply signedFive_injective
    apply ZMod.val_injective
    apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    exact congrArg Subtype.val h
  · simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card, Fintype.card_coe,
      hz.card_primitiveRoots, Nat.totient_prime_pow_succ Nat.prime_two]
    ring

/-- Multiplying the primitive chords across the signed orbit gives two. -/
theorem signed_product {K : Type*} [Field K] {z : K} (k : ℕ)
    (hz : IsPrimitiveRoot z (2^(k+2))) :
    (∏ v : Bool × ZMod (2^k), (1 - z^(signedFive k v).val)) = 2 := by
  classical
  let e := Equiv.ofBijective (rootIndex k hz) (rootIndex_bijective k hz)
  have h := e.prod_comp (fun x => 1 - (x : K))
  change (∏ v, (1 - z^(signedFive k v).val)) = _ at h
  rw [h, ← Finset.prod_subtype (primitiveRoots (2^(k+2)) K) (fun _ => Iff.rfl)]
  have he := eval_one_cyclotomic_prime_pow (R := K) (p := 2) (k+1)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hz, eval_prod] at he
  simpa using he

/-- Evaluate a cyclic exponent at an element whose order divides the modulus. -/
def atExp {M : Type*} [Monoid M] {n : ℕ} (z : M) (a : ZMod n) : M := z ^ a.val

theorem atExp_nat {M : Type*} [Monoid M] {n : ℕ} [NeZero n] {z : M}
    (hz : z^n = 1) (a : ℕ) : atExp z (a : ZMod n) = z^a := by
  apply pow_eq_pow_of_modEq _ hz
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp

theorem atExp_add {M : Type*} [Monoid M] {n : ℕ} [NeZero n] {z : M}
    (hz : z^n = 1) (a b : ZMod n) : atExp z (a+b) = atExp z a * atExp z b := by
  unfold atExp
  rw [← pow_add]
  apply pow_eq_pow_of_modEq _ hz
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp

theorem atExp_neg {K : Type*} [Field K] {n : ℕ} [NeZero n] {z : K}
    (hz : z^n = 1) (a : ZMod n) : atExp z (-a) = (atExp z a)⁻¹ := by
  have one := atExp_add hz (-a) a
  have z0 : atExp z (0 : ZMod n) = 1 := by simp [atExp]
  rw [neg_add_cancel, z0] at one
  exact eq_inv_of_mul_eq_one_left one.symm

theorem five_add (k : ℕ) (i a : ZMod (2^k)) :
    five k (i+a) = five k i * five k a := by
  apply atExp_add
  rw [← ZMod.orderOf_five k]
  exact pow_orderOf_eq_one _

/-- The squared chord attached to one representative of an exponent modulo sign. -/
def chord {K : Type*} [Field K] {n : ℕ} (z : K) (r : ZMod n) : K :=
  (1-atExp z r)*(1-(atExp z r)⁻¹)

theorem chord_product {K : Type*} [Field K] {z : K} (k : ℕ)
    (hz : IsPrimitiveRoot z (2^(k+2))) :
    (∏ i : ZMod (2^k), chord z (five k i)) = 2 := by
  have H := signed_product k hz
  rw [Fintype.prod_prod_type] at H
  have two (f : Bool → K) : (∏ b, f b) = f false * f true := by
    rw [show (univ : Finset Bool) = {false,true} by decide]
    simp
  rw [two] at H
  unfold chord
  rw [Finset.prod_mul_distrib]
  change (∏ i : ZMod (2^k), (1-atExp z (five k i))) *
    (∏ i : ZMod (2^k), (1-atExp z (-(five k i)))) = 2 at H
  simpa only [atExp_neg hz.pow_eq_one] using H

private theorem atExp_power {K : Type*} [Field K] {n : ℕ} [NeZero n] {z : K}
    (hz : z^n = 1) (a : ZMod n) (d : ℕ) :
    atExp (z^d) a = atExp z (a * (d : ZMod n)) := by
  unfold atExp
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq _ hz
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp [mul_comm]

private theorem galois_power {K : Type*} [Field K] [Algebra ℚ K] [Normal ℚ K]
    {n : ℕ} {z : K} (hn : 0 < n) (hz : IsPrimitiveRoot z n) (d : ℕ) (hd : d.Coprime n) :
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z^d := by
  let : NeZero n := ⟨hn.ne'⟩
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  have hir := cyclotomic.irreducible_rat hn
  have h := (hz.pow_of_coprime d hd).minpoly_eq_cyclotomic_of_irreducible hir
  apply minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z)
  rw [← hz.minpoly_eq_cyclotomic_of_irreducible hir, h]
  exact minpoly.aeval _ _

/-- All translations of the primitive squared chords act by rational automorphisms
in any normal field containing the chosen root. -/
theorem chord_orbit {K : Type*} [Field K] [Algebra ℚ K] [Normal ℚ K]
    {z : K} (k : ℕ) (hz : IsPrimitiveRoot z (2^(k+2))) (a : ZMod (2^k)) :
    ∃ σ : K ≃ₐ[ℚ] K, ∀ i : ZMod (2^k), σ (chord z (five k i)) = chord z (five k (i+a)) := by
  let d : ℕ := 5^a.val
  have hd : d.Coprime (2^(k+2)) :=
    ((by decide : Nat.Coprime 5 2).pow_right _).pow_left _
  obtain ⟨σ,hσ⟩ := galois_power (by positivity) hz d hd
  refine ⟨σ, fun i => ?_⟩
  have de : (d : ZMod (2^(k+2))) = five k a := by simp [d,five]
  have hpow : σ (atExp z (five k i)) = atExp z (five k (i+a)) := by
    change σ (z ^ (five k i).val) = _
    rw [map_pow, hσ]
    exact (atExp_power hz.pow_eq_one (five k i) d).trans (by rw [de, five_add k i a])
  simp only [chord, map_mul, map_sub, map_one, map_inv₀, hpow]

/-- A signed real representative of a chord lies in any complex subfield containing
the half-angle root and the imaginary unit. -/
private theorem signed_chord_coe {u : ℂ} (hu : ‖u‖ = 1) :
    ((2 * u.im : ℝ) : ℂ) = Complex.I*(u⁻¹-u) := by
  rw [Complex.inv_eq_conj hu]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem signed_chord_sq {u : ℂ} (hu : ‖u‖ = 1) :
    ((2 * u.im : ℝ) : ℂ)^2 = (1-u^2)*(1-(u^2)⁻¹) := by
  have h0 : u ≠ 0 := by intro h; simp [h] at hu
  rw [signed_chord_coe hu, mul_pow, Complex.I_sq]
  field_simp
  ring

private theorem chord_ne_zero {K : Type*} [Field K] {z : K} (k : ℕ)
    (hz : IsPrimitiveRoot z (2^(k+2))) (i : ZMod (2^k)) : chord z (five k i) ≠ 0 := by
  have h := hz.pow_of_coprime _ (coprime_val k (false,i))
  have hn : 1 < 2^(k+2) := by rw [pow_add]; have := Nat.two_pow_pos k; omega
  have hu : atExp z (five k i) ≠ 1 := h.ne_one hn
  unfold chord
  exact mul_ne_zero (sub_ne_zero.mpr hu.symm) (sub_ne_zero.mpr (by simpa using hu))

/-- In an abelian complex field the real representatives of the primitive
squared chords transfer integer independence to the chords themselves. -/
private theorem independent_of_real_representatives (K : IntermediateField ℚ ℂ)
    [IsAbelianGalois ℚ K] (k : ℕ) {z : K} (hz : IsPrimitiveRoot z (2^(k+2)))
    (s : ZMod (2^k) → ℝ) (hm : ∀ i, (s i : ℂ) ∈ K)
    (sq : ∀ i, (s i : ℂ)^2 = ((chord z (five k i) : K) : ℂ))
    (e : ZMod (2^k) → ℤ) (he : ∏ i, (chord z (five k i))^(e i) = 1) : e = 0 := by
  classical
  let embed := IsScalarTower.toAlgHom ℚ ℝ ℂ
  let E := K.comap embed
  let : IsStrictOrderedRing E := Function.Injective.isStrictOrderedRing (Subtype.val : E → ℝ)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) .rfl .rfl
  let g : E →ₐ[ℚ] K := (embed.comp E.val).codRestrict K.toSubalgebra (fun x => x.property)
  let : IsAbelianGalois ℚ E := IsAbelianGalois.of_algHom g
  letI : Algebra E K := g.toRingHom.toAlgebra
  let : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let v (i : ZMod (2^k)) : E := ⟨s i, hm i⟩
  have sqE (i : ZMod (2^k)) : algebraMap E K ((v i)^2) = chord z (five k i) := by
    apply K.val.injective
    rw [map_pow, map_pow]
    exact sq i
  have nz (i : ZMod (2^k)) : v i ≠ 0 := by
    intro hi
    apply chord_ne_zero k hz i
    rw [← sqE i, hi]; simp
  let U (i : ZMod (2^k)) := Units.mk0 (v i) (nz i)
  refine DyadicSquareOrbit.real_abelian_orbit_independent k U ?_ ?_ e ?_
  · intro a
    obtain ⟨σ,hs⟩ := chord_orbit k hz a
    refine ⟨σ.restrictNormal E, fun i => ?_⟩
    apply (algebraMap E K).injective
    change algebraMap E K ((σ.restrictNormal E (v i))^2) = algebraMap E K ((v (i+a))^2)
    rw [← map_pow, AlgEquiv.restrictNormal_commutes, sqE, sqE, hs]
  · apply (algebraMap E K).injective
    change algebraMap E K ((∏ i, v i)^2) = _
    rw [← Finset.prod_pow, map_prod, map_ofNat]
    simpa only [sqE] using chord_product k hz
  · apply (algebraMap E K).injective
    change algebraMap E K ((∏ i, (v i)^(e i))^2) = _
    rw [← Finset.prod_pow, map_prod, map_one]
    have commute (x : E) (m : ℤ) : (x^m)^2 = (x^2)^m := by
      rw [← zpow_natCast, ← zpow_natCast x 2, ← zpow_mul, ← zpow_mul, mul_comm]
    simpa only [commute, map_zpow₀, sqE] using he

/-- The primitive squared chord lengths on any complex dyadic circle are
multiplicatively independent, with one representative for each sign pair. -/
theorem primitive_chord_independent (k : ℕ) {t : ℂ} (ht : IsPrimitiveRoot t (2^(k+3)))
    (e : ZMod (2^k) → ℤ) (he : ∏ i, (chord (t^2) (five k i))^(e i) = 1) : e = 0 := by
  classical
  let N := 2^(k+3)
  let full := {x : ℂ | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ x^n = 1}
  let K := IntermediateField.adjoin ℚ full
  have hN : N ≠ 0 := by dsimp [N]; positivity
  let : IsCyclotomicExtension {N} ℚ K :=
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot _ _ _ (by
      intro n hn _
      rw [Set.mem_singleton_iff] at hn
      subst n
      exact ⟨t,ht⟩)
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  have mem {x : ℂ} (hx : x^N = 1) : x ∈ K :=
    IntermediateField.subset_adjoin ℚ full ⟨N,rfl,hN,hx⟩
  have tmem := mem ht.pow_eq_one
  have imem : Complex.I ∈ K := by
    apply mem
    have four : Complex.I^4=1 := by norm_num [pow_succ, Complex.I_mul_I]
    have Nfour : N = 4*2^(k+1) := by dsimp [N]; ring
    rw [Nfour, pow_mul, four, one_pow]
  have twice : 2^(k+3) = 2^(k+2)*2 := by ring
  have hz : IsPrimitiveRoot (t^2) (2^(k+2)) := by
    have h := ht.pow_of_dvd (p := 2) (by decide) (twice ▸ dvd_mul_left _ _)
    simpa only [twice, Nat.mul_div_cancel _ (by decide : 0 < 2)] using h
  let z : K := ⟨t^2,K.pow_mem tmem 2⟩
  have hzK : IsPrimitiveRoot z (2^(k+2)) := by
    constructor
    · exact Subtype.ext hz.pow_eq_one
    · intro l hl
      exact hz.dvd_of_pow_eq_one l (congrArg Subtype.val hl)
  let u (i : ZMod (2^k)) := t^(five k i).val
  let s (i : ZMod (2^k)) := 2*(u i).im
  have norm (i : ZMod (2^k)) : ‖u i‖ = 1 := by
    simp only [u, norm_pow, ht.norm'_eq_one hN, one_pow]
  apply independent_of_real_representatives K k hzK s _ _ e
  · apply (algebraMap K ℂ).injective
    have hc (i : ZMod (2^k)) : algebraMap K ℂ (chord z (five k i)) =
        chord (t^2) (five k i) := by
      simp only [chord, atExp, map_mul, map_sub, map_one, map_inv₀, map_pow]
      rfl
    simpa only [map_prod,map_zpow₀,map_one,hc] using he
  · intro i
    change ((2*(u i).im : ℝ) : ℂ) ∈ K
    rw [signed_chord_coe (norm i)]
    have h := K.pow_mem tmem (five k i).val
    exact K.mul_mem imem (K.sub_mem (K.inv_mem h) h)
  · intro i
    change ((2*(u i).im : ℝ) : ℂ)^2 = (1-(t^2)^(five k i).val)*(1-((t^2)^(five k i).val)⁻¹)
    have hp : (u i)^2 = (t^2)^(five k i).val := by
      unfold u
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    exact (signed_chord_sq (norm i)).trans (congrArg (fun x : ℂ => (1-x)*(1-x⁻¹)) hp)

/-- Independence of the primitive squared chords for any choice of primitive root. -/
theorem squared_chords_independent (k : ℕ) {z : ℂ} (hz : IsPrimitiveRoot z (2^(k+2)))
    (e : ZMod (2^k) → ℤ) (he : ∏ i, (chord z (five k i))^(e i) = 1) : e = 0 := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  have low : t^(2^(k+2)) ≠ 1 := by
    rw [show 2^(k+2) = 2*2^(k+1) by ring, pow_mul, ht]
    apply hz.pow_ne_one_of_pos_of_lt (by positivity)
    rw [show 2^(k+2) = 2^(k+1)*2 by ring]
    have := Nat.two_pow_pos (k+1)
    omega
  have top : t^(2^(k+3)) = 1 := by
    rw [show 2^(k+3) = 2*2^(k+2) by ring, pow_mul, ht, hz.pow_eq_one]
  have ord : orderOf t = 2^((k+2)+1) := orderOf_eq_prime_pow (p := 2) low top
  have ht' : IsPrimitiveRoot t (2^(k+3)) := ord ▸ IsPrimitiveRoot.orderOf t
  exact primitive_chord_independent k ht' e (ht ▸ he)

/-- A product of the primitive complex factors with integer exponents can have unit
absolute value only when all the exponents vanish. In particular this holds for
products equal to a root of unity. -/
theorem primitive_factors_norm_one (k : ℕ) {z : ℂ} (hz : IsPrimitiveRoot z (2^(k+2)))
    (e : ZMod (2^k) → ℤ)
    (he : ‖∏ i, (1-atExp z (five k i))^(e i)‖ = 1) : e = 0 := by
  apply squared_chords_independent k hz e
  let f (i : ZMod (2^k)) := 1-atExp z (five k i)
  have unit (i : ZMod (2^k)) : ‖atExp z (five k i)‖ = 1 := by
    simp [atExp, hz.norm'_eq_one (by positivity)]
  have hconj (i : ZMod (2^k)) : chord z (five k i) = f i * (starRingEnd ℂ) (f i) := by
    simp only [f, chord, map_sub, map_one, ← Complex.inv_eq_conj (unit i)]
  simp_rw [hconj, mul_zpow, ← map_zpow₀]
  rw [Finset.prod_mul_distrib, ← map_prod, Complex.mul_conj']
  rw [show ‖∏ i, f i ^ e i‖ = 1 from he]
  simp

theorem chord_neg {z : ℂ} {n : ℕ} [NeZero n] (hz : IsPrimitiveRoot z n) (r : ZMod n) :
    chord z (-r) = chord z r := by
  simp only [chord, atExp_neg hz.pow_eq_one, inv_inv, mul_comm]

/-- A product over all signed primitive exponents is one exactly when its two
exponents at each inverse pair cancel. -/
theorem signed_chord_relation_iff (k : ℕ) {z : ℂ} (hz : IsPrimitiveRoot z (2^(k+2)))
    (v : Bool × ZMod (2^k) → ℤ) :
    (∏ j, (chord z (signedFive k j))^(v j)) = 1 ↔
      ∀ i, v (false,i) + v (true,i) = 0 := by
  classical
  have two (f : Bool → ℂ) : (∏ b, f b) = f false * f true := by
    rw [show (univ : Finset Bool) = {false,true} by decide]
    simp
  rw [Fintype.prod_prod_type, two, ← Finset.prod_mul_distrib]
  simp only [signedFive, Bool.false_eq_true, ↓reduceIte, chord_neg hz]
  simp_rw [← zpow_add₀ (chord_ne_zero k hz _)]
  constructor
  · intro h i
    exact congrFun (squared_chords_independent k hz _ h) i
  · intro h
    simp [h]

#print axioms signed_chord_relation_iff
#print axioms primitive_factors_norm_one
#print axioms primitive_chord_independent
#print axioms chord_orbit
#print axioms chord_product
#print axioms signed_product
end ProximityGap.DyadicPrimitiveChords
