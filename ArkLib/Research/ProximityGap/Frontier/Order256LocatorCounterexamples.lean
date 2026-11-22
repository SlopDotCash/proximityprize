/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.SpurPrimeReducibleTower
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Four equal locator ratios of degree 62 on named order-256 domains -/

set_option autoImplicit false
set_option maxRecDepth 8192
open Polynomial
open ArkLib.ProximityGap.BinaryPower

namespace ArkLib.ProximityGap.Frontier.Order256LocatorCounterexamples

/-- Numerator or denominator evaluated at the exponent `i` of the root `z`. -/
def locator {R : Type*} [CommRing R] (z : R) (i : ℕ) (sites : List ℕ) : R :=
  (sites.map fun j => binaryPow z i - binaryPow z j).prod

/-- Cross product comparing the two locator quotients at `i` and `j`. -/
def cross {R : Type*} [CommRing R] (z : R) (i j : ℕ) (P Q : List ℕ) : R :=
  locator z i P * locator z j Q - locator z i Q * locator z j P

theorem locator_eq {R : Type*} [CommRing R] (z : R) (i : ℕ) (sites : List ℕ) :
    locator z i sites = (sites.map fun j => z ^ i - z ^ j).prod := by
  simp only [locator, binaryPow_eq_pow]

theorem map_locator {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : R) (i : ℕ) (L : List ℕ) : f (locator z i L) = locator (f z) i L := by
  induction L with
  | nil => simp [locator]
  | cons j L ih =>
    simp only [locator, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, ih]
    simp [binaryPow_eq_pow]

theorem map_cross {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : R) (i j : ℕ) (P Q : List ℕ) : f (cross z i j P Q) = cross (f z) i j P Q := by
  simp [cross, map_locator]

/-- An auxiliary nonzero cross product separates the complex values at every primitive root. -/
theorem complex_ne_zero (P Q : List ℕ) (i j : ℕ) (h : cross (3 : ZMod 257) i j P Q ≠ 0)
    {z : ℂ} (hz : IsPrimitiveRoot z 256) : cross z i j P Q ≠ 0 := by
  intro he
  let f := cross (X : ℤ[X]) i j P Q
  have evaluate {R : Type} [CommRing R] (a : R) : aeval a f = cross a i j P Q := by
    simpa [f] using map_cross (aeval a).toRingHom (X : ℤ[X]) i j P Q
  have hz' : aeval z f = 0 := (evaluate z).trans he
  have hd : cyclotomic 256 ℤ ∣ f := by
    rw [cyclotomic_eq_minpoly hz (by decide : 0 < 256)]
    exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral (by decide : 0 < 256)) hz'
  obtain ⟨t, ht⟩ := hd
  have haux : aeval (3 : ZMod 257) (cyclotomic 256 ℤ) = 0 := by
    rw [show (256 : ℕ) = 2^8 by decide,
      SpurPrimeReducible.cyclotomic_two_pow (by decide : 1 ≤ 8)]
    simp only [map_add, map_pow, aeval_X, map_one]
    decide
  apply h
  rw [← evaluate (3 : ZMod 257), ht, map_mul, haux, zero_mul]

/-- The generator, supports and four test centers of one named-field example. -/
structure Example where
  prime : ℕ
  root : ℕ
  value : ℕ
  numerator : List ℕ
  denominator : List ℕ
  centers : List ℕ

/-- Every listed center has nonzero denominator and the displayed common numerator ratio. -/
def finiteValues (d : Example) : Prop :=
  ∀ i ∈ d.centers, locator (d.root : ZMod d.prime) i d.denominator ≠ 0 ∧
    locator (d.root : ZMod d.prime) i d.numerator =
      (d.value : ZMod d.prime) * locator (d.root : ZMod d.prime) i d.denominator

/-- All indicated exponents are valid, and the two disjoint supports have degree 62. -/
def validSupports (d : Example) : Prop :=
  d.numerator.length = 62 ∧ d.denominator.length = 62 ∧ d.centers.length = 4 ∧
  (d.numerator ++ d.denominator ++ d.centers).Nodup ∧
  (∀ i ∈ d.centers, i % 2 = 0) ∧ ∀ i ∈ d.numerator ++ d.denominator ++ d.centers, i < 256

/-- Degree-62 witness for the first named prime. -/
def first : Example where
  prime := 365375409332725729550921208179070755120141565953
  root := 322599146406626103794850093414153468931889947837
  value := 188148678191796610178779171843413814268811727497
  numerator :=
    [7, 8, 18, 22, 25, 27, 31, 32, 34, 41, 46, 51,
     53, 63, 67, 72, 79, 85, 88, 90, 93, 95, 100, 104,
     108, 109, 111, 115, 119, 121, 126, 130, 135, 137, 141, 145,
     147, 148, 152, 156, 161, 163, 166, 168, 171, 177, 184, 189,
     193, 203, 205, 210, 215, 222, 224, 225, 229, 231, 234, 238,
     248, 249]
  denominator :=
    [10, 13, 14, 23, 24, 28, 35, 40, 48, 49, 61, 69,
     70, 71, 76, 78, 80, 81, 87, 91, 92, 94, 96, 98,
     101, 102, 105, 107, 110, 123, 125, 131, 133, 146, 149, 151,
     154, 155, 158, 160, 162, 164, 165, 169, 175, 176, 178, 180,
     185, 186, 187, 195, 207, 208, 216, 221, 228, 232, 233, 242,
     243, 246]
  centers := [2, 4, 252, 254]

/-- Degree-62 witness for the second named prime. -/
def second : Example where
  prime := 730750818665451459101842416358141509841924915201
  root := 579073162555415988350824568022172727493239031161
  value := 172618865225769840779409899132552134222571512143
  numerator :=
    [3, 11, 15, 16, 28, 33, 37, 46, 51, 55, 56, 59,
     62, 65, 70, 71, 72, 73, 74, 75, 81, 82, 87, 89,
     98, 99, 100, 102, 103, 111, 124, 132, 145, 153, 154, 156,
     157, 158, 167, 169, 174, 175, 181, 182, 183, 184, 185, 186,
     191, 194, 197, 200, 201, 205, 210, 219, 223, 228, 240, 241,
     245, 253]
  denominator :=
    [1, 7, 12, 14, 17, 20, 22, 29, 30, 38, 42, 47,
     53, 54, 60, 63, 66, 76, 78, 83, 85, 94, 96, 104,
     105, 109, 113, 115, 116, 119, 122, 134, 137, 140, 141, 143,
     147, 151, 152, 160, 162, 171, 173, 178, 180, 190, 193, 196,
     202, 203, 209, 214, 218, 226, 227, 234, 236, 239, 242, 244,
     249, 255]
  centers := [4, 10, 246, 252]

private theorem primitive_of_checks {R : Type*} [CommRing R] (a : R)
    (hn : binaryPow a 128 ≠ 1) (hp : binaryPow a 256 = 1) : IsPrimitiveRoot a 256 := by
  rw [binaryPow_eq_pow] at hn hp
  have hh : orderOf a = 2 ^ (7 + 1) := orderOf_eq_prime_pow (p := 2) (n := 7) hn hp
  rw [show 256 = orderOf a by simpa using hh.symm]
  exact IsPrimitiveRoot.orderOf a

theorem first_root : IsPrimitiveRoot (first.root : ZMod first.prime) 256 :=
  primitive_of_checks _ (by decide) (by decide)

theorem first_supports : validSupports first := by
  unfold validSupports
  decide

theorem first_finite : finiteValues first := by
  unfold finiteValues
  decide

theorem first_complex {z : ℂ} (hz : IsPrimitiveRoot z 256) :
    cross z 2 4 first.numerator first.denominator ≠ 0 :=
  complex_ne_zero _ _ _ _ (by decide) hz

theorem first_odd_asymmetry : 25 ∈ first.numerator ∧ 153 ∉ first.numerator := by
  decide

#print axioms first_root
#print axioms first_supports
#print axioms first_finite
#print axioms first_complex
#print axioms first_odd_asymmetry

theorem second_root : IsPrimitiveRoot (second.root : ZMod second.prime) 256 :=
  primitive_of_checks _ (by decide) (by decide)

theorem second_supports : validSupports second := by
  unfold validSupports
  decide

theorem second_finite : finiteValues second := by
  unfold finiteValues
  decide

theorem second_complex {z : ℂ} (hz : IsPrimitiveRoot z 256) :
    cross z 4 10 second.numerator second.denominator ≠ 0 :=
  complex_ne_zero _ _ _ _ (by decide) hz

theorem second_odd_asymmetry : 3 ∈ second.numerator ∧ 131 ∉ second.numerator := by
  decide

#print axioms second_root
#print axioms second_supports
#print axioms second_finite
#print axioms second_complex
#print axioms second_odd_asymmetry

/-- The monic degree-`m * L.length` locator after taking full power-map fibers. -/
def lifted {R : Type*} [CommRing R] (point z : R) (m : ℕ) (L : List ℕ) : R :=
  (L.map fun j => point ^ m - z ^ j).prod

theorem lifted_at {R : Type*} [CommRing R] (g z : R) (m i t : ℕ) (L : List ℕ)
    (hg : g ^ m = z) (hz : z ^ 256 = 1) :
    lifted (g ^ (i + 256 * t)) z m L = locator z i L := by
  have he : (g ^ (i + 256*t)) ^ m = z ^ i := by
    calc
      _ = (g^m)^(i + 256*t) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = z^i := by rw [hg, pow_add, pow_mul, hz, one_pow, mul_one]
  simp only [lifted, he, locator_eq]

/-- Distinct primitive-root exponents are the full zero set of the indicated locator. -/
theorem locator_zero_iff {R : Type*} [CommRing R] [IsDomain R] {z : R}
    (hz : IsPrimitiveRoot z 256) (i : ℕ) (hi : i < 256)
    (L : List ℕ) (hL : ∀ j ∈ L, j < 256) : locator z i L = 0 ↔ i ∈ L := by
  induction L with
  | nil => simp [locator]
  | cons j L ih =>
    have hj := hL j (by simp)
    have htail : ∀ k ∈ L, k < 256 := fun k hk => hL k (by simp [hk])
    have hdiff : z^i - z^j = 0 ↔ i = j :=
      sub_eq_zero.trans ⟨hz.pow_inj hi hj, fun e => e ▸ rfl⟩
    rw [show locator z i (j :: L) = (z^i - z^j) * locator z i L by simp [locator_eq],
      mul_eq_zero, hdiff, ih htail, List.mem_cons]

/-- Each lifted locator vanishes on precisely the listed fibers of the production subgroup. -/
theorem lifted_zero_iff {R : Type*} [CommRing R] [IsDomain R] (g z : R) (m i t : ℕ)
    (hi : i < 256) (L : List ℕ) (hL : ∀ j ∈ L, j < 256)
    (hg : g ^ m = z) (hz : IsPrimitiveRoot z 256) :
    lifted (g ^ (i + 256 * t)) z m L = 0 ↔ i ∈ L := by
  rw [lifted_at _ _ _ _ _ _ hg hz.pow_eq_one, locator_zero_iff hz _ hi _ hL]

/-- A separated complex pair remains separated at any two of its lifts. -/
theorem lifted_complex {i j : ℕ} (P Q : List ℕ)
    (h : ∀ {u : ℂ}, IsPrimitiveRoot u 256 → cross u i j P Q ≠ 0)
    {g : ℂ} (hg : IsPrimitiveRoot g (2^30)) (s t : ℕ) :
    let z := g^4194304
    lifted (g^(i + 256*s)) z 4194304 P * lifted (g^(j + 256*t)) z 4194304 Q -
    lifted (g^(i + 256*s)) z 4194304 Q * lifted (g^(j + 256*t)) z 4194304 P ≠ 0 := by
  have hz : IsPrimitiveRoot (g^4194304) 256 :=
    hg.pow_div_gcd 4194304 (by decide)
  dsimp only
  simp only [lifted_at _ _ _ _ _ _ rfl hz.pow_eq_one]
  exact h hz

/-- The 256 fiber indices give disjoint sets of 2²² points on the production domain. -/
theorem fiber_indices_injective {R : Type*} [CommRing R] (g : R) (hg : IsPrimitiveRoot g (2^30)) :
    Function.Injective (fun p : Fin 256 × Fin 4194304 =>
      g ^ ((p.1 : ℕ) + 256 * (p.2 : ℕ))) := by
  intro a b he
  have a₁ := a.1.isLt
  have a₂ := a.2.isLt
  have b₁ := b.1.isLt
  have b₂ := b.2.isLt
  have hh := hg.pow_inj (i := (a.1 : ℕ) + 256 * (a.2 : ℕ))
    (j := (b.1 : ℕ) + 256 * (b.2 : ℕ)) (by norm_num; omega) (by norm_num; omega) he
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The common good value holds at every production site in the four indicated fibers. -/
def productionValues (d : Example) (g : ZMod d.prime) : Prop :=
  ∀ i ∈ d.centers, ∀ t : Fin 4194304,
    lifted (g ^ (i + 256 * (t : ℕ))) (d.root : ZMod d.prime) 4194304 d.denominator ≠ 0 ∧
    lifted (g ^ (i + 256 * (t : ℕ))) (d.root : ZMod d.prime) 4194304 d.numerator =
      (d.value : ZMod d.prime) *
        lifted (g ^ (i + 256 * (t : ℕ))) (d.root : ZMod d.prime) 4194304 d.denominator

theorem production_of_finite (d : Example) (g : ZMod d.prime)
    (hg : g^4194304 = (d.root : ZMod d.prime)) (hz : IsPrimitiveRoot (d.root : ZMod d.prime) 256)
    (hf : finiteValues d) : productionValues d g := by
  intro i hi t
  simp only [lifted_at _ _ _ _ _ _ hg hz.pow_eq_one]
  exact hf i hi

theorem production_counts : 4 * 4194304 = 16777216 ∧ 62 * 4194304 = 260046848 ∧
    260046848 < 2^28 - 1 := by decide

/-- Explicit order-2³⁰ lift of the first primitive 256th root. -/
def firstProductionRoot : ZMod first.prime := 303645430271030343624574566109998498685964493478

theorem first_production : IsPrimitiveRoot firstProductionRoot (2^30) ∧
    productionValues first firstProductionRoot := by
  have hn : firstProductionRoot ^ (2^29) ≠ 1 := by rw [← binaryPow_eq_pow]; decide
  have hp : firstProductionRoot ^ (2^30) = 1 := by rw [← binaryPow_eq_pow]; decide
  have hg : firstProductionRoot^4194304 = (first.root : ZMod first.prime) := by
    rw [← binaryPow_eq_pow]
    decide
  have hh : orderOf firstProductionRoot = 2^(29+1) := orderOf_eq_prime_pow (p := 2) (n := 29) hn hp
  refine ⟨?_, production_of_finite _ _ hg first_root first_finite⟩
  rw [← hh]
  exact IsPrimitiveRoot.orderOf _

#print axioms first_production

/-- Explicit order-2³⁰ lift of the second primitive 256th root. -/
def secondProductionRoot : ZMod second.prime := 192152681249815148642741928588691886362054863855

theorem second_production : IsPrimitiveRoot secondProductionRoot (2^30) ∧
    productionValues second secondProductionRoot := by
  have hn : secondProductionRoot ^ (2^29) ≠ 1 := by rw [← binaryPow_eq_pow]; decide
  have hp : secondProductionRoot ^ (2^30) = 1 := by rw [← binaryPow_eq_pow]; decide
  have hg : secondProductionRoot^4194304 = (second.root : ZMod second.prime) := by
    rw [← binaryPow_eq_pow]
    decide
  have hh : orderOf secondProductionRoot = 2^(29+1) := orderOf_eq_prime_pow (p := 2) (n := 29) hn hp
  refine ⟨?_, production_of_finite _ _ hg second_root second_finite⟩
  rw [← hh]
  exact IsPrimitiveRoot.orderOf _

#print axioms second_production

#print axioms lifted_complex
#print axioms lifted_zero_iff
#print axioms fiber_indices_injective

end ArkLib.ProximityGap.Frontier.Order256LocatorCounterexamples
