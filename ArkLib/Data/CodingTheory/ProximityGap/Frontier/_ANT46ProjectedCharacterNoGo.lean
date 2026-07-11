/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ANT46RungTwoAccidentOrbit
import ArkLib.Data.CodingTheory.ProximityGap.TangentSumJacobiAverage

/-!
# The projected ANT46 signature as a character collision: exact identities and no-go

Let `P - 1 = n*k*r`, with `r` a prime divisor of the cofactor `(P-1)/n`.  The projected
signature from `_ANT46KappaProductionReduction` is

`chi_r(x-1) = (x-1)^(n*k)`.

It is the order-`r` power-residue character.  This file records four exact consequences.

1.  Character-fibre collisions have an exact cyclic Parseval formula.  If `c(x) in Fin r`
    is the discrete character value, then

    `r * sum_(x,y) [c(x)=c(y)] = sum_(j<r) S_j * Sbar_j`.

    Thus the large character order does not itself give a `1/r` gain: there are `r-1`
    nonprincipal modes.
2.  The existing `TangentSumJacobiAverage` theorem identifies each nonprincipal mode over a
    subgroup kernel as an average of Jacobi sums.  Applying the individual Weil bound
    `|S_j|^2 <= P` gives the raw collision ceiling

    `((n-1)^2 + (r-1)P)/r`.

    At the two production primes this misses the inversion-floor target `2n-3` by respectively
    `127--128` and `128--129` bits.
3.  Every projected fibre injects under `x |-> x-1` into a cyclotomic-class intersection
    `(C_a+1) intersect C_0`.  The Do Duc--Leung--Schmidt bound `(a,b)<=3` therefore has exactly
    the right geometric object, but its sufficient hypothesis is unusable here.  Their class
    size is `k=(P-1)/r` and `ord_k(P)=1`; the required squared threshold is `14^k < P^2`, while
    the reverse strict inequality holds at both production primes.
4.  For `x=zeta^a`, the character normalizes through the cyclotomic unit

    `u_a=(zeta^a-1)/(zeta-1)=sum_(i<a) zeta^i`.

    Projected separation is exactly separation of the `r`-th power-residue symbols of the
    `u_a`.  Kummer reciprocity can rephrase this as Frobenius separation in the extensions
    obtained by adjoining `r`-th roots of these units, but no existing certificate computes
    those Frobenius values simultaneously for `2^29-1` units.  It is a new exact socket, not a
    discharge.  Issue #466.

Reference: T. Do Duc, K. H. Leung, B. Schmidt, *Upper Bounds for Cyclotomic Numbers*,
arXiv:1903.07314, Main Theorem 1.
-/

set_option autoImplicit false

open Finset BigOperators
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo

/-! ## Cyclic character orthogonality and collision Parseval -/

/-- Orthogonality of the `r` powers of a primitive `r`-th root, indexed by two character
codes in `Fin r`. -/
theorem cyclicCode_orthogonality {r : Nat} (hr : 0 < r) {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta r) (a b : Fin r) :
    ∑ j ∈ range r, (zeta ^ (a : Nat)) ^ j * (((zeta ^ (b : Nat)) ^ j)⁻¹) =
      if a = b then (r : ℂ) else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have hzeta0 : zeta ≠ 0 := hzeta.ne_zero hr.ne'
    have hone : ∀ j ∈ range r,
        (zeta ^ (a : Nat)) ^ j * (((zeta ^ (a : Nat)) ^ j)⁻¹) = 1 := by
      intro j _
      exact mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hzeta0))
    rw [sum_congr rfl hone, sum_const, card_range]
    simp
  · rw [if_neg hab]
    let u : ℂ := zeta ^ (a : Nat) / zeta ^ (b : Nat)
    have hzeta0 : zeta ≠ 0 := hzeta.ne_zero hr.ne'
    have hu1 : u ≠ 1 := by
      intro hu
      have hpows : zeta ^ (a : Nat) = zeta ^ (b : Nat) :=
        (div_eq_one_iff_eq (pow_ne_zero _ hzeta0)).mp hu
      exact hab (Fin.ext (hzeta.pow_inj a.isLt b.isLt hpows))
    have hur : u ^ r = 1 := by
      dsimp [u]
      have ha : (zeta ^ (a : Nat)) ^ r = 1 := by
        rw [← pow_mul, mul_comm (a : Nat) r, pow_mul, hzeta.pow_eq_one, one_pow]
      have hb : (zeta ^ (b : Nat)) ^ r = 1 := by
        rw [← pow_mul, mul_comm (b : Nat) r, pow_mul, hzeta.pow_eq_one, one_pow]
      rw [div_pow, ha, hb, div_one]
    have hterm : ∀ j ∈ range r,
        (zeta ^ (a : Nat)) ^ j * (((zeta ^ (b : Nat)) ^ j)⁻¹) = u ^ j := by
      intro j _
      dsimp [u]
      rw [div_eq_mul_inv, mul_pow, inv_pow]
    rw [sum_congr rfl hterm, geom_sum_eq hu1, hur, sub_self, zero_div]

/-- The collision mass of a finite family of cyclic character codes.  It is written as an
explicit `0/1` sum so the Parseval identity stays field-valued and kernel-cheap. -/
noncomputable def codeCollisionMass {alpha : Type*} [DecidableEq alpha] {r : Nat}
    (S : Finset alpha) (code : alpha → Fin r) : ℂ :=
  ∑ x ∈ S, ∑ y ∈ S, if code x = code y then 1 else 0

/-- Exact multiplicative-character collision Parseval. -/
theorem codeCollision_parseval {alpha : Type*} [DecidableEq alpha] {r : Nat}
    (hr : 0 < r) {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta r)
    (S : Finset alpha) (code : alpha → Fin r) :
    (r : ℂ) * codeCollisionMass S code =
      ∑ x ∈ S, ∑ y ∈ S, ∑ j ∈ range r,
        (zeta ^ (code x : Nat)) ^ j * (((zeta ^ (code y : Nat)) ^ j)⁻¹) := by
  rw [codeCollisionMass, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  calc
    ∑ x ∈ S, ∑ y ∈ S, (r : ℂ) * (if code x = code y then 1 else 0) =
        ∑ x ∈ S, ∑ y ∈ S,
          ∑ j ∈ range r,
            (zeta ^ (code x : Nat)) ^ j * (((zeta ^ (code y : Nat)) ^ j)⁻¹) := by
      refine sum_congr rfl (fun x _ ↦ sum_congr rfl (fun y _ ↦ ?_))
      rw [cyclicCode_orthogonality hr hzeta]
      split_ifs <;> ring

/-! ## The exact Jacobi expansion of each collision mode -/

section JacobiMode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The character mode naturally produced by the projected difference signature. -/
noncomputable def differenceMode (chi phi : MulChar F ℂ) : ℂ :=
  ∑ x ∈ univ.filter (fun x ↦ chi x = 1), phi (x - 1)

/-- Exact shifted Jacobi formula for a projected collision mode.  It is the existing tangent-sum
identity with the harmless factor `phi(-1)` made explicit:

`ord(chi) * sum_(x in ker chi) phi(x-1)
  = phi(-1) * sum_(i<ord chi) J(chi^i,phi)`. -/
theorem differenceMode_mul_orderOf_eq_sum_jacobiSum (chi phi : MulChar F ℂ) :
    (orderOf chi : ℂ) * differenceMode chi phi =
      phi (-1) * ∑ i ∈ range (orderOf chi), jacobiSum (chi ^ i) phi := by
  have hmode : differenceMode chi phi =
      phi (-1) * ArkLib.ProximityGap.TangentSumJacobiAverage.tangentSum chi phi := by
    rw [differenceMode, ArkLib.ProximityGap.TangentSumJacobiAverage.tangentSum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← map_mul]
    congr 1
    ring
  calc
    (orderOf chi : ℂ) * differenceMode chi phi =
        phi (-1) * ((orderOf chi : ℂ) *
          ArkLib.ProximityGap.TangentSumJacobiAverage.tangentSum chi phi) := by
      rw [hmode]
      ring
    _ = phi (-1) * ∑ i ∈ range (orderOf chi), jacobiSum (chi ^ i) phi := by
      rw [ArkLib.ProximityGap.TangentSumJacobiAverage.tangentSum_mul_orderOf_eq_sum_jacobiSum]

end JacobiMode

/-! ## Exact cyclotomic-class containment -/

section CyclotomicFiber

variable {F Gamma : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq Gamma]

/-- A projected-character fibre on the punctured subgroup. -/
def characterFiber (H : Finset F) (chi : F → Gamma) (v : Gamma) : Finset F :=
  (H.erase 1).filter (fun x ↦ chi (x - 1) = v)

/-- The ambient cyclotomic-number intersection `(C_v + 1) intersect C_1`. -/
def cyclotomicIntersection (chi : F → Gamma) (v oneValue : Gamma) : Finset F :=
  univ.filter (fun z ↦ chi z = v ∧ chi (z + 1) = oneValue)

/-- Every projected fibre injects by `x |-> x-1` into the corresponding ambient cyclotomic
intersection, provided the subgroup lies in the kernel class. -/
theorem card_characterFiber_le_cyclotomicIntersection
    (H : Finset F) (chi : F → Gamma) (v oneValue : Gamma)
    (hH : ∀ x ∈ H, chi x = oneValue) :
    (characterFiber H chi v).card ≤ (cyclotomicIntersection chi v oneValue).card := by
  classical
  let f : F → F := fun x ↦ x - 1
  have hinj : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    linear_combination hxy
  rw [← Finset.card_image_of_injective (characterFiber H chi v) hinj]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
  rw [characterFiber, Finset.mem_filter] at hx
  rcases hx with ⟨hxErase, hxchi⟩
  have hxH : x ∈ H := (Finset.mem_erase.mp hxErase).2
  rw [cyclotomicIntersection, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hxchi, ?_⟩
  dsimp [f]
  simpa using hH x hxH

end CyclotomicFiber

/-! ## Cyclotomic-unit normalization -/

variable {K : Type*} [Field K]

/-- The standard cyclotomic unit quotient `(zeta^a-1)/(zeta-1)`. -/
def cyclotomicUnit (zeta : K) (a : Nat) : K := ∑ i ∈ range a, zeta ^ i

theorem pow_sub_one_eq_sub_one_mul_cyclotomicUnit (zeta : K) (a : Nat) :
    zeta ^ a - 1 = (zeta - 1) * cyclotomicUnit zeta a := by
  rw [cyclotomicUnit, mul_comm, geom_sum_mul]

/-- Exact normalization of the projected ANT46 character through a cyclotomic unit. -/
theorem projectedKappa_cyclotomicUnit_factor (zeta : K) (a n e : Nat) :
    ((zeta ^ a - 1) ^ n) ^ e =
      ((zeta - 1) ^ n) ^ e * (cyclotomicUnit zeta a) ^ (n * e) := by
  rw [pow_sub_one_eq_sub_one_mul_cyclotomicUnit, mul_pow, mul_pow, pow_mul]

/-- Once the common base class is nonzero, projected signature equality is exactly equality of
the power-residue symbols of the two cyclotomic units. -/
theorem projectedKappa_eq_iff_cyclotomicUnit_pow_eq {zeta : K} (hzeta : zeta ≠ 1)
    (a b n e : Nat) :
    ((zeta ^ a - 1) ^ n) ^ e = ((zeta ^ b - 1) ^ n) ^ e ↔
      (cyclotomicUnit zeta a) ^ (n * e) = (cyclotomicUnit zeta b) ^ (n * e) := by
  rw [projectedKappa_cyclotomicUnit_factor, projectedKappa_cyclotomicUnit_factor]
  constructor
  · exact mul_left_cancel₀ (pow_ne_zero e (pow_ne_zero n (sub_ne_zero.mpr hzeta)))
  · intro h
    rw [h]

/-- Equality of two nonzero residue symbols is the Kummer condition that their quotient lies in
the kernel of the power-residue character. -/
theorem cyclotomicUnit_pow_eq_iff_ratio_pow_eq_one {u v : K} (hv : v ≠ 0) (E : Nat) :
    u ^ E = v ^ E ↔ (u / v) ^ E = 1 := by
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero E hv)]

/-! ## Production arithmetic: Weil and cyclotomic-number thresholds -/

def productionN : Nat := 2 ^ 30
def inversionFloor : Nat := 2 * productionN - 3

def firstP : Nat := ArkLib.ProximityGap.PrizeShapePrimeP30.P
def firstR : Nat := 462478642316479903
def firstClassSize : Nat := 790037368001730942548819574784
def firstWeilNumerator : Nat :=
  (productionN - 1) ^ 2 + (firstR - 1) * firstP

def secondP : Nat := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
def secondR : Nat := 90308905535905320959
def secondClassSize : Nat := 8091680597047176816544972800
def secondWeilNumerator : Nat :=
  (productionN - 1) ^ 2 + (secondR - 1) * secondP

/-- Individual Weil bounds on all `r-1` nonprincipal modes miss the collision floor by
`127--128` bits at the first production prime. -/
theorem first_weil_collision_ceiling_gap :
    inversionFloor * firstR * 2 ^ 127 < firstWeilNumerator ∧
      firstWeilNumerator < inversionFloor * firstR * 2 ^ 128 := by
  norm_num [inversionFloor, firstWeilNumerator, productionN, firstR, firstP,
    ArkLib.ProximityGap.PrizeShapePrimeP30.P]

/-- The same modewise Weil argument misses by `128--129` bits at the second prime. -/
theorem second_weil_collision_ceiling_gap :
    inversionFloor * secondR * 2 ^ 128 < secondWeilNumerator ∧
      secondWeilNumerator < inversionFloor * secondR * 2 ^ 129 := by
  norm_num [inversionFloor, secondWeilNumerator, productionN, secondR, secondP,
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.P]

/-- The Do Duc--Leung--Schmidt sufficient threshold fails in the opposite direction at the first
production prime.  Since `P = 1 mod firstClassSize`, `ord_firstClassSize(P)=1`; squaring their
condition would require `14^firstClassSize < P^2`. -/
theorem first_cyclotomicNumber_threshold_fails : firstP ^ 2 < 14 ^ firstClassSize := by
  calc
    firstP ^ 2 < (2 ^ 160) ^ 2 := Nat.pow_lt_pow_left (by
      norm_num [firstP, ArkLib.ProximityGap.PrizeShapePrimeP30.P]) (by norm_num)
    _ = 2 ^ (160 * 2) := by rw [pow_mul]
    _ = 2 ^ 320 := by norm_num
    _ < 2 ^ firstClassSize := Nat.pow_lt_pow_right (by norm_num) (by
      norm_num [firstClassSize])
    _ < 14 ^ firstClassSize := Nat.pow_lt_pow_left (by norm_num) (by
      norm_num [firstClassSize])

/-- The same cyclotomic-number threshold is astronomically false at the second production prime. -/
theorem second_cyclotomicNumber_threshold_fails : secondP ^ 2 < 14 ^ secondClassSize := by
  calc
    secondP ^ 2 < (2 ^ 160) ^ 2 := Nat.pow_lt_pow_left (by
      norm_num [secondP, ArkLib.ProximityGap.PrizeShapePrimeP30Second.P]) (by norm_num)
    _ = 2 ^ (160 * 2) := by rw [pow_mul]
    _ = 2 ^ 320 := by norm_num
    _ < 2 ^ secondClassSize := Nat.pow_lt_pow_right (by norm_num) (by
      norm_num [secondClassSize])
    _ < 14 ^ secondClassSize := Nat.pow_lt_pow_left (by norm_num) (by
      norm_num [secondClassSize])

end ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.codeCollision_parseval
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.differenceMode_mul_orderOf_eq_sum_jacobiSum
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.card_characterFiber_le_cyclotomicIntersection
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.projectedKappa_eq_iff_cyclotomicUnit_pow_eq
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.first_weil_collision_ceiling_gap
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedCharacterNoGo.first_cyclotomicNumber_threshold_fails
