/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCenteredTranslateConeDuality
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Cyclotomic intersection-number integrality: exact coupling and its production limit

This file attacks the arithmetic successor left by `_BGKCyclotomicKreinSchurNoGo`.  For finite
sets `S,T` in a finite field, the coefficient

`p_ST(z) = #{x in S : z-x in T}`

is the literal intersection number of the two translation relations.  We prove its exact
Bose--Mesner coupling: the additive-character transform of `p_ST` is the product of the two
periods.  Thus integrality is not an analogy or a positivity relaxation; these are the actual
nonnegative integer structure constants.

For two cyclotomic classes of size `n`, orbit invariance makes `p_ST` constant on each target
class and double counting gives total class-coefficient mass `n`.  Cauchy--Davenport excludes
support on one class, but no more: the standard integral row constraints allow the extremal split
`(n-1,1)`.  At `n=2^30`, this forces only one unit of leakage.  Reducing the primitive Wick
coefficient `135135` to `126871` instead requires at least

`ceil(8264 * 2^30 / 135135) = 65663244`

units of leakage, strictly between `2^25` and `2^26`.  Hence intersection-number integrality,
the exact row mass, and even the sharp Cauchy--Davenport support obstruction are quantitatively
25--26 bits too weak at both certified production primes.  A successful association-scheme
argument must use the *values and correlated placement* of many cyclotomic numbers, not merely
their integrality, row sums, or support size.  Issue #466.

Primary source for the sumset input: Cauchy--Davenport (as formalized in Mathlib's
`Combinatorics.Additive.CauchyDavenport`).
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

open Finset BigOperators
open scoped Pointwise

namespace ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit

/-! ## Literal integral structure constants and the character coupling -/

/-- Additive convolution, reproduced locally so this scratch lane does not depend on another
unbuilt scratch module. -/
def additiveConvolution {F R : Type*} [AddCommGroup F] [Fintype F]
    [Semiring R] (w v : F → R) (b : F) : R :=
  ∑ a : F, w a * v (b - a)

/-- Fourier synthesis against an additive character. -/
def characterKernel {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] (psi : AddChar F R) (w : F → R) (x : F) : R :=
  ∑ b : F, w b * psi (b * x)

/-- Pointwise products of character kernels are transforms of additive convolutions. -/
theorem characterKernel_additiveConvolution {F R : Type*}
    [CommRing F] [Fintype F] [CommRing R]
    (psi : AddChar F R) (w v : F → R) (x : F) :
    characterKernel psi (additiveConvolution w v) x =
      characterKernel psi w x * characterKernel psi v x := by
  classical
  unfold characterKernel additiveConvolution
  calc
    (∑ b : F, (∑ a : F, w a * v (b - a)) * psi (b * x)) =
        ∑ b : F, ∑ a : F, w a * v (b - a) * psi (b * x) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
    _ = ∑ a : F, ∑ b : F, w a * v (b - a) * psi (b * x) := by
      rw [Finset.sum_comm]
    _ = ∑ a : F, ∑ c : F, w a * v c * psi ((a + c) * x) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      symm
      exact Fintype.sum_equiv (Equiv.addLeft a)
        (fun c => w a * v c * psi ((a + c) * x))
        (fun b => w a * v (b - a) * psi (b * x)) (fun c => by simp)
    _ = ∑ a : F, ∑ c : F, (w a * psi (a * x)) * (v c * psi (c * x)) := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
      rw [show (a + c) * x = a * x + c * x by ring, AddChar.map_add_eq_mul]
      ring
    _ = (∑ a : F, w a * psi (a * x)) * ∑ c : F, v c * psi (c * x) := by
      rw [Finset.sum_mul_sum]

/-- Indicator of a finite set, valued in the coefficient ring. -/
def finsetIndicator {F R : Type*} [DecidableEq F] [Zero R] [One R]
    (S : Finset F) (x : F) : R :=
  if x ∈ S then 1 else 0

/-- The literal translation-scheme intersection number at `z`. -/
def intersectionNumber {F : Type*} [Sub F] [DecidableEq F]
    (S T : Finset F) (z : F) : Nat :=
  (S.filter fun x => z - x ∈ T).card

/-- Additive convolution of indicators is the cast of the integer intersection number. -/
theorem additiveConvolution_indicator_eq_intersectionNumber
    {F R : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F] [Semiring R]
    (S T : Finset F) (z : F) :
    additiveConvolution (finsetIndicator S) (finsetIndicator T) z =
      (intersectionNumber S T z : R) := by
  classical
  unfold additiveConvolution finsetIndicator intersectionNumber
  calc
    (∑ x : F, (if x ∈ S then 1 else 0) * (if z - x ∈ T then 1 else 0)) =
        ∑ x : F, if x ∈ S ∧ z - x ∈ T then (1 : R) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : x ∈ S <;> by_cases ht : z - x ∈ T <;> simp [hx, ht]
    _ = ((Finset.univ.filter fun x : F => x ∈ S ∧ z - x ∈ T).card : R) :=
      Finset.sum_boole (R := R) (fun x : F => x ∈ S ∧ z - x ∈ T) Finset.univ
    _ = ((S.filter fun x => z - x ∈ T).card : R) := by
      congr 2
      ext x
      simp

/-- The character kernel of an indicator is the ordinary finite-set character sum. -/
theorem characterKernel_indicator
    {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R]
    (psi : AddChar F R) (S : Finset F) (x : F) :
    characterKernel psi (finsetIndicator S) x = ∑ s ∈ S, psi (s * x) := by
  classical
  simp [characterKernel, finsetIndicator]

/-- **Exact Bose--Mesner/period coupling.**  The transform of the nonnegative integral
intersection row is the product of the transforms of its two relations. -/
theorem characterKernel_intersectionNumber
    {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R]
    (psi : AddChar F R) (S T : Finset F) (x : F) :
    (∑ z : F, (intersectionNumber S T z : R) * psi (z * x)) =
      (∑ s ∈ S, psi (s * x)) * (∑ t ∈ T, psi (t * x)) := by
  rw [← characterKernel_indicator psi S x, ← characterKernel_indicator psi T x,
    ← characterKernel_additiveConvolution]
  unfold characterKernel
  congr 1
  funext z
  rw [additiveConvolution_indicator_eq_intersectionNumber]

/-! ## Exact mass and orbit coupling -/

/-- The intersection row has total integer mass `|S||T|`, by exact double counting. -/
theorem sum_intersectionNumber
    {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]
    (S T : Finset F) :
    ∑ z : F, intersectionNumber S T z = S.card * T.card := by
  classical
  calc
    (∑ z : F, intersectionNumber S T z) =
        ∑ z : F, ∑ x ∈ S, if z - x ∈ T then 1 else 0 := by
      simp [intersectionNumber]
    _ = ∑ x ∈ S, ∑ z : F, if z - x ∈ T then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _x ∈ S, T.card := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hsum := Fintype.sum_equiv (Equiv.subRight x)
        (fun z : F => if z - x ∈ T then (1 : Nat) else 0)
        (fun y : F => if y ∈ T then (1 : Nat) else 0) (fun _ => rfl)
      simpa using hsum
    _ = S.card * T.card := by simp

/-- Multiplying both source relations and the target by a subgroup element preserves the exact
intersection number. -/
theorem intersectionNumber_mul_invariant
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S T : Finset F) {g : F} (hg : g ≠ 0) (z : F) :
    intersectionNumber (S.image fun x => g * x) (T.image fun y => g * y) (g * z) =
      intersectionNumber S T z := by
  classical
  unfold intersectionNumber
  symm
  let e : F ≃ F := Equiv.mulLeft₀ g hg
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_image.mpr ⟨x, hx.1, rfl⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨z - x, hx.2, ?_⟩
    change g * (z - x) = g * z - g * x
    ring
  · intro x hx y hy hxy
    exact e.injective hxy
  · intro y hy
    simp only [Finset.mem_filter] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy.1
    refine ⟨x, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨hx, ?_⟩
    obtain ⟨t, ht, hzt⟩ := Finset.mem_image.mp hy.2
    have : z - x = t := by
      apply (mul_left_cancel₀ hg)
      calc
        g * (z - x) = g * z - g * x := by ring
        _ = g * t := hzt.symm
    exact this ▸ ht

/-- If both source relations are stable under a multiplier, then the target intersection row is
constant along that multiplier orbit.  This is the literal cyclotomic-class coupling. -/
theorem intersectionNumber_target_orbit_invariant
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S T : Finset F) {g : F} (hg : g ≠ 0)
    (hS : S.image (fun x => g * x) = S)
    (hT : T.image (fun y => g * y) = T) (z : F) :
    intersectionNumber S T (g * z) = intersectionNumber S T z := by
  calc
    intersectionNumber S T (g * z) =
        intersectionNumber (S.image fun x => g * x) (T.image fun y => g * y) (g * z) := by
      rw [hS, hT]
    _ = intersectionNumber S T z := intersectionNumber_mul_invariant S T hg z

/-! ## Cauchy--Davenport gives only a two-cell support obstruction -/

/-- If three sets have cardinalities `n,n,n` in a prime field with `2n-1<p`, the sumset of the
first two cannot fit inside the third.  For cyclotomic classes this rules out a one-class product
row, but it gives no quantitative balance between the two classes that must occur. -/
theorem cauchyDavenport_excludes_one_cell
    {p n : Nat} (hp : p.Prime) (S T O : Finset (ZMod p))
    (hS : S.card = n) (hT : T.card = n) (hO : O.card = n)
    (hn : 2 ≤ n) (hsmall : 2 * n - 1 < p) :
    ¬ (S + T : Finset (ZMod p)) ⊆ O := by
  intro hsub
  have hSne : S.Nonempty := Finset.card_pos.mp (hS.symm ▸ (by omega : 0 < n))
  have hTne : T.Nonempty := Finset.card_pos.mp (hT.symm ▸ (by omega : 0 < n))
  have hcd := ZMod.cauchy_davenport hp hSne hTne
  have hmin : min p (S.card + T.card - 1) = 2 * n - 1 := by
    rw [hS, hT, min_eq_right]
    · omega
    · omega
  rw [hmin] at hcd
  have hcard := Finset.card_le_card hsub
  rw [hO] at hcard
  omega

/-! ## The sharp integral relaxation and the production deficit -/

/-- The standard one-row information retained from cyclotomic integrality, the exact pair ledger,
and Cauchy--Davenport: nonnegative integer coefficients of total mass `n`, occupying at least two
target classes. -/
structure StandardIntegralRow {k : Nat} (n : Nat) (c : Fin k → Nat) : Prop where
  mass : ∑ i, c i = n
  two_support : 2 ≤ (Finset.univ.filter fun i => c i ≠ 0).card

/-- Dividing the exact pair ledger `n * sum c = n^2` by the class size gives row mass `n`.
This is the arithmetic passage from pointwise intersection numbers to Bose--Mesner structure
constants. -/
theorem classCoefficient_mass_of_pair_ledger
    {k n : Nat} (c : Fin k → Nat) (hn : 0 < n)
    (hledger : n * ∑ i, c i = n * n) :
    ∑ i, c i = n := by
  exact Nat.eq_of_mul_eq_mul_left (by omega) hledger

/-- The extremal two-cell integral row allowed by total mass plus Cauchy--Davenport support. -/
def twoCellRow (n : Nat) : Fin 2 → Nat
  | ⟨0, _⟩ => n - 1
  | ⟨1, _⟩ => 1

/-- Its coefficient mass is exactly `n`. -/
theorem twoCellRow_mass (n : Nat) (hn : 0 < n) :
    ∑ i : Fin 2, twoCellRow n i = n := by
  rw [Fin.sum_univ_two]
  simp [twoCellRow]
  omega

/-- Both cells are occupied when `n>=2`. -/
theorem twoCellRow_both_positive (n : Nat) (hn : 2 ≤ n) :
    0 < twoCellRow n 0 ∧ 0 < twoCellRow n 1 := by
  simp [twoCellRow]
  omega

/-- The `(n-1,1)` row satisfies every standard integral-row constraint, so those constraints
cannot force any stronger quantitative spreading. -/
theorem twoCellRow_standard (n : Nat) (hn : 2 ≤ n) :
    StandardIntegralRow n (twoCellRow n) := by
  refine ⟨twoCellRow_mass n (by omega), ?_⟩
  have hall : (Finset.univ.filter fun i : Fin 2 => twoCellRow n i ≠ 0) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    fin_cases i
    · simp [twoCellRow]
      omega
    · simp [twoCellRow]
  rw [hall]
  norm_num

/-- The dominant cell retains all but one unit of the integral row mass. -/
theorem twoCellRow_dominant (n : Nat) : twoCellRow n 0 = n - 1 := by
  rfl

/-- Production subgroup order. -/
def productionN : Nat := 2 ^ 30

/-- First certified production prime. -/
def productionP1 : Nat := productionN * (2 ^ 128 + 192) + 1

/-- Second certified production prime. -/
def productionP2 : Nat := productionN * (2 ^ 129 + 13) + 1

/-- Exact integral leakage required to replace `135135` by `126871`. -/
def requiredLeakage : Nat := (8264 * productionN + 135135 - 1) / 135135

/-- The named production moduli are exactly the two independently certified primes. -/
theorem production_prime_certificates :
    productionP1.Prime ∧ productionP2.Prime := by
  constructor
  · simpa [productionP1, productionN, ArkLib.ProximityGap.PrizeShapePrimeP30.P] using
      ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P
  · simpa [productionP2, productionN, ArkLib.ProximityGap.PrizeShapePrimeP30Second.P] using
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P

/-- Cauchy--Davenport is in its unsaturated `2n-1` regime at both production primes. -/
theorem production_cauchyDavenport_windows :
    2 * productionN - 1 < productionP1 ∧
      2 * productionN - 1 < productionP2 := by
  norm_num [productionN, productionP1, productionP2]

/-- The primitive coefficient gap is exactly `8264`. -/
theorem primitive_coefficient_gap : (135135 : Nat) - 126871 = 8264 := by
  norm_num

/-- The exact least integer leakage is `65,663,244`, between 25 and 26 bits. -/
theorem requiredLeakage_exact : requiredLeakage = 65663244 := by
  norm_num [requiredLeakage, productionN]

theorem requiredLeakage_bit_window :
    2 ^ 25 < requiredLeakage ∧ requiredLeakage < 2 ^ 26 := by
  norm_num [requiredLeakage, productionN]

/-- One unit of Cauchy--Davenport-forced leakage is insufficient by a factor between `2^25` and
`2^26`. -/
theorem one_unit_leakage_misses_by_25_26_bits :
    2 ^ 25 < requiredLeakage / 1 ∧ requiredLeakage / 1 < 2 ^ 26 := by
  simpa using requiredLeakage_bit_window

/-- Equivalently, the legal concentration `(n-1)/n` is still strictly above the permitted
primitive ratio `126871/135135`. -/
theorem twoCell_concentration_exceeds_primitive_allowance :
    126871 * productionN < 135135 * (productionN - 1) := by
  norm_num [productionN]

/-- **Concrete countermodel to the standard intersection-row program.**  There is an integral
row of the correct production mass and Cauchy--Davenport support whose dominant class exceeds the
full primitive allowance.  Therefore these constraints alone cannot supply even part of the
required `8264` coefficient saving. -/
theorem standard_integral_row_does_not_force_primitive_ratio :
    ∃ c : Fin 2 → Nat,
      StandardIntegralRow productionN c ∧
        126871 * productionN < 135135 * c 0 := by
  refine ⟨twoCellRow productionN,
    twoCellRow_standard productionN (by norm_num [productionN]), ?_⟩
  exact twoCell_concentration_exceeds_primitive_allowance

/-- The exact rounding certificate: `requiredLeakage` is the least integer `L` for which
`135135*L >= 8264*n`. -/
theorem requiredLeakage_is_least :
    135135 * (requiredLeakage - 1) < 8264 * productionN ∧
      8264 * productionN ≤ 135135 * requiredLeakage := by
  norm_num [requiredLeakage, productionN]

/-- Consolidated two-prime no-go.  The actual primes are certified and Cauchy--Davenport rules
out one cell, but the extremal integral two-cell row leaks only one unit against the exact
`65,663,244` units required by the primitive depth-seven coefficient. -/
theorem cyclotomic_intersection_integrality_boundary :
    productionP1.Prime ∧ productionP2.Prime ∧
      2 * productionN - 1 < productionP1 ∧
      2 * productionN - 1 < productionP2 ∧
      (∑ i : Fin 2, twoCellRow productionN i) = productionN ∧
      0 < twoCellRow productionN 0 ∧ 0 < twoCellRow productionN 1 ∧
      requiredLeakage = 65663244 ∧
      2 ^ 25 < requiredLeakage ∧ requiredLeakage < 2 ^ 26 := by
  exact ⟨production_prime_certificates.1, production_prime_certificates.2,
    production_cauchyDavenport_windows.1, production_cauchyDavenport_windows.2,
    twoCellRow_mass productionN (by norm_num [productionN]),
    (twoCellRow_both_positive productionN (by norm_num [productionN])).1,
    (twoCellRow_both_positive productionN (by norm_num [productionN])).2,
    requiredLeakage_exact, requiredLeakage_bit_window.1, requiredLeakage_bit_window.2⟩

end ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit

/-! ## Axiom audit (expected: standard axioms only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit.characterKernel_intersectionNumber
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit.cauchyDavenport_excludes_one_cell
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit.standard_integral_row_does_not_force_primitive_ratio
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicIntersectionIntegralityAudit.cyclotomic_intersection_integrality_boundary
