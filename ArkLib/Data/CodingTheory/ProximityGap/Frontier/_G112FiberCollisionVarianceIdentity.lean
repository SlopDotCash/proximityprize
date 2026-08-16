/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86DepthFiveConstantGap

/-!
# G112: exact variance identity for subset-sum collision fibers

Let `a_y` be the size of the fiber over `y`, let `N = ∑ a_y`, and let `q` be the number of target
values.  The exact integer identity

`∑_y (q a_y - N)^2 = q^2 ∑_y a_y^2 - q N^2`

separates the random/uniform collision main term from the centered fiber variance.  Applied to the
five-subset-sum map, `∑ a_y^2` is its raw collision count.  Thus the honest post-G83 depth-five
input is a bound on this centered square sum; no scaling-orbit representative is discarded.

The natural-number consumer avoids division: if the centered square sum is at most
`q * (q*K - N^2)`, then the collision count is at most `K`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity

open scoped BigOperators
open G86DepthFiveConstantGap

/-- Cardinality of the fiber of a finite map. -/
abbrev fiberCount {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (y : Y) : ℕ :=
  Fintype.card {x : X // f x = y}

/-- Fiber counts sum to the cardinality of the source. -/
theorem sum_fiberCount {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) :
    ∑ y, fiberCount f y = Fintype.card X := by
  calc
    ∑ y, fiberCount f y = Fintype.card (Σ y : Y, {x : X // f x = y}) := by
      simpa using (Fintype.card_sigma (fun y : Y => {x : X // f x = y})).symm
    _ = Fintype.card X := Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- Exact centered-square expansion for an arbitrary integer-valued fiber census. -/
theorem centeredFiberSquare_identity
    {Y : Type*} [Fintype Y] (a : Y → ℤ) (N : ℤ)
    (hsum : ∑ y, a y = N) :
    ∑ y, ((Fintype.card Y : ℤ) * a y - N) ^ 2 =
      (Fintype.card Y : ℤ) ^ 2 * ∑ y, (a y) ^ 2 -
        (Fintype.card Y : ℤ) * N ^ 2 := by
  have hcross :
      (∑ y, 2 * ((Fintype.card Y : ℤ) * a y) * N) =
        2 * ((Fintype.card Y : ℤ) * N) * N := by
    calc
      (∑ y, 2 * ((Fintype.card Y : ℤ) * a y) * N) =
          ∑ y, (Fintype.card Y : ℤ) * a y * N * 2 :=
            Finset.sum_congr rfl (fun _ _ => by ring)
      _ = (Fintype.card Y : ℤ) * (∑ y, a y) * N * 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = 2 * ((Fintype.card Y : ℤ) * N) * N := by rw [hsum]; ring
  simp_rw [sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcross]
  push_cast
  ring

/-- Natural-number form specialized to a fiber census with total mass `N`. -/
theorem centeredFiberSquare_identity_nat
    {Y : Type*} [Fintype Y] (a : Y → ℕ) (N : ℕ)
    (hsum : ∑ y, a y = N) :
    ∑ y, ((Fintype.card Y : ℤ) * (a y : ℤ) - N) ^ 2 =
      (Fintype.card Y : ℤ) ^ 2 * (∑ y, (a y) ^ 2 : ℕ) -
        (Fintype.card Y : ℤ) * N ^ 2 := by
  have hsumZ : ∑ y, (a y : ℤ) = (N : ℤ) := by exact_mod_cast hsum
  simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
    centeredFiberSquare_identity (fun y => (a y : ℤ)) (N : ℤ) hsumZ

/-- Division-free variance consumer.  The hypothesis is deliberately written after multiplying
by `q`, which is the form convenient for kernel-checked finite-field cardinal arithmetic. -/
theorem collision_le_of_centeredFiberSquare_le
    {Y : Type*} [Fintype Y] [Nonempty Y] (a : Y → ℕ) (N K : ℕ)
    (hsum : ∑ y, a y = N)
    (hvar : ∑ y, ((Fintype.card Y : ℤ) * (a y : ℤ) - N) ^ 2 ≤
      (Fintype.card Y : ℤ) *
        ((Fintype.card Y : ℤ) * K - N ^ 2)) :
    ∑ y, (a y) ^ 2 ≤ K := by
  rw [centeredFiberSquare_identity_nat a N hsum] at hvar
  have hq : (0 : ℤ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hmul : (Fintype.card Y : ℤ) ^ 2 * (∑ y, (a y) ^ 2 : ℕ) ≤
      (Fintype.card Y : ℤ) ^ 2 * K := by
    nlinarith
  have hcast : (∑ y, (a y) ^ 2 : ℕ) ≤ (K : ℤ) := by
    nlinarith [sq_pos_of_pos hq]
  exact_mod_cast hcast

/-- Direct finite-map specialization: a centered variance certificate bounds the number of
ordered collisions, expressed as the sum of squared fiber sizes. -/
theorem map_collision_le_of_centeredFiberSquare_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (f : X → Y) (K : ℕ)
    (hvar : ∑ y, ((Fintype.card Y : ℤ) * (fiberCount f y : ℤ) -
        Fintype.card X) ^ 2 ≤
      (Fintype.card Y : ℤ) *
        ((Fintype.card Y : ℤ) * K - (Fintype.card X) ^ 2)) :
    ∑ y, (fiberCount f y) ^ 2 ≤ K :=
  collision_le_of_centeredFiberSquare_le (fiberCount f) (Fintype.card X) K
    (sum_fiberCount f) hvar

/-! ## Production depth-five calibration -/

def productionN : ℕ := 2 ^ 30
def productionQ : ℕ := productionN * (2 ^ 128 + 192) + 1
def productionSource : ℕ := productionN.descFactorial 5
def productionWick : ℕ := Nat.doubleFactorial (2 * 110 - 1) * productionN ^ 110
def productionDepthFiveBase : ℕ :=
  ((110 : ℕ).choose 5) ^ 2 * (110 - 5).factorial * productionN ^ (110 - 5)
def productionCollisionCeiling : ℕ := 2 ^ 235

/-- The canonical depth-five envelope accepts the explicit integer collision ceiling. -/
theorem production_collisionCeiling_mul_base_le_wick :
    productionCollisionCeiling * productionDepthFiveBase ≤ productionWick := by
  norm_num [productionCollisionCeiling, productionWick, productionDepthFiveBase,
    productionN, Nat.choose, Nat.factorial, Nat.doubleFactorial]

/-- The uniform collision main term consumes less than half the canonical allowance.  In fact the
actual margin is about 94 bits; the factor two statement is a deliberately stable kernel pin. -/
theorem production_uniform_main_term_twofold_margin :
    2 * productionSource ^ 2 ≤ productionQ * productionCollisionCeiling := by
  norm_num [productionSource, productionN, productionQ, productionCollisionCeiling,
    Nat.descFactorial]

/-- Strong quantitative form: the uniform main term is at least ninety binary orders below the
accepted collision ceiling after clearing the field-cardinality denominator. -/
theorem production_uniform_main_term_ninety_bit_margin :
    2 ^ 90 * productionSource ^ 2 ≤ productionQ * productionCollisionCeiling := by
  norm_num [productionSource, productionN, productionQ, productionCollisionCeiling,
    Nat.descFactorial]

/-- The count supplied by the two-step recurrence `E₅ ≤ n⁴E₃` from a depth-three Wick input
`E₃ ≤ 15n³` lies well below the accepted raw collision ceiling. -/
theorem production_energy_three_route_fits_collision_ceiling :
    15 * productionN ^ 7 ≤ productionCollisionCeiling := by
  norm_num [productionN, productionCollisionCeiling]

/-- Optimistic fifth-energy ceiling corresponding to the best possible squared HBK constant
`C=1`: `E₅ = n^(17/2) = n⁸ * 2¹⁵` because production `n=2³⁰`. -/
def productionOptimisticFifthEnergy : ℕ := productionN ^ 8 * 2 ^ 15

/-- Largest raw unordered-core count certified by the genuine `(5!)²` internal-order quotient
alone.  No scaling orbit is divided out. -/
def productionRawUnorderedCoreCeiling : ℕ := productionOptimisticFifthEnergy / 14400

/-- The raw-scale correction refutes the G91 production interpretation.  Even with the idealized
HBK constant `C=1`, there is an integer `J` satisfying both the genuine internal-order encoding
`14400*J ≤ E₅` and `E₅²=n¹⁷`, but its corrected padded envelope exceeds Wick.  Hence the extra
factor `n` in G91's hypothesis is load-bearing and is exactly the retracted orbit quotient. -/
theorem production_raw_unordered_hbk_C1_countermodel :
    14400 * productionRawUnorderedCoreCeiling ≤ productionOptimisticFifthEnergy ∧
    productionOptimisticFifthEnergy ^ 2 = productionN ^ 17 ∧
    productionWick < correctedEnvelope productionN 110
      productionRawUnorderedCoreCeiling 5 := by
  constructor
  · rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  constructor
  · norm_num [productionOptimisticFifthEnergy, productionN]
  · norm_num [productionRawUnorderedCoreCeiling, productionOptimisticFifthEnergy,
      productionN, productionWick, correctedEnvelope, Nat.doubleFactorial,
      Nat.descFactorial, Nat.factorial]

/-- A centered variance certificate for the ordered injective-five subset-sum map implies that its
full raw collision contribution fits the canonical production depth-five envelope.  No orbit
quotient or discarded scale appears. -/
theorem production_depth_five_of_centered_variance
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (f : X → Y)
    (hX : Fintype.card X = productionSource)
    (hY : Fintype.card Y = productionQ)
    (hvar : ∑ y, ((productionQ : ℤ) * (fiberCount f y : ℤ) -
        productionSource) ^ 2 ≤
      (productionQ : ℤ) * ((productionQ : ℤ) * productionCollisionCeiling -
        productionSource ^ 2)) :
    (∑ y, (fiberCount f y) ^ 2) * productionDepthFiveBase ≤ productionWick := by
  have hvar' : ∑ y, ((Fintype.card Y : ℤ) * (fiberCount f y : ℤ) -
        Fintype.card X) ^ 2 ≤
      (Fintype.card Y : ℤ) * ((Fintype.card Y : ℤ) * productionCollisionCeiling -
        (Fintype.card X) ^ 2) := by
    simpa only [hX, hY] using hvar
  have hcollision : ∑ y, (fiberCount f y) ^ 2 ≤ productionCollisionCeiling :=
    map_collision_le_of_centeredFiberSquare_le f productionCollisionCeiling hvar'
  calc
    (∑ y, (fiberCount f y) ^ 2) * productionDepthFiveBase ≤
        productionCollisionCeiling * productionDepthFiveBase := by gcongr
    _ ≤ productionWick := production_collisionCeiling_mul_base_le_wick

end ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.centeredFiberSquare_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.collision_le_of_centeredFiberSquare_le
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.map_collision_le_of_centeredFiberSquare_le
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.production_uniform_main_term_twofold_margin
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.production_uniform_main_term_ninety_bit_margin
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.production_energy_three_route_fits_collision_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.production_raw_unordered_hbk_C1_countermodel
#print axioms
  ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity.production_depth_five_of_centered_variance
