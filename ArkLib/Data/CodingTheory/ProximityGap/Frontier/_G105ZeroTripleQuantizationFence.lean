/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G104DepthSixStratifiedConsumer
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultant
import ArkLib.Data.CodingTheory.ProximityGap.CubicSupplyCosetBridge
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicCapstone

/-!
# G105: the G104 zero-triple hypothesis is exact accident-freeness

G104 consumes `zeroTripleCount S ≤ 2^22` at the production cardinality `|S|=2^30`.
For a root-of-unity subgroup, the ordered zero-sum triple count is quantized in packets of
`|S|`: scaling a solution by the subgroup gives the exact identity

`zeroTripleCount S = |S| * repCount S 1`.

Consequently the G104 numerical hypothesis is equivalent to `zeroTripleCount S = 0`; it is
not a soft Stepanov-scale concentration estimate.  Any single characteristic-p wraparound
triple already contributes at least `2^30` ordered triples and violates the `2^22` budget by
8 bits.  Thus the remaining depth-six input is the prime-specific accident-freeness statement
`repCount S 1 = 0`, alongside primitive-quad concentration.

For the literal root set `μ_n`, this file also identifies the count with the existing BGK
intersection kernel and discharges G104's zero-triple input from polynomial coprimality of
`X^n-1` and `(X+1)^n-1`.  This is an exact resultant certificate, not an estimate.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G105ZeroTripleQuantizationFence

open Finset Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.Frontier.G104DepthSixStratifiedConsumer
open ProximityGap.Cubic

variable {F : Type*} [Field F] [DecidableEq F]

/-- G104's ordered triple count is the existing cubic-supply `zeroSumTriples`. -/
theorem zeroTripleCount_eq_zeroSumTriples (S : Finset F) :
    zeroTripleCount S = zeroSumTriples S := by
  classical
  unfold zeroTripleCount zeroSumTriples
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_product, repCount_eq_sum_pairs]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact if_congr (by constructor <;> intro h <;> linear_combination h) rfl rfl

/-- Exact packetization of G104's count on a root-of-unity subgroup. -/
theorem zeroTripleCount_eq_card_mul_repCount_one
    {S : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hSmem : ∀ z, z ∈ S ↔ z ^ n = 1) (hneg : ∀ x ∈ S, -x ∈ S) :
    zeroTripleCount S = S.card * repCount S 1 := by
  rw [zeroTripleCount_eq_zeroSumTriples,
    ArkLib.ProximityGap.AdditiveEnergyRepBound.zeroSumTriples_eq_card_mul_repCount_one
      hn hSmem hneg]

/-- At production cardinality, G104's `2^22` hypothesis forces exact triple-freeness. -/
theorem production_zeroTriple_eq_zero
    {S : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hSmem : ∀ z, z ∈ S ↔ z ^ n = 1) (hneg : ∀ x ∈ S, -x ∈ S)
    (hcard : S.card = 2 ^ 30) (hbound : zeroTripleCount S ≤ 2 ^ 22) :
    zeroTripleCount S = 0 := by
  rw [zeroTripleCount_eq_card_mul_repCount_one hn hSmem hneg, hcard] at hbound ⊢
  omega

/-- Conversely, exact triple-freeness trivially supplies G104's numerical input. -/
theorem production_zeroTriple_bound_iff_zero
    {S : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hSmem : ∀ z, z ∈ S ↔ z ^ n = 1) (hneg : ∀ x ∈ S, -x ∈ S)
    (hcard : S.card = 2 ^ 30) :
    zeroTripleCount S ≤ 2 ^ 22 ↔ zeroTripleCount S = 0 := by
  constructor
  · exact production_zeroTriple_eq_zero hn hSmem hneg hcard
  · intro h
    rw [h]
    norm_num

/-- On the literal root set, G104's triple count is exactly the BGK kernel packet count. -/
theorem zeroTripleCount_nthRoots_eq_card_mul_bgk {n : ℕ} (hn : 0 < n) :
    zeroTripleCount (nthRootsFinset n (1 : F)) =
      (nthRootsFinset n (1 : F)).card *
        ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount (F := F) n := by
  exact ArkLib.ProximityGap.AdditiveEnergyKernel.tripleZero_eq_card_mul_bgk n hn

/-- Polynomial coprimality excludes every characteristic-p triple accident on `μ_n`. -/
theorem zeroTripleCount_nthRoots_eq_zero_of_coprime {n : ℕ} (hn : 0 < n) (hne : Even n)
    (hcop : IsCoprime (Polynomial.X ^ n - 1 : Polynomial F)
      ((Polynomial.X + 1) ^ n - 1)) :
    zeroTripleCount (nthRootsFinset n (1 : F)) = 0 := by
  rw [zeroTripleCount_nthRoots_eq_card_mul_bgk hn,
    ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_eq_zero_of_coprime hn hne hcop,
    Nat.mul_zero]

/-- Hence the exact resultant certificate supplies G104's numerical zero-triple budget. -/
theorem production_zeroTriple_bound_of_coprime {n : ℕ} (hn : 0 < n) (hne : Even n)
    (hcop : IsCoprime (Polynomial.X ^ n - 1 : Polynomial F)
      ((Polynomial.X + 1) ^ n - 1)) :
    zeroTripleCount (nthRootsFinset n (1 : F)) ≤ 2 ^ 22 := by
  rw [zeroTripleCount_nthRoots_eq_zero_of_coprime hn hne hcop]
  norm_num

#print axioms zeroTripleCount_eq_zeroSumTriples
#print axioms zeroTripleCount_eq_card_mul_repCount_one
#print axioms production_zeroTriple_eq_zero
#print axioms production_zeroTriple_bound_iff_zero
#print axioms zeroTripleCount_nthRoots_eq_card_mul_bgk
#print axioms zeroTripleCount_nthRoots_eq_zero_of_coprime
#print axioms production_zeroTriple_bound_of_coprime

end ArkLib.ProximityGap.Frontier.G105ZeroTripleQuantizationFence
