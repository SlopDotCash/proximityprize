/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80HKFoldProductEnergy

/-!
# G80G: weld k-fold product energy to a pure-Nat divisor moment

G80H removes the subgroup combinatorics from the k-fold product method:
`|A|^(2k) ≤ |H| Eₖ(A)` in the no-wrap range.  This file identifies a canonical pure-integer
majorant for the remaining energy.

For `y ≤ W^k`, `boundedFactorCount W k y` counts ordered factorizations of `y` into `k`
factors in `[1,W]`.  Its second moment over `1 ≤ y ≤ W^k` dominates `Eₖ(A)` whenever
`A ⊆ [1,W]`.  Thus any estimate for this one Nat-valued moment plugs directly into the
generic subgroup consumer.

This is an exact reduction, not the missing analytic estimate.  The prize-facing residual is
now the growing-`k` bound for `boundedFactorSecondMoment`.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G80GKFoldDivisorMomentWeld

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G80HKFoldProductEnergy

/-- Number of ordered `k`-factor representations of `y`, with every factor in `[1,W]`. -/
def boundedFactorCount (W k y : ℕ) : ℕ :=
  #((piFinset fun _ : Fin k => Finset.Icc 1 W).filter fun x => tupleProduct x = y)

/-- The bounded k-fold divisor second moment up to the largest possible product `W^k`. -/
def boundedFactorSecondMoment (W k : ℕ) : ℕ :=
  ∑ y ∈ Finset.Icc 1 (W ^ k), boundedFactorCount W k y ^ 2

/-- Products of tuples from a positive interval subset lie in `[1,W^k]`. -/
theorem productImage_subset_Icc {A : Finset ℕ} {W k : ℕ}
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W) :
    productImage A k ⊆ Finset.Icc 1 (W ^ k) := by
  classical
  intro y hy
  rw [productImage, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Finset.mem_Icc]
  constructor
  · unfold tupleProduct
    exact Finset.one_le_prod (fun i _ => (hA _ (Fintype.mem_piFinset.mp hx i)).1)
  · exact tupleProduct_le_pow (fun a ha => (hA a ha).2) hx

/-- A product fiber over `A^k` injects into the corresponding bounded factor fiber. -/
theorem card_productFiber_le_boundedFactorCount
    {A : Finset ℕ} {W k : ℕ} (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W) (y : ℕ) :
    #((piFinset fun _ : Fin k => A).filter fun x => tupleProduct x = y) ≤
      boundedFactorCount W k y := by
  classical
  unfold boundedFactorCount
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro x hx
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact hA _ (Fintype.mem_piFinset.mp hx i)

/-- **Exact k-fold divisor-moment weld.** If `A ⊆ [1,W]`, its k-fold multiplicative energy
is bounded by the full bounded factor second moment through `W^k`. -/
theorem kMulEnergy_le_boundedFactorSecondMoment
    (A : Finset ℕ) {W k : ℕ} (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W) :
    kMulEnergy A k ≤ boundedFactorSecondMoment W k := by
  classical
  rw [kMulEnergy_eq_sum_sq_fibers, boundedFactorSecondMoment]
  let r : ℕ → ℕ := fun y =>
    #((piFinset fun _ : Fin k => A).filter fun x => tupleProduct x = y)
  calc
    ∑ y ∈ productImage A k, r y ^ 2
        ≤ ∑ y ∈ productImage A k, boundedFactorCount W k y ^ 2 := by
          refine Finset.sum_le_sum fun y _ => Nat.pow_le_pow_left ?_ 2
          exact card_productFiber_le_boundedFactorCount hA y
    _ ≤ ∑ y ∈ Finset.Icc 1 (W ^ k), boundedFactorCount W k y ^ 2 :=
      Finset.sum_le_sum_of_subset (productImage_subset_Icc hA)

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **Assembled k-fold Nat-moment consumer.** All finite-field content is discharged; a bound
on the pure-Nat `boundedFactorSecondMoment W k` now yields the corresponding subgroup interval
bound. -/
theorem card_pow_two_mul_le_subgroup_mul_boundedFactorSecondMoment
    (H : Finset (ZMod p)) (hone : 1 ∈ H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    {A : Finset ℕ} {W k : ℕ}
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W ∧ ((a : ℕ) : ZMod p) ∈ H)
    (hW : W ^ k < p) :
    A.card ^ (2 * k) ≤ H.card * boundedFactorSecondMoment W k := by
  have hconsumer : A.card ^ (2 * k) ≤ H.card * kMulEnergy A k :=
    card_pow_two_mul_le_subgroup_mul_kMulEnergy H hone hmul
      (fun a ha => ⟨(hA a ha).2.1, (hA a ha).2.2⟩) hW
  exact hconsumer.trans (Nat.mul_le_mul_left _
    (kMulEnergy_le_boundedFactorSecondMoment A (fun a ha => ⟨(hA a ha).1, (hA a ha).2.1⟩)))

end ArkLib.ProximityGap.Frontier.G80GKFoldDivisorMomentWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80GKFoldDivisorMomentWeld.productImage_subset_Icc
#print axioms
  ArkLib.ProximityGap.Frontier.G80GKFoldDivisorMomentWeld.kMulEnergy_le_boundedFactorSecondMoment
#print axioms
  ArkLib.ProximityGap.Frontier.G80GKFoldDivisorMomentWeld.card_pow_two_mul_le_subgroup_mul_boundedFactorSecondMoment
