/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.DegreeLTDimension
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-! # Degree costs for independent polynomial columns

Multiples of a component and short ordinate multiples of a coprime polar power
are jointly independent. Scalar interpolation on independent polynomial columns
can use a different multiplier degree on each column.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Finset Module
namespace ArkLib.ProximityGap.Frontier.PolarBasisDegreeLoss

variable {K : Type*} [Field K]

/-- A component block and a polar-power block admit no relation with a short
ordinate multiplier on the polar. This also holds over the coordinate function field. -/
theorem separate_blocks (f g A B : K[X]) (a : ℕ) (hf : f ≠ 0)
    (hc : IsCoprime f g) (hB : B.natDegree < f.natDegree)
    (h : f*A + g^a*B=0) : A=0 ∧ B=0 := by
  have hd : f ∣ g^a*B := ⟨-A,by linear_combination h⟩
  have hdiv : f ∣ B := hc.pow_right.dvd_of_dvd_mul_left hd
  have hz : B=0 := by
    by_contra hh
    exact hB.not_ge (natDegree_le_of_dvd hdiv hh)
  rw [hz,mul_zero,add_zero] at h
  exact ⟨(mul_eq_zero.mp h).resolve_left hf,hz⟩

variable {I J : Type*} [Fintype I]

/-- Give each column its own space of polynomial multipliers. -/
def columnMap (C : I → J → K[X]) (r : I → ℕ) :
    (∀ i, degreeLT K (r i)) →ₗ[K] (J → K[X]) where
  toFun p := ∑ i, (p i : K[X]) • C i
  map_add' p q := by simp [add_smul,sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply,SetLike.val_smul,RingHom.id_apply,Finset.smul_sum]
    exact sum_congr rfl fun i _ => smul_assoc ..

/-- Rational independence, restricted to polynomial coefficients, makes each
allowable multiplier coefficient contribute a full independent scalar parameter. -/
theorem column_rank (C : I → J → K[X]) (hC : LinearIndependent K[X] C) (r : I → ℕ) :
    Module.finrank K (LinearMap.range (columnMap C r)) = ∑ i, r i := by
  letI (i : I) : FiniteDimensional K (degreeLT K (r i)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv K (r i)).symm
  have hi : Function.Injective (columnMap C r) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    have hz := Fintype.linearIndependent_iff.mp hC (fun i => (p i : K[X])) hp
    exact funext fun i => Subtype.ext (hz i)
  rw [LinearMap.finrank_range_of_inj hi,Module.finrank_pi_fintype]
  apply sum_congr rfl
  intro i _
  simpa using (degreeLTEquiv K (r i)).finrank_eq

/-- The weighted scalar degree loss is the sum of the individual column
degrees whenever the target scalar window contains each column. -/
theorem weighted_loss (C : I → J → K[X]) (hC : LinearIndependent K[X] C) (d : I → ℕ)
    (s : ℕ) (hh : ∀ i, d i≤s+1) :
    Module.finrank K (LinearMap.range (columnMap C (fun i => s+1-d i))) + ∑ i, d i =
      Fintype.card I*(s+1) := by
  rw [column_rank C hC,← sum_add_distrib]
  calc
    _ = ∑ _i : I, (s+1) := sum_congr rfl (fun i _ => Nat.sub_add_cancel (hh i))
    _ = _ := by simp

#print axioms separate_blocks
#print axioms weighted_loss
end ArkLib.ProximityGap.Frontier.PolarBasisDegreeLoss
