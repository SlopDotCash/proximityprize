/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R35TransformRingHom

/-!
# LANE B2 (#466 round 36): Jacobi powers are transforms of `⊛`-powers — the bridge between
  the two convolution layers

The tower has two convolution structures: additive (`∗` on `ℤ/m`, rounds 21–27) and
multiplicative (`⊛` on `F`, round 35), in Fourier duality through the λ-transform.  This
brick lands the bridge:

* `jacobiCoeff_eq_lamTransform` — `J = c_{χ(1−·)}`: the Jacobi sequence IS a transform;
* **`jacobiCoeff_pow`** — `J_j^k = c_{f^{⊛k}}(j)` with `f = χ(1−·)` (induction via the
  round-35 ring hom).

Hence the sextic (r = 3) object `∑_c ‖(J^{∗3})(c)‖²` and the `⊛`-power correlations of the
weights are the SAME family through the duality — the assembly of the r = 3 matching
decomposition is bookkeeping inside one calculus, and the named top input can be stated on
either side.  Pure algebra.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 36, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R36JacobiPowers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation
open ArkLib.ProximityGap.Frontier.R35TransformRingHom

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The base weight of the Jacobi sequence, zero-patched at the origin so the round-35
ring hom applies without side conditions: `f₀(t) = χ(1−t)` for `t ≠ 0`, `f₀(0) = 0`. -/
noncomputable def jacobiWeight (χ : F → ℂ) : F → ℂ :=
  fun t => if t = 0 then 0 else χ (1 - t)

/-- The `k`-fold `⊛`-power of a weight (`k ≥ 1`). -/
noncomputable def mulConvPow (f : F → ℂ) : ℕ → F → ℂ
  | 0 => f
  | k + 1 => mulConv (mulConvPow f k) f

/-- **The Jacobi sequence is a transform**: `J_j = c_{f₀}(j) + χ(1)·λ_j(0)`-free form —
exactly `J_j = lamTransform lam (jacobiWeight χ) j + χ 1 · lam j 0`… simplified: since
`λ_j(0) = 0`, `J_j = c_{f₀}(j)` up to the `t = 0` term `λ_j(0)·χ(1) = 0`. -/
theorem jacobiCoeff_eq_lamTransform (hfam : SubgroupDualFamily G m lam) (j : ZMod m) :
    jacobiCoeff χ lam j = lamTransform lam (jacobiWeight χ) j := by
  rw [jacobiCoeff, lamTransform]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases ht : t = 0
  · subst ht
    rw [hfam.map_zero j]
    simp [jacobiWeight]
  · simp only [jacobiWeight, if_neg ht]
    ring

/-- `jacobiWeight` vanishes at the origin (the ring-hom side condition). -/
theorem jacobiWeight_zero : jacobiWeight χ 0 = 0 := by simp [jacobiWeight]

/-- `mulConvPow` preserves the origin-vanishing (each step is a `⊛` with the base). -/
theorem mulConvPow_zero (hχ0 : jacobiWeight χ 0 = 0) :
    ∀ k, mulConvPow (jacobiWeight χ) k 0 = 0 := by
  intro k
  induction k with
  | zero => exact hχ0
  | succ n ih =>
    simp only [mulConvPow, mulConv]
    refine Finset.sum_eq_zero (fun z hz => ?_)
    have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
    rw [mul_zero]
    simp [jacobiWeight]

/-- **JACOBI POWERS ARE TRANSFORMS OF `⊛`-POWERS (round-36 main theorem)**:
`J_j^{k+1} = c_{f₀^{⊛(k+1)}}(j)`. -/
theorem jacobiCoeff_pow (hfam : SubgroupDualFamily G m lam) (j : ZMod m) :
    ∀ k : ℕ, jacobiCoeff χ lam j ^ (k + 1)
      = lamTransform lam (mulConvPow (jacobiWeight χ) k) j := by
  intro k
  induction k with
  | zero =>
    rw [pow_one]
    exact jacobiCoeff_eq_lamTransform hfam j
  | succ n ih =>
    rw [pow_succ, ih, jacobiCoeff_eq_lamTransform (χ := χ) hfam j]
    rw [lamTransform_mul hfam _ _ (mulConvPow_zero (jacobiWeight_zero) n) j]
    rfl

end ArkLib.ProximityGap.Frontier.R36JacobiPowers

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R36JacobiPowers.jacobiCoeff_eq_lamTransform
#print axioms ArkLib.ProximityGap.Frontier.R36JacobiPowers.jacobiCoeff_pow
