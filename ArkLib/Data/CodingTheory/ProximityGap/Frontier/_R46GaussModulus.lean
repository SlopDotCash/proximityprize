/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R45GaussRatio

/-!
# LANES A+B (#466 round 46): the MODULUS LAW — `‖𝔤_j‖² = q` for every `j ≠ 0`

The quantitative half of the round-45 weld: the Gauss coefficients of the dual family have
exact modulus `√q` off the trivial index —

  **`gaussCoeff_mul_conj`** :  `𝔤_j · conj(𝔤_j) = q`   (`j ≠ 0`),

by the classical orthogonality argument (reindex `x = y·t`, unit modulus of `λ_j`, punctured
character sums).  Consequences: (i) with `gauss_ratio` (r45) and `‖g(χ)‖ = √q` (r17-class),
`‖J_j‖ = ‖𝔤_j‖·‖g(χ)‖/‖𝔤^{λχ}_j‖ = √q` — the two sequences' entanglement is by EXACT unit
twists, so every family-cancellation statement transfers between the towers with NO loss of
constants; (ii) the A-side tower's Parseval and calibration constants are pinned exactly as
the B-side's were (r20/r23).  The unification is now quantitative.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 46, LANES A+B.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R46GaussModulus

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R24InvolutionNoGo
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity
open ArkLib.ProximityGap.Frontier.R43GaussUnification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **THE MODULUS LAW (round-46 main theorem)**: `𝔤_j·conj(𝔤_j) = q` for `j ≠ 0`. -/
theorem gaussCoeff_mul_conj (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {j : ZMod m} (hj : j ≠ 0) :
    gaussCoeff lam ψ j * (starRingEnd ℂ) (gaussCoeff lam ψ j)
      = (Fintype.card F : ℂ) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconjψ : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hconjg : (starRingEnd ℂ) (gaussCoeff lam ψ j)
      = ∑ y : F, (starRingEnd ℂ) (lam j y) * ψ (-y) := by
    rw [gaussCoeff, map_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [map_mul, hconjψ y]
  rw [hconjg, gaussCoeff, Finset.sum_mul_sum]
  -- Σ_{x,y} λ_j(x)·conj(λ_j(y))·ψ(x−y); swap to y-outer, reindex x = y·t per y ≠ 0
  have hterm : ∀ x y : F, (lam j x * ψ x) * ((starRingEnd ℂ) (lam j y) * ψ (-y))
      = lam j x * (starRingEnd ℂ) (lam j y) * ψ (x - y) := by
    intro x y
    rw [show x - y = x + -y from by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hterm x y))]
  rw [Finset.sum_comm]
  -- y = 0 row: conj(λ_j(0)) = 0
  have hy0 : ∑ x : F, lam j x * (starRingEnd ℂ) (lam j (0:F)) * ψ (x - 0) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [hfam.map_zero j]
    simp
  rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
    (f := fun y => ∑ x : F, lam j x * (starRingEnd ℂ) (lam j y) * ψ (x - y)) (by
      simpa using hy0)]
  -- per y ≠ 0: reindex x = y·t, collapse |λ_j(y)|² = 1
  have hrow : ∀ y ∈ (Finset.univ : Finset F).erase 0,
      ∑ x : F, lam j x * (starRingEnd ℂ) (lam j y) * ψ (x - y)
        = ∑ t : F, lam j t * ψ (y * (t - 1)) := by
    intro y hy
    have hy0' : y ≠ 0 := (Finset.mem_erase.mp hy).1
    have hre : ∑ x : F, lam j x * (starRingEnd ℂ) (lam j y) * ψ (x - y)
        = ∑ t : F, lam j (y * t) * (starRingEnd ℂ) (lam j y) * ψ (y * t - y) := by
      exact (Fintype.sum_bijective (fun t => y * t) (mulLeft_bijective₀ y hy0')
        _ _ (fun t => rfl)).symm
    rw [hre]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hfam.map_mul j y t, show y * t - y = y * (t - 1) from by ring]
    have hunit : lam j y * (starRingEnd ℂ) (lam j y) = 1 := by
      have h1 : lam j y * (starRingEnd ℂ) (lam j y) = ((‖lam j y‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.mul_conj]; norm_cast
      rw [h1, hgrp.norm_one j y hy0']
      norm_num
    calc lam j y * lam j t * (starRingEnd ℂ) (lam j y) * ψ (y * (t - 1))
        = (lam j y * (starRingEnd ℂ) (lam j y)) * (lam j t * ψ (y * (t - 1))) := by ring
      _ = lam j t * ψ (y * (t - 1)) := by rw [hunit, one_mul]
  rw [Finset.sum_congr rfl hrow]
  -- swap and evaluate: Σ_t λ_j(t)·Σ_{y≠0}ψ(y(t−1)) = Σ_t λ_j(t)(q·1_{t=1} − 1) = q
  rw [Finset.sum_comm]
  have hcol : ∀ t : F, ∑ y ∈ (Finset.univ : Finset F).erase 0, lam j t * ψ (y * (t - 1))
      = lam j t * ((if t - 1 = 0 then (Fintype.card F : ℂ) else 0) - 1) := by
    intro t
    rw [← Finset.mul_sum]
    congr 1
    have h1 : ∑ y ∈ (Finset.univ : Finset F).erase 0, ψ (y * (t - 1))
        = (∑ y : F, ψ (y * (t - 1))) - ψ (0 * (t - 1)) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0:F))]
    rw [h1]
    have h2 := AddChar.sum_mulShift (ψ := ψ) (t - 1) hψ
    rw [h2]
    simp only [zero_mul, AddChar.map_zero_eq_one]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun t _ => hcol t)]
  have hexp : ∀ t : F, lam j t * ((if t - 1 = 0 then (Fintype.card F : ℂ) else 0) - 1)
      = lam j t * (if t - 1 = 0 then (Fintype.card F : ℂ) else 0) - lam j t := by
    intro t; ring
  rw [Finset.sum_congr rfl (fun t _ => hexp t), Finset.sum_sub_distrib]
  have hA : ∑ t : F, lam j t * (if t - 1 = 0 then (Fintype.card F : ℂ) else 0)
      = (Fintype.card F : ℂ) := by
    rw [Finset.sum_eq_single 1]
    · have hone : lam j (1:F) = 1 := by
        have h := hfam.map_mul j 1 1
        rw [mul_one] at h
        have hne : lam j (1:F) ≠ 0 := lam_ne_zero hgrp j one_ne_zero
        have h' : lam j (1:F) * 1 = lam j (1:F) * lam j (1:F) := by rw [mul_one, ← h]
        exact (mul_left_cancel₀ hne h').symm
      rw [hone]
      simp
    · intro t _ ht
      have : t - 1 ≠ 0 := sub_ne_zero.mpr ht
      simp [this]
    · intro h; exact absurd (Finset.mem_univ 1) h
  have hB : ∑ t : F, lam j t = 0 := hfam.sum_eq_zero j hj
  rw [hA, hB, sub_zero]

/-- Real norm form of `gaussCoeff_mul_conj`: every nontrivial Gauss coefficient has
modulus `sqrt q`. -/
theorem norm_gaussCoeff_eq_sqrt_card (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {j : ZMod m} (hj : j ≠ 0) :
    ‖gaussCoeff lam ψ j‖ = Real.sqrt (Fintype.card F) := by
  have hprod := gaussCoeff_mul_conj hfam hgrp hψ hj
  have hsqC : (((‖gaussCoeff lam ψ j‖ ^ 2 : ℝ) : ℂ))
      = (Fintype.card F : ℂ) := by
    rw [← hprod, RCLike.mul_conj]
    norm_cast
  have hsqR : ‖gaussCoeff lam ψ j‖ ^ 2 = (Fintype.card F : ℝ) := by
    exact_mod_cast hsqC
  rw [← hsqR, Real.sqrt_sq (norm_nonneg _)]

end ArkLib.ProximityGap.Frontier.R46GaussModulus

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R46GaussModulus.gaussCoeff_mul_conj
#print axioms ArkLib.ProximityGap.Frontier.R46GaussModulus.norm_gaussCoeff_eq_sqrt_card
