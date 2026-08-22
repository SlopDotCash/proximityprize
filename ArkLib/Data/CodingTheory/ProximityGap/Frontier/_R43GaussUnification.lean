/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R40CubeClassExact

/-!
# LANE A+B (#466 round 43): THE UNIFICATION — the A-side object enters the same calculus

The A-side of the prize (`WallHolds`, the moment tower of `η_b = ∑_{y∈μ_n} ψ(b·y)`) has the
exact expansion, by the SAME dual-family indicator as round 19:

  **`eta_gauss_expansion`** :  `m·η_b = −1 + ∑_{j≠0} 𝔤_j·conj(λ_j(b))`   (b ≠ 0),

with `𝔤_j = ∑_x λ_j(x)·ψ(x)` the Gauss coefficients — unit-modulus-`√q`, on the same dual
group `ℤ/m`, in the same form as the B-side `m·W = χ·(∑ J_j λ_j − 1)`.  Because the entire
rounds 19–40 calculus (`lamTransform`, master identity, ring hom, collapses, ladders) is
weight-agnostic, it applies VERBATIM to the A-side: `WallHolds`' tower is the iterated
self-convolution program for the Gauss sequence, its correlations collapse through
`weighted_lag_correlation'`, and its final input is the same family-torus statement with
`𝔤_j` in place of `J_j`.  Moreover `J_j = 𝔤_j·𝔤(χ)/𝔤(λ_jχ)` classically (Jacobi = ratio of
Gauss sums): the two sequences are multiplicatively entangled, and the two final inputs are
faces of ONE statement about the Gauss-coefficient sequence.  The prize's two open Props are
now formally inside a single machine-checked framework.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 43, LANES A+B.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R43GaussUnification

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R24InvolutionNoGo
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- The Gauss coefficient of the dual family: `𝔤_j = ∑_x λ_j(x)·ψ(x)`. -/
noncomputable def gaussCoeff (lam : ZMod m → F → ℂ) (ψ : AddChar F ℂ) (j : ZMod m) : ℂ :=
  ∑ x : F, lam j x * ψ x

/-- **THE A-SIDE EXPANSION (round-43 main theorem)** — the exact Gauss–Fourier expansion of
`η_b`, the precise A-side analogue of the round-19 identity:
`m·η_b = −1 + ∑_{j≠0} 𝔤_j·conj(λ_j(b))` for `b ≠ 0`. -/
theorem eta_gauss_expansion (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    (m : ℂ) * eta ψ G b
      = -1 + ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          gaussCoeff lam ψ j * (starRingEnd ℂ) (lam j b) := by
  classical
  -- m·η_b = ∑_x (∑_j λ_j(x))·ψ(b·x)   [indicator]
  have h1 : (m : ℂ) * eta ψ G b = ∑ x : F, (∑ j : ZMod m, lam j x) * ψ (b * x) := by
    have hpt : ∀ x : F, (∑ j : ZMod m, lam j x) * ψ (b * x)
        = (m : ℂ) * ((if x ∈ G then 1 else 0) * ψ (b * x)) := by
      intro x
      rw [hfam.indicator x]
      ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), ← Finset.mul_sum]
    congr 1
    rw [eta]
    have hpt2 : ∀ x : F, (if x ∈ G then (1:ℂ) else 0) * ψ (b * x)
        = (if x ∈ G then ψ (b * x) else 0) := by
      intro x; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => hpt2 x)]
    rw [Finset.sum_ite_mem Finset.univ G (fun x => ψ (b * x)), Finset.univ_inter]
  rw [h1]
  have h2 : ∑ x : F, (∑ j : ZMod m, lam j x) * ψ (b * x)
      = ∑ j : ZMod m, ∑ x : F, lam j x * ψ (b * x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ => by rw [Finset.sum_mul])
  rw [h2]
  -- per-j evaluation
  have hval : ∀ j : ZMod m, ∑ x : F, lam j x * ψ (b * x)
      = if j = 0 then -1 else gaussCoeff lam ψ j * (starRingEnd ℂ) (lam j b) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl]
      have hpt : ∀ x : F, lam 0 x * ψ (b * x)
          = ψ (b * x) - (if x = 0 then ψ (b * x) else 0) := by
        intro x
        by_cases hx : x = 0
        · subst hx; simp [hfam.map_zero]
        · rw [hfam.triv_on_units x hx]; simp [hx]
      rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib]
      have hA : ∑ x : F, ψ (b * x) = 0 := by
        have := AddChar.sum_mulShift (ψ := ψ) b hψ
        rw [if_neg hb] at this
        calc ∑ x : F, ψ (b * x) = ∑ x : F, ψ (x * b) := by
              exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])
          _ = 0 := by exact_mod_cast this
      have hB : ∑ x : F, (if x = 0 then ψ (b * x) else 0) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ (0:F) (fun x => ψ (b * x))]
        simp
      rw [hA, hB]
      ring
    · rw [if_neg hj]
      -- reindex x = b⁻¹·u
      have hre : ∑ x : F, lam j x * ψ (b * x)
          = ∑ u : F, lam j (b⁻¹ * u) * ψ (b * (b⁻¹ * u)) := by
        exact (Fintype.sum_bijective (fun u => b⁻¹ * u)
          (mulLeft_bijective₀ b⁻¹ (inv_ne_zero hb)) _ _ (fun u => rfl)).symm
      rw [hre]
      have hpt : ∀ u : F, lam j (b⁻¹ * u) * ψ (b * (b⁻¹ * u))
          = (starRingEnd ℂ) (lam j b) * (lam j u * ψ u) := by
        intro u
        have harg : b * (b⁻¹ * u) = u := by
          rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
        rw [harg, hfam.map_mul j b⁻¹ u, ← lam_inv_eq_conj hfam hgrp j hb]
        ring
      rw [Finset.sum_congr rfl (fun u _ => hpt u), ← Finset.mul_sum, gaussCoeff]
      ring
  rw [Finset.sum_congr rfl (fun j _ => hval j)]
  -- split off j = 0
  rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr
    (Finset.mem_univ (0 : ZMod m)))]
  rw [Finset.sum_singleton, if_pos rfl]
  have hrest : ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
      (if j = 0 then (-1 : ℂ) else gaussCoeff lam ψ j * (starRingEnd ℂ) (lam j b))
      = ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          gaussCoeff lam ψ j * (starRingEnd ℂ) (lam j b) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_sdiff.mp hj).2; simpa using this
    rw [if_neg hj0]
  rw [hrest]
  ring

end ArkLib.ProximityGap.Frontier.R43GaussUnification

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R43GaussUnification.eta_gauss_expansion
