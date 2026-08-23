/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Cross-orthogonality of even/odd coset periods (#407)

The two level-`(μ-1)` coset periods `η_H(b)` (even coset) and `η_H(ωb)` (odd coset, `= η_{ωH}(b)`)
are **orthogonal as functions of the frequency** whenever the `ω`-translate `ωH` is disjoint from
`H`:

> **`coset_period_orthogonal`** — `∑_b η_H(b) · conj η_H(ωb) = 0`.

Proof: expand and swap sums; the inner frequency sum `∑_b ψ(b(y'−ωy))` is `q·[y'=ωy]`, and
`y'=ωy` is impossible for `y',y∈H` since `ωy∈ωH` is disjoint from `H`. The diagonal that gives
`q·|G|` in the second-moment Parseval (`subgroup_gaussSum_secondMoment`) is killed by the shift.

This is the exact reason the **total twist equals the total period energy** (`total_twist_eq`,
both `= q·|G|`): by polarization `‖η_G‖²−‖η_H(b)−η_H(ωb)‖² = 4 Re(η_H(b)·conj η_H(ωb))`, and this
brick makes the cross term sum to `0`. The period and the twist are *complementary* (sum to
`2(‖η_H(b)‖²+‖η_H(ωb)‖²)` pointwise, equal totals) and uncorrelated on average — so a tower deficit
must come from worst-case pointwise structure, not a global cross-correlation. (BGK confirmation.)

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.CosetPeriodOrthogonal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Cross-orthogonality of coset periods.** If `ωH` is disjoint from `H`, the even and odd coset
periods are orthogonal over frequencies: `∑_b η_H(b)·conj η_H(ωb) = 0`. The ω-shift moves the
diagonal off `H`, killing the term that would otherwise give `q·|G|`. -/
theorem coset_period_orthogonal {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {H : Finset F} {ω : F}
    (hdisj : Disjoint H (H.image (fun x => ω * x))) :
    ∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (ω * b)) = 0 := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (ω * b))
      = ∑ b : F, ∑ y' ∈ H, ∑ y ∈ H, ψ (b * (y' - ω * y)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : (starRingEnd ℂ) (eta ψ H (ω * b)) = ∑ y ∈ H, ψ (-((ω * b) * y)) := by
          rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj ((ω * b) * y))
        have hL : eta ψ H b = ∑ y ∈ H, ψ (b * y) := rfl
        rw [hconjeta, hL, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun y' _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have harg : b * y' + -((ω * b) * y) = b * (y' - ω * y) := by ring
        rw [← AddChar.map_add_eq_mul, harg]
    _ = ∑ y' ∈ H, ∑ y ∈ H, ∑ b : F, ψ (b * (y' - ω * y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y' _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ y' ∈ H, ∑ y ∈ H, (0 : ℂ) := by
        refine Finset.sum_congr rfl (fun y' hy' => ?_)
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hne : ¬ (y' - ω * y = 0) := by
          rw [sub_eq_zero]
          intro h
          have hmem : y' ∈ H.image (fun x => ω * x) := by
            rw [h]; exact Finset.mem_image_of_mem _ hy
          exact Finset.disjoint_left.mp hdisj hy' hmem
        rw [AddChar.sum_mulShift (y' - ω * y) hψ, if_neg hne, Nat.cast_zero]
    _ = 0 := by simp

end ArkLib.ProximityGap.CosetPeriodOrthogonal
#print axioms ArkLib.ProximityGap.CosetPeriodOrthogonal.coset_period_orthogonal
