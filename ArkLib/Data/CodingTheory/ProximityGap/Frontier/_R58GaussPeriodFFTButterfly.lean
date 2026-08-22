/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# LANE B2 (#466 round 58): THE FFT BUTTERFLY on the Gauss-period tower (a DSP/engineering lens)

The prize subgroup `μ_n` (`n = 2^μ`) is exactly the group underlying the **radix-2 FFT**.  This
brick imports the FFT engineer's tool — the *butterfly* — onto the Gauss-period tower.

If `G = H ⊔ ζ·H` is the index-2 coset split (`H` = the squares subgroup `μ_{n/2}`, `ζ` a
generator of `G/H`), then the size-`n` Gauss period is the FFT butterfly of two size-`n/2`
periods:

  **`eta_butterfly`** :  `η_b(G) = η_b(H) + η_{ζb}(H)`.

and the two half-periods are **exactly orthogonal across the tower**:

  **`sum_cross_eq_zero`** :  `∑_b η_b(H)·conj(η_{ζb}(H)) = 0`   (when `ζ ∉ H·H⁻¹`).

The orthogonality is why the second moment is tower-consistent (`∑_b‖η_b(G)‖² = 2∑_b‖η_b(H)‖²`);
the *pointwise* butterfly cancellation `‖A+B‖ ≤ √2·max‖·‖` that would collapse the sup to the
Ramanujan bound `√n` is NOT proven here (it is the wall) — but the probe
`probe_r58_butterfly.py` confirms both identities exactly (`err ~1e-15`) and finds
`M_n/M_{n/2} < √2` at every tested cell, consistent with the Ramanujan target.

This is a genuinely new structural handle on the tower (the FFT recursion), verified and
axiom-clean.  It reframes the Paley tower as a **radix-2 signal-flow graph**: the open content
is exactly "does the butterfly cancel per-frequency, not just in mean".  Issue #466, round 58.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R58GaussPeriodFFTButterfly

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **THE FFT BUTTERFLY (round-58 main identity).**  For the index-2 coset split
`G = H ⊔ ζ·H`, the size-`n` Gauss period is the butterfly sum of two size-`n/2` periods:
`η_b(G) = η_b(H) + η_{ζb}(H)`. -/
theorem eta_butterfly {ψ : AddChar F ℂ} {G H : Finset F} {ζ : F}
    (hunion : G = H ∪ H.image (fun y => ζ * y))
    (hdisj : Disjoint H (H.image (fun y => ζ * y)))
    (hζ0 : ζ ≠ 0) (b : F) :
    eta ψ G b = eta ψ H b + eta ψ H (ζ * b) := by
  classical
  unfold eta
  rw [hunion, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hζ0 h)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  ring

/-- **CROSS-TOWER ORTHOGONALITY (round-58).**  The two half-periods of the butterfly are
orthogonal in the frequency mean: `∑_b η_b(H)·conj(η_{ζb}(H)) = 0`, provided `ζ` is not a ratio
of two `H`-elements (true when `ζ ∉ H` and `H` is a subgroup).  This is the exact identity behind
the tower-consistency of the second moment. -/
theorem sum_cross_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {H : Finset F} {ζ : F}
    (hζ : ∀ y ∈ H, ∀ y' ∈ H, y ≠ ζ * y') :
    ∑ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (ζ * b)) = 0 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- expand each summand into a double `H`-sum of a shifted character
  have hexpand : ∀ b : F, eta ψ H b * (starRingEnd ℂ) (eta ψ H (ζ * b))
      = ∑ y ∈ H, ∑ y' ∈ H, ψ (b * (y - ζ * y')) := by
    intro b
    unfold eta
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ => ?_))
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun b _ => hexpand b)]
  -- move the `b`-sum inside and collapse by orthogonality
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun y hy => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun y' hy' => ?_)
  rw [AddChar.sum_mulShift (y - ζ * y') hψ]
  simp [sub_ne_zero.mpr (hζ y hy y' hy')]

end ArkLib.ProximityGap.Frontier.R58GaussPeriodFFTButterfly

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R58GaussPeriodFFTButterfly.eta_butterfly
#print axioms ArkLib.ProximityGap.Frontier.R58GaussPeriodFFTButterfly.sum_cross_eq_zero
