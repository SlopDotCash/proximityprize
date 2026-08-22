/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail

/-!
# Sharp rooted Markov form for the char-p deep moment tail

The base file exposes the rooted unconditional moment bound in the deliberately coarse form
`‖η_b‖ ≤ q^(1/(2r)) · |G|`.  This file records the exact root of the sharper energy tail
`E_r ≤ |G|^(2r-1)`: the same Markov argument gives the marginally sharper
`q^(1/(2r)) · |G|^((2r-1)/(2r))`.  This is useful bookkeeping for no-go comparisons, but it is still
an unconditional moment-route ceiling and does not approach the prize square-root bound.
-/

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.CharPDeepMomentTailRootSharp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Exact rooted form of the sharp unconditional moment tail.  The exponent on `|G|` is written as
`(2r-1)/(2r)` in multiplication form to avoid committing downstream users to a particular
normal form for real subtraction. -/
theorem eta_le_rpow_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ≤
      (Fintype.card F : ℝ) ^ ((((2 * r : ℕ) : ℝ))⁻¹) *
        (G.card : ℝ) ^ (((2 * r - 1 : ℕ) : ℝ) * ((((2 * r : ℕ) : ℝ))⁻¹)) := by
  set x : ℝ := ‖eta ψ G b‖ with hxdef
  have hx : 0 ≤ x := norm_nonneg _
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have h : x ^ (2 * r) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1) :=
    ArkLib.ProximityGap.CharPDeepMomentTail.eta_pow2r_le_sharp hψ G r hr b
  have hmono := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ x ^ (2*r)) h
    (by positivity : (0:ℝ) ≤ (((2 * r : ℕ):ℝ))⁻¹)
  have hlhs : (x ^ (2*r)) ^ ((((2 * r : ℕ):ℝ))⁻¹) = x :=
    Real.pow_rpow_inv_natCast hx (by omega)
  rw [hlhs] at hmono
  have hrhs : ((Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1)) ^
        ((((2 * r : ℕ):ℝ))⁻¹)
      = (Fintype.card F : ℝ) ^ ((((2 * r : ℕ):ℝ))⁻¹) *
        (G.card : ℝ) ^ (((2 * r - 1 : ℕ) : ℝ) * ((((2 * r : ℕ):ℝ))⁻¹)) := by
    rw [Real.mul_rpow hq (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (G.card : ℝ) (2 * r - 1), ← Real.rpow_mul hn]
  rwa [hrhs] at hmono

end ArkLib.ProximityGap.CharPDeepMomentTailRootSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailRootSharp.eta_le_rpow_sharp
