/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickWraparoundTransfer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.OptimizedSupFromNonprincipalWick

/-!
# Direct optimized sup bound from a `K^r` wraparound-excess envelope

`OptimizedSupFromWraparound` handles the sharp `K = 1` wraparound gate.  The live numerical frontier
also tracks the more realistic absolute-slack shape

`nonprincipal moment ≤ q * K^r * (2r - 1)!! * |G|^r`.

This file states that target directly at the wraparound layer: if the excess over the char-zero Wick
ceiling fits inside the multiplicative slack `(K^r - 1) * Wick_r`, then the existing `K^r`
nonprincipal optimized-sup consumer applies, giving the direct prize-shape bound with final constant
inflated by `sqrt K`.
-/

open Finset AddChar
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.OptimizedSupFromNonprincipalWick

namespace ProximityGap.Frontier.OptimizedSupFromWraparoundK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A `K^r` wraparound-excess envelope gives the `K^r` nonprincipal Wick bound.  Algebraically,
`∑_{b≠0} |η_b|^(2r) = q*Wick + q*wickExcess - |G|^(2r)`, so fitting `q*wickExcess` inside
`q*(K^r - 1)*Wick` is enough for the `q*K^r*Wick` envelope. -/
theorem nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (hgate :
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    NonprincipalWickBoundK ψ G r K := by
  unfold NonprincipalWickBoundK
  rw [sum_nonzero_moment hψ G r]
  unfold wickExcess at hgate
  have hn2_nonneg : 0 ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  nlinarith [hgate, hn2_nonneg]

/-- Single-frequency power bound from the `K^r` wraparound-excess envelope. -/
theorem eta_pow_le_of_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {K : ℝ}
    (hgate :
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  simpa using
    eta_pow_le_of_nonprincipalWickK
      (nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack hψ hgate) hb

/-- Direct optimized square bound from the `K^r` wraparound-excess envelope. -/
theorem eta_sq_le_optimized_of_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K)
    (hrq : Real.log (Fintype.card F) ≤ r)
    (hgate :
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) :=
  eta_sq_le_optimized_of_nonprincipalWickK hr hK hrq
    (nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack hψ hgate) hb

/-- Direct optimized norm bound from the `K^r` wraparound-excess envelope. -/
theorem eta_le_optimized_of_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K)
    (hrq : Real.log (Fintype.card F) ≤ r)
    (hgate :
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ)) :=
  eta_le_optimized_of_nonprincipalWickK hr hK hrq
    (nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack hψ hgate) hb

end ProximityGap.Frontier.OptimizedSupFromWraparoundK

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.OptimizedSupFromWraparoundK

#print axioms nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack
#print axioms eta_pow_le_of_q_wickExcess_le_mul_slack
#print axioms eta_sq_le_optimized_of_q_wickExcess_le_mul_slack
#print axioms eta_le_optimized_of_q_wickExcess_le_mul_slack

end ProximityGap.Frontier.OptimizedSupFromWraparoundK
