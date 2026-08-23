/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickWraparoundTransfer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.OptimizedSupFromNonprincipalWick
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# Direct optimized sup bound from the wraparound-excess gate

`DCWickWraparoundTransfer` identifies the open char-`p` Wick input with the explicit inequality

`q * wickExcess G r ≤ |G|^(2r)`.

`OptimizedSupFromNonprincipalWick` then shows that the equivalent nonprincipal Wick input at
`r ≥ log q` gives the direct moment-method bound

`‖eta ψ G b‖ ≤ sqrt (2e * |G| * r)`.

This file composes those two reductions at a single depth.  It does not prove the wraparound gate;
it makes the direct prize-shape consumer accept the gate in its most explicit current form.
-/

open Finset AddChar
open ProximityGap.Frontier.DCWickMGFFromTermwise
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.NonprincipalWickIsDCWick
open ProximityGap.Frontier.OptimizedSupFromNonprincipalWick
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.OptimizedSupFromWraparound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A single-depth wraparound-excess gate gives the equivalent nonprincipal Wick bound. -/
theorem nonprincipalWick_of_q_wickExcess_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ}
    (hgate : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r)) :
    NonprincipalWickBound ψ G r :=
  (nonprincipalWick_iff_dcWick hψ G r).mpr
    (dcWickBound_of_q_wickExcess_le (G := G) (r := r) hgate)

/-- Single-frequency power bound from the explicit wraparound-excess gate. -/
theorem eta_pow_le_of_q_wickExcess_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ}
    (hgate : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  eta_pow_le_of_nonprincipalWick (nonprincipalWick_of_q_wickExcess_le hψ hgate) hb

/-- Direct optimized square bound from a single-depth wraparound-excess gate. -/
theorem eta_sq_le_optimized_of_q_wickExcess_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)
    (hgate : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
  eta_sq_le_optimized_of_nonprincipalWick hr hrq
    (nonprincipalWick_of_q_wickExcess_le hψ hgate) hb

/-- Direct optimized norm bound from a single-depth wraparound-excess gate.  At
`r = ceil (log q)` this is the usual `sqrt (n log q)` moment-method target up to the explicit
constant `sqrt (2e)`. -/
theorem eta_le_optimized_of_q_wickExcess_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)
    (hgate : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) :=
  eta_le_optimized_of_nonprincipalWick hr hrq
    (nonprincipalWick_of_q_wickExcess_le hψ hgate) hb

end ProximityGap.Frontier.OptimizedSupFromWraparound

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.OptimizedSupFromWraparound

#print axioms nonprincipalWick_of_q_wickExcess_le
#print axioms eta_pow_le_of_q_wickExcess_le
#print axioms eta_sq_le_optimized_of_q_wickExcess_le
#print axioms eta_le_optimized_of_q_wickExcess_le

end ProximityGap.Frontier.OptimizedSupFromWraparound
