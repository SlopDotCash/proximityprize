/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickMGFFiniteException
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickWraparoundTransfer

/-!
# Wraparound-excess finite-exception DC-Wick producers

`DCWickWraparoundTransfer` identifies the open termwise DC-Wick inequality with the explicit
wraparound gate

`q * wickExcess G r ≤ |G|^(2r)`.

`DCWickMGFFiniteException` shows that the DC-subtracted MGF only needs the termwise inequality off a
finite exceptional set, provided the exceptional aggregate is non-positive at the chosen saddle.

This file composes the two interfaces.  It does not prove the wraparound gate; it removes one more
translation layer from downstream statements by letting users state the cofinite hypothesis directly
in terms of `wickExcess`.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DCWickWraparoundFiniteException

open Finset AddChar
open ProximityGap.Frontier.DCWickMGFFromTermwise
open ProximityGap.Frontier.DCWickMGFFiniteException
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.ConvergenceHub
open ProximityGap.Frontier.NearRamanujanFromDCSaddle
open ProximityGap.Frontier.NearRamanujanFromSaddle
open ArkLib.ProximityGap.GaussPeriodSpectralFrame

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A cofinite wraparound-excess gate is exactly the cofinite `DCWickBound` input expected by the
finite-exception MGF producer. -/
theorem dcWick_except_finite_of_q_wickExcess_except_finite (G : Finset F) (s : Finset ℕ)
    (hgate : ∀ r ∉ s, (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r)) :
    ∀ r ∉ s, DCWickBound G r := by
  intro r hr
  exact dcWickBound_of_q_wickExcess_le (G := G) (r := r) (hgate r hr)

/-- Finite-exception DC-MGF producer with the non-exceptional hypothesis stated directly as the
wraparound-excess gate. -/
theorem dcMGF_le_of_q_wickExcess_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (y : ℝ) (s : Finset ℕ)
    (hgate : ∀ r ∉ s, (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r)) :
    (∑' r : ℕ, dcTerm G y r)
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)
          + ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) := by
  exact dcMGF_le_of_dcWick_except_finite hψ G y s
    (dcWick_except_finite_of_q_wickExcess_except_finite G s hgate)

/-- Clean finite-exception DC-MGF bound from a cofinite wraparound-excess gate and non-positive
exceptional aggregate. -/
theorem dcMGF_le_of_q_wickExcess_except_finite_aggNonpos {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) (s : Finset ℕ)
    (hgate : ∀ r ∉ s, (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    (∑' r : ℕ, dcTerm G y r)
      ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2) := by
  exact dcMGF_le_of_dcWick_except_finite_aggNonpos hψ G y s
    (dcWick_except_finite_of_q_wickExcess_except_finite G s hgate) hagg

/-- End-to-end finite-exception saddle consumer with the open cofinite input stated as the
wraparound-excess gate. -/
theorem nearRamanujan_of_q_wickExcess_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (s : Finset ℕ)
    (hgate : ∀ r ∉ s, (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    NearRamanujanSqrtLog ψ G (saddleConst F G y) := by
  exact nearRamanujan_of_dcWick_except_finite hψ G hy hn hL hsaddle s
    (dcWick_except_finite_of_q_wickExcess_except_finite G s hgate) hagg

/-- Prize-floor finite-exception consumer with the open cofinite input stated as the
wraparound-excess gate. -/
theorem prizeFloor_of_q_wickExcess_except_finite {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {y : ℝ} (hy : 0 < y) (hn : 0 < (G.card : ℝ))
    (hq1 : (1 : ℝ) ≤ Fintype.card F) (hq : (G.card : ℝ) ≤ Fintype.card F)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (s : Finset ℕ)
    (hgate : ∀ r ∉ s, (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r))
    (hagg : ∑ r ∈ s, (dcTerm G y r - gaussTerm G y r) ≤ 0) :
    PrizeFloor ψ G (saddleConst F G y) := by
  exact prizeFloor_of_dcWick_except_finite hψ G hy hn hq1 hq hL hsaddle s
    (dcWick_except_finite_of_q_wickExcess_except_finite G s hgate) hagg

end ProximityGap.Frontier.DCWickWraparoundFiniteException

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.DCWickWraparoundFiniteException

#print axioms dcWick_except_finite_of_q_wickExcess_except_finite
#print axioms dcMGF_le_of_q_wickExcess_except_finite
#print axioms dcMGF_le_of_q_wickExcess_except_finite_aggNonpos
#print axioms nearRamanujan_of_q_wickExcess_except_finite
#print axioms prizeFloor_of_q_wickExcess_except_finite

end ProximityGap.Frontier.DCWickWraparoundFiniteException
