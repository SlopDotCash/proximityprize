/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorIncidenceAssembly

/-!
# Literal rate-`1/16` half-predecessor bad-scalar bounds

`_HalfPredecessorIncidenceAssembly` proves the complete family-level incidence
theorem.  This file performs the final definitional specialization to the
canonical selected family and to the literal `mcaEvent` filter.  Its last two
theorems are the uniform code-length bounds consumed by the prize-shape
threshold connector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap Code
open scoped NNReal
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring

variable {ι F : Type} [Fintype ι] [Nonempty ι]
variable [Field F] [Fintype F]

open Classical in
/-- The canonical selected family has at most the coordinate length. -/
theorem canonicalRichPointFamily_card_le_two_mul
    (dom : ι ↪ F) {k h : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) :
    (canonicalBadScalarRichPointFamily dom delta u hk).G.card ≤ 2 * h :=
  badScalarRichPointFamily_card_le_two_mul
    (canonicalBadScalarRichPointFamily dom delta u hk)
    hk hn hthreshold hrate

open Classical in
/-- Literal bad-event-filter form at any radius whose agreement ceiling is
`h+1`. -/
theorem badScalar_filter_card_le_two_mul
    (dom : ι ↪ F) {k h : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma).card ≤ 2 * h := by
  simpa only [canonicalBadScalarRichPointFamily, badScalars] using
    canonicalRichPointFamily_card_le_two_mul
      dom delta u hk hn hthreshold hrate

open Classical in
/-- Uniform operational half-predecessor form for an even code length. -/
theorem canonical_halfPredecessor_card_le_length
    {n h k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 2 * h) (hk : 1 ≤ k) (hrate : 16 * k ≤ n)
    (u : WordStack F (Fin 2) (Fin n)) :
    (canonicalBadScalarRichPointFamily dom (k := k)
      (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
      u hk).G.card ≤ n := by
  have hh : 1 ≤ h := by
    have hnpos : 0 < n := NeZero.pos n
    omega
  have hcardFin : Fintype.card (Fin n) = 2 * h := by simp [hn]
  have hthreshold := halfPredecessor_ceiling_agreement_eq hn hh
  have hbound := canonicalRichPointFamily_card_le_two_mul
    dom
    (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
    u hk hcardFin (by simpa only [Fintype.card_fin] using hthreshold)
    (by omega)
  simpa only [hn] using hbound

open Classical in
/-- **Literal uniform predecessor bad-count theorem.** For every received
affine word, at most `n` scalars trigger the MCA bad event. -/
theorem halfPredecessor_badScalar_filter_card_le_length
    {n h k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 2 * h) (hk : 1 ≤ k) (hrate : 16 * k ≤ n)
    (u : WordStack F (Fin 2) (Fin n)) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (Fin n → F)))
        (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
        (u 0) (u 1) gamma).card ≤ n := by
  simpa only [canonicalBadScalarRichPointFamily, badScalars] using
    canonical_halfPredecessor_card_le_length dom hn hk hrate u

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring

/-! ## Axiom audit -/

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring

#print axioms badScalar_filter_card_le_two_mul
#print axioms halfPredecessor_badScalar_filter_card_le_length

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring
