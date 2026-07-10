/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R382HalfRadiusPinConnector

/-!
# Operational rate-1/16 pin from the half-predecessor incidence bound

This file isolates the operational payoff of the rate-`1/16` rich-point argument.  Its only
unresolved incidence input is a uniform bound on the scalar set `G` of every canonical
`BadScalarRichPointFamily` at `halfPredecessorRadius n`.

The first theorem converts that finite-family bound into

```text
epsMCA <= n / q.
```

At a tight field-normalized budget `floor(p / Q) = n`, this is at most `Q^-1`.  The existing
half-predecessor step-function bridge then gives `mcaDeltaStar >= 1/2`, while overlap packing
gives the matching upper bound.  The rate assumption `16*k <= n` supplies the `k <= n/4`
hypothesis required by the packing theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open _root_.ProximityGap Code ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A uniform cardinality bound on the canonical rich-point family is exactly a uniform
bad-scalar bound, hence bounds `epsMCA` after normalization by the field cardinality. -/
theorem epsMCA_le_card_div_of_canonicalRichPointFamily_card_le
    (dom : ι ↪ F) {k B : ℕ} (delta : ℝ≥0) (hk : 1 ≤ k)
    (hrich : ∀ u : WordStack F (Fin 2) ι,
      (canonicalBadScalarRichPointFamily dom (k := k) delta u hk).G.card ≤ B) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code dom k : Set (ι → F))) delta ≤
      (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast (show
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma).card ≤ B by
    simpa only [canonicalBadScalarRichPointFamily, badScalars] using hrich u)

/-- Half-predecessor specialization with the target budget `n/q`. -/
theorem epsMCA_halfPredecessor_le_of_canonicalRichPointFamily_card_le
    {n k : ℕ} [NeZero n] (dom : Fin n ↪ F) (hk : 1 ≤ k)
    (hrich : ∀ u : WordStack F (Fin 2) (Fin n),
      (canonicalBadScalarRichPointFamily dom (k := k)
        (halfPredecessorRadius n) u hk).G.card ≤ n) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code dom k : Set (Fin n → F)))
        (halfPredecessorRadius n) ≤
      (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_card_div_of_canonicalRichPointFamily_card_le
    dom (B := n) (halfPredecessorRadius n) hk hrich

open Classical in
/-- **Conditional rate-`1/16` operational pin.**  At a tight normalized field budget, a
uniform `|G| <= n` theorem for the canonical half-predecessor rich-point families pins the
operational MCA threshold of the smooth evaluation code exactly at `1/2`.

The hypothesis `hrich` is the sole incidence residual.  Everything after it is the proved
event-count, lattice-predecessor, budget, and overlap-packing composition. -/
theorem evalCode_mcaDeltaStar_eq_half_of_rateSixteenth_richPointBound
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hfloor : p / Q = n) (hrate : 16 * k ≤ n)
    (hsupply : 4 ≤ p - n)
    (hrich :
      let dom := ProximityGap.KKH26RegimeSplit.powDomain g hg
        (ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
      ∀ u : WordStack (ZMod p) (Fin 2) (Fin n),
        (canonicalBadScalarRichPointFamily dom (k := k)
          (halfPredecessorRadius n) u (by omega)).G.card ≤ n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) =
      (1 / 2 : ℝ≥0) := by
  have hg0 : g ≠ 0 := ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom : Fin n ↪ ZMod p :=
    ProximityGap.KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g n (k - 1) =
      (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    dsimp only [dom]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        g hg hg0 (k - 1))
  have hcount : epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n (k - 1)) (halfPredecessorRadius n) ≤
        (n : ℝ≥0∞) / (p : ℝ≥0∞) := by
    rw [hcode]
    simpa only [ZMod.card] using
      (epsMCA_halfPredecessor_le_of_canonicalRichPointFamily_card_le
        dom (by omega : 1 ≤ k) (by simpa only [dom] using hrich))
  have hnormalized : (n : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (Fact.out (p := p.Prime)).ne_zero
    rw [ENNReal.div_le_iff hp0 (ENNReal.natCast_ne_top _)]
    have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    calc
      (n : ℝ≥0∞) = (n : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
      _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast (show n * Q ≤ p by
          have hmul := Nat.mul_div_le p Q
          simpa [hfloor, Nat.mul_comm] using hmul)
      _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _
  have hlower : (1 / 2 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
    half_le_mcaDeltaStar_of_predecessor_good hnEven (by omega)
      (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      (hcount.trans hnormalized)
  have hkquarter : k ≤ n / 4 := by omega
  have hupper : mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
        (1 / 2 : ℝ≥0) :=
    mcaDeltaStar_le_half_of_floor_eq_length
      hg hQ hk hnEven hfloor hkquarter hsupply
  exact le_antisymm hupper hlower

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin
#print axioms epsMCA_halfPredecessor_le_of_canonicalRichPointFamily_card_le
#print axioms evalCode_mcaDeltaStar_eq_half_of_rateSixteenth_richPointBound
