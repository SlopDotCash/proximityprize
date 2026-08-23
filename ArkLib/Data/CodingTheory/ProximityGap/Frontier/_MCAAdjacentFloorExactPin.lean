/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Collapse
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction

/-!
# Exact MCA pins from adjacent Hamming floors

For a code of length `n`, let `a/n` be a nonzero Hamming-lattice radius and
`(a-1)/n` its predecessor.  Goodness at the predecessor controls every real
radius strictly below `a/n`: below the predecessor this follows by monotonicity,
and between the two lattice points the MCA event is constant.  Equivalently,
the agreement ceiling stays at `n-a+1` throughout that half-open band and drops
to `n-a` at `a/n`.

This module packages that observation as three reusable connectors:

* `latticeRadius_le_mcaDeltaStar_of_predecessor_good` gives the lower ledger;
* `mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad` pins the threshold
  when the next lattice point is bad;
* `mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper` accepts an
  already assembled upper ledger at the next lattice point.

The bad point in the first exact connector need not itself be good.  The formal
threshold is a supremum, so goodness arbitrarily close from below is enough.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open _root_.ProximityGap Code
open _root_.ProximityGap.MCAThresholdLedger

namespace ArkLib.ProximityGap.Frontier.MCAAdjacentFloorExactPin

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The Hamming-lattice point with radius numerator `a`. -/
noncomputable def latticeRadius (n a : ℕ) : ℝ≥0 :=
  (a : ℝ≥0) / (n : ℝ≥0)

/-- The Hamming-lattice point immediately before `a/n`. -/
noncomputable def predecessorRadius (n a : ℕ) : ℝ≥0 :=
  ((a - 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)

private theorem latticeRadius_mul_length {n a : ℕ} [NeZero n] :
    latticeRadius n a * (n : ℝ≥0) = (a : ℝ≥0) := by
  rw [latticeRadius]
  exact div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne n))

private theorem predecessorRadius_mul_length {n a : ℕ} [NeZero n] :
    predecessorRadius n a * (n : ℝ≥0) = ((a - 1 : ℕ) : ℝ≥0) := by
  rw [predecessorRadius]
  exact div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne n))

/-- A nonzero Hamming-lattice point lies strictly above its predecessor. -/
theorem predecessorRadius_lt_latticeRadius
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a) :
    predecessorRadius n a < latticeRadius n a := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnposNN : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
  rw [predecessorRadius, latticeRadius,
    div_lt_div_iff_of_pos_right hnposNN]
  exact_mod_cast (show a - 1 < a by omega)

/-- Goodness at `(a-1)/n` controls every real radius below `a/n`.

The only non-monotone-looking case is the open interval between the two
lattice points.  There `floor(delta*n)=a-1`, so the MCA step-function law
identifies its error with the predecessor error. -/
theorem epsMCA_le_of_lt_latticeRadius_of_predecessor_good
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar) :
    ∀ delta : ℝ≥0, delta < latticeRadius n a →
      epsMCA (F := F) (A := A) C delta ≤ epsilonStar := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnposNN : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
  intro delta hdelta
  by_cases hle : delta ≤ predecessorRadius n a
  · exact (epsMCA_mono C hle).trans hprev
  · have hprevDelta : predecessorRadius n a < delta := lt_of_not_ge hle
    have hlower : ((a - 1 : ℕ) : ℝ≥0) ≤ delta * (n : ℝ≥0) := by
      have hmul := mul_lt_mul_of_pos_right hprevDelta hnposNN
      rw [predecessorRadius_mul_length] at hmul
      exact hmul.le
    have hupper : delta * (n : ℝ≥0) < (a : ℝ≥0) := by
      have hmul := mul_lt_mul_of_pos_right hdelta hnposNN
      rwa [latticeRadius_mul_length] at hmul
    have hfloorDelta :
        Nat.floor (delta * (Fintype.card (Fin n) : ℝ≥0)) = a - 1 := by
      rw [Fintype.card_fin, Nat.floor_eq_iff (zero_le _)]
      constructor
      · exact hlower
      · have hsucc : a - 1 + 1 = a := by omega
        have hcast : (((a - 1 : ℕ) : ℝ≥0) + 1) = (a : ℝ≥0) := by
          exact_mod_cast hsucc
        rwa [hcast]
    have hfloorPredecessor :
        Nat.floor (predecessorRadius n a *
          (Fintype.card (Fin n) : ℝ≥0)) = a - 1 := by
      rw [Fintype.card_fin, predecessorRadius_mul_length, Nat.floor_natCast]
    rw [_root_.ProximityGap.epsMCA_eq_of_floor_eq (F := F) (A := A) C
      (hfloorDelta.trans hfloorPredecessor.symm)]
    exact hprev

/-- A good predecessor fills the threshold ledger all the way up to the next
Hamming-lattice point, even when goodness fails at that endpoint. -/
theorem latticeRadius_le_mcaDeltaStar_of_predecessor_good
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a) (han : a ≤ n)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar) :
    latticeRadius n a ≤
      mcaDeltaStar (F := F) (A := A) C epsilonStar := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnposNN : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
  have hboundaryLeOne : latticeRadius n a ≤ 1 := by
    rw [latticeRadius, div_le_one hnposNN]
    exact_mod_cast han
  have hgood := epsMCA_le_of_lt_latticeRadius_of_predecessor_good
    (F := F) (A := A) ha1 C epsilonStar hprev
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨delta, hstarDelta, hdeltaBoundary⟩ := exists_between hnot
  have hdeltaLe := le_mcaDeltaStar_of_good (F := F) (A := A) C epsilonStar
    (hdeltaBoundary.le.trans hboundaryLeOne) (hgood delta hdeltaBoundary)
  exact (not_lt_of_ge hdeltaLe) hstarDelta

/-- **Adjacent-floor exact pin.** If `(a-1)/n` is good and `a/n` is bad,
then the operational MCA threshold is exactly `a/n`. -/
theorem mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a) (han : a ≤ n)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar)
    (hbad : epsilonStar < epsMCA (F := F) (A := A) C (latticeRadius n a)) :
    mcaDeltaStar (F := F) (A := A) C epsilonStar = latticeRadius n a := by
  apply le_antisymm
  · exact mcaDeltaStar_le_of_bad C epsilonStar hbad
  · exact latticeRadius_le_mcaDeltaStar_of_predecessor_good
      (F := F) (A := A) ha1 han C epsilonStar hprev

/-- Upper-ledger form of the adjacent-floor exact pin.  This is convenient
when a concrete bad-label module has already converted badness into a
`mcaDeltaStar` upper bound. -/
theorem mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a) (han : a ≤ n)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar)
    (hupper : mcaDeltaStar (F := F) (A := A) C epsilonStar ≤ latticeRadius n a) :
    mcaDeltaStar (F := F) (A := A) C epsilonStar = latticeRadius n a := by
  exact le_antisymm hupper
    (latticeRadius_le_mcaDeltaStar_of_predecessor_good
      (F := F) (A := A) ha1 han C epsilonStar hprev)

/-- Exactness at `a/n` forces goodness at the immediate predecessor.

Indeed, if `(a-1)/n` were bad, the bad-point ledger would put `mcaDeltaStar`
at or below the predecessor, contradicting the strict gap to `a/n`. -/
theorem predecessor_good_of_mcaDeltaStar_eq_latticeRadius
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hexact : mcaDeltaStar (F := F) (A := A) C epsilonStar =
      latticeRadius n a) :
    epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar := by
  by_contra hnot
  have hbad : epsilonStar <
      epsMCA (F := F) (A := A) C (predecessorRadius n a) :=
    lt_of_not_ge hnot
  have hstarLe := mcaDeltaStar_le_of_bad C epsilonStar hbad
  rw [hexact] at hstarLe
  exact (not_lt_of_ge hstarLe) (predecessorRadius_lt_latticeRadius ha1)

/-- **Exact adjacent-floor characterization under a next-rung upper ledger.**

Once an independent construction proves `mcaDeltaStar ≤ a/n`, exactness at
that lattice point is equivalent to goodness at its immediate predecessor.
This is the sharp residual interface: any stronger incidence or structured
floor condition should be recorded only as a sufficient route to the right
side, unless its converse is separately proved. -/
theorem mcaDeltaStar_eq_latticeRadius_iff_predecessor_good_of_upper
    {n a : ℕ} [NeZero n] (ha1 : 1 ≤ a) (han : a ≤ n)
    (C : Set (Fin n → A)) (epsilonStar : ℝ≥0∞)
    (hupper : mcaDeltaStar (F := F) (A := A) C epsilonStar ≤ latticeRadius n a) :
    mcaDeltaStar (F := F) (A := A) C epsilonStar = latticeRadius n a ↔
      epsMCA (F := F) (A := A) C (predecessorRadius n a) ≤ epsilonStar := by
  constructor
  · exact predecessor_good_of_mcaDeltaStar_eq_latticeRadius
      (F := F) (A := A) ha1 C epsilonStar
  · intro hprev
    exact mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper
      (F := F) (A := A) ha1 han C epsilonStar hprev hupper

end ArkLib.ProximityGap.Frontier.MCAAdjacentFloorExactPin

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.MCAAdjacentFloorExactPin
#print axioms epsMCA_le_of_lt_latticeRadius_of_predecessor_good
#print axioms latticeRadius_le_mcaDeltaStar_of_predecessor_good
#print axioms mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
#print axioms mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper
#print axioms predecessor_good_of_mcaDeltaStar_eq_latticeRadius
#print axioms mcaDeltaStar_eq_latticeRadius_iff_predecessor_good_of_upper
