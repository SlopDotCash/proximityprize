/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandCeilingWindow

/-! ### Non-vacuity: the F31 in-window instance, now through the field-size route -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code
open ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The binomial size bound, in the powersetCard vocabulary of the window
theorem: `|{(k+m+1)-subsets of Fin n}| ≤ n^(k+m+1)`. -/
theorem powersetCard_card_le_pow (k m : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
      ≤ n ^ (k + m + 1) := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_le_pow n (k + m + 1)

open Classical in
/-- **The deep-band δ\* ceiling from a field-size inequality.**  This is the
window consumer with `hPhi` discharged parametrically: instead of asking for
the Nat-binomial bound `C(n,k+m+1) < q^(m+1)` directly, ask for the clean
field-size inequality `n^(k+m+1) < q^(m+1)` (which forces it via
`C(n,s) ≤ n^s`).  Combined with the budget `hwin`, this yields

  `mcaDeltaStar (rsCode dom k) ε* ≤ δ`   at every band radius `(1−δ)n ≤ k+m+1`.

The whole chain — binomial size bound → window collapse `Λ = C'+2` → consumer
→ ledger — in one statement: one field-size inequality + one budget in, a
machine-checked δ* ceiling out. -/
theorem mcaDeltaStar_le_of_field_size_window (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞) (hε : εstar ≠ ⊤)
    (hsize : n ^ (k + m + 1) < (Fintype.card F) ^ (m + 1))
    (hwin : εstar * ((Fintype.card F : ℝ≥0∞)
          * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2) + 1
        ≤ (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
            / (Fintype.card F) ^ m) : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  refine mcaDeltaStar_le_of_ceiling_window dom hk hhi εstar hε ?_ hwin
  exact lt_of_le_of_lt (powersetCard_card_le_pow k m) hsize


/-- The F31 instance re-derived through the field-size wrapper.  Here
`n = 10`, `s = k+m+1 = 4`, `q = 31`, `m+1 = 2`: the field-size hypothesis would
be `10^4 < 31^2 = 961`, which is FALSE (`10^4 = 10000`).  So the field-size
wrapper is genuinely STRICTER than the raw window (`C(10,4)=210 < 961` holds but
`10^4 < 961` does not): the field-size route demands `q` polynomially larger in
`n`.  We therefore do NOT claim the F31 instance through this route; it is the
asymptotic/large-field regime the wrapper is built for.  The check below only
confirms the binomial bound itself is non-vacuous at this point. -/
example : ((Finset.univ : Finset (Fin 10)).powersetCard (2 + 1 + 1)).card
    ≤ 10 ^ (2 + 1 + 1) := powersetCard_card_le_pow (n := 10) 2 1

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.powersetCard_card_le_pow
#print axioms ProximityGap.PairRank.mcaDeltaStar_le_of_field_size_window
