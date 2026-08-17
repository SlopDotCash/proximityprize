/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.AsymptoticGVBound
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionDecaySum

/-!
# CS25 #82, deliverable 2: the entropy-rate form of the ball-intersection decay

The combinatorial decay bound `I(e) ≤ V_{n−wt(e)}(B')·q^{wt(e)}`
(`CS25BallIntersectionDecaySum.jointCoverCount_le_ballVol_dim`) is here pushed into the `qEntropy`
**rate** form, the shape the CS25 band optimization consumes.  The only new ingredient is the
in-tree entropy upper bound on the Hamming ball volume, which already exists in the matching
`univ.filter` convention (`AsymptoticGVBound.filter_ball_card_le_qEntropy`), so no convention bridge
is re-derived here.

## Main results

* `hammingBallVol_le_qEntropy` — `V_m(B) ≤ (m+1)·q^{m·H_q(B/m)}`, the entropy upper bound on the
  combinatorial ball volume `hammingBallVol`.
* `jointCoverCount_le_qEntropy_decay` — the entropy-rate ball-intersection decay
  `I(e) ≤ (m+1)·q^{m·H_q(B'/m)}·q^{wt(e)}`, `m = n−wt(e)`, `B' = ⌊(2r−wt(e))/2⌋`.
-/

set_option linter.style.longLine false


open scoped BigOperators NNReal ENNReal

namespace ArkLib.CS25

open Finset CodingTheory Code

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- **Entropy upper bound on the ball volume.** `V_m(B) ≤ (m+1)·q^{m·H_q(B/m)}` for `0 < B < m`
below capacity — the bridge from the combinatorial `hammingBallVol` to the `qEntropy` rate form,
reusing the in-tree `filter_ball_card_le_qEntropy` (matching `univ.filter` convention). -/
theorem hammingBallVol_le_qEntropy {F : Type} [Fintype F] [DecidableEq F] [Zero F]
    (hq : 2 ≤ Fintype.card F) (m B : ℕ) (hB0 : 0 < B) (hBm : B < m)
    (hcap : (B : ℝ) / (m : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (hammingBallVol F m B : ℝ)
      ≤ ((m : ℝ) + 1)
        * (Fintype.card F : ℝ) ^ ((m : ℝ) * qEntropy (Fintype.card F) ((B : ℝ) / (m : ℝ))) := by
  unfold hammingBallVol
  have hrw : (univ.filter (fun x : Fin m → F => hammingNorm x ≤ B)).card
      = (univ.filter (fun x : Fin m → F => hammingDist (0 : Fin m → F) x ≤ B)).card := by
    congr 1; ext x
    simp only [Finset.mem_filter, hammingDist_comm (0 : Fin m → F) x, hammingDist_zero_right]
  rw [hrw]
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  have := filter_ball_card_le_qEntropy (ι := Fin m) (F := F) hq B hB0
    (by rw [hcard]; exact hBm) (by rw [hcard]; exact hcap)
  rw [hcard] at this
  exact this

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [Field F]

/-- **Entropy-form ball-intersection decay.** `I(e) ≤ (m+1)·q^{m·H_q(B'/m)}·q^{wt(e)}` with
`m = n − wt(e)`, `B' = ⌊(2r−wt(e))/2⌋`, `r = ⌊δ·n⌋`.  The ball factor is in `qEntropy` rate form —
the shape the CS25 band optimization consumes when summed against the MDS weight enumerator `A_d`. -/
theorem jointCoverCount_le_qEntropy_decay (δ : ℝ≥0) (e : ι → F) (hq : 2 ≤ Fintype.card F)
    (hB0 : 0 < (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2)
    (hBm : (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2
        < Fintype.card ι - hammingNorm e)
    (hcap : (((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2 : ℕ) : ℝ)
        / ((Fintype.card ι - hammingNorm e : ℕ) : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (jointCoverCount δ 0 e : ℝ)
      ≤ (((Fintype.card ι - hammingNorm e : ℕ) : ℝ) + 1)
          * (Fintype.card F : ℝ) ^ (((Fintype.card ι - hammingNorm e : ℕ) : ℝ)
              * qEntropy (Fintype.card F)
                  ((((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2 : ℕ) : ℝ)
                    / ((Fintype.card ι - hammingNorm e : ℕ) : ℝ)))
        * (Fintype.card F : ℝ) ^ (hammingNorm e) := by
  have hdim := jointCoverCount_le_ballVol_dim (F := F) δ e
  have hdimR : (jointCoverCount δ 0 e : ℝ)
      ≤ (hammingBallVol F (Fintype.card ι - hammingNorm e)
          ((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2) : ℝ)
        * ((Fintype.card F : ℝ) ^ (hammingNorm e)) := by
    calc (jointCoverCount δ 0 e : ℝ)
        ≤ ((hammingBallVol F (Fintype.card ι - hammingNorm e)
            ((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2)
              * Fintype.card F ^ hammingNorm e : ℕ) : ℝ) := by exact_mod_cast hdim
      _ = _ := by push_cast; ring
  refine le_trans hdimR ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact hammingBallVol_le_qEntropy hq _ _ hB0 hBm hcap

end ArkLib.CS25
