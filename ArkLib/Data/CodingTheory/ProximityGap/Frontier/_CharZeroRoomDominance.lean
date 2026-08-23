/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Explicit char-0 room for the cross-excess dominance, from the sharp backbone (#444)

`_AntitoneCrossExcessDecomp` reduced the antitone step to the **dominance criterion**
```
        p·(W_{r+1}·E_r − W_r·E_{r+1})  ≤  N_r·(n²·E_r − E_{r+1})            (★)
```
(`N_r = n^{2r}`, char-0 "Part A" on the right vs char-p "Part B" on the left), and proved the
wraparound-free corner using the **coarse** backbone `E_{r+1} ≤ n²·E_r` (which only makes Part A `≥ 0`).
`_CharZeroBackboneSmallRRegime` then proved the **sharp** backbone `E_{r+1} ≤ (2r+1)n·E_r` and showed it
implies the coarse one in the regime `2r+1 ≤ n`.

**This file: the explicit char-0 ROOM, from the sharp backbone.** The sharp backbone gives a *strictly
positive, quantified* lower bound on Part A in the regime:
```
        N_r·(n²·E_r − E_{r+1})  ≥  N_r·(n² − (2r+1)·n)·E_r  =  N_r·n·(n − (2r+1))·E_r  ≥ 0,
```
since `E_{r+1} ≤ (2r+1)n·E_r` and `n² − (2r+1)n = n(n − (2r+1)) ≥ 0` for `2r+1 ≤ n`. So the char-0 part
isn't merely nonneg — it has **room `N_r·n·(n−(2r+1))·E_r`** to absorb the char-p correction. This turns
the dominance criterion into an explicit, checkable sufficient condition.

**What this file proves (axiom-clean).**
* `partA_ge_room_of_sharp` — `N_r·(n²·E_r − E_{r+1}) ≥ N_r·n·(n − (2r+1))·E_r` from the sharp backbone
  (`N_r, E_r ≥ 0`, `0 ≤ n`).
* `dominance_of_charp_le_room` — if the char-p correction is at most the explicit room
  (`p·(W_{r+1}E_r − W_r E_{r+1}) ≤ N_r·n·(n−(2r+1))·E_r`), then the dominance criterion (★) holds — hence
  (via `_AntitoneCrossExcessDecomp.antitone_iff_dominance`) the antitone step. The char-p correction is
  bounded by a CONCRETE char-0 quantity, no longer an opaque inequality.
* `antitone_step_of_charp_le_room_smallR` — the end-to-end sufficient condition: in the regime `2r+1 ≤ n`,
  if the char-p correction is within the room, the antitone cross-excess `S_r E_{r+1} − S_{r+1} E_r ≥ 0`
  holds (decomposition re-proved inline to keep the file standalone).

**Honest scope.** This does NOT bound the char-p correction `p·W_r` — that is the prize. It makes the
*target* explicit: the prize ⟺ char-p correction `≤` the concrete char-0 room `N_r·n·(n−(2r+1))·E_r` at
the saddle. A sufficient condition with a named, quantified RHS, not a proof of CORE. No CORE upper bound,
no capacity/growth-law claim. Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroRoomDominance

/-- **Explicit char-0 room.** From the sharp backbone `E_{r+1} ≤ (2r+1)n·E_r` and `2r+1 ≤ n`
(`0 ≤ N_r`, `0 ≤ E_r`, `0 ≤ n`), Part A is bounded below by the concrete room `N_r·n·(n−(2r+1))·E_r`:
`N_r·(n²·E_r − E_{r+1}) ≥ N_r·n·(n − (2r+1))·E_r ≥ 0`. -/
theorem partA_ge_room_of_sharp (E N : ℕ → ℝ) (n : ℝ) (r : ℕ)
    (hNr : 0 ≤ N r) (hEr : 0 ≤ E r) (hn : 0 ≤ n)
    (hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r) (hregime : 2 * (r : ℝ) + 1 ≤ n) :
    N r * (n * (n - (2 * (r : ℝ) + 1)) * E r) ≤ N r * (n ^ 2 * E r - E (r + 1)) := by
  apply mul_le_mul_of_nonneg_left _ hNr
  -- n·(n−(2r+1))·E_r = (n² − (2r+1)n)·E_r ≤ n²·E_r − E_{r+1}, since E_{r+1} ≤ (2r+1)n·E_r
  have hstep : (2 * (r : ℝ) + 1) * n * E r ≤ n ^ 2 * E r := by
    have hcoef : (2 * (r : ℝ) + 1) * n ≤ n ^ 2 := by nlinarith [hregime, hn]
    exact mul_le_mul_of_nonneg_right hcoef hEr
  nlinarith [hsharp, hstep]

/-- **Dominance from char-p ≤ room.** If the char-p correction is at most the explicit room
`N_r·n·(n−(2r+1))·E_r`, then the dominance criterion `p·(W_{r+1}E_r − W_r E_{r+1}) ≤ N_r·(n²E_r − E_{r+1})`
holds. (Chains the char-p bound through the room into Part A.) -/
theorem dominance_of_charp_le_room (E W N : ℕ → ℝ) (n p : ℝ) (r : ℕ)
    (hNr : 0 ≤ N r) (hEr : 0 ≤ E r) (hn : 0 ≤ n)
    (hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r) (hregime : 2 * (r : ℝ) + 1 ≤ n)
    (hcharp : p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (n * (n - (2 * (r : ℝ) + 1)) * E r)) :
    p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (n ^ 2 * E r - E (r + 1)) :=
  le_trans hcharp (partA_ge_room_of_sharp E N n r hNr hEr hn hsharp hregime)

/-- **End-to-end antitone step from char-p ≤ room, in the regime.** With `S k = p·(E k + W k) − N k`,
`N (r+1) = n²·N r`, the sharp backbone + regime, and the char-p correction within the explicit room,
the antitone cross-excess `S_r·E_{r+1} − S_{r+1}·E_r ≥ 0` holds (the decomposition is re-proved inline,
mirroring `_AntitoneCrossExcessDecomp.cross_excess_decomp`). -/
theorem antitone_step_of_charp_le_room_smallR (S E W N : ℕ → ℝ) (n p : ℝ) (r : ℕ)
    (hS : ∀ k, S k = p * (E k + W k) - N k) (hN : N (r + 1) = n ^ 2 * N r)
    (hNr : 0 ≤ N r) (hEr : 0 ≤ E r) (hn : 0 ≤ n)
    (hsharp : E (r + 1) ≤ (2 * (r : ℝ) + 1) * n * E r) (hregime : 2 * (r : ℝ) + 1 ≤ n)
    (hcharp : p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (n * (n - (2 * (r : ℝ) + 1)) * E r)) :
    0 ≤ S r * E (r + 1) - S (r + 1) * E r := by
  have hdom : p * (W (r + 1) * E r - W r * E (r + 1)) ≤ N r * (n ^ 2 * E r - E (r + 1)) :=
    dominance_of_charp_le_room E W N n p r hNr hEr hn hsharp hregime hcharp
  -- cross-excess decomposition (inline): S_r E_{r+1} − S_{r+1} E_r = p(W_r E_{r+1} − W_{r+1} E_r) + N_r(n²E_r − E_{r+1})
  have hdecomp : S r * E (r + 1) - S (r + 1) * E r
      = p * (W r * E (r + 1) - W (r + 1) * E r) + N r * (n ^ 2 * E r - E (r + 1)) := by
    rw [hS r, hS (r + 1), hN]; ring
  rw [hdecomp]; linarith

end ProximityGap.Frontier.CharZeroRoomDominance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharZeroRoomDominance.partA_ge_room_of_sharp
#print axioms ProximityGap.Frontier.CharZeroRoomDominance.dominance_of_charp_le_room
#print axioms ProximityGap.Frontier.CharZeroRoomDominance.antitone_step_of_charp_le_room_smallR
