/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R257 thin-band split socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# R257 (#466): thin-band split for the q60 route

The q60 cap `S(hi) <= A` does not by itself imply the micro-band cap
`S(lo) <= A + B`; one must also bound the thin band `[lo, hi)`.

This file packages the finite-carrier accounting:

```text
#{x >= lo} <= #{x >= hi} + #{lo <= x < hi}.
```
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.R257ThinBandSplitSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`.  Duplicated locally so this scratch socket
can be checked with `pg-iterate` before the R251 socket is built as an olean. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- Count values in the half-open band `[lo, hi)`. -/
def BandCount (s : Finset ι) (t : ι → ℝ) (lo hi : ℝ) : ℝ :=
  ((s.filter (fun i => lo ≤ t i ∧ t i < hi)).card : ℝ)

/-- Superlevel at `lo` splits into superlevel at `hi` plus the thin band
`[lo, hi)`. -/
theorem survivorCount_le_hi_add_band
    (s : Finset ι) (t : ι → ℝ) {lo hi : ℝ} :
    SurvivorCount s t lo ≤ SurvivorCount s t hi + BandCount s t lo hi := by
  let A : Finset ι := s.filter (fun i => lo ≤ t i)
  let H : Finset ι := s.filter (fun i => hi ≤ t i)
  let B : Finset ι := s.filter (fun i => lo ≤ t i ∧ t i < hi)
  have hsubset : A ⊆ H ∪ B := by
    intro i hiA
    have his : i ∈ s := (Finset.mem_filter.mp hiA).1
    have hlo : lo ≤ t i := (Finset.mem_filter.mp hiA).2
    by_cases hhi : hi ≤ t i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨his, hhi⟩)
    · have hlt : t i < hi := lt_of_not_ge hhi
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨his, hlo, hlt⟩)
  have hcardA : A.card ≤ (H ∪ B).card := Finset.card_le_card hsubset
  have hcardUnion : (H ∪ B).card ≤ H.card + B.card := Finset.card_union_le H B
  have hnat : A.card ≤ H.card + B.card := le_trans hcardA hcardUnion
  unfold SurvivorCount BandCount
  exact_mod_cast hnat

/-- A high-threshold cap plus a thin-band cap gives the low-threshold cap. -/
theorem survivorCount_low_le_of_hi_and_band
    (s : Finset ι) (t : ι → ℝ) {lo hi A B : ℝ}
    (hHi : SurvivorCount s t hi ≤ A * (s.card : ℝ))
    (hBand : BandCount s t lo hi ≤ B * (s.card : ℝ)) :
    SurvivorCount s t lo ≤ (A + B) * (s.card : ℝ) := by
  calc
    SurvivorCount s t lo ≤ SurvivorCount s t hi + BandCount s t lo hi :=
      survivorCount_le_hi_add_band s t
    _ ≤ A * (s.card : ℝ) + B * (s.card : ℝ) := by
      exact add_le_add hHi hBand
    _ = (A + B) * (s.card : ℝ) := by ring

end

end ArkLib.ProximityGap.Frontier.R257ThinBandSplitSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R257ThinBandSplitSocket.survivorCount_le_hi_add_band
#print axioms
  ArkLib.ProximityGap.Frontier.R257ThinBandSplitSocket.survivorCount_low_le_of_hi_and_band
