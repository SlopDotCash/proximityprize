/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawScaleDoorScaleBridge

/-!
# Door-IV Shaw-gap boundedness no-go (#444)

This file packages the exact Shaw scale bridge into the boundedness form used by the reduction chain:
if genuine prize-floor ratios are uniformly bounded and Shaw values do not vanish, then the exact
`√(log(q/n))` synthesis gap is uniformly bounded too.  This is just the existential-boundedness wrapper
around `gap_family_le_prizeFloorBound_div_shawFloor`; it proves no cancellation theorem.
-/

namespace ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo

open _root_.ProximityGap.Frontier.ShawValueCapstone
open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
open ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge

/-- **Bounded prize-floor ratios plus a nonvanishing Shaw floor bound the exact gap factors.**
If a prize-regime family has some uniform bound on the genuine ratios `Mᵢ/√nᵢ` and every Shaw value
stays above a fixed `c>0`, then the family of exact synthesis gaps `√(log(qᵢ/nᵢ))` is uniformly
bounded.  Thus a constant prize-floor theorem with nonzero Shaw floor has already absorbed the open
door-(iv) `√log` gap.  Pure boundedness packaging; no CORE estimate is claimed. -/
theorem gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ shawValue (q i) (n i) (M i))
    (hPrizeBdd : ∃ B : ℝ, ∀ i, M i / prizeScale (n i) ≤ B) :
    ∃ G : ℝ, ∀ i, Real.sqrt (Real.log (q i / n i)) ≤ G := by
  rcases hPrizeBdd with ⟨B, hB⟩
  exact ⟨B / c, gap_family_le_prizeFloorBound_div_shawFloor hn hnq hc hfloor hB⟩

/-- **Contradiction form: bounded prize-floor ratios and a positive Shaw floor forbid unbounded
`√log` gaps.**  This is the direct no-go wrapper around
`gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor`: a family whose exact synthesis gaps drift
past every proposed bound cannot simultaneously have uniformly bounded genuine prize-floor ratios and
a nonvanishing Shaw-value floor.  Pure order algebra; no CORE estimate or cancellation theorem. -/
theorem not_gap_unbounded_of_prizeFloorRatio_bddAbove_and_shawFloor {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ shawValue (q i) (n i) (M i))
    (hPrizeBdd : ∃ B : ℝ, ∀ i, M i / prizeScale (n i) ≤ B) :
    ¬ (∀ G : ℝ, ∃ i : ι, G < Real.sqrt (Real.log (q i / n i))) := by
  intro hgapUnbounded
  rcases gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor hn hnq hc hfloor hPrizeBdd
    with ⟨G, hG⟩
  rcases hgapUnbounded G with ⟨i, hi⟩
  exact (not_lt_of_ge (hG i)) hi

end ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo

#print axioms ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo.gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor
#print axioms ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo.not_gap_unbounded_of_prizeFloorRatio_bddAbove_and_shawFloor
