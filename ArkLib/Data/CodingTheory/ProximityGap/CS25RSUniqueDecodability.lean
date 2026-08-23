/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionUniqueDecoding

/-!
# Reed–Solomon unique decodability (#82)

For `2r < n−(k−1)` (i.e. `r ≤ ⌊(d−1)/2⌋` with `d = n−k+1` the RS minimum distance), every received
word has at most one Reed–Solomon codeword within Hamming distance `r`: RS codes are uniquely
decodable up to half the minimum distance.  Immediate from `closeCount_le_one_of_minDist` and the RS
minimum distance `rsCodeFinset_hammingDist_ge`.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon unique decodability.**  For `2r < n−(k−1)`, every word has at most one RS codeword
within distance `r`. -/
theorem rs_closeCount_le_one (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hr : 2 * r < Fintype.card ι - (k - 1)) (w : ι → F) :
    closeCount (rsCodeFinset domain k) r w ≤ 1 :=
  closeCount_le_one_of_minDist (rsCodeFinset domain k) r (Fintype.card ι - (k - 1)) w
    (fun c hc c' hc' hne => rsCodeFinset_hammingDist_ge domain k c c' hc hc' hne) hr

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_closeCount_le_one
