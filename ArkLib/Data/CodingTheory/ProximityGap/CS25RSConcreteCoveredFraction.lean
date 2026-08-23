/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSDimension

/-!
# Concrete Reed–Solomon unique-decoding covered fraction (#82)

Substituting the RS dimension `|RS| = q^k` (`rsCodeFinset_card`) into the unique-decoding covered
fraction `rs_covered_count_ge_unique_decoding` gives the fully concrete statement: for `2r < n−(k−1)`,

  `q^k · V ≤ |close|`,

i.e. the covered set has at least `q^k·V` words.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete RS unique-decoding covered fraction.**  For `1 ≤ k ≤ n` and `2r < n−(k−1)`:
`q^k · V ≤ |close|`. -/
theorem rs_covered_count_concrete (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hnk : k ≤ Fintype.card ι) [Fintype (Polynomial.degreeLT F k)]
    (hr : 2 * r < Fintype.card ι - (k - 1))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    Fintype.card F ^ k * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card := by
  have h := rs_covered_count_ge_unique_decoding domain k r hr hpos
  rwa [rsCodeFinset_card domain k hnk] at h

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_covered_count_concrete
