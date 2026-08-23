/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionListSize

/-!
# Unique-decoding covered fraction (#82)

A fully concrete instance of the second-moment covered fraction `covered_count_mul_listSize_ge`,
with the list-size bound `L = 1` discharged by the triangle inequality in the **unique-decoding
regime** (`2r < d`, distinct codewords at least `d` apart):

  `closeCount 𝒞 r w ≤ 1`   (`closeCount_le_one_of_minDist`),   hence   `|𝒞|·V ≤ |close|`.

No free parameter, `sorry`/`axiom`-free.  (For `2r < d` the radius-`r` balls around distinct
codewords are disjoint, so the covered set is exactly the disjoint union and has size `|𝒞|·V`; this
records the `≥` half cleanly via the second-moment machinery.)
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Unique-decoding list size ≤ 1.**  If distinct codewords of `𝒞` are at Hamming distance ≥ `d`
and `2r < d`, then every word has at most one codeword within distance `r`. -/
theorem closeCount_le_one_of_minDist (𝒞 : Finset (ι → F)) (r d : ℕ) (w : ι → F)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hr : 2 * r < d) :
    closeCount 𝒞 r w ≤ 1 := by
  rw [closeCount, Finset.card_le_one]
  intro c hc c' hc'
  rw [Finset.mem_filter] at hc hc'
  by_contra hne
  have htri : hammingDist c c' ≤ hammingDist c w + hammingDist w c' := hammingDist_triangle c w c'
  have hcw : hammingDist c w ≤ r := by rw [hammingDist_comm]; exact hc.2
  have hd := hmin c hc.1 c' hc'.1 hne
  omega

/-- **Unique-decoding covered fraction.**  In the unique-decoding regime (`2r < d`, distinct
codewords ≥ `d` apart), `|𝒞|·V ≤ |close|`. -/
theorem covered_count_ge_of_minDist (𝒞 : Finset (ι → F)) (r d : ℕ)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hr : 2 * r < d)
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card := by
  have h := covered_count_mul_listSize_ge 𝒞 r 1
    (fun w => closeCount_le_one_of_minDist 𝒞 r d w hmin hr) hpos
  simpa using h

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.closeCount_le_one_of_minDist
#print axioms ArkLib.CS25.covered_count_ge_of_minDist
