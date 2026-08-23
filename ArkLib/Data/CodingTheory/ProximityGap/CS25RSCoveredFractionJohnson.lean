/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSJohnsonRadius
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSJohnsonRadiusSqrt
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionListSize

/-!
# Concrete Reed–Solomon covered fraction via the Johnson list size (#82)

Synthesis of the two RS threads developed here: the Johnson-radius list-size bound `rs_list_size_le`
(every word has `≤ ℓ` close RS codewords, under the Johnson conditions at the RS minimum distance)
feeds the second-moment covered fraction `covered_count_mul_listSize_ge` (`|𝒞|·V ≤ |close|·L`) to give

  `|RS| · V ≤ |close| · ℓ`,

i.e. `|close| ≥ |RS|·V/ℓ` — the proximity-gap covered fraction for Reed–Solomon in the
Johnson-decoding regime.  (Beyond the Johnson radius — the entropy band — the list size is unbounded,
which is exactly the open content of #141.)  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete RS covered fraction via the Johnson list size (#82).** When the Johnson conditions hold
at the RS minimum distance (so every word has `≤ ℓ` close RS codewords), the covered set satisfies
`|RS|·V ≤ |close|·ℓ`. -/
theorem rs_covered_count_johnson (domain : ι ↪ F) (k : ℕ) [NeZero k] (r ℓ : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (rsCodeFinset domain k).card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card * ℓ := by
  refine covered_count_mul_listSize_ge (rsCodeFinset domain k) r ℓ (fun w => ?_) hpos
  have hlist := rs_list_size_le domain k hq1 hn w r ℓ hP hsq
  rw [closeCount]
  have hfe : (rsCodeFinset domain k).filter (fun c => hammingDist w c ≤ r)
      = (rsCodeFinset domain k).filter (fun c => hammingDist c w ≤ r) := by
    apply Finset.filter_congr; intro c _; rw [hammingDist_comm]
  rw [hfe]; exact hlist

/-- **Existential RS covered fraction up to the Johnson radius (#232).**  The qualitative RS
Johnson-radius theorem supplies a list-size witness `ℓ`, and that witness gives
`|RS|·V ≤ |close|·ℓ`. -/
theorem rs_covered_count_johnson_radius (domain : ι ↪ F) (k : ℕ) [NeZero k]
    (r : ℕ) (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
            - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ∃ ℓ : ℕ,
      (rsCodeFinset domain k).card
          * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
        ≤ (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card
            * ℓ := by
  obtain ⟨ℓ, hL⟩ := rs_johnson_radius domain k r hq1 hn hP hradius
  exact ⟨ℓ, covered_count_mul_listSize_ge (rsCodeFinset domain k) r ℓ hL hpos⟩

/-- **RS covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook
`√(T·B) < A` condition supplies the list-size witness used by the second-moment bound. -/
theorem rs_covered_count_johnson_radius_sqrt
    (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hApos : 0 < ((Fintype.card ι - r : ℕ) : ℝ)
      - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hradius :
      Real.sqrt
          (((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
                - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
        < ((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ∃ ℓ : ℕ,
      (rsCodeFinset domain k).card
          * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
        ≤ (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card
            * ℓ := by
  obtain ⟨ℓ, hL⟩ := rs_johnson_radius_sqrt domain k r hq1 hn hP hApos hradius
  exact ⟨ℓ, covered_count_mul_listSize_ge (rsCodeFinset domain k) r ℓ hL hpos⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_covered_count_johnson
#print axioms ArkLib.CS25.rs_covered_count_johnson_radius
#print axioms ArkLib.CS25.rs_covered_count_johnson_radius_sqrt
