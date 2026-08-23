/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionEntropyListSize
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSJohnsonRadius
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSJohnsonRadiusSqrt

/-!
# Entropy/rate-form Reed–Solomon covered fraction via the Johnson list size (#82)

The rate-form counterpart to `rs_covered_count_johnson`.  Feeding the RS Johnson-radius list-size
bound `rs_list_size_le` (every word has `≤ ℓ` close RS codewords) into the entropy-form second-moment
covered fraction `covered_count_entropy_listSize` gives

  `|RS| · q^{n·H_q(r/n)}  ≤  (n+1) · |close| · ℓ`,

the **rate-form proximity-gap covered fraction** for Reed–Solomon in the Johnson-decoding regime
(`|close| ≳ |RS|·q^{nH}/((n+1)ℓ)`).  This is the form used in the proximity-gap literature; the open
content of #141 is the regime beyond the Johnson radius, where `ℓ` is unbounded.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Entropy-form RS covered fraction via the Johnson list size (#82).** Under the Johnson conditions
at the RS minimum distance, `|RS|·q^{n·H_q(r/n)} ≤ (n+1)·|close|·ℓ` — the rate-form proximity-gap
covered fraction for Reed–Solomon in the Johnson-decoding regime. -/
theorem rs_covered_count_johnson_entropy (domain : ι ↪ F) (k : ℕ) [NeZero k] (r ℓ : ℕ)
    (hqf : 2 ≤ Fintype.card F) (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ((rsCodeFinset domain k).card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
          * (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card * ℓ := by
  have hL : ∀ w : ι → F, closeCount (rsCodeFinset domain k) r w ≤ ℓ := by
    intro w
    have hlist := rs_list_size_le domain k hq1 hn w r ℓ hP hsq
    rw [closeCount]
    have hfe : (rsCodeFinset domain k).filter (fun c => hammingDist w c ≤ r)
        = (rsCodeFinset domain k).filter (fun c => hammingDist c w ≤ r) := by
      apply Finset.filter_congr; intro c _; rw [hammingDist_comm]
    rw [hfe]; exact hlist
  exact covered_count_entropy_listSize hqf (rsCodeFinset domain k) r ℓ hr0 hrn hL hpos

/-- **Existential entropy-form RS covered fraction up to the Johnson radius (#232).**
The qualitative RS Johnson-radius theorem supplies a list-size witness `ℓ`, and the entropy
covered-fraction bound uses that witness directly. -/
theorem rs_covered_count_johnson_radius_entropy
    (hqf : 2 ≤ Fintype.card F) (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
            - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ∃ ℓ : ℕ,
      ((rsCodeFinset domain k).card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card
            * ℓ := by
  obtain ⟨ℓ, hL⟩ := rs_johnson_radius domain k r hq1 hn hP hradius
  exact ⟨ℓ, covered_count_entropy_listSize hqf (rsCodeFinset domain k) r ℓ hr0 hrn hL hpos⟩

/-- **Entropy RS covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook
`√(T·B) < A` condition supplies the list-size witness used by the entropy bound. -/
theorem rs_covered_count_johnson_radius_sqrt_entropy
    (hqf : 2 ≤ Fintype.card F) (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
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
      ((rsCodeFinset domain k).card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card
            * ℓ := by
  obtain ⟨ℓ, hL⟩ := rs_johnson_radius_sqrt domain k r hq1 hn hP hApos hradius
  exact ⟨ℓ, covered_count_entropy_listSize hqf (rsCodeFinset domain k) r ℓ hr0 hrn hL hpos⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_covered_count_johnson_entropy
#print axioms ArkLib.CS25.rs_covered_count_johnson_radius_entropy
#print axioms ArkLib.CS25.rs_covered_count_johnson_radius_sqrt_entropy
