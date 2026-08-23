/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSCoveredFraction
import ArkLib.Data.CodingTheory.RSCodewordWeight

/-!
# CS25 Reed–Solomon covered fraction with the explicit near-codeword bound (#82)

The capstone of the #82 chain.  Combining
* `rs_card_close_mul_near_ge` (`|RS|·V ≤ |close|·|near|`, the CS25 covered-fraction bound for RS codes),
* `rsCodeFinset_eq_image` (RS code = evaluation image of degree-`<deg` polynomials),
* `hammingNorm_evalOnPoints_eq_evalSupport_card` (codeword weight = poly eval-support), and
* `card_near_codewords_le` / `card_evalWeight_le_sum` (the MDS weight-enumerator near-count),

gives the **fully explicit covered-fraction bound**

  `|RS| · |B(0,r)| ≤ |close| · ∑_{d≤2r} C(n,d)·q^{d−(n−deg)}`,

i.e. `|close| ≥ |RS|·V / ∑_{d≤2r} A_d` — the proximity-gap target #82 with the near-codeword count
discharged by the explicit MDS weight enumerator.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **RS near-codeword count ≤ MDS weight-enumerator sum.**  The number of RS codewords within
Hamming distance `R` of `0` is at most `∑_{d≤R} C(n,d)·q^{d−(n−deg)}` — RS code = eval image
(`rsCodeFinset_eq_image`), codeword weight = eval-support (`hammingNorm_evalOnPoints…`), and the
polynomial near-count (`card_near_codewords_le`). -/
theorem rs_near_codeword_count_le (domain : ι ↪ F) (deg R : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] :
    ((rsCodeFinset domain deg).filter (fun v => hammingDist (0 : ι → F) v ≤ R)).card
      ≤ ∑ d ∈ Finset.range (R + 1),
          (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  refine le_trans (Finset.card_le_card ?_) (card_near_codewords_le domain deg R)
  intro v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨hvcode, hvwt⟩ := hv
  rw [rsCodeFinset_eq_image, Finset.mem_image] at hvcode
  obtain ⟨p, _, hpv⟩ := hvcode
  rw [Finset.mem_image]
  refine ⟨p, ?_, hpv⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hammingNorm_evalOnPoints_eq_evalSupport_card, hpv]
  rw [hammingDist_zero_left] at hvwt
  exact hvwt

/-- **Explicit CS25 covered-fraction bound for Reed–Solomon codes (#82).**  `|RS|·|B(0,r)| ≤
|close| · ∑_{d≤2r} C(n,d)·q^{d−(n−deg)}` — the covered-fraction bound with the near-codeword count
replaced by the explicit MDS weight-enumerator sum. -/
theorem rs_card_close_mul_sum_ge (domain : ι ↪ F) (deg r : ℕ)
    [Fintype (Polynomial.degreeLT F deg)]
    (hpos : 0 < (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
          * (∑ d ∈ Finset.range (2 * r + 1),
              (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))) := by
  refine le_trans (rs_card_close_mul_near_ge domain deg r hpos) ?_
  exact Nat.mul_le_mul (le_refl _) (rs_near_codeword_count_le domain deg (2 * r))

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_near_codeword_count_le
#print axioms ArkLib.CS25.rs_card_close_mul_sum_ge
