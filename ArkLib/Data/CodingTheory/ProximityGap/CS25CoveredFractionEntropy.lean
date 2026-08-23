/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallEntropy
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSNearBound

/-!
# Entropy-form CS25 covered fraction for Reed–Solomon codes (#82 capstone)

Combining the entropy lower bound on the covered-fraction ball
(`filter_ball_card_ge_qEntropy`: `q^{n·H_q(r/n)} ≤ (n+1)·V`) with the explicit covered-fraction bound
(`rs_card_close_mul_sum_ge`: `|RS|·V ≤ |close|·∑_{d≤2r} A_d`) gives the **entropy (rate) form** of the
CS25 covered fraction:

  `|RS| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · ∑_{d≤2r} A_d`,

i.e. `|close| ≳ |RS| · q^{n·H_q(r/n)} / ((n+1)·∑_{d≤2r} A_d)` — the proximity-gap covered-fraction
target #82 in its asymptotic/rate form, with the ball volume lower-bounded by the entropy and the
near-codeword count upper-bounded by the explicit MDS weight enumerator.  The two ball conventions
(CS25 `univ.filter` vs ListDecodable `hammingBall.ncard`) are reconciled by
`filter_card_eq_hammingBall_ncard`, and the `Δ₀(0,·)`/`Δ₀(·,0)` orientations by `hammingDist_comm`.
-/

namespace ArkLib.CS25

open scoped BigOperators
open CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Entropy-form CS25 covered fraction for RS codes (#82).**  For `q = |F| ≥ 2`, `n = |ι|`,
`0 < r < n`, and `|RS|·V > 0`:
`|RS| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · ∑_{d≤2r} C(n,d)·q^{d−(n−deg)}`,
where `close = {w : Δ₀(w,RS) ≤ r}`.  Equivalently the covered set is at least
`|RS|·q^{n·H_q(r/n)} / ((n+1)·∑_{d≤2r} A_d)`. -/
theorem rs_covered_fraction_entropy (hq : 2 ≤ Fintype.card F) (domain : ι ↪ F) (deg r : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hpos : 0 < (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ((rsCodeFinset domain deg).card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
          * (Finset.univ.filter
              (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
          * (∑ d ∈ Finset.range (2 * r + 1),
              (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))) := by
  have hball := filter_ball_card_ge_qEntropy hq r hr0 hrn
  have hVeq : (Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card
      = (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
    congr 1
    ext w
    simp only [Finset.mem_filter, hammingDist_comm]
  rw [hVeq] at hball
  have hcov' : ((rsCodeFinset domain deg).card : ℝ)
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter
            (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
          * (∑ d ∈ Finset.range (2 * r + 1),
              (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))) := by
    exact_mod_cast rs_card_close_mul_sum_ge domain deg r hpos
  calc ((rsCodeFinset domain deg).card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((rsCodeFinset domain deg).card : ℝ)
            * (((Fintype.card ι : ℝ) + 1)
              * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :=
          mul_le_mul_of_nonneg_left hball (Nat.cast_nonneg _)
      _ = ((Fintype.card ι : ℝ) + 1)
            * (((rsCodeFinset domain deg).card : ℝ)
              * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) := by ring
      _ ≤ ((Fintype.card ι : ℝ) + 1)
            * ((Finset.univ.filter
                (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
              * (∑ d ∈ Finset.range (2 * r + 1),
                  (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)))) :=
          mul_le_mul_of_nonneg_left hcov' (by positivity)
      _ = ((Fintype.card ι : ℝ) + 1)
            * (Finset.univ.filter
                (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
            * (∑ d ∈ Finset.range (2 * r + 1),
                (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))) := by
          ring

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_covered_fraction_entropy
