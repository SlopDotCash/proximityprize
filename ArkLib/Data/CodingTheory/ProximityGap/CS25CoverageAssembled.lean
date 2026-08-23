/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionEntropy
import ArkLib.Data.CodingTheory.ProximityGap.MDSNearCountVolume

/-!
# Assembled RS coverage lower bound (toward T4.17 far half, #82)

Combines the CS25 covered-fraction entropy bound (`rs_covered_fraction_entropy`,
`|RS|·q^{n·H_q(δ)} ≤ (n+1)·#{close}·∑ A_d`) with the MDS near-count qEntropy bound
(`rs_near_count_le_qEntropy`, `∑ A_d ≤ (n+1)·(q+1)^{n·H_{q+1}(2δ)}`) to eliminate the near-count
factor, giving the **fully explicit coverage lower bound**

  `|RS|·q^{n·H_q(δ)} ≤ (n+1)²·(q+1)^{n·H_{q+1}(2δ)}·#{close}`,

i.e. `#{close} ≥ |RS|·q^{n·H_q(δ)} / ((n+1)²·(q+1)^{n·H_{q+1}(2δ)})`. This is the far/coverage half of
the CS25 breakdown band inequality in closed entropy form; the remaining step is the `q`-vs-`(q+1)`
entropy comparison against `hδ_lo`'s deviation term to conclude `#{far}` is small.
-/

open scoped BigOperators
open CodingTheory

namespace ArkLib.CS25

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Assembled RS coverage lower bound.** `|RS|·q^{n·H_q(r/n)} ≤
(n+1)²·(q+1)^{n·H_{q+1}(2r/n)}·#{close}`, eliminating the near-count factor from
`rs_covered_fraction_entropy` via the qEntropy near-count bound. -/
theorem rs_close_count_ge_qEntropy (hq : 2 ≤ Fintype.card F) (domain : ι ↪ F) (deg r : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hdeg : deg ≤ Fintype.card ι)
    (hpos : 0 < (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card)
    (hcap : (2 * r : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / ((Fintype.card F + 1 : ℕ) : ℝ)) :
    ((rsCodeFinset domain deg).card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1) ^ 2
          * ((Fintype.card F + 1 : ℕ) : ℝ)
            ^ ((Fintype.card ι : ℝ)
                * qEntropy (Fintype.card F + 1) ((2 * r : ℝ) / (Fintype.card ι : ℝ)))
          * (Finset.univ.filter
              (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card := by
  have hcov := rs_covered_fraction_entropy hq domain deg r hr0 hrn hpos
  have hcap' : ((2 * r : ℕ) : ℝ) / (Fintype.card ι : ℝ)
      ≤ 1 - 1 / ((Fintype.card F + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]; exact hcap
  have hnear := rs_near_count_le_qEntropy (Fintype.card F) (Fintype.card ι) deg (2 * r)
    (by omega) hdeg (by omega) (by omega) hcap'
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hnear
  refine hcov.trans ?_
  -- (n+1)·#close·∑A_d ≤ (n+1)·#close·((n+1)·(q+1)^{nH'}) = (n+1)²·(q+1)^{nH'}·#close
  have hfac : (0 : ℝ) ≤ ((Fintype.card ι : ℝ) + 1)
      * (Finset.univ.filter
          (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card := by positivity
  calc ((Fintype.card ι : ℝ) + 1)
          * (Finset.univ.filter
              (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
          * ((∑ d ∈ Finset.range (2 * r + 1),
              (Fintype.card ι).choose d
                * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) : ℕ) : ℝ)
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (Finset.univ.filter
                (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
            * (((Fintype.card ι : ℝ) + 1)
              * ((Fintype.card F + 1 : ℕ) : ℝ)
                ^ ((Fintype.card ι : ℝ)
                    * qEntropy (Fintype.card F + 1) ((2 * r : ℝ) / (Fintype.card ι : ℝ)))) :=
          mul_le_mul_of_nonneg_left hnear hfac
      _ = _ := by ring

end ArkLib.CS25
