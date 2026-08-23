/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionEntropy

/-!
# Entropy-form CS25 covered fraction — division (lower-bound) form (#82)

The directly interpretable "covered fraction is large" form of `rs_covered_fraction_entropy`: the
number of points within distance `r` of the Reed–Solomon code is at least

  `|RS| · q^{n·H_q(r/n)} / ((n+1) · ∑_{d≤2r} A_d)`.
-/

namespace ArkLib.CS25

open scoped BigOperators
open CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **CS25 covered fraction ≥ entropy bound (Reed–Solomon, #82).**
`|RS|·q^{n·H_q(r/n)} / ((n+1)·∑_{d≤2r} A_d) ≤ |close|` — the division (lower-bound) form of
`rs_covered_fraction_entropy`. -/
theorem rs_covered_fraction_entropy_div (hq : 2 ≤ Fintype.card F) (domain : ι ↪ F) (deg r : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hpos : 0 < (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ((rsCodeFinset domain deg).card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1)
            * (∑ d ∈ Finset.range (2 * r + 1),
                (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))))
      ≤ (Finset.univ.filter
          (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card := by
  have hsum_pos : (0 : ℝ) < (∑ d ∈ Finset.range (2 * r + 1),
      (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) : ℕ) := by
    have : (0 : ℕ) < ∑ d ∈ Finset.range (2 * r + 1),
        (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
      apply Finset.sum_pos'
      · intro i _; positivity
      · exact ⟨0, Finset.mem_range.mpr (by omega), by
          simp only [Nat.choose_zero_right, one_mul]
          exact pow_pos (by omega) _⟩
    exact_mod_cast this
  rw [div_le_iff₀ (by positivity)]
  have h := rs_covered_fraction_entropy hq domain deg r hr0 hrn hpos
  calc ((rsCodeFinset domain deg).card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (Finset.univ.filter
                (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
            * (∑ d ∈ Finset.range (2 * r + 1),
                (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d))) := h
      _ = (Finset.univ.filter
              (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
            * (((Fintype.card ι : ℝ) + 1)
              * (∑ d ∈ Finset.range (2 * r + 1),
                  (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)))) := by
          ring

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_covered_fraction_entropy_div
