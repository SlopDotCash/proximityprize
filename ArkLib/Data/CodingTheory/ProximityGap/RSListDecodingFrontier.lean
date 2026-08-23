/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The Reed–Solomon list-decoding frontier: Johnson radius `<` capacity

This module pins down, as a theorem, *where* the open ABF26 Grand-Challenge prize lives.

The prize (`GrandChallenges.mcaConjecture` / `MCAGS.epsMCAgsPrizeUniversalConjecture`) reduces to a
**polynomial list-size bound** `Λ(RS, r) ≤ poly(n)` for the ordinary Reed–Solomon code up to the
*capacity radius* `1 - ρ` (`ρ` = rate).  The in-tree machinery proves such a bound only up to the
**Johnson radius** `1 - √ρ` (`Lambda_le_of_johnson_sq`, and the weaker Sudan-algebraic
`reedSolomon_Lambda_le`), and *refutes* over-aggressive caps above capacity
(`not_ordinaryRSCapacityAtPrizeRates_of_elias_volume_gt`).

The single fact this file establishes — `johnson_radius_lt_capacity` — is that for every code of
rate `ρ ∈ (0,1)` the Johnson radius is **strictly below** capacity:

  `1 - √ρ  <  1 - ρ`      (equivalently `ρ < √ρ`, i.e. `ρ < 1`).

Hence the gap `(1 - √ρ, 1 - ρ)` in which the prize lives is **non-empty**, so no Johnson-level
argument can close it: the irreducible open content is genuinely the *beyond-Johnson* list-size
bound (Reed–Solomon list-decoding up to capacity — resolved in the literature only recently, e.g.
Brakensiek–Gopi–Makam 2023 / Guo–Zhang, via higher-order-MDS / GM-MDS machinery absent from
mathlib).  This file does not claim to close that gap; it certifies, with a build-checked proof,
that the gap is real.
-/

namespace ProximityGap

open scoped NNReal

/-- **A positive rate below `1` is strictly below its own square root.**  For `r ∈ (0,1)`,
`r = r·r·(1/r) `… concretely `r² = r·r < r·1 = r`, so by monotonicity of `NNReal.sqrt`,
`r < √r`.  This is the
arithmetic heart of "Johnson radius `<` capacity": with `r = ρ` the code rate, `√ρ` is the Johnson
parameter and `ρ` the capacity parameter. -/
theorem self_lt_sqrt_of_pos_of_lt_one {r : ℝ≥0} (hpos : 0 < r) (hlt : r < 1) :
    r < NNReal.sqrt r := by
  have hsqr : r ^ 2 < r := by
    calc r ^ 2 = r * r := by rw [pow_two]
      _ < r * 1 := by exact mul_lt_mul_of_pos_left hlt hpos
      _ = r := mul_one r
  have hsqrt : NNReal.sqrt (r ^ 2) < NNReal.sqrt r :=
    (NNReal.sqrt_lt_sqrt).2 hsqr
  simpa [NNReal.sqrt_sq] using hsqrt

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F]

/-- **The Johnson radius is strictly below the list-decoding capacity radius.**

For a Reed–Solomon code whose rate `ρ := LinearCode.rate (RS deg domain)` lies in `(0,1)`, the
Johnson decoding radius `1 - √ρ` (`= 1 - sqrtRate deg domain`) is strictly less than the capacity
radius `1 - ρ`.  Therefore the radius interval `(1 - √ρ, 1 - ρ)` — exactly the regime the GS prize
asks about — is non-empty, and the prize cannot be settled by any bound that stops at the Johnson
radius. -/
theorem johnson_radius_lt_capacity (deg : ℕ) (domain : ι ↪ F)
    (hpos : 0 < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0))
    (hlt : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) < 1) :
    (1 : ℝ) - (ReedSolomon.sqrtRate deg domain : ℝ)
      < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ) := by
  have key : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
      < ReedSolomon.sqrtRate deg domain :=
    self_lt_sqrt_of_pos_of_lt_one hpos hlt
  have hcast : ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ)
      < (ReedSolomon.sqrtRate deg domain : ℝ) := by exact_mod_cast key
  exact sub_lt_sub_left hcast 1

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.self_lt_sqrt_of_pos_of_lt_one
#print axioms ProximityGap.johnson_radius_lt_capacity
