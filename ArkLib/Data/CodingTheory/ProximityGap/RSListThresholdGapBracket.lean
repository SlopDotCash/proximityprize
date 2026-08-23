/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdJohnsonGeneral
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdOverflowSharpGen

/-!
# Strict two-sided bracket on the list-decoding threshold (#232)

Canonical capstone tying the lower (Johnson) and sharpened upper (overflow ⇒ list-decoding capacity)
bounds into a single *strict* two-sided trap of the genuine threshold:

  `rs_ld_threshold_gap_bracket` — for `RS[F, α, k]`, `m = 1`, given a Johnson-gap lower witness at
  index `j_lo` (with budget-clearing list cap) and a base-code overflow at index `j_hi`:

      `j_lo  ≤  listLatticeThreshold  <  j_hi`.

The lower side is `rs_ld_threshold_johnson_pin_general` (second-moment Johnson bound, reaches the
Johnson radius `1 − √ρ`); the strict upper side is `listLatticeThreshold_lt_of_overflow` fed by a
base-code list-size lower bound. Instantiated with `j_lo` at the Johnson radius and `j_hi` at the
capacity-exponent overflow threshold (via `rs_lambda_gt_of_capExp_overflow`), this traps `δ*` in
`[1 − √ρ, δ_LD)` with `δ_LD = H_q⁻¹(1 − ρ)` the list-decoding capacity — i.e. strictly inside the open
Johnson→capacity gap, with the conjectured value `δ_LD` as the (excluded) upper end.

The only remaining open statement is the matching lower bound `δ* ≥ δ_LD`, which is exactly the
$1M prize. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Strict two-sided bracket on the genuine list-decoding threshold.** For `RS[F, α, k]`, single
column, a Johnson-gap lower witness at `j_lo` (budget cleared by its list cap) and a base-code
overflow at `j_hi` together trap the lattice threshold strictly: `j_lo ≤ δ* < j_hi`. -/
theorem rs_ld_threshold_gap_bracket
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (α : ι ↪ F) {k j_lo j_hi : ℕ} [NeZero k]
    (hk : k ≤ Fintype.card ι) (hjlo : j_lo ≤ Fintype.card ι)
    (hgap : Fintype.card ι * (k - 1) < (Fintype.card ι - j_lo) ^ 2)
    {ε_star : ℝ≥0} (hε : ε_star < 1)
    (hbud : ((Fintype.card ι ^ 2 /
        ((Fintype.card ι - j_lo) ^ 2 - Fintype.card ι * (k - 1)) : ℕ) : ENNReal)
      ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hover : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda ((ReedSolomon.code α k : Set (ι → F)))
            (((j_hi : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal)) :
    ∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α k : Set (ι → F)) 1 ε_star).Nonempty,
      j_lo ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne
        ∧ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code α k : Set (ι → F)) 1 ε_star hne < j_hi := by
  obtain ⟨hne, hlo, _⟩ := rs_ld_threshold_johnson_pin_general α hk hjlo hgap hε hbud
  exact ⟨hne, hlo, listLatticeThreshold_lt_of_overflow
    (C := (ReedSolomon.code α k : Set (ι → F))) (m := 1) (j := j_hi) hover hne⟩

#print axioms rs_ld_threshold_gap_bracket

end ProximityGap
