/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Research.ProximityPrize.MCAPlateauWindow

/-!
# An unconditional exact faithful MCA lattice threshold (Issue #70)

All existing exact/bracket results for the faithful Grand-MCA lattice threshold
`mcaThreshold` consume external-paper witnesses (BCHKS25 Johnson, CS25 breakdown, DG25
sampling). This file proves the **first exact threshold with no external hypotheses**, by
combining the two *unconditional* witnesses proved in `MCAPlateauWindow.lean`:

* lower — `le_mcaThreshold_ofChooseLe` (the canonical-witness window bound) at the radius
  `δ = 1 - (k+2)/n`, whose lattice index is `n - k - 2`;
* upper — `mcaThreshold_lt_capacityPred_of_subsetSums` at `δ = 1 - (k+1)/n`, whose lattice
  index is `n - k - 1`.

Those two lattice indices are **consecutive**, so any threshold sandwiched in
`[n-k-2, n-k-1)` is forced to the single value `n - k - 2`. Hence, in the field band

  `2¹²⁸ · C(n, k+2) ≤ q < 2¹²⁸ · |Σ_{k+1}(L)|`,

the faithful MCA lattice threshold equals `n - k - 2` exactly, with no external-paper
hypotheses (`mcaThreshold_eq_capacityPredPred_unconditional`); the field band itself is a
hypothesis.

**Scope of the band (R-324).**  Because `|Σ_{k+1}(L)| ≤ C(n, k+1) ≤ C(n, k+2)` once
`n ≥ 2k + 3`, the band is **empty in the whole low-rate regime** (`k + 1 < n/2`, including
rate `1/4` and `1/2` production instances): `lt_two_mul_add_three_of_fieldBand` proves the
band forces `n < 2k + 3`.  The band can be nonempty only at high rate.  A compatible instance:
`k = n - 2` (`n ≥ 2`), where `C(n, k+2) = 1` and the `n` sums `(∑ L) - Lᵢ` are distinct, so
`|Σ_{n-1}| = n` and the band is `2¹²⁸ ≤ q < n · 2¹²⁸`, which contains primes by Bertrand's
postulate; there the theorem gives threshold `0` (this instance is a paper example, not
formalized here).  A low-rate exact pin needs a different lower certificate.

**Lattice maximum versus real supremum.**  The result pins the maximal good point of the
`1/n` LATTICE (`mcaThreshold`, and its radius `mcaLatticePoint`).  It is not automatically the
operational supremum of good real radii: a bad lattice boundary point can still be that real
supremum without being good.

The reusable arithmetic helper `latticeIndexOf_one_sub_div_val`
(`⌊(1 - j/n)·n⌋ = n - j`) and `ceil_one_sub_one_sub_div` (`⌈(1-(1-j/n))·n⌉ = j`) pin the
lattice indices of the special radii `1 - j/n`.

## References

- [ABF26] §1 Grand MCA Challenge; faithful `1/n`-lattice threshold.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators
open GrandChallenges GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Arithmetic of the special radii `1 - j/n` -/

/-- `(1 - j/n) * n = n - j` in `ℝ≥0` for `j ≤ n` (truncated sub; no `Nat.cast_sub` for
`ℝ≥0`, so the cast goes through `↑(n-j) + ↑j = ↑n`). -/
theorem one_sub_div_mul_cast (j : ℕ) (hj : j ≤ Fintype.card ι) :
    ((1 : ℝ≥0) - (j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) =
      ((Fintype.card ι - j : ℕ) : ℝ≥0) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [tsub_mul, one_mul, div_mul_cancel₀ _ hn0]
  -- `↑n - ↑j = ↑(n-j)` via `↑(n-j) + ↑j = ↑n`.
  have hadd : ((Fintype.card ι - j : ℕ) : ℝ≥0) + (j : ℝ≥0) = (Fintype.card ι : ℝ≥0) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hj]
  exact (eq_tsub_of_add_eq hadd).symm

/-- The lattice index of the radius `1 - j/n` is `n - j` (for `j ≤ n`). -/
theorem latticeIndexOf_one_sub_div_val (j : ℕ) (hj : j ≤ Fintype.card ι) :
    (latticeIndexOf (ι := ι) (1 - (j : ℝ≥0) / (Fintype.card ι : ℝ≥0)) tsub_le_self).val =
      Fintype.card ι - j := by
  rw [latticeIndexOf_val, one_sub_div_mul_cast j hj, Nat.floor_natCast]

/-- `⌈(1 - (1 - j/n))·n⌉ = j` for `j ≤ n`: the agreement level of the radius `1 - j/n`. -/
theorem ceil_one_sub_one_sub_div (j : ℕ) (hj : j ≤ Fintype.card ι) :
    ⌈((1 : ℝ≥0) - (1 - (j : ℝ≥0) / (Fintype.card ι : ℝ≥0))) * (Fintype.card ι : ℝ≥0)⌉₊ = j := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hdle : (j : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hj
  -- `1 - (1 - j/n) = j/n`, then `(j/n)·n = j`, then `⌈↑j⌉ = j`.
  rw [tsub_tsub_cancel_of_le hdle, div_mul_cancel₀ _ hn0, Nat.ceil_natCast]

/-! ## The unconditional exact threshold -/

/-- **Unconditional exact faithful MCA lattice threshold (Issue #70).**

For `C := RS[F, domain, k]` at the prize threshold `ε* = 2⁻¹²⁸`, in the field band

  `2¹²⁸ · C(n, k+2) ≤ q < 2¹²⁸ · |Σ_{k+1}(L)|`   (`hlo`, `hsmall`),

the faithful MCA lattice threshold is exactly `n - k - 2`. **No external-paper witness is
used** — both ends come from the unconditional plateau/window/subset-sum theorems of
`MCAPlateauWindow.lean`, and the two bracketing lattice indices `n-k-2`, `n-k-1` are
consecutive.

`hlo` is the window numeric at agreement level `k+2`: `C(n, k+2)/q ≤ ε*`.  The band
(`hlo` with `hsmall`) is unsatisfiable when `n ≥ 2k + 3`
(`lt_two_mul_add_three_of_fieldBand`), so this theorem applies only at high rate; the value
pinned is the maximal good lattice index, not necessarily the real-radius supremum. -/
theorem mcaThreshold_eq_capacityPredPred_unconditional (domain : ι ↪ F) {k : ℕ}
    (hk2 : k + 2 ≤ Fintype.card ι)
    (hlo : ((Fintype.card ι).choose (k + 2) : ENNReal) / (Fintype.card F : ENNReal) ≤
      (ProximityGap.epsStar : ENNReal))
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F))
      ProximityGap.epsStar) :
    (mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar hne).val =
      Fintype.card ι - k - 2 := by
  classical
  have hk1 : k + 1 ≤ Fintype.card ι := by omega
  -- The lower radius `δ_lo := 1 - (k+2)/n`, agreement level `k+2`.
  have hdlo_le : ((1 : ℝ≥0) - ((k : ℝ≥0) + 2) / (Fintype.card ι : ℝ≥0)) ≤ 1 := tsub_le_self
  -- Rewrite `(k:ℝ≥0)+2 = ((k+2 : ℕ) : ℝ≥0)` to reuse the `j`-helpers.
  have hcast2 : ((k : ℝ≥0) + 2) = ((k + 2 : ℕ) : ℝ≥0) := by push_cast; ring
  -- Lower witness: `latticeIndexOf δ_lo ≤ mcaThreshold`.
  have hlower :
      latticeIndexOf (ι := ι) (1 - ((k : ℝ≥0) + 2) / (Fintype.card ι : ℝ≥0)) hdlo_le ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar hne := by
    refine le_mcaThreshold_ofChooseLe domain k hdlo_le ?_ hne
    -- the window count at this radius is `C(n, max(⌈(1-δ_lo)n⌉, k+1)) = C(n, k+2)`.
    have hceil : ⌈((1 : ℝ≥0) - (1 - ((k : ℝ≥0) + 2) / (Fintype.card ι : ℝ≥0))) *
        (Fintype.card ι : ℝ≥0)⌉₊ = k + 2 := by
      rw [hcast2]; exact ceil_one_sub_one_sub_div (k + 2) hk2
    rw [hceil, max_eq_left (by omega)]
    exact hlo
  -- Upper witness: `mcaThreshold < latticeIndexOf (1 - (k+1)/n)`.
  have hupper := mcaThreshold_lt_capacityPred_of_subsetSums domain hk1 hsmall hne
  -- Lattice index values.
  -- `latticeIndexOf … .val = ⌊…⌋₊` first (strips the dependent `≤ 1` proof arg, so the
  -- subsequent `(k:ℝ≥0)+j → ↑(k+j)` cast rewrite has a type-correct motive).
  have hlo_val :
      (latticeIndexOf (ι := ι) (1 - ((k : ℝ≥0) + 2) / (Fintype.card ι : ℝ≥0)) hdlo_le).val =
        Fintype.card ι - (k + 2) := by
    rw [latticeIndexOf_val, hcast2, one_sub_div_mul_cast (k + 2) hk2, Nat.floor_natCast]
  have hhi_val :
      (latticeIndexOf (ι := ι) (1 - ((k : ℝ≥0) + 1) / (Fintype.card ι : ℝ≥0)) tsub_le_self).val =
        Fintype.card ι - (k + 1) := by
    have hcast1 : ((k : ℝ≥0) + 1) = ((k + 1 : ℕ) : ℝ≥0) := by push_cast; ring
    rw [latticeIndexOf_val, hcast1, one_sub_div_mul_cast (k + 1) hk1, Nat.floor_natCast]
  -- Sandwich the `Fin` value: `n-(k+2) ≤ thr.val < n-(k+1) = (n-(k+2)) + 1`.
  have hle_val := (Fin.le_iff_val_le_val).mp hlower
  have hlt_val := (Fin.lt_iff_val_lt_val).mp hupper
  rw [hlo_val] at hle_val
  rw [hhi_val] at hlt_val
  -- `n-(k+2) ≤ thr.val < n-(k+1)` with `k+2 ≤ n` forces `thr.val = n - k - 2`.
  omega

/-- **Radius form of the unconditional exact threshold.** The faithful maximal good radius
`δ*` (the lattice point at the threshold index) equals `(n-k-2)/n` in the band.  The band is
nonempty only at high rate (`lt_two_mul_add_three_of_fieldBand`), and this is the maximal good
lattice radius, not automatically the supremum of good real radii. -/
theorem mcaThreshold_latticePoint_eq_capacityPredPred_unconditional (domain : ι ↪ F) {k : ℕ}
    (hk2 : k + 2 ≤ Fintype.card ι)
    (hlo : ((Fintype.card ι).choose (k + 2) : ENNReal) / (Fintype.card F : ENNReal) ≤
      (ProximityGap.epsStar : ENNReal))
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F))
      ProximityGap.epsStar) :
    mcaLatticePoint (Fintype.card ι)
        (mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ProximityGap.epsStar hne) =
      ((Fintype.card ι - k - 2 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  unfold mcaLatticePoint
  rw [mcaThreshold_eq_capacityPredPred_unconditional domain hk2 hlo hsmall hne]

/-! ## Scope of the field band -/

/-- **The field band forces high rate: `n < 2k + 3`.**  Since `ε* = 2⁻¹²⁸`, the hypothesis
`hlo` of `mcaThreshold_eq_capacityPredPred_unconditional` says `2¹²⁸ · C(n, k+2) ≤ q`; together
with `hsmall` (`q < 2¹²⁸ · |Σ_{k+1}|`) and `|Σ_{k+1}| ≤ C(n, k+1)` this is impossible whenever
`n ≥ 2k + 3`, because then `C(n, k+1) ≤ C(n, k+2)`.  So the exact theorem has **no instance**
in the low-rate regime `k + 1 < n/2` (in particular none at rate `1/4` or `1/2`). -/
theorem lt_two_mul_add_three_of_fieldBand (domain : ι ↪ F) {k : ℕ}
    (hband : 2 ^ (128 : ℕ) * (Fintype.card ι).choose (k + 2) ≤ Fintype.card F)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    Fintype.card ι < 2 * k + 3 := by
  classical
  by_contra hn
  push_neg at hn
  have hΣ : (subsetSumsKplus1 domain k).card ≤ (Fintype.card ι).choose (k + 1) := by
    unfold subsetSumsKplus1
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_powersetCard, Finset.card_univ]
  have hch : (Fintype.card ι).choose (k + 1) ≤ (Fintype.card ι).choose (k + 2) := by
    rcases Nat.lt_or_ge (2 * k + 3) (Fintype.card ι) with h | h
    · exact Nat.choose_le_succ_of_lt_half_left (by omega)
    · exact (Nat.choose_symm_of_eq_add (by omega)).le
  have := Nat.mul_le_mul_left (2 ^ (128 : ℕ)) (hΣ.trans hch)
  omega
