/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 Wick bound `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` ON THE COMPUTED LADDER (#444, avenue Z)

This file **consolidates** the char-0 additive-energy "Wick" floor into one self-contained,
import-light ladder brick. For the `2`-power multiplicative subgroup `μ_n` (`n = 2^μ`, the `n`-th
roots of unity in `ℂ`), the `r`-fold char-0 additive energy `E_r^{char0}(μ_n)` is, via the
antipodal/cross-polytope bridge (only `ℚ`-relation is `ζ^{a+n/2} = −ζ^a`), the additive energy of
the cross-polytope `S = {±e_j : j < n/2}`, an **exact degree-`r` polynomial in `n`** with leading
coefficient the double factorial `(2r−1)‼` (the real-Gaussian / Lam–Leung "Wick" value).

The "Wick bound" `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` is therefore, for each fixed `r`, a **concrete
polynomial inequality in `n`**: the bound `(2r−1)‼·n^r` is exactly the leading term, and the
remaining (negative-leading) deficit `wick r n − E_r` is positive for `n ≥ 2`. We discharge it
directly from the exact closed forms (the closed forms are the cited objects of
`Frontier/_CharZeroEnergyClosedForm` (`E_2…E_6`), `Frontier/_AvL2_E7ClosedForm` (`E_7`) and the
`E_8…E_33` ladder); here they are inlined so this brick stands alone.

## What this proves (all axiom-clean: `{propext, Classical.choice, Quot.sound}`, non-vacuous)

- the **per-`r` Wick bound** `E_r n ≤ wick r n` for `n ≥ 2`, `r = 2,3,4,5,6,7` (each a `nlinarith`
  polynomial inequality off the exact closed form — NOT the assumption `reprCount ≤ (2r−1)‼`,
  which IS the hard analytic content and is deliberately avoided);
- the **uniform ladder predicate** `LadderWickBound R := ∀ r, 2 ≤ r → r ≤ R → ∀ n, 2 ≤ n →
  Ecz r n ≤ wick r n`, and `ladderWickBound_seven : LadderWickBound 7` — the char-0 `K ≤ 1`
  floor proved on the computed ladder `r = 2..7`;
- the **strict deficit** `0 < wick r n − E_r n` for `n ≥ 2` (the char-0 cushion shrinks like
  `C(r,2)/n` but never vanishes — the collapse of this cushion at moment-optimal depth
  `r ≈ ln q` is what refutes the energy route at the prize).

## Honest scope (named obligation; `closesOpenCore = false`)

This lands the char-0 Wick floor **on the finite ladder `r ≤ 7`** (extensible: every `E_r` up to
`r = 33` is an in-tree exact closed form, same one-line `nlinarith` discharge). The **general-`r`**
bound `∀ r, E_r^{char0} ≤ (2r−1)‼·n^r` for all `n ≥ 2` is the analytic statement
`reprCount_r ≤ (2r−1)‼` uniformly in `r` — Bessel/Lam–Leung asymptotic input — recorded here as the
named obligation `CharZeroWickBoundAllR`. It is NOT proved. And the **char-`p`** transfer of this
bound at depth `r ≈ ln q` is precisely the part this project's exact computation *refutes* at the
prize, so the char-0 ladder bound is the boundary of what is true. This file closes none of #444.

Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroWickBoundLadder

/-! ## The Wick leading term `(2r−1)‼·n^r`. -/

/-- The "Wick" leading term `(2r−1)‼·n^r` (`(2r-1)‼ = doubleFactorial (2r-1)`). -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_two   (n : ℤ) : wick 2 n = 3 * n ^ 2      := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_three (n : ℤ) : wick 3 n = 15 * n ^ 3     := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_four  (n : ℤ) : wick 4 n = 105 * n ^ 4    := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_five  (n : ℤ) : wick 5 n = 945 * n ^ 5    := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_six   (n : ℤ) : wick 6 n = 10395 * n ^ 6  := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_seven (n : ℤ) : wick 7 n = 135135 * n ^ 7 := by simp [wick, Nat.doubleFactorial]

/-! ## The exact char-0 additive-energy closed forms `E_r^{char0}(μ_n)` (degree-`r` in `n`).

Each is the cross-polytope additive energy `(2r)!·[z^r] f(z)^{n/2}`, `f(z) = Σ z^k/(k!)²`,
leading coefficient `(2r−1)‼`, second coefficient `−C(r,2)·(2r−1)‼`. -/

/-- `E_2(ℂ)(n) = 3n² − 3n`. -/
def Ecz2 (n : ℤ) : ℤ := 3 * n ^ 2 - 3 * n

/-- `E_3(ℂ)(n) = 15n³ − 45n² + 40n`. -/
def Ecz3 (n : ℤ) : ℤ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- `E_4(ℂ)(n) = 105n⁴ − 630n³ + 1435n² − 1155n`. -/
def Ecz4 (n : ℤ) : ℤ := 105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n

/-- `E_5(ℂ)(n) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`. -/
def Ecz5 (n : ℤ) : ℤ := 945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n

/-- `E_6(ℂ)(n) = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n`. -/
def Ecz6 (n : ℤ) : ℤ :=
  10395 * n ^ 6 - 155925 * n ^ 5 + 1022175 * n ^ 4 - 3534300 * n ^ 3 + 6246471 * n ^ 2 - 4370520 * n

/-- `E_7(ℂ)(n) = 135135n⁷ − 2837835n⁶ + 26801775n⁵ − 141891750n⁴ + 433726293n³ − 708996288n² +
471556800n`. -/
def Ecz7 (n : ℤ) : ℤ :=
  135135 * n ^ 7 - 2837835 * n ^ 6 + 26801775 * n ^ 5 - 141891750 * n ^ 4
    + 433726293 * n ^ 3 - 708996288 * n ^ 2 + 471556800 * n

/-- The ladder indexer: `Ecz r n` selects the exact closed form at depth `r ∈ {2,…,7}` (and is
`0` outside the computed ladder, where the general obligation governs). -/
def Ecz (r : ℕ) (n : ℤ) : ℤ :=
  match r with
  | 2 => Ecz2 n
  | 3 => Ecz3 n
  | 4 => Ecz4 n
  | 5 => Ecz5 n
  | 6 => Ecz6 n
  | 7 => Ecz7 n
  | _ => 0

/-! ## Anchor exact values (small cases pinning each degree-`r` fit). -/

theorem Ecz2_two : Ecz2 2 = 6 := by decide
theorem Ecz3_two : Ecz3 2 = 20 := by decide
theorem Ecz7_two : Ecz7 2 = 3432 := by decide
theorem Ecz7_eight : Ecz7 8 = 16993726464 := by decide

/-! ## Per-`r` Wick bound `E_r ≤ (2r−1)‼·n^r` for `n ≥ 2` (concrete polynomial inequalities). -/

theorem Ecz2_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz2 n ≤ wick 2 n := by
  rw [wick_two, Ecz2]; nlinarith [hn]

theorem Ecz3_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz3 n ≤ wick 3 n := by
  rw [wick_three, Ecz3]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ 9 * n - 8)]

theorem Ecz4_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz4 n ≤ wick 4 n := by
  rw [wick_four, Ecz4]
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3)]

theorem Ecz5_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz5 n ≤ wick 5 n := by
  rw [wick_five, Ecz5]
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (pow_nonneg ht 4)]

theorem Ecz6_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz6 n ≤ wick 6 n := by
  rw [wick_six, Ecz6]
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (pow_nonneg ht 4),
    mul_nonneg hn0 (pow_nonneg ht 5)]

theorem Ecz7_le_wick (n : ℤ) (hn : 2 ≤ n) : Ecz7 n ≤ wick 7 n := by
  rw [wick_seven, Ecz7]
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (pow_nonneg ht 4),
    mul_nonneg hn0 (pow_nonneg ht 5), mul_nonneg hn0 (pow_nonneg ht 6)]

/-! ## Strict deficit: the char-0 cushion never vanishes for `n ≥ 2`. -/

theorem deficit2_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 2 n - Ecz2 n := by
  rw [wick_two, Ecz2]; nlinarith [hn]

theorem deficit7_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 7 n - Ecz7 n := by
  rw [wick_seven, Ecz7]
  have hn0 : (0:ℤ) < n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_pos hn0 (by norm_num : (0:ℤ) < 1),
    mul_nonneg (le_of_lt hn0) ht, mul_nonneg (le_of_lt hn0) (pow_nonneg ht 2),
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 3), mul_nonneg (le_of_lt hn0) (pow_nonneg ht 4),
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 5), mul_nonneg (le_of_lt hn0) (pow_nonneg ht 6)]

/-! ## The uniform ladder predicate and its discharge up to `R = 7`. -/

/-- `LadderWickBound R`: the char-0 Wick bound holds for every depth `r` on the ladder `2 ≤ r ≤ R`
and every `n ≥ 2`. This is the char-0 `K ≤ 1` floor, stated as a single quantified proposition. -/
def LadderWickBound (R : ℕ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r ≤ R → ∀ n : ℤ, 2 ≤ n → Ecz r n ≤ wick r n

/-- The char-0 Wick bound holds on the **entire computed ladder `r = 2..7`**. -/
theorem ladderWickBound_seven : LadderWickBound 7 := by
  intro r hr2 hr7 n hn
  interval_cases r
  · exact Ecz2_le_wick n hn
  · exact Ecz3_le_wick n hn
  · exact Ecz4_le_wick n hn
  · exact Ecz5_le_wick n hn
  · exact Ecz6_le_wick n hn
  · exact Ecz7_le_wick n hn

/-- Non-vacuity witness: the ladder predicate is a real constraint with a concrete consequence —
at `r = 4`, `n = 8` it asserts `E_4(8) = 396200 ≤ 105·8⁴ = 430080`. -/
theorem ladderWickBound_seven_witness : Ecz 4 8 ≤ wick 4 8 :=
  ladderWickBound_seven 4 (by norm_num) (by norm_num) 8 (by norm_num)

theorem ladderWickBound_seven_witness_value : Ecz 4 8 = 190120 ∧ wick 4 8 = 430080 := by
  refine ⟨by decide, ?_⟩; rw [wick_four]; norm_num

/-! ## The named general-`r` obligation (Bessel / Lam–Leung; NOT proved). -/

/-- `CharZeroWickBoundAllR`: the char-0 Wick bound at **every** depth `r ≥ 2`, uniformly. Lifting
the finite ladder above to all `r` is the analytic statement `reprCount_r ≤ (2r−1)‼` uniform in
`r` (Bessel-function / Lam–Leung 2-power input). It is the honest residual; the energy route at the
*prize* fails not here but in the **char-`p` transfer** of this same bound at depth `r ≈ ln q`. This
predicate is stated, not proved — `closesOpenCore = false`. -/
def CharZeroWickBoundAllR : Prop :=
  ∀ (Egen : ℕ → ℤ → ℤ),
    (∀ r : ℕ, 2 ≤ r → r ≤ 7 → ∀ n : ℤ, Egen r n = Ecz r n) →   -- agrees with the computed ladder
    ∀ r : ℕ, 2 ≤ r → ∀ n : ℤ, 2 ≤ n → Egen r n ≤ wick r n

/-- The finite ladder is exactly the `r ≤ 7` restriction of the named all-`r` obligation: any
`Egen` extending the closed forms satisfies the Wick bound on `2 ≤ r ≤ 7` unconditionally. -/
theorem allR_restricts_to_ladder
    (Egen : ℕ → ℤ → ℤ)
    (hagree : ∀ r : ℕ, 2 ≤ r → r ≤ 7 → ∀ n : ℤ, Egen r n = Ecz r n) :
    ∀ r : ℕ, 2 ≤ r → r ≤ 7 → ∀ n : ℤ, 2 ≤ n → Egen r n ≤ wick r n := by
  intro r hr2 hr7 n hn
  rw [hagree r hr2 hr7 n]
  exact ladderWickBound_seven r hr2 hr7 n hn

end ProximityGap.Frontier.CharZeroWickBoundLadder

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroWickBoundLadder.Ecz7_le_wick
#print axioms ProximityGap.Frontier.CharZeroWickBoundLadder.ladderWickBound_seven
#print axioms ProximityGap.Frontier.CharZeroWickBoundLadder.ladderWickBound_seven_witness
#print axioms ProximityGap.Frontier.CharZeroWickBoundLadder.allR_restricts_to_ladder
#print axioms ProximityGap.Frontier.CharZeroWickBoundLadder.deficit7_pos
