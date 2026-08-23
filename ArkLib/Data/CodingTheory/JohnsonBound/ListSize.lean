/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The Johnson list-size bound (combinatorial, isolated)

This file proves the classical **q-ary Johnson bound** on the number of codewords of a code that lie
within a given Hamming radius of a fixed word — the foundational list-decoding bound underlying the
correlated-agreement / proximity-gap "true form" (the Johnson radius `δ < 1 - √ρ`), which is
**absent from mathlib**.

It is deliberately **self-contained**: it imports only `Mathlib` (Hamming distance, big operators,
the Cauchy–Schwarz sum inequality), so it builds independently of the rest of ArkLib. The
"universal-over-all-codes" form of the proximity gap is false; the correct form lives at the Johnson
radius, whose combinatorial heart is the bound below.

## Main statement

`card_mul_johnsonDenom_le`: for a finite set of codewords `C` with pairwise distance `≥ d`, all
within distance `e` of a word `w`, writing `n = |ι|`:

  `(C.card) · ((n - e)² - n·(n - d)) ≤ n · d`.

In the **Johnson regime** `(n - e)² > n·(n - d)` this yields `card_le_div` :
`C.card ≤ n·d / ((n - e)² - n·(n - d))`.

## Proof

Double counting. For each coordinate `i`, `colCount i` is the number of codewords agreeing with `w`
at `i`. Then `∑ i, colCount i = ∑ c, agree(c, w) ≥ |C|·(n - e)` and, by Cauchy–Schwarz,
`(∑ i, colCount i)² ≤ n · ∑ i, (colCount i)²`. Expanding `∑ i, (colCount i)²` over ordered pairs of
codewords, the diagonal contributes `∑ c, agree(c, w) ≤ |C|·n` and each off-diagonal pair `(c, c')`
contributes `agree(c, c') ≤ n - d`. Combining and cancelling one factor of `|C|` gives the bound.
-/

open scoped BigOperators

namespace ArkLib.JohnsonBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Sigma : Type*} [DecidableEq Sigma]

/-- The number of coordinates on which `c` and `w` agree. -/
def agree (c w : ι → Sigma) : ℕ := (Finset.univ.filter (fun i => c i = w i)).card

/-- Agreement plus Hamming distance equals the block length. -/
theorem agree_add_hammingDist (c w : ι → Sigma) :
    agree c w + hammingDist c w = Fintype.card ι := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset ι)) (p := fun i => c i = w i)
  simpa only [agree, hammingDist, Finset.card_univ, ne_eq] using h

/-- Agreement is at least `n - e` when `c` is within distance `e` of `w` (as naturals). -/
theorem natSub_le_agree {c w : ι → Sigma} {e : ℕ} (h : hammingDist c w ≤ e) :
    Fintype.card ι - e ≤ agree c w := by
  have := agree_add_hammingDist c w; omega

/-- Agreement is at most `n - d` for two words at distance `≥ d` (as naturals). -/
theorem agree_le_natSub {c c' : ι → Sigma} {d : ℕ} (h : d ≤ hammingDist c c') :
    agree c c' ≤ Fintype.card ι - d := by
  have := agree_add_hammingDist c c'; omega

/-! ### Real-valued indicators and the counting identities -/

/-- `0/1` indicator (in `ℚ`) that `c` agrees with `w` at coordinate `i`. -/
noncomputable def ind (c w : ι → Sigma) (i : ι) : ℚ := if c i = w i then 1 else 0

theorem ind_nonneg (c w : ι → Sigma) (i : ι) : 0 ≤ ind c w i := by
  unfold ind; split <;> norm_num

/-- Summing the indicator over coordinates gives the agreement count. -/
theorem sum_ind_eq_agree (c w : ι → Sigma) : ∑ i, ind c w i = (agree c w : ℚ) := by
  classical
  unfold ind agree
  rw [Finset.sum_boole]

/-- Product of two agreement indicators is the "both agree with `w`" indicator. -/
theorem ind_mul_ind (c c' w : ι → Sigma) (i : ι) :
    ind c w i * ind c' w i = if c i = w i ∧ c' i = w i then 1 else 0 := by
  unfold ind; split_ifs with h1 h2 h3 <;> first | rfl | simp_all

/-- The number of codewords in `C` agreeing with `w` at coordinate `i` (in `ℚ`). -/
noncomputable def colCount (C : Finset (ι → Sigma)) (w : ι → Sigma) (i : ι) : ℚ :=
  ∑ c ∈ C, ind c w i

theorem colCount_nonneg (C : Finset (ι → Sigma)) (w : ι → Sigma) (i : ι) :
    0 ≤ colCount C w i :=
  Finset.sum_nonneg (fun c _ => ind_nonneg c w i)

/-- `∑ i, colCount i = ∑ c, agree(c, w)`. -/
theorem sum_colCount (C : Finset (ι → Sigma)) (w : ι → Sigma) :
    ∑ i, colCount C w i = ∑ c ∈ C, (agree c w : ℚ) := by
  unfold colCount
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => sum_ind_eq_agree c w)

/-- The "common agreement" count of `c, c'` against `w`, in `ℚ`. -/
noncomputable def common (c c' w : ι → Sigma) : ℚ := ∑ i, ind c w i * ind c' w i

/-- `common c c w = agree(c, w)`. -/
theorem common_self (c w : ι → Sigma) : common c c w = (agree c w : ℚ) := by
  unfold common
  rw [← sum_ind_eq_agree c w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold ind; split <;> norm_num

/-- `common c c' w ≤ agree(c, c')`: coordinates where both agree with `w` are coordinates where
`c` and `c'` agree with each other. -/
theorem common_le_agree (c c' w : ι → Sigma) : common c c' w ≤ (agree c c' : ℚ) := by
  classical
  unfold common
  have hpt : ∀ i, ind c w i * ind c' w i ≤ ind c c' i := by
    intro i
    rw [ind_mul_ind, ind]
    split_ifs with hP hcc
    · exact le_refl 1
    · exact absurd (hP.1.trans hP.2.symm) hcc
    · norm_num
    · norm_num
  calc ∑ i, ind c w i * ind c' w i ≤ ∑ i, ind c c' i := Finset.sum_le_sum (fun i _ => hpt i)
    _ = (agree c c' : ℚ) := sum_ind_eq_agree c c'

/-- `∑ i, (colCount i)² = ∑ c, ∑ c', common(c, c')`: expansion over ordered pairs. -/
theorem sum_colCount_sq (C : Finset (ι → Sigma)) (w : ι → Sigma) :
    ∑ i, (colCount C w i) ^ 2 = ∑ c ∈ C, ∑ c' ∈ C, common c c' w := by
  unfold colCount common
  have step : ∀ i, (∑ c ∈ C, ind c w i) ^ 2 = ∑ c ∈ C, ∑ c' ∈ C, ind c w i * ind c' w i := by
    intro i; rw [sq, Finset.sum_mul_sum]
  simp_rw [step]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/-- Cauchy–Schwarz specialised: `(∑ i, colCount i)² ≤ n · ∑ i, (colCount i)²`. -/
theorem sq_sum_colCount_le (C : Finset (ι → Sigma)) (w : ι → Sigma) :
    (∑ i, colCount C w i) ^ 2 ≤ (Fintype.card ι : ℚ) * ∑ i, (colCount C w i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
    (f := fun i => colCount C w i)
  simpa [Finset.card_univ] using h

/-- Each agreement count, in `ℚ`, is at most the block length. -/
theorem agree_le_card (c w : ι → Sigma) : (agree c w : ℚ) ≤ (Fintype.card ι : ℚ) := by
  have : agree c w ≤ Fintype.card ι := by
    unfold agree; rw [← Finset.card_univ]; exact Finset.card_filter_le _ _
  exact_mod_cast this

/-- The **Johnson denominator** `(n - e)² - n·(n - d)`. The Johnson regime is where it is positive. -/
noncomputable def johnsonDenom (n d e : ℕ) : ℚ := ((n : ℚ) - e) ^ 2 - (n : ℚ) * ((n : ℚ) - d)

/-! ### The Johnson bound -/

/-- **Johnson bound (product form).** For a finite set of codewords `C` with pairwise Hamming
distance at least `d`, all within distance `e` of a word `w` (with `e, d ≤ n := |ι|`):

  `(C.card) · ((n - e)² - n·(n - d)) ≤ n · d`. -/
theorem card_mul_johnsonDenom_le
    (C : Finset (ι → Sigma)) (w : ι → Sigma) (d e : ℕ)
    (hd : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c')
    (he : ∀ c ∈ C, hammingDist c w ≤ e)
    (hen : e ≤ Fintype.card ι) (hdn : d ≤ Fintype.card ι) :
    (C.card : ℚ) * johnsonDenom (Fintype.card ι) d e ≤ (Fintype.card ι : ℚ) * d := by
  classical
  set n := Fintype.card ι with hn
  set L : ℚ := (C.card : ℚ) with hL
  have hLnn : 0 ≤ L := by positivity
  set S1 : ℚ := ∑ c ∈ C, (agree c w : ℚ) with hS1def
  set S2 : ℚ := ∑ c ∈ C, ∑ c' ∈ C, common c c' w with hS2def
  have hne : (0 : ℚ) ≤ (n : ℚ) - e := by
    have h : (e : ℚ) ≤ (n : ℚ) := by exact_mod_cast hen
    linarith
  have hnd : (0 : ℚ) ≤ (n : ℚ) - d := by
    have h : (d : ℚ) ≤ (n : ℚ) := by exact_mod_cast hdn
    linarith
  -- (1) lower bound on S1
  have hS1lower : L * ((n : ℚ) - e) ≤ S1 := by
    have hcast : ∀ c ∈ C, ((n : ℚ) - e) ≤ (agree c w : ℚ) := by
      intro c hc
      have hge : (n - e : ℕ) ≤ agree c w := natSub_le_agree (he c hc)
      have : ((n - e : ℕ) : ℚ) ≤ (agree c w : ℚ) := by exact_mod_cast hge
      rwa [Nat.cast_sub hen] at this
    calc L * ((n : ℚ) - e) = ∑ _c ∈ C, ((n : ℚ) - e) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ S1 := Finset.sum_le_sum hcast
  -- (2) upper bound on S1
  have hS1upper : S1 ≤ L * (n : ℚ) := by
    calc S1 ≤ ∑ _c ∈ C, (n : ℚ) := Finset.sum_le_sum (fun c _ => agree_le_card c w)
      _ = L * (n : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) upper bound on S2
  have hS2upper : S2 ≤ S1 + L * (L - 1) * ((n : ℚ) - d) := by
    have hrow : ∀ c ∈ C,
        ∑ c' ∈ C, common c c' w ≤ (agree c w : ℚ) + (L - 1) * ((n : ℚ) - d) := by
      intro c hc
      have hsplit : ∑ c' ∈ C, common c c' w
          = common c c w + ∑ c' ∈ C.erase c, common c c' w :=
        (Finset.add_sum_erase C (fun c' => common c c' w) hc).symm
      have hoff : ∑ c' ∈ C.erase c, common c c' w ≤ (L - 1) * ((n : ℚ) - d) := by
        have hbound : ∀ c' ∈ C.erase c, common c c' w ≤ (n : ℚ) - d := by
          intro c' hc'
          have hne' : c' ≠ c := Finset.ne_of_mem_erase hc'
          have hc'mem : c' ∈ C := Finset.mem_of_mem_erase hc'
          have hag : agree c c' ≤ (n - d : ℕ) :=
            agree_le_natSub (hd c hc c' hc'mem (Ne.symm hne'))
          have : (agree c c' : ℚ) ≤ ((n - d : ℕ) : ℚ) := by exact_mod_cast hag
          rw [Nat.cast_sub hdn] at this
          exact (common_le_agree c c' w).trans this
        calc ∑ c' ∈ C.erase c, common c c' w
              ≤ ∑ _c' ∈ C.erase c, ((n : ℚ) - d) := Finset.sum_le_sum hbound
          _ = ((C.erase c).card : ℚ) * ((n : ℚ) - d) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (L - 1) * ((n : ℚ) - d) := by
                rw [Finset.card_erase_of_mem hc,
                  Nat.cast_sub (Finset.one_le_card.mpr ⟨c, hc⟩)]
                push_cast; ring
      rw [hsplit, common_self]
      linarith
    calc S2 ≤ ∑ c ∈ C, ((agree c w : ℚ) + (L - 1) * ((n : ℚ) - d)) := Finset.sum_le_sum hrow
      _ = S1 + L * (L - 1) * ((n : ℚ) - d) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hS1def]; ring
  -- (4) Cauchy–Schwarz
  have hCS : S1 ^ 2 ≤ (n : ℚ) * S2 := by
    have h1 := sq_sum_colCount_le C w
    rw [sum_colCount C w, ← hS1def] at h1
    rw [sum_colCount_sq C w, ← hS2def] at h1
    exact h1
  -- (5) `(L (n-e))² ≤ S1²`
  have hsqle : (L * ((n : ℚ) - e)) ^ 2 ≤ S1 ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hLnn hne) hS1lower 2
  -- KEY inequality
  have hKEY : (L * ((n : ℚ) - e)) ^ 2 ≤ (n : ℚ) * (L * (n : ℚ) + L * (L - 1) * ((n : ℚ) - d)) := by
    have hnpos : (0 : ℚ) ≤ (n : ℚ) := by positivity
    calc (L * ((n : ℚ) - e)) ^ 2 ≤ S1 ^ 2 := hsqle
      _ ≤ (n : ℚ) * S2 := hCS
      _ ≤ (n : ℚ) * (S1 + L * (L - 1) * ((n : ℚ) - d)) := by
            apply mul_le_mul_of_nonneg_left _ hnpos; linarith [hS2upper]
      _ ≤ (n : ℚ) * (L * (n : ℚ) + L * (L - 1) * ((n : ℚ) - d)) := by
            apply mul_le_mul_of_nonneg_left _ hnpos; linarith [hS1upper]
  -- cancel a factor of `L`
  rcases eq_or_lt_of_le hLnn with hL0 | hLpos
  · rw [← hL0, zero_mul]; positivity
  · have hLLX : L * (L * johnsonDenom n d e) ≤ L * ((n : ℚ) * d) := by
      unfold johnsonDenom
      nlinarith [hKEY, hLpos, hne, hnd]
    exact le_of_mul_le_mul_left hLLX hLpos

/-- **Johnson bound (list-size form).** In the Johnson regime `(n - e)² > n·(n - d)`, the number of
codewords of `C` within distance `e` of `w` is at most `n·d / ((n - e)² - n·(n - d))`. -/
theorem card_le_div
    (C : Finset (ι → Sigma)) (w : ι → Sigma) (d e : ℕ)
    (hd : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c')
    (he : ∀ c ∈ C, hammingDist c w ≤ e)
    (hen : e ≤ Fintype.card ι) (hdn : d ≤ Fintype.card ι)
    (hJohnson : 0 < johnsonDenom (Fintype.card ι) d e) :
    (C.card : ℚ) ≤ (Fintype.card ι : ℚ) * d / johnsonDenom (Fintype.card ι) d e := by
  rw [le_div_iff₀ hJohnson]
  exact card_mul_johnsonDenom_le C w d e hd he hen hdn

/-- **List-decoding ball-size bound** (the form consumed downstream). In a code `C` with minimum
pairwise Hamming distance `d`, the number of codewords within Hamming distance `e` of *any* word `w`
is, in the Johnson regime `(n - e)² > n·(n - d)`, at most `n·d / ((n - e)² - n·(n - d))`.

This is `card_le_div` applied to the ball `{c ∈ C | Δ₀(c, w) ≤ e}`: a sub-code inherits the minimum
distance, and every element is within `e` of `w` by construction. Specialising `d` to a code's
minimum distance (e.g. `n - k + 1` for `ReedSolomon.code` via `ReedSolomon.minDist_eq'`) yields the
Reed–Solomon list-size at the Johnson radius — the input to the correlated-agreement "true form". -/
theorem card_ball_le
    (C : Finset (ι → Sigma)) (w : ι → Sigma) (d e : ℕ)
    (hd : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → d ≤ hammingDist c c')
    (hen : e ≤ Fintype.card ι) (hdn : d ≤ Fintype.card ι)
    (hJohnson : 0 < johnsonDenom (Fintype.card ι) d e) :
    ((C.filter (fun c => hammingDist c w ≤ e)).card : ℚ)
      ≤ (Fintype.card ι : ℚ) * d / johnsonDenom (Fintype.card ι) d e := by
  classical
  refine card_le_div (C.filter (fun c => hammingDist c w ≤ e)) w d e ?_ ?_ hen hdn hJohnson
  · intro c hc c' hc' hcc
    exact hd c (Finset.mem_filter.mp hc).1 c' (Finset.mem_filter.mp hc').1 hcc
  · intro c hc; exact (Finset.mem_filter.mp hc).2

end ArkLib.JohnsonBound

/- Axiom audit. -/
#print axioms ArkLib.JohnsonBound.card_mul_johnsonDenom_le
#print axioms ArkLib.JohnsonBound.card_le_div
#print axioms ArkLib.JohnsonBound.card_ball_le
