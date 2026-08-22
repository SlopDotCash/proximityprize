/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Core
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic

/-!
# The Johnson numeric bound dominates the unique-decoding error

`johnsonBoundReal` (the [Hab25] Theorem 2 numeric form) is at least `n/q`: the
unique-decoding MCA error `|ι|/|F|` (`epsMCA_rs_udr_le_full`) never exceeds the
Johnson-range budget.  This is the arithmetic half of the first *unconditional*
instance of `JohnsonNumericBound` — below the unique-decoding radius the numeric
edge holds outright, since the in-tree UD bound is stronger than the Johnson budget.

The slack is large: with `m ≥ 3` the leading coefficient is
`2·(m+1/2)⁵/(3·ρ₊^{3/2}) ≥ 2·3.5⁵/12 > 87`, so the budget exceeds `n/q` by two
orders of magnitude; the proof only needs `1 ≤` that coefficient.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
-/

namespace CodingTheory

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]

/-- The standalone real-arithmetic core: the [Hab25] numeric formula dominates `n/q`
whenever `1 ≤ n`, `0 < ρ ≤ 2`, `3 ≤ m`, and the remaining quantities are nonnegative. -/
theorem hab25_formula_ge_n_div_q
    {n q ρ m d : ℝ} (hn : 1 ≤ n) (hq : 0 < q)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hm : 3 ≤ m) (hd : 0 ≤ d) :
    n / q ≤ ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
        / (3 * ρ ^ ((3 : ℝ) / 2)) * n
      + (m + 1/2) / ρ ^ ((1 : ℝ) / 2)) / q := by
  have hm0 : (0 : ℝ) ≤ m + 1/2 := by linarith
  have hrpow32 : (0 : ℝ) < ρ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hρ0 _
  have hrpow12 : (0 : ℝ) < ρ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hρ0 _
  -- the second summand is nonnegative
  have hsecond : (0 : ℝ) ≤ (m + 1/2) / ρ ^ ((1 : ℝ) / 2) :=
    div_nonneg hm0 hrpow12.le
  -- the leading coefficient is at least 1: `3·ρ^{3/2} ≤ 12 ≤ 2·(m+1/2)^5`
  have hρ32_le : ρ ^ ((3 : ℝ) / 2) ≤ 4 := by
    calc ρ ^ ((3 : ℝ) / 2) ≤ 2 ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow hρ0.le hρ2 (by norm_num)
      _ ≤ 2 ^ ((2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by
          rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hpow5 : (3.5 : ℝ) ^ 5 ≤ (m + 1/2) ^ 5 := by
    have h35 : (3.5 : ℝ) ≤ m + 1/2 := by linarith
    exact pow_le_pow_left₀ (by norm_num) h35 5
  have hcoeff : (1 : ℝ) ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
      / (3 * ρ ^ ((3 : ℝ) / 2)) := by
    rw [le_div_iff₀ (by positivity)]
    have hcross : (0 : ℝ) ≤ 3 * (m + 1/2) * d * ρ := by positivity
    nlinarith [hpow5, hρ32_le]
  -- conclude: `n ≤ coeff·n + second`
  have hnum : n ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
      / (3 * ρ ^ ((3 : ℝ) / 2)) * n + (m + 1/2) / ρ ^ ((1 : ℝ) / 2) := by
    have h1 : n = 1 * n := (one_mul n).symm
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (by linarith : (0:ℝ) ≤ n)]
  gcongr

/-- **The Johnson budget dominates the unique-decoding error.**  `johnsonBoundReal` is at
least `|ι|/|F|`, the unconditional below-UD MCA error (`epsMCA_rs_udr_le_full`).  This is
the arithmetic half of the unconditional UD-window instance of `JohnsonNumericBound`. -/
theorem card_div_card_le_johnsonBoundReal
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (hk : k ≤ Fintype.card ι) :
    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
      ≤ CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ := by
  have hn : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hρ0 : (0 : ℝ) < (k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ) := by
    have : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / (Fintype.card ι : ℝ) := by positivity
    linarith
  have hρ2 : (k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ) ≤ 2 := by
    have h1 : (k : ℝ) / (Fintype.card ι : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact_mod_cast hk
    have h2 : 1 / (Fintype.card ι : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hn
    linarith
  have hm : (3 : ℝ) ≤
      max (⌈(((k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ))
        ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 := le_max_right _ _
  have hd : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  exact hab25_formula_ge_n_div_q hn hq hρ0 hρ2 hm hd

end CodingTheory

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open _root_.ProximityGap _root_.ProximityGap.UDRwire _root_.Code
open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The first unconditional instance of the numeric edge.**  Below the unique-decoding
radius (in the regime of `epsMCA_rs_udr_le_full`), `JohnsonNumericBound` holds outright:
the unconditional UD error `|ι|/|F|` never exceeds the Johnson budget
(`card_div_card_le_johnsonBoundReal`).  No production hypothesis. -/
theorem johnsonNumericBound_of_udr_window
    (domain : ι₀ ↪ F₀) (k : ℕ) [NeZero k] (η δ : ℝ≥0)
    (hk : k ≤ Fintype.card ι₀)
    (hδ : δ ≤ relativeUniqueDecodingRadius
      ((ReedSolomon.code domain k : Submodule F₀ (ι₀ → F₀)) : Set (ι₀ → F₀)))
    (hreg : 2 * (Fintype.card ι₀ - ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊)
      < Fintype.card ι₀ - k + 1) :
    JohnsonNumericBound domain k η δ := by
  unfold JohnsonNumericBound
  refine le_trans (epsMCA_rs_udr_le_full domain k hk δ hδ hreg) ?_
  have h1 : (Fintype.card ι₀ : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      = ENNReal.ofReal ((Fintype.card ι₀ : ℝ) / (Fintype.card F₀ : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [h1]
  exact ENNReal.ofReal_le_ofReal
    (CodingTheory.card_div_card_le_johnsonBoundReal domain k η δ hk)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.hab25_formula_ge_n_div_q
#print axioms CodingTheory.card_div_card_le_johnsonBoundReal
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_udr_window

namespace CodingTheory

open scoped NNReal

/-- The pure-real core of the tight `harith` closure: with `y = x·s ≤ 3(M+1/2)`,
`s ≤ 1`, `12 ≤ M`, the canonical budget `(x+1)·(c·x+1)` fits inside
`(2/3)·(M+1/2)⁵/s³` (all per-`n`). -/
theorem harith_core_real {x s c M : ℝ}
    (hx0 : 0 ≤ x) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hM : 12 ≤ M) (hc : c ≤ M * (M + 1) / 2)
    (hc0 : 0 ≤ c) (hy : x * s ≤ 3 * (M + 1/2)) :
    (x + 1) * (c * x + 1) ≤ (2/3) * (M + 1/2) ^ 5 / s ^ 3 := by
  have hM0 : (0 : ℝ) < M + 1/2 := by linarith
  have hkey : ((x + 1) * (c * x + 1)) * s ^ 3 ≤ (2/3) * (M + 1/2) ^ 5 := by
    have h1 : (x + 1) * s ≤ 3 * (M + 1/2) + 1 := by nlinarith
    have h2 : (c * x + 1) * s ≤ (3/2) * (M + 1/2) ^ 3 + 1 := by nlinarith
    have hs3 : s ^ 3 ≤ s * s := by nlinarith
    have hxs : 0 ≤ (x + 1) * s := by positivity
    have hcs : 0 ≤ (c * x + 1) * s := by positivity
    calc ((x + 1) * (c * x + 1)) * s ^ 3
        ≤ ((x + 1) * s) * ((c * x + 1) * s) * s := by nlinarith [sq_nonneg s, mul_nonneg hx0 hc0]
      _ ≤ (3 * (M + 1/2) + 1) * ((3/2) * (M + 1/2) ^ 3 + 1) * 1 := by
          have hAB : ((x + 1) * s) * ((c * x + 1) * s)
              ≤ (3 * (M + 1/2) + 1) * ((3/2) * (M + 1/2) ^ 3 + 1) :=
            mul_le_mul h1 h2 hcs (by linarith)
          have hABnn : 0 ≤ ((x + 1) * s) * ((c * x + 1) * s) := mul_nonneg hxs hcs
          nlinarith [mul_le_mul_of_nonneg_left hs1 hABnn]
      _ ≤ (2/3) * (M + 1/2) ^ 5 := by nlinarith [pow_pos hM0 3, pow_pos hM0 5, sq_nonneg (M + 1/2)]
  have hs3p : (0 : ℝ) < s ^ 3 := by positivity
  rw [le_div_iff₀ hs3p]
  exact hkey

end CodingTheory

namespace ProximityGapArithWrapper

open CodingTheory GuruswamiSudan
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]

set_option maxHeartbeats 1600000 in
/-- **The tight `harith`, closed.**  At the canonical tight budget
`B = (D/(k-1)+1)·max(n·|c|·(D/(k-1)), n)` with `2 ≤ k`, `k+1 ≤ n`, `12 ≤ m`, and `m`
below the Johnson multiplicity `M_J = max(⌈√ρ₊/(2η)⌉, 3)`, the arithmetic side condition
of `johnsonNumericBound_of_window_numeric_tight` holds:
`B/|F| ≤ johnsonBoundReal`. -/
theorem harith_tight_closed (domain : ι ↪ F) (k m : ℕ) (η δ : ℝ≥0)
    (hk2 : 2 ≤ k) (hkn : k + 1 ≤ Fintype.card ι) (hm12 : 12 ≤ m)
    (hmle : (m : ℝ) ≤
      max (⌈((((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι)) ^ ((1 : ℝ) / 2))
        / (2 * (η : ℝ))⌉ : ℝ) 3) :
    (((gs_degree_bound k (Fintype.card ι) m / (k - 1) + 1)
        * max (Fintype.card ι * (constraintIndices m).card
            * (gs_degree_bound k (Fintype.card ι) m / (k - 1))) (Fintype.card ι) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ ENNReal.ofReal
          (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- abbreviations
  set ρp : ℝ := (k : ℝ) / n + 1 / n with hρp
  have hρp0 : (0 : ℝ) < ρp := by
    have h1 : (0 : ℝ) < 1 / n := by positivity
    have h2 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    linarith
  have hρp1 : ρp ≤ 1 := by
    rw [hρp, show (k : ℝ) / n + 1 / n = ((k : ℝ) + 1) / n by ring, div_le_one hn0]
    exact_mod_cast hkn
  set s : ℝ := ρp ^ ((1 : ℝ) / 2) with hs
  have hs0 : (0 : ℝ) < s := Real.rpow_pos_of_pos hρp0 _
  have hs1 : s ≤ 1 := by
    rw [hs]
    calc ρp ^ ((1:ℝ)/2) ≤ 1 ^ ((1:ℝ)/2) := Real.rpow_le_rpow hρp0.le hρp1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hssq : s * s = ρp := by
    rw [hs, ← Real.rpow_add hρp0]
    norm_num
  have hs3 : s ^ 3 = ρp ^ ((3 : ℝ) / 2) := by
    rw [hs, ← Real.rpow_natCast (ρp ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hρp0.le]
    norm_num
  -- the ℕ quantities, cast
  set D : ℕ := gs_degree_bound k n m with hD
  set Dk : ℕ := D / (k - 1) with hDk
  set c : ℕ := (constraintIndices m).card with hc
  set T : ℕ := max (n * c * Dk) n with hT
  set B : ℕ := (Dk + 1) * T with hB
  -- step 1: x·s ≤ 3(m+1/2)
  have hDle : (D : ℝ) ≤ ((m : ℝ) + 1/2) * Real.sqrt ((k : ℝ) / n) * n := by
    rw [hD]
    unfold gs_degree_bound
    have harg : (0 : ℝ) ≤ (((m : ℚ) + 1/2) : ℝ) * Real.sqrt (((k : ℚ) / (n : ℚ) : ℚ) : ℝ)
        * ((n : ℚ) : ℝ) := by positivity
    refine le_trans (Nat.floor_le (by push_cast; positivity)) ?_
    push_cast
    ring_nf
    gcongr <;> norm_num
  -- step 2: `Dk·s ≤ 3(m+1/2)`
  have hk1R : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have h1 : 1 ≤ k := by omega
    push_cast [h1]
    ring
  have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hDkle : (Dk : ℝ) ≤ (D : ℝ) / ((k : ℝ) - 1) := by
    rw [hDk, ← hk1R]
    exact_mod_cast Nat.cast_div_le
  have hseq : s = Real.sqrt ρp := (Real.sqrt_eq_rpow ρp).symm
  have hρpalt : ρp = ((k : ℝ) + 1) / n := by rw [hρp]; ring
  have hsqrts : Real.sqrt ((k : ℝ) / n) * s ≤ ((k : ℝ) + 1) / n := by
    rw [hseq, ← Real.sqrt_mul (by positivity)]
    have harg : (k : ℝ) / n * ρp ≤ (((k : ℝ) + 1) / n) ^ 2 := by
      rw [hρpalt, sq]
      have h1 : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by gcongr; linarith
      have h2 : (0 : ℝ) ≤ ((k : ℝ) + 1) / n := by positivity
      exact mul_le_mul_of_nonneg_right h1 h2
    calc Real.sqrt ((k : ℝ) / n * ρp) ≤ Real.sqrt ((((k : ℝ) + 1) / n) ^ 2) :=
          Real.sqrt_le_sqrt harg
      _ = ((k : ℝ) + 1) / n := Real.sqrt_sq (by positivity)
  have hxs : (Dk : ℝ) * s ≤ 3 * ((m : ℝ) + 1/2) := by
    have hs0' : (0 : ℝ) ≤ s := hs0.le
    have h1 : (Dk : ℝ) * s ≤ (D : ℝ) / ((k : ℝ) - 1) * s :=
      mul_le_mul_of_nonneg_right hDkle hs0'
    have h2 : (D : ℝ) / ((k : ℝ) - 1) * s
        ≤ (((m : ℝ) + 1/2) * Real.sqrt ((k : ℝ) / n) * n) / ((k : ℝ) - 1) * s := by
      gcongr
    have h3 : (((m : ℝ) + 1/2) * Real.sqrt ((k : ℝ) / n) * n) / ((k : ℝ) - 1) * s
        = ((m : ℝ) + 1/2) * (Real.sqrt ((k : ℝ) / n) * s) * n / ((k : ℝ) - 1) := by
      ring
    have h4 : ((m : ℝ) + 1/2) * (Real.sqrt ((k : ℝ) / n) * s) * n / ((k : ℝ) - 1)
        ≤ ((m : ℝ) + 1/2) * (((k : ℝ) + 1) / n) * n / ((k : ℝ) - 1) := by
      gcongr
    have h5 : ((m : ℝ) + 1/2) * (((k : ℝ) + 1) / n) * n / ((k : ℝ) - 1)
        = ((m : ℝ) + 1/2) * (((k : ℝ) + 1) / ((k : ℝ) - 1)) := by
      field_simp
    have h6 : ((k : ℝ) + 1) / ((k : ℝ) - 1) ≤ 3 := by
      rw [div_le_iff₀ hk1pos]
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1/2 := by positivity
    calc (Dk : ℝ) * s ≤ ((m : ℝ) + 1/2) * (((k : ℝ) + 1) / ((k : ℝ) - 1)) := by
          rw [← h5]
          exact le_trans h1 (le_trans h2 (le_of_eq h3 |>.trans h4))
      _ ≤ ((m : ℝ) + 1/2) * 3 := mul_le_mul_of_nonneg_left h6 hm0
      _ = 3 * ((m : ℝ) + 1/2) := by ring
  -- step 3: the constraint count
  have hcle : (c : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    rw [hc, card_constraintIndices]
    calc ((m * (m + 1) / 2 : ℕ) : ℝ) ≤ ((m * (m + 1) : ℕ) : ℝ) / ((2 : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ = (m : ℝ) * ((m : ℝ) + 1) / 2 := by push_cast; ring
  -- step 4: the core
  have hcore := harith_core_real (x := (Dk : ℝ)) (s := s) (c := (c : ℝ)) (M := (m : ℝ))
    (by positivity) hs0 hs1 (by exact_mod_cast hm12) hcle (by positivity) hxs
  -- step 5: `B ≤ n·(x+1)(cx+1)`
  have hBle : (B : ℝ) ≤ (n : ℝ) * (((Dk : ℝ) + 1) * ((c : ℝ) * (Dk : ℝ) + 1)) := by
    have hTle : (T : ℝ) ≤ (n : ℝ) * ((c : ℝ) * (Dk : ℝ) + 1) := by
      rw [hT]
      push_cast [Nat.cast_max]
      rw [max_le_iff]
      constructor
      · nlinarith [hn0]
      · nlinarith [mul_nonneg (mul_nonneg hn0.le (Nat.cast_nonneg c)) (Nat.cast_nonneg Dk)]
    rw [hB]
    push_cast
    have hd0 : (0 : ℝ) ≤ (Dk : ℝ) + 1 := by positivity
    calc ((Dk : ℝ) + 1) * (T : ℝ) ≤ ((Dk : ℝ) + 1) * ((n : ℝ) * ((c : ℝ) * (Dk : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hTle hd0
      _ = (n : ℝ) * (((Dk : ℝ) + 1) * ((c : ℝ) * (Dk : ℝ) + 1)) := by ring
  -- step 6: chain into the Johnson formula
  set MJ : ℝ := max (⌈(ρp ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 with hMJ
  have hmMJ : (m : ℝ) ≤ MJ := by rw [hMJ]; exact hmle
  have hMJpow : ((m : ℝ) + 1/2) ^ 5 ≤ (MJ + 1/2) ^ 5 := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) + 1/2 := by positivity
    exact pow_le_pow_left₀ h1 (by linarith) 5
  have hfinalR : (B : ℝ) ≤ (2 * (MJ + 1/2) ^ 5 + 3 * (MJ + 1/2) * (δ : ℝ) * ρp)
      / (3 * ρp ^ ((3 : ℝ) / 2)) * n + (MJ + 1/2) / ρp ^ ((1 : ℝ) / 2) := by
    have hsecond : (0 : ℝ) ≤ (MJ + 1/2) / ρp ^ ((1 : ℝ) / 2) := by
      have hMJ3 : (3 : ℝ) ≤ MJ := le_max_right _ _
      have : (0 : ℝ) ≤ MJ + 1/2 := by linarith
      positivity
    have hδ0 : (0 : ℝ) ≤ 3 * (MJ + 1/2) * (δ : ℝ) * ρp := by
      have hMJ3 : (3 : ℝ) ≤ MJ := le_max_right _ _
      have h1 : (0 : ℝ) ≤ MJ + 1/2 := by linarith
      have h2 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
      positivity
    have h1 : (B : ℝ) ≤ (n : ℝ) * ((2/3) * ((m : ℝ) + 1/2) ^ 5 / s ^ 3) := by
      refine le_trans hBle ?_
      exact mul_le_mul_of_nonneg_left hcore hn0.le
    have h2 : (n : ℝ) * ((2/3) * ((m : ℝ) + 1/2) ^ 5 / s ^ 3)
        ≤ 2 * (MJ + 1/2) ^ 5 / (3 * ρp ^ ((3 : ℝ) / 2)) * n := by
      rw [← hs3]
      have hs3p : (0 : ℝ) < s ^ 3 := by positivity
      have hle : (2/3) * ((m : ℝ) + 1/2) ^ 5 / s ^ 3
          ≤ 2 * (MJ + 1/2) ^ 5 / (3 * s ^ 3) := by
        rw [div_le_div_iff₀ hs3p (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hMJpow hs3p.le]
      calc (n : ℝ) * ((2/3) * ((m : ℝ) + 1/2) ^ 5 / s ^ 3)
          = ((2/3) * ((m : ℝ) + 1/2) ^ 5 / s ^ 3) * n := by ring
        _ ≤ (2 * (MJ + 1/2) ^ 5 / (3 * s ^ 3)) * n :=
            mul_le_mul_of_nonneg_right hle hn0.le
    have h3 : 2 * (MJ + 1/2) ^ 5 / (3 * ρp ^ ((3 : ℝ) / 2)) * n
        ≤ (2 * (MJ + 1/2) ^ 5 + 3 * (MJ + 1/2) * (δ : ℝ) * ρp)
          / (3 * ρp ^ ((3 : ℝ) / 2)) * n := by
      gcongr
      linarith
    linarith
  -- step 7: the ENNReal wrapper
  have hwrap : ((B : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      = ENNReal.ofReal ((B : ℝ) / (Fintype.card F : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hq0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hwrap]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdivle : (B : ℝ) / (Fintype.card F : ℝ)
      ≤ ((2 * (MJ + 1/2) ^ 5 + 3 * (MJ + 1/2) * (δ : ℝ) * ρp)
          / (3 * ρp ^ ((3 : ℝ) / 2)) * n + (MJ + 1/2) / ρp ^ ((1 : ℝ) / 2))
        / (Fintype.card F : ℝ) := by
    gcongr
  exact hdivle

end ProximityGapArithWrapper
#print axioms ProximityGapArithWrapper.harith_tight_closed
#print axioms CodingTheory.harith_core_real
