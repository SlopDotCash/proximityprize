/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterCoreWeightedJets

/-! # Mixed-jet rank room at the two second-prime Johnson pivots

`SecondPrimeJohnsonPivot` reduces the side of Johnson for the second-prime MCA supremum at
half and quarter rate to the single closed tests at `314,491,699` and `536,870,913` errors.
`JohnsonJetRoom` proves that no ordinary mixed Hasse interpolant has a positive dimension
surplus at any agreement count `t` with `t² ≤ n d`. Both pivots lie one step beyond that
range: at the half pivot `t² - n d = 1,082,833,961`, and at the quarter pivot `t² - n d = 1`.

This module quantifies the remaining room. For agreement `t ≥ d`, `2t ≤ n + d` and
`t² ≤ n d + δ`, the doubled prefix difference of every scalar column obeys the exact identity

`4 r B d (2 l r t - d l (l-1) - n B) =
  -(r (r+1)² (4 r² (n d - t²) + 4 r d t - 4 r d² - d²)
    + r ((2 r ((r+1) t - l d) - (r+1) d)² + 4 r (l-r-1)² d²))`,

with `B = r (r+1)`. Hence an interpolant of multiplicity `r` can have a positive surplus only if
`4 r² δ + d² + 4 r d² > 4 r d t`, and only with value degree `v > r`.

* `half_pivot_no_room`: at `314,491,699` half-rate errors every shape with
  `r ≤ 110,255,990` or `v ≤ r` has no surplus.
* `quarter_pivot_no_room`: at `536,870,913` quarter-rate errors every shape with
  `r ≤ 72,057,593,769,492,479` or `v ≤ r` has no surplus.

Consequences for the two-surface factor method (`quarter_surface_scalar_overflow`,
`half_surfaces_resultant_overflow`): at the quarter pivot the scalar-only factor allowance of a
single constructible interpolant already exceeds the budget `2^31`; at the half pivot the
single-resultant allowance `s₁ v₂` of any two constructible interpolants exceeds `2^31`. The
interpolation-plus-resultant safety route therefore cannot decide either Johnson pivot.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonMCAP2PivotRank

open Finset QuarterCoreWeightedJets

/-! ## The exact prefix identity -/

private theorem linear_sum (k a h : ℕ) (hpos : ∀ j < k, j*h ≤ a) :
    2 * (∑ j ∈ range k, (a-j*h) : ℕ) =
      (k : ℤ)*(2*(a : ℤ)-(h : ℤ)*((k : ℤ)-1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have prev := ih (fun j hj => hpos j (by omega))
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sub (hpos k (by omega)), Nat.cast_mul,
      Nat.cast_succ]
    linarith

/-- The full-prefix comparison beyond the multiplicity, with an agreement count
`t² ≤ n d + δ`. Either the prefix has length exactly `r + 1` and `δ ≤ (t - d)²`, or the
quadratic room condition `4 r² δ + d² + 4 r d² ≤ 4 r d t` holds. -/
private theorem core {n d t δ : ℤ} (r l : ℤ) (hr : 0 < r) (hd : 0 < d) (hl : r+1 ≤ l)
    (hj : t*t ≤ n*d + δ)
    (hcase : (l = r+1 ∧ δ + 2*t*d ≤ t*t + d*d) ∨ 4*r*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t) :
    2*l*r*t - d*l*(l-1) ≤ n*r*(r+1) := by
  by_contra! bad
  have hB : 0 < r*(r+1)*d := mul_pos (mul_pos hr (by linarith)) hd
  have pos : 0 < r*(r+1)*d*(2*l*r*t - d*l*(l-1) - n*r*(r+1)) :=
    mul_pos hB (sub_pos.mpr bad)
  rcases hcase with ⟨rfl, hgap⟩ | hcond
  · have key : 0 ≤ (r*(r+1))^2 * (n*d - t*t + (t*t - 2*t*d + d*d)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have id : r*(r+1)*d*(2*(r+1)*r*t - d*(r+1)*(r+1-1) - n*r*(r+1)) =
        -((r*(r+1))^2 * (n*d - t*t + (t*t - 2*t*d + d*d))) := by ring
    linarith
  · have h4 : (0:ℤ) ≤ 4*r*r := mul_nonneg (mul_nonneg (by norm_num) hr.le) hr.le
    have hm := mul_le_mul_of_nonneg_left (show t*t - n*d ≤ δ by linarith) h4
    have h1 : 0 ≤ r*(r+1)^2*(4*r*r*(n*d - t*t) + 4*r*d*t - 4*r*d*d - d*d) :=
      mul_nonneg (mul_nonneg hr.le (sq_nonneg _)) (by linarith)
    have h2 : 0 ≤ r*((2*r*((r+1)*t - l*d) - (r+1)*d)^2 + 4*r*(l-r-1)^2*d^2) :=
      mul_nonneg hr.le (add_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr.le) (sq_nonneg _))
          (sq_nonneg _)))
    have id : 4*r*(r*(r+1)*d*(2*l*r*t - d*l*(l-1) - n*r*(r+1))) =
        -(r*(r+1)^2*(4*r*r*(n*d - t*t) + 4*r*d*t - 4*r*d*d - d*d) +
          r*((2*r*((r+1)*t - l*d) - (r+1)*d)^2 + 4*r*(l-r-1)^2*d^2)) := by ring
    have pos4 : 0 < 4*r*(r*(r+1)*d*(2*l*r*t - d*l*(l-1) - n*r*(r+1))) :=
      mul_pos (by linarith) pos
    linarith

/-- Prefix comparison of one scalar column for the room conditions above. -/
private theorem prefix_bound {n d t δ : ℕ} (hd : 0 < d) (hnd : d ≤ n) (ht : d ≤ t)
    (hmean : 2*t ≤ n+d) (hj : t*t ≤ n*d + δ) (r k : ℕ) (hr : 0 < r)
    (hcase : (k ≤ r+1 ∧ δ + 2*t*d ≤ t*t + d*d) ∨ 4*r*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t) :
    (∑ j ∈ range k, (r*t-j*d)) ≤ n * ∑ j ∈ range k, (r-j) := by
  have mean : 2*(t : ℤ) ≤ (n : ℤ) + (d : ℤ) := by exact_mod_cast hmean
  by_cases hk : k ≤ r
  · have hrow := linear_sum k r 1 (fun j hj => by simpa using (by omega : j ≤ r))
    have hcol := linear_sum k (r*t) d (fun j hj =>
      Nat.mul_le_mul (by omega : j ≤ r) ht)
    simp only [mul_one, Nat.cast_one, one_mul] at hrow
    have suffices_int : (k : ℤ)*(2*(r : ℤ)*t-d*((k : ℤ)-1)) ≤
        (k : ℤ)*(n*(2*(r : ℤ)-((k : ℤ)-1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have kr : (k : ℤ) ≤ r := by exact_mod_cast hk
      have nonneg := mul_nonneg (show 0 ≤ (r : ℤ) by positivity) (sub_nonneg.mpr mean)
      have gap : 0 ≤ (n : ℤ)-d := by exact sub_nonneg.mpr (by exact_mod_cast hnd)
      have rest := mul_nonneg (sub_nonneg.mpr kr) gap
      linarith only [nonneg, rest, gap]
    push_cast at hrow hcol
    zify
    linarith only [congrArg (fun x : ℤ => (n : ℤ)*x) hrow, hcol, suffices_int]
  · obtain ⟨l, hl_eq⟩ : ∃ l, l = min k (r*t/d+1) := ⟨_, rfl⟩
    have hlk : l ≤ k := hl_eq ▸ min_le_left _ _
    have hld : l ≤ r*t/d+1 := hl_eq ▸ min_le_right _ _
    have hlc : l = k ∨ l = r*t/d+1 := by
      rcases le_total k (r*t/d+1) with h | h
      · left
        rw [hl_eq, min_eq_left h]
      · right
        rw [hl_eq, min_eq_right h]
    have hl (j : ℕ) (hj : j < l) : j*d ≤ r*t :=
      (Nat.le_div_iff_mul_le hd).1 (by omega)
    have hc : (∑ j ∈ range l, (r*t-j*d)) = ∑ j ∈ range k, (r*t-j*d) := by
      apply sum_subset (range_mono hlk)
      intro j hj hm
      simp only [mem_range] at hj hm
      have hdiv : r*t/d < j := by omega
      exact Nat.sub_eq_zero_of_le ((Nat.div_lt_iff_lt_mul hd).1 hdiv).le
    have hs : (∑ j ∈ range r, (r-j)) = ∑ j ∈ range k, (r-j) := by
      apply sum_subset (range_mono (by omega))
      intro j _ hm
      simp only [mem_range] at hm
      omega
    have hcol := linear_sum l (r*t) d hl
    have hrow := linear_sum r r 1 (fun j hj => by simpa using hj.le)
    have hrd : r ≤ r*t/d := (Nat.le_div_iff_mul_le hd).2 (Nat.mul_le_mul_left r ht)
    have hlr : r+1 ≤ l := by omega
    have hcase' : ((l : ℤ) = r+1 ∧ (δ : ℤ) + 2*t*d ≤ t*t + d*d) ∨
        4*(r : ℤ)*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t := by
      rcases hcase with ⟨hk1, hgap⟩ | hcond
      · left
        exact ⟨by exact_mod_cast (show l = r+1 by omega), by exact_mod_cast hgap⟩
      · right
        exact_mod_cast hcond
    have hglobal := core (n := (n : ℤ)) (d := (d : ℤ)) (t := (t : ℤ)) (δ := (δ : ℤ))
      (r : ℤ) l (by exact_mod_cast hr) (by exact_mod_cast hd)
      (by exact_mod_cast hlr) (by exact_mod_cast hj) hcase'
    simp only [one_mul, mul_one, Nat.cast_one] at hrow
    push_cast at hrow hcol
    rw [← hc, ← hs]
    zify
    linarith only [congrArg (fun x : ℤ => (n : ℤ)*x) hrow, hcol, hglobal]

private theorem layer (g : ℕ → ℕ) (s M : ℕ) :
    (∑ j ∈ range M, (s+1-j)*g j) = (∑ j ∈ range M, (s-j)*g j) +
      ∑ j ∈ range (min M (s+1)), g j := by
  have hsplit (j : ℕ) : (s+1-j)*g j =
      (s-j)*g j + (if j<s+1 then g j else 0) := by
    split_ifs with hj
    · rw [show s+1-j = (s-j)+1 by omega, add_mul, one_mul]
    · simp [Nat.sub_eq_zero_of_le (by omega : s+1 ≤ j),
        Nat.sub_eq_zero_of_le (by omega : s ≤ j)]
  simp_rw [hsplit]
  rw [sum_add_distrib, ← sum_filter]
  have hf : (range M).filter (fun j => j < s+1) = range (min M (s+1)) := by
    ext j
    simp [lt_min_iff]
  rw [hf]

/-! ## The uniform room theorem -/

/-- Beyond the Johnson crossing by `δ`, an ordinary mixed Hasse shape of multiplicity `r`,
value cutoff `v` and total cutoff `s` has no dimension surplus whenever `v ≤ r` (given
`δ ≤ (t-d)²`) or the quadratic room condition fails at `r`. -/
theorem pivot_no_room {n d t δ : ℕ} (hd : 0 < d) (hnd : d ≤ n) (ht : d ≤ t)
    (hmean : 2*t ≤ n+d) (hj : t*t ≤ n*d + δ) (s v r : ℕ)
    (hcase : 0 < r →
      (v ≤ r ∧ δ + 2*t*d ≤ t*t + d*d) ∨ 4*r*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t) :
    columnCount s v d (r*t) ≤ n * rowCount s r := by
  have weighted (k : ℕ) :
      (∑ j ∈ range (v+1), (k-j)*(r*t-j*d)) ≤ n * ∑ j ∈ range r, (k-j)*(r-j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [layer, layer, mul_add]
      apply Nat.add_le_add ih
      by_cases hzero : r = 0
      · simp [hzero]
      have same : (∑ j ∈ range (min r (k+1)), (r-j)) = ∑ j ∈ range (k+1), (r-j) := by
        apply sum_subset (range_mono (min_le_right _ _))
        intro j hj hm
        simp only [mem_range] at hj hm
        omega
      rw [same]
      have hk' : min (v+1) (k+1) ≤ k+1 := min_le_right _ _
      have hv' : min (v+1) (k+1) ≤ v+1 := min_le_left _ _
      have pre := prefix_bound hd hnd ht hmean hj r (min (v+1) (k+1)) (by omega) (by
        rcases hcase (by omega) with ⟨hv, hgap⟩ | hcond
        · exact Or.inl ⟨by omega, hgap⟩
        · exact Or.inr hcond)
      have rows : (∑ j ∈ range (min (v+1) (k+1)), (r-j)) ≤ ∑ j ∈ range (k+1), (r-j) :=
        sum_le_sum_of_subset_of_nonneg (range_mono hk') (fun j _ _ => Nat.zero_le _)
      exact pre.trans (Nat.mul_le_mul_left n rows)
  simpa [columnCount, rowCount, Nat.mul_comm] using weighted (s+1)

/-- Convexity of the room condition in the multiplicity: it holds throughout `[1, R]`
once it holds at both endpoints. -/
private theorem interval_cond_int (d t δ R r : ℤ) (hδ : 0 ≤ δ) (h1 : 1 ≤ r) (hR : r ≤ R)
    (e1 : 4*1*1*δ + d*d + 4*1*d*d ≤ 4*1*d*t)
    (eR : 4*R*R*δ + d*d + 4*R*d*d ≤ 4*R*d*t) :
    4*r*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t := by
  rcases eq_or_lt_of_le (h1.trans hR) with hR1 | hR1
  · have hr : r = 1 := by linarith
    subst hr
    exact e1
  · have key : (R-1)*(4*r*r*δ + d*d + 4*r*d*d - 4*r*d*t) =
        (R-r)*(4*1*1*δ + d*d + 4*1*d*d - 4*1*d*t) +
        (r-1)*(4*R*R*δ + d*d + 4*R*d*d - 4*R*d*t) +
        (4*δ*(R-1)*(r-1))*(r-R) := by ring
    have a1 : (R-r)*(4*1*1*δ + d*d + 4*1*d*d - 4*1*d*t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have a2 : (r-1)*(4*R*R*δ + d*d + 4*R*d*d - 4*R*d*t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have a3 : (4*δ*(R-1)*(r-1))*(r-R) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
    by_contra! hc
    have hpos := mul_pos (show (0:ℤ) < R-1 by linarith)
      (show (0:ℤ) < 4*r*r*δ + d*d + 4*r*d*d - 4*r*d*t by linarith)
    linarith

private theorem interval_cond {d t δ R : ℕ} (r : ℕ) (h1 : 1 ≤ r) (hR : r ≤ R)
    (e1 : 4*1*1*δ + d*d + 4*1*d*d ≤ 4*1*d*t)
    (eR : 4*R*R*δ + d*d + 4*R*d*d ≤ 4*R*d*t) :
    4*r*r*δ + d*d + 4*r*d*d ≤ 4*r*d*t := by
  have h := interval_cond_int (d : ℤ) t δ R r (by positivity) (by exact_mod_cast h1)
    (by exact_mod_cast hR) (by exact_mod_cast e1) (by exact_mod_cast eR)
  exact_mod_cast h

/-! ## The two named pivots -/

/-- Largest multiplicity satisfying the room condition at the half-rate pivot. -/
abbrev halfRadius : ℕ := 110255990

/-- Largest multiplicity satisfying the room condition at the quarter-rate pivot. -/
abbrev quarterRadius : ℕ := 72057593769492479

/-- Both pivots: agreement counts, Johnson excesses and the exact radius endpoints. -/
theorem pivot_data :
    1073741824 - 314491699 = 759250125 ∧
    759250125*759250125 = 1073741824*536870911 + 1082833961 ∧
    1073741824 - 536870913 = 536870911 ∧
    536870911*536870911 = 1073741824*268435455 + 1 ∧
    4*halfRadius*halfRadius*1082833961 + 536870911*536870911 + 4*halfRadius*536870911*536870911
      ≤ 4*halfRadius*536870911*759250125 ∧
    4*(halfRadius+1)*(halfRadius+1)*1082833961 + 536870911*536870911 +
      4*(halfRadius+1)*536870911*536870911 > 4*(halfRadius+1)*536870911*759250125 ∧
    4*quarterRadius*quarterRadius*1 + 268435455*268435455 + 4*quarterRadius*268435455*268435455
      ≤ 4*quarterRadius*268435455*536870911 ∧
    4*(quarterRadius+1)*(quarterRadius+1)*1 + 268435455*268435455 +
      4*(quarterRadius+1)*268435455*268435455 > 4*(quarterRadius+1)*268435455*536870911 := by
  decide

/-- At `314,491,699` half-rate errors, every ordinary mixed Hasse shape with multiplicity at
most `110,255,990`, or with value cutoff at most its multiplicity, has no dimension surplus. -/
theorem half_pivot_no_room (s v r : ℕ) (h : v ≤ r ∨ r ≤ halfRadius) :
    columnCount s v 536870911 (r*759250125) ≤ 1073741824 * rowCount s r := by
  refine pivot_no_room (n := 1073741824) (d := 536870911) (t := 759250125)
    (δ := 1082833961) (by decide) (by decide) (by decide) (by decide) (by decide) s v r ?_
  intro hr
  rcases h with hv | hR
  · exact Or.inl ⟨hv, by decide⟩
  · exact Or.inr (interval_cond (d := 536870911) (t := 759250125) (δ := 1082833961)
      (R := halfRadius) r hr hR (by decide) (by decide))

/-- At `536,870,913` quarter-rate errors, every ordinary mixed Hasse shape with multiplicity at
most `72,057,593,769,492,479`, or with value cutoff at most its multiplicity, has no surplus. -/
theorem quarter_pivot_no_room (s v r : ℕ) (h : v ≤ r ∨ r ≤ quarterRadius) :
    columnCount s v 268435455 (r*536870911) ≤ 1073741824 * rowCount s r := by
  refine pivot_no_room (n := 1073741824) (d := 268435455) (t := 536870911)
    (δ := 1) (by decide) (by decide) (by decide) (by decide) (by decide) s v r ?_
  intro hr
  rcases h with hv | hR
  · exact Or.inl ⟨hv, by decide⟩
  · exact Or.inr (interval_cond (d := 268435455) (t := 536870911) (δ := 1)
      (R := quarterRadius) r hr hR (by decide) (by decide))

/-- A positive surplus at the half pivot forces multiplicity above `110,255,990` and value
cutoff above the multiplicity. -/
theorem half_surplus_forces (s v r : ℕ)
    (hpos : 1073741824 * rowCount s r < columnCount s v 536870911 (r*759250125)) :
    halfRadius < r ∧ r < v := by
  constructor
  · by_contra! h
    exact (not_le.mpr hpos) (half_pivot_no_room s v r (Or.inr h))
  · by_contra! h
    exact (not_le.mpr hpos) (half_pivot_no_room s v r (Or.inl h))

/-- A positive surplus at the quarter pivot forces multiplicity above
`72,057,593,769,492,479` and value cutoff above the multiplicity. -/
theorem quarter_surplus_forces (s v r : ℕ)
    (hpos : 1073741824 * rowCount s r < columnCount s v 268435455 (r*536870911)) :
    quarterRadius < r ∧ r < v := by
  constructor
  · by_contra! h
    exact (not_le.mpr hpos) (quarter_pivot_no_room s v r (Or.inr h))
  · by_contra! h
    exact (not_le.mpr hpos) (quarter_pivot_no_room s v r (Or.inl h))

/-- The rank hypothesis of `HalfSuccessorJetInterpolation.exists_surface` on a domain of the
named length at the half pivot forces the same lower bounds. -/
theorem half_surface_requires {I : Type*} [Fintype I] (hn : Fintype.card I = 1073741824)
    (s v r : ℕ)
    (hcount : Fintype.card I * Fintype.card (HalfSuccessorJetInterpolation.JetRows s r) <
      Fintype.card (SecondPrimeQuarticInterpolation.Monomials s v 536870911 (r*759250125))) :
    halfRadius < r ∧ r < v := by
  rw [hn, card_rows, card_columns] at hcount
  exact half_surplus_forces s v r hcount

/-- The rank hypothesis of `HalfSuccessorJetInterpolation.exists_surface` on a domain of the
named length at the quarter pivot forces the same lower bounds. -/
theorem quarter_surface_requires {I : Type*} [Fintype I] (hn : Fintype.card I = 1073741824)
    (s v r : ℕ)
    (hcount : Fintype.card I * Fintype.card (HalfSuccessorJetInterpolation.JetRows s r) <
      Fintype.card (SecondPrimeQuarticInterpolation.Monomials s v 268435455 (r*536870911))) :
    quarterRadius < r ∧ r < v := by
  rw [hn, card_rows, card_columns] at hcount
  exact quarter_surplus_forces s v r hcount

/-- At the quarter pivot, a constructible interpolant (`r ≤ s + 1`, as required by
`exists_surface`) has total scalar/value degree above the budget `2^31`. Its scalar-only
factor allowance alone therefore exceeds the number of labels the safety proof must bound. -/
theorem quarter_surface_scalar_overflow (s v r : ℕ) (hs : r ≤ s+1)
    (hpos : 1073741824 * rowCount s r < columnCount s v 268435455 (r*536870911)) :
    2147483648 < s ∧ 2147483648 < v := by
  obtain ⟨hr, hv⟩ := quarter_surplus_forces s v r hpos
  have big : 2147483648 < quarterRadius := by decide
  omega

/-- At the half pivot, any two constructible interpolants have single-resultant allowance
`s₁ v₂` above the budget `2^31`. The resultant cutoff for a primary factor to divide the
companion therefore exceeds the number of labels the safety proof must bound. -/
theorem half_surfaces_resultant_overflow (s₁ v₁ r₁ s₂ v₂ r₂ : ℕ) (hs₁ : r₁ ≤ s₁+1)
    (hpos₁ : 1073741824 * rowCount s₁ r₁ < columnCount s₁ v₁ 536870911 (r₁*759250125))
    (hpos₂ : 1073741824 * rowCount s₂ r₂ < columnCount s₂ v₂ 536870911 (r₂*759250125)) :
    2147483648 < s₁ * v₂ := by
  obtain ⟨hr₁, -⟩ := half_surplus_forces s₁ v₁ r₁ hpos₁
  obtain ⟨hr₂, hv₂⟩ := half_surplus_forces s₂ v₂ r₂ hpos₂
  have h1 : halfRadius ≤ s₁ := by omega
  have h2 : halfRadius ≤ v₂ := by omega
  have big : 2147483648 < halfRadius * halfRadius := by decide
  exact big.trans_le (Nat.mul_le_mul h1 h2)

#print axioms pivot_no_room
#print axioms pivot_data
#print axioms half_pivot_no_room
#print axioms quarter_pivot_no_room
#print axioms half_surplus_forces
#print axioms quarter_surplus_forces
#print axioms half_surface_requires
#print axioms quarter_surface_requires
#print axioms quarter_surface_scalar_overflow
#print axioms half_surfaces_resultant_overflow

end ArkLib.ProximityGap.Frontier.CarbonMCAP2PivotRank
