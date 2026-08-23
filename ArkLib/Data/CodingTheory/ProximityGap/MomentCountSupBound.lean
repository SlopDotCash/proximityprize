/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PeriodTailMarkov

/-!
# The sharp count-based sup-norm bound (#407)

The tail count `#{b : a b > T}` is a NON-NEGATIVE INTEGER. So if the Markov bound
forces it strictly below `1`, it is exactly `0` — i.e. NO index exceeds `T`, giving a
clean sup-norm bound:

> **`forall_le_of_sum_pow_lt`** — if `0 ≤ a`, `0 < T`, and `∑_b (a b)^r < T^r`,
> then `∀ b, a b ≤ T`.

Instantiated with `a_b = |η_b|²` and `∑_{b≠0}|η_b|^{2r} = q·A_r`: whenever
`q·A_r < T^r`, every non-trivial period satisfies `|η_b|² ≤ T`, hence
`M² ≤ (q·A_r)^{1/r}`. With `A_r ≤ (2r−1)‼·n^r` and `r ≈ ln q` this is the prize
`M ≤ √(2n ln q)`. The integer-count argument is sharper than the per-term
`‖η_b‖^{2r} ≤ ∑` bound (it uses that a fractional count rounds down to zero).
Open content: `A_r ≤ Wick`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.PeriodTailMarkov

namespace ArkLib.ProximityGap.MomentCountSupBound

variable {ι : Type*} [Fintype ι]

/-- **Count-based sup bound.** If the `r`-th power-sum is strictly below `T^r`
(`T > 0`, `a ≥ 0`), then no index exceeds `T`: `∀ b, a b ≤ T`.
Proof: the integer count `#{b : T < a b}` satisfies
`#·T^r ≤ ∑(a b)^r < T^r`, so `# < 1`, so `# = 0`, so the strict-exceedance set is empty. -/
theorem forall_le_of_sum_pow_lt (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ)
    (hbound : ∑ b, (a b) ^ r < T ^ r) : ∀ b, a b ≤ T := by
  have hmarkov := card_filter_mul_le_sum_pow a ha T hT r
  set s := univ.filter (fun b => T < a b) with hs
  have hTr : (0 : ℝ) < T ^ r := by positivity
  -- (s.card : ℝ) * T^r ≤ ∑ < T^r ⟹ (s.card : ℝ) < 1 ⟹ s.card = 0
  have hlt : (s.card : ℝ) * T ^ r < 1 * T ^ r := by
    rw [one_mul]; exact lt_of_le_of_lt hmarkov hbound
  have hcard1 : (s.card : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hTr.le
  have hcard0 : s.card = 0 := by
    have : s.card < 1 := by exact_mod_cast hcard1
    omega
  intro b
  by_contra hb
  push Not at hb  -- hb : T < a b
  have hbs : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
  have : 0 < s.card := Finset.card_pos.mpr ⟨b, hbs⟩
  omega

/-- **Empty exceedance set from a strict moment threshold.** This is the filter-level form of
`forall_le_of_sum_pow_lt`: if the `r`-th power-sum is strictly below `T^r`, the exceedance set
`{b : T < a b}` is empty. -/
theorem exceedance_filter_eq_empty_of_sum_pow_lt (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T : ℝ) (hT : 0 < T) (r : ℕ) (hbound : ∑ b, (a b) ^ r < T ^ r) :
    univ.filter (fun b => T < a b) = ∅ := by
  have hle := forall_le_of_sum_pow_lt a ha T hT r hbound
  rw [Finset.filter_eq_empty_iff]
  intro b _ hb
  exact (not_lt.mpr (hle b)) hb

/-- **Zero exceedance count from a strict moment threshold.** This is the integer-count corollary:
when the moment is below `T^r`, the number of indices with `a b > T` is exactly zero. -/
theorem exceedance_card_eq_zero_of_sum_pow_lt (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T : ℝ) (hT : 0 < T) (r : ℕ) (hbound : ∑ b, (a b) ^ r < T ^ r) :
    (univ.filter (fun b => T < a b)).card = 0 := by
  rw [Finset.card_eq_zero]
  exact exceedance_filter_eq_empty_of_sum_pow_lt a ha T hT r hbound

/-- **Packaged external moment-bound form.** If an externally supplied moment bound `B` satisfies
`∑_b (a b)^r ≤ B < T^r`, then no value exceeds `T`. In the period application, `B` is the
field-scaled energy bound `q·A_r`. -/
theorem forall_le_of_sum_pow_le_of_bound_lt_pow (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T : ℝ) (hT : 0 < T) (r : ℕ) (B : ℝ) (hsum : ∑ b, (a b) ^ r ≤ B)
    (hB : B < T ^ r) : ∀ b, a b ≤ T :=
  forall_le_of_sum_pow_lt a ha T hT r (lt_of_le_of_lt hsum hB)

end ArkLib.ProximityGap.MomentCountSupBound

#print axioms ArkLib.ProximityGap.MomentCountSupBound.forall_le_of_sum_pow_lt
#print axioms ArkLib.ProximityGap.MomentCountSupBound.exceedance_filter_eq_empty_of_sum_pow_lt
#print axioms ArkLib.ProximityGap.MomentCountSupBound.exceedance_card_eq_zero_of_sum_pow_lt
#print axioms ArkLib.ProximityGap.MomentCountSupBound.forall_le_of_sum_pow_le_of_bound_lt_pow
