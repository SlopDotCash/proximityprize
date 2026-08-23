/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselSeriesCoeff

/-!
# Issue #304 — the Newton tail entry: finite-range vanishing closes the WHOLE tail

**The loop breaker.**  The corrected-representative machinery (`GenuinePpolyConverter`) had a
documented circularity: the converter consumes the truncation identity, the truncation
capstones consume the representative.  This file provides the ab-initio entry, purely from the
structure of the Newton iteration (`HenselSeriesCoeff`):

The Newton recursion is **coefficient-recursive**: `coeff (t+1) γ = −u · coeff (t+1)
(eval (S t) Q)` where `S t` is the order-`t` truncation of `γ`.  Hence on a vanishing range the
partial sums freeze (`S_stable_of_vanish`), and the evaluations `eval (S (k−1)) Q` accumulate
vanishing coefficients: below `k` from `eval γ Q = 0` (agreement below), on `[k, T]` from the
recursion itself.  If the evaluation is supported in degrees `≤ T` — a **bounded-degree** fact
about the fixed polynomial data, NOT about `γ` — then it is identically zero
(`eval_S_eq_zero_of_range_vanish`), and then the recursion kills **every** higher coefficient
(`tail_of_range_vanish`): the truncation `S (k−1)` is an exact root, and the iteration never
moves again.

So: **counting-range vanishing `[k, T]` + the degree bound `T` on `eval (trunc_{k} γ) Q`
⟹ the full tail `∀ t ≥ k, coeff t γ = 0`** — no representative input, no converter loop.
The degree bound is supplied by `eval_S_coeff_eq_zero_of_bounded`: when `Q`'s coefficients are
supported in degrees `≤ DX` (polynomial-coerced GS data), the evaluation is supported in
degrees `≤ DX + deg_Y Q · (k−1)`, so `T := DX + deg_Y Q · (k−1)` always works
(`tail_of_range_vanish_of_polyQ`).

## Contents
* `coeff_γ_succ_eq` — the recursion, exported.
* `S_succ_eq_add_monomial` — the step monomial carries exactly `coeff (t+1) γ`.
* `S_stable_of_vanish` — the partial sums freeze on a vanishing range.
* `coeff_eval_sub_below` — agreement below an order propagates through `eval · Q`.
* `eval_S_eq_zero_of_range_vanish` — the frozen evaluation is zero (given the degree bound).
* `tail_of_range_vanish` — **the tail**, ab initio.
* `coeff_pow_eq_zero_of_support` / `eval_S_coeff_eq_zero_of_bounded` /
  `tail_of_range_vanish_of_polyQ` — the degree-bound supply for polynomial-coerced `Q`.

## References
* [BCIKS20] §5 (Claim 5.8′/Prop 5.5 — the bounded-degree tail); the F-series ledger on
  issue #304 (the converter loop this file breaks).
-/

set_option linter.style.longLine false

namespace ProximityPrize.HenselSeriesCoeff

open PowerSeries

variable {R : Type*} [CommRing R]
variable (Q : Polynomial R⟦X⟧) (c : R)

/-! ## The recursion, exported -/

/-- **The Newton recursion at the coefficient level**: each new coefficient of `γ` is the
unit-scaled correction read off the previous partial sum. -/
theorem coeff_γ_succ_eq (t : ℕ) :
    coeff (t + 1) (γ Q c)
      = -(Ring.inverse (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))
          * coeff (t + 1) (Polynomial.eval (S Q c t) Q) := by
  rw [coeff_γ, S, map_add, coeff_monomial, if_pos rfl,
    coeff_S_eq_zero_of_lt Q c (Nat.lt_succ_self t), zero_add]

/-- The step monomial carries exactly the new coefficient of `γ`. -/
theorem S_succ_eq_add_monomial (t : ℕ) :
    S Q c (t + 1) = S Q c t + PowerSeries.monomial (t + 1) (coeff (t + 1) (γ Q c)) := by
  rw [coeff_γ_succ_eq]
  rfl

/-! ## Freezing on a vanishing range -/

/-- **The partial sums freeze on a vanishing range**: if the coefficients of `γ` vanish on
`[k, T]` (`0 < k`), then `S t = S (k−1)` for every `t ∈ [k−1, T]`. -/
theorem S_stable_of_vanish {k T : ℕ} (hk : 0 < k)
    (hrange : ∀ s, k ≤ s → s ≤ T → coeff s (γ Q c) = 0) :
    ∀ t, k - 1 ≤ t → t ≤ T → S Q c t = S Q c (k - 1) := by
  intro t
  induction t with
  | zero =>
      intro h1 _
      have h0 : k - 1 = 0 := by omega
      rw [h0]
  | succ t ih =>
      intro h1 h2
      rcases Nat.lt_or_ge t (k - 1) with hlt | hge
      · -- t + 1 = k - 1 exactly
        have : t + 1 = k - 1 := by omega
        rw [this]
      · have hcoeff : coeff (t + 1) (γ Q c) = 0 :=
          hrange (t + 1) (by omega) h2
        rw [S_succ_eq_add_monomial, hcoeff, map_zero, add_zero]
        exact ih hge (by omega)

/-! ## Agreement below an order propagates through evaluation -/

/-- Agreement below order `m` propagates through `eval · Q`. -/
theorem coeff_eval_sub_below {γ₁ γ₂ : R⟦X⟧} {m : ℕ}
    (h : ∀ j < m, coeff j γ₁ = coeff j γ₂) :
    ∀ j < m, coeff j (Polynomial.eval γ₁ Q) = coeff j (Polynomial.eval γ₂ Q) := by
  intro j hj
  rw [coeff_eval_eq_sum_range, coeff_eval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have hb : p.2 < m := lt_of_le_of_lt (by omega) hj
  rw [coeff_pow_sub_below h i p.2 hb]

/-! ## The frozen evaluation is zero -/

variable (hc0 : Polynomial.eval c (Q₀ Q) = 0)
variable (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))

include hc0 hu in
/-- **The frozen evaluation is zero.**  Counting-range vanishing `[k, T]` plus the degree bound
`T` on `eval (S (k−1)) Q` force `eval (S (k−1)) Q = 0`: coefficients below `k` vanish by
agreement with the exact root `γ`, coefficients in `[k, T]` by the recursion, coefficients
above `T` by the bound. -/
theorem eval_S_eq_zero_of_range_vanish {k T : ℕ} (hk : 0 < k)
    (hrange : ∀ s, k ≤ s → s ≤ T → coeff s (γ Q c) = 0)
    (hbound : ∀ j, T < j → coeff j (Polynomial.eval (S Q c (k - 1)) Q) = 0) :
    Polynomial.eval (S Q c (k - 1)) Q = 0 := by
  set A := Polynomial.eval c (Polynomial.derivative (Q₀ Q)) with hA
  ext j
  rw [map_zero]
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- below k: agreement with the exact root γ
    have hagree : ∀ i < k, coeff i (S Q c (k - 1)) = coeff i (γ Q c) :=
      fun i hi => (coeff_γ_eq_S Q c (by omega)).symm
    have h := coeff_eval_sub_below Q hagree j hjk
    rw [h, eval_γ_eq_zero Q c hc0 hu, map_zero]
  · rcases Nat.lt_or_ge T j with hTj | hjT
    · exact hbound j hTj
    · -- k ≤ j ≤ T: the recursion at t := j − 1 ∈ [k−1, T−1]
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      have hS : S Q c t = S Q c (k - 1) :=
        S_stable_of_vanish Q c hk hrange t (by omega) (by omega)
      have hγ0 : coeff (t + 1) (γ Q c) = 0 := hrange (t + 1) (by omega) (by omega)
      have hrec := coeff_γ_succ_eq Q c t
      rw [hγ0, hS] at hrec
      -- 0 = −u · w with u the inverse of the unit A ⟹ w = 0
      set w := coeff (t + 1) (Polynomial.eval (S Q c (k - 1)) Q) with hwdef
      have hAu : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hu
      have huw : Ring.inverse A * w = 0 := by
        have h := hrec.symm
        rwa [neg_mul, neg_eq_zero] at h
      calc w = (A * Ring.inverse A) * w := by rw [hAu, one_mul]
        _ = A * (Ring.inverse A * w) := by ring
        _ = 0 := by rw [huw, mul_zero]

include hc0 hu in
/-- **THE TAIL, AB INITIO (the loop breaker).**  Counting-range vanishing `[k, T]` plus the
degree bound `T` on the frozen evaluation force the **entire** tail: `coeff t γ = 0` for every
`t ≥ k`.  The truncation `S (k−1)` is an exact root, so the Newton iteration never moves
again. -/
theorem tail_of_range_vanish {k T : ℕ} (hk : 0 < k)
    (hrange : ∀ s, k ≤ s → s ≤ T → coeff s (γ Q c) = 0)
    (hbound : ∀ j, T < j → coeff j (Polynomial.eval (S Q c (k - 1)) Q) = 0) :
    ∀ t, k ≤ t → coeff t (γ Q c) = 0 := by
  have h0 : Polynomial.eval (S Q c (k - 1)) Q = 0 :=
    eval_S_eq_zero_of_range_vanish Q c hc0 hu hk hrange hbound
  -- the partial sums freeze FOREVER
  have hfreeze : ∀ t, k - 1 ≤ t → S Q c t = S Q c (k - 1) := by
    intro t
    induction t with
    | zero => intro h1; have : k - 1 = 0 := by omega
              rw [this]
    | succ t ih =>
        intro h1
        rcases Nat.lt_or_ge t (k - 1) with hlt | hge
        · have : t + 1 = k - 1 := by omega
          rw [this]
        · have hS := ih hge
          have hw : coeff (t + 1) (Polynomial.eval (S Q c t) Q) = 0 := by
            rw [hS, h0, map_zero]
          rw [S_succ_eq_add_monomial, coeff_γ_succ_eq, hw, mul_zero, map_zero, add_zero]
          exact hS
  intro t hkt
  rw [coeff_γ, hfreeze t (by omega)]
  exact coeff_S_eq_zero_of_lt Q c (by omega)

/-! ## The degree-bound supply for polynomial-coerced `Q` -/

/-- Support bound for powers: a series supported in degrees `≤ d` has its `i`-th power
supported in degrees `≤ i·d`. -/
theorem coeff_pow_eq_zero_of_support {γ : R⟦X⟧} {d : ℕ}
    (h : ∀ j, d < j → coeff j γ = 0) :
    ∀ (i : ℕ) (j : ℕ), i * d < j → coeff j (γ ^ i) = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
  | succ i ih =>
      intro j hj
      rw [pow_succ, PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.lt_or_ge (i * d) p.1 with h1 | h1
      · rw [ih p.1 h1, zero_mul]
      · have h2 : d < p.2 := by
          have : i * d + d < p.1 + p.2 := by
            rw [hp]
            calc i * d + d = (i + 1) * d := by ring
              _ < j := hj
          omega
        rw [h p.2 h2, mul_zero]

/-- **The degree bound for polynomial-coerced `Q`**: if every coefficient of `Q` is supported
in degrees `≤ DX`, the frozen evaluation is supported in degrees
`≤ DX + deg_Y Q · (k−1)`. -/
theorem eval_S_coeff_eq_zero_of_bounded {DX k : ℕ}
    (hQX : ∀ i, ∀ a, DX < a → coeff a (Q.coeff i) = 0) :
    ∀ j, DX + Q.natDegree * (k - 1) < j →
      coeff j (Polynomial.eval (S Q c (k - 1)) Q) = 0 := by
  intro j hj
  rw [coeff_eval_eq_sum_range]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have hiQ : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge DX p.1 with h1 | h1
  · rw [hQX i p.1 h1, zero_mul]
  · -- p.2 exceeds the power-support bound i·(k−1)
    have hS : ∀ a, k - 1 < a → coeff a (S Q c (k - 1)) = 0 :=
      fun a ha => coeff_S_eq_zero_of_lt Q c ha
    have h2 : i * (k - 1) < p.2 := by
      have hle : i * (k - 1) ≤ Q.natDegree * (k - 1) := Nat.mul_le_mul_right _ hiQ
      omega
    rw [coeff_pow_eq_zero_of_support hS i p.2 h2, mul_zero]

include hc0 hu in
/-- **The composed ab-initio tail for polynomial-coerced `Q`** — the production-ready form:
counting-range vanishing on `[k, DX + deg_Y Q · (k−1)]` alone closes the entire tail.  `T` is
an explicit function of the fixed GS degrees; no representative, no converter loop. -/
theorem tail_of_range_vanish_of_polyQ {DX k : ℕ} (hk : 0 < k)
    (hQX : ∀ i, ∀ a, DX < a → coeff a (Q.coeff i) = 0)
    (hrange : ∀ s, k ≤ s → s ≤ DX + Q.natDegree * (k - 1) → coeff s (γ Q c) = 0) :
    ∀ t, k ≤ t → coeff t (γ Q c) = 0 :=
  tail_of_range_vanish Q c hc0 hu hk hrange
    (eval_S_coeff_eq_zero_of_bounded Q c hQX)

end ProximityPrize.HenselSeriesCoeff

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_γ_succ_eq
#print axioms ProximityPrize.HenselSeriesCoeff.S_succ_eq_add_monomial
#print axioms ProximityPrize.HenselSeriesCoeff.S_stable_of_vanish
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_below
#print axioms ProximityPrize.HenselSeriesCoeff.eval_S_eq_zero_of_range_vanish
#print axioms ProximityPrize.HenselSeriesCoeff.tail_of_range_vanish
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_pow_eq_zero_of_support
#print axioms ProximityPrize.HenselSeriesCoeff.eval_S_coeff_eq_zero_of_bounded
#print axioms ProximityPrize.HenselSeriesCoeff.tail_of_range_vanish_of_polyQ
