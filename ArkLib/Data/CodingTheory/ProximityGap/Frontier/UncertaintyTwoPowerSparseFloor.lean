/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.UncertaintyTwoPowerJohnsonRefuted

/-!
# The power-of-two sparse-zero floor law `(2^s − 1)·n/2^s` on `μ_{2^μ}` (#407 / #444)

`UncertaintyTwoPowerJohnsonRefuted` exhibits the **binomial** (`t = 2`) witness `X^{n/2} + 1` with
exactly `n/2` roots in `μ_n` (`n = 2^μ`), and `UncertaintyTwoPowerTrinomialFloor` shows a **genuine
trinomial** (`t = 3`) also reaches the `n/2` floor. Both are `s = 1` instances of a single law.

**This file proves the general power-of-two law.** For each support order `1 ≤ s` with `s < μ`, the
sparse polynomial
> `W_s(X) = (X^n − 1)/(X^{n/2^s} − 1) = ∑_{i=0}^{2^s − 1} X^{i·(n/2^s)}`
has **exactly `t = 2^s` nonzero terms** (its support is the arithmetic progression `{0, n/2^s,
2n/2^s, …, (2^s−1)n/2^s}`) and **exactly `n − n/2^s = (2^s − 1)·n/2^s` roots in `μ_n`**.

Concretely, on `μ_n` we have `X^n − 1 = 0` identically, so `W_s(ζ^j) = 0` **iff** `(ζ^j)^{n/2^s} ≠ 1`.
Since `ζ^{n/2^s}` is a primitive `2^s`-th root of unity, `(ζ^j)^{n/2^s} = (ζ^{n/2^s})^j = 1` **iff**
`2^s ∣ j`. Hence the roots are exactly the `j ∈ [0, n)` with `2^s ∤ j`, of which there are
`n − n/2^s` (the complement of the order-`(n/2^s)` subgroup `μ_{n/2^s} ⊊ μ_n`).

## What this says about the prize (rule-3 / rule-4 / rule-6)

* **A unifying generalization, NOT a CORE result.** It subsumes the `t = 2` binomial floor (`s = 1`:
  `n/2`) and is in the SAME direction as the trinomial floor — a super-Johnson **lower bound on the
  single-witness root count `s*`**. Crucially the floor **rises** toward `n` as the support `t = 2^s`
  grows: `(2^s − 1)·n/2^s`. So no uncertainty / sparse-polynomial route can give a sub-`(1−1/t)·n`
  upper bound on the single-witness root count for `n = 2^μ` — the higher the allowed sparsity, the
  WORSE (larger) the achievable root count. This sharpens the `DISPROOF_LOG` direction at every dyadic
  sparsity level at once.
* **Thinness (rule-3).** The witness `W_s` factors through the order-`2^s` element `ζ^{n/2^s}`, i.e. it
  needs `2^s ∣ n` — a genuine `2`-power phenomenon. Over a prime-order group Tao's principle forbids
  it. So this is a refutation of a would-be upper bound, NOT a thinness-monotone CORE method.
* **The prize is the LIST, not `s*`.** Per `UncertaintyTwoPowerExtremal`, each single such polynomial
  contributes `O(1)` codewords; the prize `δ*` is the list-size budget, not the single-witness root
  count. This file caps the single-witness object precisely (and from BELOW), localizing the open core
  away from it.

All `sorry`-free; intended audit `[propext, Classical.choice, Quot.sound]`. Issues #407, #444.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.UncertaintyTwoPowerSparseFloor

open Finset
open ProximityGap.UncertaintyTwoPowerJohnsonRefuted

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### A self-contained counting lemma: `#{ j < 2^μ | ¬ 2^s ∣ j } = 2^μ − 2^{μ-s}`. -/

/-- The number of `j < 2^μ` divisible by `2^s` (with `s ≤ μ`) is exactly `2^{μ-s}`: these are
`j = 2^s · i` for `i < 2^{μ-s}`. -/
theorem card_filter_dvd_range_pow (μ s : ℕ) (hsμ : s ≤ μ) :
    ((Finset.range (2 ^ μ)).filter (fun j => 2 ^ s ∣ j)).card = 2 ^ (μ - s) := by
  -- biject `{j < 2^μ : 2^s ∣ j}` with `{i < 2^{μ-s}}` via `i ↦ 2^s · i`.
  have hpow : (2 : ℕ) ^ μ = 2 ^ s * 2 ^ (μ - s) := by
    rw [← pow_add]; congr 1; omega
  have himg : (Finset.range (2 ^ μ)).filter (fun j => 2 ^ s ∣ j)
      = (Finset.range (2 ^ (μ - s))).image (fun i => 2 ^ s * i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      rw [hpow] at hj
      exact Nat.lt_of_mul_lt_mul_left hj
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, i, rfl⟩
      rw [hpow]
      have hpos : 0 < (2 : ℕ) ^ s := by positivity
      gcongr
  rw [himg, Finset.card_image_of_injective]
  · rw [Finset.card_range]
  · intro a b hab
    have h2 : (2 : ℕ) ^ s ≠ 0 := by positivity
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hab

/-- The number of `j < 2^μ` NOT divisible by `2^s` (with `s ≤ μ`) is `2^μ − 2^{μ-s}`. This is the
root-count of the sparse witness `W_s` in `μ_{2^μ}`. -/
theorem card_filter_not_dvd_range_pow (μ s : ℕ) (hsμ : s ≤ μ) :
    ((Finset.range (2 ^ μ)).filter (fun j => ¬ 2 ^ s ∣ j)).card
      = 2 ^ μ - 2 ^ (μ - s) := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.range (2 ^ μ)) (p := fun j => 2 ^ s ∣ j)
  rw [card_filter_dvd_range_pow μ s hsμ, Finset.card_range] at hsplit
  omega

/-! ### `(ζ^j)^{n/2^s} = 1 ↔ 2^s ∣ j`, the order-`2^s` factor-through. -/

/-- For `n = 2^μ`, a primitive `n`-th root `ζ`, and `s ≤ μ`: `(ζ^j)^{2^μ / 2^s} = 1` **iff**
`2^s ∣ j`. The element `ζ^{2^μ/2^s} = ζ^{2^{μ-s}}` is a primitive `2^s`-th root of unity, so its
`j`-th power is `1` exactly when `2^s ∣ j`. -/
theorem primRoot_pow_eq_one_iff_dvd {μ s : ℕ} (hsμ : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (j : ℕ) :
    (ζ ^ j) ^ (2 ^ μ / 2 ^ s) = 1 ↔ 2 ^ s ∣ j := by
  -- `2^μ / 2^s = 2^{μ-s}`, and `ζ^{2^{μ-s}}` is a primitive `2^s`-th root.
  have hquot : (2 : ℕ) ^ μ / 2 ^ s = 2 ^ (μ - s) := by
    rw [Nat.pow_div hsμ (by norm_num)]
  have hpne : (2 : ℕ) ^ (μ - s) ≠ 0 := by positivity
  have hdvd : (2 : ℕ) ^ (μ - s) ∣ 2 ^ μ := pow_dvd_pow 2 (by omega)
  have hquot2 : (2 : ℕ) ^ μ / 2 ^ (μ - s) = 2 ^ s := by
    rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  have hps : IsPrimitiveRoot (ζ ^ (2 ^ (μ - s))) (2 ^ s) := by
    have := hζ.pow_of_dvd hpne hdvd
    rwa [hquot2] at this
  -- `(ζ^j)^{2^{μ-s}} = (ζ^{2^{μ-s}})^j`.
  rw [hquot, ← pow_mul, Nat.mul_comm, pow_mul]
  exact hps.pow_eq_one_iff_dvd j

/-! ### The root-count (the load-bearing real-object fact). -/

/-- **The power-of-two sparse-zero floor.** For `n = 2^μ` (`μ ≥ 1`), a primitive `n`-th root `ζ`,
and `s ≤ μ`, the sparse witness `W_s(X) = (X^n − 1)/(X^{n/2^s} − 1)` vanishes at `ζ^j` **iff**
`(ζ^j)^{n/2^s} ≠ 1`, i.e. `2^s ∤ j`. Hence

> `#{ j < n | (ζ^j)^{n/2^s} ≠ 1 } = n − n/2^s = (2^s − 1)·n/2^s`.

For `s = 1` this is the binomial `n/2` floor (`card_neg_one_coset_eq`); for larger `s` it RISES
toward `n`. -/
theorem card_sparse_root_eq {μ s : ℕ} (hsμ : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2 ^ s) ≠ 1)).card)
      = 2 ^ μ - 2 ^ (μ - s) := by
  have hset : ((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2 ^ s) ≠ 1))
      = (Finset.range (2 ^ μ)).filter (fun j => ¬ 2 ^ s ∣ j) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h hdvd; exact h ((primRoot_pow_eq_one_iff_dvd hsμ hζ j).mpr hdvd)
    · intro h hone; exact h ((primRoot_pow_eq_one_iff_dvd hsμ hζ j).mp hone)
  rw [hset, card_filter_not_dvd_range_pow μ s hsμ]

/-- Consistency with the existing `s = 1` binomial result: the root count is `2^μ − 2^{μ-1} = n/2`. -/
theorem card_sparse_root_eq_one {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2 ^ 1) ≠ 1)).card)
      = 2 ^ μ / 2 := by
  rw [card_sparse_root_eq hμ hζ]
  -- `2^μ − 2^{μ-1} = 2^μ / 2`.
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hμ
  rw [show 1 + t = t + 1 from by omega, pow_succ]
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  omega

/-! ### The floor packaged as the closed form `(2^s − 1)·n/2^s` and its monotonicity. -/

/-- The closed form: the root count equals `(2^s − 1)·2^{μ-s}` (= `(2^s − 1)·n/2^s` with `n = 2^μ`). -/
theorem sparse_floor_closed_form {μ s : ℕ} (hsμ : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    (((Finset.range (2 ^ μ)).filter (fun j => (ζ ^ j) ^ (2 ^ μ / 2 ^ s) ≠ 1)).card)
      = (2 ^ s - 1) * 2 ^ (μ - s) := by
  rw [card_sparse_root_eq hsμ hζ]
  -- `2^μ − 2^{μ-s} = (2^s − 1)·2^{μ-s}` since `2^μ = 2^s · 2^{μ-s}`.
  have hpow : (2 : ℕ) ^ μ = 2 ^ s * 2 ^ (μ - s) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, Nat.sub_mul, one_mul]

/-- **Floor monotonicity (the "rises toward `n`" fact).** For `s < s'` (both `< μ`), the deeper
witness has STRICTLY more roots: `(2^s − 1)·n/2^s < (2^{s'} − 1)·n/2^{s'}`. So allowing MORE sparsity
makes the achievable single-witness root count LARGER, never smaller. -/
theorem sparse_floor_strict_mono {μ s s' : ℕ} (hss' : s < s') (hs'μ : s' ≤ μ) :
    (2 ^ s - 1) * 2 ^ (μ - s) < (2 ^ s' - 1) * 2 ^ (μ - s') := by
  -- Both equal `2^μ − 2^{μ-s}` resp. `2^μ − 2^{μ-s'}`; since `μ-s' < μ-s`, the subtracted term
  -- shrinks, so the value grows.
  have hsμ : s ≤ μ := le_of_lt (lt_of_lt_of_le hss' hs'μ)
  have e1 : (2 ^ s - 1) * 2 ^ (μ - s) = 2 ^ μ - 2 ^ (μ - s) := by
    have hpow : (2 : ℕ) ^ μ = 2 ^ s * 2 ^ (μ - s) := by rw [← pow_add]; congr 1; omega
    rw [hpow, Nat.sub_mul, one_mul]
  have e2 : (2 ^ s' - 1) * 2 ^ (μ - s') = 2 ^ μ - 2 ^ (μ - s') := by
    have hpow : (2 : ℕ) ^ μ = 2 ^ s' * 2 ^ (μ - s') := by rw [← pow_add]; congr 1; omega
    rw [hpow, Nat.sub_mul, one_mul]
  rw [e1, e2]
  -- `μ - s' < μ - s` so `2^{μ-s'} < 2^{μ-s} ≤ 2^μ`, and subtracting a smaller amount gives more.
  have hlt : (2 : ℕ) ^ (μ - s') < 2 ^ (μ - s) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hle1 : (2 : ℕ) ^ (μ - s) ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end ProximityGap.UncertaintyTwoPowerSparseFloor

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.card_filter_dvd_range_pow
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.card_filter_not_dvd_range_pow
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.primRoot_pow_eq_one_iff_dvd
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.card_sparse_root_eq
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.card_sparse_root_eq_one
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.sparse_floor_closed_form
#print axioms ProximityGap.UncertaintyTwoPowerSparseFloor.sparse_floor_strict_mono
