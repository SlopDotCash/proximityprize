/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# GRADED_FILTRATION angle: the wraparound filtration is IRRELEVANT to `A_K ≤ Wick_K` (#444)

Re-pointed open kernel (2026-06-19): for `μ_n` (order `n = 2^μ`, `p ∈ [n^4, 2n^4)`),
`A_K := (1/q)·Σ_{b≠0}|η_b|^{2K} = N_K − n^{2K}/p`, `Wick_K := (2K−1)!!·n^K`, prove
`A_K ≤ C·Wick_K` at deep `K` worst-case over the prime window.

## What this file records (the GRADED_FILTRATION verdict)

The task asked: does the 2-adic wraparound filtration `v_2(N(D)) = min{j : P_j odd}` predict
WHICH `(p,K)` go bad, and does it bound the wraparound count below the Wick slack (proving
`A_K ≤ Wick`)?  **Exact computation answers: NO — the filtration is the wrong control, because
`A_K ≤ Wick_K` does not bind where wraparound lives.**

### Exact findings (n=8 full window 115 primes, n=16 full window 691 primes, n=32 sample)

* **v_2(p−1) does NOT separate bad from good.** The 3 "bad" primes (`W_K := A_K − E_K^C > 0`
  for some `K`) at n=16 are `p = 76001, 107137, 108497` with `v_2(p−1) = 5, 7, 4` — scattered
  across the range. Bad-rate by `v_2` is flat (`0.3% / 0.6% / 2.6%`, the last is `1/38` noise).

* **The wraparound decomposition `N_K = DIAG + CROSS`** (DIAG = integer-sum self-energy with no
  wrap collision; CROSS = wraparound collisions = the genuine mod-`p` excess) shows `W_K > 0`
  (badness against the **refuted** char-0 target `E_K^C`) IS driven by CROSS. But:

* **Against the SURVIVING target `Wick_K`, the binding point is `K = 1`, where CROSS = 0.**
  Over the entire n=16 window the binding-`K` histogram is `{1 : 691}`; the global
  `max_K A_K/Wick_K = 0.999878 = 1 − n/p` is attained at `K = 1`. CROSS only enters at deep `K`
  where the Wick headroom has already grown to `~0.84·Wick`. So wraparound NEVER threatens
  `A_K ≤ Wick`; the 2-adic filtration governs only the refuted `A_K ≤ E_K^C`.

* **The normalized ratio `ρ_K := A_K / Wick_K` is monotone non-increasing in `K`** (0 violations
  over 921 pairs at n=8, 7601 pairs at n=16, sample at n=32; worst consecutive ratio 0.937).

* **The first step is provable in CLOSED FORM.** `N_2 = E_2 = 3n^2 − 3n` exactly (a known
  closed form for `μ_n`, char-0 and char-`p` agree at `K=2`), so
  `ρ_2/ρ_1 → (3 − 3/n)/3 = 1 − 1/n < 1`, approaching 1 from below but STRICTLY below for every
  finite `n` (the `K`-moment-barrier signature without a crossing).

## The load-bearing reduction

```
  A_K ≤ Wick_K  for ALL K ≥ 1   ⟸   [ A_1 ≤ Wick_1 : 1 − n/p ≤ 1, UNCONDITIONAL ]
                                 AND  [ ρ_{K+1} ≤ ρ_K : energy-growth A_{K+1} ≤ (2K+1)·n·A_K ].
```
Monotonicity is equivalent to the additive-energy growth bound `A_{K+1} ≤ (2K+1)·n·A_K` and is
the single open analytic input. The wraparound filtration does NOT enter it.

This file proves the base case and the reduction skeleton axiom-clean. The `K=1→2` step is
closed-form (`N_2 = 3n^2 − 3n`) and would discharge the first rung; the general-`K` energy-growth
bound is the open residual.
-/

set_option autoImplicit false


namespace Issue444.GradedFiltration

/-- **Base case (unconditional, wraparound-free).** `A_1 = n − n^2/p ≤ n = Wick_1`, i.e. the
Parseval floor `1 − n/p ≤ 1`. This is the BINDING point for `A_K ≤ Wick_K` per exact computation
over the full n=8/16/32 prime windows. No wraparound (`CROSS = 0` at `K=1`). -/
theorem A1_le_Wick1 (n p : ℕ) (hp : 0 < p) :
    (n : ℚ) - (n : ℚ) ^ 2 / (p : ℚ) ≤ (n : ℚ) := by
  have hsq : (0 : ℚ) ≤ (n : ℚ) ^ 2 / (p : ℚ) := by positivity
  linarith

/-- **The reduction core.** If the normalized ratios `ρ : ℕ → ℚ` (with `ρ K = A K / Wick K`)
satisfy `ρ 1 ≤ 1` and are monotone non-increasing for `K ≥ 1`, then `ρ K ≤ 1` for every `K ≥ 1`.
This is the logical step the exact monotonicity computation supports. -/
theorem ratio_le_one_of_base_and_monotone
    (ρ : ℕ → ℚ) (hbase : ρ 1 ≤ 1)
    (hmono : ∀ K, 1 ≤ K → ρ (K + 1) ≤ ρ K) :
    ∀ K, 1 ≤ K → ρ K ≤ 1 := by
  intro K hK
  induction K with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge 1 (m + 1) with h | h
    · have hm1 : 1 ≤ m := by omega
      have hstep := hmono m hm1
      have hρm : ρ m ≤ 1 := ih hm1
      linarith
    · have hm : m + 1 = 1 := by omega
      rw [hm]; exact hbase

/-- **Assembled target.** `A K ≤ Wick K` for all `K ≥ 1`, given:
* `Wick K > 0` (true: `Wick_K = (2K−1)!!·n^K > 0`),
* the base case `A 1 ≤ Wick 1` (proved unconditionally by `A1_le_Wick1`), and
* the EXACT-OBSERVED monotonicity of `A K / Wick K` in `K` (equivalently the energy-growth bound
  `A_{K+1} ≤ (2K+1)·n·A_K`, the single open analytic input — the wraparound filtration does not
  enter it).

The GRADED_FILTRATION verdict: this reduction has NO dependence on the 2-adic/Hasse filtration; the
binding constraint is the wrap-free `K=1` Parseval floor. -/
theorem A_le_Wick_of_base_and_monotone
    (A Wick : ℕ → ℚ)
    (hWpos : ∀ K, 1 ≤ K → 0 < Wick K)
    (hbase : A 1 ≤ Wick 1)
    (hmono : ∀ K, 1 ≤ K → A (K + 1) / Wick (K + 1) ≤ A K / Wick K) :
    ∀ K, 1 ≤ K → A K ≤ Wick K := by
  have hb : A 1 / Wick 1 ≤ 1 := by
    rw [div_le_one (hWpos 1 le_rfl)]; exact hbase
  have key := ratio_le_one_of_base_and_monotone (fun K => A K / Wick K) hb hmono
  intro K hK
  have := key K hK
  rwa [div_le_one (hWpos K hK)] at this

/-- **The `K=1 → 2` step is closed-form.** With the EXACT additive-energy `N_2 = 3n^2 − 3n` for
`μ_n` and `A_2 = N_2 − n^4/p`, `A_1 = n − n^2/p`, the normalized step is
`ρ_2/ρ_1 = (3 − 3/n − n^2/(3p)…)/(1 − n/p)`, with leading value `(3 − 3/n)/3 = 1 − 1/n < 1`.
Here we record the load-bearing inequality at the level the closed form provides:
`A_2 ≤ (2·1+1)·n·A_1 = 3n·A_1` whenever `A_2 ≤ 3n·A_1` (the energy-growth bound at `K=1`), which
the exact `N_2 = 3n^2 − 3n` underwrites (`N_2 = 3n·(n−1) ≤ 3n·n` and the DC subtractions only
help). Stated as a clean implication consuming the closed-form `N_2` value. -/
theorem energyGrowth_step_one
    (n p : ℕ) (hn : 3 ≤ n)
    (A1 A2 : ℚ) (hA1 : A1 = (n : ℚ) - (n : ℚ) ^ 2 / (p : ℚ))
    (hA2 : A2 = (3 * (n : ℚ) ^ 2 - 3 * (n : ℚ)) - (n : ℚ) ^ 4 / (p : ℚ)) :
    A2 ≤ 3 * (n : ℚ) * A1 := by
  subst hA1 hA2
  have hn3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by linarith
  rw [← sub_nonneg]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · -- p = 0: division by 0 is 0 in ℚ; the slack is 3n ≥ 0.
    subst hp; simp only [Nat.cast_zero, div_zero, sub_zero]
    nlinarith [hn0]
  · have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    -- The slack 3n·(n − n^2/p) − (3n^2 − 3n − n^4/p) = (3n·p + n^4 − 3n^3)/p ≥ 0
    -- since n ≥ 3 gives n^4 − 3n^3 = n^3·(n−3) ≥ 0 and 3n·p > 0.
    have expand :
        3 * (n : ℚ) * ((n : ℚ) - (n : ℚ) ^ 2 / (p : ℚ))
          - (3 * (n : ℚ) ^ 2 - 3 * (n : ℚ) - (n : ℚ) ^ 4 / (p : ℚ))
        = (3 * (n : ℚ) * (p : ℚ) + (n : ℚ) ^ 4 - 3 * (n : ℚ) ^ 3) / (p : ℚ) := by
      field_simp; ring
    rw [expand, le_div_iff₀ hpQ, zero_mul]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hn0) (by linarith : (0:ℚ) ≤ (n:ℚ) - 3),
      mul_nonneg (mul_nonneg hn0 hn0) hpQ.le, hpQ.le, hn0]

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms A1_le_Wick1
#print axioms ratio_le_one_of_base_and_monotone
#print axioms A_le_Wick_of_base_and_monotone
#print axioms energyGrowth_step_one

end Issue444.GradedFiltration
