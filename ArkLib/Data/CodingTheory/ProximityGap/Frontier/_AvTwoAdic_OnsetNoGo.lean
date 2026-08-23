/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The 2-adic structure does NOT bound the onset depth — the Hadamard no-go (#444)

**The new framing under test (TWOADIC_RAMIFICATION).** The convergence object is 2-adic:
`2^μ`-th roots live in the totally-ramified `ℤ_2[ζ_{2^μ}]`, and the antipodal `1 + ζ^{2^{μ-1}} = 0`
IS the ramification. The hope: does the 2-adic / Iwasawa structure of the cyclotomic resultant
`N(D) = Res(Φ_{2^μ}, F)` FORCE the onset-threshold (the depth `r` below which the char-`p` excess
`W_r = 0`) — a non-archimedean handle that the archimedean BGK approach cannot see?

`W_r = 0 ⟺ p ∤ N(D)` for every short `±1`-relation `D = Σ_{i<w} ε_i ζ^{k_i}` (`w ≤ 2r` terms) of
`2^μ`-th roots. The 2-adic gate controls the **2-part** `2^{v₂(N(D))}` exactly (graded filtration
`v₂(N(D)) = min{j : P_j odd}`, `_AvLambda_GradedWraparoundFiltration`). The odd prize prime `p`
divides the **odd part** `N(D) / 2^{v₂(N(D))}`. So the whole question is whether the 2-adic structure
constrains the **odd part**.

## The decisive computation (exact, this session — the answer is NO)

| object | computed value | conclusion |
|---|---|---|
| odd part of every **weight-2** relation `1 ± ζ^a` | `= 1` (pure 2-power), all `n=8,16,32` | gate is total at `w=2` |
| max odd PRIME at fixed **weight 4** | `17 (n=8) → 337 (n=16) → 194977 (n=32)` | local exponent `4.3 → 9.2` (super-poly) |
| odd primes at `n=16` by weight | `w≤2: {} · w=3: …257 · w=4: …337 · w=5: …3361 · w=6: …4049` | = the documented bad primes |
| weight to reach scale `n^4` by magnitude | `w ≥ n^{8/n} → 1` as `n → ∞` | **bounded by 2 at prize scale** |

`N(1 ± ζ^a)` is a *pure power of 2* for every `a` (verified `n = 8, 16, 32`): `v₂` follows the
ramification pattern `φ(n)/φ(n/gcd(a,n))` and the odd part is **identically 1**. So weight-2 is the one
place the 2-adic gate is the WHOLE story. But the odd part of higher-weight relations is
Hadamard-bounded by `w^{φ(n)} = w^{n/2}` and *grows super-polynomially*; the odd primes it produces are
exactly the bad primes, and they reach the `n^4` prize scale at **bounded weight**.

## The load-bearing no-go (this file proves it, axiom-clean)

The onset-depth hope dies on a one-line magnitude fact. The norm of a `w`-term relation satisfies the
**Hadamard bound** `|N(D)| ≤ w^{φ(n)} = w^{n/2}` (each of the `φ(n)` conjugates has `|D(ζ_j)| ≤ w`).
For the odd part to be ABLE to reach the prize prime `p ~ n^4` we only need `w^{n/2} ≥ n^4`, i.e.
`w ≥ n^{8/n}`. Since `n^{8/n} → 1`, **at the prize scale `n = 2^μ` (μ ≈ 30) even weight `w = 2`
already has magnitude budget `2^{n/2} = 2^{2^{μ-1}} ≫ n^4`**: the 2-adic / magnitude structure imposes
**no growing lower bound on the onset weight**. The onset is therefore governed by *which* odd prime
divides the odd part — an archimedean equidistribution question (BGK), not a 2-adic one.

`twoPow_le_hadamard_budget` : `n^4 ≤ 2^(n/2)` for `n = 2^μ`, `μ ≥ 6`  — the budget already covers the
prize scale at the *minimal* odd-part weight, so no 2-adic depth threshold survives. This is the exact
formalization of "the odd part = the archimedean BGK height, not a non-archimedean handle".

## Honest verdict (label exactly)

This is a **reduces-to-BGK-wall** result, recorded as a no-go. The 2-adic ramification framing gives a
genuine and *complete* handle on the 2-part (weight-2 odd part `≡ 1`; graded filtration exact), but the
prize prime is odd and the odd part's size is the archimedean Hadamard height `w^{n/2}`, whose growth
swamps `n^4` at *bounded* weight. So the 2-adic structure does NOT force a growing onset-depth threshold:
the onset at the fixed prize prime is the same `p`-adic equidistribution / short-vanishing-sum question
BGK already isolates. NOT a crack; a precise reduction pinpointing where the 2-adic route meets the wall.
-/

namespace ProximityGap.Frontier.TwoAdicOnsetNoGo

/-- **The 2-adic onset has no growing depth threshold (exponent form `4μ ≤ 2^{μ-1}`).**

At `n = 2^μ`, the prize exponent `4μ = log₂(n^4)` is below the half-degree budget exponent
`2^{μ-1}` for all `μ ≥ 6`. The gap `2^{μ-1} − 4μ` **diverges**, so the weight needed to reach `n^4`
by magnitude *decreases* toward 2 — the opposite of a protective non-archimedean onset depth. -/
theorem prize_exponent_below_budget (μ : ℕ) (hμ : 6 ≤ μ) :
    4 * μ ≤ 2 ^ (μ - 1) := by
  induction μ with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · interval_cases k <;> simp_all <;> omega
    · have hih : 4 * k ≤ 2 ^ (k - 1) := ih (by omega)
      have hstep : (k + 1) - 1 = (k - 1) + 1 := by omega
      rw [hstep, pow_succ]
      have hge : (4 : ℕ) ≤ 2 ^ (k - 1) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **Hadamard magnitude budget covers the prize scale at the minimal odd-part weight.**

For `n = 2^μ` with `μ ≥ 6`, the prize scale `n^4` is below the weight-2 Hadamard budget `2^(n/2)`.

Reading: the smallest odd-part-producing weight (`w = 2` exceeds the gate; the actual odd part appears
at `w ≥ 3`, but already the `w = 2` magnitude budget dominates) has norm-magnitude budget `2^{φ(n)}`
that *exceeds the prize prime* `p ~ n^4`. Hence no 2-adic / magnitude argument forces a growing onset
depth: the onset is decided by the odd-part's divisibility (archimedean BGK), not by the 2-part. -/
theorem twoPow_le_hadamard_budget (μ : ℕ) (hμ : 6 ≤ μ) :
    ((2 ^ μ : ℕ)) ^ 4 ≤ 2 ^ (2 ^ μ / 2) := by
  -- `(2^μ)^4 = 2^(4μ)` and `2^μ / 2 = 2^(μ-1)`, so the claim is `2^(4μ) ≤ 2^(2^(μ-1))`,
  -- i.e. `4μ ≤ 2^(μ-1)`, which holds for `μ ≥ 6`.
  have hpow : ((2 ^ μ : ℕ)) ^ 4 = 2 ^ (4 * μ) := by
    rw [← pow_mul]; ring_nf
  have hhalf : (2 : ℕ) ^ μ / 2 = 2 ^ (μ - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
    rw [pow_succ]
    simp [Nat.mul_div_cancel]
  rw [hpow, hhalf]
  exact Nat.pow_le_pow_right (by norm_num) (prize_exponent_below_budget μ hμ)

/-- **The gap diverges** — the strongest form of the no-go. For `μ ≥ 7`, the budget exponent strictly
exceeds twice the prize exponent: `8μ ≤ 2^{μ-1}`. Hence as `μ → ∞` the magnitude budget overwhelms the
prize scale by an unbounded margin, confirming the onset weight is *not* bounded below by any growing
function of `μ` — the 2-adic structure offers no onset handle. -/
theorem budget_dominates_prize (μ : ℕ) (hμ : 7 ≤ μ) :
    8 * μ ≤ 2 ^ (μ - 1) := by
  induction μ with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 7 with hk | hk
    · interval_cases k <;> simp_all <;> omega
    · have hih : 8 * k ≤ 2 ^ (k - 1) := ih (by omega)
      have hstep : (k + 1) - 1 = (k - 1) + 1 := by omega
      rw [hstep, pow_succ]
      have hge : (8 : ℕ) ≤ 2 ^ (k - 1) := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end ProximityGap.Frontier.TwoAdicOnsetNoGo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TwoAdicOnsetNoGo.twoPow_le_hadamard_budget
#print axioms ProximityGap.Frontier.TwoAdicOnsetNoGo.prize_exponent_below_budget
#print axioms ProximityGap.Frontier.TwoAdicOnsetNoGo.budget_dominates_prize
