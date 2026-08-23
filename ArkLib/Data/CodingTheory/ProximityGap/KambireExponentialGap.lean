/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KambireNotExtremal
import Mathlib.Data.Nat.Choose.Central

/-! # The complete-homogeneous / subset-sum gap is SUPER-POLYNOMIAL, not a constant (#444/#407)

`KambireNotExtremal` proved the complete-homogeneous (with-repetition) count STRICTLY dominates the
subset-sum (distinct) count: `Nat.choose s r < Nat.multichoose s r` for `2 ≤ r ≤ s`.  But it only
stated NUMERICALLY (in prose) that the gap is at the **leading exponent**, not a constant —
`multichoose / choose ≈ 2^{Θ(s)}`.  That qualitative claim is the load-bearing one for the corrected
BCHKS floor (`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md`, action D.2): it
is WHY the complete-homogeneous worst direction changes the LEADING ORDER of `δ*`, not just a
constant correction.  This file turns that into a theorem at the cleanest in-regime witness depth
`r = s` (the maximal / deep-band depth):

> `two_pow_le_multichoose_self` (HEADLINE) : `1 ≤ s → 2^(s-1) ≤ Nat.multichoose s s`.

Since `Nat.choose s s = 1`, this exhibits the ratio `multichoose s s / choose s s = multichoose s s
≥ 2^(s-1)` — an EXPONENTIAL (hence super-polynomial) lower bound on the gap.  So the gap is provably
NOT bounded by any polynomial in `s`: the complete-homogeneous count exceeds the subset-sum count by
an exponential factor at depth `r = s`.

**Mechanism.**  `multichoose s s = C(2s-1, s)` and `2·C(2s-1, s) = C(2s, s) = centralBinom s`
(`two_mul_multichoose_self_eq_centralBinom`).  The central binomial coefficient satisfies the clean
exponential lower bound `2^n ≤ centralBinom n` (`two_pow_le_centralBinom`, induction via
`succ_mul_centralBinom_succ`: `(n+1)·CB(n+1) = 2(2n+1)·CB(n) ≥ 2(n+1)·CB(n)` so `CB(n+1) ≥ 2·CB(n)`).
Hence `2·multichoose s s = centralBinom s ≥ 2^s`, i.e. `multichoose s s ≥ 2^(s-1)`.

## Probe

`scripts/probes/probe_multichoose_exp_gap.py`: at the prize depth `r = s/2`,
`log₂(multichoose/choose)/s` is bounded away from `0` (≈ `0.18 → 0.37` over `s = 4 … 256`, a positive
constant — super-poly gap confirmed).  The clean witness `r = s`: `C(2s-1, s) ≥ 2^(s-1)` holds
`0` fails for `s = 1 … 24` (e.g. `s=12`: `C(23,12) = 1352078 ≥ 2^11 = 2048`).

## Scope (rule 3 / rule 6, honesty contract)

A combinatorial constraint sharpening `KambireNotExtremal`'s strict inequality into a SUPER-POLY
separation at depth `r = s` — the formal content of "the gap is at the leading exponent, not a
constant" (the corrected-BCHKS attack's char-free leading-order ingredient, action D.2).  It does NOT
bound `δ*` or the bad-scalar count itself, NOR claim the leading-order crossing (that needs the
`poly(n)·h_j` vs `ε*·|F|` analysis, OPEN).  Pure `ℕ`-combinatorics (`Nat.choose` /
`Nat.centralBinom`); no field/regime/character input.  NO moment / census / pencil / spectrum
re-derivation, NO capacity / beyond-Johnson / growth-law claim; cliff-at-`n/2` untouched.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.KambireNotExtremal

open Nat

/-- **`multichoose s s = C(2s-1, s)`, and twice it is the central binomial `C(2s, s)`.** For `s ≥ 1`,
`2 * Nat.multichoose s s = Nat.centralBinom s`.  (`multichoose s s = C(s+s-1, s) = C(2s-1, s)`, and
the Pascal split `C(2s, s) = C(2s-1, s-1) + C(2s-1, s) = 2·C(2s-1, s)` by the symmetry
`C(2s-1, s-1) = C(2s-1, s)`.) -/
theorem two_mul_multichoose_self_eq_centralBinom {s : ℕ} (hs : 1 ≤ s) :
    2 * Nat.multichoose s s = Nat.centralBinom s := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [Nat.multichoose_eq, Nat.centralBinom_eq_two_mul_choose]
  -- `multichoose (m+1) (m+1) = C((m+1)+(m+1)-1, m+1) = C(2m+1, m+1)`
  have he1 : (m + 1) + (m + 1) - 1 = 2 * m + 1 := by omega
  have he2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [he1, he2]
  -- goal: `2 * C(2m+1, m+1) = C(2m+1+1, m+1)`
  rw [Nat.choose_succ_succ (2 * m + 1) m]
  -- `C(2m+2, m+1) = C(2m+1, m) + C(2m+1, m+1)`, and `C(2m+1, m+1) = C(2m+1, m)` (symm half)
  rw [Nat.choose_symm_half m]
  ring

/-- **Exponential lower bound on the central binomial coefficient.** `2^n ≤ Nat.centralBinom n`.
Induction via `succ_mul_centralBinom_succ`: `(n+1)·CB(n+1) = 2(2n+1)·CB(n) ≥ 2(n+1)·CB(n)`, so
`CB(n+1) ≥ 2·CB(n)`, and `CB(0) = 1 = 2^0`. -/
theorem two_pow_le_centralBinom (n : ℕ) : 2 ^ n ≤ Nat.centralBinom n := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ k ih =>
    have hrec : (k + 1) * Nat.centralBinom (k + 1) = 2 * (2 * k + 1) * Nat.centralBinom k :=
      Nat.succ_mul_centralBinom_succ k
    -- from the recurrence, `CB(k+1) ≥ 2 * CB(k)`
    have hstep : 2 * Nat.centralBinom k ≤ Nat.centralBinom (k + 1) := by
      have hkpos : 0 < k + 1 := Nat.succ_pos k
      -- `(k+1) * (2 * CB k) ≤ (k+1) * CB(k+1)` since `(k+1)*(2*CB k) ≤ 2*(2k+1)*CB k = (k+1)*CB(k+1)`
      have hle : (k + 1) * (2 * Nat.centralBinom k) ≤ (k + 1) * Nat.centralBinom (k + 1) := by
        rw [hrec]
        have heq : (k + 1) * (2 * Nat.centralBinom k) = 2 * (k + 1) * Nat.centralBinom k := by ring
        rw [heq]
        have hcoef : 2 * (k + 1) ≤ 2 * (2 * k + 1) := by omega
        gcongr
      exact Nat.le_of_mul_le_mul_left hle hkpos
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * Nat.centralBinom k := by exact Nat.mul_le_mul_left 2 ih
      _ ≤ Nat.centralBinom (k + 1) := hstep

/-- **HEADLINE: the complete-homogeneous count at depth `r = s` is exponentially large.**
For `s ≥ 1`, `2^(s-1) ≤ Nat.multichoose s s`.  Since `Nat.choose s s = 1`, the gap ratio
`multichoose s s / choose s s = multichoose s s ≥ 2^(s-1)` is EXPONENTIAL — the formal content of
"the complete-homogeneous / subset-sum gap is at the leading exponent, not a constant". -/
theorem two_pow_le_multichoose_self {s : ℕ} (hs : 1 ≤ s) :
    2 ^ (s - 1) ≤ Nat.multichoose s s := by
  -- `2 * multichoose s s = centralBinom s ≥ 2^s = 2 * 2^(s-1)`, so `multichoose s s ≥ 2^(s-1)`.
  have hcb : 2 * Nat.multichoose s s = Nat.centralBinom s :=
    two_mul_multichoose_self_eq_centralBinom hs
  have hexp : 2 ^ s ≤ Nat.centralBinom s := two_pow_le_centralBinom s
  have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  -- `2 * 2^(s-1) ≤ centralBinom s = 2 * multichoose s s`
  have : 2 * 2 ^ (s - 1) ≤ 2 * Nat.multichoose s s := by rw [hcb, ← hpow]; exact hexp
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

/-- **The gap exceeds the subset-sum count by an exponential factor at depth `r = s`.** Restatement
exposing the ratio: `Nat.choose s s * 2^(s-1) ≤ Nat.multichoose s s` (and `choose s s = 1`). -/
theorem choose_self_mul_two_pow_le_multichoose_self {s : ℕ} (hs : 1 ≤ s) :
    Nat.choose s s * 2 ^ (s - 1) ≤ Nat.multichoose s s := by
  rw [Nat.choose_self, one_mul]
  exact two_pow_le_multichoose_self hs

end ArkLib.ProximityGap.KambireNotExtremal

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.KambireNotExtremal.two_mul_multichoose_self_eq_centralBinom
#print axioms ArkLib.ProximityGap.KambireNotExtremal.two_pow_le_centralBinom
#print axioms ArkLib.ProximityGap.KambireNotExtremal.two_pow_le_multichoose_self
#print axioms ArkLib.ProximityGap.KambireNotExtremal.choose_self_mul_two_pow_le_multichoose_self
