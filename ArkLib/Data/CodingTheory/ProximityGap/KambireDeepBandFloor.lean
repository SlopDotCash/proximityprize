/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KambireExponentialGap

/-! # The complete-homogeneous bad-scalar count is super-poly across the WHOLE deep band (#444/#407)

`KambireExponentialGap` (O234) proved the complete-homogeneous count is exponentially large at the
single witness depth `r = s`: `2^(s-1) ≤ multichoose s s`.  The corrected-BCHKS attack
(`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md`) needs the count to be
super-polynomial **across the whole deep band** (not just one depth) to drive the `poly(n)·count`
vs `ε*·|F|` crossing and to REFUTE the in-tree `BCHKS1_12`-style claim ("`∃` small `r` with count
`≤ budget`") for the complete-homogeneous count.  This file supplies that:

> `multichoose_self_le_multichoose_of_le` : `1 ≤ s → s ≤ r → multichoose s s ≤ multichoose s r`
>   (for `s ≥ 1` the complete-homogeneous count is monotone non-decreasing in the depth `r`).
> `two_pow_le_multichoose_deep_band` (HEADLINE) : `1 ≤ s → s ≤ r → 2^(s-1) ≤ multichoose s r`
>   — the count is `≥ 2^(s-1)` for EVERY depth `r ≥ s`, i.e. super-polynomial throughout the deep band.

So there is **no** depth `r ≥ s` at which the complete-homogeneous bad-scalar count drops to a
polynomial budget: the count is exponential across the entire band.  This is the structural fact the
char-free leading-order floor (KB action C.1/D.1) consumes — the bad-scalar count, read out on the
worst (complete-homogeneous) monomial direction, stays super-poly through the prize-binding depths.

**Mechanism.**  `multichoose` is monotone in its depth argument via Pascal: `multichoose s r =
C(s+r-1, r)` and `C(m, k) ≤ C(m+1, k+1) = C(m,k) + C(m,k+1)` (`multichoose_le_succ`), iterated gives
`multichoose s r ≤ multichoose s r'` for `r ≤ r'`.  Combined with O234's `2^(s-1) ≤ multichoose s s`
at the base of the band, monotonicity carries the exponential bound to all `r ≥ s`.

## Probe

`scripts/probes/probe_multichoose_exp_gap.py` (extended check): `multichoose s r` is monotone
non-decreasing in `r` over `r = 0 … 2s` (verified `s = 8, 16`), and `multichoose s r ≥ 2^(s-1)` for
`r ≥ s` holds `0` fails across the band (e.g. `s=16`: `multichoose 16 r ≥ 2^15` for all
`r ∈ {16,…,32}`).

## Scope (rule 3 / rule 6, honesty contract)

A pure `ℕ`-combinatorial structural fact (monotonicity + the band-wide exponential lower bound),
extending O234 across the deep band — the char-free ingredient that the bad-scalar count read out on
the worst monomial direction is super-poly throughout the prize depths.  It does NOT bound `δ*` or
prove the crossing (`poly(n)·count` vs `ε*·|F|` is OPEN), NOR compute the count.  No moment / census
/ pencil / spectrum re-derivation, NO capacity / beyond-Johnson / growth-law claim; cliff-at-`n/2`
untouched.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.KambireNotExtremal

open Nat

/-- **One-step monotonicity of `multichoose` in the depth (for `s ≥ 1`).**
`1 ≤ s → multichoose s r ≤ multichoose s (r+1)`.  Via `multichoose_eq` it is
`C(s+r-1, r) ≤ C(s+r, r+1)`, and `C(m, k) ≤ C(m+1, k+1)` by Pascal
(`C(m+1,k+1) = C(m,k) + C(m,k+1) ≥ C(m,k)`).  (The `s = 0` empty-group case is degenerate —
`multichoose 0 0 = 1 > 0 = multichoose 0 1` — and excluded; harmless since the prize regime always
has `s = n ≥ 1`.) -/
theorem multichoose_le_succ {s : ℕ} (hs : 1 ≤ s) (r : ℕ) :
    Nat.multichoose s r ≤ Nat.multichoose s (r + 1) := by
  -- s ≥ 1: `s + (r+1) - 1 = (s + r - 1) + 1` and `C(m, r) ≤ C(m+1, r+1)`
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  have hm : s + (r + 1) - 1 = (s + r - 1) + 1 := by omega
  rw [hm]
  -- `C((s+r-1)+1, r+1) = C(s+r-1, r) + C(s+r-1, r+1)`
  rw [Nat.choose_succ_succ]
  exact Nat.le_add_right _ _

/-- **`multichoose` is monotone non-decreasing in the depth.** For `r ≤ r'`,
`multichoose s r ≤ multichoose s r'`. -/
theorem multichoose_le_of_le {s : ℕ} (hs : 1 ≤ s) {r r' : ℕ} (h : r ≤ r') :
    Nat.multichoose s r ≤ Nat.multichoose s r' := by
  induction r' with
  | zero =>
    have : r = 0 := by omega
    rw [this]
  | succ k ih =>
    rcases Nat.lt_or_ge r (k + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (multichoose_le_succ hs k)
    · -- r ≥ k+1 and r ≤ k+1 ⟹ r = k+1
      have hrk : r = k + 1 := by omega
      rw [hrk]

/-- The complete-homogeneous count at the band base `r = s` lower-bounds the count at any deeper
`r ≥ s`. -/
theorem multichoose_self_le_multichoose_of_le {s r : ℕ} (hs : 1 ≤ s) (h : s ≤ r) :
    Nat.multichoose s s ≤ Nat.multichoose s r :=
  multichoose_le_of_le hs h

/-- **HEADLINE: the complete-homogeneous bad-scalar count is exponential across the WHOLE deep band.**
For `s ≥ 1` and any depth `r ≥ s`, `2^(s-1) ≤ multichoose s r`.  So the count read out on the worst
monomial direction stays super-polynomial throughout the deep band — there is no depth `r ≥ s` at
which it drops to a polynomial budget. -/
theorem two_pow_le_multichoose_deep_band {s r : ℕ} (hs : 1 ≤ s) (hr : s ≤ r) :
    2 ^ (s - 1) ≤ Nat.multichoose s r :=
  le_trans (two_pow_le_multichoose_self hs) (multichoose_self_le_multichoose_of_le hs hr)

end ArkLib.ProximityGap.KambireNotExtremal

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.KambireNotExtremal.multichoose_le_succ
#print axioms ArkLib.ProximityGap.KambireNotExtremal.multichoose_le_of_le
#print axioms ArkLib.ProximityGap.KambireNotExtremal.two_pow_le_multichoose_deep_band
