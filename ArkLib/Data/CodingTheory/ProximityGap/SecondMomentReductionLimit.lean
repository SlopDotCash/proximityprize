/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Issue #232 — a verified NO-GO: the whole-space second-moment reduction cannot certify the prize

`ListBallIntersectionReduction.lean` proves `|Λ(C,δ)|² ≤ ∑_c |B(c,r)| + ∑_{c≠c'} |B(c,r)∩B(c',r)|`
(diagonal + off-diagonal).  It is tempting to bound the *off-diagonal* (the #82 kernel) sharply and
conclude `|Λ| ≤ ε*·|F|`.  **This route is provably hopeless**, and this file proves exactly why: the
**diagonal alone already exceeds the squared prize threshold**, so no bound on the off-diagonal can
rescue it.

Concretely, the prize asks for `|Λ(C,δ)| ≤ ε*·|F| = q / 2¹²⁸` (with `ε* = 2⁻¹²⁸`, `|F| = q`), i.e.
`|Λ|² ≤ q² / 2²⁵⁶`.  But the diagonal `∑_c |B(c,r)|` is at least `|C| ≥ q` (every Hamming ball contains
its centre, and `|C| = q^k ≥ q` for `k ≥ 1`).  For the prize field size `q < 2²⁵⁶` we have

  `diagonal ≥ q  >  q² / 2²⁵⁶ = (ε*·q)²`,

i.e. the diagonal *strictly exceeds the squared prize threshold*.  Hence the reduction's right-hand
side is `> (ε*·|F|)²` no matter how small the off-diagonal is — the bound is **vacuous for the prize**.

* `reduction_diagonal_exceeds_threshold` — the arithmetic core: `q < 2²⁵⁶`, `0 < q`, `q ≤ diag` ⟹
  `q² < 2²⁵⁶ · diag`, i.e. `diag > (ε*·q)²`.
* `reduction_too_weak_for_prize` — the packaged statement: under the same hypotheses, the reduction
  bound `diag + off` (any `off ≥ 0`) satisfies `q² < 2²⁵⁶ · (diag + off)`, so it can never certify
  `|Λ|² ≤ q²/2²⁵⁶`.

**Consequence (the genuine learning).**  The *worst-case* list size cannot be controlled by the
whole-space second moment — that moment is dominated by the (harmless but huge) diagonal `|C|·V(r)`.
The sharp control must come from the **list-restricted** second moment (the agreements among the
`≤ |Λ|` codewords near one centre, which is exactly the Johnson bound — tight, and vacuous past the
Johnson radius `1-√ρ`) or from **algebraic / multiplicity** structure (Guruswami–Sudan and beyond).
This is the precise, machine-checked reason the elementary moment routes do not pin `δ*` past Johnson.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.CodingTheory.SecondMomentReductionLimit

/-- **The diagonal of the second-moment reduction exceeds the squared prize threshold.**
The prize threshold for `|Λ|²` is `(ε*·q)² = q² / 2²⁵⁶`.  The diagonal `∑_c |B(c,r)| ≥ |C| ≥ q`.
For `q < 2²⁵⁶` (the prize field size), `q² < 2²⁵⁶ · diag`, i.e. `diag > q² / 2²⁵⁶`: the diagonal
alone overshoots the entire budget. -/
theorem reduction_diagonal_exceeds_threshold (q diag : ℕ)
    (hq0 : 0 < q) (hqbound : q < 2 ^ 256) (hdiag : q ≤ diag) :
    q ^ 2 < 2 ^ 256 * diag := by
  have h1 : q * q < 2 ^ 256 * q := mul_lt_mul_of_pos_right hqbound hq0
  have h2 : 2 ^ 256 * q ≤ 2 ^ 256 * diag := mul_le_mul_left' hdiag _
  calc q ^ 2 = q * q := pow_two q
    _ < 2 ^ 256 * q := h1
    _ ≤ 2 ^ 256 * diag := h2

/-- **The reduction is vacuous for the prize.**  For any non-negative off-diagonal `off`, the full
reduction bound `diag + off` still strictly exceeds the squared prize threshold `q² / 2²⁵⁶` (because
the diagonal already does).  Hence `|Λ|² ≤ diag + off` can never certify `|Λ|² ≤ q² / 2²⁵⁶`, i.e.
`|Λ| ≤ ε*·|F|` — no matter how sharply the off-diagonal #82 kernel is bounded. -/
theorem reduction_too_weak_for_prize (q diag off : ℕ)
    (hq0 : 0 < q) (hqbound : q < 2 ^ 256) (hdiag : q ≤ diag) :
    q ^ 2 < 2 ^ 256 * (diag + off) := by
  calc q ^ 2 < 2 ^ 256 * diag := reduction_diagonal_exceeds_threshold q diag hq0 hqbound hdiag
    _ ≤ 2 ^ 256 * (diag + off) := mul_le_mul_left' (Nat.le_add_right _ _) _

/-- **Non-vacuity.**  A concrete prize-scale instance: `q = 2²⁰⁰` (a 200-bit field, well inside
`q < 2²⁵⁶`), with the minimal diagonal `diag = q`.  The squared prize threshold `q²/2²⁵⁶ = 2¹⁴⁴` is
strictly below the diagonal `2²⁵⁶·q = 2⁴⁵⁶`-scaled budget — i.e. `(2²⁰⁰)² < 2²⁵⁶ · 2²⁰⁰`. -/
theorem reduction_too_weak_nonvacuous :
    (2 ^ 200 : ℕ) ^ 2 < 2 ^ 256 * (2 ^ 200) := by
  norm_num

end ArkLib.CodingTheory.SecondMomentReductionLimit

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.SecondMomentReductionLimit.reduction_diagonal_exceeds_threshold
#print axioms ArkLib.CodingTheory.SecondMomentReductionLimit.reduction_too_weak_for_prize
#print axioms ArkLib.CodingTheory.SecondMomentReductionLimit.reduction_too_weak_nonvacuous
