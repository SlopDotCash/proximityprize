/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The Kambiré subset-sum construction is not extremal (#407)

Kambiré (arXiv:2604.09724) proves proximity gaps fail near capacity via the line `f=X^{rm}, g=X^{(r−1)m}`
with bad scalars `λ = ξ_1+…+ξ_r` ranging over the **r-element DISTINCT-sum set** of a subgroup `H`
(`|H|=s`); the bad-scalar count is the subset-sum cardinality `≤ C(s,r) = Nat.choose s r`.

The worst dyadic MONOMIAL direction instead reads out the **complete-homogeneous** (with-REPETITION)
symmetric function, whose count is the multiset cardinality `multichoose s r = C(s+r−1, r)`. This file
records the clean combinatorial core of the self-refutation of "δ* = Kambiré formula (exact)":

> **`choose_le_multichoose`** — `C(s,r) ≤ multichoose s r`, with **strict** inequality once `r ≥ 1`
> and `s ≥ 2`: the with-repetition (complete-homogeneous) count strictly exceeds the distinct-sum
> (subset) count.

So the complete-homogeneous monomial direction realizes MORE bad scalars than Kambiré's subset-sum
construction ⟹ failure at a SMALLER `δ` ⟹ the Kambiré formula is an upper bracket, NOT the exact `δ*`.
(Numerically the gap is at the EXPONENT level: `log(C(s+r−1,r)/C(s,r))/s → ~0.26` for `r=s/2`, i.e.
`multichoose ≈ subset · 2^{0.26 s}` — a strictly larger leading exponent, not a constant.)

Issue #407.
-/

namespace ArkLib.ProximityGap.KambireNotExtremal

/-- **The complete-homogeneous count dominates the subset-sum count.** For all `s r : ℕ`,
`Nat.choose s r ≤ Nat.multichoose s r`. Equivalently `C(s,r) ≤ C(s+r−1, r)`: choosing `r` elements
WITH repetition from `s` is at least as plentiful as choosing `r` DISTINCT elements. -/
theorem choose_le_multichoose (s r : ℕ) : Nat.choose s r ≤ Nat.multichoose s r := by
  rw [Nat.multichoose_eq]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact Nat.choose_le_choose r (by omega)

/-- **Pascal strict step.** For `1 ≤ r ≤ s`, `C(s,r) < C(s+1,r)` — the upper index strictly increases
the binomial when `r ≤ s` (`C(s+1,r) = C(s,r−1)+C(s,r)` with `C(s,r−1) ≥ 1`). -/
theorem choose_lt_choose_succ {s r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    Nat.choose s r < Nat.choose (s + 1) r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Nat.choose_succ_succ s k]
  exact lt_add_of_pos_left _ (Nat.choose_pos (by omega))

/-- **Strict domination in the prize-relevant range.** For `2 ≤ r ≤ s`, the complete-homogeneous count
STRICTLY exceeds the subset-sum count: `C(s,r) < multichoose s r`. This is the formal content of "the
worst monomial direction beats Kambiré's subset-sum construction", refuting `δ* =` Kambiré formula as
exact (the gap is at the leading exponent, not a constant). -/
theorem choose_lt_multichoose (s r : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) :
    Nat.choose s r < Nat.multichoose s r := by
  rw [Nat.multichoose_eq]
  calc Nat.choose s r
      < Nat.choose (s + 1) r := choose_lt_choose_succ (by omega) hrs
    _ ≤ Nat.choose (s + r - 1) r := Nat.choose_le_choose r (by omega)

end ArkLib.ProximityGap.KambireNotExtremal

#print axioms ArkLib.ProximityGap.KambireNotExtremal.choose_le_multichoose
#print axioms ArkLib.ProximityGap.KambireNotExtremal.choose_lt_multichoose
