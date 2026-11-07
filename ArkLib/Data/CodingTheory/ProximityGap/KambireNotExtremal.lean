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
symmetric function, whose *input* count is the multiset cardinality
`multichoose s r = C(s+r−1, r)`. What this file proves is only a comparison of these two **input
counts** (finite binomial arithmetic):

> **`choose_le_multichoose`** — `C(s,r) ≤ multichoose s r` for all `s, r`;
> **`choose_lt_multichoose`** — strict inequality for `2 ≤ r ≤ s`.
> (At `r = 1` both counts equal `s`, so strictness genuinely needs `r ≥ 2`.)

**Scope (audit correction, PG-037).** These inequalities count *parameter tuples* (subsets versus
multisets), not *distinct bad scalars*. Nothing here constructs the competing monomial direction,
identifies its bad scalars, or shows that distinct multisets give distinct scalar values:
symmetric-function images can collide extensively, and every image set is bounded by the field size.
So this file does **not** show that the complete-homogeneous direction has more bad scalars, does
not show failure at a smaller `δ`, and does **not** refute an exact Kambiré `δ*` formula. Such a
conclusion would additionally need an actual bad-scalar map, a collision/image-size bound, and a
threshold comparison. (Arithmetic of the input-count gap: for `r = s/2`,
`ln(C(s+r−1,r)/C(s,r))/s → (3/2)·ln 3 − 2·ln 2 ≈ 0.2616` nats, i.e.
`multichoose ≈ subset · e^{0.26 s} ≈ subset · 2^{0.377 s}` — an exponential gap between input
counts, not between distinct-scalar counts.)

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

/-- **Strict domination of input counts.** For `2 ≤ r ≤ s`, the multiset (with-repetition) count
STRICTLY exceeds the subset (distinct) count: `C(s,r) < multichoose s r`. This compares numbers of
parameter tuples only; it does not bound distinct bad scalars (images may collide and are capped by
the field size), so by itself it neither shows that a monomial direction beats Kambiré's
construction nor refutes an exact Kambiré `δ*` formula. -/
theorem choose_lt_multichoose (s r : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s) :
    Nat.choose s r < Nat.multichoose s r := by
  rw [Nat.multichoose_eq]
  calc Nat.choose s r
      < Nat.choose (s + 1) r := choose_lt_choose_succ (by omega) hrs
    _ ≤ Nat.choose (s + r - 1) r := Nat.choose_le_choose r (by omega)

end ArkLib.ProximityGap.KambireNotExtremal

#print axioms ArkLib.ProximityGap.KambireNotExtremal.choose_le_multichoose
#print axioms ArkLib.ProximityGap.KambireNotExtremal.choose_lt_multichoose
