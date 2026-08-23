/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Bridge B29 — Binding-depth shift up the dyadic tower (target E5, #444)

**Spec.** `m*(2n) ≤ m*(n) + 1`, conditional on the *clean recursion holding at the binder*.
**Approach.** The budget doubles, the cascade shifts by one depth step.

## Context (the empirical formula E5)

In the δ* bridge program, write `D n m` for the *worst over-determined far-line incidence at
scale `n` and over-determination depth `m`* — the binding cascade `D*(m)` of
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md` (§B, E2). This is exactly
the orbit/incidence count that the substrate `OrbitCountCrossingLaw.crossing_law` governs:
at the binder the budget test `D ≤ budget` becomes an orbit-count test.

The **binding depth** `m*(n)` is the first depth `m` whose worst incidence drops to the budget:
`m*(n) = min { m : D n m ≤ budget n }`, with the prize budget `budget n = n` (`= q·ε*`).
The master gap identity E1, `δ* = 1 − ρ − (m*−1)/n`, then turns a bound on `m*` into a bound on
`δ*`, and the prize (E7) is `m* = O(log n)`.

E5 is the **dyadic cascade recursion**: empirically `D*_{2n}(m) = D*_n(m−1)` (the cascade *shifts
by one* up a tower level) at shallow depth; if it held *at the binder* it would give the
self-similar descent `m*(2n) ≤ m*(n)+1`, hence `m* = O(log n)`. The OPEN content (the *plateau
excess per tower level* — see E5/E7) is precisely whether the recursion stays clean at the binder.

## What is proved here (axiom-clean, no `sorry`)

This brick discharges the *deductive* half of E5: it makes the implication
"clean recursion at the binder + budget doubles ⟹ binding depth shifts by ≤ 1" a theorem.

* `mStar` — the binding depth as `Nat.find` of the budget-crossing predicate (least `m` with
  `D n m ≤ budget n`), given a witness that some depth binds.
* `mStar_spec`, `mStar_le_of_binds` — `mStar` binds, and is the least binder.
* `mStar_tower_shift` — **the B29 result**: from
    1. `hbud : budget n ≤ budget (2*n)`  (the budget at least doubles — here only monotonicity is
       used; `budget = id` gives `n ≤ 2n`),
    2. `hclean : D (2*n) (mStar D budget n hex + 1) ≤ D n (mStar D budget n hex)`  (the
       **clean recursion at the binder** — the cascade shifts by one at the binding depth),
  it follows that `2*n` binds at depth `mStar n + 1` and hence `mStar (2*n) ≤ mStar n + 1`.

The hypothesis `hclean` is the *named, honest gap*: it is exactly the "clean recursion holding at
the binder" the spec conditions on, and the open quantity of E5. Everything else is unconditional.

## Honest scope

This is an **honest reduction**, not a closure: the empirical input — that the dyadic cascade
recursion `D_{2n}(m*+1) ≤ D_n(m*)` actually holds at the binder (no plateau excess) — is carried
as the explicit hypothesis `hclean`. Numerically E5 is only *partial* (`n=32` shows a doubled
`89`-rung, i.e. a +1 plateau excess that still keeps the shift ≤ what is bounded here for that
case). What is a theorem is the deduction: *granting* the clean shift at the binder, the binding
depth grows by at most one per tower level, which is the engine of `m* = O(log n)` (E7).
-/

namespace ArkLib.ProximityGap.BridgeB29

/-- The **binding depth** `m*(n)`: the least over-determination depth `m` at which the worst
far-line incidence `D n m` drops to the budget `budget n`.  Defined as `Nat.find` of the
budget-crossing predicate, given a witness `hex` that some depth binds. -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) : ℕ :=
  Nat.find hex

/-- `mStar` binds: at depth `mStar n` the worst incidence is within budget. -/
theorem mStar_spec (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) :
    D n (mStar D budget n hex) ≤ budget n :=
  Nat.find_spec hex

/-- `mStar` is the **least** binder: any depth `m` that binds is at least `mStar n`. -/
theorem mStar_le_of_binds (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) {m : ℕ} (hm : D n m ≤ budget n) :
    mStar D budget n hex ≤ m :=
  Nat.find_min' hex hm

/-- **B29 — binding-depth shift up the dyadic tower (target E5).**

Conditional on the *clean recursion holding at the binder* (`hclean`: the cascade at scale `2n`,
one depth step past `m*(n)`, is no larger than the cascade at scale `n` at its binder) and the
budget being non-decreasing under doubling (`hbud`: `budget n ≤ budget (2n)` — for `budget = id`
this is just `n ≤ 2n`), the binding depth grows by at most one per tower level:

  `m*(2n) ≤ m*(n) + 1`.

This is the self-similar descent step that, iterated, yields `m* = O(log n)` (E7) — the prize —
*granting* the empirically-observed (but open at the binder) clean cascade shift. -/
theorem mStar_tower_shift
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hbud : budget n ≤ budget (2 * n))
    (hclean : D (2 * n) (mStar D budget n hex + 1) ≤ D n (mStar D budget n hex)) :
    ∃ hex2 : (∃ m, D (2 * n) m ≤ budget (2 * n)),
      mStar D budget (2 * n) hex2 ≤ mStar D budget n hex + 1 := by
  -- depth `m*(n)+1` binds at scale `2n`:
  --   D (2n) (m*(n)+1) ≤ D n (m*(n))   [clean recursion at the binder]
  --                    ≤ budget n       [definition of m*(n)]
  --                    ≤ budget (2n)    [budget non-decreasing]
  have hbinds2 : D (2 * n) (mStar D budget n hex + 1) ≤ budget (2 * n) :=
    le_trans (le_trans hclean (mStar_spec D budget n hex)) hbud
  -- hence `2n` binds, so `mStar (2n)` is defined, and it is ≤ this binder.
  refine ⟨⟨mStar D budget n hex + 1, hbinds2⟩, ?_⟩
  exact mStar_le_of_binds D budget (2 * n) _ hbinds2

/-- Convenience corollary at the **prize budget** `budget = id` (`budget n = n = q·ε*`).
Here the budget-doubling hypothesis `n ≤ 2n` is automatic, so only the clean-recursion-at-the-
binder hypothesis remains — exactly the E5 open quantity. -/
theorem mStar_tower_shift_prize
    (D : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ n)
    (hclean : D (2 * n) (mStar D id n hex + 1) ≤ D n (mStar D id n hex)) :
    ∃ hex2 : (∃ m, D (2 * n) m ≤ 2 * n),
      mStar D id (2 * n) hex2 ≤ mStar D id n hex + 1 := by
  have hbud : (id n : ℕ) ≤ id (2 * n) := by
    simp only [id]; omega
  -- reuse the general lemma with `budget = id`
  exact mStar_tower_shift D id n hex hbud hclean

end ArkLib.ProximityGap.BridgeB29

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB29.mStar_spec
#print axioms ArkLib.ProximityGap.BridgeB29.mStar_le_of_binds
#print axioms ArkLib.ProximityGap.BridgeB29.mStar_tower_shift
#print axioms ArkLib.ProximityGap.BridgeB29.mStar_tower_shift_prize
