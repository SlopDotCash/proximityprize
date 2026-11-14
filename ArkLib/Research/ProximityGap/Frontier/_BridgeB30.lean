/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Bridge B30 — net m* increment per doubling ≤ plateau width at the binder (target E5, #444)

**Spec.** *Net `m*` increment per doubling ≤ plateau width at the binding value*
(crossing-radius bookkeeping).

## Context (E5, and the refinement of B29)

In the δ* bridge program (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`),
`D n m` is the worst over-determined far-line incidence at scale `n`, over-determination depth `m`;
the **binding depth** `m*(n) = min { m : D n m ≤ budget n }`. The master gap identity E1,
`δ* = 1 − ρ − (m*−1)/n`, turns a bound on `m*` into the prize (E7: `m* = O(log n)`).

B29 (`_BridgeB29`) proved the *clean* tower step `m*(2n) ≤ m*(n)+1` **assuming** the recursion is
clean at the binder (no plateau excess). Empirically that is only PARTIAL: at `n=32` the cascade
has a **doubled `89`-rung** — a *plateau* of width `2` at the binding value — which pushes `m*`
from `3` to `5`, i.e. a net increment of `2`, not `1`.

B30 is the honest **bookkeeping** that does NOT assume the recursion is clean. It defines the
*plateau width* `w` at scale `2n` as: a length such that, starting at depth `m*(n)`, after `w`
further depth steps the scale-`2n` cascade has dropped to budget. Then the net increment is
bounded by that plateau width:

  `m*(2n) ≤ m*(n) + w`.

This is the **crossing-radius bookkeeping**: the binder at `2n` lies at most `w` (the plateau
width) past the binder at `n`. It specializes to B29 when `w = 1` (clean recursion), and it is the
form that actually accommodates the observed `w = 2` plateau-doubling at `n = 32`.

## Substrate

The crossing test `D ≤ budget` is exactly the orbit-count crossing of
`OrbitCountCrossingLaw.crossing_law` (`|B| ≤ n ⟺ N ≤ d`) at the binder; here we work at the level
of the binding-depth bookkeeping `Nat.find`, reusing the `mStar` definition pattern of B29.

## What is proved here (axiom-clean, no `sorry`)

* `mStar` — the binding depth (`Nat.find` of the budget-crossing predicate), as in B29.
* `mStar_le_of_binds`, `mStar_spec` — least-binder / binds.
* `plateauWidthBound` — the explicit *plateau-width hypothesis*: a width `w` together with a proof
  that scale-`2n` binds at depth `m*(n) + w`.
* **`mStar_increment_le_plateauWidth`** — the **B30 result**: from a plateau-width witness
  `D (2n) (m*(n) + w) ≤ budget (2n)`, the net increment is `m*(2n) − m*(n) ≤ w`, i.e.
  `m*(2n) ≤ m*(n) + w`.
* `netIncrement_le_plateauWidth` — same, phrased on the (truncated-subtraction) net increment.
* `mStar_increment_one_of_clean` — the B29 special case `w = 1` recovered as a corollary.

The honest gap (E5/E7 open content) is the **plateau-width bound itself**: that `w` stays
`O(1)` (or, summed up the tower, that `Σ w` stays `O(log n)`). That is carried as the explicit
hypothesis — never discharged. B30 makes the bookkeeping (increment ≤ plateau width) a theorem.
-/

namespace ArkLib.ProximityGap.BridgeB30

/-- The **binding depth** `m*(n)`: least over-determination depth `m` with `D n m ≤ budget n`.
`Nat.find` of the budget-crossing predicate, given a witness `hex` that some depth binds. -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) : ℕ :=
  Nat.find hex

/-- `mStar` binds. -/
theorem mStar_spec (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) :
    D n (mStar D budget n hex) ≤ budget n :=
  Nat.find_spec hex

/-- `mStar` is the least binder. -/
theorem mStar_le_of_binds (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) {m : ℕ} (hm : D n m ≤ budget n) :
    mStar D budget n hex ≤ m :=
  Nat.find_min' hex hm

/-- **B30 — net `m*` increment per doubling ≤ plateau width at the binder (target E5).**

`w` is the **plateau width** at scale `2n`: the number of further depth steps, starting at the
scale-`n` binder `m*(n)`, after which the scale-`2n` cascade has dropped to budget. The hypothesis
`hplateau : D (2n) (m*(n) + w) ≤ budget (2n)` records exactly that the scale-`2n` cascade binds at
depth `m*(n) + w`. Then the binder at `2n` is at most `w` past the binder at `n`:

  `m*(2n) ≤ m*(n) + w`.

This is the crossing-radius bookkeeping. It is unconditional in `w`: the *content* (E5/E7 open) is
a bound on `w`, carried by `hplateau`, never assumed clean. -/
theorem mStar_increment_le_plateauWidth
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n w : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hplateau : D (2 * n) (mStar D budget n hex + w) ≤ budget (2 * n)) :
    ∃ hex2 : (∃ m, D (2 * n) m ≤ budget (2 * n)),
      mStar D budget (2 * n) hex2 ≤ mStar D budget n hex + w := by
  refine ⟨⟨mStar D budget n hex + w, hplateau⟩, ?_⟩
  exact mStar_le_of_binds D budget (2 * n) _ hplateau

/-- **Net-increment form.** The truncated-subtraction net increment `m*(2n) − m*(n)` is bounded by
the plateau width `w`. (Equivalent to `mStar_increment_le_plateauWidth`; this is the "increment per
doubling ≤ plateau width" phrasing of the spec.) -/
theorem netIncrement_le_plateauWidth
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n w : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hplateau : D (2 * n) (mStar D budget n hex + w) ≤ budget (2 * n)) :
    ∃ hex2 : (∃ m, D (2 * n) m ≤ budget (2 * n)),
      mStar D budget (2 * n) hex2 - mStar D budget n hex ≤ w := by
  obtain ⟨hex2, hle⟩ := mStar_increment_le_plateauWidth D budget n w hex hplateau
  exact ⟨hex2, by omega⟩

/-- **B29 recovered as the plateau-width-`1` (clean recursion) special case.** When the cascade
shifts cleanly by one at the binder — `D (2n) (m*(n)+1) ≤ D n (m*(n))` — and the budget is
non-decreasing under doubling, the plateau width is `1`, so `m*(2n) ≤ m*(n) + 1`. -/
theorem mStar_increment_one_of_clean
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hbud : budget n ≤ budget (2 * n))
    (hclean : D (2 * n) (mStar D budget n hex + 1) ≤ D n (mStar D budget n hex)) :
    ∃ hex2 : (∃ m, D (2 * n) m ≤ budget (2 * n)),
      mStar D budget (2 * n) hex2 ≤ mStar D budget n hex + 1 := by
  have hplateau : D (2 * n) (mStar D budget n hex + 1) ≤ budget (2 * n) :=
    le_trans (le_trans hclean (mStar_spec D budget n hex)) hbud
  exact mStar_increment_le_plateauWidth D budget n 1 hex hplateau

/-- **Non-vacuity / sanity instance.** Concrete cascade matching the `n=32` plateau-doubling
observation: take `D` with a binder at depth `3` for scale `n` and a binder at depth `5` for scale
`2n` (a plateau of width `w = 2` at the binding value). The bookkeeping then yields the observed
net increment `m*(2n) ≤ m*(n) + 2`, with `m*(n) = 3`, demonstrating the lemma is non-vacuous and
accommodates plateau width `> 1`. -/
example :
    let D : ℕ → ℕ → ℕ := fun n m => if n = 32 then (if m ≥ 5 then 0 else 100)
                                     else (if m ≥ 3 then 0 else 100)
    let budget : ℕ → ℕ := fun n => n
    ∃ (hex : ∃ m, D 16 m ≤ budget 16)
      (hex2 : ∃ m, D (2 * 16) m ≤ budget (2 * 16)),
      mStar D budget (2 * 16) hex2 ≤ mStar D budget 16 hex + 2 := by
  intro D budget
  have hex : ∃ m, D 16 m ≤ budget 16 := ⟨3, by decide⟩
  -- It suffices that scale-32 binds at depth `m*(16) + 2`; since `m*(16) ≤ 3` and the
  -- scale-32 cascade is `≤ budget` for every depth `≥ 5`, depth `m*(16)+2 ≤ 5` suffices once we
  -- also know `m*(16) ≥ 3`. We get `m*(16) = 3` by least-binder + a per-depth check.
  have hle3 : mStar D budget 16 hex ≤ 3 :=
    mStar_le_of_binds D budget 16 hex (by decide)
  have hspec : D 16 (mStar D budget 16 hex) ≤ budget 16 := mStar_spec D budget 16 hex
  have hge3 : 3 ≤ mStar D budget 16 hex := by
    rcases Nat.lt_or_ge (mStar D budget 16 hex) 3 with h | h
    · exfalso
      interval_cases hm : (mStar D budget 16 hex) <;> simp_all [D, budget]
    · exact h
  have hbinder16 : mStar D budget 16 hex = 3 := le_antisymm hle3 hge3
  have hplateau : D (2 * 16) (mStar D budget 16 hex + 2) ≤ budget (2 * 16) := by
    rw [hbinder16]; decide
  obtain ⟨hex2, hle⟩ := mStar_increment_le_plateauWidth D budget 16 2 hex hplateau
  exact ⟨hex, hex2, hle⟩

end ArkLib.ProximityGap.BridgeB30

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB30.mStar_spec
#print axioms ArkLib.ProximityGap.BridgeB30.mStar_le_of_binds
#print axioms ArkLib.ProximityGap.BridgeB30.mStar_increment_le_plateauWidth
#print axioms ArkLib.ProximityGap.BridgeB30.netIncrement_le_plateauWidth
#print axioms ArkLib.ProximityGap.BridgeB30.mStar_increment_one_of_clean
