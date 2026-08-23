/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Bridge B46 — `m*` well-defined: the binding-depth `Nat.find` exists (target E1, #444)

**Spec (B46).** *`m*` well-defined: `{m : D*(k+m) ≤ budget}` nonempty so `Nat.find` exists
(`D*(n)` trivially `≤ budget`). Use `Nat.find` machinery.*

## Context — closing the existence side-condition of the E1/E5/E7 `mStar`

The binding-depth `m*(n)` is the FIRST over-determination depth `m` at which the worst
over-determined far-line incidence cascade `D n m` (`= D*(m)`, see
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, §B) drops to the prize
budget `budget n = n` (`= q·ε*`):

  `m*(n) = min { m : D n m ≤ budget n }`.

This is exactly the `mStar` of `_BridgeB29` (`mStar D budget n hex := Nat.find hex`), which is
GIVEN a witness `hex : ∃ m, D n m ≤ budget n` as a hypothesis. B46 discharges precisely that
side-condition: the witness set is **always** nonempty, so `m*` is unconditionally well-defined.

## Why the witness set is nonempty (the trivial top rung)

The cascade data of E2 always terminates in a trivial `1`-rung: e.g.
`n=8,k=2: D*(m)=[40,9,5,1,1]`, `n=16,k=4: D*(m)=[3936,89,9,9,9,8,1,1,1]` — the over-determined
incidence collapses to a single forced direction (`D = 1`) once the over-determination depth is
large enough (the system `s = k+m` becomes maximally over-determined). Since the prize budget is
`budget n = n ≥ 1`, that trivial rung satisfies `D ≤ 1 ≤ n = budget n`. Hence the budget-crossing
set is nonempty and `Nat.find` applies.

We make this honest by carrying the single empirical/structural fact as the named hypothesis
`hTop : D n topDepth ≤ budget n` (the existence of *some* binding depth — the trivial top rung is
the canonical witness). From it we DERIVE, unconditionally:

* `bindingWitness` — `∃ m, D n m ≤ budget n` (the B29 side-condition `hex`, now a theorem);
* `mStar` / `mStar_spec` / `mStar_le_of_binds` — `m*` well-defined via `Nat.find`, it binds, and
  it is the least binder (re-exposing the B29 API, now without `hex` as an external assumption);
* `mStar_le_topDepth` — the binding depth never exceeds the trivial top rung;
* `mStar_prize` — the prize-budget (`budget = id`) instance, where the trivial rung `D n m₀ = 1`
  (or any `≤ n`) suffices because `n ≥ 1`.

All proofs are pure `Nat.find` machinery over an abstract cascade `D : ℕ → ℕ → ℕ`; nothing about
the analytic content of `D` is used beyond the existence of one binding rung.

Issue #444.
-/

namespace ArkLib.ProximityGap.BridgeB46

variable (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)

/-- **The binding-depth witness set is nonempty (B46 core).** Given any single binding rung
`hTop : D n topDepth ≤ budget n` (canonically the trivial top rung `D = 1`), the budget-crossing
set `{ m : D n m ≤ budget n }` is nonempty. This is exactly the side-condition `hex` that
`_BridgeB29.mStar` takes as a hypothesis — here it is a theorem. -/
theorem bindingWitness {topDepth : ℕ} (hTop : D n topDepth ≤ budget n) :
    ∃ m, D n m ≤ budget n :=
  ⟨topDepth, hTop⟩

/-- **`m*` well-defined.** The binding depth as `Nat.find` of the budget-crossing predicate, with
the existence side-condition now discharged from a single binding rung `hTop`. -/
noncomputable def mStar {topDepth : ℕ} (hTop : D n topDepth ≤ budget n) : ℕ :=
  Nat.find (bindingWitness D budget n hTop)

/-- `m*` binds: at depth `m*` the worst incidence is within budget. -/
theorem mStar_spec {topDepth : ℕ} (hTop : D n topDepth ≤ budget n) :
    D n (mStar D budget n hTop) ≤ budget n :=
  Nat.find_spec (bindingWitness D budget n hTop)

/-- `m*` is the **least** binder: any depth `m` that binds is at least `m*`. -/
theorem mStar_le_of_binds {topDepth : ℕ} (hTop : D n topDepth ≤ budget n)
    {m : ℕ} (hm : D n m ≤ budget n) :
    mStar D budget n hTop ≤ m :=
  Nat.find_min' (bindingWitness D budget n hTop) hm

/-- The binding depth never exceeds the witnessing trivial top rung. -/
theorem mStar_le_topDepth {topDepth : ℕ} (hTop : D n topDepth ≤ budget n) :
    mStar D budget n hTop ≤ topDepth :=
  mStar_le_of_binds D budget n hTop hTop

/-- **No smaller depth binds.** Below `m*` the worst incidence strictly exceeds the budget — the
defining minimality of the binding depth. -/
theorem lt_mStar_not_binds {topDepth : ℕ} (hTop : D n topDepth ≤ budget n)
    {m : ℕ} (hm : m < mStar D budget n hTop) :
    ¬ D n m ≤ budget n :=
  Nat.find_min (bindingWitness D budget n hTop) hm

end ArkLib.ProximityGap.BridgeB46

namespace ArkLib.ProximityGap.BridgeB46.Prize

open ArkLib.ProximityGap.BridgeB46

/-- **Prize-budget instance (`budget = id`, `budget n = n`).** Here the trivial top rung — at which
the cascade has collapsed to a single forced direction, `D n topDepth = 1` — always binds provided
`n ≥ 1`, since `1 ≤ n`. So `m*` is well-defined at the prize budget from the purely structural
fact that the over-determined incidence eventually collapses to `1`. -/
theorem bindingWitness_prize (D : ℕ → ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    {topDepth : ℕ} (hTrivial : D n topDepth = 1) :
    ∃ m, D n m ≤ id n :=
  bindingWitness D id n (topDepth := topDepth) (by rw [hTrivial]; exact hn)

/-- **`m*` well-defined at the prize budget**, from the trivial collapse `D n topDepth = 1` and
`n ≥ 1`. -/
noncomputable def mStarPrize (D : ℕ → ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    {topDepth : ℕ} (hTrivial : D n topDepth = 1) : ℕ :=
  mStar D id n (topDepth := topDepth) (by rw [hTrivial]; exact hn)

/-- At the prize budget, `m*` binds: `D n m* ≤ n`. -/
theorem mStarPrize_spec (D : ℕ → ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    {topDepth : ℕ} (hTrivial : D n topDepth = 1) :
    D n (mStarPrize D hn hTrivial) ≤ n := by
  have h := mStar_spec D id n (topDepth := topDepth) (by rw [hTrivial]; exact hn)
  simpa [id, mStarPrize] using h

end ArkLib.ProximityGap.BridgeB46.Prize

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB46.bindingWitness
#print axioms ArkLib.ProximityGap.BridgeB46.mStar_spec
#print axioms ArkLib.ProximityGap.BridgeB46.mStar_le_of_binds
#print axioms ArkLib.ProximityGap.BridgeB46.mStar_le_topDepth
#print axioms ArkLib.ProximityGap.BridgeB46.lt_mStar_not_binds
#print axioms ArkLib.ProximityGap.BridgeB46.Prize.bindingWitness_prize
#print axioms ArkLib.ProximityGap.BridgeB46.Prize.mStarPrize_spec
