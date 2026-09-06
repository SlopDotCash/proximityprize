/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Bridge B31 — `m* = O(log n) ⟺ BCHKS Conjecture 1.12` (target E7, #444)

**Spec.** Name the reduction `m* = O(log n) ⟺ BCHKS Conjecture 1.12` (distinct `r`-fold
subset-sum count `|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m`).
**Approach.** Identify `D*(m)` with the distinct `r`-fold subset-sum count, then state the
equivalence as a `Prop` and prove it as a clean `Nat.find` reduction.

## Context (the empirical formula E7)

The δ* bridge program (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`)
writes `D n m` for the *worst over-determined far-line incidence at scale `n` and
over-determination depth `m`* — the binding cascade `D*(m)` (§B, E2), the same object the
substrate `OrbitCountCrossingLaw.crossing_law` and `OpenCoreConditionalPin.WorstCaseIncidenceBounded`
govern. The **binding depth** is

  `m*(n) = min { m : D n m ≤ budget n }`,    prize budget `budget n = q·ε* ≈ n`.

The master gap identity E1, `δ* = 1 − ρ − (m*−1)/n`, turns a bound on `m*` into a bound on `δ*`,
so the prize E7 is `m* = O(log n)` (equivalently `δ* → 1−ρ−c_ρ`).

E7 is asserted ⟺ **BCHKS Conjecture 1.12**: the *distinct `r`-fold subset-sum count* of the
smooth subgroup `μ_s`, `|Σ_r(μ_s)|`, is `≤ q·ε*` at `r ≈ log m`. By P2/E3 the far-line incidence
`D n m` **is** that subset-sum count (the bad-α set of a monomial pencil over `μ_n` is a union of
`r`-fold subset-sum classes); the over-determination depth `m` is the subset-sum fold `r` after a
scale-dependent index/fold reindexing `(smap n, rmap n)`. Under that identification the budget
test `D n m ≤ budget n` is *literally* the BCHKS bound `|Σ_r(μ_s)| ≤ q·ε*`, so the two
*asymptotic* statements coincide. This file makes that coincidence a theorem.

## What is proved here (axiom-clean, no `sorry`)

The reduction is a `Nat.find` characterization, parametric in the (abstract) cascade `D`, budget,
and the BCHKS subset-sum count `Sigma`, plus the **identification** `D n m = Sigma (smap n)
(rmap n m)` (the P2/E3 bridge, carried as an explicit hypothesis — it is the empirical input the
spec names, not a thing this brick proves).

* `mStar` — the binding depth `Nat.find { m : D n m ≤ budget n }` (given a binder witness).
* `BCHKSBudget` — the BCHKS 1.12 predicate at `(s, r)`: `Sigma s r ≤ budget`, i.e.
  `|Σ_r(μ_s)| ≤ q·ε*`.
* `mStar_le_iff_BCHKS` — **the per-scale reduction**: under the identification,
    `m*(n) ≤ M  ⟺  ∃ m ≤ M, BCHKSBudget Sigma (smap n) (rmap n m) (budget n)`,
  i.e. "the cascade binds by depth `M`" *is* "the BCHKS bound holds at some matched fold
  `r = rmap n m ≤ rmap n M`".
* `mStar_le_iff_BCHKS_mono` — under cascade monotonicity (E4 decay) the `∃ m ≤ M` collapses to
  the single bound at `m = M`: `m*(n) ≤ M ⟺ BCHKSBudget at fold rmap n M`. This is the literal
  "`r ≈ log m`" form (one fold per scale).
* `mStarOLog_iff_BCHKS1_12` — **THE E7 ⟺ BCHKS 1.12 reduction, as a named equivalence**:
    `(m* = O(log n) on the prize regime)  ⟺  (BCHKS 1.12 holds at r ≈ log m on the prize regime)`,
  with both sides spelled out as explicit `Prop`s.

## Honest scope (what is NOT proved)

This is an honest **reduction**, not a closure. The single non-trivial input is the
identification `hident : ∀ m, D n m = Sigma (smap n) (rmap n m)` — the P2/E3 claim that the
far-line incidence *is* the distinct `r`-fold subset-sum count. That identification is carried as
an explicit hypothesis (the bridge the spec asks to *name*), and BCHKS Conjecture 1.12 itself is
of course OPEN. What is a theorem is the equivalence: *granting the identification*, the
asymptotic statement `m* = O(log n)` and BCHKS 1.12 (`|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m`) are the
same statement. Nothing here bounds `m*` or `|Σ_r|`.
-/

namespace ArkLib.ProximityGap.BridgeB31

/-! ## The binding depth `m*` -/

/-- The **binding depth** `m*(n)`: the least over-determination depth `m` at which the worst
far-line incidence `D n m` drops to the budget `budget n` (`= q·ε* ≈ n`). `Nat.find` of the
budget-crossing predicate, given a witness `hex` that some depth binds. -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) : ℕ :=
  Nat.find hex

/-! ## The BCHKS Conjecture 1.12 predicate -/

/-- **The BCHKS Conjecture 1.12 predicate at `(s, r)`.**

`BCHKSBudget Sigma s r B` says the *distinct `r`-fold subset-sum count* of the smooth subgroup
`μ_s`, `|Σ_r(μ_s)| = Sigma s r`, is within budget `B = q·ε*`:

  `|Σ_r(μ_s)| ≤ q·ε*`.

This is BCHKS Conjecture 1.12 evaluated at a single `(s, r)`. The whole conjecture asserts it at
`r ≈ log m` (equivalently `r ≈ log s`), the depth where the subset-sum count first drops to the
budget. The object `Sigma s r` is `p`-INDEPENDENT (a combinatorial subset-sum count over `μ_s`),
off the analytic BGK char-sum wall — but OPEN. -/
def BCHKSBudget (Sigma : ℕ → ℕ → ℕ) (s r B : ℕ) : Prop :=
  Sigma s r ≤ B

/-! ## The per-scale reduction -/

/-- **The per-scale reduction (E2/E3 ⟹ the budget-crossing identity).**

Under the **identification** `hident : ∀ m, D n m = Sigma (smap n) (rmap n m)` — the P2/E3 bridge
that the far-line incidence at depth `m` *is* the distinct `r`-fold subset-sum count of `μ_{smap n}`
at fold `r = rmap n m` — the cascade binds by depth `M` iff the BCHKS bound holds at some matched
fold `r = rmap n m`, `m ≤ M`:

  `m*(n) ≤ M  ⟺  ∃ m ≤ M, |Σ_{rmap n m}(μ_{smap n})| ≤ budget n`.

Pure `Nat.find_le_iff` rewritten through the identification. -/
theorem mStar_le_iff_BCHKS
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔
      ∃ m ≤ M, BCHKSBudget Sigma (smap n) (rmap n m) (budget n) := by
  unfold mStar BCHKSBudget
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨m, hmM, hbind⟩
    exact ⟨m, hmM, by rw [← hident]; exact hbind⟩
  · rintro ⟨m, hmM, hbound⟩
    exact ⟨m, hmM, by rw [hident]; exact hbound⟩

/-- **The monotone (E4-decay) form of the per-scale reduction.**

When the cascade is non-increasing in depth (the E4 geometric decay `D*(1) ≈ n³ → … → budget`),
the budget-crossing predicate is upward-closed, so `∃ m ≤ M` collapses to the single bound at
`m = M`. Under the identification this is the literal **"`r ≈ log m`"** form — one matched fold
`r = rmap n M` per scale:

  `m*(n) ≤ M  ⟺  |Σ_{rmap n M}(μ_{smap n})| ≤ budget n`. -/
theorem mStar_le_iff_BCHKS_mono
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m))
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a) (M : ℕ) :
    mStar D budget n hex ≤ M ↔ BCHKSBudget Sigma (smap n) (rmap n M) (budget n) := by
  rw [mStar_le_iff_BCHKS D budget Sigma smap rmap n hex hident M]
  unfold BCHKSBudget
  constructor
  · rintro ⟨m, hmM, hbound⟩
    -- decay: `D n M ≤ D n m`, and by identification both sides are `Sigma`-values.
    rw [← hident]
    calc D n M ≤ D n m := hmono hmM
      _ = Sigma (smap n) (rmap n m) := hident m
      _ ≤ budget n := hbound
  · intro hbound
    exact ⟨M, le_rfl, hbound⟩

/-! ## THE E7 ⟺ BCHKS 1.12 reduction -/

/-- **`m*` is `O(log n)` on the prize regime `P`** — the E7 statement spelled out.

`MStarOLog D budget P` says: there is a constant `c` such that for every scale `n` in the prize
regime (`P n`, e.g. `n = 2^μ`, `q = n^β`, `budget n ≈ n`), once a binder exists, the binding
depth is `≤ c · log₂ n`. This is exactly `m* = O(log n)` (E7), the engine of `δ* → 1−ρ−c_ρ`. -/
def MStarOLog (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → ∀ (hex : ∃ m, D n m ≤ budget n),
    mStar D budget n hex ≤ c * Nat.log 2 n

/-- **BCHKS Conjecture 1.12 on the prize regime `P`, via the identification** — the right-hand
side of the E7 reduction, spelled out.

`BCHKS1_12 Sigma budget smap rmap P` says: there is a constant `c` such that for every scale `n`
in the prize regime, the BCHKS bound `|Σ_r(μ_{smap n})| ≤ budget n` holds at *some* matched fold
`r = rmap n m` with `m ≤ c · log₂ n` — i.e. **the distinct `r`-fold subset-sum count drops to the
budget at `r ≈ log m`** (depth `≈ log₂ n`). This is the BCHKS Conjecture 1.12 assertion. -/
def BCHKS1_12 (Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n →
    ∃ m ≤ c * Nat.log 2 n, BCHKSBudget Sigma (smap n) (rmap n m) (budget n)

/-- **B31 — the E7 ⟺ BCHKS 1.12 reduction, as a named equivalence.**

Granting the identification `hident` (P2/E3: the far-line incidence cascade `D n m` *is* the
distinct `r`-fold subset-sum count `|Σ_{rmap n m}(μ_{smap n})|`) on every prize-regime scale, and
that a binder exists at each such scale, the two asymptotic statements coincide:

  `m* = O(log n)`  (E7)   ⟺   `|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m`  (BCHKS Conjecture 1.12).

The same constant `c` witnesses both directions (the depth bound `c·log₂ n` is the fold bound).
This is the honest *naming of the reduction* the spec asks for: the prize E7 and BCHKS 1.12 are,
modulo the explicit far-line-incidence ⇄ subset-sum identification, **literally the same
conjecture**. -/
theorem mStarOLog_iff_BCHKS1_12
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hbind : ∀ n, P n → ∃ m, D n m ≤ budget n)
    (hident : ∀ n, P n → ∀ m, D n m = Sigma (smap n) (rmap n m)) :
    MStarOLog D budget P ↔ BCHKS1_12 Sigma budget smap rmap P := by
  unfold MStarOLog BCHKS1_12
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n hn => ?_⟩
    -- a binder exists here, so `m*` is defined, and `m* ≤ c·log₂ n`.
    have hex := hbind n hn
    have hle : mStar D budget n hex ≤ c * Nat.log 2 n := hc n hn hex
    -- turn the depth bound into the BCHKS bound at a matched fold via the per-scale reduction.
    exact (mStar_le_iff_BCHKS D budget Sigma smap rmap n hex (hident n hn)
      (c * Nat.log 2 n)).1 hle
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n hn hex => ?_⟩
    -- the BCHKS bound at a matched fold ≤ `c·log₂ n` gives the depth bound via the same reduction.
    exact (mStar_le_iff_BCHKS D budget Sigma smap rmap n hex (hident n hn)
      (c * Nat.log 2 n)).2 (hc n hn)

/-- **Sanity / non-vacuity.**  The reduction is realizable: a degenerate instance where the
cascade is the constant-`0` identification (`D = 0`, `Sigma = 0`, every scale binds at depth `0`),
the prize regime is all-of-`ℕ`, and both sides of the E7 ⟺ BCHKS equivalence hold with `c = 0`. -/
example :
    MStarOLog (fun _ _ => 0) (fun _ => 0) (fun _ => True) ↔
      BCHKS1_12 (fun _ _ => 0) (fun _ => 0) (fun n => n) (fun _ m => m) (fun _ => True) := by
  apply mStarOLog_iff_BCHKS1_12
  · intro n _; exact ⟨0, le_rfl⟩
  · intro n _ m; rfl

end ArkLib.ProximityGap.BridgeB31

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.BridgeB31.mStar_le_iff_BCHKS
#print axioms ArkLib.ProximityGap.BridgeB31.mStar_le_iff_BCHKS_mono
#print axioms ArkLib.ProximityGap.BridgeB31.mStarOLog_iff_BCHKS1_12
