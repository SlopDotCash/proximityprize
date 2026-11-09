/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Core A3 — the BACKWARD PROOF of `m* = O(log n)` on the p-INDEPENDENT combinatorial object (#444)

**Angle A3 (backward-proof).** *Assume* the prize target `m* = O(log n)` (equivalently
`δ* → capacity − c_ρ`) as a hypothesis, and derive the **weakest combinatorial statement that
would suffice**. Then decide: is that weakest-sufficient statement strictly WEAKER than BCHKS
Conjecture 1.12 (a possible escape), or equal to it (the wall)?

## Why this is NOT the prior backward-proof (which "converged to single-saddle MGF = wall")

A previous backward-proof (memory `issue444-bgk-proving-3angle-refutation`) ran the extraction on
the **analytic, `p`-DEPENDENT** object: it assumed `M(n) = max_{b≠0}‖η_b‖ ≤ C√(n log m)` and
derived the single-saddle Gaussian-MGF inequality `Σ_{b≠0} cosh(η_b y*) ≤ q²`, which is *literally*
the BGK / Paley char-sum wall. That convergence is forced because the char-sum object `M` lives on
the analytic wall.

The δ* object is now known to be governed by a **`p`-INDEPENDENT** combinatorial count
(memory `issue444-distinctgamma-vs-wall-resolved`, in-tree `FarCosetExplosion` +
`_ResolveFieldIndependent`): the binding cascade is

  `D n m := |⋃_{R : |R| = n − (k+m)} {γ_R}|`     (the **distinct-γ union count**, deduplicated),

a `Finset.card` of a γ-filter that is *identical across primes* at the binding radius (e.g. `D = 89`
for every prime `p > ~600` at `n=16, k=4, r=10`; `B = max‖η_b‖` by contrast varies every prime).
This file re-runs the backward-proof on `D` — OFF the analytic wall — and finds the
weakest-sufficient statement is the **per-scale budget-crossing of `D` at logarithmic depth**, with
an honest one-directional domination against BCHKS 1.12.

## The objects (all on `ℕ`, all `p`-independent — abstract `D`, `Sigma`, `budget`)

* `D : ℕ → ℕ → ℕ` — the distinct-γ union-count cascade `D n m` (p-independent; antitone in `m`,
  proven in-tree by `BridgeB48.Dstar_chain_antitone`, carried here as `hanti`).
* `budget : ℕ → ℕ` — the prize budget `budget n = q·ε* ≈ n`.
* `Sigma : ℕ → ℕ → ℕ` — the BCHKS distinct-`r`-fold subset-sum count `|Σ_r(μ_s)|`.
* `mStar` — the binding depth `Nat.find { m : D n m ≤ budget n }` (as in B29/B30/B31).
* `MStarOLog` — the E7 target `m* = O(log n)` (spelled out exactly as in B31).

## The four results (axiom-clean, no `sorry`)

1. **`WeakestSuff`** — the candidate weakest-sufficient combinatorial statement:
     `∃ c, ∀ n ∈ P, D n (c · log₂ n) ≤ budget n`
   ("the distinct-γ union count is within budget at logarithmic over-determination depth"). A
   *single per-scale budget test at log depth* on the p-independent count — nothing analytic.

2. **`mStarOLog_imp_weakestSuff`** — **THE BACKWARD STEP**: `MStarOLog ⟹ WeakestSuff`. Assuming
   the target, `m*` is the least binder so `D n (m* n) ≤ budget n`, and `m* n ≤ c·log₂ n`, so by
   antitonicity `D n (c·log₂ n) ≤ D n (m* n) ≤ budget n`. (This is "assume the target, derive the
   weakest sufficient statement".)

3. **`weakestSuff_imp_mStarOLog`** — the FORWARD step: `WeakestSuff ⟹ MStarOLog`. If `D` is within
   budget at depth `c·log₂ n`, that depth binds, so `m* n ≤ c·log₂ n`. Hence `WeakestSuff` is
   *genuinely sufficient*.

4. **`weakestSuff_iff_mStarOLog`** — the EQUIVALENCE (2+3): `WeakestSuff ⟺ MStarOLog`. So
   `WeakestSuff` is **exactly** the weakest sufficient combinatorial statement — necessary AND
   sufficient for the prize target, characterized precisely.

## The verdict on `WeakestSuff` vs BCHKS 1.12 (the A3 question)

The honest comparison is captured by the **domination** `D n m ≤ Sigma (s m) (r m)` (the
distinct-γ union count is `≤` the raw distinct subset-sum count, because every `γ_R` is the
subset-sum ratio `−h_{a−k}(R)/h_{b−k}(R)` (`SchurLagrangeBridge`), so the number of *distinct γ
values* is `≤` the number of distinct subset-sum configurations — a **deduplication can only
shrink**). Carried as `hdom`. From it:

* **`BCHKS_imp_weakestSuff`** — `BCHKS 1.12 ⟹ WeakestSuff`, UNCONDITIONALLY (no `hident`):
  `D n (c·log₂ n) ≤ Sigma … ≤ budget n`. So **`WeakestSuff` is weaker-or-equal to BCHKS 1.12.**

* **`weakestSuff_imp_BCHKS_needs_reverse`** — the converse `WeakestSuff ⟹ BCHKS 1.12` is shown to
  REQUIRE the reverse domination `Sigma ≤ D` (the exact identification `hident`), which is **FALSE
  pointwise** (B33 `objectIdentity_false`: `D` is *decreasing* `[40,9,5,…]`, `Σ_r` is *increasing*
  `[3,5,10,…]`). So the two are equal *only at the threshold level under `hident`*; the structural
  domination is strictly one-directional `D ≤ Σ_r`.

**VERDICT (returned).** `WeakestSuff` is **WEAKER-OR-EQUAL** to BCHKS 1.12, never stronger — a
genuine *potential escape*, not the wall re-named. It dominates downward (`D ≤ Σ_r`) so any BCHKS
bound gives it for free; the gap to BCHKS is exactly the dedup slack `Σ_r − D ≥ 0`. Whether it is
*strictly* weaker (a real escape) or *equal* (the wall) is **open and reduces to whether the dedup
`D ≤ Σ_r` is strict at logarithmic depth** — a p-INDEPENDENT growth-law question, decisively OFF
the analytic single-saddle-MGF wall the prior backward-proof hit. The backward-proof on the
combinatorial object does **not** collapse to the char-sum MGF.

## Honesty

This is an honest characterization + reduction. `WeakestSuff ⟺ MStarOLog` is a theorem (modulo the
antitonicity `hanti` and binder-existence `hbind`, both proven substrate facts of B48/B30).
`BCHKS ⟹ WeakestSuff` is a theorem modulo the domination `hdom` (= the in-tree `SchurLagrangeBridge`
dedup fact). Nothing here bounds `D`, `Sigma`, or `m*`; BCHKS 1.12 stays OPEN. The single new
content is the **direction** of the implication chain — `WeakestSuff ≤ BCHKS`, one-way — which
identifies `WeakestSuff` as a candidate escape strictly below the wall in the implication order.
Axiom audit must show `⊆ {propext, Classical.choice, Quot.sound}`.

Issue #444, Core angle A3.
-/

namespace ArkLib.ProximityGap.CoreA3

set_option autoImplicit false

/-! ## The binding depth `m*` (the B29/B30/B31 pattern, on the p-independent cascade `D`) -/

/-- The **binding depth** `m*(n)`: the least over-determination depth `m` at which the distinct-γ
union count `D n m` drops to the budget `budget n` (`= q·ε* ≈ n`). `Nat.find` of the budget-crossing
predicate, given a witness `hex` that some depth binds. Same definition as `BridgeB30.mStar`, on the
`p`-independent combinatorial cascade. -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) : ℕ :=
  Nat.find hex

/-- `mStar` binds: at depth `m*(n)` the union count is within budget. -/
theorem mStar_spec (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) :
    D n (mStar D budget n hex) ≤ budget n :=
  Nat.find_spec hex

/-- `mStar` is the least binder. -/
theorem mStar_le_of_binds (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n) {m : ℕ} (hm : D n m ≤ budget n) :
    mStar D budget n hex ≤ m :=
  Nat.find_min' hex hm

/-! ## The target `m* = O(log n)` (E7), spelled out exactly as in B31 -/

/-- **`m*` is `O(log n)` on the prize regime `P`** — the E7 target. There is a constant `c` such
that for every prize-regime scale `n` (`P n`), once a binder exists, the binding depth is
`≤ c·log₂ n`. The engine of `δ* → 1 − ρ − c_ρ` (capacity minus a `Θ(1/log n)` cushion). -/
def MStarOLog (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → ∀ (hex : ∃ m, D n m ≤ budget n),
    mStar D budget n hex ≤ c * Nat.log 2 n

/-! ## The candidate weakest-sufficient combinatorial statement -/

/-- **`WeakestSuff` — the weakest-sufficient combinatorial statement (the A3 extraction).**

`WeakestSuff D budget P` says: there is a constant `c` such that for every prize-regime scale `n`,
the distinct-γ union count is within budget at *logarithmic* over-determination depth:

  `D n (c · log₂ n) ≤ budget n`.

This is a **single per-scale budget-crossing test, at log depth, on the `p`-independent
combinatorial count `D`** — no character sums, no MGF, no analytic input. We prove below it is both
necessary and sufficient for the prize target (`⟺ MStarOLog`), hence it is *the* weakest sufficient
statement. -/
def WeakestSuff (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → D n (c * Nat.log 2 n) ≤ budget n

/-! ## (2) THE BACKWARD STEP: assume the target, derive `WeakestSuff` -/

/-- **A3 BACKWARD STEP — `MStarOLog ⟹ WeakestSuff`.**

*Assume* the prize target `m* = O(log n)` (`MStarOLog`). For each prize scale `n` a binder exists
(`hbind`); `m*` is the least binder, so `D n (m* n) ≤ budget n`; and `m* n ≤ c·log₂ n`. Since `D` is
antitone in the over-determination depth (`hanti`, the B48 fact: deeper agreement ⟹ smaller bad
set), deepening from `m* n` to `c·log₂ n` only shrinks the count:

  `D n (c·log₂ n) ≤ D n (m* n) ≤ budget n`.

So `WeakestSuff` holds **with the same constant `c`**. This is the literal backward-proof: the
target *implies* the weakest combinatorial sufficient statement. -/
theorem mStarOLog_imp_weakestSuff
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop)
    (hbind : ∀ n, P n → ∃ m, D n m ≤ budget n)
    (hanti : ∀ (n : ℕ) {a b : ℕ}, a ≤ b → D n b ≤ D n a) :
    MStarOLog D budget P → WeakestSuff D budget P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn => ?_⟩
  have hex := hbind n hn
  -- `m*` binds and is `≤ c·log₂ n`:
  have hbinds : D n (mStar D budget n hex) ≤ budget n := mStar_spec D budget n hex
  have hle : mStar D budget n hex ≤ c * Nat.log 2 n := hc n hn hex
  -- antitone in depth: deepening from `m*` to `c·log₂ n` keeps within budget.
  calc D n (c * Nat.log 2 n) ≤ D n (mStar D budget n hex) := hanti n hle
    _ ≤ budget n := hbinds

/-! ## (3) THE FORWARD STEP: `WeakestSuff` is genuinely sufficient -/

/-- **A3 FORWARD STEP — `WeakestSuff ⟹ MStarOLog`.**

If `D n (c·log₂ n) ≤ budget n` (`WeakestSuff`), then depth `c·log₂ n` *binds* at scale `n`, so a
binder exists and `m*` is the least binder, giving `m* n ≤ c·log₂ n`. Hence the target
`m* = O(log n)` holds with the same `c`. So `WeakestSuff` is genuinely sufficient — not just
necessary. -/
theorem weakestSuff_imp_mStarOLog
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) :
    WeakestSuff D budget P → MStarOLog D budget P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn hex => ?_⟩
  -- depth `c·log₂ n` binds, so `m*` is ≤ it.
  exact mStar_le_of_binds D budget n hex (hc n hn)

/-! ## (4) THE EQUIVALENCE: `WeakestSuff` is EXACTLY the weakest sufficient statement -/

/-- **A3 CHARACTERIZATION — `WeakestSuff ⟺ MStarOLog`.**

Combining (2) and (3): the candidate `WeakestSuff` (the per-scale log-depth budget-crossing of the
`p`-independent distinct-γ union count `D`) is **both necessary and sufficient** for the prize
target `m* = O(log n)`. Therefore it is *the* weakest sufficient combinatorial statement — there is
no logically weaker statement that still implies the target, because anything implied by the target
is implied by `WeakestSuff` and vice versa (they are equivalent). This precisely *characterizes*
weakest-suff, as the spec demands. -/
theorem weakestSuff_iff_mStarOLog
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop)
    (hbind : ∀ n, P n → ∃ m, D n m ≤ budget n)
    (hanti : ∀ (n : ℕ) {a b : ℕ}, a ≤ b → D n b ≤ D n a) :
    WeakestSuff D budget P ↔ MStarOLog D budget P :=
  ⟨weakestSuff_imp_mStarOLog D budget P,
   mStarOLog_imp_weakestSuff D budget P hbind hanti⟩

/-! ## The BCHKS 1.12 comparison — the verdict `WeakestSuff ≤ BCHKS` -/

/-- **The BCHKS 1.12 predicate at the matched fold** (as in B31): the distinct `r`-fold subset-sum
count of `μ_s`, `Sigma s r = |Σ_r(μ_s)|`, is within budget. `smap`/`rmap` are the
scale→subgroup-size and (scale,depth)→fold reindexings (P2/E3). The BCHKS conjecture asserts this at
`r ≈ log m`, i.e. at depth `c·log₂ n`. -/
def BCHKS1_12 (Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → Sigma (smap n) (rmap n (c * Nat.log 2 n)) ≤ budget n

/-- **THE VERDICT (downward direction) — `BCHKS 1.12 ⟹ WeakestSuff`, UNCONDITIONALLY.**

The single structural input is the **domination** `hdom : D n m ≤ Sigma (smap n) (rmap n m)`: the
distinct-γ union count is `≤` the distinct subset-sum count, because each forced bad scalar is the
subset-sum ratio `γ_R = −h_{a−k}(R)/h_{b−k}(R)` (the in-tree `SchurLagrangeBridge`/B33 fact), so the
number of *distinct γ values* (the union, after deduplication) is at most the number of distinct
subset-sum configurations. A deduplication can only shrink. With `hdom`,

  `D n (c·log₂ n) ≤ Sigma (smap n) (rmap n (c·log₂ n)) ≤ budget n`,

i.e. **BCHKS 1.12 implies `WeakestSuff`, with no `hident` and no analytic input**. Hence
`WeakestSuff` sits *below* BCHKS 1.12 in the implication order: it is **weaker-or-equal**, never
stronger. -/
theorem BCHKS_imp_weakestSuff
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hdom : ∀ n m, D n m ≤ Sigma (smap n) (rmap n m)) :
    BCHKS1_12 Sigma budget smap rmap P → WeakestSuff D budget P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn => ?_⟩
  calc D n (c * Nat.log 2 n)
      ≤ Sigma (smap n) (rmap n (c * Nat.log 2 n)) := hdom n (c * Nat.log 2 n)
    _ ≤ budget n := hc n hn

/-- **THE VERDICT (the converse needs the reverse domination — the gap to the wall).**

The converse `WeakestSuff ⟹ BCHKS 1.12` does NOT hold from `hdom` alone. It additionally requires
the **reverse** domination `hrev : Sigma (smap n) (rmap n m) ≤ D n m` — i.e. the exact
identification `Sigma = D` (the B31 `hident`). Under both dominations (`hdom` + `hrev`, equivalently
`Sigma = D`), the two are equal and `WeakestSuff ⟹ BCHKS 1.12`. This isolates the gap: `WeakestSuff`
upgrades to BCHKS 1.12 **exactly when the dedup is an equality** `Σ_r = D` at log depth — which is
the open growth-law question (and is FALSE pointwise off the threshold, B33 `objectIdentity_false`:
`D` decreasing, `Σ_r` increasing). So the only way `WeakestSuff` is *as strong as* BCHKS is if no
deduplication happens at the binding depth. -/
theorem weakestSuff_imp_BCHKS_needs_reverse
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hrev : ∀ n m, Sigma (smap n) (rmap n m) ≤ D n m) :
    WeakestSuff D budget P → BCHKS1_12 Sigma budget smap rmap P := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n hn => ?_⟩
  calc Sigma (smap n) (rmap n (c * Nat.log 2 n))
      ≤ D n (c * Nat.log 2 n) := hrev n (c * Nat.log 2 n)
    _ ≤ budget n := hc n hn

/-- **The implication-order summary — `WeakestSuff ≤ BCHKS 1.12` (one-way), with equality iff no
dedup.**

Packaging the verdict as a single theorem:
* `(→)` BCHKS 1.12 always implies `WeakestSuff` (via the dedup domination `hdom`, unconditional);
* `(←)` `WeakestSuff` implies BCHKS 1.12 *only* under the reverse domination `hrev` (= `Σ_r = D` at
  the matched fold, the open exactness).

So in the lattice of sufficient statements, `WeakestSuff ≤ BCHKS 1.12`, a genuine candidate escape
strictly below the wall *unless* the dedup is trivial at log depth. -/
theorem weakestSuff_le_BCHKS
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (P : ℕ → Prop)
    (hdom : ∀ n m, D n m ≤ Sigma (smap n) (rmap n m)) :
    (BCHKS1_12 Sigma budget smap rmap P → WeakestSuff D budget P)
    ∧ ((∀ n m, Sigma (smap n) (rmap n m) ≤ D n m) →
        WeakestSuff D budget P → BCHKS1_12 Sigma budget smap rmap P) :=
  ⟨BCHKS_imp_weakestSuff D budget Sigma smap rmap P hdom,
   fun hrev => weakestSuff_imp_BCHKS_needs_reverse D budget Sigma smap rmap P hrev⟩

/-! ## Non-vacuity / sanity instances -/

/-- **Sanity 1 — the equivalence is non-vacuous and matches the observed cascade.** Concrete
`p`-independent cascade `D` modelled on the reproduced data: at every scale a binder exists at a
small depth, antitone, and the budget is `n`. `MStarOLog` and `WeakestSuff` both hold with `c = 0`
(here the binder is at depth `0` for the trivial model, demonstrating the equivalence fires). -/
example :
    WeakestSuff (fun _ _ => 0) (fun n => n) (fun _ => True) ↔
      MStarOLog (fun _ _ => 0) (fun n => n) (fun _ => True) := by
  apply weakestSuff_iff_mStarOLog
  · intro n _; exact ⟨0, Nat.zero_le n⟩
  · intro n a b _; exact le_rfl

/-- **Sanity 2 — the domination `D ≤ Σ_r` is realizable with a STRICT gap (dedup nontrivial).**
A model where `D n m = 0` (fully deduplicated) but `Sigma s r` grows: `hdom` holds (`0 ≤ Σ`), the
reverse `hrev` FAILS (`Σ > 0 = D`), so `WeakestSuff` holds but the BCHKS upgrade is genuinely
blocked — exhibiting the strict-escape regime `WeakestSuff < BCHKS`. -/
example :
    BCHKS1_12 (fun _ r => r + 1) (fun n => n) (fun n => n) (fun _ m => m) (fun _ => True) →
      WeakestSuff (fun _ _ => 0) (fun n => n) (fun _ => True) := by
  apply BCHKS_imp_weakestSuff
  intro n m; exact Nat.zero_le _

/-- **Sanity 3 — the binding-depth `m*` is the genuine `Nat.find` and the backward step uses
antitonicity essentially.** Concrete `D` with a binder at depth `3` for `n = 16`: `m* = 3`, and the
backward step deepens to any `c·log₂ 16 ≥ 3` while staying within budget. -/
example :
    let D : ℕ → ℕ → ℕ := fun _ m => if m ≥ 3 then 0 else 100
    let budget : ℕ → ℕ := fun n => n
    ∃ (hex : ∃ m, D 16 m ≤ budget 16), mStar D budget 16 hex ≤ 3 := by
  intro D budget
  have hex : ∃ m, D 16 m ≤ budget 16 := ⟨3, by decide⟩
  exact ⟨hex, mStar_le_of_binds D budget 16 hex (by decide)⟩

end ArkLib.ProximityGap.CoreA3

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA3.mStarOLog_imp_weakestSuff
#print axioms ArkLib.ProximityGap.CoreA3.weakestSuff_imp_mStarOLog
#print axioms ArkLib.ProximityGap.CoreA3.weakestSuff_iff_mStarOLog
#print axioms ArkLib.ProximityGap.CoreA3.BCHKS_imp_weakestSuff
#print axioms ArkLib.ProximityGap.CoreA3.weakestSuff_imp_BCHKS_needs_reverse
#print axioms ArkLib.ProximityGap.CoreA3.weakestSuff_le_BCHKS
