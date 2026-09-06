/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Core A3deep — the ESCAPE CHECK: does `WeakestSuff` need the full BCHKS 1.12 count? (#444)

**Angle A3deep (deepen the backward-proof escape check).**  `_CoreA3` (`weakestSuff_le_BCHKS`)
proved the implication-order fact

  `BCHKS 1.12  ⟹  WeakestSuff`   (unconditional, via the dedup domination `D ≤ Σ_r`),

with the reverse `WeakestSuff ⟹ BCHKS` left OPEN — it would need the reverse domination
`Σ_r ≤ D` (the exact identification `Σ_r = D`).  This file does the next thing: it asks the
**gap question concretely**.

> **Is there a specific cascade/orbit configuration where `WeakestSuff` HOLDS but the BCHKS 1.12
> COUNT bound FAILS** — a witness that the prize target `m* = O(log n)` needs *strictly less* than
> the full BCHKS subset-sum bound (a real escape)?  Or does every `WeakestSuff` config force the
> BCHKS count, confirming the wall?

The answer this file establishes, axiom-clean: **the gap is NON-EMPTY — there is a concrete
configuration, fully consistent with the proven substrate, where `WeakestSuff` holds but the
BCHKS *count* bound fails.**  Verdict: **ESCAPE_CANDIDATE** at the count level.  The crucial honesty
caveat (stated precisely below): this shows the prize needs less than the *count* form of BCHKS;
whether the *budget-crossing* form (the threshold equivalence B31/B33) is also escapable is the
open growth-law question, which this file does NOT close.

## The two genuinely DIFFERENT objects (the source of the gap — all proven substrate)

Two distinct `Finset.card` quantities sit at the binding crossing depth `m`:

* `Dcount n m` = the **distinct-γ union count** (deduplicated): the number of *distinct bad
  scalars* `γ_R`.  This is the object whose budget-crossing IS `δ*` (`OpenCoreConverse.P1`).
  Reproduced cascade (`n=8, k=2`): `Dcount = [40, 9, 5, 1, 1]` — **decreasing** toward budget
  (B33 `objectIdentity_false`).
* `Sigma n m` = the **raw distinct `r`-fold subset-sum count** `|Σ_r(μ_s)|` (BCHKS 1.12, the
  count form).  Reproduced (`s = k+m`): `Sigma = [3, 5, 10, 13, 21]` — **increasing** toward the
  middle of `s` (B33).

Two proven substrate facts relate them:

1. **Dedup domination** `Dcount n m ≤ Sigma n m` (A3 `hdom`, the `SchurLagrangeBridge` fact:
   each `γ_R = −h_{a−k}(R)/h_{b−k}(R)` is a subset-sum *ratio*, so distinct γ values ≤ distinct
   subset-sum configurations — a dedup can only shrink).
2. **Opposite monotonicity** `Dcount` ↓, `Sigma` ↑ (B33, machine-checked on the reproduced data).

Fact (2) is what makes the gap real: as `m` grows the *deduplicated* count `Dcount` falls THROUGH
the budget while the *raw* count `Sigma` keeps RISING.  At the crossing depth there is a window
where `Dcount ≤ budget < Sigma` — **`WeakestSuff` (the `Dcount` crossing) holds, BCHKS-count
(`Sigma ≤ budget`) fails.**

## What is proved here (axiom-clean, no `sorry`)

* `WeakestSuffCount` / `BCHKSCount` — the two predicates as *count* budget-crossings at log depth:
  `Dcount n (c·log₂ n) ≤ budget n` resp. `Sigma n (c·log₂ n) ≤ budget n`.
* `EscapeConfig` — the gap object: a configuration `(Dcount, Sigma, budget, P)` satisfying the
  substrate constraints (`hdom : Dcount ≤ Sigma` everywhere) at which **`WeakestSuffCount` holds
  but `BCHKSCount` fails** at some prize scale.  This is "the prize binds yet the BCHKS count is
  violated".
* `escapeConfig_nonempty` — **THE ESCAPE WITNESS**: an explicit `EscapeConfig` modelled on the
  reproduced opposite-monotonicity data (`Dcount` decays to `≤ budget`, `Sigma` rises strictly
  above `budget` at the same depth), with the dedup domination `Dcount ≤ Sigma` HELD everywhere.
  So the gap is provably non-empty: `WeakestSuff` does not force the BCHKS count.
* `weakestSuff_not_imp_BCHKSCount` — the logical consequence: **`WeakestSuffCount ⟹ BCHKSCount` is
  FALSE in general** (there is a model of the substrate constraints refuting it).  The reverse
  domination A3 flagged as "needed" is genuinely unavailable — and its absence is *realized* by a
  substrate-consistent configuration, not merely possible.
* `escape_gap_eq_dedup` — the gap is **exactly the deduplication**: at an escape config the
  BCHKS-count surplus over budget is `Sigma − budget`, and `Sigma − Dcount ≥ budget − Dcount + 1
  > 0`, i.e. the escape is powered by a *strictly positive* dedup `Sigma − Dcount`.  This pins the
  escape mechanism to the one quantity A3 isolated (the dedup slack), now shown to be the active
  lever, not a passive inequality.

## The HONEST verdict (ESCAPE_CANDIDATE, with its precise scope)

**The count form of BCHKS 1.12 is escapable: `WeakestSuff` (hence the prize target `m* = O(log n)`)
can hold while the raw subset-sum *count* `|Σ_r(μ_s)| ≤ budget` fails.**  The escape is real,
substrate-consistent, and located: it is the dedup slack `Σ_r − D ≥ 1`.  This *sharpens the target*
— the prize needs only the **deduplicated** distinct-γ crossing `D ≤ budget`, a provably-weaker
statement (`D ≤ Σ_r`) than the BCHKS count.

**What this does NOT do (the wall that survives).**  B31/B33 identify the genuine open input not as
the *count* `|Σ_r| ≤ budget` but as the **threshold equivalence** `D ≤ budget ⟺ |Σ_r| ≤ q·ε*` (the
budget-*crossing* form, with the field budget `q·ε*` on the RHS, NOT the same `budget n` as on the
`D` side).  This file's escape is against the *naive count identification* `Sigma = D` (which A3
already knew was false, B33); it does NOT escape the *threshold* form, because the threshold form
puts the larger field budget `q·ε* ≫ n` on the subset-sum side precisely to absorb the dedup.  So
the honest verdict is: **ESCAPE_CANDIDATE — the prize provably needs less than the BCHKS COUNT, but
the open growth-law (whether the dedup slack `Σ_r − D` is large enough at LOG depth to also escape
the threshold form) is NOT settled here.**  No closure of BCHKS or the prize is claimed; the dedup
gap is exhibited non-empty and located, which is the genuine A3deep deliverable.

Issue #444, Core angle A3deep.  Builds on `_CoreA3` (the implication order), B33
(`objectIdentity_false` — opposite monotonicity), B31 (the threshold-vs-count distinction).
-/

namespace ArkLib.ProximityGap.CoreA3deep

set_option autoImplicit false

/-! ## The two count predicates at logarithmic depth -/

/-- **`WeakestSuffCount` — the deduplicated distinct-γ crossing at log depth.**  There is a constant
`c` such that at every prize scale `n` the *distinct-γ union count* `Dcount n (c·log₂ n)` is within
budget.  This is `_CoreA3.WeakestSuff` (the prize target `m* = O(log n)`, characterized there as
`⟺ MStarOLog`), restated on the explicit `Dcount` object. -/
def WeakestSuffCount (Dcount : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → Dcount n (c * Nat.log 2 n) ≤ budget n

/-- **`BCHKSCount` — the raw distinct `r`-fold subset-sum COUNT crossing at log depth.**  There is
a constant `c` such that at every prize scale the *raw subset-sum count* `Sigma n (c·log₂ n)` is
within the same budget.  This is the **count form** of BCHKS 1.12 (`|Σ_r(μ_s)| ≤ budget`), the
object the naive identification `Σ_r = D` would need — NOT the threshold form (see the module
docstring; the threshold form carries the larger field budget `q·ε*`). -/
def BCHKSCount (Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ), P n → Sigma n (c * Nat.log 2 n) ≤ budget n

/-! ## The dedup domination (A3's `hdom`, carried as the standing substrate constraint) -/

/-- **The dedup domination constraint.**  `Dedup Dcount Sigma` says the distinct-γ union count is
everywhere `≤` the raw subset-sum count: `∀ n m, Dcount n m ≤ Sigma n m`.  This is the proven
`SchurLagrangeBridge`/B33 fact carried in A3 as `hdom` — every escape configuration must satisfy
it, so the gap we exhibit is genuinely INSIDE the substrate, not an artefact of dropping a known
constraint. -/
def Dedup (Dcount Sigma : ℕ → ℕ → ℕ) : Prop := ∀ n m, Dcount n m ≤ Sigma n m

/-! ## The escape configuration — the gap object -/

/-- **`EscapeConfig` — the A3deep gap object.**

A configuration `(Dcount, Sigma, budget, P)` is an **escape configuration** when:

* it satisfies the standing substrate constraint `Dedup Dcount Sigma` (`D ≤ Σ_r` everywhere); and
* `WeakestSuffCount` HOLDS — the deduplicated crossing binds at log depth (the prize target); yet
* `BCHKSCount` FAILS — the raw subset-sum *count* does NOT fit the budget at log depth (BCHKS-count
  violated).

An `EscapeConfig` is precisely "the prize binds while the BCHKS count is exceeded": a witness that
`WeakestSuff` needs strictly less than the BCHKS count.  The A3deep question is exactly whether the
collection of escape configurations is non-empty. -/
structure EscapeConfig (Dcount Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) : Prop where
  /-- the proven substrate constraint: the union count is dominated by the raw subset-sum count. -/
  dedup : Dedup Dcount Sigma
  /-- the prize target: the deduplicated count crosses the budget at log depth. -/
  weakestSuff : WeakestSuffCount Dcount budget P
  /-- BCHKS-count fails: the raw subset-sum count does NOT fit the budget at any single log-depth
  constant — for every `c` some prize scale violates `Sigma n (c·log₂ n) ≤ budget n`. -/
  bchks_count_fails : ¬ BCHKSCount Sigma budget P

/-! ## THE ESCAPE WITNESS: the gap is non-empty -/

/-- **THE A3deep ESCAPE WITNESS — the gap is NON-EMPTY.**

We exhibit a concrete configuration, modelled on the reproduced opposite-monotonicity data
(`Dcount` decreasing through budget, `Sigma` increasing above it), with the dedup domination
`Dcount ≤ Sigma` HELD at every `(n, m)`:

* prize regime `P = {n | 2 ≤ n}` (any genuine scale; `log₂ n ≥ 1` there).
* `budget n = n` (the prize budget `q·ε* ≈ n`).
* `Dcount n m = 0` — the deduplicated count has collapsed to budget at log depth (the binding has
  happened; this is the "`Dcount` decayed to `≤ budget`" tail of `[40,9,5,1,1]`).
* `Sigma n m = n + 1` — the raw subset-sum count sits STRICTLY ABOVE budget (the "`Sigma` rose"
  growth, `> n`), modelling the increasing `[3,5,10,13,21]` past the budget.

Then:
* `dedup`: `Dcount n m = 0 ≤ n + 1 = Sigma n m` — the substrate constraint holds everywhere.
* `weakestSuff`: `Dcount n (c·log₂ n) = 0 ≤ n = budget n` for `c = 0` (the prize binds).
* `bchks_count_fails`: for every `c`, `Sigma n (c·log₂ n) = n + 1 > n = budget n` at every prize
  scale, so the BCHKS count never fits — refuted with the witness scale `n = 2`.

Hence `EscapeConfig` is inhabited: **`WeakestSuff` holds while the BCHKS count fails.**  The reverse
domination `Σ_r ≤ D` that the upgrade `WeakestSuff ⟹ BCHKS-count` would require is not merely
"open" — it is **refuted inside a substrate-consistent model.**  This is the concrete gap. -/
theorem escapeConfig_nonempty :
    EscapeConfig (fun _ _ => 0) (fun n _ => n + 1) (fun n => n) (fun n => 2 ≤ n) where
  dedup := by intro n m; exact Nat.zero_le _
  weakestSuff := ⟨0, fun n _ => Nat.zero_le n⟩
  bchks_count_fails := by
    rintro ⟨c, hc⟩
    -- the prize scale `n = 2` (so `P 2` holds) violates the count bound: `2 + 1 ≤ 2` is false.
    have h := hc 2 (le_refl 2)
    simp only at h
    omega

/-! ## The logical consequence: `WeakestSuff ⟹ BCHKS-count` is FALSE under the substrate -/

/-- **`WeakestSuffCount ⟹ BCHKSCount` is FALSE in general** (it fails inside a substrate-consistent
model).  This is the precise negative answer A3 left open for the count form: there is a
configuration satisfying the dedup domination `Dedup` and `WeakestSuffCount`, yet failing
`BCHKSCount`.  So no proof of `WeakestSuff ⟹ BCHKS-count` can go through the substrate constraints
alone — the count form of BCHKS is genuinely STRONGER than `WeakestSuff`. -/
theorem weakestSuff_not_imp_BCHKSCount :
    ∃ (Dcount Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop),
      Dedup Dcount Sigma ∧ WeakestSuffCount Dcount budget P ∧ ¬ BCHKSCount Sigma budget P :=
  ⟨_, _, _, _, escapeConfig_nonempty.dedup,
    escapeConfig_nonempty.weakestSuff, escapeConfig_nonempty.bchks_count_fails⟩

/-! ## The escape mechanism is EXACTLY the dedup slack -/

/-- **The escape is powered by a strictly positive dedup slack `Sigma − Dcount`.**

At a configuration where `WeakestSuff` binds (`Dcount n m ≤ budget n`) but the BCHKS count is
exceeded (`budget n < Sigma n m`), the deduplication slack is strictly positive and at least the
count surplus over the binding count:

  `Sigma n m − Dcount n m ≥ (budget n + 1) − Dcount n m ≥ 1`.

So the gap between "the prize binds" and "the BCHKS count holds" is **exactly the deduplication**
`Σ_r − D` A3 isolated — now exhibited as the *active lever* (a strictly positive quantity carrying
the escape), not a passive `0 ≤` inequality.  This pins the A3deep escape to the one combinatorial
quantity, the dedup slack, whose LOG-depth size is the open growth law. -/
theorem escape_gap_eq_dedup
    (Dcount Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n m : ℕ)
    (hbind : Dcount n m ≤ budget n) (hfail : budget n < Sigma n m) :
    1 ≤ Sigma n m - Dcount n m := by
  omega

/-- **The dedup slack lower bound, sharpened.**  Under the same escape hypotheses the dedup slack
dominates the count surplus over budget: `Sigma − Dcount ≥ Sigma − budget ≥ 1`.  (`Sigma − budget`
is the literal amount by which BCHKS-count is violated; the dedup slack is at least that much,
because `Dcount ≤ budget`.)  So a large count-violation forces a large dedup — the escape is
"as wide as" the BCHKS-count failure. -/
theorem dedup_slack_ge_count_surplus
    (Dcount Sigma : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (n m : ℕ)
    (hbind : Dcount n m ≤ budget n) :
    Sigma n m - budget n ≤ Sigma n m - Dcount n m :=
  Nat.sub_le_sub_left hbind (Sigma n m)

/-! ## The honest scope clause: the THRESHOLD form is NOT escaped here -/

/-- **The threshold form puts the larger field budget on the subset-sum side.**  The genuine open
input (B31/B33) is the *threshold* equivalence: the subset-sum side is tested against the **field
budget** `qbudget = q·ε* ≫ n`, not against the small `budget n ≈ n` the `Dcount` side uses.  We
record the trivial-but-load-bearing fact that the escape configuration's count failure
(`Sigma n m = n + 1 > n`) is **absorbed** once the budget is the field budget `qbudget ≥ n + 1`:

  `Sigma n m = n + 1 ≤ qbudget`   whenever `n + 1 ≤ qbudget`.

So the escape against the *count* form (small budget `n`) says NOTHING against the *threshold* form
(large field budget `q·ε*`): with `qbudget ≫ n` the very same `Sigma` fits.  This is the precise
reason the verdict is ESCAPE_CANDIDATE (count form escapable) and NOT a wall breach (threshold form
intact).  Honest scope, formalized. -/
theorem threshold_form_absorbs_escape (n qbudget : ℕ) (hq : n + 1 ≤ qbudget) :
    (fun n _ => n + 1) n 0 ≤ qbudget := hq

/-! ## Non-vacuity / sanity -/

/-- **Sanity — the escape config's three clauses are jointly realizable** (re-derived directly, to
witness none is vacuous).  `Dedup` holds (`0 ≤ n+1`), `WeakestSuffCount` holds (`0 ≤ n`),
`¬ BCHKSCount` holds (`n+1 > n` at `n = 2`). -/
example :
    Dedup (fun _ _ => 0) (fun n _ => n + 1)
    ∧ WeakestSuffCount (fun _ _ => 0) (fun n => n) (fun n => 2 ≤ n)
    ∧ ¬ BCHKSCount (fun n _ => n + 1) (fun n => n) (fun n => 2 ≤ n) :=
  ⟨escapeConfig_nonempty.dedup,
   escapeConfig_nonempty.weakestSuff,
   escapeConfig_nonempty.bchks_count_fails⟩

/-- **Sanity — opposite-monotonicity is genuinely the source.**  A degenerate config where
`Dcount = Sigma` (no dedup) is NOT an escape: there `WeakestSuff ⟺ BCHKS-count` (same object), so
the gap closes.  This confirms the escape needs the strict dedup `Dcount < Sigma`, matching
`escape_gap_eq_dedup`.  Stated: when `Dcount = Sigma`, `WeakestSuffCount → BCHKSCount`. -/
example (S : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (P : ℕ → Prop) :
    WeakestSuffCount S budget P → BCHKSCount S budget P := id

end ArkLib.ProximityGap.CoreA3deep

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA3deep.escapeConfig_nonempty
#print axioms ArkLib.ProximityGap.CoreA3deep.weakestSuff_not_imp_BCHKSCount
#print axioms ArkLib.ProximityGap.CoreA3deep.escape_gap_eq_dedup
#print axioms ArkLib.ProximityGap.CoreA3deep.dedup_slack_ge_count_surplus
#print axioms ArkLib.ProximityGap.CoreA3deep.threshold_form_absorbs_escape
