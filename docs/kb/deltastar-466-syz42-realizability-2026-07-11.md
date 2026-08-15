# SYZ42 — realizability: is the SYZ22 production-ledger join redundant after SYZ41?

**Issue:** #466 / #507 · **Date:** 2026-07-11 · **File:**
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ42Realizability.lean` · **Axiom-clean**
(`propext, Classical.choice, Quot.sound` only; no `sorry`, no `native_decide`).

## The question

After SYZ41 removed the folded `syzdimBridge` field (its syzygy logic proven as
`generation_of_module_vanishes`), the master hypothesis `StripMasterHypothesis'` stands on **two**
fields: `uniformSylvester` and `realizability`. SYZ24's `span_eq_ceiling_iff_generates` had shown
the union-budget lower bound the strip needs is *exactly* cross-core generation (`⨆ Aᵢ = W`), and
SYZ41 now backs generation from `uniformSylvester`. So: **does `realizability` follow from
`uniformSylvester` through SYZ24 + SYZ41, collapsing the hypothesis to one field?**

## Verdict: NO — realizability is NOT redundant. Final field list stays TWO.

Tracing the exact types, the two obligations have **genuinely different quantifier shapes**:

- `uniformSylvester` → generation is **rigidity**: *for a given configuration*, every in-budget
  deficiency cocycle is trivial, so its span **attains** the ceiling `finrank W`
  (SYZ41 `generation_of_module_vanishes` → SYZ24 `span_eq_ceiling_iff_generates`).
- `realizability` is `∀ Ucard, Nonempty (SuperadditiveUnion n k Ucard)` — an **existence /
  construction** statement. Unfolding `SuperadditiveUnion` (SYZ20) exposes **six** fields, of which
  **five are pure existence of data** that no rigidity input manufactures:
  `synFunctionals`, a **nonzero** `syndrome`, its `annihilated` certificate, and — decisively — the
  ambient pinning `dim_syndromePair : finrank V = 2·(n − k)` (false for a generic
  finite-dimensional `V`, e.g. `V = 0`).

Rigidity cannot deliver existence: "every deficiency vanishes" produces neither the syndrome vector
nor the functionals, and cannot force `finrank V = 2(n − k)`. The quantifiers do not meet.

## What SYZ42 *does* buy: the analytic sixth field is now derived, not assumed

The **one** `SuperadditiveUnion` field generation controls is `union_span_rank`
(`finrank (span synFunctionals) = 2(Ucard − k)`) — precisely the span **lower bound** SYZ22/SYZ24
flagged as the realizability residue for over-budget families. This file discharges it:

- `superadditiveUnion_of_generation` — **builds** a full `SuperadditiveUnion` from the existence
  data + a *generation* certificate (`span synFunctionals = W`) + the ceiling value
  (`finrank W = 2(Ucard − k)`, SYZ22 `doubled_shortening_dim`). `union_span_rank` is *computed*.
- `RealizabilityCore (n k Ucard)` — `SuperadditiveUnion` with the analytic `union_span_rank` field
  **replaced** by `(ceiling W, generates : span = W, ceiling_dim : finrank W = 2(Ucard−k))`. The
  remaining fields are the irreducible existence residue.
- `RealizabilityCore.toSuperadditiveUnion` and `SuperadditiveUnion.toRealizabilityCore` — the two
  are **logically equivalent** (reverse uses `W := span synFunctionals`, `generates := rfl`), so the
  reformulation loses nothing; it only *exposes* the analytic field as the generation condition.

## The sharpest honest master hypothesis

`StripMasterHypothesis'' (n k)` — two fields:
- `uniformSylvester : SYZ40.UniformSylvesterInjective K n k` (the substantive polynomial residual);
- `realizabilityCore : ∀ Ucard, k ≤ Ucard → Ucard ≤ n → Nonempty (RealizabilityCore … n k Ucard)`.

`toPrime`/`ofPrime` show `''` and SYZ41's `'` are interchangeable, and
`strip_theorem_of_master_hypothesis''` delivers the identical strip conclusion (concrete spread
branch: every in-budget reduced syzygy of a rate-`1/2` band triple vanishes; union budget
`|U| ≤ n − 1`). This is a **reformulation, not a field-count reduction**: value = transparency, the
generation phrasing pins which part `uniformSylvester`+SYZ22/SYZ24 discharge and isolates the genuine
open residue = the **syndrome-configuration existence** (sunflower packing / SYZ18 distinct-support
control).

## Statements (verbatim signatures)

```
def superadditiveUnion_of_generation {n k Ucard : ℕ}
    (synFunctionals : Set (Module.Dual K V)) (syndrome : V) (syndrome_ne : syndrome ≠ 0)
    (annihilated : ∀ φ ∈ synFunctionals, φ syndrome = 0)
    (W : Submodule K (Module.Dual K V)) (generates : Submodule.span K synFunctionals = W)
    (ceiling_dim : finrank K W = 2 * (Ucard - k))
    (dim_syndromePair : finrank K V = 2 * (n - k)) :
    SuperadditiveUnion (F := K) (V := V) n k Ucard

structure RealizabilityCore (n k Ucard : ℕ) where
  synFunctionals : Set (Module.Dual K V); syndrome : V; syndrome_ne : syndrome ≠ 0
  annihilated : ∀ φ ∈ synFunctionals, φ syndrome = 0
  ceiling : Submodule K (Module.Dual K V)
  generates : Submodule.span K synFunctionals = ceiling
  ceiling_dim : finrank K ceiling = 2 * (Ucard - k)
  dim_syndromePair : finrank K V = 2 * (n - k)

structure StripMasterHypothesis'' (n k : ℕ) : Prop where
  uniformSylvester : SYZ40.UniformSylvesterInjective K n k
  realizabilityCore : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (RealizabilityCore (K := K) (V := V) n k Ucard)

theorem strip_theorem_of_master_hypothesis'' [DecidableEq K] {n k : ℕ}
    (H : StripMasterHypothesis'' K V n k) (hn : n = 2 * k) :
    (∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ), … → rAB = 0 ∧ rAC = 0 ∧ rBC = 0)
    ∧ (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1)
```

## Production instantiation corollary (n = 2³⁰) and the remaining gap

At the literal prize parameters `n = 2³⁰`, `k = 2²⁹` (`hn : n = 2·k`),
`strip_theorem_of_master_hypothesis''` gives, from the two fields:

1. **Spread rigidity (from `uniformSylvester` alone):** every in-budget reduced syzygy
   `WAB·rAB − WAC·rAC + WBC·rBC = 0` of a rate-`1/2` band triple (any support) forces
   `rAB = rAC = rBC = 0`. This is SYZ40 `strip_theorem_of_uniform_sylvester` and needs *no*
   realizability.
2. **Union budget (from `realizabilityCore`):** every spread stack of degenerate cores has
   `|U| ≤ n − 1`, via `RealizabilityCore.toSuperadditiveUnion` →
   `SYZ22.strip_budget_of_realizability`.

**Gap trace between this and `mcaDeltaStar ≥ 1/3 − lattice`:** the strip theorem is the *structural*
half (over-budget stacks stay within budget on `(Johnson, 1/3)`). Converting it to a `δ*` lower
bound still needs the **epsMCA ledger lemma** from SYZ22's kb: the merge-corrected knapsack
(`SYZ20.merge_integer_closes_strip_n64`, and its `n = 2³⁰` analogue) certifies bad-count `< B`
throughout the strip *given* the union budget, and the continuous crossover
(`merge_near_crossover_eq`) ties the budget at the single top lattice radius
`δ = 1/3 − 1/(3n)`. So the residual chain to `mcaDeltaStar ≥ 1/3 − 1/(3n)` is:
`uniformSylvester` (SYZ39/BGK) **and** the realizability existence core **and** the integer-lift
knapsack ledger at `n = 2³⁰`. SYZ42 does **not** move the unconditional `δ*` — that status is
untouched; it refactors the realizability obligation into its sharpest honest form.

## Bottom line

- Realizability **redundant?** No. Final field list: **two** (`uniformSylvester`,
  `realizabilityCore`).
- Discharged: the analytic `union_span_rank` field (now derived from generation).
- Irreducible open residue of realizability: the syndrome-configuration **existence** (SYZ18
  sunflower packing), decoupled from the rank equality.
