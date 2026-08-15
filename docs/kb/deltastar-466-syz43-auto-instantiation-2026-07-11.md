# δ* / #466 — SYZ43: is `RealizabilityCore` auto-instantiated by an actual over-budget stack?

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ43AutoInstantiation.lean`
Branch: `codex/syz43-auto-instantiation` (off `fork/research/proximity-prize` tip `b84138c42`)
Axiom audit: all three theorems `[propext, Classical.choice, Quot.sound]`. No `sorry`, no
`native_decide`, no new `axiom`.

## Question

SYZ42 refactored the strip's `realizability` obligation into `RealizabilityCore`, splitting its six
fields into **one analytic field** (generation `span synFunctionals = ceiling` + its value
`finrank ceiling = 2(Ucard − k)`, together the old `union_span_rank`) and **five existence-residue
fields** (`synFunctionals`, a nonzero `syndrome`, its `annihilated` clause, the ambient pinning
`finrank V = 2(n − k)`). SYZ43 asks empirically at the concrete consumer:

> Does an actual over-budget stack `(u₀, u₁)` with `mcaEvent`-bad scalars, fed through the G87
> syndrome bridge (`_G87McaEventSyndromeBridge.lean`), auto-supply the fields of `RealizabilityCore`?

## Verdict: FIVE of six fields are auto-instantiated; the analytic field is NOT — and its residual is NOT `uniformSylvester`

The G87 bridge context hands the consumer, on the stack's own syndrome pair over
`V = SyndromePair C = ((ι→F)⧸C)²`, exactly the existence residue SYZ42 isolated:

| RealizabilityCore field | source in the over-budget stack |
|---|---|
| `synFunctionals` | `Set.range φ`, φ = G87 bridge functionals (`exists_bridge_functionals`) |
| `syndrome` | `syndromePair C u₀ u₁` (the stack's own) |
| `syndrome_ne` | **free**: `mcaEvent_not_both_mem` ⟹ `¬(u₀∈C ∧ u₁∈C)` ⟹ `≠0` via `syndromePair_eq_zero_iff` |
| `annihilated` | every bridge functional kills the pair (`exists_bridge_functionals`) |
| `dim_syndromePair` | **free**: `finrank_syndromePair` gives `2(card ι − finrank C) = 2(n−k)` |

The one field NOT delivered is the **analytic** one:
`finrank (span synFunctionals) = 2(Ucard − k)`. G87's `plantable_span_cap` gives only the *upper*
bracket `finrank(span) + 1 ≤ 2(n−k)`; the matching *lower* bound (the bridge functionals actually
**realise** the full doubled shortening) is the SYZ22(iii) sunflower-packing / SYZ18 distinct-support
residual. It is carried as the explicit hypothesis `hrank`.

Crucially `hrank` is a **separate** open input from `UniformSylvesterInjective` (SYZ38/SYZ39, BGK
type). `uniformSylvester` discharges the strip's *spread branch* (`generation_of_module_vanishes`:
reduced band-triple syzygies vanish); it says nothing about the union-rank lower bound of the G87
syndrome functionals. Therefore:

* the master hypothesis genuinely stays at **two** open fields (`uniformSylvester`, `realizability`),
  confirming SYZ42's non-redundancy verdict now from the consumer side;
* the one-hypothesis form `UniformSylvesterInjective → (no over-budget stacks)` **does NOT close**.
  This is NOT the arc's closing document — the assembly does not collapse to one hypothesis.

No unconditional δ*; no conditional-on-`uniformSylvester`-alone δ*.

## The two instantiation theorems (verbatim shapes)

```
def realizabilityCore_of_overBudget_stack
    (C : Submodule F (ι → F)) {n k Ucard : ℕ} {D : Type*}
    (hn : Fintype.card ι = n) (hk : finrank F C = k)
    {u₀ u₁ : ι → F} (hstack : u₀ ∉ C ∨ u₁ ∉ C)
    (φ : D → Module.Dual F (SyndromePair C))
    (hann : ∀ p, φ p (syndromePair C u₀ u₁) = 0)
    (hrank : finrank F (Submodule.span F (Set.range φ)) = 2 * (Ucard - k)) :
    RealizabilityCore (K := F) (V := SyndromePair C) n k Ucard
-- syndrome_ne, dim_syndromePair discharged INTERNALLY; ceiling := span(range φ), generates := rfl

theorem realizabilityCore_of_mcaEvent_witnesses
    (C : Submodule F (ι → F)) {n k Ucard r t : ℕ}
    (hn : Fintype.card ι = n) (hk : finrank F C = k)
    {u₀ u₁ : ι → F} (hstack : u₀ ∉ C ∨ u₁ ∉ C) (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S.card = t ∧ ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x)
    (hrank : ∀ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) →
      finrank F (Submodule.span F (Set.range φ)) = 2 * (Ucard - k)) :
    Nonempty (RealizabilityCore (K := F) (V := SyndromePair C) n k Ucard)
```

`realizabilityCore_of_mcaEvent_witnesses` builds the bridge functionals internally
(`exists_bridge_functionals`), so from `mcaEvent`-bad witnesses alone the entire existence residue is
discharged; the sole surviving hypothesis `hrank` is the union-rank lower bound quantified over the
produced bridge family — the isolated realizability residual.

`strip_theorem_of_uniform_sylvester_and_rank` re-exports SYZ42's two-field `''` strip conclusion
(spread branch + union budget `Ucard ≤ n−1`), recording that the realizability provider's *existence
residue* is the auto-instantiated one.

## Remaining hypothesis list (precise)

The strip theorem stands on exactly two independent open inputs, neither implying the other:

1. `UniformSylvesterInjective K n k` (SYZ38/SYZ39, BGK/additive-cancellation over μ_n) — the spread
   branch.
2. Per-`Ucard` **union-rank lower bound** `hrank`: `finrank(span of the G87 bridge functionals) =
   2(Ucard − k)` (SYZ22(iii) sunflower packing / SYZ18 distinct-support realizability). SYZ43 proves
   this is the *only* residual of the `realizability` field — its existence residue is auto-supplied.

## Not wired (honest gap)

`mcaDeltaStar_ge_of_uniform_sylvester` at the n=2^30 prize parameters was **not** landed. The
in-tree ledger lemma `MCAThresholdLedger.le_mcaDeltaStar_of_good` needs `epsMCA C δ ≤ εstar` (a good
radius). Bridging the strip's *union budget* `|U| ≤ n−1` to that `epsMCA` bound requires the census
counting chain (bad-count-per-stack ⟹ probability bound ⟹ `epsMCA`), which is a separate substantial
step not available here; wiring it would be dishonest. The conditional two-sided pin (with SYZ6's
`≤ 0.334` ceiling) therefore remains gated behind that census bridge in addition to (1)+(2).
