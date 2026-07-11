# SYZ18 — pairJoint self-exclusion: FALSE as a field-independent law, but a small/moderate-field artifact (2026-07-11)

Issue #466 (δ*/proximity-prize). High-risk/high-reward round inverting the campaign
stance: the `mcaEvent` mutual-agreement clause (`¬ pairJointAgreesOn`) as a *weapon*.

## Conjecture (as briefed)

At rate `1/2`, for a radius `δ` in the strip `(Johnson ≈ 0.2929, 1/3)`, any stack
`(u₀, u₁)` with more than budget-many `mcaEvent`-bad scalars must be a **syzygy config**
(rank-deficient witness family; G86/G87: over-budget ⇒ nontrivial syzygy among the
`γ`-weighted GRS parity rows), and every such config is **self-excluding**: the shared
algebraic structure forces `pairJointAgreesOn` to fire for at least one involved scalar,
so it was never bad. If true throughout the strip, combined with SYZ9 (channel wall) and
SYZ6 (ceiling) it would pin `δ*(rate 1/2, production) = 1/3` exactly — the prize.

Budget (G86 `_G86RankCollapseDichotomy`, `plantable_linearIndependent_cap`):
`r_max = ⌊(2(n−k) − 1)/((n−k) − e)⌋`, with `e = ⌊δ·n⌋`, `t−k = (n−k) − e`.

## Method — exact, cross-validated

`scripts/probes/probe_syz18_pairjoint_self_exclusion.py`. Generalizes the unique-regime
syndrome criterion of `probe_strip_sup_exactness.py` to the **list-decoding regime**
(`2e ≥ d`, which is exactly where the strip lives, above unique decoding `n/4` at rate 1/2).

Exact `mcaEvent` badness via syndromes only (no codeword enumeration). Parity rows
`H[rr,j] = x_jʳʳ⁺¹`; `S(E) :=` column span of `H[:,E]` = syndromes of words supported on
`E`; membership `t ∈ S(E) ⇔ rank(H_E) = rank([H_E | t])` (exact GF(p) Gaussian elim):

> `γ` is BAD ⇔ ∃ support `E`, `|E| ≤ e`, with `t_γ = s₀ + γ·s₁ ∈ S(E)` **and**
> `¬(s₀ ∈ S(E) ∧ s₁ ∈ S(E))`.
> `γ` is RESCUED (explainable but not bad) ⇔ every explaining `E` also has both
> `s₀, s₁ ∈ S(E)` (a joint codeword pair agrees on the witness set `S = Eᶜ`).

**Cross-validation vs direct word-level `mcaEvent` (ABF26 Def 4.3): PASS** on V0 (unique,
RS[F₇,μ₆,1], 30 stacks) and V1 (list regime, RS[F₁₇,μ₈,2], 15 stacks). The headline
counterexample below was additionally reconstructed to explicit words `u₀,u₁` and its bad
set matched the syndrome criterion exactly.

**Direct construction of syzygy configs.** For target scalars `Γ` and supports `{E_γ}`,
impose `s₀ + γ·s₁ ∈ S(E_γ)` (each = `dim`-`(r−e)` linear rows `L·s₀ + γ·L·s₁ = 0`,
`L ∈` left-null `H_{E_γ}`). Solving the joint GF(p) nullspace of `> r_max` such blocks
*forces* a syzygy. Then measure the TRUE bad count and rescue count over all of `F`.

## Results — data

### Strip cells, exhaustive over F, direct construction (400 trials)

| cell | n,k,e | δ | p | budget | max true-bad | over-budget cfgs | zero-rescue viol |
|------|-------|---|---|--------|--------------|------------------|-------------------|
| S1 | 10,5,3 | 0.300 | 11  | 4 | **9**  | 7 | **6** |
| S2 | 10,5,3 | 0.300 | 101 | 4 | 8      | 1 | 0 (rescued) |
| S3 | 12,6,4 | 0.333 | 13  | 5 | **13** | 6 | **6** |

S1 headline: stack `u₀=[8,8,5,6,4,0,0,0,0,0]`, `u₁=[6,3,0,5,3,0,0,0,0,0]` over `F₁₁`,
RS[10,5] (δ=0.30) has **9 of 11 scalars `mcaEvent`-bad** (`γ ∈ {0,1,2,3,6,7,8,9,10}`),
budget 4, **zero pairJoint rescue** — verified EXHAUSTIVELY at word level. A literal,
reproducible counterexample.

### Field-size sweep, fixed shape n=6,k=3,e=2 (δ=1/3), budget 5

| p | \|F\|/n | max bad (targeted) | zero-rescue viol |
|---|--------|--------------------|-------------------|
| 7 | 1 | 6 | 8 |
| 37 | 6 | 6 | 1 |
| 97 | 16 | 1 | 0 |
| 997 | 166 | 1 | 0 |
| 9973 | 1662 | 1 | 0 |
| 99991 | 16665 | 3 | 0 |
| 1000003 | 166667 | 3 | 0 |

The over-budget-zero-rescue phenomenon **disappears** once `|F|/n ≳ 16`; above the
transition every explainable-beyond-budget scalar is pairJoint-rescued (rescue rate → 1).
At `n=10` the transition is slower: a **non-degenerate** violation persists at `p=101`
(`|F|/n≈10`, `s₁≠0`, neither syndrome δ-close to `C`, 10 bad scalars, budget 4).

## Verdict

**The literal, field-independent SYZ18 conjecture is FALSE.** Over-budget syzygy configs
that are NOT self-excluding genuinely exist — word-level-verified at `F₁₁` and present
(non-degenerate) up to `|F| ≈ n²`. The `mcaEvent` mutual clause is NOT a field-independent
weapon; a syzygy among the `γ`-weighted parity rows does not force `pairJointAgreesOn` in
general, because the bad scalars use *distinct* error supports (see mechanism).

**But the phenomenon is a small/moderate-field artifact.** As `|F|/n → ∞` the violations
vanish and self-exclusion (rescue) dominates — exactly consistent with RS proximity gaps
requiring `|F| ≫ n`. So the **prize-relevant** form (production `|F| ≈ 2⁹⁰ ⋙ n`) is NOT
refuted by these probes; the large-field data is *consistent with* self-exclusion but does
**not** prove it — over-budget configs become too rare to sample as `p` grows (precisely
G86 generic-position: syzygies are increasingly non-generic). SYZ18 therefore cannot pin
`δ* = 1/3` via a clean unconditional syzygy⇒self-exclusion theorem; any such pin needs a
quantitative large-field argument, not the field-independent mechanism.

## Mechanism (proved, unconditional, all fields)

The atomic engine of self-exclusion is **shared-witness collapse**, and it explains
exactly why the conjecture holds per-support but fails in aggregate at small fields:

> If two *distinct* scalars `γ₀ ≠ γ₁` each have a codeword of `C` agreeing with their line
> `u₀ + γ·u₁` on the **same** set `S`, then `pairJointAgreesOn C S u₀ u₁` holds.

Proof (pencil inversion): `w₀ = u₀+γ₀u₁`, `w₁ = u₀+γ₁u₁` on `S` ⇒ `w₀−w₁ = (γ₀−γ₁)u₁` on
`S`, so `v₁ := (γ₀−γ₁)⁻¹·(w₀−w₁) ∈ C` agrees with `u₁` on `S`, and `v₀ := w₀ − γ₀·v₁ ∈ C`
agrees with `u₀` on `S`. Syndrome form: `S(E)` (`E = Sᶜ`) is a subspace closed under
`t_{γ₀} − t_{γ₁} = (γ₀−γ₁)s₁`, forcing both `s₀, s₁ ∈ S(E)` individually — pairJoint.

**Consequence:** two `mcaEvent`-bad scalars can never share a witness set; distinct bad
scalars require distinct supports. This is a genuine partial self-exclusion, but it caps
nothing on its own: at rate 1/2, δ=1/3, there are `C(n, e)` distinct supports available,
far more than the ~`n` scalars, so a small field can host many bad scalars each on its own
support. The bridge from "shared-support self-exclusion" to "over-budget ⇒ self-exclusion"
requires the syzygy to *manifest as* a shared/collapsed support, which happens generically
only when the field is large enough that the list-decoding budget binds before the field
is exhausted — the exact small-field failure mode observed.

## Formal results — `Frontier/_SYZ18PairJointSelfExclusion.lean` (axiom-clean)

`propext, Classical.choice, Quot.sound` only, over an arbitrary field `F`, `A` an
`F`-module, `C : Submodule F (ι → A)`:

- `shared_witness_forces_pairJoint (hne : γ₀ ≠ γ₁) (h0 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₀ • u₁ i) (h1 : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i) : pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁`
- `mcaEvent_witnesses_are_scalar_unique (hnoJoint : ¬ pairJointAgreesOn C S u₀ u₁) (h0 …) (h1 …) : γ₀ = γ₁`
- `no_two_bad_scalars_share_witness (hnoJoint …) (hbad0 …) (hbad1 …) (hne : γ₀ ≠ γ₁) : False`

These formalize the *honest maximum* — the shared-witness mechanism — NOT the (false)
full conjecture. The δ*(rate 1/2) bracket is unchanged: `3/8 ≤ δ* ≤ 43/96+ε < 1/2`; SYZ18
does not close it to `1/3`.
