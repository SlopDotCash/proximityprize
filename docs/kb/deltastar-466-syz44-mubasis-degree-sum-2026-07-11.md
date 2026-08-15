# δ* #466 — SYZ44: the μ-basis degree-sum law as a Hilbert-function count (2026-07-11)

## One-line

The classical μ-basis **degree-sum law** `δ₁ + δ₂ = a + b + c` — half of G172's rate-1/2 residual —
is now a **proved corollary** of two standard graded commutative-algebra inputs (Bézout
surjectivity + graded μ-basis two-ramp), not an independent empirical assumption. The rate-1/2
`SylvesterInjective` residual is thereby reduced to a **single** open kernel: the imbalance bound
`ι ≤ 1`.

## Context

G172 discharged SYZ38's rate-1/2 `SylvesterInjective` down to two μ-basis facts about the
pairwise-coprime triple `(W_AB, W_AC, W_BC)` with reduced degrees `a,b,c`:
- **(a) degree-sum law**: syzygy module rank-2 free, generator degrees `δ₁ ≤ δ₂`, `δ₁+δ₂ = a+b+c`;
- **(b) imbalance**: `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1`.
Both were carried empirically (probe 52/52 field-independent for (a); ≤1 over 5542 triples for (b)).

SYZ44 removes (a) from the empirical column.

## The mechanism

Let `φ : K[X]³ → K[X]`, `(r₁,r₂,r₃) ↦ W_AB r₁ + W_AC r₂ + W_BC r₃`, `gcd = 1`. For a degree budget
`D`, restrict to the balanced window `deg rᵢ + dᵢ ≤ D` (`d=(a,b,c)`) and let `hilb D = dim_K K_D`,
`K_D = ker φ ∩ window(D)`. Two classical facts pin `hilb`:

1. **Rank–nullity for large D** (`RankNullity`): for `D ≥ D₀` the windowed map is surjective onto
   `{deg ≤ D}` (Bézout `1 = uW_AB+vW_AC+wW_BC` + degree reduction), so
   `hilb D + (D+1) = (D+1−a)+(D+1−b)+(D+1−c)`.
2. **Two-ramp Hilbert function** (`TwoRamp`): the kernel is rank-2 graded free (μ-basis) with
   generator degrees `δ₁ ≤ δ₂`, so `hilb D = (D+1−δ₁)+(D+1−δ₂)` (ℕ truncated subtraction = the two
   `max(0,·)` ramps).

Equate at any `D` above every parameter (subtractions exact): `2(D+1)−(δ₁+δ₂) = 2(D+1)−(a+b+c)`, so
`δ₁+δ₂ = a+b+c`. Pure `omega`.

**Honesty**: `RankNullity` and `TwoRamp` are *not* the empirical degree-sum law — they are the two
textbook facts (Bézout surjectivity; existence of a graded μ-basis over the PID `K[X]`) whose
conjunction the law is equivalent to. Mathlib has neither the graded μ-basis nor the large-D
triple-Bézout surjectivity, so they are named hypotheses (`def … : Prop`). What is proved
axiom-clean is that **granting them, the law is a one-line count** — not a resultant computation.
This collapses (a) to standard theory, matching SYZ38/SYZ39's "genuine commutative-algebra content"
framing.

## Landed theorems (`_SYZ44MuBasisDegreeSum.lean`, axiom-clean: propext, Quot.sound)

- `RankNullity`, `TwoRamp` — the two structural inputs as `Prop`s.
- `degree_sum_of_hilbert` — **the law**: `RankNullity ∧ TwoRamp ⟹ δ₁+δ₂ = a+b+c`.
- `min_generator_le_balanced` — `δ₁+δ₂=a+b+c`, `δ₁≤δ₂` ⟹ `δ₁ ≤ ⌊(a+b+c)/2⌋` (balanced upper edge).
- `min_syzygy_out_of_budget` — glue to G172: law + interior balanced gap
  `budget+1+extraGap ≤ ⌊(a+b+c)/2⌋` + imbalance `⌊(a+b+c)/2⌋−δ₁ ≤ extraGap` ⟹ `budget+1 ≤ δ₁`
  (minimal syzygy strictly out of budget → `G172.sylvester_injective_of_diff_natDegree_lt`).
- `min_syzygy_out_of_budget_of_hilbert` — packaged: two structural inputs + imbalance ⟹ out of
  budget, exhibiting the imbalance datum as the sole remaining syzygy-side hypothesis.

## Statements verbatim

```lean
def RankNullity (hilb : ℕ → ℕ) (a b c D₀ : ℕ) : Prop :=
  ∀ D, D₀ ≤ D → hilb D + (D + 1) = (D + 1 - a) + (D + 1 - b) + (D + 1 - c)

def TwoRamp (hilb : ℕ → ℕ) (δ₁ δ₂ : ℕ) : Prop :=
  ∀ D, hilb D = (D + 1 - δ₁) + (D + 1 - δ₂)

theorem degree_sum_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : RankNullity hilb a b c D₀)
    (hTwoRamp : TwoRamp hilb δ₁ δ₂) :
    δ₁ + δ₂ = a + b + c

theorem min_syzygy_out_of_budget
    (a b c δ₁ δ₂ budget extraGap : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hbal : budget + 1 + extraGap ≤ (a + b + c) / 2)
    (himb_le : (a + b + c) / 2 - δ₁ ≤ extraGap) :
    budget + 1 ≤ δ₁
```

## Updated final residual

Rate-1/2 uniform `SylvesterInjective` ⟸ **imbalance bound `ι ≤ 1` only** (with parity refinement
`ι = 1 ⟹ a+b+c even`). The degree-sum law is no longer an independent empirical assumption; it is a
Hilbert-function corollary of Bézout surjectivity + the graded μ-basis. The two structural inputs
(`RankNullity`, `TwoRamp`) are standard commutative algebra, not resultant/field-dependent content.

Does **not** claim δ* closure: production wire still needs SYZ33 lemma-1 supports, the general-`D`
peel, SYZ22 realizability, and the `MCAThresholdLedger` BGK/incidence lower bound. CORE OPEN /
ON-BGK.
