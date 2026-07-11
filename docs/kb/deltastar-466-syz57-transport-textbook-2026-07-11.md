# #466 SYZ57 — the transport wire + the two textbook facts (honest partial, 2026-07-11)

**Status: LANDED, axiom-clean.** Two new Lean files, every `#print axioms` a subset of
`[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`, verified with `scripts/pg-iterate.sh`:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ57TextbookFacts.lean` — Task A, the Bézout
  seed behind SYZ44's `RankNullity` (✅ OK 5s, axioms `[propext, Quot.sound]`).
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ57TransportWire.lean` — Task B, the wire (iv)
  transport reduced to a named counting dictionary (✅ OK 13s, axioms
  `[propext, Classical.choice, Quot.sound]`).

This is an **honest-ledger** advance, not a δ* closure. Both underlying facts are genuinely the hard
open content of the rate-`1/2` chain; SYZ57 discharges the mechanically-reachable slice of each and
names the residue precisely.

## Task A — the two textbook facts behind the degree-sum law

SYZ44's `degree_sum_of_hilbert` is axiom-clean **given** two Props about the windowed-kernel Hilbert
function `hilb : ℕ → ℕ` of a pairwise-coprime triple: `RankNullity` (Bézout surjectivity +
rank–nullity dimension count) and `TwoRamp` (graded μ-basis, two-ramp shape).

**What SYZ57 proves (the ungraded Bézout seed underlying `RankNullity`):**

```lean
theorem exists_triple_bezout_of_coprime {f g h : R} [CommRing R]
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ r₁ r₂ r₃ : R, f * r₁ + g * r₂ + h * r₃ = 1

theorem exists_triple_repr {f g h : R} [CommRing R]
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) (p : R) :
    ∃ r₁ r₂ r₃ : R, f * r₁ + g * r₂ + h * r₃ = p

theorem span_triple_eq_top {f g h : R} [CommRing R]
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    Ideal.span ({f, g, h} : Set R) = ⊤
```

Proof route: `IsCoprime.mul_right` chains `IsCoprime f g`, `IsCoprime f h` into
`IsCoprime f (g*h)`, whose two-element Bézout `a·f + b·(g*h) = 1` gives the triple representation
`f·a + g·(b·h) + h·0 = 1`; scaling by `p` gives surjectivity onto all of `R`. This is the classical
"`1 = uf+vg+wh`, then scale" step — the reason the window map's image is eventually everything.

**Is the degree-sum law now unconditional? NO.** `RankNullity` and `TwoRamp` are statements about a
*concrete* `hilb D = finrank_K (ker φ ∩ balancedWindow D)`, a graded-module dimension. Two
genuinely-classical-but-unformalised obligations remain between the seed and those Props:

1. **Degree-controlled surjectivity + dimension count** (`RankNullity`): from ungraded surjectivity
   onto `K[X]`, extract that the *balanced-window* restriction already surjects onto `deg ≤ D` for
   `D ≥ D₀` (extended-Euclid degree bounds `deg u ≤ deg g + deg h`, reduce cofactors mod pairwise
   products), then convert the three window dims + image dim into `hilb D + (D+1) = Σ(D+1−dᵢ)`.
   Mathlib lacks both the windowed finrank bookkeeping and triple-Bézout degree control.
2. **The graded μ-basis** (`TwoRamp`): submodules of a free PID module are free, but the *graded*
   two-ramp shape needs the leading-coefficient filtration / degree-jump argument
   (`dim K_D − dim K_{D−1} ∈ {0,1,2}` monotone). Not in Mathlib.

So SYZ44's degree-sum law remains **conditional on `RankNullity ∧ TwoRamp`**, now with (1)'s
ungraded core discharged.

## Task B — the transport wire (SYZ46 hypothesis (iv))

SYZ46's capstone carries an **opaque** hypothesis
`transport : StripMasterHypothesis'' (ZMod P) V (2³⁰) (2²⁹) → StripCensusBound` (wire (iv): route
SYZ40's abstract union budget through the G87 `mcaEvent`→syndrome bridge to the concrete per-stack
`mcaBadCount` cap).

**Assessment: NOT mechanical.** SYZ42's `strip_theorem_of_master_hypothesis''` (with `n = 2k`)
delivers, as its second conjunct, the *abstract* union budget
`∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n−1` (★) — a statement about an abstract union
cardinality, **not** about `mcaBadCount` at the concrete `evalCode`. The entire residual content of
wire (iv) is the **counting dictionary**: mapping each concrete stack's bad-scalar count to an
admissible `Ucard ∈ [k,n]` dominating it. That map is the G87 bridge composed with the SYZ29
core-attribution question (are all bad scalars core-attributed?) — the genuine gap.

**What SYZ57 lands (a strict reduction, arithmetic side discharged):**

```lean
def CountingDictionary : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    ∃ Ucard : ℕ, 2 ^ 29 ≤ Ucard ∧ Ucard ≤ 2 ^ 30 ∧
      mcaBadCount (F := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator)
        (u 0) (u 1) ≤ Ucard

theorem stripCensusBound_of_master_hypothesis {V} [AddCommGroup V] [Module (ZMod P) V]
    [FiniteDimensional (ZMod P) V]
    (H : SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (dict : CountingDictionary) : StripCensusBound

theorem deltaStar_bracket_of_master_hypothesis {V} [AddCommGroup V] [Module (ZMod P) V]
    [FiniteDimensional (ZMod P) V]
    (H : SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (dict : CountingDictionary) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤ mcaDeltaStar … ∧
      mcaDeltaStar … ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal)
```

`stripCensusBound_of_master_hypothesis` discharges the `≤ n−1` half of wire (iv) *mechanically* from
(★); the only surviving input is `CountingDictionary`. This **replaces** SYZ46's opaque
`transport : H → StripCensusBound` with `H → CountingDictionary → StripCensusBound`: wire (iv) is no
longer an unstructured black box but the single named `CountingDictionary` obligation. **δ* is not
closed** — the counting dictionary (bridge + attribution) is the genuine remaining transport gap.

## Updated wire list (rate-1/2 chain)

| wire | content | status after SYZ57 |
|------|---------|--------------------|
| (i) `uniformSylvester` | SYZ38/SYZ39 BGK-type | OPEN (unchanged) |
| (ii) support control | SYZ18 `twist_pair_indep` | as before |
| (iii) realizability existence residue | SYZ22/SYZ43 union-rank `hrank` | as before |
| (iv) abstract→concrete transport | opaque `H → StripCensusBound` | **reduced to `CountingDictionary` (G87 bridge ∘ SYZ29 attribution); arithmetic `≤ n−1` side discharged** |
| degree-sum law inputs | `RankNullity`, `TwoRamp` | **ungraded Bézout seed discharged; graded finrank/μ-basis still OPEN** |

## Honesty

No δ* pin, no unconditional degree-sum law, no closed transport. Both SYZ57 files are axiom-clean
partials that discharge the Mathlib-reachable slice and name the two genuinely-open textbook /
attribution residues precisely. Nothing here belongs in `DISPROOF_LOG.md`.
