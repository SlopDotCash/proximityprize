# The sub-Johnson supply wall: the single remaining statement of the δ* deep-band programme (successor to #371)

## What this issue tracks

One statement. Everything else in the above-Johnson MCA threshold programme (#357 → #371) is proven, axiom-clean, in-tree:

> **The supply statement.** Bound, for a word `w` NOT in `rsCode dom k` (equivalently: for the lines `u₀ + γ·u₁` of bad scalars), the number of codewords of `rsCode dom k` with agreement `≥ k+m+1` with `w`, in the sub-Johnson agreement range — well enough that `ExplainableCoreSupply dom k m B` holds with `B` subexponential in the witness mass `C(n,k+m+1)/q^m`.

By `deep_band_badSet_card_of_supply` (in-tree, axiom-clean), any such `B` immediately converts the proven witness-mass law into a deep-band bad-scalar count: `∃ Q₀ : C(n,k+m+1) ≤ #badSet·q^m·B`. By the analysis logged in `DISPROOF_LOG.md` (2026-06-12 entry), this statement is quantitatively the classical sub-Johnson list-size question for Reed–Solomon codes.

## What is already proven (the #371 campaign, rounds 1–80; 96 axiom-clean declarations in rounds 64–80 alone)

| result | file |
|---|---|
| Boundary-band sup over ALL stacks `= C(n,k+1)` exactly (`C(n,k+1)² ≤ q`) | `UniversalBoundaryBound.lean` |
| Production boundary failure: `ε_mca ≈ 1`, no side conditions | `ProductionBoundaryFailure.lean` |
| Ladder curve exact at every radius (0 below band / spectrum mass in band) | `FullBandLadderLaw.lean`, `BandPackingLaw.lean`, `LadderSpectrumFusion*.lean` |
| Exact ladder count = `Σ_{a∈A(h,k+1)} 2^a·C(h,a)` (first exact count above Johnson) | `LadderSpectrumFusionValue.lean` |
| Master modular reduction: all far-stack censuses = arithmetic in `F[X]/P_S` | `ResidualModularReduction.lean` |
| Band `m ≥ 1` bracket `[⌊(n−k)/(m+1)⌋, C(n,k+1)/C(k+m+1,k+1)]` | `BandPackingLaw.lean`, `BandAttainmentChained.lean` |
| Deep-band witness mass `≥ C(n,k+m+1)/q^m`, every band, unconditional | `DeepBandCoherence.lean` |
| Multiplicity reduction to the named supply | `DeepBandMultiplicity.lean` |
| Supply proven above the wall (agreement-capped instance + near-line dichotomy) | `ExplainableCoreSupplyInstance.lean` |

Full arc: [`docs/wiki/deltastar-programme.md`](../blob/main/docs/wiki/deltastar-programme.md) · KB: [`docs/kb/deltastar-357-compiled-knowledge.md`](../blob/main/docs/kb/deltastar-357-compiled-knowledge.md) · refutations: `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` · build: `scripts/pg-warm.sh` once, then `scripts/pg-iterate.sh <file>` (lock-free).

## The two recorded attack routes

1. **The Johnson-split route**: handle near-code lines via the `near_scalar_unique` dichotomy (≤ 1 near scalar, proven) + the round-62 localization, and far lines via a list-size input at the Johnson boundary — partial closures for parameter ranges where Johnson-radius list bounds exist in-tree.
2. **The far-pair rank route**: the unconditional second moment of the coherent-core value map — requires lower-bounding the rank of paired coherence conditions for far core-pairs (the degeneracy strata are the obstacle; the diagonal and near-pair strata are already controlled by proven lemmas).

## Honesty rules (inherited)

Axiom-clean Lean or reproducible probes only; refutations to DISPROOF_LOG; the wall is a recognized open problem — do not fabricate closure; named-residual convention applies.

