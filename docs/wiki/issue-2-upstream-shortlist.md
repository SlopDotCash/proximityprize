# Issue #2 upstream shortlist review

This reviews the eight ToMathlib candidates named in
[issue #2](https://github.com/SlopDotCash/proximityprize/issues/2), against standalone
`main` at `a6475f7c0` on 2026-09-05. Source inspection establishes the boundaries below;
it is not a claim that the modules compile against upstream's current dependencies.

## Current boundaries

Paths in this table are relative to `ArkLib/ToMathlib/`.

| Candidate | Source and remaining port work |
|---|---|
| `Combinatorics/Additive/BalogSzemerediGowers.lean` | Elementary reductions, an explicit `BSGCore`, and a conditional headline theorem. Imports local `HigherEnergy`. The core is not proved here. |
| `Combinatorics/Additive/SumProduct.lean` | Elementary reductions, `SumProductExpansionCore`, and `SubgroupEnergyCore`. Imports local `HigherEnergy`. The energy conclusion remains conditional. |
| `AppendHelpers.lean` | One support-transport theorem importing `ArkLib.OracleReduction.Execution`. Port with its execution API, after checking that upstream's corresponding theorem is absent. |
| `AveragingExistence.lean` | One real-valued convenience theorem. It specializes Mathlib's `Finset.exists_le_of_sum_le`; preserve the existing local API, and do not present it as a new general averaging principle. |
| `BivariateDegreeToolkit.lean` | Imports local `Data.Polynomial.Bivariate` and `Trivariate`, whose CompPoly APIs require compatibility review. |
| `BivariateGradedDvd.lean` | Imports the local Bivariate surface. Its three declarations require the same dependency review. |
| `CoeffExtract.lean` | Imports campaign-specific `BetaMatchingVanishes`. Extract a general statement and its dependency closure before proposing a campaign-free port. |
| `CyclotomicPatternInjectivity.lean` | Three characteristic-zero results with only Mathlib imports. Review overlap, mathematical hypotheses, and upstream-toolchain compatibility before porting. |

The first two paths are nested under `Combinatorics/Additive`, rather than directly
under ToMathlib. Do not confuse a module's title with a completed proof of its named
external theorem, or infer a Mathlib-only dependency closure from its directory.

## Averaging wrapper

`AveragingExistence.exists_ge_sum_div_card` retains its public statement and derives
its conclusion directly from `Finset.exists_le_of_sum_le`. Its imports are limited
to ordered finite sums and real numbers. The old description's nonnegativity
restriction was unnecessary: the theorem permits arbitrary real summands.

The focused Lean check and explicit axiom check for this proof passed under the
repository's Lean 4.30.0-rc2 environment, with only `propext`, `Classical.choice`,
and `Quot.sound`. This does not establish compatibility with another toolchain.

## Acceptance of an upstream contribution

Each proposed port still needs an exact upstream base, a dependency-closed diff,
validation with upstream's own toolchain, checks of imported assumptions, and
regression examples where behavior changes. Retain author and license notices.
Do not copy the standalone campaign workflows or report a local compatibility
check as a completed upstream merge.

The positional `Fin.castSum`/`sumCases` correction is a separate, bounded candidate
from issue #2's shared-Data list. Its acceptance requires distinguishing repeated
block lengths, skipping empty blocks, supporting dependent elimination, and
removing `sorryAx` from the eliminator under upstream's own validation rules.
