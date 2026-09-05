# The δ* Programme

> **Standalone repository notice (2026-08-16).** The complete research corpus now lives in
> [`SlopDotCash/proximityprize`](https://github.com/SlopDotCash/proximityprize), with `main` as the
> integration branch. Develop on a focused feature branch based on `origin/main`; do not route new
> work to the retired `lalalune/ArkLib` `research/proximity-prize` branch. Current coordination is
> [#164](https://github.com/SlopDotCash/proximityprize/issues/164) for the mathematical CORE and
> independent production-completion audit, and
> [#2](https://github.com/SlopDotCash/proximityprize/issues/2) for cleanup/upstream carve-out.
> Issues #1 and #4 were consolidated into #164 on 2026-09-05; their administrative closure does
> not establish the production theorem. Issue #3 is completed historical state/census work.

The mutual-correlated-agreement threshold programme: pin
`δ*(C, ε*) = sup{δ : ε_mca(C, δ) ≤ ε*}` for explicit smooth-domain Reed–Solomon
codes ([ABF26] Definition 4.3), with matching machine-checked bounds.

## Where everything is

| What | Where |
|---|---|
| Agent guide (build recipe, honesty rules, pitfalls, state of knowledge) | [`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`](../../ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md) |
| Current standalone completion ledger and post-v3 results | [`docs/kb/deltastar-DOSSIER-v4-2026-08-16.md`](../kb/deltastar-DOSSIER-v4-2026-08-16.md) |
| Historical full campaign dossier through 2026-07-11 | [`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`](../kb/deltastar-DOSSIER-v3-2026-07-01.md) |
| Compiled campaign knowledge (#357, by theme) | [`docs/kb/deltastar-357-compiled-knowledge.md`](../kb/deltastar-357-compiled-knowledge.md) |
| Research map (papers + adjacent math + ranked attack vectors) | [`docs/kb/deltastar-research-map.md`](../kb/deltastar-research-map.md) |
| #444 no-larp companion map (25 directions/status tags) | [`ArkLib/Data/CodingTheory/ProximityGap/docs/kb/deltastar-444-complete-map-25x25-2026-06-17.md`](../../ArkLib/Data/CodingTheory/ProximityGap/docs/kb/deltastar-444-complete-map-25x25-2026-06-17.md) |
| Refuted approaches with constraint lemmas | [`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`](../../ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md) |
| Probes (exact small-scale computation) | `scripts/probes/probe_*.py` |
| **The paper** (the complete machine-checked theory, rounds 64–84) | [`docs/papers/mca-threshold-above-johnson.md`](../papers/mca-threshold-above-johnson.md) |
| The nine-hypothesis methodology record | [`docs/wiki/deltastar-357-nine-hypotheses-2026-06-11.md`](deltastar-357-nine-hypotheses-2026-06-11.md) |

## The fast build path (mandatory)

The ProximityGap cone is 800+ files. **Never iterate with `lake build`** (3000+-job
trace + the build lock serializes all agents). Instead:

```bash
scripts/pg-warm.sh                 # once per session: pre-build substrate oleans
scripts/pg-iterate.sh <file>.lean  # per attempt: ~30-75s, lock-free, parallel-safe
./scripts/lake-locked.sh build <m> # only for full-module olean builds (serialized)
```

Develop in a detached `/tmp` worktree with `.lake` symlinked to the main checkout
(see the agent guide §2 for the concurrency hazards on this shared tree).

## The state in one paragraph

The production conjecture remains **OPEN / ON-BGK**. Exact finite-instance and deep-rung pins,
threshold ledgers, brackets, reductions, and no-go theorems are machine checked, but none is the
production theorem. The analytic face still requires square-root-scale cancellation for the
adversarial smooth multiplicative subgroup. The rate-`1/2` strip face is assembled conditionally
and exposes three open surfaces: Hilbert–Burch near-balance `ι ≤ 1`, the dependent-stack bad-count
ceiling, and the union-rank `hrank` obligation. PR #5 narrows the first surface by proving that the
first balanced middle slot is linear-cofactor and by finding a reproducible on-domain occupant;
it does not lift that occupant to an over-budget MCA stack. PR #7 proves an all-depth cyclic energy
**lower** floor, and the G330 port proves an exact small spectrum-collision boundary away from
`p = 17`; neither supplies the missing production upper/cancellation input. See dossier v4 for the
claim-by-claim evidence ledger.

Historical issue numbers in the sections below (#357, #371, #389, #444, #466, and #499–#509)
identify the ArkLib campaign provenance. They are not current routing instructions.

## The boundary-band solution (2026-06-12, #371 rounds 64–75)

The deepest radius band before capacity (`k < (1−δ)n ≤ k+1`) is **solved
exactly**, and every band of the above-Johnson regime carries proven two-sided
bounds.  The file chain (all axiom-clean, in `ArkLib/Data/CodingTheory/ProximityGap/`):

| Result | File |
|---|---|
| Bad set = residual-ratio image (exact, both inclusions) | `BoundarySliceExact.lean` |
| Schur-ladder law: ladder bad set = −(subset sums) | `LadderSchurReduction.lean` |
| Master modular reduction: census = arithmetic in `F[X]/P_S` | `ResidualModularReduction.lean` |
| Strong farness is FREE for degree-`k` directions | `BoundarySliceUnconditional.lean` |
| Subset sums = signed sums (antipodal reduction, both ways) | `LadderSpectrumFusion{,Exact}.lean` |
| **Exact ladder count** `= Σ_{a∈A(h,k+1)} 2^a·C(h,a)` | `LadderSpectrumFusionValue.lean` |
| Ladder ≤ spectrum at every radius below capacity | `FullBandLadderLaw.lean` |
| Ratio functionals pairwise distinct (Lagrange/Vandermonde) | `GenericFarSeparation.lean` |
| **Generic-far pin**: `∃ stack, #badSet = C(n,k+1)` (`C(n,k+1)² ≤ q`) | `GenericFarPin.lean` |
| **Universal bound**: `#badSet ≤ C(n,k+1)`, ALL stacks, ALL radii | `UniversalBoundaryBound.lean` |
| Ladder cliff (`= 0` below band) + band packing law | `BandPackingLaw.lean` |
| Band attainment + two-sided bracket at every band | `BandAttainment.lean` |

Solved landscape (final, rounds 64–80): boundary band sup `= C(n,k+1)`
(attained + universal) and production boundary failure `ε_mca ≈ 1`
unconditionally (`ProductionBoundaryFailure.lean`); ladder curve exact at all
radii; band `m ≥ 1` bracketed `[⌊(n−k)/(m+1)⌋, C(n,k+1)/C(k+m+1,k+1)]`
(`BandAttainmentChained.lean`), witness-mass dense (`DeepBandCoherence.lean`),
multiplicity-reduced to the named `ExplainableCoreSupply`
(`DeepBandMultiplicity.lean`) with the supply proven above the wall
(`ExplainableCoreSupplyInstance.lean`).  #371 is CLOSED (consolidated
2026-06-12); the single remaining statement — the sub-Johnson supply wall,
quantitatively the classical RS list-size question — is tracked at **#389**
with the reduction chain and both recorded attack routes.

**2026-06-13 — the shallow supply is two-regime (the two-branch countermodel).**
The universal mean-degree law (`Σ a_c ≤ 2n`) is REFUTED in Lean
(`TwoBranchSupplyCountermodel.lean`, `universalMeanDegreeLaw_REFUTED`): the
two-branch parabola word (`x²` on `A`, `x²+c` on `B`) is agreement-capped by
theorem yet carries `428 > 2n = 160` mass at `(q,n) = (101,80)` — prime field,
`n < q`, no subfield structure.  Corrected named targets:
`CappedSupplyTwoRegimeLaw` (prime, calibrated `C₀ ≤ 1.91`, false over extension
fields by subfield transport) and `SmoothDomainTwoRegimeLaw` (μ_n production
form).  SS13 free-domain asymptotic red-team recorded.

**2026-06-13 — the all-`k` power-word list is exactly a zero-sum fiber.**
`PowerWordListBound.lean` proves the exact list identity
`powerWord_list_eq_sumZero`: for `w(x)=x^(k+1)`, the codewords of `rsCode dom k`
with agreement at least `k+1` are counted exactly by `(k+1)`-subsets of the
domain whose sum is zero.  The proof combines the Vieta coefficient cancellation
`coeff X^k = -ΣT`, the converse root-rigidity argument, and a root-count cap
showing no listed codeword can agree on more than `k+1` points.  This identifies
the `m=0` supply obstruction as a higher zero-sum/additive-energy fiber and links
directly to the `EsymmFiber.lean` deep-band target (`e_1 = ... = e_(m+1) = 0` for
`W=X^(k+m+1)`).  See
[`docs/kb/deltastar-powerword-zero-sum-law-2026-06-13.md`](../kb/deltastar-powerword-zero-sum-law-2026-06-13.md)
for the ten-connection research note and next formal targets.


### Reproducing the Paley constant table

With NumPy and SymPy installed, run
`python3 scripts/probes/probe_paley_C_table.py 8 16 32 64 128`.
The supported sizes are powers of two from 8 through 256. The script rejects
unsupported sizes and fails if a published prime or numerical row disagrees,
in addition to checking Parseval and the fourth moment. Large sizes take
substantially longer because every nonzero frequency is scanned.
