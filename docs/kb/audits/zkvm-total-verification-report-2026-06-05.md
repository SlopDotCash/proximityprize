# ArkLib / ZKVM Total Verification Status Report

Date: 2026-06-05

Scope: local checkout at `/home/shaw/ethereumroadmap/upstream/lean-research/ArkLib`, comparing
`lalalune/ArkLib` `fork/main` / local `main` against `Verified-zkEVM/ArkLib` `origin/main`.

## Executive Summary

ArkLib is not, by itself, a whole zkVM verifier. It is a Lean 4 library for formally verifying
SNARK / argument-system components: interactive oracle reductions, protocol specifications,
completeness, soundness, and round-by-round knowledge soundness. A whole zkVM being "formally
verified in totality" additionally requires verified instruction semantics, arithmetization,
memory/lookups/permutations, implementation equivalence, transcript/hash/commitment bindings,
recursion/aggregation, and on-chain verifier correctness.

The `lalalune/ArkLib` fork represents a major expansion over upstream `Verified-zkEVM/ArkLib`.
At the time of inspection, local `main` tracked `fork/main` at commit `cad49a13a`, with additional
local proof-wrapper edits under review, and was roughly `2,983` commits ahead of `origin/main`, with
approximately `78k+` insertions and `5k+` deletions across `334+` files. The fork grows the Lean
source tree under `ArkLib/` from `205` Lean files upstream to `359+`, while a filtered executable
`sorry` scan drops from roughly `236` unresolved proof placeholders upstream to roughly `97-113` in
the fork depending on the scan filter.

Validation status: `./scripts/validate.sh` completed the Lean build successfully, but exited nonzero
because the Data warning budget found `52` ArkLib/Data non-sorry warnings. Therefore the fork is
buildable but not routine-validation clean.

## Public Project Context

The upstream README says ArkLib aims to provide a modular and composable framework for formally
verifying succinct non-interactive arguments of knowledge. Its first-stage plan is to formalize
interactive oracle reductions and prove completeness and soundness for selected protocols. It also
states that functional equivalence between executable specs and extracted Rust implementations is
future work.

The public ArkLib site similarly describes ArkLib as a framework for formally verifying SNARKs.
The broader Verified zkEVM project has separate tracks for RISC-V zkVM arithmetization, EVM-on-RISC-V
correctness, and cryptography; ArkLib belongs primarily to the cryptography/proof-system track.

Primary public sources:

- <https://github.com/Verified-zkEVM/ArkLib>
- <https://github.com/lalalune/ArkLib>
- <https://verified-zkevm.org/>
- <https://verified-zkevm.github.io/ArkLib/>

Primary local sources:

- `README.md`
- `docs/project/roadmap.md`
- `docs/wiki/proximity-prize-leaderboard.md`
- `docs/kb/audits/proximity-prize/GRIND-LEDGER.md`
- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
- `docs/kb/audits/gh-issues-campaign-2026-06-04.md`

## What Upstream Verified-zkEVM ArkLib Had Already Done

The upstream repository already contains the core ArkLib architecture:

- Interactive Oracle Reduction framework.
- Protocol specification machinery.
- Composition and lifting interfaces.
- Active proof-system directories for Sumcheck, Spartan, Merkle trees, FRI and coding-theory
  prerequisites, STIR, WHIR, and Binius.
- Blueprint/docs infrastructure.
- Dependency integration with mathlib and VCV-io.

This constitutes substantial infrastructure for formally verified proof systems, but not an
end-to-end zkVM verification.

## What `lalalune/ArkLib` Added

The fork adds a large proof/discharge campaign and research integration layer:

- About `31k` insertions across proximity/list-decoding/ToMathlib/audit files.
- About `26.5k` insertions across proof-system and oracle-reduction files.
- About `5k` insertions across commitments, hash, lattice, constraint-system, and Plonk-related files.
- A paper-to-Lean ABF26 audit.
- A proximity-prize bits-of-security leaderboard.
- BCIKS20 / Guruswami-Sudan / correlated-agreement bridge lemmas.
- Kernel-clean supporting bricks around beta recursion, Hensel/power-series material, coefficient
  extraction, degree calculus, matching extraction, and related ToMathlib facts.
- Substantial work in Binius, RingSwitching, Sumcheck, Logup, WHIR, STIR, ToyProblem, and
  OracleReduction composition/lifting.
- New support infrastructure in domains, coding theory, probability, polynomials, commitments,
  lattices/Ajtai, Merkle batching/extraction/hiding, and constraints.

The executable-placeholder picture improved materially: despite adding `154` Lean files under
`ArkLib/`, filtered executable `sorry` uses dropped from roughly `236` to roughly `97`.

## Proximity Prize Status

The local proximity-prize ledger records a bottom-up effort to close the BCIKS20 section 5
list-decoding / correlated-agreement keystone, specifically the route to
`correlatedAgreement_affine_curves`.

The honest current status from the ledger:

- There are `29` genuine kernel-clean supporting bricks after excluding a false-positive capstone.
- `KeystoneCapstone.lean` was audited and found to be only a bundling wrapper, not a real composition
  of the beta construction. It must not be counted as keystone completion.
- The attack-to-soundness route for the proximity-prize leaderboard is substantially real:
  `ToyProblem.simplified_iop_soundness_ca_lb` and `ToyProblem.epsCA_le_winningSetSoundness` are
  recorded as sorry-free / axiom-clean in the audit notes.
- The current leaderboard frontier is approximately a 64-bit provable lower side versus a
  116-bit attack upper side, leaving a 52-bit gap at the documented anchor.
- The Grand MCA Challenge and Grand List-Decoding Challenge are present as Lean predicates /
  framework objects, but their resolutions remain open research.

Update from the 2026-06-05 swarm audit: the conditional assembly
`betaRec => CurveCoeffPolys` is already present as the genuine theorem
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` in
`ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean`. It is not merely a wrapper around
`hcoeffPoly`; it routes through `tail_zero_of_betaRec_embedding_zero`,
`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large`,
`alphaFromBeta`, and `curveCoeffPolys_of_linear_representative`. The remaining
keystone work is to supply the theorem's explicit section-5 extraction/setup
hypotheses and connect them to the in-place `Curves.lean` theorem.

Remaining work for the proximity-prize keystone:

1. Supply the remaining `curveCoeffPolys_of_betaRec` hypotheses upstream:
   matching-point data, matching-set cardinality / weight bound, `gamma`
   representative data, degree-X bound, and decoded-family specialization bridge.
2. Discharge residual `Hlift H ∣ R`.
3. Fix the `gamma` recentering bug for `x0 != 0`.
4. Replace the trivial `beta_regular` with `betaRec`.
5. Supply `hcoeffPoly` to the relevant `Curves.lean` front doors.
6. Close the in-place `correlatedAgreement_affine_curves`.
7. De-taint STIR/WHIR/FRI downstream uses.
8. Resolve or improve the Grand MCA / List-Decoding research challenges to close the prize gap.

## Remaining Work For ArkLib Completion

ArkLib cannot be considered complete until at least the following are true:

- No executable `sorry` / admitted internal theorem remains in the trusted closure, except deliberately
  accepted external paper assumptions with clear boundaries.
- Validation is green, including warning budgets.
- OracleReduction composition/lifting design gaps are resolved.
- BCS and Fiat-Shamir transformations are fully specified and proved at the required abstraction level.
- Commitment schemes, Merkle batching/extraction/hiding, and random-oracle collision layers have
  complete soundness/security proofs.
- Sumcheck, FRI, STIR, WHIR, Binius, RingSwitching, Logup, Spartan, Plonk, and toy protocols have
  complete executable specs plus completeness and soundness / knowledge-soundness proofs.
- External admits and conjectural results are either discharged, explicitly imported as trusted paper
  assumptions, or factored out of the claimed theorem closure.
- Functional equivalence between ArkLib executable specs and real implementations is proved for the
  protocols claimed as verified.

## Remaining Work For Whole-ZKVM Total Verification

A whole zkVM "formally verified in totality" requires work beyond ArkLib:

- Verified instruction-set semantics, likely RISC-V Sail alignment for a RISC-V zkVM.
- Verified arithmetization: polynomial constraints exactly encode instruction semantics.
- Verified memory model, lookups, range checks, permutations, and table constraints.
- Verified finite-field/hash/commitment implementations.
- Verified Fiat-Shamir transcript generation and challenge derivation in implementation code.
- Verified prover/verifier implementation equivalence to the mathematical specs.
- Verified recursion/aggregation if used.
- Verified on-chain verifier and serialization/deserialization.
- End-to-end theorem connecting accepted proof to correct VM execution and public outputs.

## Percentage Estimates

These estimates are judgment calls, not mechanically derivable metrics.

### Upstream Verified-zkEVM ArkLib Before The Fork

Estimated completion:

- `~25%` of the ArkLib cryptography/proof-system library needed for a complete ArkLib.
- `~5-8%` of a whole zkVM being formally verified in totality.

Reasoning: upstream had substantial architecture and active formalization surfaces, but many open
proofs, roadmap items, and no full implementation-equivalence or whole-zkVM story.

### Increment Added By `lalalune/ArkLib`

Estimated added completion:

- `+25-30` percentage points toward ArkLib/proximity/proof-system completion.
- `+5-8` percentage points toward whole-zkVM totality.

Reasoning: the fork roughly doubles the Lean source surface, substantially reduces filtered
executable `sorry` count, adds major proximity-prize and proof-system material, and documents the
remaining frontier precisely. But it still has unresolved executable `sorry`s, external admits,
validation warnings, and open research gaps.

### Current Local `lalalune/main`

Estimated current completion:

- `~50-55%` complete for ArkLib as a cryptographic proof-system verification library.
- `~12-16%` complete for an end-to-end zkVM formally verified in totality.
- `~65-70%` complete for proximity-prize formalization infrastructure.
- `~45-55%` complete for the proximity prize actually being finished.

Reasoning: the current tree builds and contains many kernel-clean proof bricks, but remains short
of validation cleanliness and complete theorem closure. For the prize, the formal scaffolding and
attack route are strong, but the central keystone assembly and Grand MCA/List-Decoding challenges
remain open.

### Remaining Work

Estimated remaining:

- `~45-50%` of ArkLib completion.
- `~84-88%` of whole-zkVM total verification.
- `~30-35%` of proximity-prize formal infrastructure, plus open research for the actual prize gap.

## Evidence Commands Run

Representative commands used during this audit:

```bash
git status --short --branch
git remote -v
git fetch origin main
git fetch fork main
git rev-list --left-right --count origin/main...fork/main
git diff --stat origin/main..fork/main
git diff --name-status origin/main..fork/main
git diff --shortstat origin/main..fork/main -- ArkLib/Data/CodingTheory/ProximityGap ArkLib/ToMathlib docs/kb/audits/proximity-prize docs/wiki/proximity-prize-leaderboard.md
git ls-tree -r --name-only origin/main ArkLib | rg '\.lean$' | wc -l
git ls-tree -r --name-only fork/main ArkLib | rg '\.lean$' | wc -l
git grep -n -E '(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)' origin/main -- ArkLib '*.lean'
git grep -n -E '(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)' fork/main -- ArkLib '*.lean'
./scripts/validate.sh
```
