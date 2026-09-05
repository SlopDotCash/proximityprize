# Issue #2 quality and upstream audit

Audited against `a6475f7c0` on 2026-09-05. This page records source inspection;
it does not certify the security of the retained protocol experiments.

[Issue #2](https://github.com/SlopDotCash/proximityprize/issues/2) began as a
historical ArkLib fork cleanup plan. Its migration note and the repository README
establish this standalone repository as the campaign home. Moving that campaign
out of the default library is superseded; the mathematical and upstream work
below is not silently declared complete by that migration.

## Completed bounded quality work

- Retired the three unused `CommitmentScheme` compatibility shims. Moved the
  remaining folding import surface to `Commitments/Functional/Fold.lean`. No
  tracked Lean source imported any of the four retired modules.
- Renamed `ArkLibScratch.Issue62` to `BCS.ErrorAccounting`. There were no qualified
  references outside its defining file; declarations and proofs are unchanged.
- Made all nine retained axiom entries in `scripts/residual_axioms.txt` point to
  the live issue #2 §3.1, preserving their historical ArkLib #470 provenance.
  This implements the explicitly permitted documented-external-assumption route;
  none of these axioms is proved by registration. The flagship axiom audit still
  rejects custom axioms in its theorem dependency closures.

## Registered external assumptions

| Source under `ArkLib/` | Explicit unproved assumptions |
|---|---|
| `Data/CodingTheory/ProximityGap/BCIKS20/WeightedAgreement.lean` | `weighted_correlated_agreement_for_parameterized_curves`, its primed variant, `weighted_correlated_agreement_over_affine_spaces`, its primed variant |
| `Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean` | `large_agreement_set_on_curve_implies_correlated_agreement` and its primed variant |
| `ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean` | `foldKnowledgeStateFunction_toFun_full`, `foldOracleVerifier_rbrKnowledgeSoundness` |
| `Data/Lattices/CyclotomicRing/Subfield/Field.lean` | `no_selfReciprocal_factor` |

These entries are proof debt, not standard Lean foundational axioms. Downstream
results depending on them remain conditional on their truth.

## Remaining proof and refactor work

- The strict [residual census](residual-census.md) classifies syntactic residual
  declarations; it does not certify every named `Prop` or structure hypothesis.
  A fresh run on the audited tree confirms 117 strict declarations: 69 open, 47 discharged,
  one refuted. A refuted statement must not be treated as a theorem to prove.
- DuplexSponge has genuine progress beyond the historical blanket description:
  `ConsistencyPaperCascade.lean` supplies the 5.12 and 5.16 honest-paper providers,
  and `Lemma514PaperFork.lean` supplies the 5.14 provider.
  `Lemma58Reduction.lean` also supplies `lemma5_8EagerPaperResidual_holds`
  and unconditional honest-birthday/Claim 5.21 bounds, under its finite,
  decidable and sampleable type instances. The checked-in census already marks
  this residual discharged. `KeyLemmaSalted.lean` records the historical unsalted
  Hyb01/Hyb34 switches as refuted by endpoint log-shape mismatch and introduces
  the salted successor `Hyb01StepResidualS`. A distribution/TV switch does not
  follow merely from the event-probability bound. A fresh
  dependency-closed Lean audit is still needed before claiming full Fiat–Shamir
  security or upstream readiness; absence of the 5.8 provider is not a blocker.
- [Binius Closeout Audit](Binius_Closeout_Audit.md) explicitly records the stale
  Relations/ReductionLogic/QueryPhase/Soundness/reconstruction strata and external
  composition hypotheses. Its buildable front doors are lightweight import
  surfaces. Grant closeout is not an unconditional full-security proof.
- The three historical Binius hotspot files now contain zero `TODO`, `FIXME`, or
  `WIP` tokens; this textual cleanup does not remove the documented proof boundaries.
- Consolidating 33 BinaryBasefold soundness and 52 sequential Append modules, reviewing
  shared Data and ToMathlib candidates, and the kept-surface comment pass still
  require dependency-aware review and validation. File counts alone do not justify
  deleting proved results or moving interfaces during an active campaign.

## Upstream carve-out remains separate work

`lakefile.toml` still pins forks of VCV-io, CompPoly, and PolyFun,
and pins doc-gen4 to `v4.30.0-rc2`. Replacing those pins without porting the APIs is
not a completed migration. A proposed upstream change must establish compatible
pins, compile the full proposed dependency closure, and exclude campaign workflows
and research-only changes. A repository-wide dependency port is not established
by this audit.

The remaining mathematical obligations and upstream preparation must remain
tracked if the historical cleanup ledger is consolidated or closed.

## Current upstream dependency comparison

The upstream manifest at `a527b514e029ecf9da40d66b5531a0707c686edc` was checked
on 2026-09-05 against the standalone manifest at
`fae76897ba7250a966a06d7e4a5627f38f46398f`. Upstream uses Lean `v4.33.1`;
the standalone repository still uses `v4.30.0-rc2`.

| Package | Standalone resolved revision | Upstream resolved revision |
| --- | --- | --- |
| VCVio | `lalalune/VCV-io`, `576766ab24a044af560b05c58d2a1229857c7c07` | `Verified-zkEVM/VCVio`, `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` |
| CompPoly | `lalalune/CompPoly`, `d8d6609e179fc26c4c56e1dae7c37032d618ad73` | `Verified-zkEVM/CompPoly`, `a09455a22fea4623a2a1c5b363cf6efc61486a83` |
| PolyFun | `lalalune/PolyFun`, `5d3a160ed751b9227af90adb9da41d0eae2e0238` | `Verified-zkEVM/PolyFun`, `c0c923693fc827a41d17116579a0c16ed4873b19` |
| doc-gen4 | `d555f83e82831466ec101c9753450e8b4ec203b4` (`v4.30.0-rc2`) | `e2af49a7b7e5e1a9224008c1f15e7aa4f58a4015` (`v4.33.1`) |

PolyFun is therefore no longer an absent upstream package. The pinned upstream
[VCVio lakefile](https://github.com/Verified-zkEVM/VCVio/blob/f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24/lakefile.lean)
requires the official PolyFun repository transitively. The remaining work is
API compatibility and validation of each proposed contribution, not introducing
PolyFun to upstream for the first time. The standalone pins have not changed.

All project pushes and pull requests target `SlopDotCash/proximityprize`.
`Verified-zkEVM/ArkLib` is a read-only comparison source, not a submission
destination. Historical upstream carve-out plans do not authorize publication
there. The mistakenly submitted upstream PR #860 is closed.

The standalone main revision `6b46efb4dcdd1d111100d103425ae81f5de27326` already
contains the positional `Fin.castSum`/`Fin.sumCases` API, `Fin.induction_four`
helpers, the four heterogeneous tuple equalities, and
`ToMathlib/CyclotomicPatternInjectivity.lean`. Copying those results into another
repository is not remaining work for issue #2. Their presence does not discharge
any conditional protocol security result.

## Shared-data review: Vandermonde

`ArkLib/Data/Matrix/Vandermonde.lean` needs no mathematical carve-out at the
reviewed revisions: upstream `a527b514e029ecf9da40d66b5531a0707c686edc` and
standalone `6b46efb4dcdd1d111100d103425ae81f5de27326`. Removing comments and import
lines yields identical token sequences, so all declaration statements and proof
bodies already occur upstream. The differences are the module documentation and
an import route (`CodingTheory.Basic.LinearCode` upstream versus
`MvPolynomial.LinearMvExtension` standalone). This comparison does not propose
changing either import graph and does not require a duplicate upstream PR.

## Validation

The renamed BCS source and relocated Fold source both pass `lake env lean`
against the existing dependency environment. The BCS file reports only standard
axioms in its explicit audit outputs. Umbrella import regeneration/check passes;
no default campaign import changed. The fresh residual census agrees with the
checked-in totals. These focused checks do not claim a full unrelated-protocol
build or discharge any registered external assumption.
