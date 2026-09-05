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
  this residual discharged. The distinct `Hyb01StepResidual` distribution/TV
  switch does not follow merely from the event-probability bound. A fresh
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

`lakefile.toml` still pins forks of VCV-io and CompPoly, requires fork-only PolyFun,
and pins doc-gen4 to `v4.30.0-rc2`. Replacing those pins without porting the APIs is
not a completed migration. A proposed upstream change must establish compatible
pins, compile the full proposed dependency closure, and exclude campaign workflows
and research-only changes. No upstream PR or dependency port is claimed here.

The remaining mathematical obligations and upstream preparation must remain
tracked if the historical cleanup ledger is consolidated or closed.

## Validation

The renamed BCS source and relocated Fold source both pass `lake env lean`
against the existing dependency environment. The BCS file reports only standard
axioms in its explicit audit outputs. Umbrella import regeneration/check passes;
no default campaign import changed. The fresh residual census agrees with the
checked-in totals. These focused checks do not claim a full unrelated-protocol
build or discharge any registered external assumption.
