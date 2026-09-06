# Axiom and Shortcut Audit - 2026-06-11

This note records the clean `origin/main` audit after the 2026-06-11
shortcut sweep. The goal was to find raw axioms, bodyless opaque/constant
declarations, live holes, theorem-shaped `True` placeholders, residual
`def : Prop` obligations, Prop-valued residual classes, and other vacuous
shortcut surfaces.

## Summary

- Residual census on clean `origin/main`: 108 total residuals, 26 open,
  82 discharged.
- Targeted shortcut scan found no live `def ... : Prop := True`,
  theorem/lemma `: True`, BCS realization `:= True`, Binius residual class, or
  `localChecks := True` debt on clean `origin/main`.
- The only Prop-valued classes found on clean `origin/main` are normal
  lawfulness/coherence classes:
  - `Serialize.IsInjective` (`ArkLib/Data/Classes/Serde.lean:28`)
  - `AppendCoherent`
    (`ArkLib/OracleReduction/Composition/Sequential/Append.lean:331`)
  - `DuplexSpongeFS.IsLawful`
    (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:172`)
- Local full-tree `python scripts/forbidden_tokens.py` timed out on this
  Windows worktree; the focused stale-branch findings were rechecked against
  clean `origin/main` before filing or closing issues.

## Open Residuals

### Proximity / List Decoding

#354 tracks the remaining AGL24 union-bound residual:

- `AGL24.RIMFullRankFailureProbResidual`
  (`ArkLib/Data/CodingTheory/AGL24UnionBound.lean:79`)

#334 tracks the GKL24 witness-cover residuals:

- `ProximityGap.GKL24MaxCorrStrictWitnessCoverResidual`
  (`ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean:1309`)
- `ProximityGap.GKL24MaxCorrWitnessCoverHypothesis`
  (`ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean:1330`)
- `ProximityGap.GKL24PetalWitnessCoverHypothesis`
  (`ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean:1412`)
- `ProximityGap.Issue67Scratch.GKL24MaxDomainWitnessCoverResidual`
  (`ArkLib/Data/CodingTheory/Connections/GKL24PetalWitnessCover.lean:56`)

#304 tracks the BCIKS20 residual cone:

- `ProximityGap.StrictCanonicalCoeffPolysResidual`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:2528`)
- `ProximityGap.RSCurveListSizeResidual`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/ListSizeResidual.lean:45`)
- `BCIKS20.HenselNumerator.βHenselSuccTermWeightResidual`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:1598`)
- `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchResidual`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2MatchProof.lean:30`)
- `ProximityGap.StrictCoeffPolysExcResidual`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/StrictCoeffPolysExceptional.lean:157`)

### OracleReduction Append

#340 tracks the two remaining append knowledge-soundness residuals:

- `Verifier.appendKnowledgeSoundnessResidual`
  (`ArkLib/OracleReduction/Composition/Sequential/Append.lean:996`)
- `OracleVerifier.appendKnowledgeSoundnessResidual`
  (`ArkLib/OracleReduction/Composition/Sequential/Append.lean:1184`)

### Duplex Sponge Fiat-Shamir

#316 tracks the open duplex-sponge Fiat-Shamir residuals:

- `DuplexSpongeFS.BirthdayBound.Lemma5_8EagerBirthdayResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BirthdayBound.lean:470`)
- `DuplexSpongeFS.KeyLemmaResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemma.lean:245`)
- `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_14HonestResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:647`)
- `DuplexSpongeFS.KeyLemmaFoundations.KeyLemmaEagerResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean:966`)
- `DuplexSpongeFS.KeyLemmaHybrids.Hyb01StepResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaHybrids.lean:709`)
- `DuplexSpongeFS.KeyLemmaHybrids.Hyb12StepResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaHybrids.lean:731`)
- `DuplexSpongeFS.KeyLemmaHybrids.Hyb23StepResidual`
  (`ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaHybrids.lean:754`)

### Proof Systems

- #341 tracks FRI query-round residuals:
  - historical false surface:
    `Fri.Spec.Completeness.queryRoundPerfectCompletenessFalseAsStated`
    (`ArkLib/ProofSystem/Fri/Spec/Completeness.lean:51`)
  - `Fri.Spec.Completeness.queryRoundChainDeliveryHypothesis`
    (`ArkLib/ToMathlib/FriCompleteQueryRound.lean:177`)
- #337 tracks the remaining Logup residuals:
  - `Logup.LogupSoundnessFullResidual`
    (`ArkLib/ProofSystem/Logup/Security/LogupSoundnessClose.lean:180`)
  - `Logup.LogupSoundnessUncondResidual`
    (`ArkLib/ProofSystem/Logup/Security/LogupSoundnessUncond.lean:249`)
  - `Logup.AppendCompletenessResidual`
    (`ArkLib/ProofSystem/Logup/Security/SubPhaseSplit.lean:183`)
- #347 tracks `StirIOP.MultiRound.stirMultiRoundRbrSoundnessResidual`
  (`ArkLib/ProofSystem/Stir/MultiRoundAssembly.lean:224`).
- #302 tracks the WHIR/MCA residuals:
  - `MutualCorrAgreement.K4GradedFactorCellResidual`
    (`Research/ProximityPrize/Protocols/Whir/MCAJohnsonBound.lean:46`)
  - `MutualCorrAgreement.K4ComponentResidual`
    (`Research/ProximityPrize/Protocols/Whir/MCAJohnsonBound.lean:64`)

## Closed Stale Findings

The initial scan was run from a dirty branch that was 750 commits behind
`origin/main`. Rechecking against clean `origin/main` showed these shortcut
findings had already been resolved, so their issues were closed or corrected:

- #342: no BCS `interaction_realizes_oracle_messages := True` /
  `opening_realizes_query_log := True` hits remain on clean main.
- #343: `FoldedStackOfRound : Prop := True` is no longer present on clean main.
- #344: no `localChecks : Prop := True` / `localChecks := True` hits remain on
  clean main.
- #345: `ArkLib.ZkVMBoundary.WholeZkVMResidual` is not open in the clean-main
  residual census.
- #346: `CodingTheory.randomRSListDecodingFirstMomentResidual` is not open in
  the clean-main residual census.
- #347: `StirIOP.MultiRound.stirMultiRoundRbrSoundnessResidual` is not open in
  the latest rebased clean-main residual census.
- #352: `Spartan.Spec.Bricks.composedCompletenessWithClaimValueRelResidual` is
  not open in the latest rebased clean-main residual census.
- #317/#338 received correction comments: Binius residual classes and
  RingSwitching/Binius `localChecks := True` hits were stale dirty-branch
  findings, not clean-main findings.

## Follow-Up Rules

1. Run `python scripts/residual_census.py` after each residual-closing patch and
   confirm the open count decreases.
2. Avoid raw `axiom`, bodyless `opaque`/`constant`, `native_decide`,
   `bv_decide`, theorem-shaped `: True`, and residual-like
   `def ... : Prop := True` declarations.
3. Add focused `#print axioms` checks for promoted theorem surfaces, allowing
   only `propext`, `Classical.choice`, and `Quot.sound`.
