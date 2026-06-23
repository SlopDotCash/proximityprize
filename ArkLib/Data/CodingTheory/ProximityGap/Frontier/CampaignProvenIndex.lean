/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B2_char0_logconcave
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B5_MomentProblemLogConvex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B6_cumulant_signs
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B8_kstability_char0_closure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B9_GaussianConvexOrderExtremal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6P1_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL3_char0_prize_moment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL4_char0_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G2_ResonanceCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G3_periodpoly_coeff_nogo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G4_roughness_not_the_driver
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeOneWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCorridorIcc
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoTighterBoundCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawFamilyReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteTrivialCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteBGKCompletionCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueBracketCenter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPWraparoundLogConcaveQ
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPStepRatioMonotoneFails
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RhoAntitoneFailsThinPrime
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVValueShiftHistogramObstruction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WraparoundMarkovVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVIndexFactorOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceOrderBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBSidonNoEnergyExcess
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeBddAbove
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeShawTetrachotomySynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitQuantitative
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultiPieceDeficitQuantitative
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitPairwiseSandwich
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueLandauBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCocycleNoRandomEdge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVJointFieldWhite
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDoorIVCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentTrappedCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeObjectGrandCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignedDeepSumAbsLeak
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignedDeepRigidityCorner
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodMomentCensus
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleTrivialOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleAllDefectCSVacuous
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvGR_GaussSumEnergyStep
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDil_MultEnergyStepDiagonal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreReductionNecessity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDecompositionInvariantCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultiPieceSignCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultiPieceSameRayConverse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSixthCumulantVanishes
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTripleCorrelationVanishes
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCorrelationHierarchyCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCumulantLadderVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCrossHalfPhaseUnstructured
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassBalanceAtArgmax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassDilationForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignCocycleMassBalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVAlgebraicFloorCyclotomicWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVEighthCumulantSignUnstable
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedPrizeReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedTelescopeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatePrizeBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPerLevelFactorSubTwo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedBaseThresholdConcrete
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstCosetCountSingleton
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawGrandSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawScaleDoorScaleBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawGapDriftContrapositive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawGapBddAboveNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GKPhaseCoboundaryNonLinear
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AttackMarkoffCouplingNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvTannakianNonTorsionPump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBHalfMassCarriesAll
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVZDegreeEnvelope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWeight2QuadformGcd
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWindowConcentrationTrivial
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVArgmaxDecouplingNoControl
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCollisionExcessPigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceSaturationInsufficient
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVFractionalMomentNoMaxGain
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVGeomMeanBelowMax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPhaseBlindRadialStats
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOrderedWalkDoobMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StepanovAtBstar
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOrderedWalkMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDIR9OrderedWalkMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDIR9ReflectionSteinitz
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacAutocorrL2SupGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvERG_ErgodicMaximalReducesToWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_ResonatorRatioLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_MomentRatioLadderGeneral
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SumProductCensusStallBeta4
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RudnevDilutionFixedSavingStall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitThicknessInvariant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceSlackVacuousAtArgmax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVComplexRayCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCommonRayCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCosetHalfCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSectorCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCanonicalHalfCoherenceQuantized
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassFactorization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTransverseSpread
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealPieceCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealSignMassSlack
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealPieceCompression
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultShiftCollinear
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoPieceAngularDeficit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVUnitPieceDeficit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBNonNested
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A1SOSLadderN16
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A3SumProductDepthConfinement
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A5TwistedMonodromyAbelianVerdict
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_JacobiEdgeBoundedSupportCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_HermiteTurnoverReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_TurnoverSupportGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvJB_HankelRoutesToMoments
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NonTensorWrapCrossResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceLogLocalizedOffDiagonal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HDCocyclePhaseCoupling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A2OnsetLatticeMinimum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WraparoundSaddleCreditForced
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OnsetToSaddleCreditChain
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OrbitCountWallDichotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WorstBOrbitLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WorstBSetCosetClosed
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueScalarEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBCosetClosed
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseCoherentNonRealizable
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A10GrossKoblitzSizeL2NormBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvThaine_DCompositionPhaseBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCongruencePadicPhaseBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPerFrequencyLocalizationCollectiveOnly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPhaseSetDilationInvariant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstIndexDelocalized
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AttackB1_BadSetCosetNonSidon
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AntiConcKurtosisRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVNegationSymmetryRealAndBalanced
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVLargestGapEnergyBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBDyadicSelectorWalled
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvN4_PadicMahlerSupplyGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVQVCauchySchwarzCircular
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMartingaleInputCeilingCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstCosetIndexUnstructured
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstIndexMultGeneric
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoDilateNoJointExtreme
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceTowerTelescope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceTowerCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTowerSlackNonAssemblable
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentTelescope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationTowerSaturates
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationTowerConcrete
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBParticipationGeneric
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBCoherentImbalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBImbalanceBand
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBPartitionDepthBand
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBPerLevelGrowthFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPhaseCurvatureGeneric
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVGapNoLongRun
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVGapSpectrumFullRank
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVGreedyHeavierHalfDescent
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBSpikeMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVZLagrangeBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSpectrumRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorBadRamificationDisjoint
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorBadDefectTowerInvariant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceOffDiagSpikeCost
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerLogConvex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerRatioSpectralCap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDeficitBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVUniformDeficitThreshold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitBudgetSublinearFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitBudgetBoundedExceptions
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVLeadingZeroDeficitFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitSumScatteredFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVEvenMomentPhaseVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMixedConjugateMomentCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOddSignedMomentCauchy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMomentHierarchyEnergyDominated
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMomentEnergyFloorOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMomentFloorTetrachotomyBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupParsevalEnergyExact
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakBracket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupDCOffDCGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOffDCCeilingDominatesBGKTarget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCMeanFloorSharp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakFloorSharp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakBracketSharp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloorFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueBGKBracketFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueTwoSidedSharpCorridorFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeConstantSuperDiagonalFloorFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueSharpenedBGKCorridorFamily

set_option linter.style.longFile 9700

/-!
# Campaign-Proven Index — permanent named exports of the prize close-out (#444)

The #389/#407/#444 BGK / δ* campaign produced a large body of **axiom-clean** results in
fast-iteration scratch files (`Frontier/_wf*`). Those files are explicitly *throwaway*
(`Frontier/README.md`: "files starting `_` are throwaway"), yet several of their headline
theorems are load-bearing and proven. This module makes that proven content **permanent and
discoverable**: each load-bearing result below is re-exported under a stable, descriptively
named theorem in a non-underscore permanent module, carrying a docstring that states its
**scope** (`char-0` / `obstruction` / `prize-bridge`) and its axiom audit.

This is a **consolidation only** — no mathematics is changed. Every export here is a direct
alias of a proven theorem; the axiom audit at the bottom confirms the inherited profile is
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Scope tags

* **char-0** — proven unconditionally in characteristic 0 (the regime where the Lam–Leung /
  Wick energy law `E_r ≤ (2r-1)‼·n^r` is a theorem). These are the substrate the prize bridges
  consume; they do NOT by themselves resolve the prize (which needs the char-`p` transfer at
  `r ≈ ln q`).
* **obstruction** — an axiom-clean proof that a *named candidate lever* cannot reach the prize
  floor (a countermodel / no-go). These are permanent negative results.
* **prize-bridge** — an axiom-clean named-conditional reduction: `<named input> ⟹ prize bound`,
  with the named input the only remaining obligation.

The remaining open core (`BGKBound(1/2)`, the thin dyadic Gauss-period exponent-1/2
cancellation) is documented in `PROXIMITY_PRIZE_WORKBENCH.lean` and is NOT discharged by
anything here; this index does not claim otherwise.

## Index of permanent exports (by scope)

| export | scope | source brick |
|---|---|---|
| `char0_stepRatio_antitone_iff_sharpNewton` | char-0 | B2 |
| `char0_W3anti_of_sharpNewton_export` | char-0 | B2 |
| `char0_kstability_cross_le_wick` | char-0 | B8 |
| `char0_prize_moment_bound_unconditional` | char-0 | L3 |
| `char0_prize_moment_bound_sq_unconditional` | char-0 | L3 |
| `char0_nonprincipalEnergyBound_discharged` | char-0 | L4 |
| `char0_eta_pow_le_unconditional` | char-0 | L4 |
| `gaussian_moment_telescope` | prize-bridge | F1 |
| `convexOrder_gaussian_iff_wick_export` | prize-bridge | B9 |
| `prize_of_matchedGaussian_stepLaw_export` | prize-bridge | B9 |
| `eta_pow_le_of_nonprincipalEnergyBound_export` | prize-bridge | P1 |
| `moment_problem_does_not_give_wick_bracket` | obstruction | B5 |
| `cumulant_sign_route_refuted` | obstruction | B6 |
| `resonance_ceiling_below_prize_floor` | obstruction | G2 |
| `coeff_route_loose_export` | obstruction | G3 |
| `roughness_does_not_add_bad_primes_export` | obstruction | G4 |
| `prizeBound_iff_shawValue_le_export` | capstone | ShawValue |
| `rawPrizeFamilyBound_iff_shawValueFamilyBound_export` | capstone | ShawValue |
| `exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound_export` | capstone | ShawValue |
| `exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_export` | capstone | ShawValue |
| `strictPrizeBound_iff_shawValue_lt_export` | capstone | ShawValue |
| `strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `shawValue_worstPeriod_clean_corridor_export` | capstone | ShawValue |
| `shawValue_clean_corridor_width_eq_export` | capstone | ShawValue |
| `shawValue_bracket_width_eq_sqrt_export` | capstone | ShawValue |
| `worstPeriod_sharp_bracket_export` | capstone | ConcreteTrivialCeiling |
| `completion_vacuous_below_trivial_ceiling_export` | obstruction | ConcreteBGKCompletionCorridor |
| `shawValue_worstPeriod_torsion_full_corridor_export` | capstone | ConcreteShawCompletionCorridorFull |
| `worstPeriod_torsion_sharp_floor_export` | capstone | ConcreteShawCompletionCorridorFull |
| `charP_wrap_gap_ge_two_mul_sq_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_wrap_gap_nonneg_of_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_transfer_of_dominance_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_stepRatioMonotoneAt_iff_gap_nonneg_export` | obstruction | CharPStepRatioFails |
| `charP_stepRatioMonotone_false_n32_export` | obstruction | CharPStepRatioFails |
| `charP_no_universal_positive_stepRatioMonotone_export` | obstruction | CharPStepRatioFails |
| `rho_normalized_antitone_and_ceiling_incompatible_export` | obstruction | RhoAntitoneFails |
| `rho_antitone_route_not_universal_export` | obstruction | RhoAntitoneFails |
| `valueShift_nontrivial_forces_flat_histogram_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_step_zero_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_route_vacuous_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `wraparound_markov_count_le_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_markov_bound_vacuous_below_mean_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_average_control_does_not_bound_sup_export` | obstruction | WraparoundMarkovVacuity |
| `doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_index_le_sq_of_scaledConstant_le_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_scaledConstant_le_iff_index_le_sq_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_constant_lt_scaledConstant_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_not_scaledConstant_le_constant_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_constant_lt_scaledConstant_iff_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_cosetInvariant_blind_to_order_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_cosetHitting_selector_bound_iff_global_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_strict_selector_bound_misses_coset_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_positive_additiveEnergyExcess_iff_not_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_bddAbove_nonneg_normalizedPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_normalizedHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_rawPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_rawHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_nonneg_rawPrize_iff_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_prize_iff_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_halfMass_iff_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_prize_iff_not_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_halfMass_iff_not_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `shawOOne_bddAbove_range_shawValue_export` | capstone | ShawValueCapstone |
| `corePrize_bddAbove_range_shawValue_export` | capstone | ShawValueCapstone |
| `corePrize_bddAbove_range_shawValue_of_pos_lt_export` | capstone | ShawValueCapstone |
| `shawOOne_unbounded_shawValue_drift_export` | capstone | ShawValueCapstone |
| `corePrize_unbounded_shawValue_drift_export` | capstone | ShawValueCapstone |
| `corePrize_unbounded_shawValue_drift_of_pos_lt_export` | capstone | ShawValueCapstone |
| `doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_floorPrizeConstant_ge_one_export` | constraint | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_no_prize_iff_no_shawBound_nonneg_and_floorPrizeRatio_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_corePrize_of_dominated_majorant_export` | capstone | ShawValueCapstone |
| `doorIV_shawOOne_of_coreMajorant_export` | capstone | ShawValueCapstone |
| `doorIV_landau_shaw_of_dominated_majorant_export` | capstone | ShawValueLandauBridge |
| `doorIV_shawOOne_of_dominated_majorant_export` | capstone | ShawValueLandauBridge |
| `trivial_cocycle_full_concentration_export` | obstruction | JacobiCocycleDispersion |
| `trivial_cocycle_offSupport_zero_export` | obstruction | JacobiCocycleDispersion |
| `jacobiCocycleDispersion_iff_shawValue_le_export` | capstone | JacobiCocycleDispersion |
| `exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export` | capstone | JacobiCocycleDispersion |
| `doorIV_arithMean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_weightedMean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_weightedSubmean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_radialSum_invariant_under_unit_twist_export` | obstruction | DoorIVPhaseBlindRadialStats |
| `doorIV_stepanov_bstar_bound_export` | obstruction | StepanovAtBstar |
| `doorIV_bstar_saving_iff_degenerate_export` | obstruction | StepanovAtBstar |
| `doorIV_orderedWalk_endpoint_le_maximalExcursion_export` | obstruction | DoorIVOrderedWalkMajorant |
| `doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export` | obstruction | DoorIVOrderedWalkMajorant |
| `doorIV_avDIR9Reflection_endpoint_le_R_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_endpoint_id_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_bound_two_R1_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_reduces_export` | obstruction | AvDIR9Reflection |
| `doorIV_abs_signed_le_abs_moment_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_leak_nonneg_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_abs_moment_bound_transfers_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `trivial_cocycle_overshoots_thin_export` | obstruction | JacobiCocycleTrivialOvershoot |
| `trivial_overshoot_gap_pos_export` | obstruction | JacobiCocycleTrivialOvershoot |
| `allDefect_cs_floor_vacuous_export` | obstruction | JacobiCocycleAllDefectCSVacuous |
| `gaussEnergyStep_incrementOne_lt_two_n_export` | capstone | AvGR_GaussSumEnergyStep |
| `gaussEnergyStep_step_of_increments_le_export` | capstone | AvGR_GaussSumEnergyStep |
| `dilationEnergy_step_iff_offdiagonal_export` | capstone | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_deep_step_of_depth2K_energy_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_not_deep_step_of_offdiagonal_gt_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `coreReduction_mStar_gt_of_BCHKS_fails_export` | capstone | CoreReductionNecessity |
| `coreReduction_mStar_le_iff_BCHKS_export` | capstone | CoreReductionNecessity |
| `coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export` | capstone | CoreReductionNecessity |
| `doorIV_decomposition_block_sum_common_ray_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_decomposition_partition_invariant_coherence_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_decomposition_no_partition_beats_one_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_multiPiece_coherence_mem_Icc_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_exact_saving_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_eps_budget_eq_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_eps_budget_iff_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_no_eps_slack_one_side_zero_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiWindow_budget_forces_card_le_export` | obstruction | DoorIVWindowConcentrationTrivial |
| `doorIV_no_multiWindow_split_rhs_le_strict_budget_export` | obstruction | DoorIVWindowConcentrationTrivial |
| `doorIV_argmaxDecoupled_const_ge_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_control_below_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_uniformControl_iff_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_candidate_pos_on_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_positive_support_on_subset_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_control_constant_pos_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_nonpos_candidate_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_zero_candidate_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_candidate_pos_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_positive_support_subset_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_absolute_const_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_collision_defect_eq_zero_iff_injOn_export` | obstruction | DoorIVCollisionExcessPigeonhole |
| `doorIV_collision_defect_pos_iff_not_injOn_export` | obstruction | DoorIVCollisionExcessPigeonhole |
| `doorIV_tripleCorrelation_sixPoint_zero_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_tripleCorrelation_sixPoint_vacuous_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_tripleCorrelation_m33_eq_wick_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_crossHalf_norm_add_eq_halfMass_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_halfMassBalance_single_half_pays_floor_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_halfMassBalance_descent_loss_eq_two_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_halfMassBalance_descent_loss_le_two_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_worstB_coherent_imbalance_breaks_symmetric_descent_export` | obstruction | DoorIVWorstBCoherentImbalance |
| `doorIV_halfMass_eta_image_smul_eq_eta_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_eta_index_two_split_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_norm_eta_le_two_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_eq_two_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_norm_eta_eq_two_dilate_of_coherent_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_sign_positiveMass_eq_negativeMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_not_all_nonneg_of_positiveMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_exists_negative_cross_of_positiveMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_exists_positive_cross_of_negativeMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_positiveMass_le_half_card_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_negativeMass_le_half_card_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_positiveMass_eq_half_total_doublingMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_negativeMass_eq_half_total_doublingMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_gappedMinor125_159_eq_zero_export` | obstruction | DoorIVAlgebraicFloorCyclotomicWall |
| `doorIV_not_gappedMinor125_159_ne_zero_export` | obstruction | DoorIVAlgebraicFloorCyclotomicWall |
| `doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export` | obstruction | DoorIVEighthCumulantSignUnstable |
| `doorIV_eighthCumulant_no_fixedSignCertificate_export` | obstruction | DoorIVEighthCumulantSignUnstable |
| `doorIV_levelWorst_step_of_levelRatioBoundNZ_export` | capstone | DoorIVXGatedTelescopeBridge |
| `doorIV_levelWorst_le_sqrt2_pow_mul_of_levelRatioBoundNZ_export` | capstone | DoorIVXGatedTelescopeBridge |
| `doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export` | capstone | DoorIVXGatedPrizeReduction |
| `doorIV_levelWorst_le_prize_budget_of_xgate_export` | capstone | DoorIVXGatePrizeBudget |
| `doorIV_gateThreshold_split_telescope_sqrt2_export` | obstruction | DoorIVXGatedBaseThreshold |
| `doorIV_gateThreshold_strictly_above_clean_export` | obstruction | DoorIVXGatedBaseThreshold |
| `doorIV_levelWorst_base_step_two_export` | obstruction | DoorIVXGatedBaseThresholdConcrete |
| `doorIV_levelWorst_base_corrected_of_gate_export` | obstruction | DoorIVXGatedBaseThresholdConcrete |

## Lane-2 capstone (the `prize ⟺ Sh(n)=O(1)` normalization)

The **capstone** scope tag marks the Lane-2 deliverable of the door-(iv) phase (#444,
Shaw-value essay 2026-06-18): the axiom-clean reduction of the prize inequality to a bounded
normalized *Shaw value* `Sh(M) = M / √(n·L)`, together with the proven two-sided corridor
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on the REAL Gauss-period worst frequency `M(μ_n)`. The floor is
unconditional (thin-regime Parseval, `q ≥ 2n`); the ceiling is unconditional (triangle
inequality); the open prize is *exactly* the demand to collapse this `√n`-wide corridor to an
absolute constant. These are normalization/consolidation only — no anti-concentration, completion,
moment, or capacity claim is hidden, and CORE stays OPEN.
-/

open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex

open ProximityGap.PrizeWorkbench
open ArkLib.ProximityGap.Frontier
open Asymptotics Filter
-- `eta` (the subgroup Gauss-sum period) lives here; needed for the L4/P1 exports below.
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteShawValueThinFloor
open ProximityGap.Frontier.WorstPeriodSqrtNFloor

/-! ## B2 — char-0 Wick step-ratio antitonicity (log-concavity), reduced to the classical
`SharpNewtonBessel` (Laguerre–Pólya type-I) input. Scope: **char-0**. -/

/-- **[char-0, B2]** The char-0 Wick-normalised moment step ratio `R d r = m_{r+1}/m_r` is
antitone in `r` **iff** the sharp Newton inequality holds for the Bessel power coefficients —
an exact, axiom-clean algebraic equivalence (no analytic input). -/
theorem char0_stepRatio_antitone_iff_sharpNewton (d : ℕ) (hd : 1 ≤ d) (r : ℕ) :
    Rstep d (r + 1) ≤ Rstep d r ↔
      ((r + 2 : ℕ) : ℚ) * besselCoeff d (r + 2) * besselCoeff d r
        ≤ ((r + 1 : ℕ) : ℚ) * (besselCoeff d (r + 1)) ^ 2 :=
  R_antitone_iff_sharpNewton hd r

/-- **[char-0, B2]** Headline: the classical `SharpNewtonBessel` (LP-I) hypothesis yields the
full telescope input `R d r ≤ 1` for all `r`, i.e. char-0 Wick monotonicity (`W3-anti`). -/
theorem char0_W3anti_of_sharpNewton_export (d : ℕ) (hd : 1 ≤ d)
    (hSN : SharpNewtonBessel d) : ∀ r, Rstep d r ≤ 1 :=
  char0_W3anti_of_sharpNewton hd hSN

/-! ## B8 — char-0 K=1 K-stability cross bound (the dyadic convolution closes). Scope: **char-0**. -/

/-- **[char-0, B8]** The char-0 `K = 1` K-stability cross bound. From the exact dyadic
convolution `E_r(μ_n) = ∑ C(2r,2j)·E_j(H)·E_{r-j}(H)` (`H = μ_{n/2}`, `-1 ∈ H`) and the per-set
char-0 Wick bound, the interior (cross) energy satisfies
`E_r(μ_n) - 2·E_r(H) ≤ (2r-1)‼·((2h)^r - 2 h^r) = Wick(n,r) - 2·Wick(n/2,r)`. -/
theorem char0_kstability_cross_le_wick {r : ℕ} (hr : 1 ≤ r) {h Eμn : ℝ} (hh : 0 ≤ h)
    (E : ℕ → ℝ) (hE0 : E 0 = 1) (hEnonneg : ∀ j, 0 ≤ E j)
    (hconv : Eμn = ∑ j ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * j) : ℝ) * E j * E (r - j))
    (hwick : ∀ j, j ≤ r → E j ≤ ((2 * j - 1)‼ : ℝ) * h ^ j) :
    Eμn - 2 * E r ≤ ((2 * r - 1)‼ : ℝ) * ((2 * h) ^ r - 2 * h ^ r) :=
  W5KStabilityChar0.cross_le_wick_cross hr hh E hE0 hEnonneg hconv hwick

/-! ## L3 — the FULL char-0 prize moment bound as ONE *unconditional* theorem (no Sidon /
no antipodal-pairing hypothesis; the char-0 Lam–Leung energy bound is discharged internally via
`DyadicEnergyK1`). Scope: **char-0**. This is the strongest single proven statement of the
campaign: in characteristic 0 the per-frequency prize cancellation is a *theorem*, with the only
remaining gap being the char-`p` transfer at the prize scale `n = 2^30` (the BGK wall). -/

/-- **[char-0, L3]** THE char-0 prize moment bound (norm form), UNCONDITIONAL. For `G ⊆ μ_{2^k}`
(`k ≥ 1`) in a characteristic-zero field, a formal period sup `M` with `Q ≥ 1` frequencies and the
formal-period moment identity `M^{2r} ≤ Q·E_r(G)` obeys, at optimal depth `r ≥ max(1, log Q)`, the
prize square-root shape `M ≤ √(2e·|G|·r)`. The Lam–Leung energy bound `E_r ≤ (2r-1)‼·|G|^r` is
proven *inside* the theorem (char-0); there is no Sidon/`repThree`/pairing side hypothesis. -/
theorem char0_prize_moment_bound_unconditional {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) :=
  WFL3.char0_prize_moment_bound hk G hG hM hQ hr hrQ hmoment

/-- **[char-0, L3]** Squared form of `char0_prize_moment_bound_unconditional`: `M² ≤ 2e·|G|·r`. -/
theorem char0_prize_moment_bound_sq_unconditional {L : Type*} [Field L] [CharZero L]
    [DecidableEq L] {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
  WFL3.char0_prize_moment_bound_sq hk G hG hM hQ hr hrQ hmoment

/-! ## L4 — char-0 discharge of the nonprincipal-energy named hypothesis `(S-M1')` and the
per-frequency sup bound wired through the P1 bridge. Scope: **char-0** (the char-0 energy bound is
the proven `DyadicEnergyK1` value). -/

/-- **[char-0, L4]** Under the char-0 additive-energy bound `E_r(G) ≤ (2r-1)‼·|G|^r`, the named
nonprincipal-energy hypothesis `NonprincipalEnergyBound` holds with `doubleFact = (2r-1)‼` (`K=1`):
`q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`. Discharges `(S-M1')` from the char-0 substrate. -/
theorem char0_nonprincipalEnergyBound_discharged {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :
    WF6P1.NonprincipalEnergyBound (F := F) G r ((2 * r - 1)‼ : ℝ) :=
  WFL4.nonprincipalEnergyBound_of_energyR_le G r henergy

/-- **[char-0, L4]** Composing the char-0 discharge with the P1 bridge: under the char-0 energy
bound, every nontrivial frequency obeys the Gaussian/Wick sup bound
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r`. In characteristic 0 the hypothesis is the proven `DyadicEnergyK1`
value, so this is an unconditional per-frequency bound there. -/
theorem char0_eta_pow_le_unconditional {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
  WFL4.char0_eta_pow_le_of_energyR_le hψ G r henergy b hb

/-! ## F1 — the sub-Gaussian moment telescope (the consumer that turns a per-step Gaussian
step-law into the full Wick even-moment bound). Scope: **prize-bridge**. -/

/-- **[prize-bridge, F1]** THE TELESCOPE. A nonnegative moment sequence obeying the Gaussian
step-law `M(r+1) ≤ (2r+1)·s·M(r)` from base `M 0 ≤ 1` satisfies the full sub-Gaussian even-moment
bound `M r ≤ (2r-1)‼·s^r` for every `r`. Pure induction; the load-bearing consumer of every
step-law lever. -/
theorem gaussian_moment_telescope {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1)
    (hstep : WF6F1.GaussianStepLaw M s) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r :=
  WF6F1.gaussian_moment_bound_of_stepLaw hs hM hbase hstep

/-! ## B9 — the matched Gaussian is the unique extremal target; its step-law telescopes to the
prize. Scope: **char-0 / prize-bridge** (the step-law is the named input). -/

/-- **[prize-bridge, B9]** Convex-order domination by the matched Gaussian ⟺ the Wick bound. -/
theorem convexOrder_gaussian_iff_wick_export {n : ℕ} (hn : 1 ≤ n) (M : ℕ → ℝ) :
    (∀ r, M r ≤ WF8B9.gaussianMoment n r) ↔ (∀ r, WF8B9.wickMoment M n r ≤ 1) :=
  WF8B9.convexOrder_gaussian_iff_wick hn M

/-- **[prize-bridge, B9]** Headline: if the period moment sequence obeys the matched-Gaussian
sub-step-law `M(r+1) ≤ (2r+1)·n·M(r)` from base `M 0 ≤ 1`, then `wickMoment M n r ≤ 1` for all
`r` — i.e. the period law is convex-order-dominated by `N(0,n)` (= the prize). The matched
Gaussian is pinned as the unique minimal target. -/
theorem prize_of_matchedGaussian_stepLaw_export {n : ℕ} (hn : 1 ≤ n) {M : ℕ → ℝ}
    (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1) (hstep : WF6F1.GaussianStepLaw M (n : ℝ)) :
    ∀ r, WF8B9.wickMoment M n r ≤ 1 :=
  WF8B9.prize_of_matchedGaussian_stepLaw hn hM hbase hstep

/-! ## P1 — the nonprincipal-energy bridge (the live moment-route lever). Scope: **prize-bridge**. -/

/-- **[prize-bridge, P1]** The named sufficient hypothesis `(S-M1')` — the nonprincipal additive
energy bound — implies the per-frequency sup bound `‖η_b‖^{2r} ≤ q·(doubleFact·|G|^r)` for every
nonprincipal `b`. With `doubleFact = (2r-1)‼` and depth `r ≈ ln q`, this is the prize
cancellation `max_{b≠0}‖η_b‖ ≤ C√(n log q)`. The correct, non-vacuous moment-route lever. -/
theorem eta_pow_le_of_nonprincipalEnergyBound_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (doubleFact : ℝ) (hbnd : WF6P1.NonprincipalEnergyBound (F := F) G r doubleFact)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFact * (G.card : ℝ) ^ r) :=
  WF6P1.eta_pow_le_of_nonprincipalEnergyBound hψ G r doubleFact hbnd b hb

/-! ## B5 / B6 — the moment-problem obstructions. Scope: **obstruction**. -/

/-- **[obstruction, B5]** Hankel-positivity (the free moment-problem half `M₁² ≤ M₀·M₂`) does
NOT imply the ultra-sub-Gaussian Wick bracket: there is an explicit positive raw-moment sequence
that satisfies the free half yet violates `UltraSubGaussianStep` at `r = 1`. Any unconditional
moment-sequence theorem (which sees only positivity) cannot establish `W3-anti`. -/
theorem moment_problem_does_not_give_wick_bracket :
    ∃ (M W : ℕ → ℝ) (n : ℕ),
      (∀ k, 0 < M k) ∧ (∀ k, W k = ((2 * k - 1)‼ : ℝ) * (n : ℝ) ^ k) ∧
      (M 1) ^ 2 ≤ (M 0) * (M 2) ∧
      ¬ _root_.ProximityGap.Frontier.MomentProblemB5.UltraSubGaussianStep M W 1 :=
  _root_.ProximityGap.Frontier.MomentProblemB5.ultraSubGaussian_not_free

/-- **[obstruction, B6]** The cumulant-sign sufficiency criterion is refuted at the actual
period law: no cumulant sequence with `κ₄ < 0` can have `κ₈ > 0` and still meet the
nonpositive-higher-cumulant envelope. The period law's cumulants are sign-indefinite, so the
cumulant route cannot drive the prize bound. -/
theorem cumulant_sign_route_refuted {κ : ℕ → ℝ} (h4 : κ 2 < 0) (h8 : 0 < κ 4) :
    ¬ (∀ r, 2 ≤ r → κ r ≤ 0) :=
  CumulantSigns.subWick_positivity_refuted h4 h8

/-! ## G2 / G3 / G4 — the late-campaign lever obstructions (resonance / coefficient / roughness).
Scope: **obstruction**. Each is an axiom-clean proof that a named candidate lever cannot reach the
prize floor `√(n·log(p/n))`. -/

/-- **[obstruction, G2]** The Parseval/RMS resonance certificate is strictly below the prize floor
in the thin prize regime: `c·√n < √(n·L)` whenever `0 < n`, `0 ≤ c`, `c² < L`. With the measured
resonance constant `c ≤ 2` and the prize index `L = log(p/n) = log m ≫ c²`, the resonance route
gives NO Ω-disproof of `C = O(1)`. -/
theorem resonance_ceiling_below_prize_floor (c n L : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hL : c ^ 2 < L) :
    c * Real.sqrt n < Real.sqrt (n * L) :=
  WF9G2.resonance_below_floor c n L hn hc hL

/-- **[obstruction, G3]** The cyclotomy-coefficient (Fujiwara coefficient-root) route is loose by a
divergent factor: for every constant `C` there is an `m` with `fujiwaraAtTwo (n·m+1) n > C·prizeScale n m`
for all `n > 0`. No coefficient-magnitude root bound can meet the BGK target. -/
theorem coeff_route_loose_export (C : ℝ) (hC : 0 < C) :
    ∃ m : ℝ, 2 ≤ m ∧
      ∀ n : ℝ, 0 < n →
        WF9G3.fujiwaraAtTwo (n * m + 1) n > C * WF9G3.prizeScale n m :=
  WF9G3.coeff_route_loose C hC

/-- **[obstruction, G4]** Roughness is not the driver: the per-config bad-prime set `{p : p ∣ N}`
is determined by the FIXED integer `N` alone, so adjoining a roughness side-condition `rough p` can
only restrict it — `{p : p ∣ N ∧ rough p} ⊆ {p : p ∣ N}`. The largest prime factor of `m = (p-1)/n`
is not a parameter of the bad set. -/
theorem roughness_does_not_add_bad_primes_export (N : ℕ) (rough : ℕ → Prop) :
    {p : ℕ | p ∣ N ∧ rough p} ⊆ {p : ℕ | p ∣ N} :=
  G4RoughnessNotTheDriver.roughness_does_not_add_bad_primes N rough

/-! ## prize-bridge — the two faces are ONE wall (Parseval-dual; answers the "campaign still
points miners at the refuted bare sup-norm" flag, #444). The additive-energy face and the
multiplicative sup-norm face are the SAME object, bracketed within the trivial averaging factor
`q−1`. The link is the exact moment identity `sum_nonzero_moment` — NO loss and NO gain — so the
open core is one wall in two Fourier-dual bases, not two independent walls to be bridged. -/

/-- **[prize-bridge, OneWall]** The backward bridge: a sup-norm bound forces an energy bound. If
every nonzero period satisfies `‖η_b‖ ≤ M`, then the additive energy is controlled by `M`:
`q·E_r − n^{2r} ≤ (q−1)·M^{2r}`. Together with the forward `M^{2r} ≤ q·E_r − n^{2r}`
(worst-term ≤ sum), the worst-case sup-norm `M^{2r}` and the additive energy `E_r` bracket each
other within `q−1`: the additive count and the Gauss-phase worst case carry IDENTICAL information.
This is the consolidating statement that the prize is one wall, not two independent obstructions. -/
theorem two_faces_are_one_wall_export {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hsup : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ≤ M) :
    (Fintype.card F : ℝ)
        * (_root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
        - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ (2 * r) :=
  _root_.ArkLib.ProximityGap.Frontier.BridgeOneWall.pincer_is_one_wall hψ G r hM hsup

/-! ## NoFifthDoor — the Lane-2/3 tetrachotomy capstone (Shaw's "Shaw Value" essay, #444).
Scope: **capstone**. The headline citable statement of the campaign: there is NO fifth door, every
prize-scale certificate must pass through door (iv) (a genuinely new monomial-sum evaluation), and the
remaining obligation is exactly to shave the `√L = √log(p/n)` factor separating the BGK ceiling
`√(n·L)` that doors (i)-(iii) deliver from the prize floor `√n`. Pure scale algebra over the
abstract `Mechanism`/`DoorType` model; the classical-overshoot hypothesis is the formal content of the
proven Lever A-D refutations (indexed above as the obstruction-scope exports). -/

/-- **[capstone, NoFifthDoor]** No fifth door: if every classical door (moment/completion/extreme-value)
overshoots the BGK scale (the proven Lever A-D fate) in the regime `L > 1`, then any mechanism `m`
certifying a prize-scale bound `m.certScale ≤ √n` has door `newEvaluation` — door (iv) is the ONLY
door through which a prize-scale certificate can pass. -/
theorem noFifthDoor_forces_doorIV_export
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L)
    (hcert : m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n) :
    m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.forces_doorIV hn hL
    hclassicalOvershoots hcert

/-- **[capstone, NoFifthDoor]** Existential form: under the classical-overshoot hypothesis, the set of
prize-certifying mechanisms is contained in the door-(iv) mechanisms. Every prize-scale certificate is
a door-(iv) certificate. -/
theorem prizeCertifying_subset_doorIV_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L) :
    ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
      m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
      m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hn hL
    hclassicalOvershoots

/-- **[capstone, NoFifthDoor]** The door-(iv) target corridor: the worst-frequency sup `M` lives in
`[√n, √(n·L)]` — the prize floor (Plancherel/RMS) below and the BGK ceiling (what doors (i)-(iii)
deliver) above. The entire remaining door-(iv) content is to descend from the ceiling to the floor. -/
theorem doorIV_corridor_export {M n L : ℝ}
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M)
    (hceil : M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M ∧
      M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.mem_doorIV_corridor hfloor hceil

/-- **[capstone, NoFifthDoor]** The corridor has positive width in the prize regime `L > 1`: the
floor is strictly below the ceiling, so the door-(iv) shave is a real `√L`-factor gap, not a point. -/
theorem doorIV_corridor_width_pos_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      < _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIV_corridor_width_pos hn hL

/-- **[capstone, DoorIVCorridorIcc]** `Set.Icc` membership form of the door-(iv) corridor: a value
lies in the closed target interval exactly when it is between the Plancherel floor and BGK ceiling. -/
theorem doorIVCorridor_mem_iff_export {n L M : ℝ} :
    M ∈ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor n L ↔
      _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M ∧
        M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.mem_doorIVCorridor_iff

/-- **[capstone, DoorIVCorridorIcc]** In the prize regime `L > 1`, the `Set.Icc` door-(iv) corridor is
nonempty. This packages the positive-width target as an order-theoretic interval. -/
theorem doorIVCorridor_nonempty_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    (_root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor n L).Nonempty :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor_nonempty hn hL

/-- **[capstone, DoorIVCorridorIcc]** At `L = 1`, the door-(iv) corridor collapses to the singleton
floor `{√n}`. Positive-width statements therefore genuinely use the thinness slack `L > 1`. -/
theorem doorIVCorridor_one_eq_singleton_export (n : ℝ) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor n 1 =
      {_root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n} :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor_one_eq_singleton n

/-- **[capstone, DoorIVCorridorIcc]** Corridor monotonicity in the thinness parameter: increasing
`L` only widens the BGK ceiling while leaving the prize floor fixed. -/
theorem doorIVCorridor_subset_of_le_export {n L₁ L₂ : ℝ} (hn : 0 ≤ n) (hL : L₁ ≤ L₂) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor n L₁ ⊆
      _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor n L₂ :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor_subset_of_le hn hL

#print axioms doorIVCorridor_mem_iff_export
#print axioms doorIVCorridor_nonempty_export
#print axioms doorIVCorridor_one_eq_singleton_export
#print axioms doorIVCorridor_subset_of_le_export

/-- **[capstone, NoFifthDoor]** The exact factor door (iv) must remove: the BGK ceiling equals the
prize floor scaled by `√L`, i.e. `√(n·L) = √L · √n`. Pins the door-(iv) obligation quantitatively. -/
theorem bgkScale_eq_sqrtL_mul_prizeScale_export {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L
      = Real.sqrt L * _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale_eq_sqrtL_mul_prizeScale hn hL

/-- **[obstruction, NoFifthDoor]** Discharged classical overshoot quantifier for honest mechanisms:
past the SOTA threshold, every classical mechanism that respects its proven scale (`√q` for completion,
`C·n^{1−δ}` for moment/EVT) overshoots BGK. This is the theorem replacing the abstract
`hclassicalOvershoots` postulate on the physically meaningful subclass. -/
theorem noFifthDoor_ceilingRespecting_classical_overshoots_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.door.isClassical → m.RespectsProvenScale q C δ n →
          m.OvershootsBGK n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.ceilingRespecting_classical_overshoots
    hLnn hC hδ

/-- **[capstone, NoFifthDoor]** Discharged no-fifth-door capstone: past the SOTA threshold, if
classical mechanisms are real instances of their doors (they respect the proven completion/moment/EVT
scales), then any prize-scale certificate is forced through door (iv). The classical overshoot input is
proved from the concrete ceilings, not assumed. -/
theorem noFifthDoor_forces_doorIV_ceilingRespecting_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      (∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.RespectsProvenScale q C δ n) →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
          m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.forces_doorIV_ceilingRespecting
    hLnn hL hC hδ

/-- **[capstone/obstruction, NoFifthDoor]** Local contrapositive of the discharged classical side:
past the SOTA threshold, a classical mechanism that certifies the prize scale must violate its own
proven door-scale (`√q` for completion, `C·n^{1−δ}` for moment/EVT). This blocks the degenerate
`certScale` loophole without assuming every mechanism globally respects its ceiling. -/
theorem noFifthDoor_classical_prize_certificate_violates_provenScale_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.door.isClassical →
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
        ¬ m.RespectsProvenScale q C δ n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.classical_prize_certificate_violates_provenScale
    hLnn hL hC hδ

/-- **[capstone, NoFifthDoor]** Local no-fifth-door alternative: past the SOTA threshold, any
prize-scale certificate is either a genuine door-(iv) mechanism, or it violates the proven scale of
its own classical door. This is the discharged, single-mechanism form of the no-fifth-door capstone. -/
theorem noFifthDoor_prize_certificate_doorIV_or_violates_provenScale_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
          m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation ∨
            ¬ m.RespectsProvenScale q C δ n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prize_certificate_doorIV_or_violates_provenScale
    hLnn hL hC hδ

/-! ## ShawGrandSynthesis — the composed Lane-2/Lane-3 headline. Scope: **capstone**.
These exports make permanent the newly landed synthesis module: the prize is exactly Shaw boundedness,
and any proof at the prize floor must pass through door (iv). Pure composition, no CORE bound. -/

/-- **[capstone, ShawGrandSynthesis]** Conjoined headline: `ShawOOneOn ↔ CorePrizeBoundOn` and,
at a proven-scale mechanism instance, a prize-floor certificate forces door (iv). -/
theorem shawGrand_prize_reduces_to_doorIV_export
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι,
      0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism}
    {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n₀ L₀ ≤
      C * n₀ ^ (1 - δ))
    (hatScale : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale
      m n₀ q₀ C δ) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n₀ →
        m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV
    hscale hn₀ hL₀ hq₀ hsota hatScale

/-- **[capstone, ShawGrandSynthesis]** Same synthesis with Shaw-scale positivity discharged from
`0 < n_i < q_i` on the family. -/
theorem shawGrand_prize_reduces_to_doorIV_of_pos_lt_export
    {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i)
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism}
    {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n₀ L₀ ≤
      C * n₀ ^ (1 - δ))
    (hatScale : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale
      m n₀ q₀ C δ) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n₀ →
        m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV_of_pos_lt
    hn hnq hn₀ hL₀ hq₀ hsota hatScale

/-- **[capstone, ShawGrandSynthesis]** Eventual family headline: Shaw boundedness is exactly the
CORE prize bound, and past the SOTA threshold every proven-scale prize-floor certificate is door (iv). -/
theorem shawGrand_prize_reduces_to_doorIV_eventually_export
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι,
      0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    {L q₀ C δ : ℝ} (hC : 0 < C) (hL : 1 < L) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      ∃ N₀ : ℝ, ∀ n' : ℝ, N₀ ≤ n' → 2 ≤ n' → n' * L ≤ q₀ →
        ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale m n' q₀ C δ →
          m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n' →
            m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV_eventually
    hscale hC hL hLnn hδ

/-! ## NoTighterBound — the #407/#444 "no tighter bound from any direction" capstone (Lane-2).
Scope: **capstone**. The negative structural theorem: any functional bounding the per-frequency core
`M(n) = max_{b≠0}‖η_b‖` must be simultaneously b-sensitive, deterministic-archimedean, and genuinely
`L∞`. The two machine-checkable failure faces — a b-symmetric (moment-determined) statistic CANNOT
determine the sup, and an only-`L²`/depth-`r`-moment method is floored at the trivial `√S` — are
bundled into one citation point. (The third property, deterministic-archimedean, is named in prose; it
is the absence of an ensemble/freeness the fixed subgroup lacks.) -/

/-- **[capstone, NoTighterBound]** A `b`-symmetric statistic cannot determine the sup: two explicit
real families on `Fin 4` with IDENTICAL first and second moments but a strictly larger coordinate in
one. So any functional determined by the (permutation-invariant) moment data is blind to the worst
`b`. Failure mode (1) of the 3-property necessary condition. -/
theorem noTighterBound_secondMoment_blind_export :
    ∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
      (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
      (∀ j, |η' j| < |η b₀|) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.secondMoment_does_not_determine_sup

/-- **[capstone, NoTighterBound]** The packaged no-tighter-bound capstone: BOTH machine-checkable
faces in one conjunction — (1) a moment-determined `b`-symmetric statistic cannot see the worst `b`,
and (3) any only-`L²`/depth-`r`-moment method `g` is floored at `√S` (cannot reach
`√(n·log m) ≪ √S`). Every classical and fresh tool fails at least one. The structural reason no
tighter bound on `M` is reachable from the symmetric / `L²` directions. -/
theorem noTighterBound_from_symmetric_or_L2_export :
    (∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
        (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
        (∀ j, |η' j| < |η b₀|)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}, 1 ≤ r → ∀ (g : ℝ → ℝ),
        (∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) →
        ∀ {S : ℝ}, 0 ≤ S → Real.sqrt S ≤ g (S ^ r)) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.noTighterBound_from_symmetric_or_L2

/-! ## ShawValue — the Lane-2 `prize ⟺ Sh(n)=O(1)` capstone (the citable normalization).
Scope: **capstone**. The prize inequality `M ≤ C·√(n·L)` is exactly a bound on the normalized
Shaw value `Sh(M) = M/√(n·L)`; the proven two-sided corridor `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on
the REAL Gauss-period worst frequency brackets the open prize at multiplicative width `√n`. -/

/-- **[capstone, ShawValue]** The prize normalization equivalence: under a positive prize scale,
the raw prize-shaped bound `M ≤ C·√(n·L)` is *exactly* the statement that the normalized Shaw
value is at most `C`. This removes the arithmetic wrapper, so the prize reads as “bound the
normalized object by an absolute constant” (`Sh(n)=O(1)`). Pure normalization — no cancellation
estimate is hidden. -/
theorem prizeBound_iff_shawValue_le_export {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le hs

/-- **[capstone, ShawValue]** Uniform non-strict family form of the Lane-2 reduction: with positive
pointwise prize scale, a raw prize bound by the same constant throughout a family is exactly a
Shaw-value bound by that constant throughout the family. This is the direct `Sh(n)=O(1)` wrapper,
not a cancellation estimate. -/
theorem rawPrizeFamilyBound_iff_shawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound hs

#print axioms rawPrizeFamilyBound_iff_shawValueFamilyBound_export

/-- **[capstone, ShawValue]** Existential non-strict family form of the Lane-2 reduction: existence
of one absolute raw-prize constant is exactly existence of one absolute Shaw-value constant. This is
the Big-O form of the citable normalization equivalence. -/
theorem exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound hs

#print axioms exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound_export

/-- **[capstone, ShawValue]** Wall-facing non-strict existential form: failure of every absolute
raw-prize constant is exactly failure of every absolute Shaw-value constant. Pure normalization
bookkeeping for the obstruction side of `prize ⇔ Sh(n)=O(1)`. -/
theorem not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound hs

#print axioms not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound_export

/-- **[capstone, ShawValue]** Nonnegative-constant non-strict family form of the Lane-2 reduction:
with positive pointwise prize scale, existence of a nonnegative absolute raw-prize constant is exactly
existence of a nonnegative absolute Shaw-value constant. This pins the usual Big-O constant domain. -/
theorem exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs

#print axioms exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound_export

/-- **[capstone, ShawValue]** Wall-facing nonnegative non-strict family form: failure of every
nonnegative raw-prize Big-O constant is exactly failure of every nonnegative Shaw-value Big-O
constant. Pure normalization bookkeeping; no Door-IV anti-concentration is asserted. -/
theorem not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound hs

#print axioms not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_export

/-- **[capstone, ShawValue]** Strict prize normalization equivalence: under a positive prize scale,
a strict raw prize-shaped bound `M < C·√(nL)` is exactly the statement that the normalized Shaw
value is strictly below `C`. This is the strict-slack companion to the citable Lane-2 equivalence,
not a cancellation estimate. -/
theorem strictPrizeBound_iff_shawValue_lt_export {M C n L : ℝ}
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L) :
    M < C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n L < C :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictPrizeBound_iff_shawValue_lt hs

/-- **[capstone, ShawValue]** Uniform strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, a strict raw prize bound by the same constant throughout a family is exactly
a strict Shaw-value bound by that constant throughout the family. Pure normalization bookkeeping. -/
theorem strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Existential strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, existence of one absolute strict raw-prize constant is exactly existence of
one absolute strict Shaw-value constant. Pure normalization bookkeeping. -/
theorem exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C,
      (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
        hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C,
      (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
        hs).2 hC⟩

/-- **[capstone, ShawValue]** Wall-facing strict existential form: failure of every absolute strict
raw-prize constant is exactly failure of every absolute strict Shaw-value constant. Pure
normalization bookkeeping for strict-margin obstructions. -/
theorem not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Nonnegative strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, existence of one nonnegative absolute strict raw-prize constant is exactly
existence of one nonnegative absolute strict Shaw-value constant. Pure normalization bookkeeping. -/
theorem exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Wall-facing nonnegative strict-family form: failure of every
nonnegative absolute strict raw-prize constant is exactly failure of every nonnegative absolute strict
Shaw-value constant. Pure normalization bookkeeping for strict-margin obstructions. -/
theorem not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** THE Lane-2 corridor. For the actual primitive-character Gauss-period
worst frequency `M(μ_n) = worstPeriod ψ G` in the thin prize regime `q ≥ 2n` (automatic at
`q = n^β`, `β > 1`), the normalized Shaw value is sandwiched
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)`, both endpoints in closed form. The lower endpoint is the
`n`-independent thin-regime Parseval floor `1/√(2L)`; the upper is the trivial-ceiling scale
`√(n/L)`. The open prize `Sh(M(μ_n)) = O(1)` lives strictly inside this proven corridor.

(All identifiers in the statement are FULLY QUALIFIED: restating them unqualified in this
heavily-`open`ed index context resolves `worstPeriod`/`shawValue` to a different overload, so we pin
the exact source declarations to inherit the clean proof term verbatim.) -/
theorem shawValue_worstPeriod_clean_corridor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (G.card : ℝ) L) :
    1 / Real.sqrt (2 * L) ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) :=
  _root_.ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_clean_corridor
    hψ G hne hn1 hq2n hL hs

/-- **[capstone, ShawValue]** The corridor width is exactly `√n`: the ratio of the trivial-ceiling
endpoint to the Plancherel-floor endpoint equals `√n`. So the open prize is precisely the demand to
collapse this `√n`-wide normalized bracket to an absolute constant. -/
theorem shawValue_bracket_width_eq_sqrt_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (n / prizeScale n L) / (Real.sqrt n / prizeScale n L) = Real.sqrt n :=
  bracket_width_eq_sqrt hn hL

/-- **[capstone, ShawValue]** Exact width of the clean thin-regime normalized corridor.  The citable
Lane-2 bracket `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` has endpoint ratio `√(2n)`, so normalization leaves a
`√n`-scale unconditional gap (up to the harmless `√2`).  This is pure arithmetic over the proven
corridor, not a CORE/cancellation estimate. -/
theorem shawValue_clean_corridor_width_eq_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    Real.sqrt (n / L) / (1 / Real.sqrt (2 * L)) = Real.sqrt (2 * n) :=
  _root_.ProximityGap.Frontier.ConcreteShawValueThinFloor.clean_corridor_width_eq hn hL

/-- **[Lane 2 concrete family reduction]** For a concrete family of thin Gauss-period instances,
a uniform raw prize bound for the actual worst periods is exactly a uniform bound on Shaw's
normalized value, with the same constant. This is the citable concrete `prize ⇔ Sh(n)=O(1)` capstone,
not an anti-concentration estimate. -/
theorem concreteShawFamily_corePrizeBound_iff_shawBounded_export {ι : Type*}
    (T : ι → _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.ThinInstance) (C : ℝ) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T) C
      ↔ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T) C :=
  _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.corePrizeBound_iff_shawBounded T C

/-- **[Lane 2 concrete family reduction]** Existential-constant form of the same concrete capstone:
an absolute CORE constant for the real worst-period family exists iff an absolute Shaw-value constant
exists. The open content is only the uniform upper constant. -/
theorem concreteShawFamily_exists_corePrizeBound_iff_exists_shawBounded_export {ι : Type*}
    (T : ι → _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.ThinInstance) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T) C)
      ↔ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T) C) :=
  _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.exists_corePrizeBound_iff_exists_shawBounded T

/-- **[Lane 2 concrete family reduction]** Every member of a concrete thin family has the proven
`n`-independent Shaw floor `1/√(2Lᵢ)`. The bounded-Shaw side is therefore a real two-sided corridor,
not a vacuous predicate. -/
theorem concreteShawFamily_shawValue_floor_uniform_export {ι : Type*}
    (T : ι → _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.ThinInstance) (i : ι) :
    1 / Real.sqrt (2 * _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T i) ≤
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T i)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T i)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T i) :=
  _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.shawValue_floor_uniform T i

/-- **[Lane 2 concrete family reduction]** A uniform raw prize bound for the real worst-period family
forces each normalized Shaw value into the concrete sandwich `1/√(2Lᵢ) ≤ Shᵢ ≤ C`. This records the
exact Shaw-value corridor the open CORE bound must collapse. -/
theorem concreteShawFamily_corePrizeBound_forces_sandwich_export {ι : Type*}
    (T : ι → _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.ThinInstance) {C : ℝ}
    (hC : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T)
        (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T) C) (i : ι) :
    1 / Real.sqrt (2 * _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T i) ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T i)
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T i)
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T i)
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.worstFam T i)
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.nFam T i)
          (_root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.LFam T i) ≤ C :=
  _root_.ProximityGap.Frontier.ConcreteShawFamilyReduction.corePrizeBound_forces_sandwich T hC i

#print axioms concreteShawFamily_corePrizeBound_iff_shawBounded_export
#print axioms concreteShawFamily_exists_corePrizeBound_iff_exists_shawBounded_export
#print axioms concreteShawFamily_shawValue_floor_uniform_export
#print axioms concreteShawFamily_corePrizeBound_forces_sandwich_export

/-- **[capstone, ConcreteTrivialCeiling]** The sharp unconditional corridor on the real worst
period in the quadratic thin regime: `√(|G|-1) ≤ M(G) ≤ |G|`. This is the concrete lower/upper
bracket the Shaw normalization rests on; it is pure Parseval plus the triangle ceiling and makes no
cancellation claim. -/
theorem worstPeriod_sharp_bracket_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) - 1) ≤
        _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne
      ∧ _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne
          ≤ (G.card : ℝ) :=
  _root_.ProximityGap.Frontier.ConcreteTrivialCeiling.worstPeriod_sharp_bracket
    hψ G hne hq1 hG1 hsq

/-- **[obstruction, ConcreteBGKCompletionCorridor]** In the thin regime `d² ≤ q`, the classical
`√q` completion ceiling is no better than the free triangle ceiling `d`: `d ≤ √q`. Thus door (ii)
is not just above the BGK target, it can be vacuous relative to `M≤d` on the real period. -/
theorem completion_vacuous_below_trivial_ceiling_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℝ} (hd : 0 ≤ d)
    (hsq : d ^ 2 ≤ (Fintype.card F : ℝ)) :
    d ≤ Real.sqrt (Fintype.card F) :=
  _root_.ProximityGap.Frontier.ConcreteBGKCompletionCorridor.card_le_completionCeiling_of_sq_le
    (F := F) hd hsq

/-- **[capstone, ConcreteShawCompletionCorridorFull]** The complete normalized completion corridor
on the actual torsion-subgroup object `μ_d`: `1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))`. The upper endpoint
is exactly the SOTA completion baseline; collapsing it to `O(1)` is the open prize. -/
theorem shawValue_worstPeriod_torsion_full_corridor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L) :
    1 / Real.sqrt (2 * L)
        ≤ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
            (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne)
          ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
            (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne)
          ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L
          ≤ Real.sqrt ((Fintype.card F : ℝ) / ((d : ℝ) * L)) :=
  _root_.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.shawValue_worstPeriod_torsion_full_corridor
    hd hd0 hψ hne hd1 hq2d hL hs

/-- **[capstone, ConcreteShawCompletionCorridorFull]** The sharp Parseval floor specialized to the
canonical prize object `μ_d`: in the quadratic thin regime, `√(d−1) ≤ M(μ_d)`. This records the true
lower endpoint on the real object; the missing work remains entirely on the upper/cancellation side. -/
theorem worstPeriod_torsion_sharp_floor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) (hd1 : (1 : ℝ) < (d : ℝ))
    (hsq : (d : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((d : ℝ) - 1) ≤
      _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne :=
  _root_.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.worstPeriod_torsion_sharp_floor
    hd hd0 hψ hne hq1 hd1 hsq

/-! ## CoreReductionNecessity — exact `m*` gate for the BCHKS/Shaw reduction.
Scope: **capstone**. These exports make the Lane-2 necessity direction permanent: under the
monotone cascade and the P2/E3 identification, the BCHKS budget at a fold is not merely sufficient
for the binding depth to clear that fold, it is exactly equivalent. Thus the Johnson-side strict
gate `m* < k` is equivalent to the single named BCHKS/Shaw budget at `k-1`. This is reduction
bookkeeping only; the BCHKS budget itself remains the explicit open input. -/

/-- **[capstone, CoreReductionNecessity]** Failure of the named BCHKS budget at fold `M` pushes
the binding depth strictly past `M`. This is the necessity half of the `m*` gate. -/
theorem coreReduction_mStar_gt_of_BCHKS_fails_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ)
    (hfail : ¬ ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n M)
      (budget n)) :
    M < ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex :=
  ArkLib.ProximityGap.CoreReductionComplete.mStar_gt_of_BCHKS_fails
    D budget Sigma smap rmap n hex hmono hident M hfail

/-- **[capstone, CoreReductionNecessity]** Exact two-sided gate: under cascade monotonicity and
the P2/E3 identification, `m* ≤ M` iff the BCHKS/Shaw budget holds at the corresponding fold. -/
theorem coreReduction_mStar_le_iff_BCHKS_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex ≤ M ↔
      ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n M)
        (budget n) :=
  ArkLib.ProximityGap.CoreReductionComplete.mStar_le_iff_BCHKS
    D budget Sigma smap rmap n hex hmono hident M

/-- **[capstone, CoreReductionNecessity]** Consumer-facing Johnson-fold form: for positive
`kNat`, clearing `m* < kNat` is equivalent to the BCHKS/Shaw budget at the previous fold `kNat-1`.
This pins the exact open input of the reduction, without proving that input. -/
theorem coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (kNat : ℕ) (hk_pos : 1 ≤ kNat) :
    ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex < kNat ↔
      ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n (kNat - 1))
        (budget n) :=
  ArkLib.ProximityGap.CoreReductionComplete.clears_johnson_iff_BCHKS_at_prev_fold
    D budget Sigma smap rmap n hex hmono hident kNat hk_pos

/-! ## Door-IV wraparound `Q ≥ 0` discharge. Scope: **obstruction**.

These exports preserve the algebraic narrowing of the char-`p` transfer route: the blind
wraparound-gap assumption `Q ≥ 0` follows from the sharper log-concavity input `wa·wc ≤ wb²`,
with an explicit `2·wb²` margin. The companion dominance hypothesis is refuted by the next section,
so this is a route-local constraint/reduction, not a CORE proof. -/

/-- **[obstruction, CharPWraparoundLogConcaveQ]** Under wraparound log-concavity `wa·wc≤wb²`
and `0≤s`, the wraparound transfer gap is at least `2·wb²`. This replaces a blind `Q≥0` input
by a sharper single inequality plus an explicit margin. -/
theorem charP_wrap_gap_ge_two_mul_sq_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    2 * wb ^ 2 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_ge_two_mul_sq hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The open wraparound-control hypothesis `Q≥0`
of the char-`p` transfer assembly follows from `0≤s` and wraparound log-concavity. The remaining
dominance input is separate and is not discharged here. -/
theorem charP_wrap_gap_nonneg_of_logConcave_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_nonneg_of_logConcave hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The char-`p` transfer assembly with the
`Q≥0` hypothesis replaced by wraparound log-concavity. This records the exact remaining obligation:
`0≤G₀+L` dominance plus `wa·wc≤wb²`, with dominance refuted at concrete prize-regime witnesses in
`CharPStepRatioFails`. -/
theorem charP_transfer_of_dominance_logConcave_export {s a₀ b₀ c₀ wa wb wc : ℝ}
    (hs : 0 ≤ s)
    (hdom : 0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s a₀ b₀ c₀ +
      (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa)))
    (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap
      s (a₀ + wa) (b₀ + wb) (c₀ + wc) :=
  ArkLib.ProximityGap.CharPTransferDecomposition.charP_transfer_of_dominance_logConcave
    hs hdom hlc

/-! ## Door-IV char-p transfer / ρ-antitone refutations. Scope: **obstruction**.

These exports make the newest door-(iv) Lane-3 no-go results permanent: char-`p` step-ratio
monotonicity is exactly the sign of the transfer gap, and explicit prize-regime witnesses
refute both the universal step-ratio route and the normalized `ρ`-antitone-and-bounded route. These are route
refutations only; they do not disprove CORE. -/

/-- **[obstruction, CharPStepRatioFails]** The abstract char-`p` step-ratio monotonicity predicate
`s·E_r·E_{r+2} ≤ (s+2)·E_{r+1}²` is exactly nonnegativity of the transfer gap functional used in
`_CharPTransferDecomposition`. This pins the step-ratio route to one sign condition. -/
theorem charP_stepRatioMonotoneAt_iff_gap_nonneg_export (s Er Er1 Er2 : ℝ) :
    ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2 ↔
      0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s Er Er1 Er2 :=
  ArkLib.ProximityGap.CharPStepRatioFails.stepRatioMonotoneAt_iff_gap_nonneg s Er Er1 Er2

/-- **[obstruction, CharPStepRatioFails]** Exact prize-regime witness (`n=32`, `p=786433`, `r=3`)
refuting char-`p` step-ratio monotonicity: `7·E₃·E₅ ≤ 9·E₄²` is false for
the exact period energies. -/
theorem charP_stepRatioMonotone_false_n32_export :
    ¬ ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt
        7 446720 92179360 24850732032 :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_stepRatioMonotoneAt_n32

/-- **[obstruction, CharPStepRatioFails]** No theorem using only positivity of
`s,E_r,E_{r+1},E_{r+2}` can prove universal char-`p` step-ratio monotonicity; the exact positive
`n=32` witness violates it. -/
theorem charP_no_universal_positive_stepRatioMonotone_export :
    ¬ (∀ s Er Er1 Er2 : ℝ,
      0 < s → 0 < Er → 0 < Er1 → 0 < Er2 →
        ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2) :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_forall_positive_stepRatioMonotoneAt

/-- **[obstruction, RhoAntitoneFails]** In normalized `ρ = S/((p−1)E)` coordinates, the `n=32`,
`p=786433` witness cannot satisfy both the antitone step `ρ(4)≤ρ(3)` and the order-5 ceiling
`ρ(5)≤1`. This is the probe-facing no-go interface for the `ρ`-antitone-and-bounded route. -/
theorem rho_normalized_antitone_and_ceiling_incompatible_export :
    ¬ (ArkLib.ProximityGap.RhoAntitoneFails.S4 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E4)
        ≤ ArkLib.ProximityGap.RhoAntitoneFails.S3 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E3) ∧
      ArkLib.ProximityGap.RhoAntitoneFails.S5 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E5)
        ≤ (1 : ℝ)) :=
  ArkLib.ProximityGap.RhoAntitoneFails.not_normalized_antitone_and_ceiling

/-- **[obstruction, RhoAntitoneFails]** The `ρ`-antitone route is not universally satisfiable:
there are positive exact witness values with the `r=3` cross-inequality reversed and the `r=5`
normalized ceiling broken. Hence `open_core_of_rho_antitone` remains a conditional sufficient route,
not a universal proof strategy. -/
theorem rho_antitone_route_not_universal_export :
    ∃ S3 S4 S5 E3 E4 E5 pm1 : ℝ,
      (0 < pm1 ∧ 0 < E3 ∧ 0 < E4 ∧ 0 < E5) ∧
      S3 * E4 < S4 * E3 ∧
      pm1 * E5 < S5 :=
  ArkLib.ProximityGap.RhoAntitoneFails.antitone_route_not_universal

/-! ## Door-IV value-shift histogram obstruction. Scope: **obstruction**.

These exports make the finite anti-concentration no-go reusable from the permanent index. The
value-shift mechanism is the one door-(iv) `L^∞` spreading idea that genuinely avoids the moment route,
but its own necessary condition is stronger than value-set symmetry: a nontrivial shift must preserve
the full fiber-cardinality histogram. In a prime field the realizable steps are all-or-nothing, so one
nonzero histogram mismatch collapses the entire mechanism to step `0` and hence to the trivial
`fiberCard val 0 ≤ #T` ceiling. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVValueShiftHistogram]** In a prime field, a single nonzero realizable
value-shift step forces the fiber histogram to be completely flat: every two residues have equal
fiber cardinality. Thus a useful value-shift free part demands perfect residue equidistribution,
not merely value-set invariance. -/
theorem valueShift_nontrivial_forces_flat_histogram_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s : ZMod p} (hs : s ≠ 0)
    (hreal : ∃ vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val,
      vs.s = s) :
    ∀ a b : ZMod p,
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a =
        ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val b :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.nontrivial_valueShift_forces_flat_histogram val hs hreal

/-- **[obstruction, DoorIVValueShiftHistogram]** Single-witness collapse: in a prime field, one
fiber-cardinality mismatch at one step rules out the all-steps case and forces every value-shift to
have trivial step `0`. -/
theorem valueShift_step_zero_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_step_zero_of_one_histogram_witness val hne vs

/-- **[obstruction, DoorIVValueShiftHistogram]** With one histogram mismatch, the value-shift
spreading route gives only the trivial ceiling `fiberCard val 0 ≤ #T`; it cannot supply a useful
wraparound anti-concentration bound for the prize value map without a flat periodic histogram. -/
theorem valueShift_route_vacuous_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 ∧
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val 0 ≤ Fintype.card T :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_route_vacuous_of_one_histogram_witness val hne vs

/-! ## Door-IV wraparound Markov vacuity. Scope: **obstruction**.

These exports lock the average-to-sup no-go interface for the wraparound bad-prime route. The finite
Markov/union bound is valid, but when the threshold is at or below the mean its right side is at least
the whole prime set, so it cannot exclude even one heavy prime. Average wraparound control therefore
does not supply a supremum bound through the union route. -/

/-- **[obstruction, WraparoundMarkovVacuity]** Finite Markov inequality in multiplicative form:
for nonnegative weights, `T * #{j ∈ S : T ≤ W j} ≤ ∑ W j`. This is the exact union-bound interface
for the summed wraparound incidence. -/
theorem wraparound_markov_count_le_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ) (hW : ∀ j ∈ S, 0 ≤ W j) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_count_le S W T hW

/-- **[obstruction, WraparoundMarkovVacuity]** If `0 < T ≤ mean S W`, the Markov right-hand side
`(∑ W)/T` is at least `|S|`, so the union bound is vacuous at that threshold. -/
theorem wraparound_markov_bound_vacuous_below_mean_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_bound_vacuous_below_mean S W T hne hT hTmean

/-- **[obstruction, WraparoundMarkovVacuity]** Combined interface: below the average, the Markov
count bound still holds but its exclusion bound is already at least the full index-set size, so
average-control does not bound the supremum through this route. -/
theorem wraparound_average_control_does_not_bound_sup_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T) (hW : ∀ j ∈ S, 0 ≤ W j)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j
      ∧ (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.average_control_does_not_bound_sup
    S W T hne hT hW hTmean

/-! ## Door-IV index-factor overshoot. Scope: **obstruction**.

These exports make the naive-incidence scale loss citable from the permanent index: replacing the prize
scale `sqrt(n L)` by the incidence bridge scale `sqrt(n m L)` multiplies the normalized Shaw constant
by exactly `sqrt m`. A bounded normalized naive constant therefore bounds the index itself; an unbounded
index family cannot pass through this bridge without a genuinely new argument removing the factor. -/

/-- **[obstruction, DoorIVIndexFactorOvershoot]** The naive incidence bridge scale
`sqrt(n*m*L)` is exactly `sqrt(m)` times the prize scale `sqrt(n*L)`. -/
theorem doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export {n m L : ℝ}
    (hm : 0 ≤ m) :
    ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L =
      Real.sqrt m * ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_sqrt_mul_prizeScale hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** A raw bound at the naive incidence scale is
exactly a Shaw-value bound with the constant multiplied by `sqrt(m)`. -/
theorem doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export {M C n m L : ℝ}
    (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 < L) :
    M ≤ C * ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L ↔
      ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n L ≤ C * Real.sqrt m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceBound_iff_shawValue_le_scaled hn hm hL

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Contrapositive-facing form: with fixed positive
raw constant `C`, any uniform cap `D` on `C*sqrt(m)` forces `m ≤ (D/C)^2`; hence the naive bridge
cannot give a bounded Shaw constant on an unbounded-index family. -/
theorem doorIV_index_le_sq_of_scaledConstant_le_export {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hbound : C * Real.sqrt m ≤ D) :
    m ≤ (D / C) ^ 2 :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.index_le_sq_of_scaledConstant_le
    hC hm hbound

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact pointwise cap criterion: for a positive raw
constant and nonnegative advertised cap, a naive normalized cap `C*sqrt(m) ≤ D` is equivalent to the
finite index constraint `m ≤ (D/C)^2`. The `sqrt(m)` loss is exactly an index bound. -/
theorem doorIV_scaledConstant_le_iff_index_le_sq_export {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hD : 0 ≤ D) :
    C * Real.sqrt m ≤ D ↔ m ≤ (D / C) ^ 2 :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstant_le_iff_index_le_sq
    hC hm hD

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Single-witness family refutation: if some index
exceeds `(D/C)^2`, then no uniform cap `C*sqrt(m i) ≤ D` can hold across the family. This is the
probe-facing audit hook for unbounded-index failures of the naive bridge. -/
theorem doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export
    {ι : Type*} {C D : ℝ} {m : ι → ℝ}
    (hC : 0 < C) (hm : ∀ i, 0 ≤ m i)
    (hlarge : ∃ i, (D / C) ^ 2 < m i) :
    ¬ ∀ i, C * Real.sqrt (m i) ≤ D :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq
    hC hm hlarge

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Strict nontrivial-index scale loss: if the
hidden index satisfies `1 < m`, the naive incidence bridge scale is strictly larger than the prize
scale. The no-loss endpoint is exactly degenerate index one. -/
theorem doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export {n m L : ℝ}
    (hn : 0 < n) (hm : 1 < m) (hL : 0 < L) :
    ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L <
      ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_of_one_lt_m
    hn hm hL

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Strict normalized-constant loss: with positive raw
constant and genuinely nontrivial index, the normalized naive Shaw constant is strictly larger than the
desired constant. -/
theorem doorIV_constant_lt_scaledConstant_of_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm : 1 < m) :
    C < C * Real.sqrt m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_of_one_lt_m
    hC hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Contrapositive strict form: at a nontrivial index,
the inflated naive Shaw constant cannot remain below the desired constant. A route through
`sqrt(n*m*L)` must remove the index factor before claiming a constant Shaw bound. -/
theorem doorIV_not_scaledConstant_le_constant_of_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm : 1 < m) :
    ¬ C * Real.sqrt m ≤ C :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaled_constant_le_constant_of_one_lt_m
    hC hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact strict normalized-constant criterion:
the naive Shaw constant is strictly larger than the desired constant iff the hidden index is
strictly larger than one. -/
theorem doorIV_constant_lt_scaledConstant_iff_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm0 : 0 ≤ m) :
    C < C * Real.sqrt m ↔ 1 < m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_iff_one_lt_m
    hC hm0

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact strict scale criterion: the naive incidence
scale strictly exceeds the prize scale iff the hidden index is strictly larger than one. -/
theorem doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export {n m L : ℝ}
    (hn : 0 < n) (hm0 : 0 ≤ m) (hL : 0 < L) :
    ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L <
      ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L ↔
        1 < m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_iff_one_lt_m
    hn hm0 hL

/-! ## Door-IV order-blindness / selector obstruction. Scope: **obstruction**.

These exports make the Lane-1 `rho(b)` order-selector no-go permanent: a coset-invariant
coherence statistic is a quotient-level function on `b·μₙ`, not a function of the raw
multiplicative order of `b`. Any restricted selector can improve the worst coherence only
by missing an entire coset; merely filtering element-level/order buckets that still hit
every coset preserves the global bound problem. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a statistic is invariant on left `H`-cosets,
then even same-coset elements with different multiplicative orders have the same statistic value.
Thus a `rho(b)`-style coset-level coherence cannot be controlled by multiplicative order alone. -/
theorem doorIV_cosetInvariant_blind_to_order_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    {a b : G} (hab : a * b⁻¹ ∈ H)
    (hord : orderOf a ≠ orderOf b) :
    f a = f b :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_blind_to_order
    hf hab hord

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a restricted frequency class `T` meets every
left `H`-coset, then an upper bound for a coset-invariant statistic on `T` is exactly the global
upper bound. Order buckets or element-level filters do not create a new anti-concentration lever
unless they omit whole cosets. -/
theorem doorIV_cosetHitting_selector_bound_iff_global_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [LE β] {f : G → β} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    (∀ t ∈ T, f t ≤ C) ↔ ∀ b : G, f b ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.bound_on_cosetHitting_set_iff_global
    (H := H) (f := f) (C := C) hf hT

/-- **[obstruction, DoorIVCoherenceOrderBlind]** Positive selector no-go: if a restricted class
claims a strict improvement below some global coset-invariant value, then it must miss an entire
left `H`-coset. Any genuine improvement is quotient-level, not multiplicative-order-level. -/
theorem doorIV_strict_selector_bound_misses_coset_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [Preorder β] {f : G → β} {T : Set G} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    (hbound : ∀ t ∈ T, f t ≤ C) (hstrict : ∃ b : G, C < f b) :
    ∃ x : G, ∀ t ∈ T, t * x⁻¹ ∉ H :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.exists_coset_missed_of_strict_selector_bound
    (H := H) (f := f) hf hbound hstrict

/-! ## Door-IV worst-b Sidon/no energy-excess obstruction. Scope: **obstruction**.

These exports make the exact Sidon-floor constraint reusable from the permanent index. On a Sidon
worst-frequency representative set, the additive-energy excess above `2|G|²-|G|` is exactly zero,
and this remains true on every subset. Thus an additive-energy/sum-product lever must first prove
non-Sidon structure; when the probe-facing object is Sidon, the route has no positive energy budget
to grip. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** The additive-energy excess above the Sidon
floor vanishes exactly for Sidon sets. This pins the probe report `E(W)=2|W|²-|W|` to a kernel
checked no-excess statement. -/
theorem doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G = 0 ↔
      ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_eq_zero_iff_sidon G

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Sidon-ness is hereditary for this no-go:
every subset of a Sidon worst-b representative set has zero positive additive-energy budget above
the Sidon floor. Restricting to a subcollection cannot resurrect an additive-energy lever. -/
theorem doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {G H : Finset F}
    (hG : ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G) (hHG : H ⊆ G) :
    ∀ B : ℕ, 0 < B →
      ¬ (B ≤ ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess H) :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.no_positive_additiveEnergyExcess_of_subset_sidon
    hG hHG

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Positive additive-energy excess is exactly
non-Sidon structure. Any door-(iv) certificate demanding positive energy excess is therefore a
certificate that the worst-b object is not Sidon, contrary to the pinned Sidon-floor probe regime. -/
theorem doorIV_positive_additiveEnergyExcess_iff_not_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    0 < ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G ↔
      ¬ ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.positive_additiveEnergyExcess_iff_not_sidon G

/-! ## Door-IV half-mass equivalence capstone. Scope: **capstone**.

These exports make the half-mass reduction citable: under the pointwise comparison `M ≤ H ≤ K*M`
with one family-wide `K`, the original uniform prize bound is equivalent to a uniform half-mass
bound and to bounded normalized half-mass Shaw value. This is normalization/reduction only; the
analytic half-mass cancellation estimate remains the open door-(iv) problem. -/

/-- **[capstone, DoorIVHalfMassEquivalence]** Uniform-family reduction: with one comparison
constant `K`, the existence of an absolute prize constant is equivalent to the existence of an
absolute half-mass constant. -/
theorem doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
    hK hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Mixed Shaw-value form: with positive scales, the
raw uniform prize Big-O bound is equivalent to bounded normalized half-mass Shaw value `H/scale`. -/
theorem doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Four-way packaging: the raw prize bound is equivalent
to simultaneous raw half-mass, normalized prize, and normalized half-mass formulations. -/
theorem doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) ∧
        (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound M scale C) ∧
          (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_all_halfMassShaw_forms
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Standard-library `BddAbove` and the conventional
nonnegative `O(1)` constant are exactly equivalent for normalized prize/Shaw ratios. -/
theorem doorIV_bddAbove_nonneg_normalizedPrize_export {ι : Type*} (M scale : ι → ℝ) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedPrizeFamilyBound
    M scale

/-- **[capstone, DoorIVPrizeBddAbove]** Same nonnegative-constant `BddAbove` bridge for the
normalized half-mass Shaw target. -/
theorem doorIV_bddAbove_nonneg_normalizedHalfMass_export {ι : Type*} (H scale : ι → ℝ) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedHalfMassFamilyBound
    H scale

/-- **[capstone, DoorIVPrizeBddAbove]** Positive-scale `BddAbove` of normalized prize/Shaw ratios
is exactly the raw prize-family Big-O statement with a conventional nonnegative constant. -/
theorem doorIV_bddAbove_nonneg_rawPrize_export {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Positive-scale `BddAbove` of normalized half-mass/Shaw
ratios is exactly the raw half-mass-family Big-O statement with a conventional nonnegative constant. -/
theorem doorIV_bddAbove_nonneg_rawHalfMass_export {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Mixed sign-normalized face: bounded normalized prize/Shaw
ratios are exactly the existence of a conventional nonnegative raw half-mass family constant. -/
theorem doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_halfMassFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Symmetric mixed sign-normalized face: bounded normalized
half-mass Shaw ratios are exactly the existence of a conventional nonnegative raw prize constant. -/
theorem doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_prizeFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Failure of a conventional nonnegative raw prize constant is
exactly explicit normalized-prize drift past every candidate constant. -/
theorem doorIV_not_nonneg_rawPrize_iff_prizeDrift_export {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Failure of a conventional nonnegative raw half-mass constant
is exactly explicit normalized half-mass Shaw drift past every candidate constant. -/
theorem doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) ↔
      ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** The door-(iv) wall is invariant under the half-mass
reduction: failure of `BddAbove` for normalized prize ratios is exactly failure for normalized
half-mass Shaw ratios. -/
theorem doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ¬ BddAbove (Set.range fun i => H i / scale i) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** The unbounded prize-side wall can be stated as explicit
half-mass Shaw drift: every candidate constant is exceeded by some normalized half-mass ratio. -/
theorem doorIV_not_bddAbove_prize_iff_halfMassDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_forall_exists_lt_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** The symmetric wall face: unbounded normalized half-mass
Shaw ratios can be stated as explicit normalized-prize drift past every candidate constant. -/
theorem doorIV_not_bddAbove_halfMass_iff_prizeDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => H i / scale i)) ↔
      ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedHalfMass_iff_forall_exists_lt_normalizedPrize
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Positive door-(iv) boundedness is exactly the negation of
half-mass Shaw drift, packaging `prize ⇔ ¬ wall` in the same standard-library API. -/
theorem doorIV_bddAbove_prize_iff_not_halfMassDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ¬ ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_not_forall_exists_lt_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Symmetric positive/wall face: bounded normalized half-mass
Shaw ratios are exactly the negation of normalized-prize drift. -/
theorem doorIV_bddAbove_halfMass_iff_not_prizeDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ¬ ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_not_forall_exists_lt_normalizedPrize
    hK hscale hMH hHM

/-- **[capstone, ShawValueCapstone]** Standard-library boundedness form of the Shaw slogan:
`Sh(n)=O(1)` is exactly `BddAbove` of the dimensionless Shaw-value range. The nonnegative constant in
`ShawOOneOn` is obtained by replacing any upper bound `C` with `max C 0`. -/
theorem shawOOne_bddAbove_range_shawValue_export {ι : Type*} {q n M : ι → ℝ} :
    _root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_iff_bddAbove_range_shawValue

/-- **[capstone, ShawValueCapstone]** Positive-scale prize bound as a bounded Shaw-value range:
`CorePrizeBoundOn` is equivalent to `BddAbove (range Sh)`. This is the standard-library `BddAbove`
face of the literal `prize ⇔ Sh(n)=O(1)` reduction, with no new analytic estimate. -/
theorem corePrize_bddAbove_range_shawValue_export {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i)) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_iff_bddAbove_range_shawValue hscale

/-- **[capstone, ShawValueCapstone]** Prize-regime version of the `BddAbove (range Sh)` capstone,
discharging scale positivity from `0 < n_i < q_i`. -/
theorem corePrize_bddAbove_range_shawValue_of_pos_lt_export {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_iff_bddAbove_range_shawValue_of_pos_lt
    hn hnq

/-- **[capstone, ShawValueCapstone]** Negative `BddAbove` face of the Shaw slogan: failure of
`Sh(n)=O(1)` is exactly explicit drift of the Shaw values past every proposed constant. -/
theorem shawOOne_unbounded_shawValue_drift_export {ι : Type*} {q n M : ι → ℝ} :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_shawOOneOn_iff_forall_exists_lt_shawValue

/-- **[capstone, ShawValueCapstone]** Negative prize-reduction face: under positive Shaw scale,
failure of `CorePrizeBoundOn` is exactly explicit unbounded drift of the dimensionless Shaw values. -/
theorem corePrize_unbounded_shawValue_drift_export {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_corePrizeBoundOn_iff_forall_exists_lt_shawValue
    hscale

/-- **[capstone, ShawValueCapstone]** Prize-regime negative face of the Shaw drift criterion,
discharging positive scale from `0 < n_i < q_i`. -/
theorem corePrize_unbounded_shawValue_drift_of_pos_lt_export {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_corePrizeBoundOn_iff_forall_exists_lt_shawValue_of_pos_lt
    hn hnq


/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** Single citable Lane-2 synthesis: the
nonnegative-constant prize-family reduction is exactly the nonnegative Shaw-value `O(1)` reduction,
and, under the classical-overshoot refutations, every prize-certifying mechanism is door (iv). -/
theorem doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, 0 ≤ C ∧ ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.prize_iff_shawBounded_nonneg_and_doorIV_only
    hs hnref hLref hclassicalOvershoots

/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** The remaining quantitative gap is exactly
`√L` between the prize floor and BGK scale, and the no-fifth-door theorem routes any certificate for
that gap to door (iv). -/
theorem doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (NoFifthDoorTetrachotomy.prizeScale nref < NoFifthDoorTetrachotomy.bgkScale nref Lref) ∧
      (NoFifthDoorTetrachotomy.bgkScale nref Lref =
        Real.sqrt Lref * NoFifthDoorTetrachotomy.prizeScale nref) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.remaining_gap_is_sqrtL_factor_doorIV_only
    hnref hLref hclassicalOvershoots

/-- **[constraint, DoorIVPrizeShawTetrachotomySynthesis]** Any floor-scale prize constant must be
at least one: the Plancherel floor `√n ≤ M` and a putative certificate `M ≤ K√n` force `1 ≤ K`.
This makes the floor-unit baseline citable from the campaign index. -/
theorem doorIV_floorPrizeConstant_ge_one_export
    {M n K : ℝ} (hn : 0 < n)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale n ≤ M)
    (hbound : M ≤ K * NoFifthDoorTetrachotomy.prizeScale n) :
    1 ≤ K :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.one_le_prizeFloorConstant_of_plancherel_floor
    hn hfloor hbound

/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** Fully discharged positive-side package:
`prize ⇔ Sh(n)=O(1)` with nonnegative constants, plus an eventual floor-ratio formulation of the
pointwise certificate problem after all honest classical doors are excluded. -/
theorem doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export
    {ι : Type*} {Mfam n Lfam : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Lfam i))
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      ((∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound Mfam n Lfam K) ↔
          (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound Mfam n Lfam K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * L ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref) →
          ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale nref ≤ M →
            (1 ≤ DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref) ∧
              (M ≤ K * NoFifthDoorTetrachotomy.prizeScale nref ↔
                DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref ≤ K) ∧
              (∀ m : NoFifthDoorTetrachotomy.Mechanism,
                m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
                m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation)) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.prize_iff_shawBounded_nonneg_and_floorPrizeRatio
    hs hLnn hL hC hδ

/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** Fully discharged wall-side package:
failure of every nonnegative raw prize constant is exactly failure of every nonnegative Shaw-value
constant, and the same eventual floor-ratio formulation leaves only door (iv) for honest
ceiling-respecting mechanisms.  This is pure Lane-2/3 synthesis, not a new estimate. -/
theorem doorIV_no_prize_iff_no_shawBound_nonneg_and_floorPrizeRatio_export
    {ι : Type*} {Mfam n Lfam : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Lfam i))
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      (¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound Mfam n Lfam K) ↔
          ¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound Mfam n Lfam K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * L ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref) →
          ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale nref ≤ M →
            (1 ≤ DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref) ∧
              (M ≤ K * NoFifthDoorTetrachotomy.prizeScale nref ↔
                DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref ≤ K) ∧
              (∀ m : NoFifthDoorTetrachotomy.Mechanism,
                m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
                m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation)) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.no_prizeBound_iff_no_shawBound_nonneg_and_floorPrizeRatio
    hs hLnn hL hC hδ

/-- **[capstone, ShawValueCapstone]** Elementary dominated-majorant transfer: a campaign
`CorePrizeBoundOn` theorem for a pointwise majorant gives the same raw prize-scale bound for every
smaller target.  This is pure monotonicity of the sup norm, with no new analytic estimate. -/
theorem doorIV_corePrize_of_dominated_majorant_export {ι : Type*} {q n M M' : ι → ℝ}
    (hle : ∀ i : ι, M' i ≤ M i)
    (h : ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) :
    ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_of_le hle h

/-- **[capstone, ShawValueCapstone]** Non-Landau citation form of the dominated-majorant Lane-2
reduction: under positive scale, a campaign raw prize bound for a majorant implies `Sh(n)=O(1)` for
any dominated target. -/
theorem doorIV_shawOOne_of_coreMajorant_export {ι : Type*} {q n M M' : ι → ℝ}
    (hscale : ∀ i : ι, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i : ι, M' i ≤ M i)
    (h : ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) :
    ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_of_le_corePrizeBoundOn hscale hle h

/-- **[capstone, ShawValueLandauBridge]** A literal Landau prize bound for any nonnegative
pointwise majorant transfers directly to the Shaw-value `O(1)` statement for the dominated target.
This is the consumer-facing majorant composition rung for the Lane-2 `prize ⇔ Sh(n)=O(1)` reduction;
it is pure order/normalization bookkeeping and proves no new Gauss-period estimate. -/
theorem doorIV_landau_shaw_of_dominated_majorant_export {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i)
    (hscale : ∀ i, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (ProximityGap.Frontier.ShawValueCapstone.supSeq M) =O[atTop]
      (ProximityGap.Frontier.ShawValueCapstone.scaleSeq q n)) :
    (ProximityGap.Frontier.ShawValueCapstone.shawSeq q n M') =O[atTop]
      (fun _ => (1 : ℝ)) :=
  ProximityGap.Frontier.ShawValueCapstone.shawSeq_isBigO_one_of_le_prizeBigO
    hM'nn hscale hle h

/-- **[capstone, ShawValueLandauBridge]** The same dominated-majorant transfer in the campaign's
`ShawOOneOn` predicate: a Landau prize-scale bound for a pointwise majorant gives a global uniform
`Sh(n)=O(1)` bound for every nonnegative dominated target. -/
theorem doorIV_shawOOne_of_dominated_majorant_export {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i)
    (hscale : ∀ i, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (ProximityGap.Frontier.ShawValueCapstone.supSeq M) =O[atTop]
      (ProximityGap.Frontier.ShawValueCapstone.scaleSeq q n)) :
    ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_of_le_prizeBigO hM'nn hscale hle h


/-! ## JacobiCocycleDispersion — the named door-(iv) missing theorem, permanently indexed.
Scope: **capstone**. The point of this section is discoverability: the #444 reduction does not
leave an anonymous anti-concentration obligation, but the explicit predicate
`JacobiCocycleDispersion M C n m`, exactly equivalent to a bounded Shaw value with `L = log m`.
These exports are direct aliases of the proven Lane-2 wrappers; they do NOT prove the missing
Jacobi dispersion theorem, and make no CORE/cancellation/completion/moment/capacity claim. -/

/-- **[obstruction, JacobiCocycleDispersion]** The degenerate trivial cocycle has full
concentration at a support frequency: if the written phase ratio satisfies `ζ^k = 1`, the length-`n`
fiber is exactly `n`. This is the baseline the missing Jacobi dispersion theorem must destroy. -/
theorem trivial_cocycle_full_concentration_export {n : ℕ} (hn : 0 < n) (ζ : ℂ) {k : ℕ}
    (hζk : ζ ^ k = 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = (n : ℂ) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_full_concentration
    hn ζ hζk

/-- **[obstruction, JacobiCocycleDispersion]** Off a support frequency, a trivial cocycle has exact
geometric cancellation. The on/off pattern shows that the named Door-IV theorem is not a normalization
artifact: it must rule out collapse to this degenerate support. -/
theorem trivial_cocycle_offSupport_zero_export {n : ℕ} (ζ : ℂ) {k : ℕ}
    (hpow : (ζ ^ k) ^ n = 1) (hoff : ζ ^ k ≠ 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_offSupport_zero
    ζ hpow hoff

/-- **[capstone, JacobiCocycleDispersion]** Pointwise form of the named door-(iv) target: the
Jacobi-cocycle dispersion predicate is exactly a Shaw-value bound with logarithmic thinness
parameter `L = log m`. -/
theorem jacobiCocycleDispersion_iff_shawValue_le_export {M C n m : ℝ}
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n (Real.log m)) :
    _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion M C n m ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n (Real.log m) ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersion_iff_shawValue_le hs

/-- **[capstone, JacobiCocycleDispersion]** Uniform nonnegative-constant form under the standard
thin-instance positivity hypotheses `0 < n_i` and `0 < log m_i`: bounded Jacobi-cocycle dispersion
is equivalent to `Sh=O(1)`. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Wall-facing uniform form: under the standard positivity
hypotheses, failing to find any nonnegative Jacobi-dispersion constant is exactly failing to find any
nonnegative Shaw-value constant. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    ¬ (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Raw-sandwich invariance for the named Jacobi target:
if a downstream door-(iv) quantity `H` is uniformly between `M` and `K*M`, then boundedness of
Jacobi-cocycle dispersion transfers exactly up to constants. -/
theorem exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
    {ι : Type*} {M H n m : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound H n m C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_jacobiCocycleDispersionFamilyBound_iff_of_rawSandwich
    hK hMH hHM

/-! ## DoorIVObject — the single live door-(iv) open object is moment-trapped (Lane-1 close-out).
Scope: **capstone**. The worst-frequency coset-half coherence sup of the monomial sum (the sole live
open object of the tetrachotomy) is, in every measurement (n=16..128, multiple structured primes),
moment-trapped: bounded below by the iid-unit-phase (extreme-value) surrogate floor `iidSup`, with the
gap above it bounded by the additive-energy (moment) excess `Δ`. Equivalently the object sup is pinned
to the corridor `[iidSup, iidSup + Δ]`. No non-moment, non-extreme-value slack survives. CORE stays
open; no cancellation/anti-concentration/capacity claim. (#444, probes
`probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`, `probe_dooriv_cocycle_excess_structure.py`.) -/

/-- **[capstone, DoorIVObject]** The door-(iv) object sup is pinned to the moment-corridor: under the
no-edge floor (`iidSup ≤ realSup`) and the excess-is-moment bound (`realSup − iidSup ≤ Δ`), the real
sup satisfies `iidSup ≤ realSup ≤ iidSup + Δ`. -/
theorem doorIV_object_moment_corridor_export {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess : _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.realSup_in_moment_corridor
    hEdge hExcess

/-- **[capstone, DoorIVObjectMomentTrapped]** Conjunctive no-slack form for the single live
Door-IV object: the real cocycle sup has no edge below the iid/extreme-value surrogate, and its
advantage above the surrogate cannot exceed the additive-energy/moment excess. -/
theorem doorIV_object_moment_trapped_no_slack_export {iidSup realSup δ Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hMoment : _root_.ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment.MomentSourced δ Δ) :
    (¬ realSup < iidSup) ∧ (¬ Δ < δ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone.doorIV_object_moment_trapped
    hEdge hMoment

/-- **[capstone, DoorIVObjectMomentTrapped]** Any proposed upper bound on the real Door-IV object
must also dominate the iid/extreme-value surrogate, while the real-over-iid advantage remains capped
by the door-(i) moment ceiling. This is the object-level two-dead-doors constraint. -/
theorem doorIV_candidate_bound_forced_through_dead_doors_export
    {iidSup realSup δ Δ B Bm : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hMoment : _root_.ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment.MomentSourced δ Δ)
    (hReal : realSup ≤ B) (hCeil : Δ ≤ Bm) :
    iidSup ≤ B ∧ δ ≤ Bm :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone.candidate_bound_forced_through_dead_doors
    hEdge hMoment hReal hCeil

/-- **[capstone, DoorIVObjectMomentTrapped]** Falsifiable audit form: object moment-trapping is
exactly the pair of measured hypotheses `iidSup ≤ realSup` and `0 ≤ δ ∧ δ ≤ Δ`. A future probe must
break one of these two inequalities to reopen this lever. -/
theorem doorIV_object_moment_trapped_iff_export {iidSup realSup δ Δ : ℝ} :
    (_root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal iidSup realSup ∧
      _root_.ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment.MomentSourced δ Δ) ↔
      (iidSup ≤ realSup ∧ (0 ≤ δ ∧ δ ≤ Δ)) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone.moment_trapped_iff

/-- **[capstone, DoorIVObject]** The grand three-pillar statement of the #444 structural result: from
the standard thin-instance positivity, the proven classical-overshoot refutations, and the two measured
facts about the door-(iv) object, ALL THREE pillars hold simultaneously — (1) the prize ⇔ `Sh=O(1)`
reduction, (2) the door-(iv)-only mechanism exclusion, and (3) the object moment-corridor
`[iidSup, iidSup + Δ]`. The single citable statement: the prize is a bounded Shaw value, deliverable
only through door (iv), whose open object is moment-trapped. CORE stays open. -/
theorem prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    ((∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref →
        m.door =
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.prize_iff_shawBounded_doorIV_only_and_object_moment_trapped
    hs hnref hLref hclassicalOvershoots hEdge hExcess

/-- **[capstone, DoorIVObject]** The grand FOUR-pillar statement: the three pillars above PLUS the
unconditional floor envelope `[c₀, √nref]` (`c₀ = (5/4)^{1/4}`).  From the proven super-diagonal period
floor `c₀·√nref ≤ Mref` and the trivial cardinality ceiling `Mref ≤ nref` — with NO door hypothesis —
the floor-normalized worst-frequency ratio `Mref/√nref` lives in `[c₀, √nref]`.  This records, in the
single citable statement, the bracket inside which the entire open problem lives: the prize is the
demand to collapse the unconditional `√nref` ceiling to an absolute constant, with the conditional
door ceiling `√L` sitting strictly inside.  Packaging extension; CORE stays open. -/
theorem prize_iff_shawBounded_doorIV_only_object_trapped_and_floor_bracketed_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ)
    {Mref : ℝ}
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst *
      Real.sqrt nref ≤ Mref)
    (hceil : Mref ≤ nref) :
    ((∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref →
        m.door =
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) ∧
      (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst ≤
          _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
            Mref nref ∧
        _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
            Mref nref ≤ Real.sqrt nref) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.prize_iff_shawBounded_doorIV_only_object_trapped_and_floor_bracketed
    hs hnref hLref hclassicalOvershoots hEdge hExcess hfloor hceil

/-- **[capstone, DoorIVObject]** The DISCHARGED grand four-pillar statement: pillars (1) reduction and
(2) door-(iv)-only exclusion are the THEOREM-BACKED discharged form (no abstract overshoot hypothesis;
the classical-overshoot input is discharged from the SOTA eventual-domination theorem past a threshold
`N₀`, with only the honest anti-degenerate `RespectsProvenScale` guard surviving), fused with (3) the
object moment-corridor and (4) the unconditional floor envelope `[c₀, √nref]`.  The first single
citable statement combining the discharged reduction+exclusion with both object-trap and floor
envelope.  CORE stays open. -/
theorem prize_reduction_dischargedDoorIV_object_trapped_and_floor_bracketed_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {Lref q C δ : ℝ} (hLnn : 0 ≤ Lref) (hLref : 1 < Lref) (hC : 0 < C) (hδ : δ < 1 / 2)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ)
    {Mref nref : ℝ} (hnref : 0 < nref)
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst *
      Real.sqrt nref ≤ Mref)
    (hceil : Mref ≤ nref) :
    ∃ N₀ : ℝ,
      ((∃ K, 0 ≤ K ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L K) ↔
          (∃ K, 0 ≤ K ∧
            _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L K)) ∧
        (∀ nref' : ℝ, max N₀ 1 ≤ nref' → nref' * Lref ≤ q →
          (∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref') →
          ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
            m.certScale ≤
              _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref' →
            m.door =
              _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
        (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) ∧
        (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst ≤
            _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
              Mref nref ∧
          _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
              Mref nref ≤ Real.sqrt nref) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.prize_reduction_dischargedDoorIV_object_trapped_and_floor_bracketed
    hs hLnn hLref hC hδ hEdge hExcess hnref hfloor hceil

/-- **[capstone, DoorIVObject]** The WALL-FACING (contrapositive) discharged grand four-pillar
statement: (1') the negated reduction `¬ prizeBound ↔ ¬ shawBound` (the prize is impossible iff the
Shaw value is unbounded), with (2) the theorem-backed discharged door-(iv)-only exclusion past `N₀`,
(3) the object moment-corridor, and (4) the unconditional floor envelope `[c₀, √nref]`.  The
contrapositive companion of `..._reduction_dischargedDoorIV_..._export`, suitable for the "why the
prize is hard" citation.  CORE stays open. -/
theorem no_prizeBound_dischargedDoorIV_object_trapped_and_floor_bracketed_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {Lref q C δ : ℝ} (hLnn : 0 ≤ Lref) (hLref : 1 < Lref) (hC : 0 < C) (hδ : δ < 1 / 2)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ)
    {Mref nref : ℝ} (hnref : 0 < nref)
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst *
      Real.sqrt nref ≤ Mref)
    (hceil : Mref ≤ nref) :
    ∃ N₀ : ℝ,
      (¬ (∃ K, 0 ≤ K ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L K) ↔
          ¬ (∃ K, 0 ≤ K ∧
            _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L K)) ∧
        (∀ nref' : ℝ, max N₀ 1 ≤ nref' → nref' * Lref ≤ q →
          (∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref') →
          ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
            m.certScale ≤
              _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref' →
            m.door =
              _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
        (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) ∧
        (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.superDiagonalFloorConst ≤
            _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
              Mref nref ∧
          _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio
              Mref nref ≤ Real.sqrt nref) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.no_prizeBound_dischargedDoorIV_object_trapped_and_floor_bracketed
    hs hLnn hLref hC hδ hEdge hExcess hnref hfloor hceil

/-! ## DoorIVSignedDeepSumAbsLeak — the absolute-value leak made permanent.
Scope: **obstruction / positive localization**. The signed deep period-power probe found the
thinness-essential signal in `Σ η_b^r`, while all moment / energy packages pass through
`Σ |η_b|^r` and discard cancellation. These permanent exports expose the kernel-checked
triangle-inequality leak and its monotone transfer direction. They do NOT prove the open
uniform signed deep-cancellation bound, and make no CORE/cancellation/completion/capacity claim. -/

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Absolute-value / moment packaging can
only upper-bound the signed deep sum through the triangle-inequality leak:
`|Σ η_b^r| ≤ Σ |η_b|^r`. The gap is exactly the signed cancellation thrown away by
moment methods. -/
theorem doorIV_abs_signed_le_abs_moment_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    |∑ b ∈ s, (η b) ^ r| ≤ ∑ b ∈ s, |η b| ^ r := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_signed_le_abs_moment
    s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** The leak gap is nonnegative:
absolute moments minus the signed deep sum magnitude are a real discarded-cancellation
budget, never a saving. -/
theorem doorIV_leak_nonneg_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    0 ≤ (∑ b ∈ s, |η b| ^ r) - |∑ b ∈ s, (η b) ^ r| := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_nonneg s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Any absolute-moment bound transfers
only one way, to a bound on the signed sum. The converse is false (kernelized in the
source file), so a signed deep-cancellation certificate cannot be recovered from an
absolute-value certificate. -/
theorem doorIV_abs_moment_bound_transfers_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) {B : ℝ}
    (hB : ∑ b ∈ s, |η b| ^ r ≤ B) :
    |∑ b ∈ s, (η b) ^ r| ≤ B := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_moment_bound_transfers
    s η r hB


/-! ## JacobiCocycleTrivialOvershoot — the trivial baseline fails the thin prize target.
Scope: **obstruction**. The trivial cocycle's full `n`-spike is not a dispersion witness in the
prize regime `n > C² log m`; it overshoots the target `C√(n log m)` by a positive amount.
These exports pin the gap the genuine Jacobi cocycle must close, without proving it closes it. -/

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the thin prize regime
`C² log m < n`, the trivial-cocycle baseline `M = n` fails the named Jacobi dispersion predicate.
This is the kernel-checked version of "the genuine cocycle must break the full `n`-spike." -/
theorem trivial_cocycle_overshoots_thin_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion
      n C n (Real.exp logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_cocycle_overshoots_thin
    hn hC hlogm hthin

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the same thin regime, the additive
overshoot gap `n - C√(n log m)` of the trivial spike is strictly positive. The open Door-IV
work is exactly to make the genuine cocycle disperse enough to remove this gap. -/
theorem trivial_overshoot_gap_pos_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    0 < n - C * Real.sqrt (n * logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_overshoot_gap_pos
    hn hC hlogm hthin


/-! ## JacobiCocycleAllDefectCSVacuous — Cauchy--Schwarz has zero floor at full defect.
Scope: **obstruction**. The k-defect deficit floor degenerates exactly in the adversarial
all-defect regime `k = M`: its lower bound is `0`, leaving only the trivial ceiling. This locks
Shaw's Lever-B / L²-budget refutation as a permanent indexed constraint lemma. -/

/-- **[obstruction, JacobiCocycleAllDefectCSVacuous]** In the all-defect regime, the
Cauchy--Schwarz k-defect floor is exactly zero and the only remaining consequence is the
trivial ceiling on the phase sum. Thus the metric L²-budget route cannot certify prize-scale
cancellation at `k = M`. -/
theorem allDefect_cs_floor_vacuous_export (M : ℕ) (hM : 1 ≤ M) (w : Fin M → ℂ)
    (hunit : ∀ i, ‖w i‖ = 1) :
    ((M : ℝ) - (Finset.univ : Finset (Fin M)).card)
        * (∑ i ∈ (Finset.univ : Finset (Fin M)), (1 - (w i).re)) / (M : ℝ) = 0
      ∧ ‖_root_.ProximityGap.Frontier.DyadicJacobiCocycleNonContraction.phaseSum
            (_root_.ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefectFamily
              (Finset.univ : Finset (Fin M)) w)‖ ≤ (M : ℝ) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous.allDefect_cs_floor_vacuous
    M hM w hunit


/-! ## GaussSumEnergyStep / DilationMultEnergyStep — the exact deep-step assault.
Scope: **capstone / obstruction**. These exports permanently index the focused Door-IV
Paley-kernel assault at the exact increment/off-diagonal level. The K=1 increment closes
unconditionally; the all-K step is reduced to the named tilted-increment input; and the
dilation split isolates the remaining BGK wall as off-diagonal/depth-`2K` cancellation.
No CORE bound is claimed. -/

/-- **[capstone, GaussSumEnergyStep]** The `K = 1` tilted-energy increment is strictly below
`2n` for every rational parameter pair `4 ≤ n < p`. This is the one unconditional closed-form
multiplicative-subgroup rung of the Paley/BGK deep step. -/
theorem gaussEnergyStep_incrementOne_lt_two_n_export
    (n p : ℚ) (hn : 4 ≤ n) (hpn : n < p) :
    (3 * p * (n - 1) - n ^ 3) / (p - n) - n * (p - n) / (p - 1) < 2 * n :=
  _root_.Issue444.GaussSumEnergyStep.incrementOne_lt_two_n n p hn hpn

/-- **[capstone, GaussSumEnergyStep]** The exact telescope reduction: if every tilted increment
is at most `2n`, then every deep-step ratio satisfies `r K ≤ (2K+1)n`. The hypothesis for
`K ≥ 2` is exactly the open tilted-variance/BGK input; this export records the reduction only. -/
theorem gaussEnergyStep_step_of_increments_le_export
    (n : ℚ) (r : ℕ → ℚ) (hr0 : r 0 ≤ n)
    (hincr : ∀ K, r (K + 1) - r K ≤ 2 * n) :
    ∀ K, r K ≤ (2 * (K : ℚ) + 1) * n :=
  _root_.Issue444.GaussSumEnergyStep.step_of_increments_le n r hr0 hincr

/-- **[capstone, DilationMultEnergyStep]** The exact diagonal split turns the deep step
`A_{K+1} ≤ (2K+1)nA_K` into the off-diagonal inequality `OFF ≤ 2KnA_K`. This is the
load-bearing algebraic reduction supplied by multiplicative dilation invariance. -/
theorem dilationEnergy_step_iff_offdiagonal_export
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off) :
    (Akp1 ≤ (2 * K + 1) * n * Ak) ↔ (off ≤ 2 * K * n * Ak) :=
  _root_.Issue444.DilationMultEnergyStep.step_iff_offdiagonal Akp1 Ak off n K hsplit

/-- **[obstruction, DilationMultEnergyStep]** The Cauchy--Schwarz route from the off-diagonal
piece proves the deep step only after assuming the depth-`2K` energy/Wick input
`Em·Ephi ≤ (2K n A_K)^2`. Thus the dilation lever reduces to, but does not discharge, the
BGK wall. -/
theorem dilationEnergy_deep_step_of_depth2K_energy_export
    (Akp1 Ak off Em Ephi : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_nonneg : 0 ≤ off)
    (hCS : off ^ 2 ≤ Em * Ephi)
    (htarget_nonneg : 0 ≤ 2 * K * n * Ak)
    (hdepth : Em * Ephi ≤ (2 * K * n * Ak) ^ 2) :
    Akp1 ≤ (2 * K + 1) * n * Ak :=
  _root_.Issue444.DilationMultEnergyStep.deep_step_of_depth2K_energy
    Akp1 Ak off Em Ephi n K hsplit hoff_nonneg hCS htarget_nonneg hdepth


/-- **[obstruction, DilationMultEnergyStep]** Probe-facing contrapositive of the diagonal split:
if the off-diagonal piece exceeds `2K n A_K`, the deep step itself is false. -/
theorem dilationEnergy_not_deep_step_of_offdiagonal_gt_export
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_gt : 2 * K * n * Ak < off) :
    ¬ Akp1 ≤ (2 * K + 1) * n * Ak :=
  _root_.Issue444.DilationMultEnergyStep.not_deep_step_of_offdiagonal_gt
    Akp1 Ak off n K hsplit hoff_gt

/-- **[obstruction, DilationMultEnergyStep]** If Cauchy--Schwarz certifies
`OFF² ≤ Em·Ephi` while the target is already below `OFF`, then the depth-`2K` energy budget
`Em·Ephi ≤ target²` is impossible. This names the exact BGK-wall failure mode. -/
theorem dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export
    (off Em Ephi target : ℚ)
    (hoff_nonneg : 0 ≤ off)
    (htarget_nonneg : 0 ≤ target)
    (hoff_gt : target < off)
    (hCS : off ^ 2 ≤ Em * Ephi) :
    ¬ Em * Ephi ≤ target ^ 2 :=
  _root_.Issue444.DilationMultEnergyStep.not_depth2K_energy_of_cs_and_offdiagonal_gt
    off Em Ephi target hoff_nonneg htarget_nonneg hoff_gt hCS


/-! ## DoorIVDecompositionInvariantCoherence — partition-invariant coherence saturation.
Scope: **obstruction**. These exports make the newest Lane-1 partition no-go permanent: if the
underlying terms already lie on a common nonnegative ray at the adversarial frequency, then every
partition of those terms has multi-piece coherence exactly `1`. Non-negation-stable / asymmetric /
finer partitions cannot create a coherence saving; any useful theorem must break term-level co-ray
alignment, i.e. the original CORE sup-norm problem. -/

/-- **[obstruction, DoorIVDecompositionInvariant]** Common-ray terms group to common-ray
block-sums under any partition map. -/
theorem doorIV_decomposition_block_sum_common_ray_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (k : κ) :
    (∑ i ∈ t.filter (fun i => g i = k), f i)
      = (∑ i ∈ t.filter (fun i => g i = k), c i) • u
    ∧ 0 ≤ (∑ i ∈ t.filter (fun i => g i = k), c i) :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.block_sum_common_ray
    t f u c hf hc g k

/-- **[obstruction, DoorIVDecompositionInvariant]** Headline partition-invariance theorem:
common-ray term alignment forces grouped multi-piece coherence to equal `1` for every partition. -/
theorem doorIV_decomposition_partition_invariant_coherence_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s)
    (hmass : 0 < ∑ i ∈ t, c i) (hu : u ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence s
      (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) = 1 :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.multiPieceNormCoherence_block_eq_one_of_common_ray t s f u c hf hc g hcover hmass hu

/-- **[obstruction, DoorIVDecompositionInvariant]** Constraint form: while the terms are
common-ray aligned, no partition can certify a strict coherence bound `≤ θ < 1`. -/
theorem doorIV_decomposition_no_partition_beats_one_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) {θ : ℝ}
    (hθ : θ < 1)
    (hray : ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ t, f i = c i • u) ∧ (∀ i ∈ t, 0 ≤ c i) ∧
      0 < (∑ i ∈ t, c i) ∧ u ≠ 0)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s) :
    ¬ _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence s
        (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) ≤ θ :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.no_partition_beats_one_of_common_ray_terms t s f hθ hray g hcover

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Real refined-piece coherence has the
closed-unit-interval ceiling `0 ≤ coherence ≤ 1` whenever its `L¹` denominator is positive. Therefore
all nontrivial door-(iv) content starts only at a strict subunit bound `≤ 1 - ε`; the signed-mass
exports below identify the exact minority-mass payment for that slack. -/
theorem doorIV_multiPiece_coherence_mem_Icc_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) (hpos : 0 < ∑ i ∈ s, |A i|) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ∈
      Set.Icc (0 : ℝ) 1 :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_mem_Icc s A hpos

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact saving identity for real refined
piece coherence. After compression to aggregate positive/negative masses, the slack below saturation
is precisely `2·minority/total`; refinement alone creates no hidden cancellation term. -/
theorem doorIV_multiPiece_exact_saving_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    1 - _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A =
      (2 * min posMass negMass) / (posMass + negMass) :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.one_sub_multiPieceCoherence_eq_two_mul_min_ratio
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact epsilon-budget equality interface for real
refined piece coherence. A certificate `coherence = 1 - ε` is equivalent to the exact
minority-sign payment `ε·total = 2·minority`. -/
theorem doorIV_multiPiece_eps_budget_eq_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A = 1 - ε ↔
      ε * (posMass + negMass) = 2 * min posMass negMass :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_eq_one_sub_iff_eps_mass_budget_eq
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact epsilon-budget interface for real refined
piece coherence. A certificate `coherence ≤ 1 - ε` is equivalent to the denominator-cleared minority
sign-mass obligation `ε·total ≤ 2·minority`; subdivision alone cannot create door-(iv) slack. -/
theorem doorIV_multiPiece_eps_budget_iff_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ≤ 1 - ε ↔
      ε * (posMass + negMass) ≤ 2 * min posMass negMass :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_le_one_sub_iff_eps_mass_budget
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** One-sided aggregate sign mass forbids any
positive epsilon saving for a real refined split. This is the consumer-facing contrapositive of the
exact budget: if one side has zero mass, no bound `coherence ≤ 1 - ε` with `ε > 0` can hold. -/
theorem doorIV_multiPiece_no_eps_slack_one_side_zero_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hzero : posMass = 0 ∨ negMass = 0) (hε : 0 < ε) :
    ¬ _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ≤ 1 - ε :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.not_multiPieceCoherence_le_one_sub_eps_of_one_side_zero
    s A hsum hden hposMass hnegMass htotal hzero hε

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Single-window occupancy certificates
force the trivial cardinality budget. If the in/out window triangle RHS is at most `B`, then already
`|s| ≤ B`; a coarse small-ball count alone cannot beat the linear ceiling. -/
theorem doorIV_window_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) {B : ℝ}
    (hbudget : (W.card : ℝ) + ((s \ W).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_budget_forces_card_le
    hW hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Two-window occupancy certificates force the
trivial cardinality budget. If two disjoint windows and the outside complement fit under `B`, then
already `|s| ≤ B`; any sublinear certificate must use phase cancellation, not occupancy bookkeeping. -/
theorem doorIV_twoWindow_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s W₁ W₂ : Finset ι} (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂)
    {B : ℝ}
    (hbudget : (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.two_window_budget_forces_card_le
    h₁ h₂ hdis hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Finite multi-window occupancy certificates
force the trivial cardinality budget. If the disjoint-window triangle RHS is at most `B`, then
already `|s| ≤ B`; coarse small-ball bookkeeping alone cannot beat the linear ceiling. -/
theorem doorIV_multiWindow_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ}
    (hbudget : (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.multi_window_budget_forces_card_le
    hsub hdis hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Strict finite multi-window small-ball
certificates are impossible without extra phase cancellation: the occupancy split RHS is exactly
`|s|`, so it cannot fit under any strict budget `B < |s|`. -/
theorem doorIV_no_multiWindow_split_rhs_le_strict_budget_export {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ} (hB : B < (s.card : ℝ)) :
    ¬ (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.no_multi_window_split_rhs_le_strict_budget
    hsub hdis hB

#print axioms doorIV_window_budget_forces_card_le_export
#print axioms doorIV_twoWindow_budget_forces_card_le_export
#print axioms doorIV_multiWindow_budget_forces_card_le_export
#print axioms doorIV_no_multiWindow_split_rhs_le_strict_budget_export

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** A uniform multiplicative control of the
sup-norm `target` by a candidate functional `F` evaluated at the target's worst frequency `bstar`
(with `F bstar > 0`) FORCES the constant `C ≥ target bstar / F bstar`.  When `F` is decoupled and
small at the worst frequency (probe `smallball_vs_energy`: argmax mismatch at every n), this forces a
large constant. -/
theorem doorIV_argmaxDecoupled_const_ge_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (hFpos : 0 < F bstar) :
    target bstar / F bstar ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.const_ge_ratio_at_argmax
    hctrl hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** A claimed absolute constant strictly below the
measured worst-frequency ratio `target bstar / F bstar` (with `F bstar > 0`) is impossible: there is
no such uniform control. -/
theorem doorIV_argmaxDecoupled_no_control_below_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hbelow : C < target bstar / F bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_control_below_measured_ratio
    hFpos hbelow

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Exact ratio-envelope characterization:
when the candidate functional is strictly positive at every frequency, `target ≤ C·F` is equivalent to
bounding every pointwise ratio `target i / F i` by `C`. Thus absolute control is exactly a uniform
bound on the ratio envelope, not an argmax-only phenomenon. -/
theorem doorIV_argmaxDecoupled_uniformControl_iff_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hFpos : ∀ i, 0 < F i) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C
      ↔ ∀ i, target i / F i ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControl_iff_ratio_le
    hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Ratio-envelope no-go: with positive candidate
values, a single frequency whose witness ratio exceeds `C` refutes the claimed `C`-control, whether or
not that frequency is an argmax of the target or candidate. -/
theorem doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hFpos : ∀ i, 0 < F i)
    (hwit : ∃ i, C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_exists_ratio_gt
    hFpos hwit


/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support monotonicity: control on a larger
measured support restricts to any smaller support. -/
theorem doorIV_argmaxDecoupled_uniformControlOn_of_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      t target F C) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControlOn_of_subset
    hst hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support obstruction propagates upward:
if `C`-control fails on a measured sub-support, it fails on every larger support containing it. -/
theorem doorIV_argmaxDecoupled_no_controlOn_superset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hno : ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn t target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_subset_not_control
    hst hno

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support exact ratio-envelope
characterization: on the enumerated probe support `s`, positive-candidate control is equivalent to
bounding every support ratio `target i / F i`. This is the finite-frequency form used by door-(iv)
small-ball/window probes, without silently claiming control outside the measured support. -/
theorem doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hFpos : ∀ i ∈ s, 0 < F i) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C
      ↔ ∀ i ∈ s, target i / F i ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControlOn_iff_ratio_le_on
    hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support ratio witness no-go: if one
measured frequency in the probe support has ratio above `C`, then there is no `C`-control even on that
finite support. -/
theorem doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hFpos : ∀ i ∈ s, 0 < F i)
    (hwit : ∃ i ∈ s, C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_exists_ratio_gt_on
    hFpos hwit



/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support sign hygiene: if a measured
support control holds at one point where both target and candidate are positive, then the control
constant is itself positive. -/
theorem doorIV_argmaxDecoupled_controlOn_constant_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) (hi : i ∈ s) (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.controlOn_constant_pos_of_positive_target_and_candidate
    hctrl hi hFpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support point-ratio no-go: a single
measured support point with positive candidate value and ratio above `C` refutes `C`-control on that
support, without assuming the candidate is positive at every measured frequency. -/
theorem doorIV_argmaxDecoupled_point_ratio_gt_no_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hi : i ∈ s)
    (hFpos : 0 < F i) (hgt : C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_point_ratio_gt_on
    hi hFpos hgt

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support family no-go: if the measured
support witness ratios are unbounded across a family, then every candidate absolute constant fails on
some measured support.  This is the finite-enumeration version of the unbounded-ratio obstruction. -/
theorem doorIV_argmaxDecoupled_no_absolute_constOn_export {ι N : Type*}
    {target F : N → ι → ℝ} {s : N → Finset ι} {bstar : N → ι}
    (hmem : ∀ n, bstar n ∈ s n)
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      (s n) (target n) (F n) C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_absolute_constantOn_of_unbounded_point_ratio
    hmem hFpos hunbdd

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support support constraint:
a positive `C`-control on the measured support `s` forces the candidate to be positive at every support
frequency where the target is positive. -/
theorem doorIV_argmaxDecoupled_candidate_pos_on_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) (hi : i ∈ s) (htpos : 0 < target i) :
    0 < F i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.candidate_pos_of_positive_controlOn_at_positive_target
    hCpos hctrl hi htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support support-inclusion form:
a positive `C`-control on `s` forces `{i | i ∈ s ∧ target i > 0} ⊆ {i | F i > 0}`. -/
theorem doorIV_argmaxDecoupled_positive_support_on_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) :
    {i | i ∈ s ∧ 0 < target i} ⊆ {i | 0 < F i} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.positiveTargetOn_subset_positiveCandidate_of_positive_controlOn
    hCpos hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support endpoint no-go: for any
nonnegative constant `C`, if a measured support frequency has positive target value but nonpositive
candidate value, then no `C`-control holds even on that finite support. -/
theorem doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFnonpos : F i ≤ 0) (htpos : 0 < target i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_nonpos_candidate_at_positive_target
    hC hi hFnonpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support zero endpoint: a nonnegative
constant cannot control a positive measured target point through a candidate that vanishes at that
support point. -/
theorem doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFzero : F i = 0) (htpos : 0 < target i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_zero_candidate_at_positive_target
    hC hi hFzero htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Nontrivial positive control forces the
constant positive: if `target ≤ C·F`, `F i > 0`, and `target i > 0` at even one frequency, then
`C > 0`. Thus positive-control support constraints require no extra sign assumption in the nonzero
positive-candidate regime. -/
theorem doorIV_argmaxDecoupled_control_constant_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {i : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.control_constant_pos_of_positive_target_and_candidate
    hctrl hFpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Endpoint no-go: for any nonnegative absolute
constant `C`, if the candidate functional is nonpositive at a strictly-positive target peak, then no
uniform multiplicative control exists. This covers the zero/small-window endpoint of the measured
argmax-decoupling obstruction. -/
theorem doorIV_argmaxDecoupled_no_nonpos_candidate_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι} (hC : 0 ≤ C)
    (hFnonpos : F bstar ≤ 0) (htpos : 0 < target bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_nonpos_candidate_at_positive_target
    hC hFnonpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Zero endpoint no-go: a nonnegative constant
cannot control a positive target peak through a candidate functional that vanishes at that peak. -/
theorem doorIV_argmaxDecoupled_no_zero_candidate_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι} (hC : 0 ≤ C)
    (hFzero : F bstar = 0) (htpos : 0 < target bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_zero_candidate_at_positive_target
    hC hFzero htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Positive-control support constraint: if
`target ≤ C·F` with `C > 0`, then `F` must be positive at every positive target frequency. -/
theorem doorIV_argmaxDecoupled_candidate_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {i : ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (htpos : 0 < target i) :
    0 < F i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.candidate_pos_of_positive_control_at_positive_target
    hCpos hctrl htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Set-level form: a positive multiplicative
control forces `{i | target i > 0} ⊆ {i | F i > 0}`.  A candidate whose positive support misses the
true target support is dead before any ratio estimate. -/
theorem doorIV_argmaxDecoupled_positive_support_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C) :
    {i | 0 < target i} ⊆ {i | 0 < F i} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.positiveTarget_subset_positiveCandidate_of_positive_control
    hCpos hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Family no-go: if the per-`n` worst-frequency
witness ratio is UNBOUNDED above (decoupling: the target peaks where `F` is small), then NO single
absolute constant `C` uniformly controls every family member — for each `C` some member fails. -/
theorem doorIV_argmaxDecoupled_no_absolute_const_export {ι N : Type*}
    {target F : N → ι → ℝ} {bstar : N → ι}
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl
      (target n) (F n) C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_absolute_constant_of_unbounded_ratio
    hFpos hunbdd
/-- **[obstruction, DoorIVCollisionExcessPigeonhole]** Collision-free mod-`p` reduction is
exactly injectivity on the char-0 source classes. The zero-defect regime is therefore an elementary
no-merge certificate, not a phase-coherence estimate. -/
theorem doorIV_collision_defect_eq_zero_iff_injOn_export {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card - (s.image f).card = 0 ↔ Set.InjOn f s :=
  _root_.ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole.defect_eq_zero_iff_injOn s f

/-- **[obstruction, DoorIVCollisionExcessPigeonhole]** Positive collision excess is exactly
non-injectivity of the reduction map on the source classes. Thus `Ψ₀ - Ψ_p > 0` certifies a merge
witness only; by itself it is not a cancellation or CORE upper-bound lever. -/
theorem doorIV_collision_defect_pos_iff_not_injOn_export {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    0 < s.card - (s.image f).card ↔ ¬ Set.InjOn f s :=
  _root_.ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole.defect_pos_iff_not_injOn s f

/-- **[obstruction, door-(iv) Lane-1]** The STRICT worst-frequency peak is a SINGLE coset
(`Ncos(τ→0)=1`).  For an orbit-constant statistic `f` (the `μ_n`-invariant `|η_·|`) whose maximum
value `Mval` is attained at `b₀`, IF every strict maximizer lies in the orbit `G • b₀` (the measured
fact `Ncos(2%)=1`, n=16,32,64), then the exact argmax set is PRECISELY that single orbit.  The worst
frequency peak is isolated, not spread; any door-(iv) Lane-1 'spread the worst-b set' slack lives only
in the near-peak shell `τ>0` = a moment average = dead door (i). -/
theorem doorIV_strict_peak_single_coset_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    (hf : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.OrbitConstant (G := G) f)
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      = MulAction.orbit G b₀ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet_eq_single_orbit
    hf hb₀ hsingle

/-- **[obstruction, door-(iv) Lane-1]** Every strict maximizer is a coset translate of `b₀`:
`f b = Mval ↔ ∃ g, g • b₀ = b`.  No NEW arithmetic frequency outside the one peak coset is ever a
strict maximizer — the worst-b selector is coset-blind at the peak. -/
theorem doorIV_strict_maximizer_iff_translate_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    (hf : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.OrbitConstant (G := G) f)
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) (b : β) :
    f b = Mval ↔ ∃ g : G, g • b₀ = b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.isMaximizer_iff_translate
    hf hb₀ hsingle b

/-- **[obstruction, door-(iv) Lane-1]** The literal `Ncos = 1` count: under the single-coset
hypothesis, the image of the exact argmax set under the orbit-quotient map `β → β /ₘ G` is the single
class `{⟦b₀⟧}` — the strict peak meets EXACTLY ONE orbit. -/
theorem doorIV_strict_peak_Ncos_eq_one_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) :
    (fun x => Quotient.mk (MulAction.orbitRel G β) x) ''
        _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      = {Quotient.mk (MulAction.orbitRel G β) b₀} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.orbitQuot_image_argmaxSet_eq_singleton
    hb₀ hsingle


/-! ## Door-IV Lane 2 Hankel/Toda route-to-moments exports.
Scope: **obstruction/capstone**.

These exports make the form-(D) Hankel-ratio honesty constraint permanent. The Jacobi
recurrence target `max_k b_k` is bounded and numerically stable, but under the classical
Hankel-functional model it is a function of the moment vector through depth `2*k*`. Thus a
certificate for `maxb` is exactly a certificate for that deep-moment functional. The Jacobi
repackaging relocates the wall but does not create an independent fifth door.
-/

/-- **[obstruction, HankelRoutes]** Under the Hankel-functional model, bounding the Jacobi
recurrence target `maxb` by `T` is exactly the deep-moment sublevel statement `F m ≤ T`. -/
theorem doorIV_hankelRoutes_maxb_le_iff_moment_functional_le_export {kstar : ℕ} {maxb T : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : _root_.ProximityGap.Frontier.HankelRoutes.HankelFunctional kstar maxb F m) :
    maxb ≤ T ↔ F m ≤ T :=
  _root_.ProximityGap.Frontier.HankelRoutes.maxb_le_iff_moment_functional_le h

/-- **[obstruction, HankelRoutes]** Same deep-moment vector, same Hankel functional, same `maxb`:
the bounded Jacobi target contains no independent information beyond the moment vector it consumes. -/
theorem doorIV_hankelRoutes_maxb_determined_by_moments_export {kstar : ℕ} {maxb maxb' : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : _root_.ProximityGap.Frontier.HankelRoutes.HankelFunctional kstar maxb F m)
    (h' : _root_.ProximityGap.Frontier.HankelRoutes.HankelFunctional kstar maxb' F m) :
    maxb = maxb' :=
  _root_.ProximityGap.Frontier.HankelRoutes.maxb_determined_by_moments h h'

/-- **[obstruction, HankelRoutes]** A prize-scale Jacobi certificate routed through `maxb` is a
deep-moment statement `F m ≤ T`. Form (D)'s bounded `b_k` object therefore routes back through
form (A)'s deep moments rather than bypassing them. -/
theorem doorIV_hankelRoutes_prize_via_jacobi_is_moment_statement_export {kstar : ℕ} {maxb T : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : _root_.ProximityGap.Frontier.HankelRoutes.HankelFunctional kstar maxb F m)
    (hprize : maxb ≤ T) : F m ≤ T :=
  _root_.ProximityGap.Frontier.HankelRoutes.prize_via_jacobi_is_moment_statement h hprize

#print axioms doorIV_hankelRoutes_maxb_le_iff_moment_functional_le_export
#print axioms doorIV_hankelRoutes_maxb_determined_by_moments_export
#print axioms doorIV_hankelRoutes_prize_via_jacobi_is_moment_statement_export


/-! ## Door-IV non-tensor wraparound-cross residual exports.
Scope: **reduction/obstruction**.

These exports make the newest non-tensor split citable: the char-`p` cross term is exactly the
char-`0` cross term plus the wraparound cross `ΔW`; the full `r`-linear Wick rung follows from
the proven char-`0` step plus the single open wraparound residual; and below wraparound onset the
residual is vacuous. This isolates the remaining BGK/Lam-Leung wall without claiming it.
-/

/-- **[reduction, NT5WrapCrossSplit]** Exact non-tensor cross decomposition:
`crossP = crossC0 + wrapStep`. The char-`p` residual is precisely the wraparound cross. -/
theorem doorIV_nonTensor_cross_succ_split_export (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ) :
    _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.crossP n Ep r =
      _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.crossC0 n Ec r +
        _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.wrapStep n Ec Ep r :=
  _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.cross_succ_split n Ec Ep r

/-- **[reduction, NT5WrapCrossSplit]** The full char-`p` `r`-linear Wick cross step follows from
the char-`0` non-tensor step plus the single open wraparound-cross residual. -/
theorem doorIV_nonTensor_charP_wickStep_of_char0_and_wrap_export
    (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hc0 : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.Char0WickStep n Ec r)
    (hwrap : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.WrapCrossBounded n Ec Ep r) :
    _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.crossP n Ep r ≤
      2 * r * (n * Ep r) :=
  _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.charP_wickStep_of_char0_and_wrap
    n Ec Ep r hc0 hwrap

/-- **[reduction, NT5WrapCrossSplit]** Consumable energy-rung form:
`E_{r+1}^{Fp} ≤ (2r+1)nE_r^{Fp}` from the char-`0` step and wraparound residual. -/
theorem doorIV_nonTensor_energyStep_of_char0_and_wrap_export
    (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hc0 : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.Char0WickStep n Ec r)
    (hwrap : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.WrapCrossBounded n Ec Ep r) :
    (Ep (r + 1) : ℤ) ≤ (2 * r + 1) * n * Ep r :=
  _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.energyStep_of_char0_and_wrap
    n Ec Ep r hc0 hwrap

/-- **[obstruction, NT5WrapCrossSplit]** Below wraparound onset (`W_r = W_{r+1} = 0`) the
wraparound residual is vacuous, so the split reduces to the char-`0` step alone. -/
theorem doorIV_nonTensor_wrapCross_vacuous_of_noWraparound_export
    (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hWr : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.W Ec Ep r = 0)
    (hWr1 : _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.W Ec Ep (r + 1) = 0) :
    _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.WrapCrossBounded n Ec Ep r :=
  _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.wrapCross_vacuous_of_noWraparound
    n Ec Ep r hWr hWr1

/-- **[obstruction, NT5WrapCrossSplit]** The `r`-linear non-tensor target is strictly below the
fixed-saving tensor ceiling whenever `2r+1 < n`; the split target is genuinely stronger. -/
theorem doorIV_nonTensor_tensor_dilution_strict_export
    (n : ℕ) (Ep : ℕ → ℕ) (r : ℕ) (hr : 1 ≤ r) (hrn : 2 * r + 1 < n) (hE : 0 < Ep r) :
    2 * (r : ℤ) * (n * Ep r) < n * (n - 1) * Ep r :=
  _root_.ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.tensor_dilution_strict n Ep r hr hrn hE

#print axioms doorIV_nonTensor_cross_succ_split_export
#print axioms doorIV_nonTensor_charP_wickStep_of_char0_and_wrap_export
#print axioms doorIV_nonTensor_energyStep_of_char0_and_wrap_export
#print axioms doorIV_nonTensor_wrapCross_vacuous_of_noWraparound_export
#print axioms doorIV_nonTensor_tensor_dilution_strict_export





/-- **[Lane 2 Door-IV Jacobi-cocycle capstone]** Bundles the three proven faces of the localized
Jacobi-cocycle gap into one permanent citable theorem: the exact cancellation factor, the forced
non-alignment mechanism under a flat prize budget, and the exclusion of the Fermat closed-form corner.
This is a characterization/reduction capstone only: it does NOT prove the missing cocycle dispersion,
CORE, cancellation, completion, moment saving, or capacity. -/
theorem doorIV_jacobiCocycle_characterization_export
    {C n m : ℝ} (hC : 0 < C) (hn : 0 < n) (hm : 1 < m)
    {pSub nNat mNat r a : ℕ}
    (hfac : pSub = nNat * mNat) (hnNat : nNat = 2 ^ a)
    (hr_odd : Odd r) (hr1 : 1 < r) (hr_dvd : r ∣ mNat)
    {M : ℕ} {γ : Fin M → ℂ}
    (hbudget : ‖_root_.ProximityGap.Frontier.DyadicJacobiCocycleNonContraction.phaseSum γ‖ ≤
      C * Real.sqrt ((M : ℝ) * Real.log M))
    (hgap : C * Real.sqrt ((M : ℝ) * Real.log M) < (M : ℝ)) :
    n / (C * Real.sqrt (n * Real.log m)) =
        _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.requiredCancellationFactor C n m
      ∧ (¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j, γ j = ζ)
      ∧ (∀ k, pSub ≠ 2 ^ k) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDoorIVCapstone.jacobiCocycle_doorIV_characterization
    hC hn hm hfac hnNat hr_odd hr1 hr_dvd hbudget hgap

#print axioms doorIV_jacobiCocycle_characterization_export


end ArkLib.ProximityGap.Frontier.CampaignProvenIndex

/-! ## Cone axiom audit — every permanent export above is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). -/
namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex
#print axioms char0_stepRatio_antitone_iff_sharpNewton
#print axioms char0_W3anti_of_sharpNewton_export
#print axioms char0_kstability_cross_le_wick
#print axioms char0_prize_moment_bound_unconditional
#print axioms char0_prize_moment_bound_sq_unconditional
#print axioms char0_nonprincipalEnergyBound_discharged
#print axioms char0_eta_pow_le_unconditional
#print axioms gaussian_moment_telescope
#print axioms convexOrder_gaussian_iff_wick_export
#print axioms prize_of_matchedGaussian_stepLaw_export
#print axioms eta_pow_le_of_nonprincipalEnergyBound_export
#print axioms moment_problem_does_not_give_wick_bracket
#print axioms cumulant_sign_route_refuted
#print axioms resonance_ceiling_below_prize_floor
#print axioms coeff_route_loose_export
#print axioms roughness_does_not_add_bad_primes_export
#print axioms prizeBound_iff_shawValue_le_export
#print axioms strictPrizeBound_iff_shawValue_lt_export
#print axioms strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export
#print axioms exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export
#print axioms not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export
#print axioms exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export
#print axioms not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export
#print axioms shawValue_worstPeriod_clean_corridor_export
#print axioms shawValue_clean_corridor_width_eq_export
#print axioms shawValue_bracket_width_eq_sqrt_export
#print axioms worstPeriod_sharp_bracket_export
#print axioms completion_vacuous_below_trivial_ceiling_export
#print axioms shawValue_worstPeriod_torsion_full_corridor_export
#print axioms worstPeriod_torsion_sharp_floor_export
#print axioms charP_wrap_gap_ge_two_mul_sq_export
#print axioms charP_wrap_gap_nonneg_of_logConcave_export
#print axioms charP_transfer_of_dominance_logConcave_export
#print axioms charP_stepRatioMonotoneAt_iff_gap_nonneg_export
#print axioms charP_stepRatioMonotone_false_n32_export
#print axioms charP_no_universal_positive_stepRatioMonotone_export
#print axioms rho_normalized_antitone_and_ceiling_incompatible_export
#print axioms rho_antitone_route_not_universal_export
#print axioms valueShift_nontrivial_forces_flat_histogram_export
#print axioms valueShift_step_zero_of_one_histogram_witness_export
#print axioms valueShift_route_vacuous_of_one_histogram_witness_export
#print axioms wraparound_markov_count_le_export
#print axioms wraparound_markov_bound_vacuous_below_mean_export
#print axioms wraparound_average_control_does_not_bound_sup_export
#print axioms doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export
#print axioms doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export
#print axioms doorIV_index_le_sq_of_scaledConstant_le_export
#print axioms doorIV_scaledConstant_le_iff_index_le_sq_export
#print axioms doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export
#print axioms doorIV_cosetInvariant_blind_to_order_export
#print axioms doorIV_cosetHitting_selector_bound_iff_global_export
#print axioms doorIV_strict_selector_bound_misses_coset_export
#print axioms doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export
#print axioms doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export
#print axioms doorIV_positive_additiveEnergyExcess_iff_not_sidon_export
#print axioms doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export
#print axioms doorIV_bddAbove_nonneg_normalizedPrize_export
#print axioms doorIV_bddAbove_nonneg_normalizedHalfMass_export
#print axioms doorIV_bddAbove_nonneg_rawPrize_export
#print axioms doorIV_bddAbove_nonneg_rawHalfMass_export
#print axioms doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export
#print axioms doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export
#print axioms doorIV_not_nonneg_rawPrize_iff_prizeDrift_export
#print axioms doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export
#print axioms doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export
#print axioms doorIV_not_bddAbove_prize_iff_halfMassDrift_export
#print axioms doorIV_not_bddAbove_halfMass_iff_prizeDrift_export
#print axioms doorIV_bddAbove_prize_iff_not_halfMassDrift_export
#print axioms doorIV_bddAbove_halfMass_iff_not_prizeDrift_export
#print axioms doorIV_corePrize_of_dominated_majorant_export
#print axioms doorIV_shawOOne_of_coreMajorant_export
#print axioms doorIV_landau_shaw_of_dominated_majorant_export
#print axioms doorIV_shawOOne_of_dominated_majorant_export
#print axioms trivial_cocycle_full_concentration_export
#print axioms trivial_cocycle_offSupport_zero_export
#print axioms jacobiCocycleDispersion_iff_shawValue_le_export
#print axioms exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
#print axioms two_faces_are_one_wall_export
#print axioms noFifthDoor_forces_doorIV_export
#print axioms prizeCertifying_subset_doorIV_export
#print axioms doorIV_corridor_export
#print axioms doorIV_corridor_width_pos_export
#print axioms bgkScale_eq_sqrtL_mul_prizeScale_export
#print axioms noFifthDoor_ceilingRespecting_classical_overshoots_export
#print axioms noFifthDoor_forces_doorIV_ceilingRespecting_export
#print axioms noFifthDoor_classical_prize_certificate_violates_provenScale_export
#print axioms noFifthDoor_prize_certificate_doorIV_or_violates_provenScale_export
#print axioms shawGrand_prize_reduces_to_doorIV_export
#print axioms shawGrand_prize_reduces_to_doorIV_of_pos_lt_export
#print axioms shawGrand_prize_reduces_to_doorIV_eventually_export
#print axioms noTighterBound_secondMoment_blind_export
#print axioms noTighterBound_from_symmetric_or_L2_export
#print axioms doorIV_object_moment_corridor_export
#print axioms doorIV_object_moment_trapped_no_slack_export
#print axioms doorIV_candidate_bound_forced_through_dead_doors_export
#print axioms doorIV_object_moment_trapped_iff_export
#print axioms prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
#print axioms prize_iff_shawBounded_doorIV_only_object_trapped_and_floor_bracketed_export
#print axioms prize_reduction_dischargedDoorIV_object_trapped_and_floor_bracketed_export
#print axioms no_prizeBound_dischargedDoorIV_object_trapped_and_floor_bracketed_export
#print axioms doorIV_abs_signed_le_abs_moment_export
#print axioms doorIV_leak_nonneg_export
#print axioms doorIV_abs_moment_bound_transfers_export
#print axioms trivial_cocycle_overshoots_thin_export
#print axioms trivial_overshoot_gap_pos_export
#print axioms allDefect_cs_floor_vacuous_export
#print axioms gaussEnergyStep_incrementOne_lt_two_n_export
#print axioms gaussEnergyStep_step_of_increments_le_export
#print axioms dilationEnergy_step_iff_offdiagonal_export
#print axioms dilationEnergy_deep_step_of_depth2K_energy_export
#print axioms dilationEnergy_not_deep_step_of_offdiagonal_gt_export
#print axioms dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export
#print axioms coreReduction_mStar_gt_of_BCHKS_fails_export
#print axioms coreReduction_mStar_le_iff_BCHKS_export
#print axioms coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export



/-! ## Door-IV odd signed moment census bridge. Scope: **obstruction/capstone**.

These exports make the exact algebra behind the odd-`r` signed-deep probes permanent: full period
moments equal a zero-sum census, deleting the principal `b = 0` term gives the prize-relevant
`b ≠ 0` identity, and vanishing census forces the rigid value `A_r = -|G|^r`. This pins the
sign-rigidity wall as an exact census identity, not a numerical artifact. -/

/-- **[capstone, GaussPeriodMomentCensus]** Full all-frequency moment ↔ additive zero-sum census
identity, valid at every depth `r` by character orthogonality. -/
theorem gaussPeriod_sum_eta_pow_eq_card_mul_zeroSumCensus_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b : F,
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = (Fintype.card F : ℂ) *
        (_root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r : ℂ) :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_eq_card_mul_zeroSumCensus
    hψ G r

/-- **[capstone, GaussPeriodMomentCensus]** Deleted `b ≠ 0` moment ↔ census identity: the
prize-relevant signed moment equals `|F|·W_r - |G|^r`, with the principal term removed exactly. -/
theorem gaussPeriod_sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = (Fintype.card F : ℂ) *
          (_root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r : ℂ)
        - (G.card : ℂ) ^ r :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub
    hψ G r

/-- **[obstruction, GaussPeriodMomentCensus]** Rigid odd-depth value: if the additive zero-sum
census is zero, the deleted signed moment is exactly `-|G|^r`. Thus the observed odd-`r` sign
rigidity is a census identity, not a sup-norm bound. -/
theorem gaussPeriod_sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hcensus : _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r = 0) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = -((G.card : ℂ) ^ r) :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero
    hψ G r hcensus

#print axioms gaussPeriod_sum_eta_pow_eq_card_mul_zeroSumCensus_export
#print axioms gaussPeriod_sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub_export
#print axioms gaussPeriod_sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero_export

/-! ## Door-IV signed-deep rigidity gap. Scope: **constraint/capstone**.

The signed-deep floor is not just a point: on a negation-closed `0`-free domain in characteristic
`≠ 2`, the deviation above `-|G|^r` lives on a `2q`-spaced lattice. These exports package the
probe-facing contrapositive: any claimed leakage smaller than the first `2q` step is no leakage at
all, hence the signed deep sum is exactly at its rigidity floor. -/

/-- **[constraint, SignedDeepRigidityCorner]** No sub-`2q` leakage: below the first parity-quantized
lattice step, the signed zero-sum count remains zero. -/
theorem doorIV_signedDeep_zeroSumCount_zero_of_deviation_lt_two_q_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {r : ℕ} (hr : r ≠ 0) (h2 : (2 : F) ≠ 0) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (h0 : (0 : F) ∉ G)
    (hsmall :
      (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)), (∑ x ∈ G, ψ x) ^ r).re + (G.card : ℝ) ^ r
        < 2 * (Fintype.card F : ℝ)) :
    _root_.ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount G r = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.zeroSumCount_eq_zero_of_deviation_lt_two_q
    hr h2 G hneg h0 hsmall

/-- **[constraint, SignedDeepRigidityCorner]** Sub-`2q` deviation collapses to the exact floor
`A_r = -|G|^r`; there is no tiny positive signed-deep structure to harvest before the open BGK-rate
regime begins. -/
theorem doorIV_signedDeep_eq_floor_of_deviation_lt_two_q_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {r : ℕ} (hr : r ≠ 0) (h2 : (2 : F) ≠ 0) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (h0 : (0 : F) ∉ G)
    (hsmall :
      (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)), (∑ x ∈ G, ψ x) ^ r).re + (G.card : ℝ) ^ r
        < 2 * (Fintype.card F : ℝ)) :
    (∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)), (∑ x ∈ G, ψ x) ^ r)
      = - (G.card : ℂ) ^ r :=
  _root_.ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.signedPeriodPow_eq_floor_of_deviation_lt_two_q
    hr h2 G hneg h0 hsmall

#print axioms doorIV_signedDeep_zeroSumCount_zero_of_deviation_lt_two_q_export
#print axioms doorIV_signedDeep_eq_floor_of_deviation_lt_two_q_export

/-! ## Door-IV sixth marginal cumulant collapse. Scope: **obstruction**.

These exports make the explicit 6th-marginal rung permanent: when the sixth connected cumulant
vanishes, the sixth moment is exactly its Wick/lower-cumulant value, hence any sixth-moment control
passes through the already-mapped 2nd/4th data. This complements the signed 3-3 connected-correlation
closure below; it is a no-new-sixth-order-lever statement only. -/

/-- **[obstruction, DoorIVSixthCumulant]** Vanishing sixth connected cumulant collapses the sixth
moment to its Wick value. -/
theorem doorIV_m6_eq_wick_of_sixth_cumulant_zero_export
    {m6 wick kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + wick) (hzero : kappa6 = 0) :
    m6 = wick :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_wick_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** Explicit lower-cumulant polynomial form: with `κ₆ = 0`,
`m₆ = 15·κ₄·κ₂ + 15·κ₂³`, so the sixth moment carries no independent sixth-order datum. -/
theorem doorIV_m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero_export
    {m6 kappa2 kappa4 kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + (15 * kappa4 * kappa2 + 15 * kappa2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * kappa4 * kappa2 + 15 * kappa2 ^ 3 :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** Central-moment polynomial form: with `κ₆ = 0`,
`m₆ = 15·m₄·m₂ - 30·m₂³`, a fixed polynomial in the dead Plancherel/energy data. -/
theorem doorIV_m6_eq_centralMoment_poly_of_sixth_cumulant_zero_export
    {m6 m2 m4 kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + (15 * (m4 - 3 * m2 ^ 2) * m2 + 15 * m2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * m4 * m2 - 30 * m2 ^ 3 :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_centralMoment_poly_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** A sixth-moment control gives no new door-(iv) lever once
`m₆` Wick-factorizes: the candidate is controlled by the lower-order Wick data. -/
theorem doorIV_control_passes_through_sixth_wick_export
    {M m6 wick : ℝ}
    (hctrl : M ≤ m6) (hfact : m6 = wick) :
    M ≤ wick :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.control_passes_through_sixth_wick
    hctrl hfact

#print axioms doorIV_m6_eq_wick_of_sixth_cumulant_zero_export
#print axioms doorIV_m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero_export
#print axioms doorIV_m6_eq_centralMoment_poly_of_sixth_cumulant_zero_export
#print axioms doorIV_control_passes_through_sixth_wick_export

/-! ## Door-IV connected-correlation hierarchy closure. Scope: **obstruction/capstone**.

These exports make the newest door-(iv) Lane-1/Lane-3 closure permanent: once the connected fourth
cumulant and the signed 3-3 / sixth-order connected cumulant vanish, every attempted bound routed
through the connected-correlation hierarchy through sixth order factors through the lower-order Wick
/ diagonal data already mapped dead. The order-uniform ladder lemma records the same obstruction for
any finite set of higher cumulant rungs. This is a no-new-correlation-lever statement only; it does
not prove CORE. -/

/-- **[obstruction, DoorIVCorrelationHierarchy]** If the connected triple correlation vanishes,
the canonical signed six-point functional `|κ₃|²` is exactly zero. Thus the first phase-sensitive
sixth-order object supplies no door-(iv) lower-bound content. -/
theorem doorIV_sixPoint_lever_vacuous_export {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.sixPoint_lever_vacuous hzero

/-- **[capstone, DoorIVCorrelationHierarchy]** Connected-correlation closure through sixth order:
if a candidate is controlled by both the 2-2 and 3-3 moments, and the connected fourth and sixth
cumulants vanish, then both controls pass through the Wick values. No connected-correlation
functional through order six supplies a fresh door-(iv) bound. -/
theorem doorIV_correlation_hierarchy_no_lever_export
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0) :
    M ≤ wick4 ∧ M ≤ wick6 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_no_lever
    hctrl4 hctrl6 hdec4 hcum4 hdec6 hcum6

/-- **[capstone, DoorIVCorrelationHierarchy]** Full citable closure through sixth order, including
both Wick-factorization of the 4th/6th connected-correlation controls and the exact zero
of the signed six-point functional when `κ₃ = 0`. -/
theorem doorIV_correlation_hierarchy_closed_through_six_export
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ} {κ₃ : ℂ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0)
    (htriple : κ₃ = 0) :
    (M ≤ wick4 ∧ M ≤ wick6) ∧ Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_closed_through_six
    hctrl4 hctrl6 hdec4 hcum4 hdec6 hcum6 htriple

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** If the connected triple correlation `κ₃`
vanishes, the signed six-point functional `|κ₃|²` is exactly zero. This is the direct indexed form of
the 6-point connected-correlation wall. -/
theorem doorIV_tripleCorrelation_sixPoint_zero_export {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_functional_zero_of_triple_zero
    hzero

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** A six-point lever routed through the signed
triple-correlation functional is vacuous when `κ₃ = 0`: it only supplies `0 ≤ ‖M‖²`. -/
theorem doorIV_tripleCorrelation_sixPoint_vacuous_export {M κ₃ : ℂ}
    (hbound : Complex.normSq κ₃ ≤ Complex.normSq M) (hzero : κ₃ = 0) :
    (0 : ℝ) ≤ Complex.normSq M :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_lever_vacuous_of_triple_zero
    hbound hzero

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** With vanishing connected 3-3 cumulant, the
sixth-order 3-3 moment collapses to its Wick/lower-order value, so the candidate adds no new
six-point phase structure beyond already-mapped covariance/diagonal data. -/
theorem doorIV_tripleCorrelation_m33_eq_wick_export {m33 wick cumulant : ℝ}
    (hdecomp : m33 = wick + cumulant) (hzero : cumulant = 0) :
    m33 = wick :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.m33_eq_wick_of_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVCumulantLadder]** Order-uniform single-rung form: for any
moment-cumulant decomposition `mr = wickr + cumr`, a vanishing connected cumulant forces every
control through that rung to pass through the Wick value. -/
theorem doorIV_ladder_control_passes_through_wick_export
    {M mr wickr cumr : ℝ}
    (hctrl : M ≤ mr) (hdecomp : mr = wickr + cumr) (hzero : cumr = 0) :
    M ≤ wickr :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.ladder_control_passes_through_wick
    hctrl hdecomp hzero

/-- **[capstone, DoorIVCumulantLadder]** Whole finite ladder form: if every connected
cumulant in a finite set of orders vanishes and every moment decomposes as Wick plus cumulant,
then each moment is its Wick value. Climbing to higher connected-correlation rungs adds no new
structure without a nonzero connected cumulant. -/
theorem doorIV_whole_ladder_wick_export
    {R : Finset ℕ} {m wick cum : ℕ → ℝ}
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, m r = wick r :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_wick hdec hladder

/-- **[capstone, DoorIVCumulantLadder]** Whole finite ladder control form: if a candidate is
bounded at every rung of a finite cumulant ladder whose connected cumulants vanish, it is bounded
at every rung by the corresponding Wick value. This packages the higher-order correlation route
as a Wick-data route, not a fresh anti-concentration lever. -/
theorem doorIV_whole_ladder_control_export
    {R : Finset ℕ} {M : ℝ} {m wick cum : ℕ → ℝ}
    (hctrl : ∀ r ∈ R, M ≤ m r)
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, M ≤ wick r :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_control hctrl hdec hladder

/-- **[obstruction, DoorIVCrossHalfPhase]** In the probed real-collinear cross-half regime,
the period norm equals the half-mass exactly. The cross-half datum carries no angular saving:
coherence is saturated at `1`. -/
theorem doorIV_crossHalf_norm_add_eq_halfMass_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t : ℝ} (ht : 0 ≤ t)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.norm_add_eq_halfMass_of_real_collinear
    ht h

/-- **[obstruction, DoorIVCrossHalfPhase]** Any fixed multiplier bound through one half,
`‖A+B‖≤c‖A‖`, must already pay the full measured real ratio: `1+t≤c`. Thus a fixed-factor
recursive half route hides the hard frequency-dependent ratio in the constant. -/
theorem doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t)
    (hbound : ‖A + B‖ ≤ c * ‖A‖) :
    1 + t ≤ c :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_forces_ratio_le
    ht hA h hbound

/-- **[obstruction, DoorIVCrossHalfPhase]** Contrapositive form used by the probe verdict:
if the measured cross-half ratio exceeds the proposed fixed multiplier, the one-half factorization
bound fails at that frequency. -/
theorem doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t)
    (hgt : c < 1 + t) :
    ¬ ‖A + B‖ ≤ c * ‖A‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_fails_of_ratio_gt
    ht hA h hgt

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** A positive balance floor `r` forces any
single-half certificate at a coherent frequency to pay `(1+r)` times the heavier half.  This is the
formal version of the probed worst-b balance enrichment: keeping one dyadic half cannot manufacture a
shrinking anti-concentration gain. -/
theorem doorIV_halfMassBalance_single_half_pays_floor_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {g : ℝ → ℝ} {r : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hr : r ≤ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.balance A B)
    (hbound : ‖A + B‖ ≤ g (max ‖A‖ ‖B‖)) :
    (1 + r) * max ‖A‖ ‖B‖ ≤ g (max ‖A‖ ‖B‖) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.single_half_bound_pays_balance_floor
    hcoh hr hbound

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** At coherent perfect balance the normalized loss
from keeping only the heavier half is exactly `2`, the sharp endpoint of the drop-a-half obstruction. -/
theorem doorIV_halfMassBalance_descent_loss_eq_two_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hbal : ‖A‖ = ‖B‖)
    (hpos : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ / max ‖A‖ ‖B‖ = 2 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_eq_two_of_coherent_balanced
    hcoh hbal hpos

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** In any coherent two-half split, dropping to the
heavier half loses at most the constant factor `2`.  The balanced worst-b probes saturate this endpoint,
so this descent shape is constant-factor bookkeeping, not a square-root cancellation lever. -/
theorem doorIV_halfMassBalance_descent_loss_le_two_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hpos : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ ≤ 2 * max ‖A‖ ‖B‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_le_two hcoh hpos

/-- **[capstone, DoorIVHalfMassDilationForm]** The second coset half is exactly the same
sub-period evaluated at the dilated frequency: `eta(gH,b)=eta(H,g*b)`. -/
theorem doorIV_halfMass_eta_image_smul_eq_eta_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0) :
    _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H.image (fun y => g * y)) b =
      _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_image_smul_eq_eta_dilate H hg

/-- **[capstone, DoorIVHalfMassDilationForm]** On a disjoint index-two split, the full period is
the sum of one sub-period at `b` and the same sub-period at the dilated frequency `g*b`. -/
theorem doorIV_halfMass_eta_index_two_split_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b =
      _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b +
        _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_index_two_split_dilate
    H hg hdisj

/-- **[capstone, DoorIVHalfMassDilationForm]** The open half-mass burden is a bound on a single
sub-period magnitude at two multiplicatively dilated frequencies, `b` and `g*b`. -/
theorem doorIV_halfMass_norm_eta_le_two_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b‖ ≤
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.norm_eta_le_two_dilate H hg hdisj

/-- **[capstone, DoorIVHalfMassDilationForm]** The index-two half-mass itself is exactly the
sum of the same sub-period magnitude at the two dilated frequencies `b` and `g*b`.  This is the
non-inequality identity behind the two-dilate reformulation. -/
theorem doorIV_halfMass_eq_two_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
          (H.image (fun y => g * y)) b‖ =
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
          ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.halfMass_eq_two_dilate H hg

/-- **[capstone, DoorIVHalfMassDilationForm]** At a coherent two-dilate frequency the triangle
upper bound is exact: the full period norm equals the two-dilate half-mass.  This names the equality
case used by the worst-`b` coherence probes without asserting any CORE saving. -/
theorem doorIV_halfMass_norm_eta_eq_two_dilate_of_coherent_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y)))
    (hcoh : ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b +
        _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ =
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b‖ =
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.norm_eta_eq_two_dilate_of_coherent
    H hg hdisj hcoh

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The positive same-sign/doubling cross-mass
is exactly balanced by the negative opposite-sign/cancellation cross-mass. This is the indexed
mass-level constraint behind the real dilation sign-cocycle: the `+` branch is not a free budget. -/
theorem doorIV_sign_positiveMass_eq_negativeMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
        ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
          (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re)) :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sign_positiveMass_eq_negativeMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Nonzero positive same-sign mass rules out
a globally nonnegative sign cocycle. Any nontrivial doubling mass forces an opposite-sign/cancelling
contribution somewhere else; the remaining open problem is only the single worst-frequency word. -/
theorem doorIV_sign_not_all_nonneg_of_positiveMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hpos : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ¬ ∀ b : F, 0 ≤
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.not_all_nonneg_of_positiveMass_pos
    hψ G hG hdisj hpos

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Local witness form: nonzero positive
same-sign/doubling mass forces an actually negative opposite-sign frequency. The balance theorem is
therefore concrete spectral cancellation, not just an abstract equality of totals. -/
theorem doorIV_sign_exists_negative_cross_of_positiveMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hpos : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ∃ b : F,
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re < 0 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_negative_cross_of_positiveMass_pos
    hψ G hG hdisj hpos

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Symmetric local witness form: nonzero
opposite-sign/cancelling mass forces an actual same-sign frequency. The exact 50/50 sign-cocycle split
is therefore witnessed on both sides of the finite spectrum. -/
theorem doorIV_sign_exists_positive_cross_of_negativeMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hneg : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ∃ b : F, 0 <
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_positive_cross_of_negativeMass_pos
    hψ G hG hdisj hneg

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The same-sign/doubling branch occupies at most
half of the global Cauchy--Schwarz cross budget `q·|G|`. This is only a global mass constraint, not a
worst-frequency CORE bound. -/
theorem doorIV_sign_positiveMass_le_half_card_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_le_half_card
    hψ G hG hζ hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The opposite-sign/cancelling branch obeys the
same half-budget cap as the same-sign branch. Neither side of the real sign-cocycle can spend more
than half of the global cross budget. -/
theorem doorIV_sign_negativeMass_le_half_card_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_le_half_card
    hψ G hG hζ hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Direct norm-cross form: under the disjoint-dilate
sign-cocycle hypotheses, the same-sign branch is exactly one half of
`∑ b, ‖η_b‖ * ‖η_{ζb}‖`. -/
theorem doorIV_sign_positiveMass_eq_half_total_doublingMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      (∑ b : F, ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ *
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)‖) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_eq_half_total_doublingMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Direct norm-cross form for the cancelling branch:
it is also exactly one half of the total norm cross-mass. Any proof narrative that spends only the
same-sign side is therefore globally over-budget. -/
theorem doorIV_sign_negativeMass_eq_half_total_doublingMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      (∑ b : F, ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ *
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)‖) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_eq_half_total_doublingMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVAlgebraicFloorCyclotomicWall]** The concrete `μ₁₆` gapped minor
(rows `(1,2,5)`, powers `(1,5,9)`) vanishes under the dyadic relation `ζ^8=-1`. This is the
formal cyclotomic wall behind the algebraic-floor probe: generic nonzero-minor reasoning is not
valid on the actual dyadic subgroup without handling these relations. -/
theorem doorIV_gappedMinor125_159_eq_zero_export {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159 ζ = 0 :=
  _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159_eq_zero_of_pow8_eq_neg_one
    hζ

/-- **[obstruction, DoorIVAlgebraicFloorCyclotomicWall]** Contradiction form: any hypothesis that
this explicit dyadic gapped minor is nonzero is false. -/
theorem doorIV_not_gappedMinor125_159_ne_zero_export {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    ¬ _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159 ζ ≠ 0 :=
  _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.not_gappedMinor125_159_ne_zero_of_pow8_eq_neg_one
    hζ

/-- **[obstruction, DoorIVEighthCumulantSignUnstable]** Mixed signs in a candidate eighth-cumulant
statistic refute both universal fixed-sign certificates (`κ ≥ 0` and `κ ≤ 0`). This indexes the
formal constraint supplied by the multiprime door-IV probe; no cumulant bound is claimed. -/
theorem doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export
    {ι : Type*} {κ : ι → ℝ} {i j : ι} (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonnegative κ ∧
      ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonpositive κ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.mixed_sign_forbids_universal_fixed_sign
    hpos hneg

/-- **[obstruction, DoorIVEighthCumulantSignUnstable]** Disjunction/contradiction form: once the
same admissible statistic takes both positive and negative values, it cannot provide a universal
fixed-sign eighth-cumulant route. -/
theorem doorIV_eighthCumulant_no_fixedSignCertificate_export
    {ι : Type*} {κ : ι → ℝ} {i j : ι} (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ (_root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonnegative κ ∨
      _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonpositive κ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.no_fixedSignCertificate_of_mixed_sign
    hpos hneg

/-- **[capstone, DoorIVXGatedTelescopeBridge]** The corrected nonzero-frequency ratio hypothesis
`LevelRatioBoundNZ ψ G ζ μ r` is exactly a one-step tower inequality on the concrete worst-period
object: `M_{k+1} ≤ r·M_k` for every `k < μ`. This is the local rung of Shaw's door-(iv) descent;
it assumes the open ratio gate and makes no cancellation claim. -/
theorem doorIV_levelWorst_step_of_levelRatioBoundNZ_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {r : ℝ}
    (hr : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ ψ G ζ μ r)
    {k : ℕ} (hk : k < μ) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ (k + 1) ≤
      r * _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ k :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst_step_of_levelRatioBoundNZ
    hr hk

/-- **[capstone, DoorIVXGatedTelescopeBridge]** Telescoping the corrected `b ≠ 0` `√2` gate gives
exactly the prize square-root tower factor `(√2)^μ·M₀`. This records the clean equivalence target:
shaving every dyadic level from factor `2` to factor `√2` is precisely the geometric door-(iv)
obligation. The `LevelRatioBoundNZ ... √2` input is open. -/
theorem doorIV_levelWorst_le_sqrt2_pow_mul_of_levelRatioBoundNZ_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (μ : ℕ)
    (hr : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ ψ G ζ μ
      (Real.sqrt 2)) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤
      (Real.sqrt 2) ^ μ *
        _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst_le_sqrt2_pow_mul_of_xgate
    μ hr

#print axioms doorIV_levelWorst_step_of_levelRatioBoundNZ_export
#print axioms doorIV_levelWorst_le_sqrt2_pow_mul_of_levelRatioBoundNZ_export

/-- **[capstone, DoorIVXGatedPrizeReduction]** The named open `XGatedRatio` hypothesis, plus its
levelwise `x`-gate, telescopes to the explicit square-root tower factor `√(2^μ)·M₀`. This is the
end-to-end Lane-2 reduction of the corrected door-(iv) scalar to the geometric prize scale; the
`XGatedRatio` input itself remains open. -/
theorem doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {x₀ lnm : ℝ}
    (hx : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.XGatedRatio ψ G ζ μ x₀ lnm)
    (hgate : ∀ k : ℕ, k ≤ μ → x₀ * lnm ≤ ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k).card : ℝ)) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤
      Real.sqrt ((2 : ℝ) ^ μ) *
        _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedPrizeReduction.levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio
    hx hgate

/-- **[capstone, DoorIVXGatePrizeBudget]** The corrected `√2` per-level gate, a base bound
`M₀≤C√L`, and the dimension registration `(√2)^μ≤√n` compose to the exact prize-shaped budget
`M_μ≤C√(nL)`. This is pure reduction algebra: no proof of the open gate, no CORE claim. -/
theorem doorIV_levelWorst_le_prize_budget_of_xgate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget.levelWorst_le_prize_budget_of_xgate
    hr h_dim h_base hC hL hn

/-- **[obstruction, DoorIVXGatedBaseThreshold]** Split telescope with `k*` factor-2 base levels
and `√2` cancellation above the gate threshold. -/
theorem doorIV_gateThreshold_split_telescope_sqrt2_export (M : ℕ → ℝ) (hpos : ∀ k, 0 ≤ M k)
    (kstar r : ℕ)
    (hbase : ∀ k, k < kstar → M (k + 1) ≤ 2 * M k)
    (hcanc : ∀ j, j < r → M (kstar + j + 1) ≤ Real.sqrt 2 * M (kstar + j)) :
    M (kstar + r) ≤ 2 ^ kstar * (Real.sqrt 2) ^ r * M 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.split_telescope_sqrt2
    M hpos kstar r hbase hcanc

/-- **[obstruction, DoorIVXGatedBaseThreshold]** Any nonzero gate threshold `k* ≥ 1` costs a
strict excess factor over the clean `(√2)^(k*+r)` floor. -/
theorem doorIV_gateThreshold_strictly_above_clean_export {kstar : ℕ} (hk : 1 ≤ kstar) (r : ℕ) :
    (Real.sqrt 2) ^ (kstar + r) < (2 : ℝ) ^ kstar * (Real.sqrt 2) ^ r :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.gate_threshold_strictly_above_clean
    hk r

/-- **[obstruction, DoorIVXGatedBaseThresholdConcrete]** On the real `levelWorst` character sum,
the thin base step costs the unconditional trivial factor `2`. -/
theorem doorIV_levelWorst_base_step_two_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (k : ℕ)
    (hdisj : Disjoint
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k))) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ (k + 1) ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ k :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_step_two
    hζ k hdisj

/-- **[obstruction, DoorIVXGatedBaseThresholdConcrete]** Concrete base-corrected bound on the
real `levelWorst` object: `k*` base levels pay factor `2`, only the `r` levels above the gate get `√2`. -/
theorem doorIV_levelWorst_base_corrected_of_gate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (kstar r : ℕ)
    (hdisj : ∀ k, Disjoint
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)))
    (hgate : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ
      ψ G ζ (kstar + r) (Real.sqrt 2)) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ (kstar + r)
      ≤ 2 ^ kstar * (Real.sqrt 2) ^ r *
        _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_le_base_corrected_of_gate
    hζ kstar r hdisj hgate

/-! ## Door-IV direct-proof refutations from the Paley/direct-proof essay. Scope: **obstruction**.

These exports make the latest direct-proof no-go kernels permanent: Gross--Koblitz phase
bookkeeping, Markoff-surface coupling, and Tannakian non-torsion twists. All three are
constraint lemmas only. They refute claimed shortcuts but do not prove CORE. -/

/-- **[obstruction, GKPhaseCoboundary]** The additive Hasse--Davenport coboundary is exactly the
Jacobi phase: under the product relation among unit Gauss phases, `J` is the `√p`-radius phase at
`θ₁ + θ₂ - θ₁₂`. -/
theorem doorIV_gk_coboundary_phase_eq_export {p : ℝ} (hp : 0 < p) (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁ *
        ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₂ =
      J * ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁₂) :
    J = ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p (θ₁ + θ₂ - θ₁₂) :=
  ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.coboundary_phase_eq
    hp θ₁ θ₂ θ₁₂ hJ

/-- **[obstruction, GKPhaseCoboundary]** A non-positive-real Jacobi factor certifies a nontrivial
coboundary, hence forbids the linear/character-phase model needed for the free `√m` collapse. -/
theorem doorIV_gk_nontrivial_coboundary_not_linearizable_export {p : ℝ} (hp : 0 < p)
    (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁ *
        ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₂ =
      J * ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁₂)
    (hJne : J ≠ (Real.sqrt p : ℂ)) :
    Complex.exp ((θ₁ + θ₂ - θ₁₂) * Complex.I) ≠ 1 :=
  ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.nontrivial_coboundary_not_linearizable
    hp θ₁ θ₂ θ₁₂ hJ hJne

/-- **[obstruction, MarkoffCoupling]** A Markoff/twisted weighted period transfers to the real
Paley period only in the constant-weight case; then the weighted period factors as `K` times the
original period. -/
theorem doorIV_markoff_weighted_period_factors_export {ι : Type*} (G : Finset ι)
    (w f : ι → ℂ) (K : ℂ) (hw : ∀ x ∈ G, w x = K) :
    (∑ x ∈ G, w x * f x) = K * (∑ x ∈ G, f x) :=
  _root_.ProximityGap.Frontier.weighted_period_factors G w f K hw

/-- **[obstruction, MarkoffCoupling]** Nonconstant slice weights refute every single-constant
factorization through the Paley period on a two-slice witness. -/
theorem doorIV_markoff_transfer_refuted_export {ι : Type*} [DecidableEq ι] (w : ι → ℂ)
    (x₀ x₁ : ι) (hx : x₀ ≠ x₁) (hprobe : w x₀ ≠ w x₁) :
    ¬ ∃ K : ℂ, ∀ f : ι → ℂ,
        (∑ x ∈ ({x₀, x₁} : Finset ι), w x * f x)
          = K * (∑ x ∈ ({x₀, x₁} : Finset ι), f x) :=
  _root_.ProximityGap.Frontier.markoff_transfer_refuted w x₀ x₁ hx hprobe

/-- **[obstruction, TannakianTwist]** A diagonal multiplicative twist only multiplies a
cyclotomic minor determinant by the product of row weights. -/
theorem doorIV_tannakian_twist_det_eq_export {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (χ : n → R) (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = (∏ i, χ i) * A.det :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq χ A

/-- **[obstruction, TannakianTwist]** Unit-valued diagonal twists preserve determinant vanishing,
so they cannot turn a dyadic cyclotomic vanishing minor into a nonzero one. -/
theorem doorIV_tannakian_twist_det_zero_iff_export {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] [IsDomain R] {χ : n → R} (hχ : ∀ i, χ i ≠ 0)
    (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = 0 ↔ A.det = 0 :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq_zero_iff hχ A

/-- **[obstruction, TannakianTwist]** A character whose image orders divide `d` with
`gcd(d, |G|)=1` is trivial on the order-`|G|` subgroup. Thus a coprime non-torsion twist does
nothing on `μ_n`. -/
theorem doorIV_tannakian_coprime_order_trivial_export {G H : Type*} [Group G] [Group H]
    [Fintype G] (χ : G →* H) {d : ℕ} (hdiv : ∀ g : G, orderOf (χ g) ∣ d)
    (hcop : Nat.Coprime d (Fintype.card G)) :
    ∀ g : G, χ g = 1 :=
  ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_trivial_on_mu χ hdiv hcop

/-- **[obstruction, TannakianTwist]** If a twist is trivial on the support, the twisted period
`Σ χ(x)f(x)` is literally the original period `Σ f(x)`. -/
theorem doorIV_tannakian_twist_period_eq_original_export {ι A : Type*} [Semiring A]
    (G : Finset ι) (χ f : ι → A) (hχ : ∀ x ∈ G, χ x = 1) :
    (∑ x ∈ G, χ x * f x) = ∑ x ∈ G, f x :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_period_eq_original_of_trivial G χ f hχ

/-- **[obstruction, TannakianTwist]** A coprime-order multiplicative twist has no period-level
effect: after embedding its values into any semiring with `1 ↦ 1`, the twisted period equals the
untwisted period. -/
theorem doorIV_tannakian_coprime_twisted_period_eq_original_export {G H A : Type*}
    [Group G] [Group H] [Fintype G] [Semiring A] (χ : G →* H) {d : ℕ}
    (hdiv : ∀ g : G, orderOf (χ g) ∣ d) (hcop : Nat.Coprime d (Fintype.card G))
    (embed : H → A) (hembed_one : embed 1 = 1) (f : G → A) :
    (∑ x : G, embed (χ x) * f x) = ∑ x : G, f x :=
  ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_twisted_period_eq_original
    χ hdiv hcop embed hembed_one f

#print axioms doorIV_gk_coboundary_phase_eq_export
#print axioms doorIV_gk_nontrivial_coboundary_not_linearizable_export
#print axioms doorIV_markoff_weighted_period_factors_export
#print axioms doorIV_markoff_transfer_refuted_export
#print axioms doorIV_tannakian_twist_det_eq_export
#print axioms doorIV_tannakian_twist_det_zero_iff_export
#print axioms doorIV_tannakian_coprime_order_trivial_export

/-- **[descent, ZDegreeEnvelope]** The even/odd descent quadform
`R = Pp^2 - X·Qp^2` has degree at most the larger of the two branch support budgets
`2 deg Pp` and `1 + 2 deg Qp`. -/
theorem doorIV_descent_quadform_degreeEnvelope_export {F : Type*} [Field F]
    (Pp Qp : Polynomial F) :
    (_root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp).natDegree ≤
      max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform_natDegree_le_max Pp Qp

/-- **[descent, ZDegreeEnvelope]** Consumer form: the non-symmetric descent `Z` count is
bounded by `max (2 deg Pp) (1 + 2 deg Qp)`, the explicit support envelope. -/
theorem doorIV_descent_Z_card_le_degreeEnvelope_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degreeEnvelope hR B

/-- **[descent, ZDegreeEnvelope]** Indicator-sum form matching the descent identity's
`Z` term. -/
theorem doorIV_descent_Z_indicator_sum_le_degreeEnvelope_export {F : Type*} [Field F]
    [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degreeEnvelope hR B

/-- **[descent, ZLagrangeBound]** Exponent-controlled form from the G1→G2 bridge:
`Z ≤ 1 + 2 * max (deg Pp) (deg Qp)`. -/
theorem doorIV_descent_Z_card_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degBound hR B

/-- **[descent, ZLagrangeBound]** Indicator-sum exponent-controlled form matching the
summed `A + Z` notation: the `Z` indicator sum obeys the same G1→G2 exponent budget. -/
theorem doorIV_descent_Z_indicator_sum_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degBound hR B

/-- **[descent, even-spine]** Global symmetric backbone: summing the even fibre identity over the
base gives exactly twice the lower-level agreement count. -/
theorem doorIV_descentAgreement_even_eq_two_mul_export {F : Type*} [Field F] [DecidableEq F]
    (B : Finset F) (ρ Pf : F → F)
    (hρ0 : ∀ y ∈ B, ρ y ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∑ y ∈ B, (({ρ y, -ρ y} : Finset F).filter (fun x => Pf y + x * 0 = 0)).card)
      = 2 * (B.filter (fun y => Pf y = 0)).card :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentAgreement_even_eq_two_mul B ρ Pf hρ0 h2

/-- **[descent, weight-2 even-even spine]** Exact shifted binomial fiber count for the
symmetric weight-2 spine: the count is `gcd(#G,c)` when the target is a `c`-th power and `0`
otherwise. -/
theorem doorIV_weight2_evenSpine_card_eq_if_mem_range_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card
      = if w ∈ (_root_.powMonoidHom c : G →* G).range then (Nat.card G).gcd c else 0 :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_if_mem_range c w

/-- **[descent, weight-2 even-even spine]** Reachable-target consumer form: when the target is a
`c`-th power, the symmetric spine count is exactly the kernel size `gcd(#G,c)`. -/
theorem doorIV_weight2_evenSpine_card_eq_gcd_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G)
    (hw : w ∈ (_root_.powMonoidHom c : G →* G).range) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card = (Nat.card G).gcd c :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_gcd_of_mem_range c w hw

/-- **[descent, weight-2 even-even spine]** Off-range consumer form: if the target is not a
`c`-th power, the symmetric spine count is exactly zero. -/
theorem doorIV_weight2_evenSpine_card_eq_zero_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G)
    (hw : w ∉ (_root_.powMonoidHom c : G →* G).range) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card = 0 :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_zero_of_not_mem_range c w hw

/-- **[descent, weight-2 mixed quadform]** Exact mixed-parity binomial root count: over a finite
cyclic group, the non-symmetric weight-2 quadform count `#{y : y^a = y^b}` is exactly
`gcd(#G, a-b)` when `b ≤ a`. This is the citable Door-IV/G2 replacement for the false
"subgroup-root O(1)" hope: the count is controlled by the actual cyclotomic gcd. -/
theorem doorIV_weight2_mixedQuadform_card_eq_gcd_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (a b : ℕ) (hba : b ≤ a) :
    (Finset.univ.filter (fun y : G => y ^ a = y ^ b)).card = (Nat.card G).gcd (a - b) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_binomial_roots_eq_gcd a b hba

/-- **[descent, weight-2 mixed quadform]** Mixed-parity specialization over a two-power cyclic
group: if the exponent gap is odd and `#G = 2^k`, the non-symmetric weight-2 correction is exactly
one. This pins the measured `S₁ ≤ 1` mechanism as parity/cyclotomic gcd, not cancellation. -/
theorem doorIV_weight2_mixedQuadform_card_eq_one_of_odd_gap_twoPow_export {G : Type*}
    [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (a b : ℕ) (hba : b ≤ a) (hodd : Odd (a - b)) {k : ℕ} (hN : Nat.card G = 2 ^ k) :
    (Finset.univ.filter (fun y : G => y ^ a = y ^ b)).card = 1 :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_binomial_roots_eq_one_of_odd_gap_of_twoPow
    a b hba hodd hN

#print axioms doorIV_descent_quadform_degreeEnvelope_export
#print axioms doorIV_descent_Z_card_le_degreeEnvelope_export
#print axioms doorIV_descent_Z_indicator_sum_le_degreeEnvelope_export
#print axioms doorIV_descent_Z_card_le_degBound_export
#print axioms doorIV_descent_Z_indicator_sum_le_degBound_export
#print axioms doorIV_descentAgreement_even_eq_two_mul_export
#print axioms doorIV_weight2_evenSpine_card_eq_if_mem_range_export
#print axioms doorIV_weight2_evenSpine_card_eq_gcd_export
#print axioms doorIV_weight2_evenSpine_card_eq_zero_export
#print axioms doorIV_weight2_mixedQuadform_card_eq_gcd_export
#print axioms doorIV_weight2_mixedQuadform_card_eq_one_of_odd_gap_twoPow_export

/-- **[obstruction, WorstBHalfMass]** At two-piece coherence one with positive denominator, the
period magnitude equals the half-mass exactly. Thus the cross-half coherence factor contributes no
saving. -/
theorem doorIV_worstB_norm_add_eq_halfMass_of_coherence_one_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖)
    (hρ : _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B = 1) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.norm_add_eq_halfMass_of_coherence_one
    hden hρ

/-- **[obstruction, WorstBHalfMass]** A strict magnitude saving below half-mass requires the two
canonical halves to be non-`SameRay`; same-ray worst-b halves rule out this coherence-saving lever. -/
theorem doorIV_worstB_not_sameRay_of_magnitude_lt_halfMass_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hlt : ‖A + B‖ < ‖A‖ + ‖B‖) :
    ¬ _root_.SameRay ℝ A B :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.not_sameRay_of_magnitude_lt_halfMass hlt

/-- **[obstruction, WorstBHalfMass]** Positive-half-mass capstone: saturated two-piece coherence
`ρ=1` is equivalent to equality of period magnitude and half-mass. -/
theorem doorIV_worstB_coherence_one_iff_magnitude_eq_halfMass_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B = 1 ↔
      ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.coherence_one_iff_magnitude_eq_halfMass
    hden

/-- **[obstruction, WorstBHalfMass]** Positive-half-mass epsilon budget: a coherence saving
`ρ ≤ 1 - ε` is exactly an `ε·H` lower bound on the strict-triangle deficit. -/
theorem doorIV_worstB_eps_halfMass_deficit_iff_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖) (ε : ℝ) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B ≤ 1 - ε ↔
      ε * (‖A‖ + ‖B‖) ≤ (‖A‖ + ‖B‖) - ‖A + B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.coherence_le_one_sub_eps_iff_eps_halfMass_le_deficit
    hden ε

/-- **[obstruction, CoherenceSaturationInsufficient]** Under coherence saturation (`M = H`), the
prize-shaped bound is exactly a half-mass bound: `M ≤ C·prizeScale n L ↔ H ≤ C·prizeScale n L`. The
entire prize task transfers onto bounding the half-mass; the index-2 coherence object contributes
nothing. (Probe `probe_dooriv_worstb_coherence_deficit_law.py`: `ρ(b*) ≡ 1`.) -/
theorem doorIV_coherenceSaturation_prizeBound_iff_halfMassBound_export {M H C n L : ℝ}
    (hsat : M = H) :
    M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
      H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeBound_iff_halfMassBound_of_saturation
    hsat

/-- **[obstruction, CoherenceSaturationInsufficient]** In the thin prize regime
(`prizeScale n L < n`, i.e. `√(n·L) < n ⟺ L < n`) any prize constant `0 < C ≤ 1` makes the prize
target strictly below the trivial half-mass ceiling `n`. So coherence saturation supplies none of the
prize gap; the whole burden is a strict-sub-trivial bound on the half-mass (the self-similar
descent). -/
theorem doorIV_coherenceSaturation_prizeTarget_lt_trivial_ceiling_export {C n L : ℝ}
    (hscale : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n)
    (hC0 : 0 < C) (hC1 : C ≤ 1) :
    C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeTarget_lt_trivial_ceiling
    hscale hC0 hC1

/-- **[obstruction, CoherenceSaturationInsufficient]** Under coherence saturation, any measured
half-mass excess over the prize target immediately refutes the corresponding prize bound for `M`.
This is the contrapositive probe-facing form: once `ρ(b*) = 1`, cross-half coherence cannot rescue an
over-budget half-mass. -/
theorem doorIV_coherenceSaturation_halfMass_excess_refutes_prize_export {M H C n L : ℝ}
    (hsat : M = H)
    (hH : C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < H) :
    ¬ M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L := by
  intro hM
  have hHle : H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
    (_root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeBound_iff_halfMassBound_of_saturation
      hsat).mp hM
  exact not_le_of_gt hH hHle

/-- **[obstruction, CoherenceSaturationInsufficient]** Coherence-insufficiency transfer capstone:
at coherence saturation (`M = H`) with the trivial ceiling (`H ≤ n`) in the thin prize regime
(`prizeScale n L < n`), for any prize constant `0 < C ≤ 1` the prize-shaped bound is exactly a
strict-sub-trivial half-mass bound. The kerneled form of the probe verdict
`ρ(b*) ≡ 1 ≫ ρ_needed = √(n·L)/n` ⟹ COHERENCE-INSUFFICIENT: the prize burden lives entirely on the
half-mass descent, not the index-2 coherence object. -/
theorem doorIV_coherenceSaturation_transfers_to_strict_subTrivial_halfMass_export
    {M H C n L : ℝ}
    (hsat : M = H) (hceil : H ≤ n)
    (hscale : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n)
    (hC0 : 0 < C) (hC1 : C ≤ 1) :
    (M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
        H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L) ∧
      C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.coherenceSaturation_transfers_to_strict_subTrivial_halfMass
    hsat hceil hscale hC0 hC1

#print axioms doorIV_worstB_norm_add_eq_halfMass_of_coherence_one_export
#print axioms doorIV_worstB_not_sameRay_of_magnitude_lt_halfMass_export
#print axioms doorIV_worstB_coherence_one_iff_magnitude_eq_halfMass_export
#print axioms doorIV_worstB_eps_halfMass_deficit_iff_export
#print axioms doorIV_coherenceSaturation_prizeBound_iff_halfMassBound_export
#print axioms doorIV_coherenceSaturation_prizeTarget_lt_trivial_ceiling_export
#print axioms doorIV_coherenceSaturation_halfMass_excess_refutes_prize_export
#print axioms doorIV_coherenceSaturation_transfers_to_strict_subTrivial_halfMass_export

/-- **[obstruction, FractionalMomentNoMaxGain]** The moment-to-max envelope multiplier `c^{1/r}`
(`c = card s`) is ANTITONE in moment depth `r`: a deeper moment gives a tighter overshoot. This is
the direction in Shaw's probe `(N·A_q)^{1/(2q)}` decreasing in `q`. -/
theorem doorIV_envelope_multiplier_antitone_export {c : ℝ} (hc : 1 ≤ c)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    c ^ ((1 : ℝ) / r₂) ≤ c ^ ((1 : ℝ) / r₁) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.envelope_multiplier_antitone
    hc hr₁ hr₁₂

/-- **[obstruction, FractionalMomentNoMaxGain]** No max-gain from a smaller moment: for nonempty `s`
and `0 ≤ M`, the high-moment max-envelope `(card s)^{1/r₂}·M` is `≤` the low-moment one
`(card s)^{1/r₁}·M`. Dropping to the fractional / Harper `q<1` regime cannot tighten the worst-case
max bound — the average-vs-max obstruction in kerneled form. -/
theorem doorIV_no_maxGain_from_smaller_moment_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {M : ℝ} (hM : 0 ≤ M) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    (s.card : ℝ) ^ ((1 : ℝ) / r₂) * M ≤ (s.card : ℝ) ^ ((1 : ℝ) / r₁) * M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.no_maxGain_from_smaller_moment
    s hs hM hr₁ hr₁₂

#print axioms doorIV_envelope_multiplier_antitone_export
#print axioms doorIV_no_maxGain_from_smaller_moment_export

/-- **[obstruction, GeomMeanBelowMax]** The arithmetic mean / density average lies at or below the
max. This kernels the murmuration-density half of the average-not-max obstruction: an additive
average can witness typical behavior, but it does not control the adversarial worst frequency. -/
theorem doorIV_arithMean_le_max_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    (∑ i ∈ s, lam i) / (s.card : ℝ) ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.arithMean_le_max s hs lam hM

/-- **[obstruction, GeomMeanBelowMax]** Uniform arithmetic/density averages above a threshold
expose an entry above that threshold. Density excess is a lower witness for the max, not an upper
control of the adversarial worst frequency. -/
theorem doorIV_arithMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) {C : ℝ} (hgt : C < (∑ i ∈ s, lam i) / (s.card : ℝ)) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_arithMean
    s hs lam hgt

/-- **[obstruction, GeomMeanBelowMax]** Probability-weighted density averages also lie below the
max. This strengthens the murmuration-density obstruction from uniform averages to arbitrary finite
probability weights: changing the averaging measure does not control the adversarial worst frequency. -/
theorem doorIV_weightedMean_le_max_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedMean_le_max
    s w lam hw_nonneg hw_sum hM

/-- **[obstruction, GeomMeanBelowMax]** Subprobability-weighted density averages still lie below the
max when `0 ≤ M`. Truncating or thinning the averaging window cannot turn an average-side statistic
into a worst-case max bound. -/
theorem doorIV_weightedSubmean_le_max_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {M : ℝ} (hM_nonneg : 0 ≤ M) (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedSubmean_le_max
    s w lam hw_nonneg hw_sum hM_nonneg hM

/-- **[obstruction, GeomMeanBelowMax]** Probability-weighted averages that beat a threshold expose
an entry above the same threshold. Average-side murmuration/density evidence is a lower witness for
`max`, not an upper-control mechanism for the adversarial frequency. -/
theorem doorIV_weightedMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {C : ℝ} (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedMean
    s w lam hw_nonneg hw_sum hgt

/-- **[obstruction, GeomMeanBelowMax]** Subprobability-weighted averages above a nonnegative
threshold still expose an entry above that threshold. Truncation does not create hidden worst-case
upper control. -/
theorem doorIV_weightedSubmean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedSubmean
    s w lam hw_nonneg hw_sum hC_nonneg hgt

/-- **[obstruction, GeomMeanBelowMax]** The geometric mean (Mahler-measure / log-average) of the
nonnegative spectrum lies at or below the max: `(∏_{i∈s} lam i)^{1/card s} ≤ M` for `lam i ≤ M` on a
nonempty `s`. Kernels the (b)/(d) literature-cluster verdict (murmuration density / Mahler measure are
AVERAGE objects, the wrong side of the worst-case max). -/
theorem doorIV_geomMean_le_max_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card) ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.geomMean_le_max s hs lam hnn hM

/-- **[obstruction, GeomMeanBelowMax]** A Mahler/geometric-mean excess above a threshold exposes
an entry above that threshold. The log-average object is a lower witness for the worst conjugate,
not an upper-control mechanism for the adversarial max. -/
theorem doorIV_geomMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) (hnn : ∀ i ∈ s, 0 ≤ lam i) {C : ℝ}
    (hgt : C < (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card)) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_geomMean
    s hs lam hnn hgt

/-- **[obstruction, DoorIVOrderedWalkMajorant]** DIR9 ordered-walk scaffold: the endpoint
norm is bounded by the finite maximal prefix excursion. This makes the ordered Doob/van-der-Corput
object a genuine majorant of the Gauss-period endpoint while making no cancellation claim. -/
theorem doorIV_orderedWalk_endpoint_le_maximalExcursion_export
    {E : Type*} [SeminormedAddCommGroup E] (S : ℕ → E) (n : ℕ) :
    ‖S n‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion S n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_norm_le_maximalExcursion
    S n

/-- **[obstruction, DoorIVOrderedWalkMajorant]** Consumer form for DIR9: any uniform bound on the
ordered maximal prefix excursion immediately bounds the Gauss-period endpoint. The whole analytic
content remains proving the maximal-excursion bound. -/
theorem doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export
    {E : Type*} [SeminormedAddCommGroup E] {S : ℕ → E} {n : ℕ} {C : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion S n ≤ C) :
    ‖S n‖ ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_bound_of_maximalExcursion_bound h

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** In the ordered-walk formulation, the endpoint
period is one of the prefixes, so its norm is dominated by the maximal excursion `R`. -/
theorem doorIV_avDIR9_endpoint_le_R_export {n : ℕ} (a : Fin n → ℂ) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9.endpoint a‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9.R a :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.endpoint_le_R a

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** Per-pair summed cancellation of the ordered
signed-area contributions forces the whole signed-area family sum to vanish. This is a global
phase-blind statement only, not per-worst-frequency cancellation. -/
theorem doorIV_avDIR9_pairAntisym_sum_zero_export {n : ℕ} {B : Type*} [Fintype B]
    (c : B → Fin n → Fin n → ℝ) (hpair : ∀ k l, ∑ b, c b k l = 0) :
    ∑ b, ((1 / 2 : ℝ) *
      ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)), c b k l) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.pairAntisym_sum_zero c hpair

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** The abstract DIR9 reduction theorem is exactly
`endpoint≤R`: the unconditional handle is the majorant direction, not a new upper bound. -/
theorem doorIV_avDIR9_majorant_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9.DIR9MajorantReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.dir9_majorant_reduces

/-- **[obstruction, JacAutocorrL2SupGap]** Complex Wiener-Khinchin identity for the cyclic
Jacobi/Gauss-sum autocorrelation: the autocorrelation L2 mass equals the convolution L2 mass. -/
theorem doorIV_jacAutocorr_wienerKhinchin_export {m : ℕ} [NeZero m]
    (g : ZMod m → ℂ) :
    ∑ s : ZMod m,
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2 =
      ∑ d : ZMod m,
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicConv g d‖ ^ 2 :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.sum_normSq_autocorr_eq_sum_normSq_conv g

/-- **[obstruction, JacAutocorrL2SupGap]** The exact L2-to-sup control for one off-diagonal
Jacobi autocorrelation term is the whole off-diagonal L2 mass, i.e. the route loses the square-root
number of shifts unless a new flatness theorem is supplied. -/
theorem doorIV_jacAutocorr_offdiag_le_total_sub_diag_export {m : ℕ} [NeZero m]
    (g : ZMod m → ℂ) {s : ZMod m} (hs : s ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2
      ≤ (∑ d : ZMod m,
          ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicConv g d‖ ^ 2) -
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g 0‖ ^ 2 :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_total_sub_diag g hs

/-- **[prize-bridge, JacAutocorrL2SupGap]** The named autocorrelation flatness residual removes the
L2-to-sup square-root loss and yields the per-shift prize-shape bound. The residual itself is the open
Door-IV wall, not asserted here. -/
theorem doorIV_jacAutocorr_gap_suffices_export {m : ℕ} [NeZero m] {C : ℝ}
    (g : ZMod m → ℂ) (hm : 2 ≤ m)
    (hgap : _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.AutocorrL2SupGap C g)
    {s : ZMod m} (hs : s ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2
      ≤ (C * Real.log m / ((m : ℝ) - 1))
          * (∑ t ∈ (Finset.univ.erase (0 : ZMod m)),
              ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g t‖ ^ 2) :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_of_gap g hm hgap hs

/-- **[obstruction, AvERG]** Periodic ergodic sums have exact drift by the endpoint period:
there is no new infinite-time cancellation regime beyond the single Door-IV window. -/
theorem doorIV_avERG_drift_export (a : ℕ → ℂ) (n : ℕ)
    (hper : ∀ j, a (j + n) = a j) (k : ℕ) :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodicSum a (n + k) =
      _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodicSum a k +
        _root_.ArkLib.ProximityGap.Frontier.AvERG.periodSum a n :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.drift a n hper k

/-- **[obstruction, AvERG]** At the prize relation `p = n^4`, the deterministic
Rademacher-Menshov maximal scale exceeds the prize scale for `n ≥ 55`; the route loses a real
`sqrt(log n)` factor. -/
theorem doorIV_avERG_rmScale_gt_prizeScale_export (n : ℕ) (hn : 55 ≤ n) :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.prizeScale n <
      _root_.ArkLib.ProximityGap.Frontier.AvERG.rmScale n :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.rmScale_gt_prizeScale n hn

/-- **[obstruction, AvERG]** The ergodic/dynamical maximal-function angle reduces to the wall:
zero-entropy drift plus Rademacher-Menshov scale loss are the exact unconditional certificate. -/
theorem doorIV_avERG_ergodic_maximal_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.ErgodicMaximalReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodic_maximal_reduces

/-- **[obstruction, PhaseBlindRadialStats]** Every finite `normSq`-radial statistic is invariant
under arbitrary pointwise unit twists. This is the kerneled radial side of Shaw's phase-blindness
probe: a `b`-summed moment/radial summary cannot see the adversarial phase alignment Door (iv) needs. -/
theorem doorIV_radialSum_invariant_under_unit_twist_export {ι : Type*} (s : Finset ι)
    (F : ℝ → ℝ) (tw A : ι → ℂ) (htw : ∀ i ∈ s, Complex.normSq (tw i) = 1) :
    (∑ i ∈ s, F (Complex.normSq (tw i * A i))) =
      ∑ i ∈ s, F (Complex.normSq (A i)) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.radialSum_invariant_under_unit_twist
    s F tw A htw

/-- **[capstone, OrderedWalkDoobMajorant]** DIR9 ordered-walk consumer: if the ordered maximal
excursion radius `R` dominates the endpoint period at every family member, then a prize-scale theorem
for `R` transfers verbatim to the endpoint periods. The remaining open obligation is the genuine
per-`b*` maximal-inequality bound for `R`, not another normalization step. -/
theorem doorIV_orderedWalk_corePrize_endpoint_of_majorant_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.EndpointDominated endpoint R)
    (hR : _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n R) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖endpoint i‖) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_orderedWalkMajorant
    hdom hR

/-- **[obstruction, OrderedWalkDoobMajorant]** Contrapositive DIR9 form: if the endpoint periods are
not prize-bounded, then no pointwise-dominating ordered-walk radius can be prize-bounded either. Thus
an ordered-walk/Doob route must prove a bound as strong as the original Paley/BGK wall. -/
theorem doorIV_orderedWalk_not_radius_bound_of_endpoint_not_bound_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.EndpointDominated endpoint R)
    (hnot : ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖endpoint i‖)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n R :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_radius_of_endpoint_not_core
    hdom hnot

/-- **[capstone, OrderedWalkDoobMajorant]** Concrete finite-prefix DIR9 consumer: a prize-scale
bound for the ordered maximal excursion `max_{k≤N_i} ‖S_i k‖` transfers to the endpoint periods
`‖S_i N_i‖`. This composes the finite prefix-max scaffold with the Shaw prize predicate. -/
theorem doorIV_orderedWalk_corePrize_endpoint_of_maximalExcursion_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hR : _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i))) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖S i (N i)‖) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_maximalExcursion_bound
    hR

/-- **[obstruction, OrderedWalkDoobMajorant]** Concrete contrapositive: if the endpoint
periods are not prize-bounded, then the finite ordered maximal-prefix excursion cannot be
prize-bounded either. -/
theorem doorIV_orderedWalk_not_maximalExcursion_bound_of_endpoint_not_bound_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hnot : ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖S i (N i)‖)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i)) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_maximalExcursion_of_endpoint_not_core
    hnot

/-- **[obstruction, StepanovAtBstar]** Per-`b*` Stepanov supplies only the counting
inequality: if a nonzero auxiliary vanishes to order `M` on the major-arc set `B`, then
`M * |B| ≤ deg F`. -/
theorem doorIV_stepanov_bstar_bound_export {F : Type*} [Field F]
    {B : Finset F} {F' : Polynomial F} {M : ℕ}
    (hF : F' ≠ 0) (hvanish : ∀ x ∈ B, (Polynomial.X - Polynomial.C x) ^ M ∣ F') :
    M * B.card ≤ F'.natDegree :=
  _root_.ProximityGap.Frontier.StepanovAtBstar.stepanov_bstar_bound hF hvanish

/-- **[obstruction, StepanovAtBstar]** A strictly sub-count per-`b*` Stepanov saving is
exactly the named `MajorArcDegenerate` obligation. The natural structured/even auxiliaries have
house=count, so closing this lane requires genuine major-arc algebraic degeneracy beyond the
measured full-rank wall. -/
theorem doorIV_bstar_saving_iff_degenerate_export {F : Type*} [Field F]
    {B : Finset F} {M : ℕ} :
    _root_.ProximityGap.Frontier.StepanovAtBstar.MajorArcDegenerate B M ↔
      ∃ F' : Polynomial F, F' ≠ 0 ∧
        (∀ x ∈ B, (Polynomial.X - Polynomial.C x) ^ M ∣ F') ∧
        F'.natDegree < M * B.card :=
  _root_.ProximityGap.Frontier.StepanovAtBstar.bstar_saving_iff_degenerate

/-- **[obstruction, AvDIR9Reflection]** Endpoint domination for the reflection-Steinitz
ordered walk: for every ordering, the endpoint Gauss period is one of the finite prefixes, so
`‖η_b‖ ≤ R`. This is the wall-facing direction: any bound on the ordered maximal function must
already bound the endpoint period itself. -/
theorem doorIV_avDIR9Reflection_endpoint_le_R_export (a : ℕ → ℂ) (n : ℕ) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a n‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R a n :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_le_R a n

/-- **[obstruction, AvDIR9Reflection]** Endpoint specialization of the antipodal reflection
identity: the full endpoint is `S_h + conj(S_h)`, so the reflection lane exposes the half-period
partial Gauss sum rather than eliminating it. -/
theorem doorIV_avDIR9Reflection_endpoint_id_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h) =
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h +
        (starRingEnd ℂ) (_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h) :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_reflection_id hanti

/-- **[obstruction, AvDIR9Reflection]** Endpoint-only reflection bound `‖η_b‖ ≤ 2·R₁`.
This is a wall certificate, not a prize upper bound, because `R₁` contains the half-period partial
Gauss sum. -/
theorem doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h)‖ ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R1 a h :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_norm_le_two_R1 hanti

/-- **[obstruction, AvDIR9Reflection]** Half-period lower wall: the reflected half-walk must
already carry at least half the endpoint norm. -/
theorem doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h)‖ / 2 ≤
      ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h‖ :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.half_norm_ge_endpoint_half hanti

/-- **[obstruction, AvDIR9Reflection]** Exact antipodal reflection gives the full-walk maximal
function bound `R(2h) ≤ 2 R₁(h)`. Iterating this bound loses cancellation and recurses into the
half-scale Gauss-sum wall, so it is a reduction certificate rather than a prize upper bound. -/
theorem doorIV_avDIR9Reflection_bound_two_R1_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R a (2 * h) ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R1 a h :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.reflection_bound_two_R1 hanti

/-- **[obstruction, AvDIR9Reflection]** The reflection-Steinitz attack reduces to the same
endpoint wall: the permanent certificate is precisely `endpoint_le_R`, with the reflection majorant
pointing in the wrong direction for an unconditional `M` upper bound. -/
theorem doorIV_avDIR9Reflection_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.DIR9ReflectionReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.dir9_reflection_reduces

/-- **[capstone, ShawValueBracketCenter]** The product of the normalized floor endpoint
`√n/√(nL)` and ceiling endpoint `n/√(nL)` is the closed-form midpoint datum `√n/L`. -/
theorem shawValue_bracket_endpoint_product_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L *
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L =
      Real.sqrt n / L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.endpoint_product hn hL

/-- **[capstone, ShawValueBracketCenter]** The geometric center of the Shaw-value prize bracket has
the closed form `sqrt (sqrt n) / sqrt L`, i.e. `n^(1/4)/sqrt L`. -/
theorem shawValue_bracket_geomCenter_eq_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L =
      Real.sqrt (Real.sqrt n) / Real.sqrt L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter_eq hn hL

/-- **[capstone, ShawValueBracketCenter]** The geometric center is the multiplicative midpoint of
the Shaw-value floor/ceiling bracket: `ceiling / center = center / floor`. -/
theorem shawValue_bracket_ratio_symmetric_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L /
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L =
      _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L /
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ratio_symmetric hn hL

/-- **[capstone, ShawValueBracketCenter]** For `1 ≤ n`, the geometric center is an honest point
inside the normalized Shaw-value prize bracket. -/
theorem shawValue_bracket_center_between_export {n L : ℝ} (hn : 1 ≤ n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L ∧
      _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.center_between hn hL

#print axioms shawValue_bracket_endpoint_product_export
#print axioms shawValue_bracket_geomCenter_eq_export
#print axioms shawValue_bracket_ratio_symmetric_export
#print axioms shawValue_bracket_center_between_export
#print axioms doorIV_arithMean_le_max_export
#print axioms doorIV_arithMean_gt_forces_point_gt_export
#print axioms doorIV_weightedMean_le_max_export
#print axioms doorIV_weightedSubmean_le_max_export
#print axioms doorIV_weightedMean_gt_forces_point_gt_export
#print axioms doorIV_weightedSubmean_gt_forces_point_gt_export
#print axioms doorIV_geomMean_le_max_export
#print axioms doorIV_geomMean_gt_forces_point_gt_export
#print axioms doorIV_orderedWalk_endpoint_le_maximalExcursion_export
#print axioms doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export
#print axioms doorIV_avDIR9_endpoint_le_R_export
#print axioms doorIV_avDIR9_pairAntisym_sum_zero_export
#print axioms doorIV_avDIR9_majorant_reduces_export
#print axioms doorIV_avDIR9Reflection_endpoint_le_R_export
#print axioms doorIV_avDIR9Reflection_endpoint_id_export
#print axioms doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export
#print axioms doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export
#print axioms doorIV_avDIR9Reflection_bound_two_R1_export
#print axioms doorIV_avDIR9Reflection_reduces_export
#print axioms doorIV_jacAutocorr_wienerKhinchin_export
#print axioms doorIV_jacAutocorr_offdiag_le_total_sub_diag_export
#print axioms doorIV_jacAutocorr_gap_suffices_export
#print axioms doorIV_avERG_drift_export
#print axioms doorIV_avERG_rmScale_gt_prizeScale_export
#print axioms doorIV_avERG_ergodic_maximal_reduces_export
#print axioms doorIV_radialSum_invariant_under_unit_twist_export
#print axioms doorIV_orderedWalk_corePrize_endpoint_of_majorant_export
#print axioms doorIV_orderedWalk_not_radius_bound_of_endpoint_not_bound_export
#print axioms doorIV_orderedWalk_corePrize_endpoint_of_maximalExcursion_export
#print axioms doorIV_orderedWalk_not_maximalExcursion_bound_of_endpoint_not_bound_export
#print axioms doorIV_stepanov_bstar_bound_export
#print axioms doorIV_bstar_saving_iff_degenerate_export
#print axioms doorIV_tannakian_twist_period_eq_original_export
#print axioms doorIV_tannakian_coprime_twisted_period_eq_original_export
#print axioms shawOOne_bddAbove_range_shawValue_export
#print axioms corePrize_bddAbove_range_shawValue_export
#print axioms corePrize_bddAbove_range_shawValue_of_pos_lt_export
#print axioms shawOOne_unbounded_shawValue_drift_export
#print axioms corePrize_unbounded_shawValue_drift_export
#print axioms corePrize_unbounded_shawValue_drift_of_pos_lt_export
#print axioms doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export
#print axioms doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export
#print axioms doorIV_floorPrizeConstant_ge_one_export
#print axioms doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export
#print axioms doorIV_no_prize_iff_no_shawBound_nonneg_and_floorPrizeRatio_export
#print axioms doorIV_decomposition_block_sum_common_ray_export
#print axioms doorIV_decomposition_partition_invariant_coherence_export
#print axioms doorIV_decomposition_no_partition_beats_one_export
#print axioms doorIV_multiPiece_coherence_mem_Icc_export
#print axioms doorIV_multiPiece_exact_saving_export
#print axioms doorIV_multiPiece_eps_budget_eq_export
#print axioms doorIV_multiPiece_eps_budget_iff_export
#print axioms doorIV_multiPiece_no_eps_slack_one_side_zero_export
#print axioms doorIV_multiWindow_budget_forces_card_le_export
#print axioms doorIV_no_multiWindow_split_rhs_le_strict_budget_export
#print axioms doorIV_argmaxDecoupled_const_ge_ratio_export
#print axioms doorIV_argmaxDecoupled_no_control_below_ratio_export
#print axioms doorIV_argmaxDecoupled_uniformControl_iff_ratio_export
#print axioms doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export
#print axioms doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export
#print axioms doorIV_argmaxDecoupled_uniformControlOn_of_subset_export
#print axioms doorIV_argmaxDecoupled_no_controlOn_superset_export
#print axioms doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export
#print axioms doorIV_argmaxDecoupled_controlOn_constant_pos_export
#print axioms doorIV_argmaxDecoupled_point_ratio_gt_no_controlOn_export
#print axioms doorIV_argmaxDecoupled_no_absolute_constOn_export
#print axioms doorIV_argmaxDecoupled_candidate_pos_on_export
#print axioms doorIV_argmaxDecoupled_positive_support_on_subset_export
#print axioms doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export
#print axioms doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export
#print axioms doorIV_argmaxDecoupled_control_constant_pos_export
#print axioms doorIV_argmaxDecoupled_no_nonpos_candidate_control_export
#print axioms doorIV_argmaxDecoupled_no_zero_candidate_control_export
#print axioms doorIV_argmaxDecoupled_candidate_pos_export
#print axioms doorIV_argmaxDecoupled_positive_support_subset_export
#print axioms doorIV_argmaxDecoupled_no_absolute_const_export
#print axioms doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export
#print axioms doorIV_constant_lt_scaledConstant_of_one_lt_m_export
#print axioms doorIV_not_scaledConstant_le_constant_of_one_lt_m_export
#print axioms doorIV_constant_lt_scaledConstant_iff_one_lt_m_export
#print axioms doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export
#print axioms doorIV_collision_defect_eq_zero_iff_injOn_export
#print axioms doorIV_collision_defect_pos_iff_not_injOn_export
#print axioms doorIV_sixPoint_lever_vacuous_export
#print axioms doorIV_correlation_hierarchy_no_lever_export
#print axioms doorIV_correlation_hierarchy_closed_through_six_export
#print axioms doorIV_tripleCorrelation_sixPoint_zero_export
#print axioms doorIV_tripleCorrelation_sixPoint_vacuous_export
#print axioms doorIV_tripleCorrelation_m33_eq_wick_export
#print axioms doorIV_ladder_control_passes_through_wick_export
#print axioms doorIV_whole_ladder_wick_export
#print axioms doorIV_whole_ladder_control_export
#print axioms doorIV_crossHalf_norm_add_eq_halfMass_export
#print axioms doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export
#print axioms doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export
#print axioms doorIV_halfMassBalance_single_half_pays_floor_export
#print axioms doorIV_halfMassBalance_descent_loss_eq_two_export
#print axioms doorIV_halfMassBalance_descent_loss_le_two_export
#print axioms doorIV_halfMass_eta_image_smul_eq_eta_dilate_export
#print axioms doorIV_halfMass_eta_index_two_split_dilate_export
#print axioms doorIV_halfMass_norm_eta_le_two_dilate_export
#print axioms doorIV_halfMass_eq_two_dilate_export
#print axioms doorIV_halfMass_norm_eta_eq_two_dilate_of_coherent_export
#print axioms doorIV_sign_positiveMass_eq_negativeMass_export
#print axioms doorIV_sign_not_all_nonneg_of_positiveMass_pos_export
#print axioms doorIV_sign_exists_negative_cross_of_positiveMass_pos_export
#print axioms doorIV_sign_exists_positive_cross_of_negativeMass_pos_export
#print axioms doorIV_sign_positiveMass_le_half_card_export
#print axioms doorIV_sign_negativeMass_le_half_card_export
#print axioms doorIV_sign_positiveMass_eq_half_total_doublingMass_export
#print axioms doorIV_sign_negativeMass_eq_half_total_doublingMass_export
#print axioms doorIV_gappedMinor125_159_eq_zero_export
#print axioms doorIV_not_gappedMinor125_159_ne_zero_export
#print axioms doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export
#print axioms doorIV_eighthCumulant_no_fixedSignCertificate_export
#print axioms doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export
#print axioms doorIV_levelWorst_le_prize_budget_of_xgate_export
#print axioms doorIV_gateThreshold_split_telescope_sqrt2_export
#print axioms doorIV_gateThreshold_strictly_above_clean_export
#print axioms doorIV_levelWorst_base_step_two_export
#print axioms doorIV_levelWorst_base_corrected_of_gate_export
#print axioms doorIV_strict_peak_single_coset_export
#print axioms doorIV_strict_maximizer_iff_translate_export
#print axioms doorIV_strict_peak_Ncos_eq_one_export

/-! ## Recent Door-IV capstones: resonator collapse and Rudnev/incidence stall.
Scope: **obstruction/capstone**.

These exports make the latest #444 reductions discoverable from the permanent index. The resonator
brick records that the natural Montgomery-Soundararajan resonator on `μ_n` reproduces the ordinary
moment-ratio floor; the Rudnev brick records, in exponent bookkeeping, why point-plane/sum-product
incidence savings at `β = 4` stall at the `α = 1` census wall rather than the prize `α = 1/2`.
-/

/-- **[obstruction, AvResonator]** The natural resonator on `G` gives exactly the moment-ratio
inequality `Σ‖η‖⁴ ≤ M²·Σ‖η‖²`. Thus this resonator lower-bound route factors through the already
mapped moment/DC-crossover wall; it is a lower witness, not a Door-IV upper-control mechanism. -/
theorem doorIV_resonator_one_gives_moment_floor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 4)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F),
              ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2) :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonator.resonator_one_gives_moment_floor ψ G hne

/-- **[obstruction, RudnevPointPlaneStall]** At the prize exponent `β = 4`, the subgroup density
parameter is exactly the point-plane/sum-product threshold `θ = 1/4`. The known incidence engine is
therefore on the boundary, not in a strict-saving regime. -/
theorem doorIV_rudnev_theta_at_beta_four_export :
    _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta 4 = 1 / 4 :=
  _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta_at_beta_four

/-- **[obstruction, RudnevPointPlaneStall]** To make the incidence exponent reach the prize value
`1/2`, the saving would have to be `κ = β + r - 1`, linear in the depth `r`. Fixed point-plane /
sum-product savings cannot supply this; the remaining gap is the BGK phase-cancellation wall. -/
theorem doorIV_rudnev_prize_needs_r_linear_saving_export (β κ : ℝ) (r : ℕ) (hr : 0 < r) :
    _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.MExponent β κ r = 1 / 2 ↔
      κ = β + r - 1 :=
  _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.prize_needs_r_linear_saving β κ r hr

#print axioms doorIV_resonator_one_gives_moment_floor_export
#print axioms doorIV_rudnev_theta_at_beta_four_export
#print axioms doorIV_rudnev_prize_needs_r_linear_saving_export


/-! ## Door-IV Lane 1 rule-3 thickness-invariance exports.
Scope: **obstruction**.

These exports make the recent near-worst coherence-deficit and half-mass rule-3 negatives permanent:
if the thin and thick regime values of a scalar lever remain comparable within a factor below two,
that lever cannot supply the factor-two regime separation required of a thinness-essential CORE
route.
-/

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** If a lever's thin and thick values
are comparable within `K < 2` and the thin value is positive, then it admits no factor-two thin-side
separation. This is the reusable kernel behind the near-worst coherence-deficit rule-3 failure. -/
theorem doorIV_regimeLever_not_factor2_thin_of_comparable_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever)
    {K : ℝ} (hK : K < 2) (hthin_pos : 0 < L.thin)
    (hcomp : L.Comparable K) : ¬ L.Factor2ThinSeparation :=
  L.not_factor2_thin_of_comparable hK hthin_pos hcomp

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** The exact probe-facing equivalence:
no factor-two thin separation is the same as `thick < 2*thin`. -/
theorem doorIV_regimeLever_no_factor2_thin_iff_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever) :
    (¬ L.Factor2ThinSeparation) ↔ L.thick < 2 * L.thin :=
  L.no_factor2_thin_iff_thick_lt_two_thin

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** The half-mass companion:
comparability within the measured factor `1.07 < 2` forbids both thin- and thick-side factor-two
separation. The worst-`b` half-mass is therefore thickness-blind, not a thin-specific leak. -/
theorem doorIV_halfMass_lever_not_separating_either_side_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever)
    (hthin_pos : 0 < L.thin) (hthick_pos : 0 < L.thick)
    (hcomp : L.Comparable (107 / 100 : ℝ)) :
    (¬ L.Factor2ThinSeparation) ∧ (¬ L.Factor2ThickSeparation) :=
  L.halfMass_lever_not_separating_either_side hthin_pos hthick_pos hcomp

#print axioms doorIV_regimeLever_not_factor2_thin_of_comparable_export
#print axioms doorIV_regimeLever_no_factor2_thin_iff_export
#print axioms doorIV_halfMass_lever_not_separating_either_side_export


/-! ## Door-IV Lane 1 finite coherent-argmax slack obstructions.
Scope: **obstruction**.

These exports package the probe-native finite-support wrappers for the coherent-argmax no-go: if the
observed finite argmax itself has full coherence, adding a zero-slack baseline, affine baseline, or
multiplicative normalized factor cannot rescue a slack certificate whose baseline is below the peak.
-/

open _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Vanishing-slack form: at a fully
coherent frequency, a zero-slack certificate collapses all the way to `mass ≤ 0`. This is the local
reason the `1 - ρ(b)` slack lever cannot control a positive coherent peak. -/
theorem doorIV_coherenceSlack_vanishing_bound_at_coherent_export {ι : Type*}
    {mass coh : ι → ℝ} {g : ℝ → ℝ}
    (hb : CoherenceSlackBound mass coh g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ 0 :=
  slack_bound_trivial_at_coherent hb hcoh

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Any relaxed slack certificate evaluated at
full coherence reduces to its zero-slack baseline `g 0`; no slack survives at the adversarial point. -/
theorem doorIV_coherenceSlack_baseline_bound_at_coherent_export {ι : Type*}
    {mass coh : ι → ℝ} {g : ℝ → ℝ}
    (hb : CoherenceSlackBoundWithBaseline mass coh g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ g 0 :=
  slack_bound_withBaseline_at_coherent hb hcoh

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Affine slack collapses to its additive
baseline at full coherence; a `1 - ρ` penalty contributes nothing where `ρ = 1`. -/
theorem doorIV_affineCoherenceSlack_baseline_bound_at_coherent_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    (hb : AffineCoherenceSlackBound mass coh B g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ B :=
  affineSlack_bound_at_coherent hb hcoh

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Multiplicative slack collapses to its
baseline at full coherence; a normalized ratio factor cannot damp the coherent worst frequency. -/
theorem doorIV_multiplicativeCoherenceSlack_baseline_bound_at_coherent_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    (hb : MultiplicativeCoherenceSlackBound mass coh B g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ B :=
  multiplicativeSlack_bound_at_coherent hb hcoh

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite observed-argmax baseline form:
when the coherent argmax has peak mass above `g 0`, a baseline slack certificate cannot hold. -/
theorem doorIV_no_coherenceSlackWithBaseline_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : g 0 < mass bstar) :
    ¬ CoherenceSlackBoundWithBaseline mass coh g :=
  no_coherenceSlackBoundWithBaseline_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite affine form: a below-peak
additive baseline cannot be rescued by a slack penalty at a fully coherent observed argmax. -/
theorem doorIV_no_affineCoherenceSlack_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ AffineCoherenceSlackBound mass coh B g :=
  no_affineCoherenceSlackBound_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite multiplicative form: a below-peak
baseline times a normalized slack factor cannot hold at a fully coherent observed argmax. -/
theorem doorIV_no_multiplicativeCoherenceSlack_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ MultiplicativeCoherenceSlackBound mass coh B g :=
  no_multiplicativeCoherenceSlackBound_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

#print axioms doorIV_coherenceSlack_vanishing_bound_at_coherent_export
#print axioms doorIV_coherenceSlack_baseline_bound_at_coherent_export
#print axioms doorIV_affineCoherenceSlack_baseline_bound_at_coherent_export
#print axioms doorIV_multiplicativeCoherenceSlack_baseline_bound_at_coherent_export
#print axioms doorIV_no_coherenceSlackWithBaseline_finsetArgmax_export
#print axioms doorIV_no_affineCoherenceSlack_finsetArgmax_export
#print axioms doorIV_no_multiplicativeCoherenceSlack_finsetArgmax_export


/-! ## Door-IV Lane 2 floor-ladder capstone exports.
Scope: **lower-floor/capstone**.

These exports make the general moment-ratio lower-floor ladder permanent and discoverable.
They are floor statements: they certify unavoidable mass of the worst frequency, and explicitly do
not prove the CORE upper bound. The value is the citable `M² · Aᵣ ≥ Aᵣ₊₁` capstone that subsumes
`√3`, `√5`, and `√7` below the documented DC-crossover ceiling.
-/

/-- **[lower-floor, AvFloorLadder]** General abstract moment-ratio ladder: for every depth `r`,
`∑_{b≠0} ‖η_b‖^(2(r+1)) ≤ M² * ∑_{b≠0} ‖η_b‖^(2r)`, where
`M² = sup'_{b≠0} ‖η_b‖²`. This is the permanent index form of the citable `M² · Aᵣ ≥ Aᵣ₊₁`
floor capstone, not a cancellation upper bound. -/
theorem doorIV_avFloorLadder_momentSucc_le_sup_moment_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ (2 * (r + 1)))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F),
              ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ (2 * r)) :=
  _root_.ArkLib.ProximityGap.Frontier.AvFloorLadder.momentSucc_le_sup'_moment ψ G hne r

/-- **[lower-floor, AvFloorLadder]** General energy-form ladder: substituting the exact nonzero
moment identity gives `q*E_{r+1} - n^(2(r+1)) ≤ M² * (q*E_r - n^(2r))` for every `r`. This
packages the `√3/√5/√7/...` moment-ratio floor family under one indexed theorem. -/
theorem doorIV_avFloorLadder_energy_moment_floor_general_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (Fintype.card F : ℝ) * _root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G (r + 1)
        - (G.card : ℝ) ^ (2 * (r + 1))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ)
              * _root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r
              - (G.card : ℝ) ^ (2 * r)) :=
  _root_.ArkLib.ProximityGap.Frontier.AvFloorLadder.energy_moment_floor_general hψ G hne r

#print axioms doorIV_avFloorLadder_momentSucc_le_sup_moment_export
#print axioms doorIV_avFloorLadder_energy_moment_floor_general_export


/-! ## Door-IV Lane 3 sum-product/incidence census-stall exports.
Scope: **obstruction/capstone**.

These exports make the beta-four incidence-threshold obstruction permanent. They record that
newer sum-product and incidence levers either point in the wrong direction, sit on the `θ = 1/4`
boundary at beta four, or deliver only the best-case `κ = 1/15`, far short of the prize `κ = 1`.
-/

/-- **[obstruction, SumProductCensusStall]** The Stevens-de Zeeuw best-case exponent saving is
`κ = 1/15`, positive but strictly below the prize saving `κ = 1`. -/
theorem doorIV_sumProduct_sdz_does_not_reach_prize_export :
    (0 : ℝ) < 1 / 15 ∧ (1 : ℝ) / 15 < 1 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.sdz_does_not_reach_prize

/-- **[obstruction, SumProductCensusStall]** At beta four the point-plane/SdZ threshold is exactly
met, not strictly exceeded: `¬ (1/4 > 1/4)`. Thus the strict-saving incidence engine is boundary
blocked in the prize regime. -/
theorem doorIV_sumProduct_pointplane_boundary_beta4_export :
    ¬ ((1 : ℝ) / 4 > 1 / 4) :=
  _root_.ArkLib.ProximityGap.SP0Scratch.pointplane_threshold_boundary_at_beta4

/-- **[obstruction, SumProductCensusStall]** The census-stall capstone: all `0 ≤ κ < 1` savings are
vacuous for the prize target, `κ = 1/15` is in that vacuous range, and the prize `κ = 1` is not
delivered by the cluster. -/
theorem doorIV_sumProduct_census_stall_confirmed_export :
    (∀ κ : ℝ, 0 ≤ κ → κ < 1 →
        _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 κ) ∧
      _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 (1 / 15) ∧
      ¬ _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 1 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.census_stall_confirmed

/-- **[obstruction, SumProductCensusStall]** Kurihara-style valuation data does not determine the
archimedean energy count: the same total count can be compatible with energies `T` and `T²`, and for
`T ≥ 2` these differ strictly. -/
theorem doorIV_kurihara_valuation_not_count_export (T : ℝ) (hT : 2 ≤ T) : T < T ^ 2 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.kurihara_is_valuation_not_count T hT

#print axioms doorIV_sumProduct_sdz_does_not_reach_prize_export
#print axioms doorIV_sumProduct_pointplane_boundary_beta4_export
#print axioms doorIV_sumProduct_census_stall_confirmed_export
#print axioms doorIV_kurihara_valuation_not_count_export


/-! ## Door-IV Lane 3 every-angle failure-step exports.
Scope: **obstruction/capstone**.

These exports make the newest exact failure-step certificates permanent and discoverable. They are
not new moment grinding and not CORE upper bounds: the SOS export pins the finite `n = 16` Hankel
obstruction to a uniform SOS certificate; the depth export pins why the sum-product cluster is
confined to a vacuous depth-2 input at `β = 4`; the monodromy export pins that every `b`-summed
correlation remains an abelian lattice count, so the A5 non-abelian-growth escape has no sheaf to
apply to.
-/

/-- **[obstruction, A1SOSLadderN16]** At the exact Fermat-prime `n = 16`, `q = 65537` witness,
the integral Wick-deficit Hankel minor `d̃₁*d̃₃ - d̃₂^2` is strictly negative. Thus the true
per-depth deficits are not a positive-measure moment sequence, blocking a single degree-extending
SOS/Gram certificate in the moment degree. -/
theorem doorIV_A1SOS_hankel_minor2_negative_export :
    _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 1
        * _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 3
      - _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 2 ^ 2 < 0 :=
  _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.hankel_minor2_negative

/-- **[obstruction, A1SOSLadderN16]** The exact `n = 16`, `q = 65537` beta-four window sanity:
`n^4 ≤ q` and `n ∣ q-1`. This keeps the SOS/Hankel witness inside the proper thin-prime regime,
not the full-group false-positive regime. -/
theorem doorIV_A1SOS_window_export :
    _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.n ^ 4
        ≤ _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.q ∧
      _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.n ∣
        (_root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.q - 1) :=
  _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.window

/-- **[obstruction, A3DepthConfinement]** The capstone depth mismatch: at beta four, the native
sum-product/depth-2 engine is vacuous even with optimal `E₂`, remains vacuous for any `E₂` exponent
`a ≥ 2`, and Wick-fed saving starts only after depth four. This is the exact depth/order mismatch
that prevents a second-energy sum-product input from being the prize mechanism. -/
theorem doorIV_A3_depth_order_mismatch_export :
    (1 : ℝ) < _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.momentEngineExp 4 2 2 ∧
    (∀ a : ℝ, 2 ≤ a →
      (1 : ℝ) < _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.momentEngineExp 4 a 2) ∧
    (_root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFedExp 4 = 1 ∧
      ∀ r : ℝ, 4 < r →
        _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFedExp r < 1) :=
  _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth_order_mismatch

/-- **[obstruction, A5TwistedMonodromy]** Every `b`-summed Gauss-period correlation is a `q` times
an integer lattice count with zero imaginary part, uniformly in all orders. Hence the proposed
A5 growing non-abelian monodromy route has no non-abelian `√q` contribution to exploit. -/
theorem doorIV_A5_monodromy_abelian_all_orders_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∀ a c : ℕ, ∃ N : ℕ,
      (∑ b : F,
          _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ a
            * (starRingEnd ℂ)
                (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ c))
        = (Fintype.card F : ℂ) * (N : ℂ) ∧
      (∑ b : F,
          _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ a
            * (starRingEnd ℂ)
                (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ c)).im = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.A5TwistedMonodromyAbelianVerdict.monodromy_abelian_all_orders hψ G

#print axioms doorIV_A1SOS_hankel_minor2_negative_export
#print axioms doorIV_A1SOS_window_export
#print axioms doorIV_A3_depth_order_mismatch_export
#print axioms doorIV_A5_monodromy_abelian_all_orders_export


/-! ## Door-IV Lane 2 Jacobi bounded-edge relocation exports.
Scope: **capstone/obstruction**.

These exports make the char-`p` Jacobi recurrence-coefficient relocation citable from the permanent
index. The tool is real: support-bounded Jacobi coefficients give a uniformly bounded edge, unlike
the exploding char-0 Wick edge. The honesty brake is equally real: the unconditional Gershgorin
ceiling is only `3S`, hence support-trivial; any prize-scale improvement must use fine arithmetic
structure of the recurrence coefficients, not the support bound alone.
-/

/-- **[capstone, JacobiBounded]** Support-bounded char-`p` Jacobi recurrence coefficients have
uniformly bounded edge terms: `edge a b k ≤ 3S` for every level `k`. This packages the real
relocation from an unbounded char-0 Wick edge to a bounded char-`p` object. -/
theorem doorIV_jacobi_edge_le_three_S_export {a b : ℕ → ℝ} {S : ℝ}
    (h : _root_.ProximityGap.Frontier.JacobiBounded.SupportBounded a b S) (k : ℕ) :
    _root_.ProximityGap.Frontier.JacobiBounded.edge a b k ≤ 3 * S :=
  _root_.ProximityGap.Frontier.JacobiBounded.edge_le_three_S h k

/-- **[capstone, JacobiBounded]** Gershgorin consumption form: if the prize quantity `M` is
controlled by one bounded Jacobi edge, then `M ≤ 3S`. With `S = n` this is the unconditional
support-trivial ceiling produced by the recurrence-coefficient tool. -/
theorem doorIV_jacobi_M_le_three_S_export {a b : ℕ → ℝ} {S M : ℝ}
    (h : _root_.ProximityGap.Frontier.JacobiBounded.SupportBounded a b S)
    {k₀ : ℕ} (hM : M ≤ _root_.ProximityGap.Frontier.JacobiBounded.edge a b k₀) :
    M ≤ 3 * S :=
  _root_.ProximityGap.Frontier.JacobiBounded.M_le_three_S h hM

/-- **[obstruction, JacobiBounded]** Honesty brake: for positive support radius, the uniform
`3S` Gershgorin ceiling is strictly above the support radius itself. Thus the unconditional bounded
edge fact alone cannot supply the sub-radius/prize-scale cancellation; the remaining content is the
fine arithmetic of the coefficients. -/
theorem doorIV_jacobi_three_S_strictly_above_support_export {a b : ℕ → ℝ} {S : ℝ}
    (h : _root_.ProximityGap.Frontier.JacobiBounded.SupportBounded a b S) (hS : 0 < S) :
    S < 3 * S :=
  _root_.ProximityGap.Frontier.JacobiBounded.three_S_strictly_above_support h hS

#print axioms doorIV_jacobi_edge_le_three_S_export
#print axioms doorIV_jacobi_M_le_three_S_export
#print axioms doorIV_jacobi_three_S_strictly_above_support_export


/-! ## Door-IV Lane 2 Hermite-turnover reduction exports.
Scope: **conditional capstone/obstruction**.

These exports make form (D) of the Jacobi problem statement citable: under the explicit
edge-turnover model `M^2 = 2*n*kstar`, the prize-scale bound is equivalent to `kstar ≤ L`, and the
free support/Gershgorin input only gives the much weaker `kstar ≤ (9/2)n`. The missing theorem is
therefore exactly early turnover `kstar = O(log p)`; the exports do not assert that model or prove
that bound.
-/

/-- **[conditional capstone, HermiteTurnover]** Under the explicit edge-turnover model, the prize
bound `M ≤ sqrt 2 * sqrt(n*L)` is equivalent to the scalar turnover-depth bound `kstar ≤ L`. -/
theorem doorIV_hermite_prize_iff_turnover_le_export {n M kstar L : ℝ}
    (h : _root_.ProximityGap.Frontier.HermiteTurnover.EdgeTurnover n M kstar) (hL : 0 ≤ L) :
    M ≤ Real.sqrt 2 * Real.sqrt (n * L) ↔ kstar ≤ L :=
  _root_.ProximityGap.Frontier.HermiteTurnover.prize_iff_turnover_le h hL

/-- **[conditional capstone, HermiteTurnover]** Specializing `L = log p`, the Jacobi form of the
prize is exactly `kstar ≤ log p`, under the explicit edge-turnover model. -/
theorem doorIV_hermite_prize_iff_turnover_le_logp_export {n M kstar p : ℝ}
    (h : _root_.ProximityGap.Frontier.HermiteTurnover.EdgeTurnover n M kstar)
    (hp1 : 1 ≤ p) :
    M ≤ Real.sqrt 2 * Real.sqrt (n * Real.log p) ↔ kstar ≤ Real.log p :=
  _root_.ProximityGap.Frontier.HermiteTurnover.prize_iff_turnover_le_logp h hp1

/-- **[obstruction, HermiteTurnover]** The free support/Gershgorin ceiling `M ≤ 3n` yields only
`kstar ≤ (9/2)n` under the edge-turnover model. This is the support-trivial turnover bound, far
weaker than the desired `O(log p)` early-turnover theorem. -/
theorem doorIV_hermite_turnover_le_free_ceiling_export {n M kstar : ℝ}
    (h : _root_.ProximityGap.Frontier.HermiteTurnover.EdgeTurnover n M kstar)
    (hMle : M ≤ 3 * n) : kstar ≤ (9 / 2) * n :=
  _root_.ProximityGap.Frontier.HermiteTurnover.turnover_le_free_ceiling h hMle

/-- **[obstruction, HermiteTurnover]** If the free ceiling is tight and the target scale `L` is
below `(9/2)n`, then the prize bound at scale `L` fails. This packages the `O(n)` versus `O(log p)`
gap that the support bound cannot close. -/
theorem doorIV_hermite_free_ceiling_insufficient_for_prize_export {n M kstar : ℝ}
    (h : _root_.ProximityGap.Frontier.HermiteTurnover.EdgeTurnover n M kstar)
    (htight : (9 / 2) * n ≤ kstar) {L : ℝ} (hLnn : 0 ≤ L)
    (hLgap : L < (9 / 2) * n) :
    ¬ (M ≤ Real.sqrt 2 * Real.sqrt (n * L)) :=
  _root_.ProximityGap.Frontier.HermiteTurnover.free_ceiling_insufficient_for_prize h htight hLnn hLgap

#print axioms doorIV_hermite_prize_iff_turnover_le_export
#print axioms doorIV_hermite_prize_iff_turnover_le_logp_export
#print axioms doorIV_hermite_turnover_le_free_ceiling_export
#print axioms doorIV_hermite_free_ceiling_insufficient_for_prize_export


/-! ## Door-IV Lane 3 coset-resonator diagonal/off-diagonal localization exports.
Scope: **obstruction/reduction**.

These exports make the coset-multiplicative resonator verdict permanent. The diagonal part of any
unit-modulus coset resonator is exactly the Parseval floor and is independent of the resonator
coefficients. Therefore any logarithmic gain must live entirely in the off-diagonal Gauss-period
spectral autocorrelation, i.e. in the same phase-correlation/BGK wall rather than in a free
Euler-product diagonal contribution.
-/

/-- **[reduction, AvResonatorCand1]** The coset-resonator lower-bound engine specialized to the
unit-coset resonator weight `‖∑ r_j φ_j(b)‖²`. This is a valid lower-bound identity for `M²`, but
it does not by itself supply a logarithmic gain. -/
theorem doorIV_cosetResonator_lower_bound_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (phi : ι → F → ℂ)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖_root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.cosetResonator J r phi b‖ ^ 2
          * ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F),
              ‖_root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.cosetResonator J r phi b‖ ^ 2) :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_lower_bound
    ψ G J r phi hne

/-- **[obstruction, AvResonatorCand1]** The diagonal numerator of any unit-modulus coset resonator
is phase-free: it is just `‖r‖²` times the nonzero Parseval mass. Thus the resonator's diagonal part
cannot be the source of the missing logarithm. -/
theorem doorIV_cosetResonator_diagonal_numerator_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (phi : ι → F → ℂ)
    (hphi : ∀ j ∈ J, ∀ b ∈ Finset.univ.erase (0 : F), ‖phi j b‖ = 1) :
    (∑ j ∈ J, r j * (starRingEnd ℂ) (r j)
        * (∑ b ∈ Finset.univ.erase (0 : F),
            phi j b * (starRingEnd ℂ) (phi j b)
              * ((‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2 : ℝ) : ℂ)))
      = ((∑ j ∈ J, (‖r j‖ ^ 2 : ℝ)) : ℂ)
          * ((∑ b ∈ Finset.univ.erase (0 : F),
                ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2 : ℝ) : ℂ) :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_numerator
    ψ G J r phi hphi

/-- **[obstruction, AvResonatorCand1]** The diagonal-only coset-resonator ratio cancels the
coefficient mass `‖r‖²`, so it is independent of the resonator. This algebraic cancellation is the
kernel statement behind the no-free-log verdict. -/
theorem doorIV_cosetResonator_diagonal_ratio_export
    {ι : Type*} (J : Finset ι) (r : ι → ℂ) (A₁ Q : ℝ)
    (hr : 0 < ∑ j ∈ J, ‖r j‖ ^ 2) :
    ((∑ j ∈ J, ‖r j‖ ^ 2) * A₁) / (Q * (∑ j ∈ J, ‖r j‖ ^ 2)) = A₁ / Q :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_ratio J r A₁ Q hr

/-- **[obstruction, AvResonatorCand1]** Instantiating the diagonal ratio with the subgroup second
moment gives exactly the Parseval floor `(q*n - n²)/(q-1)`. Any logarithmic improvement must therefore
come from the off-diagonal Gauss-period spectral autocorrelation, not from the diagonal resonator
Euler product. -/
theorem doorIV_cosetResonator_diagonal_floor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ)
    (hr : 0 < ∑ j ∈ J, ‖r j‖ ^ 2) :
    ((∑ j ∈ J, ‖r j‖ ^ 2)
        * (∑ b ∈ Finset.univ.erase (0 : F),
            ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
        / (((Fintype.card F : ℝ) - 1) * (∑ j ∈ J, ‖r j‖ ^ 2))
      = ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1) :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_floor
    hψ G J r hr

#print axioms doorIV_cosetResonator_lower_bound_export
#print axioms doorIV_cosetResonator_diagonal_numerator_export
#print axioms doorIV_cosetResonator_diagonal_ratio_export
#print axioms doorIV_cosetResonator_diagonal_floor_export


/-! ## Door-IV Lane 2 Hasse-Davenport cocycle phase-coupling exports.
Scope: **conditional reduction/obstruction**.

These exports make the new re-randomization-asymmetric HD cocycle machinery citable. They do not
prove the missing contraction theorem. They pin the exact escape criterion: phase-blind or
re-randomization-invariant functionals are average-pinned, while the HD cocycle is not invariant and
reduces the prize to a concrete cocycle-contraction/off-diagonal-deficit input.
-/

/-- **[obstruction, HDCocycle]** Universal re-randomization no-go: a re-randomization-invariant
functional has the same value on `u` and on any coordinatewise phase twist of `u`. Such a functional
cannot distinguish the arithmetic Gauss phases from a randomized phase vector. -/
theorem doorIV_hd_rerandom_invariant_forces_average_export
    {m : ℕ} {Phi : (Fin m → ℂ) → ℝ}
    (hPhi : _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.RerandomInvariant Phi)
    (u eps : Fin m → ℂ) :
    Phi (_root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom eps u) = Phi u :=
  _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom_invariant_forces_average
    hPhi u eps

/-- **[escape criterion, HDCocycle]** The Hasse-Davenport cocycle is re-randomization-asymmetric:
if one cocycle value is nonzero, a genuine unit-modulus phase twist breaks the same cocycle relation.
Thus any tool that genuinely consumes the HD identity lies outside the phase-blind class. -/
theorem doorIV_hd_cocycle_breaks_rerandom_export
    {m : ℕ} (u : Fin m → ℂ) (dbl lag : Fin m → Fin m) (w : Fin m → ℂ)
    (hcoc : _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.HDCocycle u dbl lag w)
    (j0 : Fin m) (hne : w j0 * u (dbl j0) ≠ 0) :
    ∃ eps : Fin m → ℂ,
      (∀ j, ‖eps j‖ = 1) ∧
        ¬ _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.HDCocycle
          (_root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom eps u) dbl lag w := by
  refine ⟨fun _ => -1, ?_, ?_⟩
  · intro j
    norm_num [Complex.normSq]
  · intro hbad
    have h := hbad j0
    simp only [_root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom] at h
    have horig := hcoc j0
    have hzero : (2 : ℂ) * (w j0 * u (dbl j0)) = 0 := by
      have e : (-1 : ℂ) * u j0 * ((-1 : ℂ) * u (lag j0)) = u j0 * u (lag j0) := by
        ring
      rw [e, horig] at h
      linear_combination h
    have h2 : (w j0 * u (dbl j0)) = 0 := by
      rcases mul_eq_zero.mp hzero with h' | h'
      · norm_num at h'
      · exact h'
    exact hne h2

/-- **[identity, HDCocycle]** The exact self-similarity: under the HD cocycle, the bilinear lag
sum `Σ_j (u_j u_lag(j)) z_j` collapses termwise to the twisted linear sum
`Σ_j (w_j u_dbl(j)) z_j`. -/
theorem doorIV_hd_selfSimilarity_is_linear_in_phases_export
    {m : ℕ} (u : Fin m → ℂ) (dbl lag : Fin m → Fin m) (w z : Fin m → ℂ)
    (hcoc : _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.HDCocycle u dbl lag w) :
    ∑ j, (u j * u (lag j)) * z j = ∑ j, (w j * u (dbl j)) * z j :=
  _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.selfSimilarity_is_linear_in_phases
    u dbl lag w z hcoc

/-- **[conditional reduction, HDCocycle]** A per-level cocycle contraction telescopes down the
2-adic tower: if every `S (a+1) ≤ theta*S a` and `S` is nonnegative, then
`S a ≤ theta^a*S 0`. This is the transfer-operator spectral-radius shape of the proposed route. -/
theorem doorIV_hd_doubling_defect_telescope_export
    {theta : ℝ} {S : ℕ → ℝ} (hS : ∀ a, 0 ≤ S a)
    (hc : _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.CocycleContraction theta S) :
    ∀ a, S a ≤ theta ^ a * S 0 :=
  _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.doubling_defect_telescope hS hc

/-- **[conditional reduction, HDCocycle]** If the cocycle contraction telescope clears the target
budget at depth `a`, then the level-`a` worst-frequency sup meets that target. The only remaining
input is the contraction theorem itself. -/
theorem doorIV_hd_prizeSup_of_cocycleContraction_export
    {theta : ℝ} {S : ℕ → ℝ} {a : ℕ} {target : ℝ}
    (hS : ∀ a, 0 ≤ S a)
    (hc : _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.CocycleContraction theta S)
    (hbudget : theta ^ a * S 0 ≤ target) :
    S a ≤ target :=
  _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.prizeSup_of_cocycleContraction
    hS hc hbudget

/-- **[reduction, HDCocycle]** One contraction step follows from the exact self-similarity value
`S(a+1)=T` plus an off-diagonal deficit `T≤theta*S(a)`. This exposes the missing theorem as a
worst-frequency cocycle-twisted off-diagonal bound, not a moment or completion estimate. -/
theorem doorIV_hd_contractionStep_of_offDiagonalDeficit_export
    {theta : ℝ} {S : ℕ → ℝ} {a : ℕ} {T : ℝ}
    (hSS : S (a + 1) = T) (hdef : T ≤ theta * S a) :
    S (a + 1) ≤ theta * S a :=
  _root_.ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.contractionStep_of_offDiagonalDeficit
    hSS hdef

#print axioms doorIV_hd_rerandom_invariant_forces_average_export
#print axioms doorIV_hd_cocycle_breaks_rerandom_export
#print axioms doorIV_hd_selfSimilarity_is_linear_in_phases_export
#print axioms doorIV_hd_doubling_defect_telescope_export
#print axioms doorIV_hd_prizeSup_of_cocycleContraction_export

#print axioms doorIV_hd_contractionStep_of_offDiagonalDeficit_export

/-! ## Door-IV Lane 2/3 onset-to-saddle credit chain exports.
Scope: **reduction/obstruction capstone**.

These exports make the newest `W_r` onset lattice and saddle-credit correction citable from the
permanent index. They do not prove the saddle budget inequality. They pin the exact failure of the
static `W_r = 0` target: pigeonhole-onset forces short wraparound relations below the saddle, and
once the real-valued wraparound count is positive, any successful budget proof must spend a strictly
positive DC/char-0 credit.
-/

/-- **[obstruction, A2OnsetLatticeMinimum]** Contributing-pair embedding: two reduced `r`-tuples
with equal residue evaluation but distinct integer reductions produce a nonzero lattice vector of
`ℓ¹`-weight at most `2r`. This is the exact short-vector source of the onset law. -/
theorem doorIV_A2_contributing_pair_short_lattice_export
    {m p r : ℕ} (g : ZMod p) (rv rw : Fin m → ℤ)
    (hrv : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 rv ≤ r)
    (hrw : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 rw ≤ r)
    (heval : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.eval g rv =
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.eval g rw) (hne : rv ≠ rw) :
    _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.inLattice g (fun j => rv j - rw j) ∧
      (fun j => rv j - rw j) ≠ 0 ∧
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 (fun j => rv j - rw j) ≤ 2 * r :=
  _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.contributing_pair_short_lattice
    g rv rw hrv hrw heval hne

/-- **[obstruction, A2OnsetLatticeMinimum]** Onset law, sufficient direction: if every nonzero
lattice vector has `ℓ¹`-weight greater than `2r`, then equal evaluations of two reduced `r`-tuples
force the reductions to be equal. Equivalently, below the first lattice minimum there is no genuine
wraparound contribution. -/
theorem doorIV_A2_no_wraparound_below_lambda_export
    {m p r : ℕ} (g : ZMod p)
    (hmin : ∀ a : Fin m → ℤ,
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.inLattice g a → a ≠ 0 →
        2 * r < _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a)
    (rv rw : Fin m → ℤ)
    (hrv : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 rv ≤ r)
    (hrw : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 rw ≤ r)
    (heval : _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.eval g rv =
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.eval g rw) :
    rv = rw :=
  _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.no_wraparound_of_below_lambda
    g hmin rv rw hrv hrw heval

/-- **[obstruction, A2OnsetLatticeMinimum]** Pigeonhole upper bound on the onset minimum: more than
`p` integer vectors of `ℓ¹`-weight at most `w` force two to collide modulo `p`, hence a nonzero
lattice relation of weight at most `2w`. This is the short-relation mechanism that makes onset
constant-scale at prize parameters. -/
theorem doorIV_A2_short_relation_of_card_gt_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w : ℕ)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.inLattice g (fun j => a j - b j) ∧
      (fun j => a j - b j) ≠ 0 ∧
      _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 (fun j => a j - b j) ≤ 2 * w :=
  _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.exists_short_relation_of_card_gt
    p g w S hSw hcard

/-- **[obstruction, A2OnsetLatticeMinimum]** Pigeonhole refutes `OnsetSavesSaddle`: if the short
ball already outgrows `p` at radius `w ≤ r`, then the saddle cannot be certified by `W_r = 0`.
The surviving obligation is the orbit-count/budget bound beyond onset. -/
theorem doorIV_A2_not_onsetSavesSaddle_of_card_gt_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card) :
    ¬ _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r :=
  _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.not_onsetSavesSaddle_of_card_gt
    p g w r hwr S hSw hcard

/-- **[obstruction, WraparoundSaddleCreditForced]** If the saddle wraparound mass is positive and
the budget `p*W≤credit` holds with `p>0`, then the credit is strictly positive. Therefore a saddle
budget proof cannot be a zero-credit certificate. -/
theorem doorIV_saddle_credit_pos_of_budget_wrap_pos_export
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hbudget : p * W ≤ credit) :
    0 < credit :=
  _root_.ArkLib.ProximityGap.Frontier.WraparoundSaddleCreditForced.credit_pos_of_budget_of_wrap_pos
    hp hW hbudget

/-- **[obstruction, WraparoundSaddleCreditForced]** Past onset, positive wraparound makes the
static `W=0` target false and forces strictly positive credit under the budget inequality. This is
Shaw's corrected target in kernel form: prove the budget on positive `W`, not `W=0`. -/
theorem doorIV_saddle_target_budget_not_vanishing_export
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hbudget : p * W ≤ credit) :
    W ≠ 0 ∧ 0 < credit ∧ p * W ≤ credit :=
  _root_.ArkLib.ProximityGap.Frontier.WraparoundSaddleCreditForced.saddle_target_is_budget_not_vanishing
    hp hW hbudget

/-- **[capstone, OnsetToSaddleCreditChain]** The count-positivity bridge as a stable named
index predicate: failure of `OnsetSavesSaddle` at depth `r` implies strictly positive real-valued
wraparound count `W r`. This remains an explicit hypothesis, not an asserted theorem. -/
def doorIV_wraparoundCountPositive_export (m : ℕ) {p : ℕ} (g : ZMod p) (W : ℕ → ℝ) : Prop :=
  _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.WraparoundCountPositive m g W

/-- **[capstone, OnsetToSaddleCreditChain]** Pigeonhole below the saddle plus the explicit
count-positivity bridge gives positive wraparound at depth `r`. The bridge is a hypothesis, not
asserted here; the exported theorem wires the proven onset-pigeonhole side to that named rung. -/
theorem doorIV_onset_chain_wrap_pos_of_pigeonhole_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card) (W : ℕ → ℝ)
    (hbridge : _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.WraparoundCountPositive
      m g W) :
    0 < W r :=
  _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.wrap_pos_of_pigeonhole
    p g w r hwr S hSw hcard W hbridge

/-- **[capstone, OnsetToSaddleCreditChain]** Credit-only projection of the full chain:
pigeonhole plus the explicit count-positivity bridge and budget inequality imply `0 < credit`.
This gives a convenient citable scalar form of the saddle-credit consequence. -/
theorem doorIV_credit_pos_of_pigeonhole_chain_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card) (W : ℕ → ℝ)
    (hbridge : doorIV_wraparoundCountPositive_export m g W)
    {pp credit : ℝ} (hpp : 0 < pp) (hbudget : pp * (W r) ≤ credit) :
    0 < credit :=
  _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.credit_pos_of_pigeonhole_chain
    p g w r hwr S hSw hcard W hbridge hpp hbudget

/-- **[capstone, OnsetToSaddleCreditChain]** Full citable chain: pigeonhole refutes onset-saving,
the explicit count-positivity bridge turns that into `0<W_r`, and any successful budget inequality
`pp*W_r≤credit` must spend a strictly positive credit. No budget inequality or CORE bound is asserted. -/
theorem doorIV_onset_chain_saddle_spends_credit_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card) (W : ℕ → ℝ)
    (hbridge : _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.WraparoundCountPositive
      m g W)
    {pp credit : ℝ} (hpp : 0 < pp) (hbudget : pp * (W r) ≤ credit) :
    ¬ _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r ∧
      0 < W r ∧ 0 < credit :=
  _root_.ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain.saddle_forced_past_onset_spends_credit
    p g w r hwr S hSw hcard W hbridge hpp hbudget

#print axioms doorIV_A2_contributing_pair_short_lattice_export
#print axioms doorIV_A2_no_wraparound_below_lambda_export
#print axioms doorIV_A2_short_relation_of_card_gt_export
#print axioms doorIV_A2_not_onsetSavesSaddle_of_card_gt_export
#print axioms doorIV_saddle_credit_pos_of_budget_wrap_pos_export
#print axioms doorIV_saddle_target_budget_not_vanishing_export
#print axioms doorIV_wraparoundCountPositive_export
#print axioms doorIV_onset_chain_wrap_pos_of_pigeonhole_export
#print axioms doorIV_credit_pos_of_pigeonhole_chain_export

#print axioms doorIV_onset_chain_saddle_spends_credit_export

/-! ## Door-IV Lane 2 orbit-count wall dichotomy exports.
Scope: **reduction capstone**.

These exports make the named `OrbitCountWall` reduction discoverable. They record the precise
post-onset dichotomy: if onset does not save the saddle, then the only remaining branch is the
per-shell orbit-count wall plus an explicit orbit-to-moment transfer hypothesis. The wall itself is
not proved here.
-/

/-- **[definition export, OrbitCountWallDichotomy]** The per-shell orbit-count wall: the `n`-fold
orbit contribution at depth `r` is within the Wick saddle budget. This is the named open obligation
that survives once onset fails. -/
theorem doorIV_orbitCountWall_def_export
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (r : ℕ) :
    _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.OrbitCountWall
        orbitCount Wick n r ↔
      n * orbitCount r ≤ Wick r := by
  rfl

/-- **[capstone, OrbitCountWallDichotomy]** Boolean saddle dichotomy: either onset saves the saddle
(no short relation at depth `r`) or onset fails and the burden passes to the orbit-count branch. -/
theorem doorIV_orbit_saddle_obligation_dichotomy_export
    (m : ℕ) {p : ℕ} (g : ZMod p) (r : ℕ) :
    _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r ∨
      ¬ _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r :=
  _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.saddle_obligation_dichotomy
    m g r

/-- **[conditional reduction, OrbitCountWallDichotomy]** On the onset-fails branch, a per-shell
orbit-count wall plus the explicit orbit-to-moment transfer implies the saddle bound. This is the
kernel form of "the saddle bound must come from `OrbitCountWall`". -/
theorem doorIV_orbit_saddle_bound_of_onset_fail_and_wall_export
    (m : ℕ) {p : ℕ} (g : ZMod p) (r : ℕ)
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (SaddleBound : ℕ → Prop)
    (htransfer :
      _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.OrbitWallImpliesSaddle
        m g orbitCount Wick n SaddleBound)
    (honsetFail :
      ¬ _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r)
    (hwall :
      _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.OrbitCountWall
        orbitCount Wick n r) :
    SaddleBound r :=
  _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.saddle_bound_of_onset_fail_and_wall
    m g r orbitCount Wick n SaddleBound htransfer honsetFail hwall

/-- **[conditional reduction, OrbitCountWallDichotomy]** Pigeonhole below the saddle forces onset
failure, so with the explicit orbit-to-moment transfer and the orbit-count wall the saddle bound is
routed through `OrbitCountWall`, not through `W_r=0`. -/
theorem doorIV_orbit_pigeonhole_routes_to_orbit_wall_export
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ))
    (hSw : ∀ a ∈ S, _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.l1 a ≤ w)
    (hcard : p < S.card)
    (orbitCount Wick : ℕ → ℝ) (n : ℝ) (SaddleBound : ℕ → Prop)
    (htransfer :
      _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.OrbitWallImpliesSaddle
        m g orbitCount Wick n SaddleBound)
    (hwall :
      _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.OrbitCountWall
        orbitCount Wick n r) :
    ¬ _root_.ProximityGap.Frontier.A2OnsetLatticeMinimum.OnsetSavesSaddle m g r ∧
      SaddleBound r :=
  _root_.ArkLib.ProximityGap.Frontier.OrbitCountWallDichotomy.pigeonhole_routes_to_orbit_wall
    p g w r hwr S hSw hcard orbitCount Wick n SaddleBound htransfer hwall

#print axioms doorIV_orbitCountWall_def_export
#print axioms doorIV_orbit_saddle_obligation_dichotomy_export
#print axioms doorIV_orbit_saddle_bound_of_onset_fail_and_wall_export
#print axioms doorIV_orbit_pigeonhole_routes_to_orbit_wall_export


/-! ## Door-IV Lane 3 Gross--Koblitz size/L²-norm no-go exports.
Scope: **refuted lever / obstruction**.

These exports make the A10 verdict permanent: the Gross--Koblitz/norm-size route can improve the
naive house base to an L²/AM--GM base, but the resulting no-wraparound threshold remains inactive at
the saddle, and the L² datum does not determine the archimedean norm spread. This is not a CORE
upper bound or a completion estimate; it is a route-elimination brick.
-/

/-- **[A10, AM--GM]** Product of nonnegative conjugate squared moduli is bounded by the L² mean
raised to the number of conjugates. This is the only unconditional information extracted from the
Gross--Koblitz size/L² datum. -/
theorem doorIV_A10_prod_le_mean_pow_card_export
    {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ k ∈ s, 0 ≤ z k) (hs : 0 < s.card) :
    (∏ k ∈ s, z k) ≤ ((∑ k ∈ s, z k) / s.card) ^ s.card :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.prod_le_mean_pow_card
    s z hz hs

/-- **[A10, AM--GM]** Feeding the exact `L²` cap `mean≤4r` gives the norm-square bound
`∏z_k≤(4r)^φ`; this is a size bound only, not a sup-norm or CORE bound. -/
theorem doorIV_A10_norm_sq_le_fourR_pow_export
    {ι : Type*} (s : Finset ι) (z : ι → ℝ) (r : ℝ)
    (hz : ∀ k ∈ s, 0 ≤ z k) (hs : 0 < s.card)
    (hL2 : (∑ k ∈ s, z k) / s.card ≤ 4 * r) (hr : 0 ≤ r) :
    (∏ k ∈ s, z k) ≤ (4 * r) ^ s.card :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.norm_sq_le_fourR_pow
    s z r hz hs hL2 hr

/-- **[A10, comparison]** The L² base `√(4r)` improves the house base `2r` for `r≥1`, but this
base-level improvement is not enough to reach the saddle/deep-r prize scale. -/
theorem doorIV_A10_L2_base_le_house_base_export (r : ℝ) (hr : 1 ≤ r) :
    Real.sqrt (4 * r) ≤ 2 * r :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.L2_base_le_house_base r hr

/-- **[A10, obstruction]** Once `4r≥B²`, the L² norm bound `p≤(4r)^e` excludes nothing from a
prime bounded by `(B²)^e`. Thus the Gross--Koblitz size threshold is vacuous at the saddle. -/
theorem doorIV_A10_L2_threshold_vacuous_at_saddle_export
    (B : ℝ) (r : ℝ) (e : ℕ) (p : ℝ)
    (hB : 0 ≤ B) (hr : B ^ 2 ≤ 4 * r) (hp : p ≤ (B ^ 2) ^ e) :
    p ≤ (4 * r) ^ e :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.L2_threshold_vacuous_at_saddle
    B r e p hB hr hp

/-- **[A10, obstruction]** Equal L² data can have different products: the L²/Ramanujan datum does
not pin the norm. This is the formal spread-free-degree witness behind the route refutation. -/
theorem doorIV_A10_L2_does_not_pin_norm_export :
    (2 : ℝ) + 2 = 1 + 3 ∧ (2 : ℝ) * 2 ≠ 1 * 3 :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.L2_does_not_pin_norm

/-- **[A10, obstruction]** The exact n=16,r=3 spread interval is nondegenerate, so the archimedean
norm spread carries information absent from the L² datum. -/
theorem doorIV_A10_free_spread_nondegenerate_export : (256 : ℝ) < 20736 :=
  _root_.ArkLib.ProximityGap.Frontier.A10GrossKoblitzSize.free_spread_nondegenerate

#print axioms doorIV_A10_prod_le_mean_pow_card_export
#print axioms doorIV_A10_norm_sq_le_fourR_pow_export
#print axioms doorIV_A10_L2_base_le_house_base_export
#print axioms doorIV_A10_L2_threshold_vacuous_at_saddle_export
#print axioms doorIV_A10_L2_does_not_pin_norm_export
#print axioms doorIV_A10_free_spread_nondegenerate_export

/-! ## Door-II/Door-IV boundary phase-coherent resonator non-realizability exports.
Scope: **obstruction**.

These exports make the phase-aligned √q-completion resonator no-go permanent. The residual
`PhaseCoherentUniform` would force every nonzero Gauss period to attain the same completion-scale
saturation value; the exact Parseval second moment forbids this in the thin prize regime. This backs
the no-fifth-door tetrachotomy by closing a named completion-resonator residual, without proving any
new cancellation or CORE upper bound.
-/

/-- **[identity, ResonancePhaseCoherent]** The trivial frequency has `η₀ = |G|`. -/
theorem doorII_phaseCoherent_eta_zero_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) :
    _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G 0 = (G.card : ℂ) :=
  _root_.ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.eta_zero ψ G

/-- **[identity, ResonancePhaseCoherent]** The nonzero-frequency second moment is exactly
`q|G|-|G|²`, after removing the trivial frequency from Parseval. -/
theorem doorII_phaseCoherent_secondMoment_nonzero_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 :=
  _root_.ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.secondMoment_nonzero
    hψ G

/-- **[obstruction, ResonancePhaseCoherent]** In the prize regime `4d ≤ q-1`, the uniform
phase-coherent completion resonator is non-realizable: it would contradict the exact nonzero
Parseval mass. This closes the named phase-aligned √q-completion residual, not the CORE bound. -/
theorem doorII_not_phaseCoherentUniform_of_prizeRegime_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hregime : 4 * d ≤ Fintype.card F - 1) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.RES2Diagnostics.PhaseCoherentUniform ψ d :=
  _root_.ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.not_phaseCoherentUniform_of_prizeRegime
    hd hd0 hψ hregime

#print axioms doorII_phaseCoherent_eta_zero_export
#print axioms doorII_phaseCoherent_secondMoment_nonzero_export
#print axioms doorII_not_phaseCoherentUniform_of_prizeRegime_export

/-! ## Door-IV Lane 1 worst-frequency orbit multiplicity exports.
Scope: **quotient-count bookkeeping / obstruction**.

These exports record the exact coset-orbit consequence of eta invariance: a nonzero frequency above a
threshold contributes its whole multiplicative `G`-orbit above the same threshold. This is useful for
quotient probes of the worst-`b` set, but it gives no upper bound or anti-concentration by itself.
-/

/-- **[Lane 1, WorstBOrbitLowerBound]** Eta-norm threshold membership is closed under the
multiplicative `G`-orbit of a frequency. -/
theorem doorIV_worstB_frequency_orbit_subset_threshold_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F}
    (hbthr : thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖) :
    (G.image fun c => c * b) ⊆ Finset.univ.filter
      (fun y => thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G y‖) :=
  _root_.ProximityGap.Frontier.WorstBOrbitLowerBound.frequency_orbit_subset_threshold
    G hGnz hmulG thr hbthr

/-- **[Lane 1, WorstBOrbitLowerBound]** For nonzero `b`, the whole above-threshold orbit lies in
the non-principal frequency line. -/
theorem doorIV_worstB_frequency_orbit_subset_nonzero_threshold_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F} (hbne : b ≠ 0)
    (hbthr : thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖) :
    (G.image fun c => c * b) ⊆ Finset.univ.filter
      (fun y => y ≠ 0 ∧
        thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G y‖) :=
  _root_.ProximityGap.Frontier.WorstBOrbitLowerBound.frequency_orbit_subset_nonzero_threshold
    G hGnz hmulG thr hbne hbthr

/-- **[Lane 1, WorstBOrbitLowerBound]** A single nonzero above-threshold representative forces at
least `|G|` non-principal above-threshold frequencies. -/
theorem doorIV_worstB_card_nonzero_threshold_ge_card_of_mem_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F} (hbne : b ≠ 0)
    (hbthr : thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖) :
    G.card ≤ (Finset.univ.filter
      (fun y => y ≠ 0 ∧
        thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G y‖)).card :=
  _root_.ProximityGap.Frontier.WorstBOrbitLowerBound.card_nonzero_threshold_ge_card_of_mem
    G hGnz hmulG thr hbne hbthr

/-- **[Lane 1, WorstBOrbitLowerBound]** Contrapositive quotient-count certificate: fewer than
`|G|` non-principal threshold clearers rules out every nonzero threshold clearer. -/
theorem doorIV_worstB_not_exists_nonzero_threshold_of_card_lt_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ)
    (hcard : (Finset.univ.filter
      (fun y => y ≠ 0 ∧
        thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G y‖)).card <
        G.card) :
    ¬ ∃ b : F, b ≠ 0 ∧
      thr ≤ ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ :=
  _root_.ProximityGap.Frontier.WorstBOrbitLowerBound.not_exists_nonzero_threshold_of_card_lt
    G hGnz hmulG thr hcard

#print axioms doorIV_worstB_frequency_orbit_subset_threshold_export
#print axioms doorIV_worstB_frequency_orbit_subset_nonzero_threshold_export
#print axioms doorIV_worstB_card_nonzero_threshold_ge_card_of_mem_export
#print axioms doorIV_worstB_not_exists_nonzero_threshold_of_card_lt_export


/-! ## Door-IV Lane 3 phase-blind Jacobi/Thaine no-go exports.
Scope: **obstruction / reduction localization**.

These exports make Shaw's 31-paper mine verdict permanent: Thaine `d`-composition and
Hasse--Davenport lifting transport Jacobi-sum **moduli** exactly, while congruence/`p`-adic
Jacobi-sum data are invariant under archimedean unit phases. Both methods therefore leave the
signed off-diagonal phase-cancellation wall explicit instead of proving CORE.
-/

/-- **[Thaine d-composition, phase-blindness]** The squared modulus of a composed Jacobi datum is
exactly the product of the squared moduli. Thus the composition/lifting law transports absolute
values, not the archimedean phase cancellation needed for the door-(iv) off-diagonal wall. -/
theorem doorIV_thaine_jacobiCompose_normSq_eq_export
    (J₁ J₂ : _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData) :
    Complex.normSq
        (_root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.compose J₁ J₂).val =
      J₁.fieldSize * J₂.fieldSize :=
  _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.jacobiCompose_normSq_eq J₁ J₂

/-- **[Hasse--Davenport lift, phase-blindness]** The `(k+1)`-fold self-lift has squared modulus
`q^(k+1)` exactly. No cancellation is gained by lifting the Weil modulus data. -/
theorem doorIV_thaine_jacobiLift_normSq_eq_export
    (J : _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData) (k : ℕ) :
    Complex.normSq (_root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.lift J k).val =
      J.fieldSize ^ (k + 1) :=
  _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.jacobiLift_normSq_eq J k

/-- **[Thaine d-composition, obstruction]** The phase-blind moment estimate only rearranges to the
triangle/diagonal bound `C * nTerms * qPow`; the off-diagonal signed cancellation remains outside
the composition law. -/
theorem doorIV_thaine_phaseBlind_moment_bound_export
    {Ar nTerms qPow C : ℝ} (hC : 1 ≤ C) (hq : 0 ≤ qPow) (hn : 0 ≤ nTerms)
    (hblind : Ar ≤ nTerms * (qPow * C)) :
    Ar ≤ C * (nTerms * qPow) :=
  _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.phaseBlind_moment_bound hC hq hn hblind

/-- **[Thaine d-composition, prize-regime overshoot]** In the thin regime `q ≥ n`, the phase-blind
ratio `q^r/n^r` is at least `q/n` for every `r ≥ 1`, recording the multiplicative overshoot of the
modulus-only route. -/
theorem doorIV_thaine_composition_overshoot_export
    {q n : ℝ} (hn : 0 < n) (hqn : n ≤ q) {r : ℕ} (hr : 1 ≤ r) :
    q / n ≤ q ^ r / n ^ r :=
  _root_.ArkLib.ProximityGap.Frontier.ThaineDComposition.composition_overshoot hn hqn hr

/-- **[Jacobi congruence, phase-blindness]** A phase-blind `p`-adic/congruence readout gives the same
value to the two-piece aligned and cancelling configurations. Hence valuation/congruence data alone
cannot detect the archimedean cancellation needed for the energy face. -/
theorem doorIV_jacobiCongruence_phaseBlind_cannot_separate_export
    (v : (Fin 2 → ℂ) → ℝ) (ρ : ℝ)
    (hv : _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.PhaseBlind
      (Finset.univ : Finset (Fin 2)) v) :
    v (fun i => if i = 0 then (ρ : ℂ) else (-(ρ : ℂ))) = v (fun _ => (ρ : ℂ)) :=
  _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.phaseBlind_cannot_separate_cancel_from_aligned
    v ρ hv

/-- **[Jacobi congruence, full norm gap]** The same phase-blind value is compatible with
archimedean norm `0` and with the aligned norm `2ρ`; this is the precise obstruction to turning a
`p`-adic/congruence certificate into a CORE energy bound. -/
theorem doorIV_jacobiCongruence_full_norm_range_export
    (v : (Fin 2 → ℂ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.PhaseBlind
      (Finset.univ : Finset (Fin 2)) v) :
    ∃ Acancel Aaligned : Fin 2 → ℂ,
      v Acancel = v Aaligned ∧
      ‖∑ i, Acancel i‖ = 0 ∧
      ‖∑ i, Aaligned i‖ = 2 * ρ :=
  _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.phaseBlind_value_compatible_with_full_norm_range
    v ρ hρ hv

/-- **[Jacobi congruence, capstone]** The congruence/`p`-adic method is phase-blind on F2: every
phase-blind readout admits an aligned/cancel pair with identical value and maximal archimedean norm
separation. -/
theorem doorIV_jacobiCongruence_phaseBlindOnF2_export :
    _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.CongruenceMethodPhaseBlindOnF2 :=
  _root_.ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.congruenceMethodPhaseBlindOnF2_holds

#print axioms doorIV_thaine_jacobiCompose_normSq_eq_export
#print axioms doorIV_thaine_jacobiLift_normSq_eq_export
#print axioms doorIV_thaine_phaseBlind_moment_bound_export
#print axioms doorIV_thaine_composition_overshoot_export
#print axioms doorIV_jacobiCongruence_phaseBlind_cannot_separate_export
#print axioms doorIV_jacobiCongruence_full_norm_range_export
#print axioms doorIV_jacobiCongruence_phaseBlindOnF2_export


/-! ## Door-IV Lane 1 worst-b set coset-closure exports.

These exports pin the formal part of the worst-frequency arithmetic probe: the near-max set
`{b : thr ≤ ‖η_b‖}` is closed under every multiplicative dilation preserving the coset support `G`.
Thus the forced structure lives on multiplicative `μ_n`-cosets; the formal statement gives no CORE
upper bound and no additive anti-concentration, it only localizes what any Lane-1 attack must exploit
after quotienting by `μ_n`.
-/

/-- **[worst-b set, coset closure]** Membership in the threshold worst-frequency set is invariant
under every nonzero dilation `b ↦ c*b` whose multiplier preserves the support `G`. -/
theorem doorIV_worstBSet_mem_dilate_iff_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (thr : ℝ) (b : F) :
    c * b ∈ _root_.ProximityGap.Frontier.WorstBSetCosetClosed.worstSet ψ G thr ↔
      b ∈ _root_.ProximityGap.Frontier.WorstBSetCosetClosed.worstSet ψ G thr :=
  _root_.ProximityGap.Frontier.WorstBSetCosetClosed.mem_worstSet_dilate_iff G hc hcG thr b

/-- **[worst-b set, forward closure]** If `b` is above threshold, every support-preserving
`μ_n`-dilate of `b` is also above threshold. -/
theorem doorIV_worstBSet_dilate_mem_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F}
    (hb : b ∈ _root_.ProximityGap.Frontier.WorstBSetCosetClosed.worstSet ψ G thr) :
    c * b ∈ _root_.ProximityGap.Frontier.WorstBSetCosetClosed.worstSet ψ G thr :=
  _root_.ProximityGap.Frontier.WorstBSetCosetClosed.worstSet_dilate_mem G hc hcG thr hb

/-- **[worst-b maximizer orbit]** Every support-preserving `μ_n`-dilate has exactly the same
Fourier magnitude, so a maximizer is accompanied by its whole multiplicative coset orbit. -/
theorem doorIV_worstBSet_maximiser_orbit_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (b : F) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (c * b)‖ = ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ :=
  _root_.ProximityGap.Frontier.WorstBSetCosetClosed.maximiser_orbit G hc hcG b

#print axioms doorIV_worstBSet_mem_dilate_iff_export
#print axioms doorIV_worstBSet_dilate_mem_export
#print axioms doorIV_worstBSet_maximiser_orbit_export

/-- **[Lane 2/3 composition capstone, PerFrequencyLocalizationCollectiveOnly]** The worst-`b`
per-frequency decomposition `M = ρ · H` admits NO factor-2 thin-separation in either factor (and the
half-mass admits no factor-2 thick-separation either), under the probe-supplied thickness-comparability
hypotheses (coherence deficit `K = 118/100`, half-mass `K = 107/100`). Both per-`b` factors are
thickness-blind ⟹ by rule 3 neither is the thinness-essential CORE lever; the prize √-cancellation
content is COLLECTIVE-only (the BGK wall). Refuted-lever constraint capstone — NO CORE/cancellation/
completion/moment/anti-concentration/capacity claim. -/
theorem doorIV_no_perFrequency_factor_separates_export
    (D : _root_.ProximityGap.Frontier.DoorIVPerFrequencyLocalizationCollectiveOnly.WorstBDecomposition)
    (hcoh_thin_pos : 0 < D.coherenceDeficit.thin)
    (hcoh_bound : D.coherenceDeficit.thick ≤ (118 / 100 : ℝ) * D.coherenceDeficit.thin)
    (hhm_thin_pos : 0 < D.halfMass.thin) (hhm_thick_pos : 0 < D.halfMass.thick)
    (hhm_comp : D.halfMass.Comparable (107 / 100 : ℝ)) :
    (¬ D.coherenceDeficit.Factor2ThinSeparation) ∧
      (¬ D.halfMass.Factor2ThinSeparation) ∧
      (¬ D.halfMass.Factor2ThickSeparation) :=
  D.no_perFrequency_factor_separates hcoh_thin_pos hcoh_bound hhm_thin_pos hhm_thick_pos hhm_comp

/-- **[Lane 2/3 composition capstone, PerFrequencyLocalizationCollectiveOnly]** Slogan form: neither
per-frequency factor of `M = ρ · H` thin-separates (no per-`b` thin lever). -/
theorem doorIV_neither_factor_thin_separates_export
    (D : _root_.ProximityGap.Frontier.DoorIVPerFrequencyLocalizationCollectiveOnly.WorstBDecomposition)
    (hcoh_thin_pos : 0 < D.coherenceDeficit.thin)
    (hcoh_bound : D.coherenceDeficit.thick ≤ (118 / 100 : ℝ) * D.coherenceDeficit.thin)
    (hhm_thin_pos : 0 < D.halfMass.thin) (hhm_thick_pos : 0 < D.halfMass.thick)
    (hhm_comp : D.halfMass.Comparable (107 / 100 : ℝ)) :
    (¬ D.coherenceDeficit.Factor2ThinSeparation) ∧ (¬ D.halfMass.Factor2ThinSeparation) :=
  D.neither_factor_thin_separates hcoh_thin_pos hcoh_bound hhm_thin_pos hhm_thick_pos hhm_comp

#print axioms doorIV_no_perFrequency_factor_separates_export
#print axioms doorIV_neither_factor_thin_separates_export

/-- **[Lane 3 two-piece phase geometry obstruction, ComplexRayCoherence]** Any positive
two-piece Door-IV coherence saving below `1` is exactly a non-same-ray obligation: the normalized
two-piece norm coherence drops strictly below `1` iff the two vector pieces are not carried by the
same nonnegative real ray. This is a pure triangle-equality constraint, not a CORE/cancellation bound. -/
theorem doorIV_twoPieceNormCoherence_lt_one_iff_not_sameRay_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence x y < 1 ↔
      ¬ SameRay ℝ x y :=
  _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_lt_one_iff_not_sameRay hden

/-- **[Lane 3 finite-refinement phase geometry obstruction, ComplexRayCoherence]** A universal
positive epsilon-drop for finite Door-IV refinements is refuted by one member whose pieces all lie on
a common nonnegative ray. Subdivision alone supplies no anti-concentration unless it rules out this
common-ray geometry at the adversarial frequency. -/
theorem doorIV_not_family_multiPieceNormCoherence_le_one_sub_of_exists_common_ray_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ ι : Type*} (s : κ → Finset ι) (A : κ → ι → E) {ε : κ → ℝ}
    (hε : ∀ k, 0 < ε k)
    (hbad : ∃ k, ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ s k, A k i = c i • u) ∧
      (∀ i ∈ s k, 0 ≤ c i) ∧
      0 < (∑ i ∈ s k, c i) ∧ u ≠ 0) :
    ¬ ∀ k,
      _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence (s k) (A k) ≤
        1 - ε k :=
  _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.not_family_multiPieceNormCoherence_le_one_sub_of_exists_common_nonneg_ray
    s A hε hbad

#print axioms doorIV_twoPieceNormCoherence_lt_one_iff_not_sameRay_export
#print axioms doorIV_not_family_multiPieceNormCoherence_le_one_sub_of_exists_common_ray_export

/-- **[Lane 3 coset-half factorization obstruction, HalfMassFactorization]** At positive half-mass,
a strict coset-half coherence drop is exactly strict triangle slack in the half-mass envelope. The act
of splitting `A+B` supplies no saving unless the certificate proves `‖A+B‖ < ‖A‖+‖B‖` at the
adversarial frequency. -/
theorem doorIV_halfMass_coherence_lt_one_iff_norm_lt_halfMass_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (h : 0 < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence A B < 1 ↔
      ‖A + B‖ < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_lt_one_iff_norm_lt_halfMass h

/-- **[Lane 3 coset-half reciprocal-spend obstruction, HalfMassFactorization]** If a split has
coherence at most `rho > 0` while the original period norm has floor `T`, then the half-mass must pay
at least `T / rho`. A coherence drop alone only relocates the burden onto the `L¹` half-mass budget. -/
theorem doorIV_halfMass_ge_normFloor_div_of_coherence_le_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {T rho : ℝ}
    (h : 0 < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B)
    (hrho : 0 < rho)
    (hcoh : _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence A B ≤ rho)
    (hT : T ≤ ‖A + B‖) :
    T / rho ≤ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass_ge_normFloor_div_of_coherence_le
    h hrho hcoh hT

/-- **[Lane 3 coset-half single-instance product-budget obstruction, HalfMassFactorization]** If an
advertised coherence cap `rho` and half-mass cap `H` have product strictly below a known period floor
`T`, then that coherence cap is impossible under the half-mass cap. This is the local algebraic budget
gate behind the family version below. -/
theorem doorIV_not_coherence_le_of_normFloor_gt_product_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {T rho H : ℝ}
    (h : 0 < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B)
    (hrho0 : 0 ≤ rho)
    (hcohMass : _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B ≤ H)
    (hT : T ≤ ‖A + B‖) (hprod : rho * H < T) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence A B ≤ rho :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_coherence_le_of_normFloor_gt_product
    h hrho0 hcohMass hT hprod

/-- **[Lane 3 coset-half budget obstruction, HalfMassFactorization]** A family of advertised
coherence caps and half-mass caps is impossible if one member's half-mass budget lies below the forced
reciprocal floor `T_i / rho_i` coming from the period floor. Coherence savings must be paid for in
`L¹` half-mass unless an independent half-mass theorem is supplied. -/
theorem doorIV_not_family_coherence_and_halfMass_caps_of_exists_halfMass_floor_gt_export
    {E : Type*} [SeminormedAddCommGroup E] {ι : Type*} {A B : ι → E} {T rho H : ι → ℝ}
    (h : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass (A i) (B i))
    (hrho : ∀ i, 0 < rho i) (hT : ∀ i, T i ≤ ‖A i + B i‖)
    (hbad : ∃ i, H i < T i / rho i) :
    ¬ ∀ i,
      _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence (A i) (B i) ≤ rho i ∧
        _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass (A i) (B i) ≤ H i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_family_coherence_and_halfMass_caps_of_exists_halfMass_floor_gt
    h hrho hT hbad

/-- **[Lane 3 coset-half product-budget obstruction, HalfMassFactorization]** If a proposed
coherence cap and half-mass cap have product below the known period floor at even one indexed member,
the family of caps is impossible. This is the exact algebraic budget gate for coset-half Door-IV claims,
not a CORE/cancellation estimate. -/
theorem doorIV_not_family_coherence_and_halfMass_caps_of_exists_normFloor_gt_product_export
    {E : Type*} [SeminormedAddCommGroup E] {ι : Type*} {A B : ι → E} {T rho H : ι → ℝ}
    (h : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass (A i) (B i))
    (hrho0 : ∀ i, 0 ≤ rho i) (hT : ∀ i, T i ≤ ‖A i + B i‖)
    (hbad : ∃ i, rho i * H i < T i) :
    ¬ ∀ i,
      _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence (A i) (B i) ≤ rho i ∧
        _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass (A i) (B i) ≤ H i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_family_coherence_and_halfMass_caps_of_exists_normFloor_gt_product
    h hrho0 hT hbad

/-- **[Lane 3 coset-half zero-order budget obstruction, HalfMassFactorization]** Any period-norm
floor `T ≤ ‖A+B‖` is already a half-mass floor `T ≤ ‖A‖+‖B‖`, before any coherence cap is considered.
Thus a Door-IV split certificate cannot hide the original prize floor inside the split; the `L¹`
half-mass budget must cover the floor first. NO CORE / cancellation / capacity claim. -/
theorem doorIV_halfMass_normFloor_le_halfMass_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {T : ℝ}
    (hT : T ≤ ‖A + B‖) :
    T ≤ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.normFloor_le_halfMass_of_normFloor_le_norm
    hT

/-- **[Lane 3 coset-half zero-order budget obstruction, HalfMassFactorization]** If an advertised
half-mass cap `H` is below a known period floor `T`, the cap is impossible. Coherence bookkeeping is
irrelevant until the raw half-mass budget can already pay the observed period floor. NO CORE /
cancellation / capacity claim. -/
theorem doorIV_not_halfMass_le_of_normFloor_gt_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {T H : ℝ}
    (hT : T ≤ ‖A + B‖) (hH : H < T) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass A B ≤ H :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_halfMass_le_of_normFloor_gt
    hT hH

#print axioms doorIV_halfMass_coherence_lt_one_iff_norm_lt_halfMass_export
#print axioms doorIV_halfMass_ge_normFloor_div_of_coherence_le_export
#print axioms doorIV_not_coherence_le_of_normFloor_gt_product_export
#print axioms doorIV_not_family_coherence_and_halfMass_caps_of_exists_halfMass_floor_gt_export
#print axioms doorIV_not_family_coherence_and_halfMass_caps_of_exists_normFloor_gt_product_export
#print axioms doorIV_halfMass_normFloor_le_halfMass_export
#print axioms doorIV_not_halfMass_le_of_normFloor_gt_export
/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** The additive energy `E⁺(b • S)` of the
worst-`b` phase set `S_b = b • μ_n` is INVARIANT under the nonzero dilation `b`: `E⁺(b • S) = E⁺(S)`.
The worst frequency therefore cannot tune the additive (small-ball / Halász) structure of the phase
set; the additive-energy lever is `b`-blind. Lane-1 small-ball verdict backbone (kernel-checked).
NO CORE / cancellation / completion / moment-saving / capacity claim. -/
theorem doorIV_phaseSet_addEnergy_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] (S : Finset F) {b : F} (hb : b ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy
        (S.image (fun x => b * x)) =
      _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy S :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_smul_eq S hb

/-- **[Lane 1 phase-set sumset invariance]** Nonzero frequency dilation preserves additive-doubling
cardinality. A small-ball route based on `|bS+bS|` cannot distinguish the adversarial `b`; the worst
frequency only relabels the sumset. -/
theorem doorIV_phaseSet_addSumset_card_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] (S : Finset F) {b : F} (hb : b ≠ 0) :
    (_root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset
        (S.image (fun x => b * x))).card =
      (_root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset S).card :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_card_smul_eq S hb

/-- **[Lane 1 phase-set difference invariance]** Nonzero frequency dilation preserves the additive
difference-set cardinality. Pair-spacing support of `{b*x^m}` is `b`-blind, so it cannot identify a
worst-frequency anti-concentration selector. -/
theorem doorIV_phaseSet_addDiffset_card_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] (S : Finset F) {b : F} (hb : b ≠ 0) :
    (_root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset
        (S.image (fun x => b * x))).card =
      (_root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset S).card :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_card_smul_eq S hb

/-- **[Lane 1 phase-set pair-sum fiber invariance]** Every pair-sum multiplicity is preserved after
rescaling the target by the same nonzero frequency. This is the multiplicity-level form behind the
sumset small-ball no-go. -/
theorem doorIV_phaseSet_addPairSumCount_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (S : Finset F) {b t : F} (hb : b ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount
        (S.image (fun x => b * x)) (b * t) =
      _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount S t :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount_smul_eq S hb

/-- **[Lane 1 phase-set pair-difference fiber invariance]** Every pair-difference multiplicity is
preserved after rescaling the target by the same nonzero frequency. Difference-fiber small-ball data
of `{b*x^m}` is also `b`-blind. -/
theorem doorIV_phaseSet_addPairDiffCount_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (S : Finset F) {b t : F} (hb : b ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairDiffCount
        (S.image (fun x => b * x)) (b * t) =
      _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairDiffCount S t :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairDiffCount_smul_eq S hb

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** No strict scalar improvement for an
additive-energy small-ball bound: if one nonzero frequency dilate exceeds a proposed threshold `C`,
NO other nonzero dilate can satisfy `E⁺ ≤ C`. An additive-energy/Halász lever cannot become a
worst-frequency anti-concentration theorem by optimizing over `b` — the scalar only relabels the
phase set. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_no_phaseSet_addEnergy_scalar_improvement_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy
        (S.image (fun x => b₁ * x))) :
    ¬ _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy
        (S.image (fun x => b₂ * x)) ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addEnergy_scalar_improvement
    S hb₁ hb₂ hbad

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** The strongest dilation-invariance no-go: even
the target-optimized multi-dimensional small-ball maximum (max over vector targets of the joint
linear-system fiber, i.e. the actual Halász/Littlewood-Offord small-ball use case where the target is
chosen adversarially after the linear system `A` is fixed) admits NO scalar improvement. Any
linear-pattern small-ball lever over the dilated phase set is `b`-blind. This is the kernel-checked
statement that closes the brief's Lane-1 "non-moment small-ball anti-concentration over the worst-`b`
phase set" hope: every such statistic is dilation-invariant, so the worst `b` cannot be the lever.
NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_no_phaseSet_systemSmallBall_scalar_improvement_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternMaxFiber
        (S.image (fun x => b₁ * x)) A) :
    ¬ _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternMaxFiber
        (S.image (fun x => b₂ * x)) A ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addSystemPatternMaxFiber_scalar_improvement
    S A hb₁ hb₂ hbad

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** Every finite-order additive energy
`E_k(b • S)` is invariant under nonzero frequency dilation. Thus the "go higher-order" escape from
ordinary `E⁺` small-ball bounds is still `b`-blind at every fixed order: the adversarial worst
frequency cannot tune any finite-order balanced-sum energy of the phase set. NO CORE / cancellation /
completion / moment-saving / capacity claim. -/
theorem doorIV_phaseSet_addEnergyK_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (S : Finset F) {b : F} (hb : b ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK (k := k)
        (S.image (fun x => b * x)) =
      _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK (k := k) S :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK_smul_eq (k := k) S hb

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** No strict scalar improvement for any
finite-order additive-energy / Gowers / higher-Halász bound. If one nonzero frequency dilate exceeds
a proposed `E_k ≤ C` threshold, then every other nonzero dilate has the same `E_k` and cannot satisfy
that threshold. Optimizing over the worst `b` cannot convert finite-order additive energy into a
new door-(iv) anti-concentration theorem. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_no_phaseSet_addEnergyK_scalar_improvement_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK (k := k)
        (S.image (fun x => b₁ * x))) :
    ¬ _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK (k := k)
        (S.image (fun x => b₂ * x)) ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addEnergyK_scalar_improvement
    (k := k) S hb₁ hb₂ hbad

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** The higher-order `k`-sum max-fiber
small-ball statistic is invariant under nonzero frequency dilation. Maximizing over the target does
not recover dependence on the adversarial scalar `b`; dilation only relabels which target realizes the
maximal fiber. NO CORE / cancellation / completion / moment-saving / capacity claim. -/
theorem doorIV_phaseSet_addKSumMaxFiber_dilation_invariant_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (S : Finset F) {b : F} (hb : b ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber (k := k)
        (S.image (fun x => b * x)) =
      _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber (k := k) S :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber_smul_eq (k := k) S hb

/-- **[Lane 1/3 constraint, PhaseSetDilationInvariant]** No strict scalar improvement for the
higher-order `k`-sum max-fiber small-ball bound. If one nonzero dilate violates `max_t #{Σv_i=t} ≤ C`,
then every other nonzero dilate violates the same threshold. The usual target-optimized
Littlewood-Offord/Halász statistic cannot become a worst-`b` anti-concentration lever. NO CORE /
cancellation / completion / capacity claim. -/
theorem doorIV_no_phaseSet_addKSumMaxFiber_scalar_improvement_export
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber (k := k)
        (S.image (fun x => b₁ * x))) :
    ¬ _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber (k := k)
        (S.image (fun x => b₂ * x)) ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addKSumMaxFiber_scalar_improvement
    (k := k) S hb₁ hb₂ hbad

#print axioms doorIV_phaseSet_addEnergy_dilation_invariant_export
#print axioms doorIV_phaseSet_addSumset_card_dilation_invariant_export
#print axioms doorIV_phaseSet_addDiffset_card_dilation_invariant_export
#print axioms doorIV_phaseSet_addPairSumCount_dilation_invariant_export
#print axioms doorIV_phaseSet_addPairDiffCount_dilation_invariant_export
#print axioms doorIV_no_phaseSet_addEnergy_scalar_improvement_export
#print axioms doorIV_no_phaseSet_systemSmallBall_scalar_improvement_export
#print axioms doorIV_phaseSet_addEnergyK_dilation_invariant_export
#print axioms doorIV_no_phaseSet_addEnergyK_scalar_improvement_export
#print axioms doorIV_phaseSet_addKSumMaxFiber_dilation_invariant_export
#print axioms doorIV_no_phaseSet_addKSumMaxFiber_scalar_improvement_export

/-- **[Lane 1/3 constraint, WorstIndexDelocalized]** Packaged worst-frequency no-selector: a
prime-independently DELOCALIZED worst-index family (realizing two distinct residues mod `d` AND two
distinct values, as the cross-prime probe measures) is excluded by EVERY fixed-residue rule and EVERY
fixed-position rule simultaneously. The adversarial frequency offers no prime-stable arithmetic target
for a TARGETED (non-energy, non-sum-product) anti-concentration bound. NO CORE / cancellation /
completion / capacity claim. -/
theorem doorIV_worstIndex_delocalized_excludes_fixed_selector_export
    {P : Type*} (J : P → ℕ) (d : ℕ)
    (h : _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.IndexDelocalized J d) :
    (∀ r, ¬ _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.FixedResidueRule J d r) ∧
      (∀ c, ¬ _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.FixedPositionRule J c) :=
  _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.delocalized_excludes_fixed_selector J d h

/-- **[Lane 1/3 constraint, WorstIndexDelocalized]** Residue spread alone kills a pinned index: if the
worst-index family realizes two distinct residues mod `d` across primes, NO fixed-position selector can
fit it (without needing a separate raw-value witness). NO CORE / cancellation / completion / capacity
claim. -/
theorem doorIV_worstIndex_residueSpread_excludes_fixedPosition_export
    {P : Type*} (J : P → ℕ) (d : ℕ) (h : ∃ p₁ p₂, J p₁ % d ≠ J p₂ % d) :
    ∀ c, ¬ _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.FixedPositionRule J c :=
  _root_.ProximityGap.Frontier.DoorIVWorstIndexDelocalized.residue_delocalized_excludes_fixedPosition
    J d h

#print axioms doorIV_worstIndex_delocalized_excludes_fixed_selector_export
#print axioms doorIV_worstIndex_residueSpread_excludes_fixedPosition_export

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** A transfer ratio below `1`
from the level-`n` worst frequency to the true level-`n/2` sub-maximum is exactly a positive missed-
subargmax gap. High percentile behavior is not argmax identity. -/
theorem doorIV_worstB_ratio_lt_one_iff_witness_gap_pos_export
    {ι : Type*} {subMag : ι → ℝ} {b c : ι} (hpos : 0 < subMag c) :
    subMag b / subMag c < 1 ↔ 0 < subMag c - subMag b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.ratio_lt_one_iff_witness_gap_pos hpos

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** If the observed transfer
ratio is bounded by some explicit `r < 1`, then the level-`n` worst frequency is not a level-`n/2`
sub-maximizer. This is the formal obstruction behind the full-scan worst-b nesting probes. -/
theorem doorIV_worstB_not_isSubMaximizer_of_ratio_le_lt_one_export
    {ι : Type*} {subMag : ι → ℝ} {b c : ι} {r : ℝ}
    (hpos : 0 < subMag c) (hratio : subMag b / subMag c ≤ r) (hr : r < 1) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.IsSubMaximizer subMag b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.not_isSubMaximizer_of_ratio_le_lt_one
    hpos hratio hr

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** Non-maximality is exactly
the existence of a positive raw gap. A recursive-ascent certificate must rule out every such witness,
not merely show that the level-`n` worst frequency has high percentile rank at level `n/2`. -/
theorem doorIV_worstB_not_isSubMaximizer_iff_exists_gap_pos_export
    {ι : Type*} {subMag : ι → ℝ} {b : ι} :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.IsSubMaximizer subMag b ↔
      ∃ c, 0 < subMag c - subMag b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.not_isSubMaximizer_iff_exists_gap_pos

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** The quantitative transfer
ratio certificate `subMag b / subMag c ≤ r` is exactly the missed-gap certificate
`(1-r)M₂ ≤ M₂-a*`. This preserves the full scale of the non-nesting obstruction. -/
theorem doorIV_worstB_ratio_le_iff_witness_gap_ge_export
    {ι : Type*} {subMag : ι → ℝ} {b c : ι} {r : ℝ} (hpos : 0 < subMag c) :
    subMag b / subMag c ≤ r ↔ (1 - r) * subMag c ≤ subMag c - subMag b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.ratio_le_iff_witness_gap_ge hpos

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** A claimed nested
sub-maximizer with positive magnitude is equivalent to bounding every thinner-frequency ratio by
`1`; high percentile evidence is insufficient unless all ratio spikes above one are ruled out. -/
theorem doorIV_worstB_isSubMaximizer_iff_forall_ratio_le_one_export
    {ι : Type*} {subMag : ι → ℝ} {b : ι} (hpos : 0 < subMag b) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.IsSubMaximizer subMag b ↔
      ∀ c, subMag c / subMag b ≤ 1 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.isSubMaximizer_iff_forall_ratio_le_one hpos

/-- **[Lane 1/3 worst-b recursive-ascent obstruction, WorstBNonNested]** Non-nesting is equivalently
a ratio spike above one at the thinner level. This is the reciprocal audit hook for any proposed
recursive-ascent proof: one explicit spike refutes nesting. -/
theorem doorIV_worstB_not_isSubMaximizer_iff_exists_ratio_gt_one_export
    {ι : Type*} {subMag : ι → ℝ} {b : ι} (hpos : 0 < subMag b) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.IsSubMaximizer subMag b ↔
      ∃ c, 1 < subMag c / subMag b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.not_isSubMaximizer_iff_exists_ratio_gt_one hpos

#print axioms doorIV_worstB_ratio_lt_one_iff_witness_gap_pos_export
#print axioms doorIV_worstB_not_isSubMaximizer_of_ratio_le_lt_one_export
#print axioms doorIV_worstB_not_isSubMaximizer_iff_exists_gap_pos_export
#print axioms doorIV_worstB_ratio_le_iff_witness_gap_ge_export
#print axioms doorIV_worstB_isSubMaximizer_iff_forall_ratio_le_one_export
#print axioms doorIV_worstB_not_isSubMaximizer_iff_exists_ratio_gt_one_export

/-- **[Lane 3 b-side constraint, AttackB1 BadSetCosetNonSidon]** The worst-frequency BAD set
`{b : |η_b| large}` is a union of negation-symmetric multiplicative `μ_n`-cosets (n even ⟹ `-1 ∈ μ_n`),
so it contains an antipodal 4-pattern `{a,-a,c,-c}` (`a ≠ ±c`) and is therefore NOT a Sidon set: the
additive coincidence `a+(-a)=0=c+(-c)` has no trivial resolution. Hence a b-SIDE additive (Sidon /
Littlewood-Offord-on-frequencies) anti-concentration lever cannot grip the bad set — it carries forced
additive structure. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_badSet_antipodal_not_sidon_export
    {G : Type*} [AddCommGroup G] (S : Set G) (a c : G)
    (ha : a ∈ S) (hna : -a ∈ S) (hc : c ∈ S) (hnc : -c ∈ S)
    (hac : a ≠ c) (hanc : a ≠ -c) :
    ¬ _root_.AtkB1.IsSidonSet S :=
  _root_.AtkB1.not_sidon_of_antipodal_quad S a c ha hna hc hnc hac hanc

/-- **[Lane 3 b-side constraint, AttackB1 BadSetCosetNonSidon]** Packaged coset form: any set carrying
TWO genuinely-distinct negation-symmetric pairs `{a,-a}`, `{c,-c}` (`a ≠ ±c`) — exactly the structure of
a single multiplicative coset `b·μ_n` with `n ≥ 4` — is non-Sidon. The bad set's coset structure forces
additive energy strictly above the Sidon baseline, so no b-side small-ball/Sidon lever is available.
NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_coset_two_antipodal_pairs_not_sidon_export
    {G : Type*} [AddCommGroup G] (S : Set G) (a c : G)
    (hpair_a : a ∈ S ∧ -a ∈ S) (hpair_c : c ∈ S ∧ -c ∈ S)
    (hdiff : a ≠ c ∧ a ≠ -c) :
    ¬ _root_.AtkB1.IsSidonSet S :=
  _root_.AtkB1.coset_with_two_antipodal_pairs_not_sidon S a c hpair_a hpair_c hdiff

#print axioms doorIV_badSet_antipodal_not_sidon_export
#print axioms doorIV_coset_two_antipodal_pairs_not_sidon_export

/-- **[Lane 1 constraint, AntiConcKurtosisRefuted]** The anti-concentration DISPROOF of Paley is itself
refuted by the sub-Gaussian 4th moment of the period family. The exact additive energy is
`E₂(μ_n) = 3n² - 3n < 3n²` (n even), so the kurtosis `E₂/n² = 3 - 3/n` is strictly BELOW the Gaussian
(Wick) ceiling `3` with deficit exactly `3n`. A Paley-Zygmund / 4th-moment lower bound can therefore
certify at most `M_cert² ≲ 3·μ₂ = Θ(n)`, i.e. `M_cert = O(√n)`, short of the prize target `√(n log p)`
by a `√(log p)` factor: NO kurtosis-based disproof of CORE exists. This CLOSES an attack vector
(disproof route), not CORE itself. NO CORE upper-bound / cancellation / completion / capacity claim. -/
theorem doorIV_no_kurtosis_disproof_export (n : ℕ) (hn : 1 ≤ n) :
    _root_.ProximityGap.Frontier.AntiConcKurtosisRefuted.E2 n < 3 * n ^ 2 ∧
      3 * n ^ 2 - _root_.ProximityGap.Frontier.AntiConcKurtosisRefuted.E2 n = 3 * n :=
  _root_.ProximityGap.Frontier.AntiConcKurtosisRefuted.no_kurtosis_disproof n hn

#print axioms doorIV_no_kurtosis_disproof_export

/-- **[Lane 1/3 constraint, DoorIVNegationSymmetryRealAndBalanced]** A SECOND b-blindness mechanism,
distinct from the dilation-invariance meta-theorem: because the phase set at the worst `b` is
conjugation-closed, the period is real and `η(-b) = conj(η(b)) = η(b)`, so the paired frequencies
`b, -b` carry the IDENTICAL signed complex value. Hence ANY frequency selector that reads the signed
period value (threshold, sign test, half-plane gate, arbitrary predicate `P`) is exactly `±b`-blind —
covering value-selectors outside the reach of the additive-linear dilation-invariance no-go. NO CORE /
cancellation / completion / anti-concentration / capacity claim. -/
theorem doorIV_signed_value_selector_pm_b_blind_export
    {ι : Type*} (η : ι → ℂ) (P : ℂ → Prop) (b nb : ι)
    (hreal : (starRingEnd ℂ) (η b) = η b) (hneg : η nb = (starRingEnd ℂ) (η b)) :
    P (η nb) ↔ P (η b) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVNegationSymmetryRealAndBalanced.signed_value_selector_invariant
    η P b nb hreal hneg

/-- **[Lane 1/3 constraint, DoorIVNegationSymmetryRealAndBalanced]** Conjugation-closed phase-set form:
any predicate on the signed period sum is `±b`-invariant given the standard negation relation
`η(-b) = conj(η(b))`. The signed-value gate cannot distinguish the paired frequencies. NO CORE /
cancellation / completion / capacity claim. -/
theorem doorIV_signed_value_selector_pm_b_blind_of_conjClosed_export
    {ι : Type*} (S : ι → Finset ℂ) (P : ℂ → Prop) (b nb : ι)
    (hS : _root_.ArkLib.ProximityGap.Frontier.DoorIVNegationSymmetryRealAndBalanced.ConjClosed (S b))
    (hneg : (∑ z ∈ S nb, z) = (starRingEnd ℂ) (∑ z ∈ S b, z)) :
    P (∑ z ∈ S nb, z) ↔ P (∑ z ∈ S b, z) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVNegationSymmetryRealAndBalanced.signed_value_selector_invariant_of_conjClosed
    S P b nb hS hneg

#print axioms doorIV_signed_value_selector_pm_b_blind_export
#print axioms doorIV_signed_value_selector_pm_b_blind_of_conjClosed_export

/-- **[Lane 1 constraint, DoorIVLargestGapEnergyBlind]** The longest-empty-arc / largest-gap small-ball
functional (the NON-energy small-ball quantity — max single-residue gap / longest empty arc) yields only
the TRIVIAL linear ceiling `‖∑ z_j‖ ≤ n` for unit-modulus terms: an empty arc has no inside mass, so the
cardinality split right-hand side is exactly `n`, blind to the gap size. Hence the largest-gap statistic
cannot supply any √-cancellation — a door-(iv) bound must prove coherence/cancellation among the
surviving terms, not merely exhibit a hole. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_largestGap_yields_only_trivial_ceiling_export
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, ‖z j‖ = 1) (S : Finset (Fin n)) (hS : S = ∅) :
    ‖∑ j, z j‖ ≤ (n : ℝ) :=
  _root_.ProximityGap.Frontier.DoorIVLargestGapEnergyBlind.largestGap_yields_only_trivial_ceiling
    z hz S hS

/-- **[Lane 1 constraint, DoorIVLargestGapEnergyBlind]** Strict-budget obstruction: no largest-empty-arc
split certificate can fit below a strict budget `B < n` (the split RHS is exactly `n`). A √-scale
door-(iv) bound cannot come from the empty-arc statistic alone. NO CORE / cancellation / completion /
capacity claim. -/
theorem doorIV_no_emptyArc_split_rhs_le_strict_budget_export
    {n : ℕ} (S : Finset (Fin n)) (hS : S = ∅) {B : ℝ} (hB : B < (n : ℝ)) :
    ¬ (S.card : ℝ) + ((Sᶜ).card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVLargestGapEnergyBlind.no_emptyArc_split_rhs_le_strict_budget
    S hS hB

#print axioms doorIV_largestGap_yields_only_trivial_ceiling_export
#print axioms doorIV_no_emptyArc_split_rhs_le_strict_budget_export

/-- **[Lane 3 refuted-lever constraint, DyadicSelectorWalled — Shaw's Lever A]** Dyadic-tower coherence
refutation: no FIXED dyadic-rung selector can explain the worst frequency, because two observed worst-`b`
samples on different 2-adic rungs `v₂(dlog_g b*)` already contradict any single-rung rule. The adversarial
frequency does NOT live on a fixed dyadic subtower. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_no_fixedDyadicRungRule_of_two_rungs_export
    {α : Type*} {a : ℕ} (S : Finset α) (rung : α → Fin a) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : rung x ≠ rung y) :
    ¬ ∃ j : Fin a,
      _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.FixedRungRule S rung j :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.no_fixedRungRule_of_two_rungs
    S rung hx hy hxy

/-- **[Lane 3 refuted-lever constraint, DyadicSelectorWalled — Shaw's Lever A]** A genuine fixed-subtower
selection (`hist j = total`) is FORCED to be a visible scaled-Haar-excess histogram spike (given honest
probe thresholds): it cannot hide inside Haar-null noise. Hence the verified no-spike sweep rules out the
dyadic-tower coherence lever — it must exhibit an actual spike that the probe did not find. NO CORE /
cancellation / completion / capacity claim. -/
theorem doorIV_fixedDyadicRung_full_mass_forces_spike_export
    {a : ℕ} (hist : Fin a → ℕ) {total spikeNum spikeDen massNum massDen : ℕ} {j : Fin a}
    (hfull : hist j = total) (hpos : 0 < total)
    (hthreshold : spikeNum < spikeDen * 2 ^ (j.val + 1)) (hmass : massNum ≤ massDen) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.FixedRungSpike
      hist total spikeNum spikeDen massNum massDen j :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.fixedRung_full_mass_forces_spike
    hist hfull hpos hthreshold hmass

#print axioms doorIV_no_fixedDyadicRungRule_of_two_rungs_export
#print axioms doorIV_fixedDyadicRung_full_mass_forces_spike_export

/-- **[Lane 3 refuted-lever constraint, AvN4 PadicMahlerSupplyGap — Shaw's Lever C]** Bad-prime / p-adic
Mahler refutation: at every prize scale `μ ≥ 4`, the binomial supply crosses `p` already at constant
weight `7` (`prizePrime μ ≤ supply (2^μ) 7`), so non-balanced vanishing relations exist at constant
weight and Lam-Leung rigidity is overrun there; YET the moment saddle depth `8μ` is `> 7` and grows
without bound. Hence there is NO `μ`-uniform weight threshold below the saddle at which rigidity could
suppress the wraparound — the p-adic / Mahler angle REDUCES to the generic BGK moment wall. NO CORE /
cancellation / completion / capacity claim. -/
theorem doorIV_padic_mahler_no_leverage_export {μ : ℕ} (hμ : 4 ≤ μ) :
    _root_.ArkLib.ProximityGap.Frontier.AvN4.prizePrime μ ≤
        _root_.ArkLib.ProximityGap.Frontier.AvN4.supply (2 ^ μ) 7 ∧
      7 < _root_.ArkLib.ProximityGap.Frontier.AvN4.saddleDepth μ :=
  _root_.ArkLib.ProximityGap.Frontier.AvN4.padic_mahler_no_leverage hμ

/-- **[Lane 3 refuted-lever constraint, AvN4 PadicMahlerSupplyGap — Shaw's Lever C]** The moment saddle
depth is UNBOUNDED in the scale: for every `N` there is a scale `μ` with `N < saddleDepth μ`. This is the
load-bearing fact that the constant-weight rigidity band can never reach the `Θ(μ)`-deep saddle the
moment/di-Benedetto route requires. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_mahler_saddleDepth_unbounded_export (N : ℕ) :
    ∃ μ, N < _root_.ArkLib.ProximityGap.Frontier.AvN4.saddleDepth μ :=
  _root_.ArkLib.ProximityGap.Frontier.AvN4.saddleDepth_unbounded N

#print axioms doorIV_padic_mahler_no_leverage_export
#print axioms doorIV_mahler_saddleDepth_unbounded_export

/-- **[Lane 3 refuted-lever constraint, QVCauchySchwarzCircular — Shaw's Lever B]** Additive-energy /
quadratic-variation circularity: the Cauchy-Schwarz + proven-QV (Freedman) combination on the
log-ratio tower `Mtow` only RECOVERS the trivial ceiling `log(Mtow a) - log(Mtow 0) ≤ a·log 2`. It is the
LARGEST value consistent with the QV inequality `S² ≤ a·log2·S` at `S ≥ 0`, so the QV lever does not
distinguish the prize from the trivial ceiling. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_qv_route_recovers_trivial_ceiling_export
    (Mtow : ℕ → ℝ) (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i) (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) :
    Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
  _root_.ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular.qv_route_recovers_trivial_ceiling
    Mtow a hpos hdouble hmono

/-- **[Lane 3 refuted-lever constraint, QVCauchySchwarzCircular — Shaw's Lever B]** No sublinear drift
from the QV route: any drift bound strictly below the trivial ceiling, `R < a·log 2`, is NOT a
consequence of the Cauchy-Schwarz + QV combination (which is satisfied by the full ceiling `a·log 2`).
The Freedman QV lever alone cannot force the sublinear excess `O(log a)` the prize requires; an
independent mean-drift control is necessary. NO CORE / cancellation / completion / capacity claim. -/
theorem doorIV_qv_route_no_sublinear_saving_export (a : ℕ) (R : ℝ)
    (hR : R < (a : ℝ) * Real.log 2) :
    ¬ ((a : ℝ) * Real.log 2 ≤ R) :=
  _root_.ProximityGap.Frontier.DoorIVQVCauchySchwarzCircular.qv_route_no_sublinear_saving a R hR

#print axioms doorIV_qv_route_recovers_trivial_ceiling_export
#print axioms doorIV_qv_route_no_sublinear_saving_export


/-- **[Lane 3 refuted-lever capstone, DoorIVMartingaleInputCeilingCapstone]** The bounded-increment
martingale input and the predictable-QV input converge to the IDENTICAL trivial tower ceiling
`S_a ≤ a·log 2`; any target `R < a·log 2` is therefore outside what these inputs certify. The strict
separation from the prize drift `a·log2/2` is exactly another `a·log2/2`. This is a citable wrapper for
the martingale/Azuma/Freedman dead lever: no CORE / cancellation / completion / moment / capacity
claim; a genuinely new mean-drift law is still required. -/
theorem doorIV_martingale_inputs_all_trivial_ceiling_export
    (Mtow : ℕ → ℝ) (a : ℕ) (R : ℝ)
    (hpos : ∀ i, 0 < Mtow i) (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i)
    (hmono : ∀ i, Mtow i ≤ Mtow (i + 1)) (ha : 1 ≤ a)
    (hR : R < (a : ℝ) * Real.log 2) :
    (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) ∧
    (Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2) ∧
    (¬ ((a : ℝ) * Real.log 2 ≤ R)) ∧
    ((a : ℝ) * (Real.log 2 / 2) < (a : ℝ) * Real.log 2) ∧
    ((a : ℝ) * Real.log 2 - (a : ℝ) * (Real.log 2 / 2) =
      (a : ℝ) * (Real.log 2 / 2)) :=
  ⟨(_root_.ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone.martingale_inputs_same_ceiling
      Mtow a hpos hdouble hmono).1,
   (_root_.ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone.martingale_inputs_same_ceiling
      Mtow a hpos hdouble hmono).2,
   _root_.ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone.no_martingale_input_reaches_sublinear
      a R hR,
   _root_.ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone.prize_ceiling_strictly_below_martingale_ceiling
      a ha,
   _root_.ProximityGap.Frontier.DoorIVMartingaleInputCeilingCapstone.martingale_minus_prize_ceiling_eq
      a⟩

#print axioms doorIV_martingale_inputs_all_trivial_ceiling_export


/-- **[Lane 1 worst-b coset-index arithmetic obstruction]** A top-three worst-coset-index witness
with consecutive-gap gcd `1` cannot be contained in any proper arithmetic progression / sublattice
`r₀ + dℤ` with `d ≥ 2`. Thus the observed worst-`b` coset-index set cannot be thinned by an AP or
proper residue-class selector. This is only a class-restriction no-go, not a CORE bound. -/
theorem doorIV_worstCosetIndex_no_proper_progression_export
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ d r₀ : ℤ, 2 ≤ d →
      ¬ (d ∣ (t₀ - r₀) ∧ d ∣ (t₁ - r₀) ∧ d ∣ (t₂ - r₀)) :=
  _root_.ProximityGap.Frontier.DoorIVWorstCosetIndex.no_proper_progression_of_consecutive_gap_gcd_one
    hgcd

/-- **[Lane 1 worst-b coset-index arithmetic obstruction]** The same gap-gcd witness forbids putting
three worst-coset indices in one residue class modulo any proper modulus `d ≥ 2`. This is the exact
formal interface for the probe verdict that there is no fixed mod-`d` class selecting the adversarial
worst frequencies. No CORE / cancellation / completion / capacity claim. -/
theorem doorIV_worstCosetIndex_no_common_residue_mod_export
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ d r : ℤ, 2 ≤ d → ¬ (t₀ % d = r ∧ t₁ % d = r ∧ t₂ % d = r) :=
  _root_.ProximityGap.Frontier.DoorIVWorstCosetIndex.no_common_residue_mod_of_consecutive_gap_gcd_one
    hgcd

/-- **[Lane 1 worst-b coset-index arithmetic obstruction]** Parity/2-adic specialization: a
consecutive-gap-gcd-one witness cannot have all three top indices in a common parity progression.
So the worst-`b` set is not trapped in the even sublattice or a fixed parity class. No CORE claim. -/
theorem doorIV_worstCosetIndex_not_parity_restricted_export
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ r₀ : ℤ, ¬ ((2 : ℤ) ∣ (t₀ - r₀) ∧ (2 : ℤ) ∣ (t₁ - r₀) ∧ (2 : ℤ) ∣ (t₂ - r₀)) :=
  _root_.ProximityGap.Frontier.DoorIVWorstCosetIndex.worst_index_not_parity_restricted hgcd

#print axioms doorIV_worstCosetIndex_no_proper_progression_export
#print axioms doorIV_worstCosetIndex_no_common_residue_mod_export
#print axioms doorIV_worstCosetIndex_not_parity_restricted_export


/-- **[Lane 1 worst-b coset-index multiplicative genericity]** If an observed worst-index set
contains two elements whose ratio lies outside a subgroup `H`, then the set is not contained in any
single left coset of `H`. This is the generic multiplicative class-restriction obstruction. -/
theorem doorIV_worstIndexMult_not_subset_coset_export
    {G : Type*} [Group G] {H : Subgroup G} {s : Set G} {a b : G}
    (ha : a ∈ s) (hb : b ∈ s) (hne : b⁻¹ * a ∉ H) :
    ∀ g : G, ¬ (∀ x ∈ s,
      _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.inCoset H g x) :=
  _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_subset_coset_of_ratio_not_mem
    ha hb hne

/-- **[Lane 1 worst-b coset-index multiplicative genericity]** Quadratic-residue specialization:
a finite observed worst-index set containing one pair with non-square ratio is not confined to a
single square-coset. Thus QR/non-QR coexistence kills the multiplicative QR selector. -/
theorem doorIV_worstIndexMult_not_finset_power_coset_restricted_export
    {A : Type*} [CommGroup A] {s : Finset A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s)
    (hns : b⁻¹ * a ∉ _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.squares A) :
    ∀ g : A, ¬ (∀ x ∈ s,
      _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.inCoset
        (_root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.squares A) g x) :=
  _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_finset_power_coset_restricted
    ha hb hns

/-- **[Lane 1 worst-b coset-index multiplicative genericity]** General `k`-th-power specialization:
one pair ratio outside the `k`-th-power subgroup prevents the finite worst-index set from lying in any
single `k`-power coset. No CORE / cancellation / completion / capacity claim. -/
theorem doorIV_worstIndexMult_not_finset_kth_power_coset_restricted_export
    {A : Type*} [CommGroup A] {k : ℕ} {s : Finset A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s)
    (hnp : b⁻¹ * a ∉ _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.kthPowers A k) :
    ∀ g : A, ¬ (∀ x ∈ s,
      _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.inCoset
        (_root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.kthPowers A k) g x) :=
  _root_.ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_finset_kth_power_coset_restricted
    ha hb hnp

#print axioms doorIV_worstIndexMult_not_subset_coset_export
#print axioms doorIV_worstIndexMult_not_finset_power_coset_restricted_export
#print axioms doorIV_worstIndexMult_not_finset_kth_power_coset_restricted_export


/-- **[Lane 1/3 two-dilate coupling obstruction]** The half-period dilation sum at any frequency is
bounded by twice the marginal sub-period maximum. This is the exact perfect-co-peak ceiling, not a
CORE upper bound. -/
theorem doorIV_twoDilate_le_two_mul_max_export
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax : ℝ} {b : ι}
    (h1 : s b ≤ Smax) (h2 : s (σ b) ≤ Smax) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate s σ b ≤
      2 * Smax :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate_le_two_mul_max
    h1 h2

/-- **[Lane 1/3 two-dilate coupling obstruction]** A strict factor `c < 2` below the marginal envelope
is precisely a no-co-peak certificate: the two shifted halves cannot both sit at the marginal maximum.
This packages the probe verdict that the dilation coupling gives no recursive co-peaking gain. -/
theorem doorIV_twoDilate_no_copeak_recursion_export
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hbound : _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate s σ b ≤
      c * Smax)
    (hb : s b = Smax) :
    s (σ b) < Smax :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.no_copeak_recursion
    hc hSmax hbound hb

/-- **[Lane 1/3 two-dilate coupling obstruction]** The no-co-peak certificate is symmetric: if the
shifted half reaches the marginal maximum under the same strict `c < 2` envelope, the base half must
be strictly below the maximum.  The observed worst-`b` shape cannot hide a perfect joint extreme by
swapping the two dilates. -/
theorem doorIV_twoDilate_no_copeak_recursion_left_export
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hbound : _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate s σ b ≤
      c * Smax)
    (hb : s (σ b) = Smax) :
    s b < Smax :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.no_copeak_recursion_left
    hc hSmax hbound hb

/-- **[Lane 1/3 two-dilate coupling obstruction]** Minimal contradiction form of the strict envelope:
`H(b) ≤ c·Smax` with `c < 2` forbids both dilates at that same frequency from being marginal maximizers.
This is the exact formal statement that the two-dilate coupling supplies no recursive co-peak. -/
theorem doorIV_twoDilate_not_joint_marginal_extreme_export
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hbound : _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate s σ b ≤
      c * Smax) :
    ¬ (s b = Smax ∧ s (σ b) = Smax) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.not_joint_marginal_extreme_of_lt_two_mul
    hc hSmax hbound

/-- **[Lane 1/3 two-dilate coupling obstruction]** If the two-dilate maximum is dominated by a
structureless independent-pairing surrogate and the surrogate is bounded by the perfect co-peak
ceiling, then the dilation route remains at the same marginal envelope. No cancellation, completion,
or capacity claim. -/
theorem doorIV_dilate_le_surrogate_le_two_max_export {H I Smax : ℝ}
    (hHI : H ≤ I) (hI : I ≤ 2 * Smax) :
    H ≤ 2 * Smax :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.dilate_le_surrogate_le_two_max
    hHI hI

/-- **[Lane 1/3 two-dilate coupling obstruction]** When the dilation maximum is pinned between the
marginal floor and the independent-pairing surrogate, the two-dilate structure carries the marginal
`√(n·log)` burden rather than supplying a new anti-concentration mechanism. -/
theorem doorIV_dilate_pinned_between_marginal_and_surrogate_export {H I Smax : ℝ}
    (hfloor : Smax ≤ H) (hHI : H ≤ I) :
    Smax ≤ H ∧ H ≤ I :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.dilate_pinned_between_marginal_and_surrogate
    hfloor hHI

#print axioms doorIV_twoDilate_le_two_mul_max_export
#print axioms doorIV_twoDilate_no_copeak_recursion_export
#print axioms doorIV_twoDilate_no_copeak_recursion_left_export
#print axioms doorIV_twoDilate_not_joint_marginal_extreme_export
#print axioms doorIV_dilate_le_surrogate_le_two_max_export
#print axioms doorIV_dilate_pinned_between_marginal_and_surrogate_export


/-- **[Lane 1/3 dyadic coherence-tower obstruction]** If the upper segment of the dyadic coherence
product is fully coherent, its factors are all `1`, so the whole product collapses to the bottom
segment alone. Upper coherent levels provide no damping. -/
theorem doorIV_tower_product_collapses_to_bottom_export (upper bottom : List ℝ)
    (hupper : ∀ r ∈ upper, r = 1) :
    (upper ++ bottom).prod = bottom.prod :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.product_collapses_to_bottom
    upper bottom hupper

/-- **[Lane 1/3 dyadic coherence-tower obstruction]** With a coherent upper tower and a uniform
bottom-factor floor `c`, the full tower product is bounded below by `c ^ bottom.length`. Thus all
possible damping lives in the bottom segment. -/
theorem doorIV_tower_product_ge_bottom_floor_export (upper bottom : List ℝ) {c : ℝ}
    (hupper : ∀ r ∈ upper, r = 1) (hc : 0 ≤ c)
    (hbottom : ∀ r ∈ bottom, c ≤ r) :
    c ^ bottom.length ≤ (upper ++ bottom).prod :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.tower_product_ge_bottom_floor
    upper bottom hupper hc hbottom

/-- **[Lane 1/3 dyadic coherence-tower telescope]** Exact endpoint telescope: for any positive mass
chain, the product of consecutive parent/child coherence ratios times the final leaf mass is exactly
the initial root mass. This kernelizes the algebra behind "root = product × leaf". -/
theorem doorIV_coherenceProduct_mul_getLast_export (a : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t) *
        (a :: t).getLast (by simp) = a :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.coherenceProduct_mul_getLast
    a t hpos

/-- **[Lane 1/3 dyadic coherence-tower telescope]** Door-IV-facing restatement of the exact telescope:
the root mass equals the coherence product times the leaf mass. No cancellation is created here; it is
only the faithful algebraic reduction that exposes the product as the remaining obligation. -/
theorem doorIV_root_eq_coherenceProduct_mul_leaf_export (a : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    a = DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t) *
        (a :: t).getLast (by simp) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_eq_coherenceProduct_mul_leaf
    a t hpos

/-- **[Lane 1/3 dyadic coherence-tower telescope]** The coherence product is exactly root divided by
leaf. Therefore a prize-scale root bound inside the tower is precisely a small-product requirement,
not an independent fifth lever. -/
theorem doorIV_coherenceProduct_eq_root_div_leaf_export (a : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t) =
      a / (a :: t).getLast (by simp) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.coherenceProduct_eq_root_div_leaf
    a t hpos

/-- **[Lane 1/3 dyadic coherence-tower telescope]** Raw root control is equivalent to controlling the
coherence product below the normalized target `B / leaf`. This is the formal interface used by the
tower-collapse obstruction. -/
theorem doorIV_root_le_bound_iff_coherenceProduct_le_bound_div_leaf_export
    (a B : ℝ) (t : List ℝ) (hpos : ∀ x ∈ a :: t, 0 < x) :
    a ≤ B ↔
      DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t) ≤
        B / (a :: t).getLast (by simp) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_le_bound_iff_coherenceProduct_le_bound_div_leaf
    a B t hpos

/-- **[Lane 1/3 dyadic coherence-tower obstruction]** If the product has a floor `c` and the normalized
target is below that floor, the advertised root bound is impossible. This packages the exact consumer
for the fixed-width tower-collapse no-go. -/
theorem doorIV_not_root_le_bound_of_bound_div_leaf_lt_product_floor_export
    (a B c : ℝ) (t : List ℝ) (hpos : ∀ x ∈ a :: t, 0 < x)
    (hfloor : c ≤ DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t))
    (htarget : B / (a :: t).getLast (by simp) < c) :
    ¬ a ≤ B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_root_le_bound_of_bound_div_leaf_lt_product_floor
    a B c t hpos hfloor htarget

/-- **[Lane 1/3 dyadic coherence-tower obstruction]** Product floors transfer back to raw root floors:
`c ≤ ∏ρ_j` forces `c * leaf ≤ root`. A fixed product floor therefore keeps the period at a fixed
fraction of leaf mass and cannot by itself yield the prize's square-root saving. -/
theorem doorIV_root_ge_product_floor_mul_leaf_export (a c : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x)
    (hfloor : c ≤ DoorIVCoherenceTowerTelescope.coherenceProduct (a :: t)) :
    c * (a :: t).getLast (by simp) ≤ a :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_ge_product_floor_mul_leaf
    a c t hpos hfloor

#print axioms doorIV_coherenceProduct_mul_getLast_export
#print axioms doorIV_root_eq_coherenceProduct_mul_leaf_export
#print axioms doorIV_coherenceProduct_eq_root_div_leaf_export
#print axioms doorIV_root_le_bound_iff_coherenceProduct_le_bound_div_leaf_export
#print axioms doorIV_not_root_le_bound_of_bound_div_leaf_lt_product_floor_export
#print axioms doorIV_root_ge_product_floor_mul_leaf_export


/-- **[Lane 1/3 dyadic coherence-tower obstruction]** A fixed-width bottom slack zone gives only a
fixed-width floor: if the nontrivial bottom segment has length at most `K` and all its factors are at
least `c ∈ [0,1]`, then the full product is still at least `c^K`, independent of the upper tower
height. This blocks logarithmic-in-`n` damping from a fully coherent upper tower. -/
theorem doorIV_tower_product_ge_fixed_width_floor_export (upper bottom : List ℝ) {c : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlen : bottom.length ≤ K) (hbottom : ∀ r ∈ bottom, c ≤ r) :
    c ^ K ≤ (upper ++ bottom).prod :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.tower_product_ge_fixed_width_floor
    upper bottom hupper hc0 hc1 hlen hbottom

/-- **[Lane 1/3 dyadic coherence-tower obstruction]** Any claimed coherence-product target below the
fixed floor `c^K` forces an escape from the observed fixed-width-bottom model: either the bottom segment
has more than `K` nontrivial levels, or some bottom factor is below `c`. No CORE or capacity claim. -/
theorem doorIV_below_floor_target_forces_width_or_floor_break_export
    (upper bottom : List ℝ) {c θ : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (htarget : (upper ++ bottom).prod ≤ θ) (hbelow : θ < c ^ K) :
    K < bottom.length ∨ ∃ r ∈ bottom, r < c :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.below_floor_target_forces_width_or_floor_break
    upper bottom hupper hc0 hc1 htarget hbelow

#print axioms doorIV_tower_product_collapses_to_bottom_export
#print axioms doorIV_tower_product_ge_bottom_floor_export
#print axioms doorIV_tower_product_ge_fixed_width_floor_export
#print axioms doorIV_below_floor_target_forces_width_or_floor_break_export


/-- **[Lane 3 dyadic descent obstruction]** Iterating the per-level dilation descent
`M (k+1) ≤ 2*M k` through `a` dyadic levels gives only `M a ≤ 2^a * M 0`, the factor-`n` trivial
ceiling for `n=2^a`. -/
theorem doorIV_dilation_telescope_le_two_pow_mul_export (M : ℕ → ℝ)
    (hpos : ∀ k, 0 ≤ M k) (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (a : ℕ) :
    M a ≤ 2 ^ a * M 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope.telescope_le_two_pow_mul
    M hpos hstep a

/-- **[Lane 3 dyadic descent obstruction]** With the base period normalized to one, pure factor-2
recursion gives exactly `M a ≤ 2^a`. This is the trivial `M(μ_n) ≤ n` ceiling, not the prize
`√(n log)` cancellation scale. -/
theorem doorIV_dilation_telescope_le_two_pow_of_base_one_export (M : ℕ → ℝ)
    (hpos : ∀ k, 0 ≤ M k) (hstep : ∀ k, M (k + 1) ≤ 2 * M k)
    (hbase : M 0 = 1) (a : ℕ) :
    M a ≤ 2 ^ a :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope.telescope_le_two_pow_of_base_one
    M hpos hstep hbase a

/-- **[Lane 3 dyadic descent obstruction]** More generally, any descent with per-level factor `c`
telescopes to `c^a * M 0`. Thus all nontrivial saving must come from a real per-level factor below the
doubling ceiling, precisely the slack object isolated by the Door-IV probes. -/
theorem doorIV_dilation_telescope_per_level_factor_export (M : ℕ → ℝ) (hpos : ∀ k, 0 ≤ M k)
    {c : ℝ} (hc1 : 1 ≤ c) (hstep : ∀ k, M (k + 1) ≤ c * M k) (a : ℕ) :
    M a ≤ c ^ a * M 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope.telescope_per_level_factor
    M hpos hc1 hstep a

#print axioms doorIV_dilation_telescope_le_two_pow_mul_export
#print axioms doorIV_dilation_telescope_le_two_pow_of_base_one_export
#print axioms doorIV_dilation_telescope_per_level_factor_export


/-- **[Lane 3 dyadic descent obstruction]** Per-frequency half-subgroup control is exactly bounded by
that half-subgroup's worst period. This is the pointwise input to the Door-IV dilation recursion, and
it carries no cancellation beyond the definition of `M(H)`. -/
theorem doorIV_norm_eta_le_worstPeriod_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    {c : F} (hc : c ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H c‖ ≤
      _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ H hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion.norm_eta_le_worstPeriod
    H hne hc

/-- **[Lane 3 dyadic descent obstruction]** The two sub-periods in a nonzero dilation split are bounded
by `2*M(H)`. Since multiplication by a nonzero coset representative preserves nonzero frequencies,
this is the exact factor-2 bottleneck of the elementary descent. -/
theorem doorIV_two_dilate_le_two_mul_worstPeriod_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    {g b : F} (hg : g ≠ 0) (hb : b ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ ≤
        2 * _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ H hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion.two_dilate_le_two_mul_worstPeriod
    H hne hg hb

/-- **[Lane 3 dyadic descent obstruction]** On an index-2 dilation cover `G = H ∪ gH`, each nonzero
frequency has period magnitude at most `2*M(H)`. This is triangle inequality plus nonzero-frequency
preservation only, hence no Door-IV anti-concentration input. -/
theorem doorIV_norm_eta_union_le_two_mul_worstPeriod_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    {g b : F} (hg : g ≠ 0) (hb : b ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b‖ ≤
      2 * _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ H hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion.norm_eta_union_le_two_mul_worstPeriod
    H hne hg hb hdisj

/-- **[Lane 3 dyadic descent obstruction]** Headline recursion: the worst period of the index-2 cover
is at most twice the half-subgroup worst period. Iterated down a dyadic tower this recovers only the
trivial `M(μ_n) ≤ n` ceiling, so any prize-relevant descent must prove a real per-level factor below
`2`. No CORE / cancellation / completion / moment-saving / capacity claim. -/
theorem doorIV_worstPeriod_union_le_two_mul_worstPeriod_export {F : Type*} [Field F]
    [Fintype F] [DecidableEq F] {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    {g : F} (hg : g ≠ 0) (hdisj : Disjoint H (H.image (fun y => g * y))) :
    _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
        (H ∪ H.image (fun y => g * y)) hne ≤
      2 * _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ H hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion.worstPeriod_union_le_two_mul_worstPeriod
    H hne hg hdisj

/-- **[Lane 3 dyadic descent obstruction]** The RHS of the factor-2 recursion is nonnegative, so the
recursion is a genuine non-vacuous ceiling between nonnegative worst-period quantities. -/
theorem doorIV_two_mul_worstPeriod_nonneg_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty) :
    0 ≤ 2 * _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ H hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion.two_mul_worstPeriod_nonneg
    H hne

#print axioms doorIV_norm_eta_le_worstPeriod_export
#print axioms doorIV_two_dilate_le_two_mul_worstPeriod_export
#print axioms doorIV_norm_eta_union_le_two_mul_worstPeriod_export
#print axioms doorIV_worstPeriod_union_le_two_mul_worstPeriod_export
#print axioms doorIV_two_mul_worstPeriod_nonneg_export


/-- **[Lane 3 refuted-lever constraint, Jacobi cocycle no-random-edge]** If the iid-unit-phase
surrogate sup is below the real Jacobi-cocycle sup, then the real object has no strict dispersion edge
over that random-phase surrogate. This kernelizes the probe verdict that the cocycle route is
surrogate-dominated, hence any successful bound must also control the moment / extreme-value surrogate
rather than exploit a cocycle-specific door-(iv) mechanism. No CORE / cancellation / completion /
capacity claim. -/
theorem doorIV_cocycle_no_random_edge_export {iidSup realSup : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup) :
    ¬ realSup < iidSup :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.no_cocycle_edge_of_surrogate_le h

/-- **[Lane 3 refuted-lever constraint, Jacobi cocycle no-random-edge]** Any bound on the real
Jacobi-cocycle sup transfers immediately to the iid surrogate under the measured regime
`iidSup ≤ realSup`. Thus a purported door-(iv) real-object bound is no stronger than the same bound on
the surrogate, i.e. it routes back to the random extreme-value / moment face. -/
theorem doorIV_cocycle_real_bound_transfers_to_surrogate_export {iidSup realSup B : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup) (hB : realSup ≤ B) :
    iidSup ≤ B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.real_bound_transfers_to_surrogate
    h hB

/-- **[Lane 3 refuted-lever constraint, Jacobi cocycle no-random-edge]** A certificate below the iid
surrogate is impossible: if `B < iidSup`, then `B` cannot bound the real Jacobi-cocycle sup. This is the
probe-facing contrapositive of surrogate domination. -/
theorem doorIV_cocycle_no_sub_surrogate_certificate_export {iidSup realSup B : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup) (hlt : B < iidSup) :
    ¬ realSup ≤ B :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.real_not_le_of_lt_surrogate
    h hlt

/-- **[Lane 3 refuted-lever constraint, Jacobi cocycle no-random-edge]** Headline packaging: the real
Jacobi-cocycle sup is surrogate-dominated below, so a cocycle-specific dispersion advantage over iid
random phases is excluded. This only records the obstruction to the proof route; it does not prove the
CORE Gauss-period cancellation bound. -/
theorem doorIV_cocycle_dispersion_surrogate_dominated_export {iidSup realSup : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup) :
    iidSup ≤ realSup ∧ ¬ realSup < iidSup :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.cocycle_dispersion_is_surrogate_dominated
    h

#print axioms doorIV_cocycle_no_random_edge_export
#print axioms doorIV_cocycle_real_bound_transfers_to_surrogate_export
#print axioms doorIV_cocycle_no_sub_surrogate_certificate_export
#print axioms doorIV_cocycle_dispersion_surrogate_dominated_export


/-- **[Lane 1/3 joint-field whiteness obstruction]** Centering is linear. This is the bookkeeping
identity used by the lag-covariance probe interface before the white-field diagonalization. -/
theorem doorIV_jointField_sum_centered_export {ι : Type*}
    (f : ι → ℝ) (s : Finset ι) (μ : ℝ) :
    ∑ i ∈ s, (f i - μ) = (∑ i ∈ s, f i) - (s.card : ℝ) * μ :=
  _root_.ProximityGap.Frontier.DoorIVJointFieldWhite.sum_centered f s μ

/-- **[Lane 1/3 joint-field whiteness obstruction]** The diagonal second moment of the centered
period field is nonnegative. In the white-field regime this variance is the only surviving quadratic
mass; nonzero lag blocks carry no additional structure. -/
theorem doorIV_jointField_diagonal_sndMoment_nonneg_export {ι : Type*}
    (f : ι → ℝ) (s : Finset ι) (μ : ℝ) :
    0 ≤ ∑ i ∈ s, (f i - μ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVJointFieldWhite.diagonal_sndMoment_nonneg f s μ

/-- **[Lane 1/3 joint-field whiteness obstruction]** If the centered period field has zero summed
cross-covariance against a shifted copy, and the shift preserves the diagonal mass, then the quadratic
form of the two-block sum diagonalizes to exactly twice the marginal variance. Thus the joint `b ↔ b'`
route contributes no information beyond the marginal moment/variance face. No CORE / cancellation /
completion / capacity claim. -/
theorem doorIV_jointField_white_diagonalizes_export {ι : Type*}
    (f : ι → ℝ) (s : Finset ι) (μ : ℝ) (σ : ι → ι)
    (hσ : ∑ i ∈ s, (f i - μ) * (f (σ i) - μ) = 0)
    (hbij : ∑ i ∈ s, (f (σ i) - μ) ^ 2 = ∑ i ∈ s, (f i - μ) ^ 2) :
    ∑ i ∈ s, ((f i - μ) + (f (σ i) - μ)) ^ 2 =
      2 * ∑ i ∈ s, (f i - μ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVJointFieldWhite.white_field_diagonalizes
    f s μ σ hσ hbij

#print axioms doorIV_jointField_sum_centered_export
#print axioms doorIV_jointField_diagonal_sndMoment_nonneg_export
#print axioms doorIV_jointField_white_diagonalizes_export

/-- **[Lane 1/3 common-ray coherence obstruction]** A finite list of nonnegative pieces on a fixed
unit complex ray has coherence exactly `1` whenever its total mass is nonzero. Thus subdividing the
worst-frequency monomial sum cannot by itself supply door-(iv) anti-concentration while all pieces
remain ray-collinear; a real saving must prove genuine angular spread. -/
theorem doorIV_commonRay_coherence_eq_one_export {xs : List ℝ} {u : ℂ}
    (hu : ‖u‖ = 1) (hxs : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) :
    _root_.ProximityGap.Frontier.DoorIVCommonRayCoherence.complexPieceCoherence
      (xs.map fun x => (x : ℂ) * u) = 1 :=
  _root_.ProximityGap.Frontier.DoorIVCommonRayCoherence.complexPieceCoherence_eq_one_of_commonRay_nonneg
    hu hxs hsum

/-- **[Lane 1/3 common-ray coherence obstruction]** A nonzero common-ray decomposition cannot satisfy
any strict threshold `θ < 1`. This is the probe-facing target form of the same-ray obstruction: before
claiming a `ρ ≤ θ` certificate, the door-(iv) route must first rule out common-ray alignment. -/
theorem doorIV_commonRay_not_coherence_le_target_export {xs : List ℝ} {u : ℂ} {theta : ℝ}
    (hu : ‖u‖ = 1) (hxs : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) (htheta : theta < 1) :
    ¬ _root_.ProximityGap.Frontier.DoorIVCommonRayCoherence.complexPieceCoherence
        (xs.map fun x => (x : ℂ) * u) ≤ theta :=
  _root_.ProximityGap.Frontier.DoorIVCommonRayCoherence.commonRay_not_complexPieceCoherence_le_of_lt_one
    hu hxs hsum htheta

/-- **[Lane 1/3 raw coset-half obstruction]** For the real index-2 coset-half split, same-sign
half-period sums saturate the two-piece coherence at `1`. The raw split therefore has no intrinsic
anti-concentration slack at same-sign adversarial frequencies. -/
theorem doorIV_cosetHalf_sameSign_coherence_eq_one_export {A B : ℝ}
    (hsign : (0 ≤ A ∧ 0 ≤ B) ∨ (A ≤ 0 ∧ B ≤ 0)) (hsum : A + B ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence A B = 1 :=
  _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_sameSign
    hsign hsum

/-- **[Lane 1/3 raw coset-half same-sign no-go]** Same-sign real halves saturate the raw index-2
coherence at `1`, so no positive `ε` saving certificate `ρ ≤ 1-ε` can hold in this branch. Any door-(iv)
coset-half theorem must first exclude same-sign adversarial frequencies or refine the split. -/
theorem doorIV_cosetHalf_noPositiveSaving_of_sameSign_export {A B ε : ℝ}
    (hsign : (0 ≤ A ∧ 0 ≤ B) ∨ (A ≤ 0 ∧ B ≤ 0)) (hsum : A + B ≠ 0)
    (hε : 0 < ε) :
    ¬ _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence A B ≤ 1 - ε := by
  intro hsave
  have heq := doorIV_cosetHalf_sameSign_coherence_eq_one_export hsign hsum
  rw [heq] at hsave
  linarith

#print axioms doorIV_cosetHalf_noPositiveSaving_of_sameSign_export

/-- **[Lane 1/3 raw coset-half obstruction]** In the opposite-sign case, a non-strict `ε` coherence
saving is equivalent to the minority half carrying the corresponding `ε/2` share of the total
absolute half-mass. Opposite signs alone do not prove the missing anti-concentration input. -/
theorem doorIV_cosetHalf_saving_iff_minority_mass_export {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence P (-N) ≤ 1 - ε ↔
      ε * (P + N) ≤ 2 * min P N :=
  _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_le_one_sub_iff_min_mass
    hP hN htotal

/-- **[Lane 1/3 raw coset-half strict obstruction]** Strict `ε` coherence saving in the raw index-2
opposite-sign split is EXACTLY strict minority-mass participation after clearing the positive denominator.
So a strict door-(iv) anti-concentration theorem cannot come from the formal split alone: it must prove
`ε*(P+N) < 2*min(P,N)` at the adversarial frequency. -/
theorem doorIV_cosetHalf_strictSaving_iff_strictMinorityMass_export {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence P (-N) < 1 - ε ↔
      ε * (P + N) < 2 * min P N :=
  _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_lt_one_sub_iff_min_mass
    hP hN htotal

#print axioms doorIV_cosetHalf_strictSaving_iff_strictMinorityMass_export

/-- **[Lane 1/3 raw coset-half strict no-go]** If the strict minority-mass threshold fails, then
strict `ε` coherence saving is impossible for the raw index-2 opposite-sign split. This is the direct
contrapositive consumer of the strict iff: below proportional minority-mass participation, the split
cannot certify door-(iv) anti-concentration. -/
theorem doorIV_cosetHalf_noStrictSaving_of_minorityMass_le_export {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N)
    (hmass : 2 * min P N ≤ ε * (P + N)) :
    ¬ _root_.ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence P (-N) < 1 - ε := by
  intro hsave
  have hlt : ε * (P + N) < 2 * min P N :=
    (doorIV_cosetHalf_strictSaving_iff_strictMinorityMass_export hP hN htotal).mp hsave
  exact (not_lt_of_ge hmass) hlt

#print axioms doorIV_cosetHalf_noStrictSaving_of_minorityMass_le_export

/-- **[Lane 1/3 transverse-spread geometry]** In a unit direction frame, projection and transverse
components decompose the squared norm exactly. This names the geometric content a door-(iv) angular
spread certificate must control. -/
theorem doorIV_transverse_pythagorean_export {u z : ℂ} (hu : ‖u‖ = 1) :
    (_root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayProj u z) ^ 2 +
      (_root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp u z) ^ 2 = ‖z‖ ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_sq_add_rayPerp_sq hu

/-- **[Lane 1/3 transverse-spread geometry]** Projection deficit controls genuine perpendicular
spread by the sharp inequality `perp² ≤ 2‖z‖(‖z‖ - proj)`. Sector/coherence deficit certificates
therefore pay an explicit angular-spread budget rather than obtaining cancellation for free. -/
theorem doorIV_transverse_perp_sq_le_deficit_export {u z : ℂ} (hu : ‖u‖ = 1) :
    (_root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp u z) ^ 2 ≤
      2 * ‖z‖ * (‖z‖ - _root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayProj u z) :=
  _root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_sq_le_two_norm_mul_deficit hu

/-- **[Lane 1/3 resultant-frame geometry]** In the resultant frame of a nonzero list, the per-piece
transverse components sum to zero. Any angular-spread argument must control a signed cancelling
transverse set, not merely subdivide the monomial sum into more pieces. -/
theorem doorIV_transverse_resultant_frame_perp_sum_zero_export (zs : List ℂ) (hR : zs.sum ≠ 0) :
    (zs.map (_root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp
      (zs.sum / (‖zs.sum‖ : ℂ)))).sum = 0 :=
  _root_.ProximityGap.Frontier.DoorIVTransverseSpread.sum_rayPerp_resultant_frame_eq_zero zs hR

/-- **[Lane 1/3 resultant-frame geometry]** In the resultant frame, the total projection deficit is
exactly `L¹ - ‖Σ zᵢ‖`, i.e. the coherence deficit times the `L¹` mass. This is only a sharp geometric
accounting identity; it proves no CORE cancellation bound. -/
theorem doorIV_transverse_resultant_frame_deficit_budget_export (zs : List ℂ) (hR : zs.sum ≠ 0) :
    (zs.map (fun z => ‖z‖ - _root_.ProximityGap.Frontier.DoorIVTransverseSpread.rayProj
      (zs.sum / (‖zs.sum‖ : ℂ)) z)).sum = (zs.map norm).sum - ‖zs.sum‖ :=
  _root_.ProximityGap.Frontier.DoorIVTransverseSpread.sum_deficit_resultant_frame_eq zs hR

#print axioms doorIV_commonRay_coherence_eq_one_export
#print axioms doorIV_commonRay_not_coherence_le_target_export
#print axioms doorIV_cosetHalf_sameSign_coherence_eq_one_export
#print axioms doorIV_cosetHalf_saving_iff_minority_mass_export
#print axioms doorIV_transverse_pythagorean_export
#print axioms doorIV_transverse_perp_sq_le_deficit_export
#print axioms doorIV_transverse_resultant_frame_perp_sum_zero_export
#print axioms doorIV_transverse_resultant_frame_deficit_budget_export

/-- **[Lane 1 sector-coherence obligation]** If every phase piece remains in a sector whose
projection floor is `c` along a fixed unit direction, then the list coherence is at least `c`.
Consequently, any door-(iv) coherence saving must prove genuine sector escape, not just subdivision
or common-ray bookkeeping. -/
theorem doorIV_sector_floor_le_coherence_export {zs : List ℂ} {u : ℂ} {c : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hproj : ∀ z ∈ zs,
      c * ‖z‖ ≤ _root_.ProximityGap.Frontier.DoorIVSectorCoherence.rayProj u z) :
    c ≤ _root_.ProximityGap.Frontier.DoorIVSectorCoherence.complexPieceCoherence zs :=
  _root_.ProximityGap.Frontier.DoorIVSectorCoherence.sector_floor_le_complexPieceCoherence
    hu hden hproj

/-- **[Lane 1 sector-coherence obligation]** A claimed bound `ρ ≤ θ` with `θ < c` forces at least
one piece to leave every unit-direction sector of floor `c`. This is the precise consumer form of
the sector obstruction. -/
theorem doorIV_sector_escape_of_coherence_le_export {zs : List ℂ} {u : ℂ} {c θ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hcoh : _root_.ProximityGap.Frontier.DoorIVSectorCoherence.complexPieceCoherence zs ≤ θ)
    (hθ : θ < c) :
    ∃ z ∈ zs, _root_.ProximityGap.Frontier.DoorIVSectorCoherence.rayProj u z < c * ‖z‖ :=
  _root_.ProximityGap.Frontier.DoorIVSectorCoherence.exists_piece_rayProj_lt_of_complexPieceCoherence_le
    hu hden hcoh hθ

/-- **[Lane 1 aggregate angular budget]** Any `ρ ≤ 1 - ε` coherence drop forces at least an
`ε`-fraction of the total `L¹` mass to appear as aggregate ray-projection deficit in every unit
direction. This is a budget identity/obligation only, not a cancellation theorem. -/
theorem doorIV_sector_aggregate_deficit_budget_export {zs : List ℂ} {u : ℂ} {ε : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hcoh : _root_.ProximityGap.Frontier.DoorIVSectorCoherence.complexPieceCoherence zs ≤ 1 - ε) :
    ε * (zs.map norm).sum ≤
      (zs.map (fun z => ‖z‖ - _root_.ProximityGap.Frontier.DoorIVSectorCoherence.rayProj u z)).sum :=
  _root_.ProximityGap.Frontier.DoorIVSectorCoherence.aggregate_rayProj_deficit_ge_eps_of_complexPieceCoherence_le_one_sub
    hu hden hcoh

/-- **[Lane 1 aggregate angular budget]** Contrapositive: if some unit direction has aggregate
projection deficit below the `ε · L¹` budget, then the pieces cannot certify `ρ ≤ 1 - ε`. This pins
the exact missing angular-spread input for door-(iv). -/
theorem doorIV_sector_not_coherence_le_one_sub_of_deficit_short_export {zs : List ℂ} {u : ℂ}
    {ε : ℝ} (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hdef : (zs.map (fun z => ‖z‖ - _root_.ProximityGap.Frontier.DoorIVSectorCoherence.rayProj u z)).sum <
      ε * (zs.map norm).sum) :
    ¬ _root_.ProximityGap.Frontier.DoorIVSectorCoherence.complexPieceCoherence zs ≤ 1 - ε :=
  _root_.ProximityGap.Frontier.DoorIVSectorCoherence.not_complexPieceCoherence_le_one_sub_of_aggregate_rayProj_deficit_lt
    hu hden hdef

#print axioms doorIV_sector_floor_le_coherence_export
#print axioms doorIV_sector_escape_of_coherence_le_export
#print axioms doorIV_sector_aggregate_deficit_budget_export
#print axioms doorIV_sector_not_coherence_le_one_sub_of_deficit_short_export
/-- **[Lane 1/3 real-piece coherence obstruction]** If all real pieces in a door-(iv) refinement
are nonnegative and the total signed mass is positive, the normalized real-piece coherence is exactly
`1`. A real/collinear split has no intrinsic anti-concentration slack until it proves genuine negative
mass. -/
theorem doorIV_realPiece_coherence_eq_one_nonneg_export {xs : List ℝ}
    (h : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) :
    _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs = 1 :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence_eq_one_of_forall_nonneg
    h hsum

/-- **[Lane 1/3 real-piece coherence obstruction]** Mirror same-sign obstruction: an all-nonpositive
real-piece refinement with negative total mass also saturates coherence at `1`. -/
theorem doorIV_realPiece_coherence_eq_one_nonpos_export {xs : List ℝ}
    (h : ∀ x ∈ xs, x ≤ 0) (hsum : xs.sum < 0) :
    _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs = 1 :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence_eq_one_of_forall_nonpos
    h hsum

/-- **[Lane 1/3 real-piece coherence obstruction]** Strict real-piece coherence slack below `1`
forces both signs to occur in the actual finite list. Thus a real, negation-stable door-(iv)
refinement only helps if it proves balanced sign mixing, not merely a finer partition. -/
theorem doorIV_realPiece_coherence_lt_one_forces_both_signs_export {xs : List ℝ}
    (hsum : xs.sum ≠ 0)
    (hcoh : _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs < 1) :
    (∃ x ∈ xs, 0 < x) ∧ (∃ x ∈ xs, x < 0) :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence_lt_one_forces_both_signs
    hsum hcoh

/-- **[Lane 1/3 sign-mass slack obstruction]** In the compressed real two-mass model, coherence
is exactly `1 - 2 * min(P,N)/(P+N)`. The entire possible saving is the minority sign mass. -/
theorem doorIV_signMass_coherence_eq_one_sub_twice_min_export {P N : ℝ}
    (hden : 0 < P + N) :
    _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence P N =
      1 - 2 * min P N / (P + N) :=
  _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence_eq_one_sub_twice_min
    hden

/-- **[Lane 1/3 sign-mass slack obstruction]** A target `theta` for compressed real coherence is
equivalent to the minority-mass lower bound `(1-theta)(P+N)/2 ≤ min(P,N)`. This is the exact
probe-facing constraint behind any real/collinear anti-concentration claim. -/
theorem doorIV_signMass_coherence_le_iff_minority_mass_ge_export {P N theta : ℝ}
    (hden : 0 < P + N) :
    _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence P N ≤ theta ↔
      (1 - theta) * (P + N) / 2 ≤ min P N :=
  _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence_le_iff_minority_mass_ge
    hden

/-- **[Lane 1/3 sign-mass slack obstruction]** If the minority sign mass is below the requested
`eps/2` fraction, then a `1-eps` real-coherence certificate is impossible. -/
theorem doorIV_signMass_no_coherence_drop_of_minority_lt_export {P N eps : ℝ}
    (hden : 0 < P + N) (hminor : min P N < eps * (P + N) / 2) :
    ¬ _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence P N ≤ 1 - eps :=
  _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.not_coherence_le_one_sub_of_minority_mass_lt
    hden hminor

/-- **[Lane 1/3 real-piece compression obstruction]** Once a real refinement is compressed to
positive mass `P` and negative mass `N`, its list coherence is literally the sign-mass coherence.
Finer real partitions add no hidden angular degree of freedom. -/
theorem doorIV_realPiece_compression_eq_signMass_export {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) :
    _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs =
      _root_.ProximityGap.Frontier.DoorIVRealSignMassSlack.signMassCoherence P N :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCompression.realPieceCoherence_eq_signMassCoherence_of_compression
    hsum habssum

/-- **[Lane 1/3 real-piece compression obstruction]** Under compression, achieving a threshold
`theta` is exactly the same minority-sign-mass lower bound as in the two-mass model. -/
theorem doorIV_realPiece_compression_le_iff_minority_mass_ge_export {xs : List ℝ} {P N theta : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N) :
    _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs ≤ theta ↔
      (1 - theta) * (P + N) / 2 ≤ min P N :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCompression.realPieceCoherence_le_iff_minority_mass_ge_of_compression
    hsum habssum hden

/-- **[Lane 1/3 real-piece compression obstruction]** Compressed strict slack forces a positive
minority sign mass and actual list-level sign mixing. This locks the real/collinear Door-IV route to
a concrete sign-balance obligation; no CORE / cancellation / completion / capacity claim. -/
theorem doorIV_realPiece_compression_slack_forces_minority_and_both_signs_export {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N)
    (hsumne : xs.sum ≠ 0)
    (hcoh : _root_.ProximityGap.Frontier.DoorIVRealPieceCoherence.realPieceCoherence xs < 1) :
    0 < min P N ∧ (∃ x ∈ xs, 0 < x) ∧ (∃ x ∈ xs, x < 0) :=
  _root_.ProximityGap.Frontier.DoorIVRealPieceCompression.min_pos_and_both_signs_of_realPieceCoherence_lt_one_of_compression
    hsum habssum hden hsumne hcoh

#print axioms doorIV_realPiece_coherence_eq_one_nonneg_export
#print axioms doorIV_realPiece_coherence_eq_one_nonpos_export
#print axioms doorIV_realPiece_coherence_lt_one_forces_both_signs_export
#print axioms doorIV_signMass_coherence_eq_one_sub_twice_min_export
#print axioms doorIV_signMass_coherence_le_iff_minority_mass_ge_export
#print axioms doorIV_signMass_no_coherence_drop_of_minority_lt_export
#print axioms doorIV_realPiece_compression_eq_signMass_export
#print axioms doorIV_realPiece_compression_le_iff_minority_mass_ge_export
#print axioms doorIV_realPiece_compression_slack_forces_minority_and_both_signs_export

/-- **[Lane 1/3 mult-shift collinearity obstruction]** For any finite real multiplicative-shift
piece family, the normalized coherence is exactly the sign-mass imbalance. Thus a real/collinear
refinement has no hidden two-dimensional angular degree of freedom; it must prove sign cancellation. -/
theorem doorIV_multShift_coherence_eq_signMass_imbalance_export {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) :
    _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A =
      |_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A -
        _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A| /
        (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
          _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence_eq_signMass_imbalance s A

/-- **[Lane 1/3 mult-shift collinearity obstruction]** A claimed threshold for real-collinear
multiplicative-shift coherence is equivalent to a concrete minority-sign-mass lower bound. This is
the exact finite obligation left by such refinements, not a cancellation theorem. -/
theorem doorIV_multShift_coherence_le_iff_minority_mass_ge_export {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) {theta : ℝ}
    (hden : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
      _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :
    _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A ≤ theta ↔
      (1 - theta) *
          (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
            _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) / 2 ≤
        min (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A)
          (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence_le_iff_minority_mass_ge s A hden

/-- **[Lane 1/3 mult-shift collinearity obstruction]** In the operational `1 - ε` form, a real
multiplicative-shift refinement must prove an `ε/2` minority-sign-mass fraction. If the adversarial
frequency is nearly one-signed, this route has no slack. -/
theorem doorIV_multShift_coherence_le_one_sub_iff_minority_mass_ge_export {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) {eps : ℝ}
    (hden : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
      _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :
    _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A ≤ 1 - eps ↔
      eps *
          (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
            _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) / 2 ≤
        min (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A)
          (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence_le_one_sub_iff_minority_mass_ge s A hden

/-- **[Lane 1/3 mult-shift collinearity obstruction]** Contrapositive budget form: if the minority
sign mass is below the requested `ε/2` fraction, a real-collinear mult-shift split cannot certify
`ρ ≤ 1 - ε`. -/
theorem doorIV_multShift_not_coherence_le_one_sub_of_minority_lt_export {ι : Type*} (s : Finset ι)
    (A : ι → ℝ) {eps : ℝ}
    (hden : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
      _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A)
    (hminor : min (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A)
        (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) <
      eps * (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
        _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) / 2) :
    ¬ _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A ≤ 1 - eps :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.not_coherence_le_one_sub_of_minority_mass_lt
    s A hden hminor

/-- **[Lane 1/3 mult-shift collinearity obstruction]** Exact strict-slack criterion: once total
real mass is nonzero, real-collinear coherence drops below `1` iff both sign masses are present. -/
theorem doorIV_multShift_coherence_lt_one_iff_both_sign_masses_pos_export {ι : Type*} (s : Finset ι)
    (A : ι → ℝ)
    (hden : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
      _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :
    _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A < 1 ↔
      0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A ∧
        0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence_lt_one_iff_both_sign_masses_pos s A hden

/-- **[Lane 1/3 mult-shift collinearity obstruction]** With both signs present, the exact deficit
`1 - ρ` is the doubled minority sign mass over total mass. The real mult-shift route reduces to this
one scalar balance condition. -/
theorem doorIV_multShift_one_sub_coherence_eq_export {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hP : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A)
    (hN : 0 < _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :
    1 - _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.coherence s A =
      2 * min (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A)
          (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) /
        (_root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.posMass s A +
          _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.negMass s A) :=
  _root_.ProximityGap.Frontier.DoorIVMultShiftCollinear.one_sub_coherence_eq s A hP hN

#print axioms doorIV_multShift_coherence_eq_signMass_imbalance_export
#print axioms doorIV_multShift_coherence_le_iff_minority_mass_ge_export
#print axioms doorIV_multShift_coherence_le_one_sub_iff_minority_mass_ge_export
#print axioms doorIV_multShift_not_coherence_le_one_sub_of_minority_lt_export
#print axioms doorIV_multShift_coherence_lt_one_iff_both_sign_masses_pos_export
#print axioms doorIV_multShift_one_sub_coherence_eq_export

open scoped ComplexConjugate

/-- **[Lane 1 canonical-half quantization obstruction]** A conjugate-closed finite sum is real:
an involutive reindexing that sends each summand to its conjugate forces zero imaginary part. This
is the formal real-axis gate behind canonical half-sum coherence probes. -/
theorem doorIV_canonicalHalf_sum_conjClosed_isReal_export
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) (σ : ι → ι)
    (hσ_mem : ∀ i ∈ s, σ i ∈ s)
    (hσ_invol : ∀ i ∈ s, σ (σ i) = i)
    (hσ_conj : ∀ i ∈ s, f (σ i) = conj (f i)) :
    (∑ i ∈ s, f i).im = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.sum_conjClosed_isReal
    s f σ hσ_mem hσ_invol hσ_conj

/-- **[Lane 1 canonical-half quantization obstruction]** Once both canonical half pieces are real,
the normalized two-piece real inner product is quantized to `{-1, 0, 1}`. There is no continuous
coherence parameter to shave in this real-halved regime. -/
theorem doorIV_canonicalHalf_coherence_quantized_of_real_export {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) :
    let c := (a * conj b).re / (‖a‖ * ‖b‖)
    c = -1 ∨ c = 0 ∨ c = 1 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_quantized_of_real
    ha hb

/-- **[Lane 1 canonical-half quantization obstruction]** If the two real canonical halves are both
nonzero, the coherence is forced to `±1`. Any strict `1-ε` saving must first rule out the
constructive `+1` sign case. -/
theorem doorIV_canonicalHalf_coherence_pm_one_of_real_ne_export {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = -1 ∨
      (a * conj b).re / (‖a‖ * ‖b‖) = 1 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_pm_one_of_real_ne
    ha hb ha0 hb0

/-- **[Lane 1 canonical-half quantization obstruction]** Positive product of the real half-sums
pins the canonical-half coherence to the fully constructive value `+1`. -/
theorem doorIV_canonicalHalf_coherence_eq_one_of_real_mul_pos_export {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hpos : 0 < a.re * b.re) :
    (a * conj b).re / (‖a‖ * ‖b‖) = 1 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_one_of_real_mul_pos
    ha hb hpos

/-- **[Lane 1 canonical-half quantization obstruction]** Negative product of the real half-sums
pins the canonical-half coherence to the destructive value `-1`. -/
theorem doorIV_canonicalHalf_coherence_eq_neg_one_of_real_mul_neg_export {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hneg : a.re * b.re < 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = -1 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_neg_one_of_real_mul_neg
    ha hb hneg

/-- **[Lane 1 canonical-half quantization obstruction]** Zero real-product gives zero coherence,
closing the canonical-half sign-selector trichotomy. This is only a constraint on a proof route, not
a CORE cancellation bound. -/
theorem doorIV_canonicalHalf_coherence_eq_zero_of_real_mul_eq_zero_export {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hzero : a.re * b.re = 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_zero_of_real_mul_eq_zero
    ha hb hzero

#print axioms doorIV_canonicalHalf_sum_conjClosed_isReal_export
#print axioms doorIV_canonicalHalf_coherence_quantized_of_real_export
#print axioms doorIV_canonicalHalf_coherence_pm_one_of_real_ne_export
#print axioms doorIV_canonicalHalf_coherence_eq_one_of_real_mul_pos_export
#print axioms doorIV_canonicalHalf_coherence_eq_neg_one_of_real_mul_neg_export
#print axioms doorIV_canonicalHalf_coherence_eq_zero_of_real_mul_eq_zero_export

/-- **[Lane 1 angular-deficit accounting]** The squared norm of a two-piece sum loses exactly twice
`angularDeficit A B` from the squared half-mass. This is the sharp two-piece Door-IV identity: any
strict coset-half coherence drop is genuine angular misalignment, not a bookkeeping artifact. -/
theorem doorIV_twoPiece_norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit_export (A B : ℂ) :
    ‖A + B‖ ^ 2 = (‖A‖ + ‖B‖) ^ 2 -
      2 * _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.angularDeficit A B :=
  _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit
    A B

/-- **[Lane 1 angular-deficit accounting]** A strict squared half-mass deficit is equivalent to a
positive two-piece angular deficit. Thus a two-piece anti-concentration certificate must prove a
positive phase-misalignment term. -/
theorem doorIV_twoPiece_norm_add_sq_lt_iff_angularDeficit_pos_export (A B : ℂ) :
    ‖A + B‖ ^ 2 < (‖A‖ + ‖B‖) ^ 2 ↔
      0 < _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.angularDeficit A B :=
  _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_lt_halfMass_sq_iff_angularDeficit_pos
    A B

/-- **[Lane 1 multi-piece angular-deficit accounting]** For a finite list of complex pieces, the
squared resultant norm equals squared `L¹` mass minus twice the total pairwise angular deficit. This
identifies the exact many-piece object a Door-IV phase-spread proof must lower-bound. -/
theorem doorIV_multiPiece_norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit_export (zs : List ℂ) :
    ‖zs.sum‖ ^ 2 =
      (_root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.l1Mass zs) ^ 2 -
        2 * _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs :=
  _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit
    zs

/-- **[Lane 1 threshold reduction]** A squared resultant ceiling `T` is exactly equivalent to a
lower bound on total pairwise angular deficit. This is a sqrt-free, non-moment accounting reduction
only; it does not prove the missing arithmetic anti-concentration lower bound. -/
theorem doorIV_multiPiece_norm_sum_sq_le_iff_totalPairDeficit_ge_export (zs : List ℂ) (T : ℝ) :
    ‖zs.sum‖ ^ 2 ≤ T ↔
      ((_root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.l1Mass zs) ^ 2 - T) / 2 ≤
        _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs :=
  _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_le_iff_totalPairDeficit_ge
    zs T

/-- **[Lane 1 angular-deficit ceiling]** The total pairwise angular deficit is bounded by the
antipodal `L¹²/2` ceiling. This names the corresponding L²/triangle-inequality ceiling: controlling
the deficit only by this generic cap cannot by itself supply the prize-scale arithmetic saving. -/
theorem doorIV_totalPairDeficit_le_l1Mass_sq_div_two_export (zs : List ℂ) :
    _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs ≤
      (_root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.l1Mass zs) ^ 2 / 2 :=
  _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit_le_l1Mass_sq_div_two zs

#print axioms doorIV_twoPiece_norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit_export
#print axioms doorIV_twoPiece_norm_add_sq_lt_iff_angularDeficit_pos_export
#print axioms doorIV_multiPiece_norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit_export
#print axioms doorIV_multiPiece_norm_sum_sq_le_iff_totalPairDeficit_ge_export
#print axioms doorIV_totalPairDeficit_le_l1Mass_sq_div_two_export

/-- **[Lane 3 worst-b participation budget]** The aligned coherent mass at a candidate worst
frequency is bounded by its L² magnitude budget: `(Σ wⱼ)² ≤ |s| Σ wⱼ²`. Thus a participation or
forward-mass certificate for the Door-IV coherence cannot evade the Plancherel-style magnitude
object merely by renaming the aligned terms; it must pay the corresponding L² budget. No CORE /
cancellation / completion / moment-saving / capacity claim. -/
theorem doorIV_worstB_participation_sq_aligned_le_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) :
    (∑ j ∈ s, w j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.sq_aligned_mass_le_card_mul_sumSq
    s w

/-- **[Lane 3 worst-b participation ratio]** With positive L² denominator, the normalized
participation ratio is at most one. This is the generic Cauchy ceiling behind the observed worst-b
internal geometry: a strict saving needs arithmetic input beyond the L² participation variable. -/
theorem doorIV_worstB_participation_ratio_le_one_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ)
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ 1 :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_le_one
    s w hpos

/-- **[Lane 3 worst-b participation threshold]** A claimed normalized participation bound
`PR ≤ θ` is exactly the denominator-cleared squared-aligned-mass inequality. The route has no hidden
phase slack unless that concrete L²-normalized inequality is proved. -/
theorem doorIV_worstB_participation_ratio_le_iff_sq_aligned_le_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ θ ↔
      (∑ j ∈ s, w j) ^ 2 ≤ θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_le_iff_sq_aligned_le
    s w hpos

/-- **[Lane 3 worst-b strict participation threshold]** A strict normalized participation saving
`PR < θ` is exactly the strict denominator-cleared squared-aligned-mass inequality. This is the
strict-budget interface probes need before claiming a worst-b participation lever has any content
beyond the same L² magnitude object. -/
theorem doorIV_worstB_participation_ratio_lt_iff_sq_aligned_lt_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < θ ↔
      (∑ j ∈ s, w j) ^ 2 < θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_lt_iff_sq_aligned_lt
    s w hpos

/-- **[Lane 3 worst-b participation failed-saving certificate]** If the squared aligned mass already
exceeds the `θ` denominator budget, then `PR ≤ θ` is impossible. This is the exact no-go form for a
claimed participation anti-concentration saving at the adversarial frequency. -/
theorem doorIV_worstB_not_participation_ratio_le_of_sq_aligned_gt_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2)
    (hgt : θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < (∑ j ∈ s, w j) ^ 2) :
    ¬ (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ θ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_participation_ratio_le_of_sq_aligned_gt
    s w hpos hgt

/-- **[Lane 3 worst-b strict participation failed-saving certificate]** If the squared aligned mass
reaches the `θ` denominator budget, then `PR < θ` is impossible. Strict participation improvements
therefore have exactly the strict L²-normalized squared-mass content, with no hidden phase slack. -/
theorem doorIV_worstB_not_participation_ratio_lt_of_sq_aligned_ge_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2)
    (hge : θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ (∑ j ∈ s, w j) ^ 2) :
    ¬ (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < θ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_participation_ratio_lt_of_sq_aligned_ge
    s w hpos hge

/-- **[Lane 3 worst-b coherence L² floor]** If nonnegative coherent mass `C` is below the aligned
mass, then the L² mass must be at least `C² / |s|`. This is the probe-facing floor: a large aligned
worst-b certificate already forces the corresponding Plancherel expenditure. -/
theorem doorIV_worstB_sumSq_ge_coherence_sq_div_card_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ ∑ j ∈ s, w j) :
    C ^ 2 / (s.card : ℝ) ≤ ∑ j ∈ s, (w j) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.sumSq_ge_coherence_sq_div_card
    s w hcard hC0 hC

/-- **[Lane 3 worst-b budget contrapositive]** An explicit L² budget `B < C² / |s|` rules out
aligned coherent mass `C`. Worst-b participation/coherence attacks must either pay this L² floor or
leave the coherent certificate below `C`; naming participation variables gives no arithmetic
anti-concentration for free. -/
theorem doorIV_worstB_not_coherence_le_aligned_mass_of_sumSq_le_budget_export {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) {B C : ℝ}
    (hC0 : 0 ≤ C) (hbudget : ∑ j ∈ s, (w j) ^ 2 ≤ B)
    (hB : B < C ^ 2 / (s.card : ℝ)) :
    ¬ C ≤ ∑ j ∈ s, w j :=
  _root_.ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_coherence_le_aligned_mass_of_sumSq_le_budget
    s w hcard hC0 hbudget hB

#print axioms doorIV_worstB_participation_sq_aligned_le_export
#print axioms doorIV_worstB_participation_ratio_le_one_export
#print axioms doorIV_worstB_participation_ratio_le_iff_sq_aligned_le_export
#print axioms doorIV_worstB_participation_ratio_lt_iff_sq_aligned_lt_export
#print axioms doorIV_worstB_not_participation_ratio_le_of_sq_aligned_gt_export
#print axioms doorIV_worstB_not_participation_ratio_lt_of_sq_aligned_ge_export
#print axioms doorIV_worstB_sumSq_ge_coherence_sq_div_card_export
#print axioms doorIV_worstB_not_coherence_le_aligned_mass_of_sumSq_le_budget_export

/-- **[Lane 1 unit-piece angular deficit]** For unit-modulus Door-IV phase pieces, the abstract
`L¹` mass is exactly the number of pieces. This specializes the angular-deficit accounting to the
actual monomial-sum geometry without introducing any estimate. -/
theorem doorIV_unitPiece_l1Mass_eq_length_export {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.l1Mass zs = zs.length :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.l1Mass_eq_length_of_forall_norm_one h

/-- **[Lane 1 unit-piece angular deficit]** For unit-modulus phase pieces, the squared resultant
loses exactly twice the total pairwise angular deficit from `(#pieces)²`. This is the concrete
identity `|η_b|² = n² - 2D(b)` for the Door-IV monomial pieces. No CORE bound is claimed. -/
theorem doorIV_unitPiece_norm_sum_sq_eq_length_sq_sub_two_deficit_export {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 = (zs.length : ℝ) ^ 2 -
      2 * _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_eq_length_sq_sub_two_totalPairDeficit_of_unit
    h

/-- **[Lane 1 unit-piece threshold reduction]** For unit pieces, a squared-resultant ceiling `T` is
exactly the lower bound `D ≥ ((#pieces)² - T)/2` on total pairwise angular deficit. The prize burden
is therefore the arithmetic task of forcing the worst-b unit-piece deficit near its ceiling. -/
theorem doorIV_unitPiece_norm_sum_sq_le_iff_deficit_ge_export {zs : List ℂ} (T : ℝ)
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 ≤ T ↔
      ((zs.length : ℝ) ^ 2 - T) / 2 ≤
        _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_le_iff_totalPairDeficit_ge_of_unit
    T h

/-- **[Lane 1 unit-piece deficit ceiling]** The total pairwise angular deficit of unit pieces is at
most `(#pieces)²/2`, so the prize-scale deficit target sits just below this sharp generic ceiling.
This is only accounting, not an anti-concentration estimate. -/
theorem doorIV_unitPiece_totalPairDeficit_le_length_sq_div_two_export {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs ≤
      (zs.length : ℝ) ^ 2 / 2 :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.totalPairDeficit_le_length_sq_div_two_of_unit
    h

/-- **[Lane 1 normalized unit-piece deficit]** For a nonempty list of unit pieces, the normalized
`deficitFraction` is exactly `2D/(#pieces)²`, i.e. the complement of normalized squared coherence.
The prize is equivalently a near-one lower bound on this finite worst-b deficit fraction. -/
theorem doorIV_unitPiece_deficitFraction_eq_two_mul_totalPairDeficit_div_export {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) (hne : zs ≠ []) :
    _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.deficitFraction zs =
      2 * _root_.ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit zs /
        (zs.length : ℝ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.deficitFraction_eq_two_mul_totalPairDeficit_div
    h hne

/-- **[Lane 1 normalized unit-piece threshold]** Bounding normalized squared resultant by `ε` is
exactly forcing the deficit fraction above `1 - ε`. This names the no-slack normalized form of the
Door-IV worst-b prize burden; the missing content remains the arithmetic lower bound. -/
theorem doorIV_unitPiece_norm_sum_sq_div_le_iff_deficitFraction_ge_export {zs : List ℂ} (ε : ℝ) :
    ‖zs.sum‖ ^ 2 / (zs.length : ℝ) ^ 2 ≤ ε ↔
      1 - ε ≤ _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.deficitFraction zs :=
  _root_.ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_div_le_iff_deficitFraction_ge ε

#print axioms doorIV_unitPiece_l1Mass_eq_length_export
#print axioms doorIV_unitPiece_norm_sum_sq_eq_length_sq_sub_two_deficit_export
#print axioms doorIV_unitPiece_norm_sum_sq_le_iff_deficit_ge_export
#print axioms doorIV_unitPiece_totalPairDeficit_le_length_sq_div_two_export
#print axioms doorIV_unitPiece_deficitFraction_eq_two_mul_totalPairDeficit_div_export
#print axioms doorIV_unitPiece_norm_sum_sq_div_le_iff_deficitFraction_ge_export

/-- **[Lane 3 floor-route constraint — §9 bad-prime localization]** For the #464 §9 `n=32` defect
core `S(u) = u⁴ − 196u³ + 4486u² − 21700u + 1` (`disc(S) = 2⁴¹·17²·257²`): the disc-ramification
set `{17, 257}` (primes dividing the discriminant, where `S`'s mod-`p` root-count drops from the
generic 4 to 3) is DISJOINT from the §9 floor-bad prime `97 = ` least prime `≡ 1 (mod 32)` (which is
unramified — `97 ∤ disc` — with the full 4 roots mod 97, and `17 ≢ 1 mod 32`, `257 ≠ 97`). Hence the
discriminant / ramification locus of the defect resultant does NOT identify the floor-bad prime: a
"ramified ⟹ bad" reading of the off-BGK floor route is refuted by explicit finite arithmetic. The
floor-bad selector is the least-prime-in-AP object, a disjoint phenomenon (cf.
`_AvD2_LinnikWindowCountRequired`: Linnik existence ⊬ divisibility). No CORE / cancellation /
completion / moment / capacity claim; CORE remains OPEN. -/
theorem floorBad_disjoint_from_defect_ramification_export :
    (17 ∣ FloorBadRamif.discS ∧ FloorBadRamif.rootCountMod 17 = 3) ∧
    (257 ∣ FloorBadRamif.discS ∧ FloorBadRamif.rootCountMod 257 = 3) ∧
    ((97 : ℕ) % 32 = 1 ∧ ¬ (97 ∣ FloorBadRamif.discS) ∧ FloorBadRamif.rootCountMod 97 = 4) ∧
    ((17 : ℕ) % 32 ≠ 1) ∧ ((257 : ℕ) % 32 = 1 ∧ (257 : ℕ) ≠ 97) :=
  FloorBadRamif.floorBad_disjoint_from_ramification

#print axioms floorBad_disjoint_from_defect_ramification_export

/-- **[Lane 3 floor-route constraint — §9 bad-prime 0-dimensionality / tower-invariance]** For the
#464 §9 `n=8`/`n=32` defect tower: the `n=32` defect polynomial `R³²(g) = g¹⁶ − 196g¹² + 4486g⁸ −
21700g⁴ + 1` is EXACTLY the `n=8` excess quartic `S(u) = u⁴ − 196u³ + 4486u² − 21700u + 1` composed
with the subgroup-dilation `u = g⁴` (the `(p−1)/n` exponent step), `S` has a UNIT constant term
`S(0)=1`, and consequently the odd-prime ramification support of `disc(S)` and of `disc(R³²)` is the
*same* fixed set `{17, 257}` (each is `17^a·257^b`; the dilation adds no new odd prime BECAUSE the
constant term is a unit). So the §9 bad-prime *ramification* locus is a fixed finite set that does NOT
grow with the tower level — a kernel-checked backbone for the dossier's "0-dimensional / flat-in-`p`"
characterization of the bad-prime set, *forced by the unit constant term*. Distinct from
`floorBad_disjoint_from_defect_ramification_export` (which pins floor-bad `97` ∉ `{17,257}`; this
pins the ramification SET is tower-invariant). No CORE / cancellation / completion / moment /
capacity claim; CORE remains OPEN. -/
theorem floorBad_defect_ramification_tower_invariant_export :
    (∀ g : ℤ, FloorBadTower.R32 g = FloorBadTower.S (g ^ 4)) ∧
    (FloorBadTower.S (0 : ℤ) = 1) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ FloorBadTower.discS → q = 17 ∨ q = 257) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ FloorBadTower.discR32 → q = 17 ∨ q = 257) :=
  FloorBadTower.defect_ramification_tower_invariant

#print axioms floorBad_defect_ramification_tower_invariant_export


/-- **[obstruction, DoorIVTowerSlackNonAssemblable — door-(iv) Lane-1/3]** The empirical
min-over-cosets tower slack count `K_min` is the wrong object for bounding the worst-frequency period:
its product is **below** every honest single-chain product, so a small min-product is only a lower bound,
not an upper bound.  The concrete two-level witness shows the min product can be strictly below the
maximally coherent `[1,1]` chain by mixing sibling branches, and the honest chain product, when equal to
the period ratio, is tautological rather than a new saving.  This makes the non-assemblability of the
observed `K_min` growth citable without claiming CORE, cancellation, completion, moment-saving, or
capacity. -/
theorem doorIV_towerSlack_nonassemblable_package_export
    (T : DoorIVTowerSlackNonAssemblable.CoherenceTable) (sel : List ℝ)
    (hlen : T.length = sel.length)
    (hmem : ∀ i (hi : i < T.length),
      sel.get ⟨i, hlen ▸ hi⟩ ∈ T.get ⟨i, hi⟩)
    (hmin_nonneg : ∀ lvl ∈ T, 0 ≤ lvl.foldr min 1)
    (hsel_nonneg : ∀ x ∈ sel, 0 ≤ x) {r : ℝ}
    (hr : DoorIVTowerSlackNonAssemblable.chainProd sel = r) :
    (DoorIVTowerSlackNonAssemblable.minProd T ≤
        DoorIVTowerSlackNonAssemblable.chainProd sel) ∧
    (DoorIVTowerSlackNonAssemblable.minProd [[1, 0], [0, 1]] = 0 ∧
      DoorIVTowerSlackNonAssemblable.chainProd [1, 1] = 1 ∧
      DoorIVTowerSlackNonAssemblable.minProd [[1, 0], [0, 1]] <
        DoorIVTowerSlackNonAssemblable.chainProd [1, 1]) ∧
    (r ≤ DoorIVTowerSlackNonAssemblable.chainProd sel) :=
  ⟨DoorIVTowerSlackNonAssemblable.minProd_le_chainProd T sel hlen hmem hmin_nonneg hsel_nonneg,
   DoorIVTowerSlackNonAssemblable.minProd_strictly_below_topcoherent_chain,
   DoorIVTowerSlackNonAssemblable.chainProd_eq_period_ratio_no_saving sel r hr⟩

#print axioms doorIV_towerSlack_nonassemblable_package_export

/-- **[obstruction, DoorIVWorstBCoherentImbalance — door-(iv) Lane-1/3]** At the **true** worst frequency
the two index-2 coset-halves `A_{b*}, B_{b*}` of `η_{b*} = Σ_{y∈μ_n} e_p(b*·y)` are COHERENT
(`ρ(b*)=1`, `‖A+B‖ = ‖A‖+‖B‖`, the same-ray fact — probe deficit `1−ρ(b*)` identically `0`,
`∠(A,B)=0` to machine precision, `n=16..256`) yet STRICTLY IMBALANCED (`‖A‖ ≠ ‖B‖`; full-coset-scan
balance `r(b*) = 0.89 / 0.61 / 0.78` at `n=16/32/64`, bounded away from `1`, correcting the earlier
*sampled* probe's `r→0.99` reading which was a sampling artifact). Under this coherent-imbalanced
regime the period norm is **strictly below** the symmetric ceiling `‖A+B‖ < 2·max(‖A‖,‖B‖)`, with the
over-count `2·max − ‖A+B‖ = max − min > 0` equal to the half-mass imbalance. Contrapositively, any
descent step that uses the symmetric identity `‖A+B‖ = 2·max(‖A‖,‖B‖)` *forces* `‖A‖ = ‖B‖`, which the
true worst-`b` violates — so the balanced-symmetric "÷2" descent is INAPPLICABLE at the adversarial
frequency and the dyadic recursion the prize reduces to is genuinely asymmetric. Distinct from
`_DoorIVHalfMassBalanceAtArgmax` (which proves the *conditional* balanced identities `‖A+B‖=2‖A‖`); this
pins that the conditioning hypothesis FAILS at the real argmax. No CORE / cancellation / completion /
moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_worstB_coherent_imbalance_breaks_symmetric_descent_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hne : ‖A‖ ≠ ‖B‖) :
    (‖A + B‖ < 2 * max ‖A‖ ‖B‖) ∧
    (2 * max ‖A‖ ‖B‖ - ‖A + B‖ = max ‖A‖ ‖B‖ - min ‖A‖ ‖B‖) ∧
    (∀ (_h : ‖A + B‖ = 2 * max ‖A‖ ‖B‖), ‖A‖ = ‖B‖) :=
  ⟨DoorIVWorstBCoherentImbalance.norm_lt_two_mul_max_of_coherent_imbalanced hcoh hne,
   DoorIVWorstBCoherentImbalance.two_mul_max_sub_norm_eq_imbalance hcoh,
   fun h => DoorIVWorstBCoherentImbalance.coherent_norm_eq_two_mul_max_forces_balance hcoh h⟩

#print axioms doorIV_worstB_coherent_imbalance_breaks_symmetric_descent_export

/-- **[obstruction, DoorIVWorstBCoherentImbalance — normalized ratio form]** Scale-free companion to
`doorIV_worstB_coherent_imbalance_breaks_symmetric_descent_export`: under coherence and a positive
heavier half, the ratio to the balanced symmetric ceiling is exactly
`(1 + min/max)/2`; if the halves are imbalanced, this ratio is strictly below `1`.  This is the
citable normalized form of the true-worst-`b` verdict: coherence `ρ=1` does not authorize the balanced
`÷2` recursion unless the magnitudes are also equal. No CORE upper bound. -/
theorem doorIV_worstB_coherent_imbalance_normalized_ratio_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hmax : 0 < max ‖A‖ ‖B‖) (hne : ‖A‖ ≠ ‖B‖) :
    (‖A + B‖ / (2 * max ‖A‖ ‖B‖)
        = (1 + min ‖A‖ ‖B‖ / max ‖A‖ ‖B‖) / 2) ∧
      ‖A + B‖ / (2 * max ‖A‖ ‖B‖) < 1 :=
  ⟨DoorIVWorstBCoherentImbalance.coherent_norm_div_two_mul_max_eq_avg_ratio hcoh hmax,
   DoorIVWorstBCoherentImbalance.coherent_imbalanced_ratio_lt_one hcoh hmax hne⟩

#print axioms doorIV_worstB_coherent_imbalance_normalized_ratio_export

/-- **[obstruction, DoorIVWorstBImbalanceBand — door-(iv) Lane-1/3]** If the coherent worst-frequency
half split sits in a stationary balance band `rlo·H ≤ min ≤ rhi·H`, then it has proportional gaps from
BOTH dead endpoints: it exceeds the single heavier-half model by at least `rlo·H`, and the symmetric
`2H` ceiling over-counts it by at least `(1-rhi)·H`.  This packages the robust probe verdict that the
worst-`b` half split is neither degenerate-to-one nor a `√`-thinning mechanism: it is only an `O(1)`
reshuffle around the heavier-half scale.  No CORE / cancellation / completion / moment / capacity claim;
CORE remains OPEN. -/
theorem doorIV_worstB_imbalance_stationary_band_endpoint_gap_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {rlo rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖)
    (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    rlo * max ‖A‖ ‖B‖ ≤ ‖A + B‖ - max ‖A‖ ‖B‖ ∧
      (1 - rhi) * max ‖A‖ ‖B‖ ≤ 2 * max ‖A‖ ‖B‖ - ‖A + B‖ :=
  ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.stationary_band_endpoint_gap_bounds
    hcoh hlo hhi

#print axioms doorIV_worstB_imbalance_stationary_band_endpoint_gap_export


/-- **[obstruction, DoorIVWorstBPartitionDepthBand — door-(iv) Lane-1/3]** At any coherent `k`-piece
dyadic partition, if `i₀` is a heaviest piece `H` and every other piece still carries at least
`rlo·H`, then the aggregate exceeds the single-piece endpoint by at least `(k-1)·rlo·H`, expressed as
`(s.erase i₀).card * (rlo*H) ≤ ‖Σ Q i‖ - H`.  This is the probe-facing quantitative form of
partition-depth non-degeneration: a coherent dyadic refinement cannot be treated as one surviving
piece while the lower band persists.  No CORE / cancellation / completion / moment / capacity claim;
CORE remains OPEN. -/
theorem doorIV_partitionDepth_lower_band_slack_over_single_export
    {ι E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E]
    {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖)
    (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H)
    (hlb : ∀ i ∈ s.erase i₀, rlo * H ≤ ‖Q i‖) :
    (s.erase i₀).card * (rlo * H) ≤ ‖∑ i ∈ s, Q i‖ - H :=
  ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.lower_band_slack_over_single_ge
    hcoh hi₀ hH hlb

#print axioms doorIV_partitionDepth_lower_band_slack_over_single_export

/-! **[obstruction, DoorIVPhaseCurvatureGeneric — door-(iv) Lane-1/3]** The discrete-curvature
small-ball lever has both probe-facing failures bundled in one permanent export.  If the cyclic
second-difference map is injective, then its distinct-value set has the maximal possible cardinality
`|ι|`, so no bounded-curvature budget `C < |ι|` can hold.  If the same curvature statistic also agrees
at the worst and a generic frequency, then no threshold separates that worst/generic pair.  Hence this
curvature statistic is simultaneously non-collapsed and frequency-blind: it cannot be the missing
thinness-essential Door-IV anti-concentration input.  No CORE / cancellation / completion / moment /
capacity claim; CORE remains OPEN. -/
theorem doorIV_phase_curvature_generic_dead_export
    {ι : Type*} [Fintype ι] {β : Type*}
    (d : ι → ℤ) (hinj : Function.Injective d)
    (s : β → ℕ) (bstar b0 : β)
    (hblind : ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric.FrequencyBlind s bstar b0) :
    (ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric.secondDiffSet d).card = Fintype.card ι ∧
      (∀ C : ℕ, C < Fintype.card ι →
        ¬ (ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric.secondDiffSet d).card ≤ C) ∧
      (∀ t : ℕ, ¬ (t ≤ s bstar ∧ s b0 < t)) :=
by
  classical
  exact ArkLib.ProximityGap.Frontier.DoorIVPhaseCurvatureGeneric.doorIV_phaseCurvature_dead
    d hinj s bstar b0 hblind

#print axioms doorIV_phase_curvature_generic_dead_export

/-- **[obstruction, DoorIVGapSpectrumFullRank — door-(iv) Lane-1/3]** The gap-spectrum probe
is recorded as a citable full-rank obstruction.  If the worst-frequency rank is full (`N-1`) and
is at least the generic rank, then no low-rank budget below `N-1` can hold at the worst frequency,
and no threshold can select the worst frequency as the low-rank one.  This is a negative structural
lemma only: no CORE / cancellation / completion / moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_gap_spectrum_full_rank_dead_export {N genericRank worstRank : ℕ}
    (hfull : worstRank = N - 1) (hN : 1 ≤ N) (hle : genericRank ≤ worstRank) :
    (∀ C : ℕ, C < N - 1 → ¬ (worstRank ≤ C)) ∧
      genericRank ≤ N - 1 ∧
      (∀ t : ℕ, ¬ (worstRank < t ∧ t ≤ genericRank)) :=
  ArkLib.ProximityGap.Frontier.DoorIVGapSpectrumFullRank.doorIV_gapSpectrum_dead hfull hN hle

#print axioms doorIV_gap_spectrum_full_rank_dead_export

/-- **[obstruction, DoorIVGapNoLongRun — door-(iv) Lane-1/3]** The local near-AP gap-run probe is
recorded as a citable obstruction.  A worst-frequency longest monotone run bounded by `K` has no
run of any target length above `K`, stays below every ambient `n > K`, and if it equals the generic
run-length then no threshold selects the worst frequency as the long-run one.  This is a negative
structural lemma only: no CORE / cancellation / completion / moment / capacity claim; CORE remains
OPEN. -/
theorem doorIV_gap_no_long_run_dead_export {Lworst Lgen K n : ℕ}
    (hbound : Lworst ≤ K) (hKn : K < n) (heq : Lworst = Lgen) :
    (∀ L0 : ℕ, K < L0 → Lworst < L0) ∧
      Lworst < n ∧
      (∀ t : ℕ, ¬ (Lgen < t ∧ t ≤ Lworst)) :=
  ArkLib.ProximityGap.Frontier.DoorIVGapNoLongRun.doorIV_gapNoLongRun_dead hbound hKn heq

#print axioms doorIV_gap_no_long_run_dead_export

/-- **[obstruction, DoorIVWorstBPartitionDepthBand — door-(iv) Lane-1/3]** For any coherent `k`-piece
worst-frequency partition satisfying the stationary lower band and having at least one strict-under-max
piece, the measured aggregate inflation `F_k = M/H` is strictly interior: `1 < F_k < k`.  This makes
the partition-depth-invariant probe conclusion citable at the exact ratio level: no single-piece
collapse and no balanced full-`k` thinning at any dyadic refinement.  No CORE / cancellation /
completion / moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_worstB_partition_depth_inflation_ratio_strictly_between_export
    {ι E : Type*} [SeminormedAddCommGroup E]
    {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ i₁ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖)
    (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H) (hrlo : 0 < rlo) (hHpos : 0 < H) (htwo : 2 ≤ s.card)
    (hlb : ∀ i ∈ s, rlo * H ≤ ‖Q i‖) (hub : ∀ i ∈ s, ‖Q i‖ ≤ H)
    (hi₁ : i₁ ∈ s) (hstrict : ‖Q i₁‖ < H) :
    1 < ‖∑ i ∈ s, Q i‖ / H ∧ ‖∑ i ∈ s, Q i‖ / H < (s.card : ℝ) :=
by
  classical
  exact ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.one_lt_norm_div_max_and_norm_div_max_lt_card
    hcoh hi₀ hH hrlo hHpos htwo hlb hub hi₁ hstrict

#print axioms doorIV_worstB_partition_depth_inflation_ratio_strictly_between_export

/-- **[obstruction, DoorIVWorstBPartitionDepthBand — door-(iv) Lane-1/3]** For a coherent `k`-piece
coset partition, the surplus over a certified heaviest piece is exactly the tail mass after erasing
that piece, and any lower band on the tail forces a literal `(k-1)·rlo·H` surplus. This is the
partition-depth version of the stationary-band endpoint gap: dyadic refinement gives no hidden
anti-concentration beyond the mass already present in the non-heaviest tail. No CORE / cancellation /
completion / moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_partitionDepth_tail_slack_budget_export
    {ι E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E]
    {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hi₀ : i₀ ∈ s)
    (hH : ‖Q i₀‖ = H) (hlb_tail : ∀ i ∈ s.erase i₀, rlo * H ≤ ‖Q i‖) :
    (‖∑ i ∈ s, Q i‖ - H = ∑ i ∈ s.erase i₀, ‖Q i‖) ∧
      ((s.card - 1 : ℕ) : ℝ) * (rlo * H) ≤ ‖∑ i ∈ s, Q i‖ - H := by
  have htail : ‖∑ i ∈ s, Q i‖ - H = ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    rw [hcoh]
    have hsplit : (∑ i ∈ s, ‖Q i‖) = ‖Q i₀‖ + ∑ i ∈ s.erase i₀, ‖Q i‖ := by
      rw [← Finset.sum_erase_add s _ hi₀]; ring
    rw [hsplit, hH]
    ring
  refine ⟨htail, ?_⟩
  rw [htail]
  calc
    ((s.card - 1 : ℕ) : ℝ) * (rlo * H)
        = ((s.erase i₀).card : ℝ) * (rlo * H) := by
          rw [Finset.card_erase_of_mem hi₀]
    _ = ∑ _i ∈ s.erase i₀, rlo * H := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s.erase i₀, ‖Q i‖ := Finset.sum_le_sum hlb_tail

#print axioms doorIV_partitionDepth_tail_slack_budget_export

/-- **[obstruction, DoorIVWorstBPartitionDepthBand — door-(iv) Lane-1/3]** If a coherent `k`-piece
partition has surplus over the certified heaviest piece strictly below the `(k-1)·rlo·H` lower-band
floor, then some non-heaviest tail piece is genuinely below `rlo·H`. So any attempted improvement over
the partition-depth floor must prove tail collapse; refinement depth alone cannot supply it. No CORE /
cancellation / completion / moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_partitionDepth_tail_thinness_necessary_export
    {ι E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E]
    {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hi₀ : i₀ ∈ s)
    (hH : ‖Q i₀‖ = H)
    (hshort : ‖∑ i ∈ s, Q i‖ - H < ((s.card - 1 : ℕ) : ℝ) * (rlo * H)) :
    ∃ i ∈ s.erase i₀, ‖Q i‖ < rlo * H := by
  by_contra hnone
  push_neg at hnone
  have hlb_tail : ∀ i ∈ s.erase i₀, rlo * H ≤ ‖Q i‖ := hnone
  have htail : ‖∑ i ∈ s, Q i‖ - H = ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    rw [hcoh]
    have hsplit : (∑ i ∈ s, ‖Q i‖) = ‖Q i₀‖ + ∑ i ∈ s.erase i₀, ‖Q i‖ := by
      rw [← Finset.sum_erase_add s _ hi₀]; ring
    rw [hsplit, hH]
    ring
  have hfloor : ((s.card - 1 : ℕ) : ℝ) * (rlo * H) ≤ ‖∑ i ∈ s, Q i‖ - H := by
    rw [htail]
    calc
      ((s.card - 1 : ℕ) : ℝ) * (rlo * H)
          = ((s.erase i₀).card : ℝ) * (rlo * H) := by
            rw [Finset.card_erase_of_mem hi₀]
      _ = ∑ _i ∈ s.erase i₀, rlo * H := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s.erase i₀, ‖Q i‖ := Finset.sum_le_sum hlb_tail
  linarith

#print axioms doorIV_partitionDepth_tail_thinness_necessary_export

/-- **[obstruction, DoorIVWorstBPerLevelGrowthFloor — door-(iv) Lane-1/3]** Under the measured
coherent-band plus near-worst transfer hypotheses, if the conditional per-level floor satisfies
`√2 < (1+rlo)(1−ε)`, then the dyadic wall cannot satisfy the square-root thinning step
`M(μ_n) ≤ √2·M(μ_{n/2})`.  This pins the exact threshold behind the per-level growth probe: the
observed floor is a lower-bound obstruction to a recursive `√2` descent, not a CORE upper bound or a
cancellation claim. -/
theorem doorIV_worstB_no_sqrt_two_perLevel_thinning_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {rlo ε M₂ : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlb : rlo * ‖A‖ ≤ ‖B‖) (hrlo : 0 ≤ rlo)
    (htransfer : (1 - ε) * M₂ ≤ ‖A‖) (hε : 0 ≤ 1 - ε)
    (hM₂ : 0 < M₂) (hsqrt : Real.sqrt 2 < (1 + rlo) * (1 - ε)) :
    ¬ ‖A + B‖ ≤ Real.sqrt 2 * M₂ :=
  ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.no_sqrt_two_perLevel_thinning
    hcoh hlb hrlo htransfer hε hM₂ hsqrt

#print axioms doorIV_worstB_no_sqrt_two_perLevel_thinning_export


/-! **[obstruction, DoorIVGreedyHeavierHalfDescent — door-(iv) Lane-1/3]** The greedy heavier-half
descent found by the probe is an exact reconstruction at the worst frequency, but as a proof lever it
has two kernel-checkable failures. First, a product of factors `1+rᵢ` with `rᵢ ∈ [0,1]` is bounded only
by the trivial `2^a` ceiling, is always `≥1`, and any capped levels contribute the full `2^|S|` floor;
so a `√n` thinning would have to be a genuinely new log-product estimate, not a consequence of the
reconstruction. Second, the fixed-frequency greedy subvalue is merely one competitor below the true
sub-period maximum, and when the downstream argmax is non-nested (`subMag b < M₂`) it is strictly NOT a
majorant (`0 < M₂-subMag b`, `¬ M₂≤subMag b`). Thus the 1-D descent transfers the wall and cannot
telescope upward. No CORE / cancellation / completion / moment / capacity claim; CORE remains OPEN. -/
theorem doorIV_greedy_heavier_half_descent_dead_lever_export {a : ℕ} (r : Fin a → ℝ)
    (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1) (S : Finset (Fin a))
    (hS : ∀ i ∈ S, r i = 1) {ι : Type*} (subMag : ι → ℝ) (M₂ : ℝ) (b : ι)
    (hmax : ∀ c, subMag c ≤ M₂) (hstrict : subMag b < M₂) :
    ((∏ i, (1 + r i)) ≤ 2 ^ a) ∧
    (1 ≤ ∏ i, (1 + r i)) ∧
    ((2 : ℝ) ^ S.card ≤ ∏ i, (1 + r i)) ∧
    (subMag b ≤ M₂) ∧
    (0 < M₂ - subMag b) ∧
    ¬ (M₂ ≤ subMag b) :=
  ⟨DoorIVGreedyHeavierHalfDescent.greedyProduct_le_two_pow a r h0 h1,
   DoorIVGreedyHeavierHalfDescent.one_le_greedyProduct a r h0,
   DoorIVGreedyHeavierHalfDescent.greedyProduct_ge_two_pow_of_capped r h0 S hS,
   DoorIVGreedyHeavierHalfDescent.greedyValue_le_subMax subMag M₂ b hmax,
   (DoorIVGreedyHeavierHalfDescent.descent_not_majorant_of_strict subMag M₂ b hstrict).1,
   (DoorIVGreedyHeavierHalfDescent.descent_not_majorant_of_strict subMag M₂ b hstrict).2⟩

#print axioms doorIV_greedy_heavier_half_descent_dead_lever_export


/-- **[Lane 3 worst-b spike constraint]** A b-side near-maximum/spike-count argument pays exactly
the centered second moment: the number of indices above a threshold `μ+d`, multiplied by `d²`, is
bounded by `Σ (xᵢ-μ)²`.  Thus proving the worst frequency is isolated, or that few `b` are near it,
routes through the moment object rather than opening a new door-(iv) anti-concentration lever. -/
theorem doorIV_worstB_spike_count_mul_sq_le_centered_sndMoment_export
    {ι : Type*} (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d) :
    ((s.filter (fun i => μ + d ≤ x i)).card : ℝ) * d ^ 2
      ≤ ∑ i ∈ s, (x i - μ) ^ 2 :=
  ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_mul_sq_le_centered_sndMoment
    x s μ d hd

/-- **[Lane 3 worst-b spike constraint]** Division form of the same wall: the above-threshold count
is at most the centered second moment divided by `d²`.  Any selector/count proof of a worst-b spike
therefore consumes second-moment budget, i.e. the already-dead moment/BGK route. -/
theorem doorIV_worstB_spike_count_le_sndMoment_div_export
    {ι : Type*} (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d) :
    ((s.filter (fun i => μ + d ≤ x i)).card : ℝ)
      ≤ (∑ i ∈ s, (x i - μ) ^ 2) / d ^ 2 :=
  ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_le_sndMoment_div
    x s μ d hd

/-- **[Lane 3 worst-b spike constraint]** Even one adversarial spike at height `μ+d` already forces
the centered second moment to be at least `d²`.  Isolating the worst `b` is therefore not independent
information: the spike itself has already paid the moment cost. -/
theorem doorIV_worstB_sndMoment_ge_sq_of_exists_threshold_export
    {ι : Type*} (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d)
    (hex : ∃ i ∈ s, μ + d ≤ x i) :
    d ^ 2 ≤ ∑ i ∈ s, (x i - μ) ^ 2 :=
  ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.sndMoment_ge_sq_of_exists_threshold
    x s μ d hd hex

/-- **[Lane 3 worst-b spike contrapositive]** If the centered second-moment budget is below `d²`,
then no `b`-side value can reach the threshold `μ+d`.  Thus a claimed isolated threshold spike is not
free arithmetic information: even one hit forces a `d²` moment cost, so the route is moment/BGK-bound. -/
theorem doorIV_worstB_threshold_count_eq_zero_of_sndMoment_lt_sq_export
    {ι : Type*} (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d)
    (hsmall : (∑ i ∈ s, (x i - μ) ^ 2) < d ^ 2) :
    (s.filter (fun i => μ + d ≤ x i)).card = 0 :=
  ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_eq_zero_of_sndMoment_lt_sq
    x s μ d hd hsmall

#print axioms doorIV_worstB_spike_count_mul_sq_le_centered_sndMoment_export
#print axioms doorIV_worstB_spike_count_le_sndMoment_div_export
#print axioms doorIV_worstB_sndMoment_ge_sq_of_exists_threshold_export
#print axioms doorIV_worstB_threshold_count_eq_zero_of_sndMoment_lt_sq_export

/-- **[Lane 3 resonance spike/off-diagonal constraint]** A one-step squared-spectrum spike `d`
above the Parseval mean forces `d² ≤ m · Re Off(2)`.  This pins the exact localized agreement
budget paid by any proposed worst-frequency spike selector. -/
theorem doorIV_resonance_spike_cost_le_offDiag_two_re_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m,
      ((m : ℝ) - 1) + d
        ≤ ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
            (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2) :
    d ^ 2 ≤ (m : ℝ) *
      (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re :=
  ArkLib.ProximityGap.GaussPhaseResonance.spike_cost_le_offDiag_two_re u hu d hd hspike

/-- **[Lane 3 resonance spike/off-diagonal constraint]** Normalized form: a spike of height `d`
forces the named depth-two agreement object to be at least `d² / m`. -/
theorem doorIV_resonance_offDiag_two_re_ge_spike_sq_div_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m,
      ((m : ℝ) - 1) + d
        ≤ ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
            (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2) :
    d ^ 2 / (m : ℝ)
      ≤ (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re :=
  ArkLib.ProximityGap.GaussPhaseResonance.offDiag_two_re_ge_spike_sq_div u hu d hd hspike

/-- **[Lane 3 resonance spike/off-diagonal constraint]** Count form: the number of frequencies
spiking `d` above the mean is bounded by `m · Re Off(2) / d²`.  Selector/count routes therefore
consume the same localized agreement budget. -/
theorem doorIV_resonance_spike_count_le_offDiag_two_re_div_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d) :
    (((Finset.univ : Finset (ZMod m)).filter
        (fun k => ((m : ℝ) - 1) + d
          ≤ ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
              (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2)).card : ℝ)
      ≤ (m : ℝ) *
        (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re / d ^ 2 :=
  ArkLib.ProximityGap.GaussPhaseResonance.spike_count_le_offDiag_two_re_div u hu d hd

/-- **[Lane 3 resonance spike/off-diagonal constraint]** Contrapositive count form: if the
localized depth-two agreement budget is below `d²`, no frequency can spike `d` above the mean. -/
theorem doorIV_resonance_spike_count_eq_zero_of_offDiag_two_re_lt_sq_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d)
    (hsmall : (m : ℝ) *
      (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re < d ^ 2) :
    ((Finset.univ : Finset (ZMod m)).filter
        (fun k => ((m : ℝ) - 1) + d
          ≤ ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
              (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2)).card = 0 :=
  ArkLib.ProximityGap.GaussPhaseResonance.spike_count_eq_zero_of_offDiag_two_re_lt_sq
    u hu d hd hsmall

/-- **[Lane 3 resonance tower shape]** Every consecutive growth ratio of the named door-(iv)
resonance tower is at least the Parseval floor `m−1`: `(m−1) ≤ T(r+1)/T(r)`.  This pins the
Chebyshev lower step directly at the ratio level used by the log-convex tower: no proof can obtain
a prize-scale saving from a local below-floor rung. -/
theorem doorIV_resonance_ratio_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    ((m : ℝ) - 1) ≤
      ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u (r + 1) /
        ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u r :=
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_floor u hu hm r

/-- **[Lane 3 resonance tower shape]** No unit-phase resonance tower in the `m ≥ 2` regime can have
a consecutive growth ratio strictly below the Parseval floor `m−1`.  Constraint form of the ratio
floor, useful as a refuted-lever guard against proposed cheap local tower dips. -/
theorem doorIV_not_resonance_ratio_lt_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    ¬ ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u (r + 1) /
        ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u r < ((m : ℝ) - 1) :=
  ArkLib.ProximityGap.GaussPhaseResonance.not_resonanceMoment_ratio_lt_floor u hu hm r

#print axioms doorIV_resonance_ratio_floor_export
#print axioms doorIV_not_resonance_ratio_lt_floor_export

/-- **[Lane 3 resonance tower shape]** Endpoint rigidity for the ratio sandwich: if every squared
kernel spectral weight is capped by the Parseval mean `m−1`, then every consecutive tower ratio is
forced to equal `m−1` exactly.  This pins the mean-cap endpoint as rigidity, not prize cancellation. -/
theorem doorIV_resonance_ratio_eq_floor_of_specMaxSq_le_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ)
    (hcap : ∀ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 ≤ (m : ℝ) - 1) :
    ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u (r + 1) /
        ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u r = (m : ℝ) - 1 :=
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_eq_base_of_specMaxSq_le_base
    u hu hm r hcap

#print axioms doorIV_resonance_ratio_eq_floor_of_specMaxSq_le_floor_export
/-- **[Lane 3 resonance spectral-floor endpoint]** A realised squared spectral maximum cannot sit
below the Parseval floor `m−1`.  This is the endpoint compatibility condition forced by the
growth-ratio sandwich: the actual worst frequency is at least the spectral mean.  Lower-side
constraint only, not an upper bound on the BGK object. -/
theorem doorIV_realised_specMaxSq_ge_parseval_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 ≤
        ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2) :
    (m : ℝ) - 1 ≤
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
        (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2 :=
  ArkLib.ProximityGap.GaussPhaseResonance.realised_specMaxSq_ge_parseval_floor u hu hm b₀ hb₀

/-- **[Lane 3 resonance spectral-floor endpoint]** Contrapositive guard: no realised
worst-frequency squared mass can be strictly below `m−1`.  Any proposed door-(iv) cap must live
above the Parseval floor; the open work is an upper bound in that range, not a
sub-floor collapse. -/
theorem doorIV_not_realised_specMaxSq_lt_parseval_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 ≤
        ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2) :
    ¬ ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
        (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2 < ((m : ℝ) - 1) :=
  ArkLib.ProximityGap.GaussPhaseResonance.not_realised_specMaxSq_lt_parseval_floor u hu hm b₀ hb₀

#print axioms doorIV_realised_specMaxSq_ge_parseval_floor_export
#print axioms doorIV_not_realised_specMaxSq_lt_parseval_floor_export

/-- **[Lane 3 resonance spectral-floor endpoint]** If a realised worst spectral mass is capped by
`m−1`, then it is exactly `m−1`. The endpoint is rigid: a worst frequency may touch the Parseval
floor, but cannot sit below it. -/
theorem doorIV_realised_specMaxSq_eq_parseval_floor_of_le_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 ≤
        ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2)
    (hle : ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
        (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2 ≤ (m : ℝ) - 1) :
    ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
        (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2 = (m : ℝ) - 1 :=
  ArkLib.ProximityGap.GaussPhaseResonance.realised_specMaxSq_eq_parseval_floor_of_le_floor
    u hu hm b₀ hb₀ hle

/-- **[Lane 3 resonance spectral-floor endpoint]** Realised mean-cap tower rigidity: if an actual
worst frequency is already capped by the Parseval mean, every consecutive tower ratio equals
`m−1`. Thus nontrivial ratio slack forces the realised worst spectral mass above the mean. -/
theorem doorIV_resonance_ratio_eq_floor_of_realised_specMaxSq_le_floor_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 ≤
        ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2)
    (hle : ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
        (ArkLib.ProximityGap.GaussPhaseResonance.dftChar b₀) u‖ ^ 2 ≤ (m : ℝ) - 1) :
    ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u (r + 1) /
        ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment u r = (m : ℝ) - 1 :=
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_eq_base_of_realised_specMaxSq_le_base
    u hu hm r b₀ hb₀ hle

#print axioms doorIV_realised_specMaxSq_eq_parseval_floor_of_le_floor_export
#print axioms doorIV_resonance_ratio_eq_floor_of_realised_specMaxSq_le_floor_export

/-- **[Lane 3 resonance two-sided off-diagonal constraint]** A one-step squared-spectrum dip `d`
below the Parseval mean also forces `d² ≤ m · Re Off(2)`.  Near-flatness must therefore control
both upward spikes and downward holes; either kind of deviation consumes the same named depth-two
agreement budget. -/
theorem doorIV_resonance_dip_cost_le_offDiag_two_re_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d)
    (hdip : ∃ k : ZMod m,
      ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 + d ≤ ((m : ℝ) - 1)) :
    d ^ 2 ≤ (m : ℝ) *
      (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re :=
  ArkLib.ProximityGap.GaussPhaseResonance.dip_cost_le_offDiag_two_re u hu d hd hdip

/-- **[Lane 3 resonance two-sided off-diagonal constraint]** Contrapositive dip form: if the
localized depth-two agreement budget is below `d²`, no frequency can lie `d` below the mean. -/
theorem doorIV_resonance_dip_count_eq_zero_of_offDiag_two_re_lt_sq_export
    {m : ℕ} [NeZero m] (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (d : ℝ) (hd : 0 < d)
    (hsmall : (m : ℝ) *
      (ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag u 2).re < d ^ 2) :
    ((Finset.univ : Finset (ZMod m)).filter
        (fun k => ‖ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum
          (ArkLib.ProximityGap.GaussPhaseResonance.dftChar k) u‖ ^ 2 + d ≤ ((m : ℝ) - 1))).card = 0 :=
  ArkLib.ProximityGap.GaussPhaseResonance.dip_count_eq_zero_of_offDiag_two_re_lt_sq
    u hu d hd hsmall

#print axioms doorIV_resonance_spike_cost_le_offDiag_two_re_export
#print axioms doorIV_resonance_offDiag_two_re_ge_spike_sq_div_export
#print axioms doorIV_resonance_spike_count_le_offDiag_two_re_div_export
#print axioms doorIV_resonance_spike_count_eq_zero_of_offDiag_two_re_lt_sq_export
#print axioms doorIV_resonance_dip_cost_le_offDiag_two_re_export
#print axioms doorIV_resonance_dip_count_eq_zero_of_offDiag_two_re_lt_sq_export

/-- **[Door-IV/G1 exact incidence bound]** The non-symmetric `Z` correction in the even/odd descent
is the root count of the explicit quadratic form `Pp² - X·Qp²`; if that polynomial is nonzero,
Lagrange gives `Z ≤ natDegree(R)`.  This is degree control only, not Gauss-sum cancellation, and it
records the exact algebraic incidence handle left as prose in the A+Z descent rung. -/
theorem doorIV_descentZ_card_le_natDegree_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F} (hR : ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ (ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp).natDegree :=
  ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_natDegree hR B

/-- **[Door-IV/G1 exact incidence bound]** The same `Z` correction is bounded by the explicit word
exponent envelope `1 + 2 * max deg(Pp) deg(Qp)`.  Thus the descent's non-symmetric branch is governed
by word degree/exponent, not by an unproved subgroup-root `O(1)` hope. -/
theorem doorIV_descentZ_card_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F} (hR : ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degBound hR B

/-- **[Door-IV/G1 exact incidence bound]** Indicator-sum consumer form of the exponent-controlled
`Z` bound, matching the summed A+Z descent notation.  This is the usable capstone for downstream
formal reductions: non-symmetric agreement contributes at most `1 + 2·max(deg Pp, deg Qp)`. -/
theorem doorIV_descentZ_indicator_sum_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F} (hR : ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degBound hR B

#print axioms doorIV_descentZ_card_le_natDegree_export
#print axioms doorIV_descentZ_card_le_degBound_export
#print axioms doorIV_descentZ_indicator_sum_le_degBound_export

/-- **[Lane 1 worst-b selector obstruction]** If the frequency statistic is constant on group
orbits, then super-level membership is exactly invariant under every orbit move. A worst-`b`
selector cannot distinguish points inside one multiplicative coset using that statistic. -/
theorem doorIV_worstBCoset_smul_mem_superLevel_iff_export {G β : Type*} [Group G]
    [MulAction G β] {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (c : ℝ) (g : G) {b : β} :
    g • b ∈ DoorIVWorstBCosetClosed.superLevel f c ↔
      b ∈ DoorIVWorstBCosetClosed.superLevel f c :=
  DoorIVWorstBCosetClosed.smul_mem_superLevel_iff_of_orbitConstant hf c g

/-- **[Lane 1 worst-b selector obstruction]** With an invariant involution (the prize case is
`b ↦ -b`), super-level membership is also exactly sign-invariant. The near-max set is sign-closed. -/
theorem doorIV_worstBCoset_sigma_mem_superLevel_iff_export {β : Type*} {f : β → ℝ}
    {σ : β → β} (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) {b : β} :
    σ b ∈ DoorIVWorstBCosetClosed.superLevel f c ↔
      b ∈ DoorIVWorstBCosetClosed.superLevel f c :=
  DoorIVWorstBCosetClosed.sigma_mem_superLevel_iff hσ c

/-- **[Lane 1 worst-b selector obstruction]** Combined coset-plus-sign invariance: applying any
coset move and then the involution neither creates nor destroys near-max membership. This is the
selector-facing form of the coset/sign granularity wall. -/
theorem doorIV_worstBCoset_sigma_smul_mem_superLevel_iff_export {G β : Type*} [Group G]
    [MulAction G β] {f : β → ℝ} {σ : β → β}
    (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) (g : G) {b : β} :
    σ (g • b) ∈ DoorIVWorstBCosetClosed.superLevel f c ↔
      b ∈ DoorIVWorstBCosetClosed.superLevel f c :=
  DoorIVWorstBCosetClosed.sigma_smul_mem_superLevel_iff hf hσ c g

/-- **[Lane 1 worst-b selector obstruction]** Finite cardinal floor: a near-max point forces the
finite super-level set to contain its whole actual orbit image. Thus sub-orbit-sized worst-`b` sets
are impossible unless the orbit itself has collapsed by stabilizers. -/
theorem doorIV_worstBCoset_card_orbitImage_le_superLevelFinset_export {G β : Type*} [Group G]
    [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c) :
    (Finset.univ.image (fun g : G => g • b)).card ≤
      (DoorIVWorstBCosetClosed.superLevelFinset f c).card :=
  DoorIVWorstBCosetClosed.card_orbitImage_le_superLevelFinset hf c hb

/-- **[Lane 1 worst-b selector obstruction]** Signed-fiber cardinal floor: with sign symmetry, a
near-max point forces the whole image `g ↦ σ(g•b)` into the finite super-level set. -/
theorem doorIV_worstBCoset_card_sigmaOrbitImage_le_superLevelFinset_export {G β : Type*} [Group G]
    [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c) :
    (Finset.univ.image (fun g : G => σ (g • b))).card ≤
      (DoorIVWorstBCosetClosed.superLevelFinset f c).card :=
  DoorIVWorstBCosetClosed.card_sigmaOrbitImage_le_superLevelFinset hf hσ c hb

/-- **[Lane 1 worst-b selector obstruction]** Singleton selector collapse: if a finite
super-level set containing `b` is literally a singleton, then the whole actual coset orbit image of
`b` has already collapsed to one point. Thus an isolated worst-`b` selector is only possible after
stabilizers have killed the coset fiber. -/
theorem doorIV_worstBCoset_orbitImage_card_eq_one_of_superLevel_singleton_export
    {G β : Type*} [Group G] [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c)
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card = 1) :
    (Finset.univ.image (fun g : G => g • b)).card = 1 :=
  DoorIVWorstBCosetClosed.orbitImage_card_eq_one_of_superLevelFinset_card_eq_one hf c hb hcard

/-- **[Lane 1 worst-b selector obstruction]** Signed singleton selector collapse: a singleton
near-max set containing `b` forces the signed coset image `g ↦ σ(g•b)` to have cardinal one.  Sign
symmetry cannot produce a point-sized worst-frequency set unless the signed fiber is degenerate. -/
theorem doorIV_worstBCoset_sigmaOrbitImage_card_eq_one_of_superLevel_singleton_export
    {G β : Type*} [Group G] [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c)
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card = 1) :
    (Finset.univ.image (fun g : G => σ (g • b))).card = 1 :=
  DoorIVWorstBCosetClosed.sigmaOrbitImage_card_eq_one_of_superLevelFinset_card_eq_one
    hf hσ c hb hcard

/-- **[Lane 1 worst-b selector obstruction]** Audit contrapositive: if a reported threshold set is
smaller than the actual orbit image of `b`, then `b` cannot be in that threshold set. This pins the
minimum budget any coset-blind worst-frequency selector must pay. -/
theorem doorIV_worstBCoset_not_mem_of_card_lt_orbitImage_export {G β : Type*} [Group G]
    [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card <
      (Finset.univ.image (fun g : G => g • b)).card) :
    ¬ b ∈ DoorIVWorstBCosetClosed.superLevel f c :=
  DoorIVWorstBCosetClosed.not_mem_superLevel_of_card_superLevelFinset_lt_orbitImage hf c hcard

/-- **[Lane 1 worst-b selector obstruction]** Free-orbit version of the cardinal floor: if the orbit
map at `b` injects, one near-max frequency forces at least `|G|` near-max frequencies. A point-sized
or sub-coset-sized worst-`b` selector is impossible in the free case. -/
theorem doorIV_worstBCoset_card_group_le_superLevelFinset_of_free_orbit_export {G β : Type*}
    [Group G] [MulAction G β] [Fintype G] [Fintype β]
    {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c)
    (hfree : ∀ {g h : G}, g • b = h • b → g = h) :
    Fintype.card G ≤ (DoorIVWorstBCosetClosed.superLevelFinset f c).card :=
  DoorIVWorstBCosetClosed.card_group_le_superLevelFinset_of_free_orbit hf c hb hfree

/-- **[Lane 1 worst-b selector obstruction]** Signed audit contrapositive: if a threshold set is
smaller than the actual signed coset fiber of `b`, then `b` cannot be in that threshold set. This is
the signed version of the exact coset-budget wall for worst-frequency selectors. -/
theorem doorIV_worstBCoset_not_mem_of_card_lt_sigmaOrbitImage_export {G β : Type*} [Group G]
    [MulAction G β] [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) {b : β}
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card <
      (Finset.univ.image (fun g : G => σ (g • b))).card) :
    ¬ b ∈ DoorIVWorstBCosetClosed.superLevel f c :=
  DoorIVWorstBCosetClosed.not_mem_superLevel_of_card_superLevelFinset_lt_sigmaOrbitImage hf hσ c hcard

/-- **[Lane 1 worst-b selector obstruction]** Free signed-fiber cardinal floor: if
`g ↦ σ(g•b)` injects, one near-max frequency forces at least `|G|` signed coset mates in the
threshold set. Sign symmetry does not give a cheaper selector; it pays a whole signed fiber. -/
theorem doorIV_worstBCoset_card_group_le_superLevelFinset_of_free_sigma_orbit_export {G β : Type*}
    [Group G] [MulAction G β] [Fintype G] [Fintype β]
    {f : β → ℝ} {σ : β → β} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ DoorIVWorstBCosetClosed.superLevel f c)
    (hfree : ∀ {g h : G}, σ (g • b) = σ (h • b) → g = h) :
    Fintype.card G ≤ (DoorIVWorstBCosetClosed.superLevelFinset f c).card :=
  DoorIVWorstBCosetClosed.card_group_le_superLevelFinset_of_free_sigma_orbit hf hσ c hb hfree

/-- **[Lane 1 worst-b selector obstruction]** Sub-coset threshold no-go: a threshold set with
cardinality below `|G|` contains no point with a free orbit. This exports the direct audit hook for
claims that a coset-blind worst-`b` statistic has isolated a sub-coset-sized near-max set. -/
theorem doorIV_worstBCoset_not_exists_free_orbit_mem_of_card_lt_group_export {G β : Type*}
    [Group G] [MulAction G β] [Fintype G] [Fintype β]
    {f : β → ℝ} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f) (c : ℝ)
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card < Fintype.card G) :
    ¬ ∃ b : β, b ∈ DoorIVWorstBCosetClosed.superLevel f c ∧
      ∀ {g h : G}, g • b = h • b → g = h :=
  DoorIVWorstBCosetClosed.not_exists_free_orbit_mem_of_card_superLevelFinset_lt_group hf c hcard

/-- **[Lane 1 worst-b selector obstruction]** Signed sub-coset threshold no-go: a threshold set with
cardinality below `|G|` contains no point whose signed coset fiber is free. This pins the exact
signed-selector budget obstruction used by worst-`b` arithmetic probes. -/
theorem doorIV_worstBCoset_not_exists_free_sigma_orbit_mem_of_card_lt_group_export {G β : Type*}
    [Group G] [MulAction G β] [Fintype G] [Fintype β]
    {f : β → ℝ} {σ : β → β} (hf : DoorIVWorstBCosetClosed.OrbitConstant (G := G) f)
    (hσ : DoorIVWorstBCosetClosed.InvolutionConstant σ f) (c : ℝ)
    (hcard : (DoorIVWorstBCosetClosed.superLevelFinset f c).card < Fintype.card G) :
    ¬ ∃ b : β, b ∈ DoorIVWorstBCosetClosed.superLevel f c ∧
      ∀ {g h : G}, σ (g • b) = σ (h • b) → g = h :=
  DoorIVWorstBCosetClosed.not_exists_free_sigma_orbit_mem_of_card_superLevelFinset_lt_group hf hσ c hcard

#print axioms doorIV_worstBCoset_smul_mem_superLevel_iff_export
#print axioms doorIV_worstBCoset_sigma_mem_superLevel_iff_export
#print axioms doorIV_worstBCoset_sigma_smul_mem_superLevel_iff_export
#print axioms doorIV_worstBCoset_card_orbitImage_le_superLevelFinset_export
#print axioms doorIV_worstBCoset_card_sigmaOrbitImage_le_superLevelFinset_export
#print axioms doorIV_worstBCoset_orbitImage_card_eq_one_of_superLevel_singleton_export
#print axioms doorIV_worstBCoset_sigmaOrbitImage_card_eq_one_of_superLevel_singleton_export
#print axioms doorIV_worstBCoset_not_mem_of_card_lt_orbitImage_export
#print axioms doorIV_worstBCoset_card_group_le_superLevelFinset_of_free_orbit_export
#print axioms doorIV_worstBCoset_not_mem_of_card_lt_sigmaOrbitImage_export
#print axioms doorIV_worstBCoset_card_group_le_superLevelFinset_of_free_sigma_orbit_export
#print axioms doorIV_worstBCoset_not_exists_free_orbit_mem_of_card_lt_group_export
#print axioms doorIV_worstBCoset_not_exists_free_sigma_orbit_mem_of_card_lt_group_export

/-- Door-IV spectrum localization export: if the one-step kernel spectrum vanishes at a
frequency, then every positive depth spectrum vanishes there too.  This is an exact
algebraic annihilation criterion only, not a Gauss-period bound. -/
theorem doorIV_phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero_export
    {m : ℕ} [NeZero m] (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y)
    (hk : ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum ψ u = 0) :
    ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum ψ u (r + 1) = 0 :=
  ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero
    ψ u r hmul hk

/-- Door-IV spectrum localization export: any nonzero positive-depth spectrum certifies
that the one-step kernel spectrum is nonzero.  The prize-relevant obligation remains an
upper bound on that one-step kernel. -/
theorem doorIV_kernelSpectrum_ne_zero_of_phaseSpectrum_succ_ne_zero_export
    {m : ℕ} [NeZero m] (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y)
    (hspec : ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum ψ u (r + 1) ≠ 0) :
    ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum ψ u ≠ 0 :=
  ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_ne_zero_of_phaseSpectrum_succ_ne_zero
    ψ u r hmul hspec

#print axioms doorIV_phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero_export
#print axioms doorIV_kernelSpectrum_ne_zero_of_phaseSpectrum_succ_ne_zero_export

/-- Door-IV Lane-2 capstone export: the dimensionless Shaw bound is equivalent to the raw
prize-floor scalar bound, with the same constant, whenever the floor is positive. -/
theorem doorIV_shawValueBound_iff_prizeScalarBound_export {C M n m : ℝ}
    (hn : 0 < n) (hm : 1 < m) :
    ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.ShawValueBound C M n m ↔
      ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.PrizeScalarBound C M n m :=
  ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.shawValueBound_iff_prizeScalarBound
    hn hm

/-- Door-IV Lane-2 family capstone export: a uniform raw prize-floor constant is equivalent to
`Sh(n)=O(1)` for any positive-floor family.  This is normalization only; the open monomial-sum
anti-concentration theorem is not discharged here. -/
theorem doorIV_shawFamilyBound_iff_prizeFamilyBound_export {ι : Type*} (M n m : ι → ℝ)
    (hn : ∀ i : ι, 0 < n i) (hm : ∀ i : ι, 1 < m i) :
    ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.ShawFamilyBound M n m ↔
      ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.PrizeFamilyBound M n m :=
  ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.shawFamilyBound_iff_prizeFamilyBound
    M n m hn hm

#print axioms doorIV_shawValueBound_iff_prizeScalarBound_export
#print axioms doorIV_shawFamilyBound_iff_prizeFamilyBound_export

/-- Door-IV coherence-deficit QUANTITATIVE capstone export: in a real inner product space the
multi-piece coherence deficit `1 − ρ_multi` is SANDWICHED (up to a factor `2`) by the total pairwise
misalignment `S(A) = Σ_{j<k}(‖A j‖‖A k‖ − ⟪A j,A k⟫_ℝ)` over the squared total piece mass:
`S/M² ≤ 1 − ρ_multi ≤ 2·S/M²`.  This upgrades the qualitative `ρ=1 ⟺ same-ray` obstruction to a
two-sided quantitative one.  Constraint lemma — CORE `M(μ_n)` is NOT discharged here. -/
theorem doorIV_coherenceDeficit_pairwiseSandwich_export {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ι : Type*} (s : Finset ι) (A : ι → F)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.totalPairwiseMisalign s A
        / (∑ i ∈ s, ‖A i‖) ^ 2
      ≤ 1 - ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative.multiPieceNormCoherence s A
    ∧ 1 - ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative.multiPieceNormCoherence s A
        ≤ 2 * ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.totalPairwiseMisalign s A
          / (∑ i ∈ s, ‖A i‖) ^ 2 :=
  ProximityGap.Frontier.DoorIVDeficitPairwiseSandwich.coherence_deficit_pairwise_sandwich
    s A hden

#print axioms doorIV_coherenceDeficit_pairwiseSandwich_export

/-- Door-IV Lane-3 dilation-deficit BUDGET capstone export: the 2-dilation descent with a VARIABLE
per-level coherence deficit `δ_k ∈ [0,1]` (the level-`k` factor `c_k ≤ 2 − 2δ_k`, from the weld) gives
the telescoped budget bound `M_a ≤ 2^a · exp(−∑_{k<a} δ_k) · M_0`.  The trivial doubling ceiling `2^a`
improves only by `exp(−S)` where `S = ∑ δ_k` is the total coherence-deficit budget spent over the
`a = log₂ n` levels.  Constraint lemma — it prices the dilation route's exact budget; the open
monomial-sum anti-concentration (a SUSTAINED, linear-in-`a` deficit budget) is NOT discharged here.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_dilationDeficitBudget_export (M : ℕ → ℝ) (δ : ℕ → ℝ)
    (hδ0 : ∀ k, 0 ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1) (hM : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ (2 - 2 * δ k) * M k) (a : ℕ) :
    M a ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M 0 :=
  ProximityGap.Frontier.DoorIVDilationDeficitBudget.telescope_deficit_budget
    M δ hδ0 hδ1 hM hstep a

#print axioms doorIV_dilationDeficitBudget_export

/-- Door-IV Lane-3 uniform-deficit THRESHOLD export: for a uniform per-level coherence deficit `δ*`,
the EXACT telescoped per-level factor `2·(1−δ*)` reaches the prize per-level threshold `√2` iff
`δ* ≥ (2−√2)/2` — the SAME constant the weld named.  Unifies the deficit budget with the per-level
weld threshold.  Constraint lemma; CORE not discharged. -/
theorem doorIV_uniformDeficitReachesSqrt2_iff_export (δstar : ℝ) :
    2 * (1 - δstar) ≤ Real.sqrt 2 ↔ δstar ≥ (2 - Real.sqrt 2) / 2 :=
  ProximityGap.Frontier.DoorIVUniformDeficitThreshold.uniform_deficit_reaches_sqrt2_iff δstar

/-- Door-IV Lane-3 sublinear-budget CONVERSE export: if the total deficit budget is sub-average
`S ≤ ε·a` with `ε < (log 2)/2`, the exp budget bound stays at/above the `√(2^a)·M₀` Plancherel scale:
`(√2)^a·M₀ ≤ 2^a·exp(−S)·M₀`.  So the exp-relaxed dilation budget cannot witness a `√n` bound unless
the average per-level deficit reaches `(log 2)/2` (a sustained, linear-in-`a` floor).  Constraint lemma. -/
theorem doorIV_deficitBudgetSublinearFloor_export {ε S M0 : ℝ} (a : ℕ)
    (hε : ε < Real.log 2 / 2) (hS : S ≤ ε * a) (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0 ≤ 2 ^ a * Real.exp (-S) * M0 :=
  ProximityGap.Frontier.DoorIVDeficitBudgetSublinearFloor.deficit_budget_ge_sqrt_scale_of_sublinear
    a hε hS hM0

#print axioms doorIV_uniformDeficitReachesSqrt2_iff_export
#print axioms doorIV_deficitBudgetSublinearFloor_export

/-- Door-IV Lane-2 SHARPENED Shaw-value FLOOR export: the proven unconditional super-diagonal period
floor `(5/4)^{1/4}·√n ≤ M` lifts the Shaw value strictly above the bare `1/√L` bracket floor to
`(5/4)^{1/4}/√L ≤ Sh(M)`.  The super-diagonal constant `c₀ = (5/4)^{1/4} > 1`, so the prize's `O(1)`
target must clear a floor strictly above the bare Parseval scale.  Normalization rung; CORE not
discharged. -/
theorem doorIV_shawValueSuperDiagonalFloor_export {M n L : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M) :
    ShawValueCapstone.superDiagonalFloorConst / Real.sqrt L ≤ ShawValueCapstone.shawValue M n L :=
  ShawValueCapstone.shawValue_ge_superDiagonal_floor hn hL hfloor

/-- Door-IV Lane-2 refined window WIDTH export: under the sharpened floor the trivial Shaw-value
window narrows from `√n` to `√n / c₀`, strictly below `√n` since `c₀ > 1`. -/
theorem doorIV_shawValueRefinedWindowWidth_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    Real.sqrt (n / L) / (ShawValueCapstone.superDiagonalFloorConst / Real.sqrt L)
      = Real.sqrt n / ShawValueCapstone.superDiagonalFloorConst :=
  ShawValueCapstone.refined_window_width_eq hn hL

#print axioms doorIV_shawValueSuperDiagonalFloor_export
#print axioms doorIV_shawValueRefinedWindowWidth_export

/-- Door-IV Lane-2 SHARPENED FLOOR-UNIT CORRIDOR export: lifts the floor-normalized (`√n`-unit) prize
corridor lower end from the bare Plancherel `1` to the proven super-diagonal constant
`c₀ = (5/4)^{1/4} > 1`.  Given the proven super-diagonal period floor `c₀·√n ≤ M`, a classical-door
BGK ceiling `M ≤ √(n·L)`, and the classical-overshoot refutations, the floor-normalized ratio `M/√n`
lives in `[c₀, √L]` (strictly narrower at the bottom than the bare `[1, √L]`), and any prize-floor
certifying mechanism is door-(iv) `newEvaluation`.  This is the `√n`-unit sibling of the sharpened
Shaw bracket `[c₀/√L, √(n/L)]`.  Normalization rung; CORE not discharged. -/
theorem doorIV_sharpenedFloorUnitCorridor_export
    {M nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt nref ≤ M)
    (hceil : M ≤ NoFifthDoorTetrachotomy.bgkScale nref Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (ShawValueCapstone.superDiagonalFloorConst ≤
          DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref
        ∧ DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref ≤ Real.sqrt Lref)
      ∧ (1 < ShawValueCapstone.superDiagonalFloorConst)
      ∧ (∀ m : NoFifthDoorTetrachotomy.Mechanism,
          m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
          m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  DoorIVPrizeShawTetrachotomySynthesis.sharpenedFloorUnit_corridor_doorIV_only
    hnref hLref hfloor hceil hclassicalOvershoots

#print axioms doorIV_sharpenedFloorUnitCorridor_export

/-- Door-IV Lane-3 PRIZE-CONSTANT lower-bound export: any achievable floor-scale prize constant `K`
must clear the proven super-diagonal floor `c₀ = (5/4)^{1/4} ≈ 1.0574 > 1`.  Sharpens the bare
`1 ≤ K` baseline (`doorIV_floorPrizeConstant_ge_one_export`): if `c₀·√n ≤ M` (proven super-diagonal
period floor) and `M ≤ K·√n`, then `c₀ ≤ K`.  A floor-normalized certificate cannot have a constant
below `c₀`; the prize must clear a constant strictly above the bare Plancherel `1`.  Constraint rung on
the achievable prize constant itself; CORE not discharged. -/
theorem doorIV_prizeFloorConstant_ge_superDiagonal_export
    {M n K : ℝ} (hn : 0 < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hbound : M ≤ K * NoFifthDoorTetrachotomy.prizeScale n) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K :=
  DoorIVPrizeShawTetrachotomySynthesis.superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor
    hn hfloor hbound

#print axioms doorIV_prizeFloorConstant_ge_superDiagonal_export

/-- Door-IV Lane-2 SHARPENED floor-normalized SYNTHESIS BUNDLE export: the single citable `√n`-unit
statement with lower end lifted from bare `1` to `c₀ = (5/4)^{1/4}`.  Given the proven super-diagonal
period floor `c₀·√n ≤ M` and the classical-overshoot refutations: (1) `c₀ ≤ M/√n`; (2) the prize-floor
bound `M ≤ C·√n` is exactly `M/√n ≤ C`; (3) any prize-floor-certifying mechanism is door-(iv).  The
`√n`-unit sibling of the sharpened Shaw bracket, one theorem for the prose "the prize must clear `c₀`
and only door (iv) can cap it."  Capstone bundle; CORE not discharged. -/
theorem doorIV_sharpenedFloorRatioBracketedSynthesis_export
    {M nref Lref C : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt nref ≤ M)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (ShawValueCapstone.superDiagonalFloorConst ≤
          DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref) ∧
      (M ≤ C * NoFifthDoorTetrachotomy.prizeScale nref ↔
          DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref ≤ C) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  DoorIVPrizeShawTetrachotomySynthesis.sharpenedFloorRatio_bracketed_prize_iff_and_doorIV_only
    hnref hLref hfloor hclassicalOvershoots

#print axioms doorIV_sharpenedFloorRatioBracketedSynthesis_export

/-- Door-IV Lane-2 UNCONDITIONAL floor-unit bracket export `[c₀, √n]`, NO door assumption.  Combines
the proven super-diagonal period floor `c₀·√n ≤ M` (`c₀ = (5/4)^{1/4}`, the sharp Wick-permutation
4th-moment constant) with the trivial cardinality ceiling `M ≤ n` (triangle inequality on a sum of `n`
unit phases) to bracket the floor-normalized worst-frequency ratio `M/√n ∈ [c₀, √n]` with NO BGK /
completion / classical-door hypothesis whatsoever.  This is the bedrock unconditional envelope of the
conditional `[c₀, √L]` corridor (`doorIV_sharpenedFloorUnitCorridor_export`): the conditional Shaw/BGK
ceiling `√L` (`< √n` for `1 < L < n`) sits strictly inside, the gap `[√L, √n]` is what a classical
door buys for free, and the residual `[C, √L]` is the door-(iv)-only frontier.  Isolates the entire
prize content as collapsing the unconditional `√n` ceiling to an absolute constant.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_floorUnitUnconditionalBracket_export {M n : ℝ} (hn : 0 < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hceil : M ≤ n) :
    ShawValueCapstone.superDiagonalFloorConst ≤
        DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M n ∧
      DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M n ≤ Real.sqrt n :=
  DoorIVPrizeShawTetrachotomySynthesis.floorUnit_unconditional_bracket hn hfloor hceil

#print axioms doorIV_floorUnitUnconditionalBracket_export

/-- Door-IV Lane-2 STRICT floor-unit corridor nesting export `[c₀,√L] ⊊ [c₀,√n]` in the prize
regime `1 < L < n`.  Locks the gap decomposition behind the unconditional bracket
(`doorIV_floorUnitUnconditionalBracket_export`): with the shared proven super-diagonal floor lower end
`c₀ ≤ M/√n` and the classical-door BGK ceiling `M ≤ √(n·L)` giving the conditional ceiling `M/√n ≤ √L`,
the strict separation `√L < √n` (`L < n`) certifies that a classical door shaves `[√L, √n]` off the
unconditional ceiling for free, leaving the residual `[c₀, √L]` (still unbounded as `√L = √log(p/n) → ∞`)
as the door-(iv)-only frontier.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_floorUnitCorridorStrictNesting_export {M n L : ℝ} (hn : 0 < n)
    (hL : 1 < L) (hLn : L < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hceilL : M ≤ NoFifthDoorTetrachotomy.bgkScale n L) :
    ShawValueCapstone.superDiagonalFloorConst ≤
        DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M n ∧
      DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M n ≤ Real.sqrt L ∧
      Real.sqrt L < Real.sqrt n :=
  DoorIVPrizeShawTetrachotomySynthesis.floorUnit_corridor_strict_nesting hn hL hLn hfloor hceilL

#print axioms doorIV_floorUnitCorridorStrictNesting_export

/-- Door-IV Lane-3 BOUNDED-EXCEPTION deficit-budget √-floor export: sharpens the sub-`(log2)/2`
average-deficit converse into a per-level structural statement.  If the `a = log₂n` dilation levels
split into good levels (coherence deficit `δ_k ≤ ε`, `ε < (log2)/2`) and an exceptional set `E` of deep
spikes (`δ_k ≤ 1`) whose count respects the positive-density floor `(1−ε)·|E| ≤ ((log2)/2 − ε)·a`,
then the exp-relaxed dilation budget bound stays AT/ABOVE the `√(2^a)·M₀` Plancherel/prize scale.
Mechanism: a thin (sublinear) set of deep deficit spikes cannot drag the dilation budget down to the
√n prize scale — the route needs `Ω(a)`-many `Ω(1)`-deficit levels, which the same-ray-at-`b*`
geometry (measured `δ_k ≈ 0` on the dominant top levels) does not supply.  Constraint lemma; CORE
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_deficitBudgetBoundedExceptions_export {a : ℕ} {ε M0 : ℝ}
    (δ : ℕ → ℝ) (E : Finset ℕ) (hE : E ⊆ Finset.range a)
    (hgood : ∀ k ∈ Finset.range a, k ∉ E → δ k ≤ ε)
    (hbad : ∀ k ∈ Finset.range a, k ∈ E → δ k ≤ 1)
    (hεthr : ε < Real.log 2 / 2)
    (hdensity : (1 - ε) * (E.card : ℝ) ≤ (Real.log 2 / 2 - ε) * a)
    (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0
      ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M0 :=
  ProximityGap.Frontier.DoorIVDeficitBudgetBoundedExceptions.budget_ge_sqrt_scale_of_bounded_exceptions
    δ E hE hgood hbad hεthr hdensity hM0

#print axioms doorIV_deficitBudgetBoundedExceptions_export

/-- Door-IV Lane-3 LEADING-ZERO-BLOCK √-floor export: the measured worst-`b` 2-dilation descent has a
leading block of `T` zero-deficit levels (coset halves exactly same-ray, `δ_k = 0` for `k < T`, with
`T ≈ a − O(1)` numerically).  All the `exp(−S)` saving is confined to the thin tail of the bottom
`a − T` levels.  Specialising the bounded-exception floor at `ε = 0`: if the leading zero block is large
enough that the tail fits the budget threshold `(a : ℝ) − T ≤ ((log2)/2)·a` (i.e. `T ≥ (1−(log2)/2)·a
≈ 0.6534·a`, satisfied with room to spare by the measured `a−T = O(1)`), then the exp-relaxed dilation
budget stays AT/ABOVE the `√(2^a)·M₀` Plancherel/prize scale.  A descent whose coherence saving is
confined to a sub-`((log2)/2)·a` tail cannot reach the `√n` prize scale.  Constraint lemma; CORE
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_leadingZeroDeficitBlockFloor_export {a T : ℕ} {M0 : ℝ}
    (δ : ℕ → ℝ) (hT : T ≤ a)
    (hzero : ∀ k, k < T → δ k = 0)
    (hbad : ∀ k ∈ Finset.range a, δ k ≤ 1)
    (hblock : (a : ℝ) - T ≤ (Real.log 2 / 2) * a)
    (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0
      ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M0 :=
  ProximityGap.Frontier.DoorIVLeadingZeroDeficitFloor.budget_ge_sqrt_scale_of_leading_zero_block
    δ hT hzero hbad hblock hM0

#print axioms doorIV_leadingZeroDeficitBlockFloor_export

/-- Door-IV Lane-3 SCATTERED-deficit sum floor export (structure-free, strict measured form): if the
RAW total coherence deficit `S = ∑_{k<a} δ_k` over the `a`-level 2-dilation descent is strictly below
the linear-in-`a` threshold `S < (log 2 / 2)·a` (with `a ≥ 1`), then for `M₀ ≥ 0` the exp-relaxed
deficit-budget bound stays AT/ABOVE the `√(2^a)·M₀` Plancherel/prize scale.  Unlike the leading-zero-
block floor, NO assumption is made on how the deficit is distributed: no leading block, contiguity, or
per-level cap — only the total `S`.  This is the invariant that survives in the measured worst-`b`
descent, where the nonzero deficits are SCATTERED (a=8: levels 4,5,7 with zeros interspersed, NOT a
leading block), yet `S < (log2/2)·a` holds with slack at a=5..8 (S = 0, 0.88, 1.62, 1.03 vs threshold
1.73, 2.08, 2.43, 2.77).  Constraint lemma; CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_deficitSumScatteredFloor_export {S M0 : ℝ} (a : ℕ)
    (ha : 1 ≤ a) (hS : S < Real.log 2 / 2 * a) (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0 ≤ 2 ^ a * Real.exp (-S) * M0 :=
  ProximityGap.Frontier.DoorIVDeficitSumScatteredFloor.deficit_budget_ge_sqrt_scale_of_measured_sum
    a ha hS hM0

#print axioms doorIV_deficitSumScatteredFloor_export

/-- Door-IV Lane-1 EVEN-MOMENT PHASE-VACUITY export: the campaign's `_DoorIVFourthMomentEnergyCollapse`
closing note left ONE explicit escape — "a surviving door-(iv) crack must be a higher-order functional
that does NOT reduce to `E₂`; it must use the PHASE the modulus `|η_b|⁴` discards."  This forecloses it.
The candidate phase-carrying object is the UNMODULATED even moment `Σ_b (η_b)^{2r}` (vs the dead modulus
moment `Σ_b ‖η_b‖^{2r}`).  Since `μ_n` is negation-closed (`−1 ∈ μ_n`, `n` even), each `η_b` is REAL, and
for a real `z`, `z^{2r} = ‖z‖^{2r}` — the discarded phase is identically ZERO.  Hence the phase-carrying
even moment EQUALS the modulus even moment (the refuted energy object), at every order `r`.  The
"phase-sensitive even-order escape" is VACUOUS, not merely dead.  Stated for any finite real-valued field
`η : β → ℂ` with `(η b).im = 0`.  Constraint lemma; CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_evenMomentPhaseVacuity_export
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ b ∈ s, (η b).im = 0) (r : ℕ) :
    (∑ b ∈ s, (η b) ^ (2 * r)) = (∑ b ∈ s, ((‖η b‖ : ℝ) : ℂ) ^ (2 * r)) :=
  ProximityGap.Frontier.DoorIVEvenMomentPhaseVacuity.unmodulated_even_moment_eq_modulus s η hreal r

#print axioms doorIV_evenMomentPhaseVacuity_export

/-- Door-IV Lane-1 ASYMMETRIC MIXED-CONJUGATE MOMENT COLLAPSE export: STRICTLY GENERALISES the
even-moment vacuity above.  The finer escape route left after the symmetric `Σ_b η_b^{2r}` died is an
asymmetric / mixed-conjugate correlator `Σ_c η_c^a · conj(η_c)^b` with `a + b = 2r` and `a ≠ b` (e.g.
the `3-to-1` functional `Σ η³·conj η`).  Since `μ_n` is negation-closed each `η_c` is REAL, so
`conj η_c = η_c` and `η_c^a · conj(η_c)^b = η_c^{a+b} = ‖η_c‖^{a+b}` — the conjugate SPLIT is irrelevant,
only the total degree matters, and it lands on the refuted modulus / energy moment.  Hence the ENTIRE
`(2r+1)`-element conjugate ladder `{Σ_c η_c^a · conj(η_c)^{2r−a} : a = 0..2r}` is pinned to one value:
the asymmetric mixed-conjugate door-(iv) escape is VACUOUS at every split.  This proves the campaign's
measured `T = E₂ = Z₄` identity (`probe_dooriv_mixed_conjugate_moment_collapse.py`) split-uniformly.
Stated for any finite real-valued field `η : β → ℂ`.  Constraint lemma; CORE remains OPEN. -/
theorem doorIV_mixedConjugateMomentCollapse_export
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a b r : ℕ) (hab : a + b = 2 * r) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b
      = ∑ c ∈ s, ((‖η c‖ : ℝ) : ℂ) ^ (2 * r) :=
  ProximityGap.Frontier.DoorIVMixedConjugateMomentCollapse.mixedMoment_eq_modulusMoment
    s η hreal a b r hab

#print axioms doorIV_mixedConjugateMomentCollapse_export

/-- Door-IV Lane-1 FULL-LADDER split-independence (any total degree, even OR odd): completes the
mixed-conjugate collapse to EVERY order.  The even collapse needs `a+b` even (squaring the sign away,
landing on `E_r`); the weaker identity `η_c^a·conj(η_c)^b = η_c^{a+b}` (conjugation is the identity on
the real axis) holds at every total degree.  So any two splits with the SAME total `a₁+b₁ = a₂+b₂`
(no evenness) give the same averaged correlator: even total to energy `E_r`, ODD total to the signed
moment `A_D = Σ η_c^D` (real, sign-sensitive).  Probe `probe_odd_mixed_split.py` confirmed odd totals
D∈{3,5} collapse split-uniformly.  Conjugation is a complete red herring at ALL orders; no parity of
total degree lets an asymmetric split make a new object.  Constraint lemma; CORE remains OPEN. -/
theorem doorIV_mixedConjugateMoment_splitIndependent_anyDegree_export
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a₁ b₁ a₂ b₂ : ℕ) (h : a₁ + b₁ = a₂ + b₂) :
    (∑ c ∈ s, (η c) ^ a₁ * ((starRingEnd ℂ) (η c)) ^ b₁)
      = ∑ c ∈ s, (η c) ^ a₂ * ((starRingEnd ℂ) (η c)) ^ b₂ :=
  ProximityGap.Frontier.DoorIVMixedConjugateMomentCollapse.mixedMoment_any_two_splits_eq_any_degree
    s η hreal a₁ b₁ a₂ b₂ h

#print axioms doorIV_mixedConjugateMoment_splitIndependent_anyDegree_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR export: normalizes the two-dilate recursion by the thinner-level
marginal maximum.  If the two-dilate maximum is written `H = c·Smax` with `Smax > 0`, then the strict
no-co-peak gap `H < 2·Smax` is EQUIVALENT to the strict sub-doubling per-level factor `c < 2`.  This is
pure bookkeeping for the empirical law `c(n)=M(n)/M(n/2)`: the probe-localized observation "factor below
2" is exactly the normalized form of the already-kernelled no-co-peak obstruction, while the prize gate
remains the stronger open target `c≤√2`.  No empirical numeric claim, CORE upper bound, cancellation,
completion, moment, anti-concentration, or capacity claim is made here. -/
theorem doorIV_perLevelFactorSubTwo_export
    {H Smax c : ℝ} (hSmax : 0 < Smax) (hH : H = c * Smax) :
    c < 2 ↔ H < 2 * Smax :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.perLevelFactor_lt_two_iff_dilate_lt_two_mul hSmax hH

#print axioms doorIV_perLevelFactorSubTwo_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR no-co-peak export: once a two-dilate frequency is normalized
as `twoDilate = c·Smax` with `c < 2`, it is strictly below the perfect joint marginal extreme
`2·Smax`.  This is a citable consumer form of the sub-doubling factor certificate; it asserts no
arithmetic `√2` gate and no CORE upper bound. -/
theorem doorIV_perLevelFactorNoCopeak_export
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hfactor : ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme.twoDilate s σ b = c * Smax) :
    s b + s (σ b) < 2 * Smax :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.no_copeak_of_perLevelFactor_lt_two
    hc hSmax hfactor

#print axioms doorIV_perLevelFactorNoCopeak_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR product-telescope export: a variable list of measured dyadic
multipliers controls the top level by their product.  This is pure bookkeeping for the per-level factor
probe: if `M(k+1) ≤ c_k M(k)` and `∏ c_k ≤ B`, then `M(a) ≤ B M(0)`.  No empirical product bound,
CORE upper bound, cancellation, moment, completion, or anti-concentration estimate is asserted. -/
theorem doorIV_perLevelFactorProductTelescope_export (M c : ℕ → ℝ) {a : ℕ} {B : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hM0 : 0 ≤ M 0)
    (hprod : (∏ k ∈ Finset.range a, c k) ≤ B)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k) :
    M a ≤ B * M 0 :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.telescope_of_factorProduct_le
    M c hc hM0 hprod hstep

#print axioms doorIV_perLevelFactorProductTelescope_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR pointwise-`√2` export: if every explicitly measured finite
per-level factor in the dyadic tower is bounded by `√2`, the tower satisfies
`M(a) ≤ (√2)^a M(0)`.  This is only the finite product/telescope algebra; it does not prove the
arithmetic `√2` gate for the monomial sums. -/
theorem doorIV_perLevelFactorPointwiseSqrtTwoTelescope_export (M c : ℕ → ℝ) {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k) (hM0 : 0 ≤ M 0)
    (hc2 : ∀ k ∈ Finset.range a, c k ≤ Real.sqrt 2)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k) :
    M a ≤ (Real.sqrt 2) ^ a * M 0 :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.telescope_of_pointwise_sqrtTwo_factors
    M c hc0 hM0 hc2 hstep

#print axioms doorIV_perLevelFactorPointwiseSqrtTwoTelescope_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR obstruction export: if a finite product of nonnegative measured
rung factors exceeds the `√2` product budget, then some individual rung is strictly super-`√2`.  Thus
finite product-gate failure is locally witnessed; it is not hidden in a mean statistic. -/
theorem doorIV_perLevelFactorProductFailureLocalizes_export {c : ℕ → ℝ} {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k)
    (hprod : (Real.sqrt 2) ^ a < ∏ k ∈ Finset.range a, c k) :
    ∃ k ∈ Finset.range a, Real.sqrt 2 < c k :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.exists_factor_gt_sqrtTwo_of_factorProduct_gt
    hc0 hprod

#print axioms doorIV_perLevelFactorProductFailureLocalizes_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR counterexample-localization export: any finite top-level excess
over the `√2` telescope budget forces an explicitly bad dyadic rung `√2 < c_k`.  This pins the exact
local obstruction the door-(iv) arithmetic must rule out or compensate. -/
theorem doorIV_perLevelFactorCounterexampleHasSuperSqrtTwoRung_export (M c : ℕ → ℝ) {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k) (hM0 : 0 < M 0)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k)
    (hcounter : (Real.sqrt 2) ^ a * M 0 < M a) :
    ∃ k ∈ Finset.range a, Real.sqrt 2 < c k :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.exists_super_sqrtTwo_factor_of_telescope_counterexample
    M c hc0 hM0 hstep hcounter

#print axioms doorIV_perLevelFactorCounterexampleHasSuperSqrtTwoRung_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR compensation export: if a positive-height finite product still
meets the total `√2` budget while one rung is strictly super-`√2`, the remaining product must be
strictly below the residual `(√2)^(a-1)` budget.  Super-rungs therefore require real compensating slack
elsewhere. -/
theorem doorIV_perLevelFactorBadRungNeedsCompensation_export {a : ℕ} {cBad R : ℝ}
    (ha : 0 < a) (hR : 0 ≤ R) (hbad : Real.sqrt 2 < cBad)
    (htotal : cBad * R ≤ (Real.sqrt 2) ^ a) :
    R < (Real.sqrt 2) ^ (a - 1) :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_pred_of_bad_rung
    ha hR hbad htotal

#print axioms doorIV_perLevelFactorBadRungNeedsCompensation_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR two-bad-rung compensation export: if two finite rungs are
strictly super-`√2` yet the total height-`b+2` product still meets the `√2` product budget, then the
remaining product must be strictly below `(√2)^b`.  This is pure slack accounting for clustered bad
rungs; it makes no claim that the arithmetic gate or CORE bound holds. -/
theorem doorIV_perLevelFactorTwoBadRungsNeedCompensation_export {b : ℕ} {cBad₁ cBad₂ R : ℝ}
    (hR : 0 ≤ R) (hbad₁ : Real.sqrt 2 < cBad₁) (hbad₂ : Real.sqrt 2 < cBad₂)
    (htotal : cBad₁ * cBad₂ * R ≤ (Real.sqrt 2) ^ (b + 2)) :
    R < (Real.sqrt 2) ^ b :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_of_two_bad_rungs
    hR hbad₁ hbad₂ htotal

#print axioms doorIV_perLevelFactorTwoBadRungsNeedCompensation_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR super-budget block compensation export: any finite block whose
product is strictly above its own `(√2)^r` budget forces the complementary product in a still-good
height-`b+r` tower to lie strictly below `(√2)^b`.  This is the general finite slack-accounting law for
clustered bad rungs, not an arithmetic proof of the `√2` gate. -/
theorem doorIV_perLevelFactorSuperBudgetBlockNeedsCompensation_export {b r : ℕ} {badBlock R : ℝ}
    (hR : 0 ≤ R) (hbad : (Real.sqrt 2) ^ r < badBlock)
    (htotal : badBlock * R ≤ (Real.sqrt 2) ^ (b + r)) :
    R < (Real.sqrt 2) ^ b :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_of_superBudget_block
    hR hbad htotal

#print axioms doorIV_perLevelFactorSuperBudgetBlockNeedsCompensation_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR uncompensated-block export: if a bad block is already above
its own `(√2)^r` budget and the complementary product is still at or above its own `(√2)^b` budget,
then the total product strictly exceeds the height-`b+r` `√2` budget.  Pure finite algebra; no
arithmetic `√2` gate or CORE claim. -/
theorem doorIV_perLevelFactorUncompensatedBlockBreaksBudget_export {b r : ℕ}
    {badBlock R : ℝ} (hbad : (Real.sqrt 2) ^ r < badBlock)
    (hR : (Real.sqrt 2) ^ b ≤ R) :
    (Real.sqrt 2) ^ (b + r) < badBlock * R :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.totalProduct_gt_sqrtTwo_pow_of_uncompensated_superBudget_block
    hbad hR

#print axioms doorIV_perLevelFactorUncompensatedBlockBreaksBudget_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR scaled uncompensated-block export: if a bad block is a factor
`K` above its own `(√2)^r` budget, then the complementary product must fall strictly below the
reciprocal `1/K` share of its own `(√2)^b` budget.  Equivalently, a `K`-overshoot block paired with an
uncompensated `1/K` remainder already breaks the height-`b+r` telescope budget.  Pure finite algebra;
no arithmetic `√2` gate or CORE claim. -/
theorem doorIV_perLevelFactorScaledUncompensatedBlockBreaksBudget_export {b r : ℕ}
    {K badBlock R : ℝ} (hK : 0 < K) (hbad : K * (Real.sqrt 2) ^ r < badBlock)
    (hR : (1 / K) * (Real.sqrt 2) ^ b ≤ R) :
    (Real.sqrt 2) ^ (b + r) < badBlock * R :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.totalProduct_gt_sqrtTwo_pow_of_scaled_uncompensated_block
    hK hbad hR

#print axioms doorIV_perLevelFactorScaledUncompensatedBlockBreaksBudget_export

/-- Door-IV Lane-3 PER-LEVEL FACTOR prize-budget export: the corrected `√2` per-level gate is the exact
factor target singled out by the recursion probe.  Supplying `LevelRatioBoundNZ … √2`, the dyadic tower
identity `(√2)^μ ≤ √n`, and a base `C√L` estimate yields the citable prize-shaped budget `C√(nL)`.
The open arithmetic content is precisely the `√2` gate; this theorem only composes the telescope and
real-algebra budget conversion. -/
theorem doorIV_perLevelFactorSqrtTwoPrizeBudget_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : SubgroupGaussSumSecondMoment.LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) :=
  ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.prizeBudget_of_sqrtTwo_perLevelFactor
    hr h_dim h_base hC hL hn

#print axioms doorIV_perLevelFactorSqrtTwoPrizeBudget_export

/-- Synthesis-scale BRIDGE export: the reduction-half normalization scale `shawScale q n` is the
door-half BGK scale at the concrete thinness index `L = log(q/n)`, so the two `_ShawGrandSynthesis`
halves live over the SAME scale once the index is named.  Pure definitional identity; no CORE claim. -/
theorem shawScale_eq_bgkScale_export (q n : ℝ) :
    ProximityGap.Frontier.ShawValueCapstone.shawScale q n
      = ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawScale_eq_bgkScale q n

#print axioms shawScale_eq_bgkScale_export

/-- Synthesis-gap CLOSED-FORM export: in the prize regime `q > n > 0`, the reduction target
`shawScale q n` exceeds the genuine prize floor `prizeScale n = √n` by EXACTLY the factor
`√(log(q/n))` — the kernel-checked form of `_ShawGrandSynthesis`'s prose "open `√L`-gap".  Asserts
NOTHING about whether the factor is bounded; absorbing it is exactly the open door-(iv) problem. -/
theorem shawScale_div_prizeScale_export (q n : ℝ) (hn : 0 < n) (hnq : n < q) :
    ProximityGap.Frontier.ShawValueCapstone.shawScale q n
      / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      = Real.sqrt (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawScale_div_prizeScale_of_pos_lt q n hn hnq

#print axioms shawScale_div_prizeScale_export

/-- Synthesis-gap STRICT-SEPARATION export: in the thin regime `log(q/n)>1`, the Shaw/BGK
normalization scale strictly exceeds the genuine prize floor.  This is the positive-form guard for the
open door-(iv) gap: the two scales are not accidentally identical once the logarithmic factor bites.
Pure scale bookkeeping; no CORE/cancellation claim. -/
theorem prizeScale_lt_shawScale_of_one_lt_log_export (q n : ℝ) (hn : 0 < n)
    (hL : 1 < Real.log (q / n)) :
    ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      < ProximityGap.Frontier.ShawValueCapstone.shawScale q n :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeScale_lt_shawScale_of_one_lt_log
    q n hn hL

#print axioms prizeScale_lt_shawScale_of_one_lt_log_export

/-- Synthesis-gap SCALE-BOUND export: comparing the Shaw/BGK scale to the genuine prize floor by a
constant `K` is equivalent to bounding the exact gap factor `√log(q/n)` by `K`.  Scale-only bookkeeping;
no CORE/cancellation claim. -/
theorem shawScale_le_const_mul_prizeScale_iff_gap_le_export (q n K : ℝ) (hn : 0 < n)
    (hnq : n < q) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale q n
      ≤ K * ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ↔
      Real.sqrt (Real.log (q / n)) ≤ K :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawScale_le_const_mul_prizeScale_iff_gap_le
    q n K hn hnq

#print axioms shawScale_le_const_mul_prizeScale_iff_gap_le_export

/-- Synthesis-gap FAMILY SCALE-BOUND export: a uniform scale comparison
`shawScaleᵢ ≤ K·prizeScaleᵢ` over a prize-regime family is exactly the pointwise bound
`√log(qᵢ/nᵢ) ≤ K`.  This isolates the scale gap itself, before any value estimate enters. -/
theorem shawScale_family_le_const_mul_prizeScale_iff_gap_le_export {ι : Type*} {q n : ι → ℝ}
    (K : ℝ) (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) :
    (∀ i, _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i)
      ≤ K * ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i)) ↔
      (∀ i, Real.sqrt (Real.log (q i / n i)) ≤ K) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawScale_family_le_const_mul_prizeScale_iff_gap_le
    K hn hnq

#print axioms shawScale_family_le_const_mul_prizeScale_iff_gap_le_export

/-- Synthesis-gap CONSUMER export: in the prize regime `q > n > 0`, the genuine cancellation ratio
`M / prizeScale n = M/√n` equals the campaign Shaw value `shawValue q n M` amplified by EXACTLY the gap
factor `√(log(q/n))`.  This is the precise reason `Sh = O(1)` (the reduction) does NOT by itself bound
the genuine `M/√n` cancellation: the `√(log(q/n))` factor must be absorbed, which is the open door-(iv)
content.  Pure algebra over the definitional bridge; no boundedness claim. -/
theorem prizeFloorRatio_eq_shawValue_mul_gap_export (q n M : ℝ) (hn : 0 < n) (hnq : n < q) :
    M / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      = _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue q n M
          * Real.sqrt (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_eq_shawValue_mul_gap
    q n M hn hnq

#print axioms prizeFloorRatio_eq_shawValue_mul_gap_export


/-- Synthesis-gap ONE-SIDED BOUND export: a pointwise Shaw-value bound `shawValue q n M ≤ C` gives a
genuine prize-floor cancellation bound only after paying the displayed `√(log(q/n))` multiplier.  This
is the operational no-go form of the scale bridge: the reduction's constant bound does not silently
become an `O(1)` bound against `√n`; the exact gap factor remains. -/
theorem prizeFloorRatio_le_shawBound_mul_gap_export (q n M C : ℝ) (hn : 0 < n) (hnq : n < q)
    (hSh : _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue q n M ≤ C) :
    M / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      ≤ C * Real.sqrt (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_le_shawBound_mul_gap
    q n M C hn hnq hSh

#print axioms prizeFloorRatio_le_shawBound_mul_gap_export

/-- Synthesis-gap FAMILY BOUND export: a uniform Shaw-value bound over a prize-regime family transports
to pointwise prize-floor ratios with the exact logarithmic envelope
`Mᵢ/√nᵢ ≤ C·√(log(qᵢ/nᵢ))`.  No CORE/cancellation claim is made; this records exactly what the
reduction alone buys before the open door-(iv) gap is absorbed. -/
theorem prizeFloorRatio_family_le_of_uniformShawBound_export {ι : Type*} {q n M : ι → ℝ} {C : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i)
    (hSh : _root_.ProximityGap.Frontier.ShawValueCapstone.UniformShawBound q n M C) :
    ∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i)
      ≤ C * Real.sqrt (Real.log (q i / n i)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_family_le_of_uniformShawBound
    hn hnq hSh

#print axioms prizeFloorRatio_family_le_of_uniformShawBound_export



/-- Synthesis-gap SAME-CONSTANT FAMILY export: for any proposed constant `C`, the genuine floor-scale
family bound `Mᵢ/√nᵢ ≤ C` is equivalent to the gap-amplified Shaw bound `Shᵢ·√log(qᵢ/nᵢ) ≤ C` with
the SAME `C`.  This is the exact constant-preserving form of the Shaw-scale bridge after the open gap
factor is displayed. -/
theorem prizeFloorRatio_familyBound_iff_gapAmplifiedShaw_familyBound_export {ι : Type*}
    {q n M : ι → ℝ} (C : ℝ) (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) :
    (∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ C) ↔
      (∀ i, _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)
        * Real.sqrt (Real.log (q i / n i)) ≤ C) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_familyBound_iff_gapAmplifiedShaw_familyBound
    C hn hnq

#print axioms prizeFloorRatio_familyBound_iff_gapAmplifiedShaw_familyBound_export

/-- Synthesis-gap EXACT BOUNDEDNESS export: over a prize-regime family, boundedness of the genuine
floor-scale ratios `Mᵢ/√nᵢ` is exactly boundedness of the Shaw values after multiplying by the displayed
`√log` gap factor.  This is the citable boundedness form of `M/√n = Sh·√log`: a Shaw `O(1)` statement
becomes a floor-scale prize `O(1)` statement only for the gap-amplified Shaw quantity. -/
theorem prizeFloorRatio_bddAbove_iff_gapAmplifiedShaw_bddAbove_export {ι : Type*}
    {q n M : ι → ℝ} (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) :
    (∃ B : ℝ, ∀ i,
      M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B) ↔
      (∃ B : ℝ, ∀ i,
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)
          * Real.sqrt (Real.log (q i / n i)) ≤ B) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_bddAbove_iff_gapAmplifiedShaw_bddAbove
    hn hnq

#print axioms prizeFloorRatio_bddAbove_iff_gapAmplifiedShaw_bddAbove_export

/-- Synthesis-gap EXACT UNBOUNDEDNESS export: the wall-facing companion to the boundedness equivalence.
The floor-scale ratios drift beyond every proposed bound iff the gap-amplified Shaw values do.  Pure
scale algebra over the exact `√log` bridge; no CORE/cancellation claim. -/
theorem prizeFloorRatio_unbounded_iff_gapAmplifiedShaw_unbounded_export {ι : Type*}
    {q n M : ι → ℝ} (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) :
    (∀ B : ℝ, ∃ i : ι,
      B < M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i)) ↔
      (∀ B : ℝ, ∃ i : ι,
        B < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)
          * Real.sqrt (Real.log (q i / n i))) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_unbounded_iff_gapAmplifiedShaw_unbounded
    hn hnq

#print axioms prizeFloorRatio_unbounded_iff_gapAmplifiedShaw_unbounded_export

/-- Synthesis-gap INVERSE CONSUMER export: under positive logarithmic thinness, the Shaw value is the
genuine prize-floor ratio divided by the exact gap factor.  This is a normalization identity only, not
an upper or lower bound. -/
theorem shawValue_eq_prizeFloorRatio_div_gap_export (q n M : ℝ) (hn : 0 < n) (hnq : n < q)
    (hL : 0 < Real.log (q / n)) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue q n M
      = (M / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n) /
        Real.sqrt (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawValue_eq_prizeFloorRatio_div_gap
    q n M hn hnq hL

#print axioms shawValue_eq_prizeFloorRatio_div_gap_export

/-- Synthesis-gap FAMILY INVERSE CONSUMER export: every member of a positive-thinness family satisfies
`Shᵢ = (Mᵢ/√nᵢ)/√(log(qᵢ/nᵢ))` pointwise.  This records the exact normalization conversion and makes
no CORE/cancellation claim. -/
theorem shawValue_family_eq_prizeFloorRatio_div_gap_export {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i)
    (hL : ∀ i, 0 < Real.log (q i / n i)) :
    ∀ i, _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)
      = (M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i)) /
        Real.sqrt (Real.log (q i / n i)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawValue_family_eq_prizeFloorRatio_div_gap
    hn hnq hL

#print axioms shawValue_family_eq_prizeFloorRatio_div_gap_export

/-- Synthesis-gap INVERSE BOUND export: under positive logarithmic thinness, a genuine prize-floor
ratio bound `M/√n ≤ B` gives Shaw-value control only after dividing by the exact gap factor:
`Sh(q,n,M) ≤ B/√(log(q/n))`.  This is pure normalization bookkeeping and makes no CORE/cancellation
claim. -/
theorem shawValue_le_prizeFloorBound_div_gap_export (q n M B : ℝ) (hn : 0 < n) (hnq : n < q)
    (hL : 0 < Real.log (q / n))
    (hPrize : M / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ B) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue q n M
      ≤ B / Real.sqrt (Real.log (q / n)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawValue_le_prizeFloorBound_div_gap
    q n M B hn hnq hL hPrize

#print axioms shawValue_le_prizeFloorBound_div_gap_export

/-- Synthesis-gap FAMILY INVERSE BOUND export: a uniform genuine prize-floor ratio bound over a
positive-thinness family transports pointwise to `Shᵢ ≤ B/√(log(qᵢ/nᵢ))`.  Together with the forward
bound consumer this records the exact one-sided `√log` conversion between the two normalizations. -/
theorem shawValue_family_le_prizeFloorBound_div_gap_export {ι : Type*} {q n M : ι → ℝ} {B : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i)
    (hL : ∀ i, 0 < Real.log (q i / n i))
    (hPrize : ∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B) :
    ∀ i, _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)
      ≤ B / Real.sqrt (Real.log (q i / n i)) :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.shawValue_family_le_prizeFloorBound_div_gap
    hn hnq hL hPrize

#print axioms shawValue_family_le_prizeFloorBound_div_gap_export

/-- Synthesis-gap INVERSE NO-GO export: if a prize-regime instance has a positive Shaw-value floor
`c ≤ shawValue q n M` and a genuine prize-floor ratio bound `M/√n ≤ B`, then the gap factor itself is
bounded by `√(log(q/n)) ≤ B/c`.  Thus any constant prize-floor bound with nonvanishing Shaw value has
already absorbed the open door-(iv) gap. -/
theorem gap_le_prizeFloorBound_div_shawFloor_export (q n M B c : ℝ) (hn : 0 < n) (hnq : n < q)
    (hc : 0 < c) (hfloor : _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue q n M ≥ c)
    (hPrize : M / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ B) :
    Real.sqrt (Real.log (q / n)) ≤ B / c :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.gap_le_prizeFloorBound_div_shawFloor
    q n M B c hn hnq hc hfloor hPrize

#print axioms gap_le_prizeFloorBound_div_shawFloor_export

/-- Synthesis-gap FAMILY INVERSE NO-GO export: if a prize-regime family has uniformly bounded genuine
prize-floor ratios and every Shaw value stays above a fixed positive floor `c`, then every gap factor is
pointwise bounded by the same quotient `B/c`.  This is only algebra over the Shaw-scale bridge; it makes
no cancellation, anti-concentration, or CORE claim. -/
theorem gap_family_le_prizeFloorBound_div_shawFloor_export {ι : Type*} {q n M : ι → ℝ} {B c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) ≥ c)
    (hPrize : ∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B) :
    ∀ i, Real.sqrt (Real.log (q i / n i)) ≤ B / c :=
  ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.gap_family_le_prizeFloorBound_div_shawFloor
    hn hnq hc hfloor hPrize

#print axioms gap_family_le_prizeFloorBound_div_shawFloor_export

/-- Synthesis-gap UNBOUNDED-DRIFT export: if the exact gap factors `√(log(qᵢ/nᵢ))` drift past every
rescaled target and every Shaw value stays above a fixed positive floor `c`, then the genuine
prize-floor ratios `Mᵢ/√nᵢ` also drift past every target.  This is the explicit contrapositive
pressure behind the gap no-go: a constant prize-floor bound with nonvanishing Shaw value already
requires controlling the open door-(iv) `√log` gap.  Pure algebra over `M/√n = Sh·√log`; no CORE or
cancellation claim. -/
theorem prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor_export {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i))
    (hgapDrift : ∀ B : ℝ, ∃ i : ι, B / c < Real.sqrt (Real.log (q i / n i))) :
    ∀ B : ℝ, ∃ i : ι,
      B < M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) :=
  ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor
    hn hnq hc hfloor hgapDrift

#print axioms prizeFloorRatio_unbounded_of_gap_unbounded_and_shawFloor_export

/-- Synthesis-gap BOUNDEDNESS NO-GO export: if genuine prize-floor ratios are uniformly bounded and
every Shaw value stays above a fixed positive floor `c`, then the exact `√log` gap factors are uniformly
bounded too.  This existential wrapper is the boundedness-form companion to the pointwise inverse no-go;
it makes explicit that an `O(1)` prize-floor theorem with nonvanishing Shaw value already controls the
open door-(iv) gap. -/
theorem gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor_export {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i))
    (hPrizeBdd : ∃ B : ℝ, ∀ i,
      M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B) :
    ∃ G : ℝ, ∀ i, Real.sqrt (Real.log (q i / n i)) ≤ G :=
  ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo.gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor
    hn hnq hc hfloor hPrizeBdd

#print axioms gap_bddAbove_of_prizeFloorRatio_bddAbove_and_shawFloor_export

/-- Synthesis-gap UNBOUNDEDNESS CONTRADICTION export: uniformly bounded genuine prize-floor ratios
and a fixed positive Shaw-value floor forbid the exact `√log` gap from drifting past every proposed
bound.  This is the direct contradiction form of the boundedness no-go; pure scale algebra, no CORE
claim. -/
theorem not_gap_unbounded_of_prizeFloorRatio_bddAbove_and_shawFloor_export {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i))
    (hPrizeBdd : ∃ B : ℝ, ∀ i,
      M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B) :
    ¬ (∀ G : ℝ, ∃ i : ι, G < Real.sqrt (Real.log (q i / n i))) :=
  ArkLib.ProximityGap.Frontier.ShawGapBddAboveNoGo.not_gap_unbounded_of_prizeFloorRatio_bddAbove_and_shawFloor
    hn hnq hc hfloor hPrizeBdd

#print axioms not_gap_unbounded_of_prizeFloorRatio_bddAbove_and_shawFloor_export
/-- Synthesis-gap VANISHING-SHAW export: if genuine prize-floor ratios stay bounded by a nonnegative
constant `B` while the exact gap factors `√(log(qᵢ/nᵢ))` drift past every target, then the Shaw values
become arbitrarily small along a subsequence.  This is the complementary no-go to the positive-Shaw
floor drift theorem: over an unbounded `√log` regime, bounded `Mᵢ/√nᵢ` cannot coexist with a
nonvanishing Shaw-value floor.  Pure normalization algebra; no CORE/cancellation claim. -/
theorem shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound_export {ι : Type*}
    {q n M : ι → ℝ} {B : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hB : 0 ≤ B)
    (hPrize : ∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B)
    (hgapDrift : ∀ T : ℝ, ∃ i : ι, T < Real.sqrt (Real.log (q i / n i))) :
    ∀ ε : ℝ, 0 < ε → ∃ i : ι,
      _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) < ε :=
  ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound
    hn hnq hB hPrize hgapDrift

#print axioms shawValue_arbitrarily_small_of_gap_unbounded_and_prizeFloorBound_export

/-- Synthesis-gap POSITIVE-SHAW-FLOOR NO-GO export: if genuine prize-floor ratios stay bounded by a
nonnegative constant while the exact gap factors `√(log(qᵢ/nᵢ))` drift past every target, then there is
no fixed positive constant below all Shaw values.  This is the existential consumer form of the
arbitrary-small Shaw theorem: bounded `Mᵢ/√nᵢ` over an unbounded synthesis-gap regime forces the Shaw
values to vanish along a subsequence.  Pure normalization algebra; no CORE/cancellation claim. -/
theorem not_exists_positive_shawFloor_of_gap_unbounded_and_prizeFloorBound_export {ι : Type*}
    {q n M : ι → ℝ} {B : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hB : 0 ≤ B)
    (hPrize : ∀ i, M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B)
    (hgapDrift : ∀ T : ℝ, ∃ i : ι, T < Real.sqrt (Real.log (q i / n i))) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ i : ι,
      c ≤ _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.not_exists_positive_shawFloor_of_gap_unbounded_and_prizeFloorBound
    hn hnq hB hPrize hgapDrift

#print axioms not_exists_positive_shawFloor_of_gap_unbounded_and_prizeFloorBound_export

/-- Synthesis-gap PRIZE-RATIO BOUNDEDNESS NO-GO export: a positive uniform Shaw floor plus unbounded
exact gap factors forbids any uniform upper bound on the genuine ratios `Mᵢ/√nᵢ`.  This is the
existential boundedness consumer of the drift theorem; pure scale algebra, no CORE/cancellation claim. -/
theorem not_prizeFloorRatio_bddAbove_of_gap_unbounded_and_shawFloor_export {ι : Type*}
    {q n M : ι → ℝ} {c : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i) (hc : 0 < c)
    (hfloor : ∀ i, c ≤ _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i))
    (hgapDrift : ∀ B : ℝ, ∃ i : ι, B / c < Real.sqrt (Real.log (q i / n i))) :
    ¬ ∃ B : ℝ, ∀ i : ι,
      M i / ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale (n i) ≤ B :=
  ArkLib.ProximityGap.Frontier.ShawGapDriftContrapositive.not_prizeFloorRatio_bddAbove_of_gap_unbounded_and_shawFloor
    hn hnq hc hfloor hgapDrift

#print axioms not_prizeFloorRatio_bddAbove_of_gap_unbounded_and_shawFloor_export

/-- Door-IV Lane-2 EXACT SUBGROUP PARSEVAL ENERGY export: for the order-`d` subgroup
indicator `1_{μ_d}` in `ZMod N`, the full DFT spectral energy is exactly `N·d`.  This is
the kernel-checked Plancherel normalization substrate behind the Shaw-value floor, not a
per-frequency peak bound and not CORE cancellation. -/
theorem doorIV_subgroupIndicator_total_energy_export {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N) :
    (∑ k : ZMod N,
        ‖(ZMod.dft
          (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
            (N := N) d)) k‖ ^ 2)
      = (N : ℝ) * d :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact.subgroupIndicator_total_energy hd

#print axioms doorIV_subgroupIndicator_total_energy_export

/-- Door-IV Lane-2 DC-SUBTRACTED PARSEVAL export: subtracting the DC term from the exact
subgroup indicator energy gives the #444 master-chain identity `Σ_{k≠0}|η_k|² = N·d − d²`.
This pins the exact mean-energy floor/normalization used by the reduction chain; it makes no
sup-norm, anti-concentration, completion, moment-saving, or capacity claim. -/
theorem doorIV_subgroupIndicator_offDC_energy_export {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N) :
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖(ZMod.dft
          (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
            (N := N) d)) k‖ ^ 2)
      = (N : ℝ) * d - (d : ℝ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact.subgroupIndicator_offDC_energy hd

#print axioms doorIV_subgroupIndicator_offDC_energy_export

/-- Door-IV Lane-2 OFF-DC MEAN FLOOR export: for `1 < N`, the average off-DC
subgroup-indicator spectral energy is at most the subgroup order `d`.  This permanently exports
the proven `E₁/card ≤ n` normalization substrate for the Shaw reduction, while explicitly leaving
the open per-frequency CORE peak bound untouched. -/
theorem doorIV_subgroupIndicator_offDC_mean_le_order_export {N : ℕ} [NeZero N] {d : ℕ}
    (hd : d ∣ N) (hN1 : 1 < N) :
    (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖(ZMod.dft
          (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
            (N := N) d)) k‖ ^ 2)
        / ((N : ℝ) - 1) ≤ (d : ℝ) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact.subgroupIndicator_offDC_mean_le_order
    hd hN1

#print axioms doorIV_subgroupIndicator_offDC_mean_le_order_export


/-- Door-IV Lane-2 DC VALUE export: for the order-`d` subgroup indicator, the zero-frequency
coefficient is exactly the subgroup order.  This is the DC term that must be removed before the
prize object is the off-DC maximum; it is normalization bookkeeping, not cancellation. -/
theorem doorIV_subgroupIndicator_dc_value_export {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N) :
    (ZMod.dft
      (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
        (N := N) d)) 0 = (d : ℂ) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap.subgroupIndicator_dc_value hd

#print axioms doorIV_subgroupIndicator_dc_value_export

/-- Door-IV Lane-2 DC NORM export: the magnitude of the zero-frequency subgroup-indicator DFT
coefficient is exactly `d`.  This pins the DC-dominated all-frequency maximum separately from the
off-DC prize maximum. -/
theorem doorIV_subgroupIndicator_dc_norm_export {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N) :
    ‖(ZMod.dft
      (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
        (N := N) d)) 0‖ = (d : ℝ) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap.subgroupIndicator_dc_norm hd

#print axioms doorIV_subgroupIndicator_dc_norm_export

/-- Door-IV Lane-2 DC/OFF-DC SPECTRAL GAP export: every off-DC coefficient is bounded by the
trivial completion gap relative to the DC coefficient, `M² ≤ ((N-d)/d)·|DC|²`.  This formally
separates the off-DC prize object from the DC term; the factor is the completion fence, not CORE. -/
theorem doorIV_offDC_peak_sq_le_gap_mul_dc_sq_export {N : ℕ} [NeZero N] {d : ℕ}
    (hd : d ∣ N) {k₀ : ZMod N} (hk₀ : k₀ ∈ (Finset.univ.erase (0 : ZMod N)))
    (hd0 : 0 < d) :
    ‖(ZMod.dft
      (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
        (N := N) d)) k₀‖ ^ 2
      ≤ (((N : ℝ) - d) / d) * ‖(ZMod.dft
        (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
          (N := N) d)) 0‖ ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap.offDC_peak_sq_le_gap_mul_dc_sq
    hd hk₀ hd0

#print axioms doorIV_offDC_peak_sq_le_gap_mul_dc_sq_export


/-- Door-IV Lane-2 DC/OFF-DC SPECTRAL GAP export, norm form: every off-DC coefficient is
bounded by `sqrt((N-d)/d)` times the DC magnitude.  This is just the square-root form of the
trivial completion gap relative to DC, not the CORE upper bound. -/
theorem doorIV_offDC_peak_le_sqrt_gap_mul_dc_export {N : ℕ} [NeZero N] {d : ℕ}
    (hd : d ∣ N) {k₀ : ZMod N} (hk₀ : k₀ ∈ (Finset.univ.erase (0 : ZMod N)))
    (hd0 : 0 < d) :
    ‖(ZMod.dft
      (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
        (N := N) d)) k₀‖
      ≤ Real.sqrt (((N : ℝ) - d) / d) * ‖(ZMod.dft
        (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
          (N := N) d)) 0‖ :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap.offDC_peak_le_sqrt_gap_mul_dc
    hd hk₀ hd0

#print axioms doorIV_offDC_peak_le_sqrt_gap_mul_dc_export

/-- Door-IV Lane-2 EXACT OFF-DC PEAK BRACKET export (squared form): there is an off-DC
frequency whose squared subgroup-indicator DFT magnitude lies between the exact off-DC mean
`(N·d - d²)/(N - 1)` and the exact off-DC total energy `N·d - d²`.  This is the honest
Plancherel-floor-to-completion-ceiling bracket on the concrete prize object.
It is a floor/ceiling
substrate only: no CORE upper bound, cancellation, anti-concentration, moment-saving, or capacity
claim. -/
theorem doorIV_exists_offDC_peak_sq_bracket_export {N : ℕ} [NeZero N] {d : ℕ}
    (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
          ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ ^ 2
      ∧ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ ^ 2 ≤ (N : ℝ) * d - (d : ℝ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket.exists_offDC_peak_sq_bracket
    hd hN1

#print axioms doorIV_exists_offDC_peak_sq_bracket_export

/-- Door-IV Lane-2 EXACT OFF-DC PEAK BRACKET export (norm form): the same concrete off-DC
frequency has norm between `sqrt((N·d - d²)/(N - 1))` and `sqrt(N·d - d²)`.  The lower endpoint is
only the Plancherel floor and the upper endpoint is only the trivial `√(N·d)` completion fence;
CORE remains the missing descent to `C·sqrt(d·log(N/d))`. -/
theorem doorIV_exists_offDC_peak_bracket_export {N : ℕ} [NeZero N] {d : ℕ}
    (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      Real.sqrt (((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1))
          ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖
      ∧ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖
          ≤ Real.sqrt ((N : ℝ) * d - (d : ℝ) ^ 2) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket.exists_offDC_peak_bracket
    hd hN1

#print axioms doorIV_exists_offDC_peak_bracket_export

/-- Door-IV Lane-2 BGK-IN-BRACKET export: in the prize-regime inequalities
`1 ≤ n`, `1 < p`, and `1 ≤ L ≤ p - n`, the BGK target `sqrt(n·L)` lies between the
exact off-DC Plancherel floor and the exact off-DC completion ceiling.  This is a
consistency/containment capstone for the proven bracket, not a CORE upper bound. -/
theorem doorIV_offDC_band_contains_bgkTarget_export {n p L : ℝ} (hn : 1 ≤ n)
    (hp : 1 < p) (hL1 : 1 ≤ L) (hL2 : L ≤ p - n) :
    Real.sqrt ((p * n - n ^ 2) / (p - 1)) ≤ Real.sqrt (n * L)
      ∧ Real.sqrt (n * L) ≤ Real.sqrt (p * n - n ^ 2) :=
  _root_.ProximityGap.Frontier.DoorIVOffDCCeilingDominatesBGKTarget.offDC_band_contains_bgkTarget
    hn hp hL1 hL2

#print axioms doorIV_offDC_band_contains_bgkTarget_export

/-- Door-IV Lane-2 OFF-DC MEAN FLOOR SHARPNESS export: the exact off-DC mean
energy is trapped between `d·(1 - (d - 1)/(N - 1))` and `d`.  Thus the Plancherel
floor is asymptotically sharp in the thin prize regime; the open gap is above the
floor, in the off-DC peak upper bound, not in the normalization. -/
theorem doorIV_subgroupIndicator_offDC_mean_two_sided_export {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
        ≤ ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
      ∧ ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1) ≤ (d : ℝ) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp.subgroupIndicator_offDC_mean_two_sided
    hd hN1

#print axioms doorIV_subgroupIndicator_offDC_mean_two_sided_export

/-- Door-IV Lane-2 SHARP OFF-DC PEAK FLOOR export: an off-DC frequency has squared
magnitude at least the sharp closed-form floor `d*(1-(d-1)/(N-1))`.  This composes
the exact off-DC peak floor with mean-floor sharpness; lower endpoint only, no CORE
upper-bound claim. -/
theorem doorIV_exists_offDC_peak_sq_ge_sharpFloor_export {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
        ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp.exists_offDC_peak_sq_ge_sharpFloor
    hd hN1

#print axioms doorIV_exists_offDC_peak_sq_ge_sharpFloor_export

/-- Door-IV Lane-2 SHARP OFF-DC PEAK FLOOR export, norm form: an off-DC DFT coefficient
has magnitude at least `sqrt(d*(1-(d-1)/(N-1)))`.  This pins the Plancherel floor on
the prize object in its sharp `sqrt(d*(1-o(1)))` form; no cancellation or CORE
upper-bound claim. -/
theorem doorIV_exists_offDC_peak_ge_sqrt_sharpFloor_export {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      Real.sqrt ((d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1)))
        ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp.exists_offDC_peak_ge_sqrt_sharpFloor
    hd hN1

#print axioms doorIV_exists_offDC_peak_ge_sqrt_sharpFloor_export


/-- Door-IV Lane-2 SHARP OFF-DC PEAK BRACKET export, squared form: the concrete off-DC
prize object lies between the sharp Plancherel floor `d*(1-(d-1)/(N-1))` and the
trivial completion ceiling `N*d-d^2`.  This is a floor-to-fence bracket, not CORE. -/
theorem doorIV_exists_offDC_peak_sq_bracket_sharp_export {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
        ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ ^ 2
      ∧ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖ ^ 2 ≤ (N : ℝ) * d - (d : ℝ) ^ 2 :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp.exists_offDC_peak_sq_bracket_sharp
    hd hN1

#print axioms doorIV_exists_offDC_peak_sq_bracket_sharp_export

/-- Door-IV Lane-2 SHARP OFF-DC PEAK BRACKET export, norm form: the off-DC peak is bracketed
between `sqrt(d*(1-(d-1)/(N-1)))` and `sqrt(N*d-d^2)`.  The upper endpoint is still only the
completion fence; the missing CORE theorem is the descent to `C*sqrt(d*log(N/d))`. -/
theorem doorIV_exists_offDC_peak_bracket_sharp_export {N : ℕ} [NeZero N]
    {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (Finset.univ.erase (0 : ZMod N)),
      Real.sqrt ((d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1)))
        ≤ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖
      ∧ ‖(ZMod.dft
            (_root_.ProximityGap.Frontier.ZModSubgroupSaturation.subgroupIndicator
              (N := N) d)) k₀‖
          ≤ Real.sqrt ((N : ℝ) * d - (d : ℝ) ^ 2) :=
  _root_.ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp.exists_offDC_peak_bracket_sharp
    hd hN1

#print axioms doorIV_exists_offDC_peak_bracket_sharp_export

/-- Door-IV Lane-1 ODD SIGNED-MOMENT CAUCHY export: the real sign-sensitive signed moment
`A_D = Σ_b (η_b)^D` (the odd endpoint of the mixed-conjugate ladder) is CONTROLLED by the energy face:
`(Σ_b (η_b)^D)² ≤ card(s) · Σ_b (η_b)^{2D}`.  So the last named "different object" the moment-collapse
leaves standing (real, sign-sensitive, unlike the even modulus moments) is dominated by `√card` times
the refuted order-`2D` even/energy moment.  Combined with `_DoorIVEvenMomentPhaseVacuity` +
`_DoorIVMixedConjugateMomentCollapse`, this forecloses the Lane-1 "phase-carrying moment" door at BOTH
parities: every functional in the `Σ η^a conj(η)^b` lattice routes back to the dead modulus/energy face.
Constraint lemma — NO CORE / cancellation / completion / anti-concentration / capacity claim;
CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_sq_signedMoment_le_card_mul_evenMoment_export
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) :
    (∑ b ∈ s, (η b) ^ D) ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D) :=
  ArkLib.ProximityGap.Frontier.DoorIVOddSignedMomentCauchy.sq_signedMoment_le_card_mul_evenMoment
    s η D

/-- Door-IV Lane-1 ODD SIGNED-MOMENT magnitude export: `|A_D| ≤ √(card · energy_{2D})`.  The signed odd
moment's magnitude cannot exceed the `√card`-scaled square root of the (refuted) even/energy moment. -/
theorem doorIV_abs_signedMoment_le_sqrt_card_mul_evenMoment_export
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) :
    |∑ b ∈ s, (η b) ^ D| ≤ Real.sqrt ((s.card : ℝ) * ∑ b ∈ s, (η b) ^ (2 * D)) :=
  ArkLib.ProximityGap.Frontier.DoorIVOddSignedMomentCauchy.abs_signedMoment_le_sqrt_card_mul_evenMoment
    s η D

/-- Door-IV Lane-1 ODD SIGNED-MOMENT no-go export (energy budget controls the signed moment): if the
energy moment is below `E₀` and `card(s)·E₀ < T²` (with `T ≥ 0`), the signed `D`-moment cannot reach `T`
in magnitude.  A prize-scale signed-moment certificate already forces a matching energy expenditure;
the odd signed moment carries no cancellation independent of the dead energy face. -/
theorem doorIV_not_abs_signedMoment_ge_of_energy_budget_export
    {β : Type*} (s : Finset β) (η : β → ℝ) (D : ℕ) {E₀ T : ℝ}
    (hE : ∑ b ∈ s, (η b) ^ (2 * D) ≤ E₀) (hT : 0 ≤ T)
    (hbudget : (s.card : ℝ) * E₀ < T ^ 2) :
    |∑ b ∈ s, (η b) ^ D| < T :=
  ArkLib.ProximityGap.Frontier.DoorIVOddSignedMomentCauchy.not_abs_signedMoment_ge_of_energy_budget
    s η D hE hT hbudget

#print axioms doorIV_sq_signedMoment_le_card_mul_evenMoment_export
#print axioms doorIV_abs_signedMoment_le_sqrt_card_mul_evenMoment_export
#print axioms doorIV_not_abs_signedMoment_ge_of_energy_budget_export

/-- Door-IV Lane-1 MOMENT-HIERARCHY CAPSTONE export: the ENTIRE mixed-conjugate correlator hierarchy of
the real period field is energy-dominated at BOTH parities. For a finite real-valued field `η : β → ℝ`
(the real period field of negation-closed `μ_n`): (1) every EVEN-total-degree `2r` real correlator
`Σ_c (η_c)^a (η_c)^b` (`a+b=2r`, any split) equals the modulus/energy moment `Σ_c (η_c)^{2r}` exactly; and
(2) every total-degree `D` signed correlator `Σ_c (η_c)^D` has `(Σ_c (η_c)^D)² ≤ card · Σ_c (η_c)^{2D}`
(Cauchy-Schwarz). This CONSOLIDATES `_DoorIVEvenMomentPhaseVacuity` + `_DoorIVMixedConjugateMomentCollapse`
(even-total = energy) with `_DoorIVOddSignedMomentCauchy` (odd-total → signed moment → energy-dominated)
into ONE "no-fifth-door in the moment hierarchy" statement: there is no phase-carrying correlator
anywhere in the `Σ η^a conj(η)^b` lattice — all collapse onto the refuted even/energy face. Constraint
capstone — NO CORE / cancellation / completion / anti-concentration / capacity claim; CORE
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_momentHierarchy_energy_dominated_export
    {β : Type*} (s : Finset β) (η : β → ℝ) :
    (∀ a b r : ℕ, a + b = 2 * r →
        ∑ c ∈ s, (η c) ^ a * (η c) ^ b = ∑ c ∈ s, (η c) ^ (2 * r))
      ∧ (∀ D : ℕ,
        (∑ c ∈ s, (η c) ^ D) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, (η c) ^ (2 * D)) :=
  ArkLib.ProximityGap.Frontier.DoorIVMomentHierarchyEnergyDominated.momentHierarchy_energy_dominated
    s η

#print axioms doorIV_momentHierarchy_energy_dominated_export

/-- Door-IV Lane-3 MOMENT-DOOR OVERSHOOT export (INTERNAL discharge of the tetrachotomy's door-(i)).
The no-fifth-door tetrachotomy discharges the moment door (i) overshoot from the EXTERNAL SOTA exponent
`n^{1-δ}`. This export gives the INTERNAL, proof-backed reason, using only the real-field facts:
because every `η_b` is REAL the only objects a moment mechanism can access are the energy moments
`E_r = Σ_c (η_c)^{2r}` (by `doorIV_momentHierarchy_energy_dominated_export`); and the energy-moment
scale never drops below the L²/Plancherel rms floor. Concretely, for a finite real field `η`:
(1) `E_1/card ≤ (max_c |η_c|)²` — the sup sits ABOVE rms (the wrong-side Plancherel floor); and
(2) `(E_1/card)² ≤ E_2/card` — the normalized L⁴ energy moment dominates the squared normalized L²
moment, i.e. the energy-moment scale a moment mechanism extracts is itself ABOVE rms. Hence the
energy/moment route is confined to `[rms, max|η|]`: it OVERSHOOTS the prize floor `√n = rms` and is
dominated by the sup. The moment door cannot certify a sup bound below `rms` — a kernel-proven overshoot
from `η` being REAL, with NO SOTA exponent cited. Constraint capstone — NO CORE / cancellation /
completion / anti-concentration / capacity claim; CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_momentDoor_overshoots_rms_export
    {ι : Type*} (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    ((∑ c ∈ s, (f c) ^ (2 * 1)) / (s.card : ℝ) ≤ (s.sup' hs (fun c => |f c|)) ^ 2) ∧
    (((∑ c ∈ s, (f c) ^ (2 * 1)) / (s.card : ℝ)) ^ 2
        ≤ (∑ c ∈ s, (f c) ^ (2 * 2)) / (s.card : ℝ)) := by
  simpa [ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.energyMoment] using
    ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.momentDoor_overshoots_rms f s hs

#print axioms doorIV_momentDoor_overshoots_rms_export

/-- Door-IV Lane-3 BRIDGE export: the INTERNAL moment-energy floor wired into the no-fifth-door
tetrachotomy's `Mechanism`/`prizeScale`/`bgkScale` vocabulary AT THE PRIZE FLOOR (not the BGK ceiling).
The tetrachotomy previously discharged door (i) only from the third-party SOTA exponent `δ<1/2` (a moment
mechanism `RespectsProvenScale` certifies `C·n^{1−δ}`, which eventually exceeds `√(n·L)`).  This export
gives the SOTA-FREE half: for a real period field `η = f` with Plancherel normalization `E_1/card = n`,
a real moment mechanism (certifying at least its accessible rms scale `√(E_1/card)`) has certified scale
`≥ prizeScale n = √n` — the moment door cannot descend BELOW the prize floor, derived from `η` being
REAL (energy-moment domination), with NO SOTA exponent.  The bundle ALSO records the honest gap
`prizeScale n < bgkScale n L` (`L>1`): the internal floor sits at `√n`, a strict `√L` factor BELOW the
BGK ceiling `√(n·L)` that `OvershootsBGK` requires — so it does NOT discharge `OvershootsBGK` and does
NOT replace the SOTA citation; that residual `√L` factor IS the open door-(iv) gap.  Honest
connector/constraint capstone — NO CORE / cancellation / anti-concentration / completion / capacity
claim; CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/
theorem doorIV_momentFloorTetrachotomyBridge_export
    {ι : Type*} (f : ι → ℝ) (s : Finset ι) {n L : ℝ}
    (m : ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism)
    (hn : 0 < n) (hL : 1 < L)
    (hPlancherel : (∑ c ∈ s, (f c) ^ (2 * 1)) / (s.card : ℝ) = n)
    (hreal :
      ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge.rmsScale f s ≤ m.certScale) :
    ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ m.certScale ∧
    ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      < ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L := by
  refine ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge.momentDoor_internalFloor_bridge
    f s m hn hL ?_ hreal
  simpa [ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.energyMoment] using hPlancherel

#print axioms doorIV_momentFloorTetrachotomyBridge_export

/-- Door-IV Lane-2 FAMILY sharpened Shaw-value FLOOR export: the family companion of
`doorIV_shawValueSuperDiagonalFloor_export`.  A uniform super-diagonal period floor `c₀·√nᵢ ≤ Mᵢ`
(`c₀ = (5/4)^{1/4}`) over an admissible prize family lifts every normalized Shaw value strictly above
the bare `1/√Lᵢ` bracket floor to `c₀/√Lᵢ ≤ Sh(Mᵢ)`, pointwise across the family.  Normalization rung;
CORE not discharged. -/
theorem doorIV_shawValueFamilySuperDiagonalFloor_export {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ∀ i, ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i)
      ≤ ShawValueCapstone.shawValue (M i) (n i) (L i) :=
  ShawValueCapstone.shawValueFamily_ge_superDiagonal_floor hn hL hfloor

#print axioms doorIV_shawValueFamilySuperDiagonalFloor_export

/-- Door-IV Lane-2 FAMILY refined window WIDTH export: under a uniform super-diagonal family floor
the trivial Shaw-value window narrows from `√nᵢ` to `√nᵢ/c₀` at every instance, strictly below
`√nᵢ` since `c₀ > 1`.  Family companion of `doorIV_shawValueRefinedWindowWidth_export`. -/
theorem doorIV_shawValueFamilyRefinedWindowWidth_export {ι : Type*} {n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ∀ i, Real.sqrt (n i / L i) /
        (ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i))
      = Real.sqrt (n i) / ShawValueCapstone.superDiagonalFloorConst :=
  ShawValueCapstone.shawValueFamily_refined_window_width_eq hn hL

#print axioms doorIV_shawValueFamilyRefinedWindowWidth_export

/-- Door-IV Lane-2 FAMILY conditional BGK SHARP BRACKET export: the upper-end family companion of the
sharpened floor family.  Under a uniform Plancherel floor `√nᵢ ≤ Mᵢ` and a uniform BGK-shaped ceiling
`Mᵢ ≤ √(nᵢ·Lᵢ)`, every normalized Shaw value lies in the sharp bracket `[1/√Lᵢ, 1]` pointwise across the
family.  Conditional on the supplied BGK ceiling (NOT an unconditional cancellation theorem);
CORE not discharged. -/
theorem doorIV_shawValueFamilyBGKSharpBracket_export {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ ShawValueCapstone.prizeScale (n i) (L i)) :
    ∀ i, Real.sqrt (n i) / ShawValueCapstone.prizeScale (n i) (L i)
          ≤ ShawValueCapstone.shawValue (M i) (n i) (L i)
      ∧ ShawValueCapstone.shawValue (M i) (n i) (L i) ≤ 1 :=
  ShawValueBGKBracket.shawValueFamily_sharp_bracket_of_pos hn hL hfloor hceil

#print axioms doorIV_shawValueFamilyBGKSharpBracket_export

/-- Door-IV Lane-2 FAMILY BGK sharp WIDTH export: the conditional BGK family bracket has width `√Lᵢ` at
every instance, strictly below the trivial-ceiling width `√nᵢ` in the prize regime `Lᵢ < nᵢ`.  Family
companion of the pointwise width/improvement statements. -/
theorem doorIV_shawValueFamilyBGKSharpWidth_export {ι : Type*} {n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL0 : ∀ i, 0 ≤ L i) (hLn : ∀ i, L i < n i) :
    ∀ i, ((1 : ℝ) / (Real.sqrt (n i) / ShawValueCapstone.prizeScale (n i) (L i))
          = Real.sqrt (L i))
      ∧ Real.sqrt (L i) < Real.sqrt (n i) := fun i =>
  ⟨ShawValueBGKBracket.shawValueFamily_sharp_bracket_width hn i,
    ShawValueBGKBracket.shawValueFamily_sharp_width_lt_trivial hL0 hLn i⟩

#print axioms doorIV_shawValueFamilyBGKSharpWidth_export

/-- Door-IV Lane-2 CAPSTONE export: the TWO-SIDED sharpened Shaw-value corridor `[c₀/√Lᵢ, 1]` at family
granularity.  Welds the sharpened LOWER endpoint (super-diagonal floor `c₀/√Lᵢ`) and the conditional
BGK UPPER endpoint (`≤ 1`) into one statement: under a uniform super-diagonal floor `c₀·√nᵢ ≤ Mᵢ` and a
uniform BGK-shaped ceiling `Mᵢ ≤ √(nᵢ·Lᵢ)`, every Shaw value is trapped in `[c₀/√Lᵢ, 1]` — strictly
inside the bare `[1/√Lᵢ, √(nᵢ/Lᵢ)]`.  Conditional on the supplied BGK ceiling; CORE not discharged. -/
theorem doorIV_shawValueFamilyTwoSidedSharpCorridor_export {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ ShawValueCapstone.prizeScale (n i) (L i)) :
    ∀ i, ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i)
          ≤ ShawValueCapstone.shawValue (M i) (n i) (L i)
      ∧ ShawValueCapstone.shawValue (M i) (n i) (L i) ≤ 1 :=
  DoorIVShawValueTwoSidedSharpCorridorFamily.shawValueFamily_twoSided_sharp_corridor
    hn hL hfloor hceil

#print axioms doorIV_shawValueFamilyTwoSidedSharpCorridor_export

/-- Door-IV Lane-3 FAMILY PRIZE-CONSTANT lower-bound export: the family companion of the pointwise
prize-constant lower bound.  Over a NONEMPTY admissible thin family with a uniform super-diagonal floor
`c₀·√nᵢ ≤ Mᵢ` (`c₀ = (5/4)^{1/4}`), any single uniform floor-scale prize constant `K` (`Mᵢ ≤ K·√nᵢ`)
satisfies `c₀ ≤ K`.  So the achievable prize constant is bounded BELOW by the super-diagonal floor,
strictly above the bare Plancherel `1`, uniformly across the family.  Constraint lemma (bounds the prize
constant from below, the easy direction); CORE upper bound not discharged. -/
theorem doorIV_familyPrizeConstantSuperDiagonalLowerBound_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} {K : ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hbound : ∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K :=
  DoorIVPrizeShawTetrachotomySynthesis.superDiagonalFloorConst_le_familyPrizeFloorConstant
    hn hfloor hbound

#print axioms doorIV_familyPrizeConstantSuperDiagonalLowerBound_export

/-- Door-IV Lane-3 FAMILY PRIZE-CONSTANT no-go export: over a nonempty admissible family with a uniform
super-diagonal floor, no uniform floor-scale prize constant `K < c₀` can hold.  Contrapositive form of
the family lower bound. -/
theorem doorIV_noFamilyPrizeConstantBelowSuperDiagonal_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} {K : ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hlt : K < ShawValueCapstone.superDiagonalFloorConst) :
    ¬ (∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :=
  DoorIVPrizeShawTetrachotomySynthesis.not_familyPrizeFloorConstant_lt_superDiagonal
    hn hfloor hlt

#print axioms doorIV_noFamilyPrizeConstantBelowSuperDiagonal_export

/-- Door-IV Lane-3 FAMILY PRIZE-CONSTANT packaged lower-bound export: any uniform floor-scale prize
constant over a nonempty family with a uniform super-diagonal floor satisfies `c₀ ≤ K`, with
`1 < c₀`, hence `1 < K`.  This packages the lower-bound and strict-above-one facts; it is only the easy
lower bound on the achievable constant, not the open upper-bound direction. -/
theorem doorIV_familyPrizeConstantSuperDiagonalPackage_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} {K : ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hbound : ∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K
      ∧ (1 : ℝ) < ShawValueCapstone.superDiagonalFloorConst
      ∧ (1 : ℝ) < K :=
  DoorIVPrizeShawTetrachotomySynthesis.familyPrizeFloorConstant_ge_superDiagonal_gt_one
    hn hfloor hbound

#print axioms doorIV_familyPrizeConstantSuperDiagonalPackage_export

/-- Door-IV Lane-3 FAMILY PRIZE-CONSTANT unit no-go export: over a nonempty admissible family with a
uniform super-diagonal floor, no uniform floor-scale prize constant `K ≤ 1` can hold.  This is the
consumer form of the lower bound `c₀ ≤ K` together with `1 < c₀`; the open upper-bound direction is
unchanged. -/
theorem doorIV_noFamilyPrizeConstantAtMostOne_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} {K : ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hK : K ≤ 1) :
    ¬ (∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :=
  DoorIVPrizeShawTetrachotomySynthesis.not_familyPrizeFloorConstant_le_one
    hn hfloor hK

#print axioms doorIV_noFamilyPrizeConstantAtMostOne_export

/-- Door-IV Lane-3 concrete unit no-go export: over a nonempty family with positive `nᵢ` and a uniform
super-diagonal floor, the bare Plancherel-unit floor-scale certificate `Mᵢ ≤ √nᵢ` cannot hold uniformly.
This is the `K = 1` specialization of the family constant lower bound; it is only a lower-bound
constraint on prize constants, not the open upper-bound direction. -/
theorem doorIV_noFamilyPrizeConstantOne_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ¬ (∀ i, M i ≤ NoFifthDoorTetrachotomy.prizeScale (n i)) :=
  DoorIVPrizeShawTetrachotomySynthesis.not_familyPrizeFloorConstant_one hn hfloor

#print axioms doorIV_noFamilyPrizeConstantOne_export

/-- Door-IV Lane-3 FAMILY PRIZE-CONSTANT strict-lower-bound export: under a uniform super-diagonal
floor, any uniform floor-scale prize constant `K` that bounds the family must satisfy `1 < K`.  This
is the positive consumer form complementary to the `K ≤ 1` no-go; it proves no upper bound. -/
theorem doorIV_familyPrizeConstantStrictlyAboveOne_export {ι : Type*} [Nonempty ι]
    {M n : ι → ℝ} {K : ℝ} (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hbound : ∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :
    (1 : ℝ) < K :=
  DoorIVPrizeShawTetrachotomySynthesis.familyPrizeFloorConstant_gt_one hn hfloor hbound

#print axioms doorIV_familyPrizeConstantStrictlyAboveOne_export

/-- Door-IV Lane-2 FAMILY sharpened-BGK width export: the exact sharpened corridor width is `√Lᵢ/c₀`,
strictly below the bare conditional BGK width `√Lᵢ` and, in the prize regime `Lᵢ<nᵢ`, below the trivial
width `√nᵢ`.  Pure corridor bookkeeping; CORE remains open. -/
theorem doorIV_shawValueFamilySharpenedBGKWidth_export {ι : Type*} {n L : ι → ℝ}
    (hL : ∀ i, 0 < L i) (hLn : ∀ i, L i < n i) :
    ∀ i, ((1 : ℝ) /
          (ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i))
          = Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst)
      ∧ Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst < Real.sqrt (L i)
      ∧ Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst < Real.sqrt (n i) := by
  intro i
  have hwL : Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst < Real.sqrt (L i) :=
    ShawValueSharpenedBGKCorridorFamily.shawValueFamily_sharpened_bgk_width_lt_bgk_width hL i
  have hLn_sqrt : Real.sqrt (L i) < Real.sqrt (n i) :=
    ShawValueBGKBracket.shawValueFamily_sharp_width_lt_trivial (fun j => (hL j).le) hLn i
  exact ⟨ShawValueSharpenedBGKCorridorFamily.shawValueFamily_sharpened_bgk_width hL i,
    hwL,
    lt_trans hwL hLn_sqrt⟩

#print axioms doorIV_shawValueFamilySharpenedBGKWidth_export

/-- Door-IV Lane-2 FAMILY sharpened-BGK corridor package export: under a uniform super-diagonal floor,
a supplied BGK-shaped ceiling, and the prize-regime comparison `Lᵢ<nᵢ`, every Shaw value lies in the
sharpened conditional corridor `[c₀/√Lᵢ, 1]`, whose exact multiplicative width is `√Lᵢ/c₀`; this width
is strictly below both the bare conditional-BGK width `√Lᵢ` and the trivial width `√nᵢ`.  This is a
single citable package for the sharpened-BGK family corridor.  Conditional bookkeeping only; no CORE
cancellation claim. -/
theorem doorIV_shawValueFamilySharpenedBGKCorridorPackage_export {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ ShawValueCapstone.prizeScale (n i) (L i))
    (hLn : ∀ i, L i < n i) :
    ∀ i, (ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i)
          ≤ ShawValueCapstone.shawValue (M i) (n i) (L i)
        ∧ ShawValueCapstone.shawValue (M i) (n i) (L i) ≤ 1)
      ∧ (1 : ℝ) / (ShawValueCapstone.superDiagonalFloorConst / Real.sqrt (L i))
        = Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst
      ∧ Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst < Real.sqrt (L i)
      ∧ Real.sqrt (L i) / ShawValueCapstone.superDiagonalFloorConst < Real.sqrt (n i) :=
  ShawValueSharpenedBGKCorridorFamily.shawValueFamily_sharpened_bgk_corridor_package
    hn hL hfloor hceil hLn

#print axioms doorIV_shawValueFamilySharpenedBGKCorridorPackage_export

/-- Door-IV Lane-3 DILATION-TOWER abstract export: any fixed per-level descent factor `c` iterates as
`c^a`.  In the dilation route the proven factor is `2`, so the recursion reproduces the trivial
`2^a = n` ceiling rather than the prize `2^(a/2)` scale.  Constraint packaging only; no CORE upper
bound or cancellation claim. -/
theorem doorIV_descent_tower_le_export {M : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ k, M (k + 1) ≤ c * M k) :
    ∀ a, M a ≤ c ^ a * M 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationTowerSaturates.descent_tower_le hc hstep

#print axioms doorIV_descent_tower_le_export

/-- Door-IV Lane-3 DILATION-TOWER trivial-saturation export: the factor-`2` recursion plus singleton
base mass `≤ 1` gives `M a ≤ 2^a`, exactly the trivial cardinality ceiling.  This is the stable citable
form of the no-√-saving lock for the iterated dyadic descent route. -/
theorem doorIV_dilation_tower_saturates_trivial_export {M : ℕ → ℝ}
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (hbase : M 0 ≤ 1) :
    ∀ a, M a ≤ 2 ^ a :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationTowerSaturates.dilation_tower_saturates_trivial
    hstep hbase

#print axioms doorIV_dilation_tower_saturates_trivial_export

/-- Door-IV Lane-3 CONCRETE dilation-tower export: along a descending dyadic chain of actual finite
sets, iterating `worstPeriod ψ (G k) ≤ 2 * worstPeriod ψ (G(k+1))` gives
`worstPeriod ψ (G 0) ≤ 2^a * worstPeriod ψ (G a)`.  This realizes the saving-free tower on the prize
object itself, not just an abstract sequence. -/
theorem doorIV_worstPeriodChain_le_two_pow_export {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (G : ℕ → Finset F) (g : ℕ → F) (hg : ∀ k, g k ≠ 0)
    (hdisj : ∀ k, Disjoint (G (k + 1)) ((G (k + 1)).image (fun y => g k * y)))
    (hchain : ∀ k, G k = G (k + 1) ∪ (G (k + 1)).image (fun y => g k * y)) :
    ∀ a, _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ (G 0) hne
        ≤ 2 ^ a * _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ (G a) hne :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationTowerConcrete.worstPeriodChain_le_two_pow
    hne G g hg hdisj hchain

#print axioms doorIV_worstPeriodChain_le_two_pow_export

/-- Door-IV Lane-3 CONCRETE trivial-saturation export: if the bottom of the dyadic chain has worst
period `≤ 1`, the actual top object satisfies only `≤ 2^a` by iterating the factor-`2` recursion.  This
is a constraint/no-go for the dilation route, not a prize bound. -/
theorem doorIV_worstPeriodChain_saturates_trivial_export {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (G : ℕ → Finset F) (g : ℕ → F) (hg : ∀ k, g k ≠ 0)
    (hdisj : ∀ k, Disjoint (G (k + 1)) ((G (k + 1)).image (fun y => g k * y)))
    (hchain : ∀ k, G k = G (k + 1) ∪ (G (k + 1)).image (fun y => g k * y))
    {a : ℕ} (hbase : _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ (G a) hne ≤ 1) :
    _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ (G 0) hne ≤ 2 ^ a :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVDilationTowerConcrete.worstPeriodChain_saturates_trivial
    hne G g hg hdisj hchain hbase

#print axioms doorIV_worstPeriodChain_saturates_trivial_export

end ArkLib.ProximityGap.Frontier.CampaignProvenIndex
