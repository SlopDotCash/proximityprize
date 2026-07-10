/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipCensusSharpened
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
-- §2.2 the exact projective form of the production incidence core:
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveWorstCaseIncidence
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientSupport
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveRankTwoAPI
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveCosetWeight
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveMetricUnification
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveProperQuotientBall
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientBall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R383HalfRadiusMDSLineRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfRadiusConicSecantBoundaryFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfRadiusStrictSlackLowRateRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenthPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthCutoffArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterObtuse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSparseSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportThreeSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourSixStratumRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourTopTraceCoupling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourTopTraceResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSmoothCounterexampleF97
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterMu16Locator
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleOperationalCountConnector
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleFinalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterOperationalBracket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalOperationalBracket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterCommonFactorOwnershipAmplifier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorBadCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorCanonicalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAAdjacentFloorExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorGenericSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAdjacentExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterSaturatedFiveCoreBarrier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterPredecessorFourClusterCapacity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterPredecessorFourPencilReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterFourPencilExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorResidualEquiv
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterProjectiveStructuredSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterExtremeZeroJohnsonBand
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterProjectiveExtremeZeroSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterJointWitnessCharge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterSharedFreshCoordinateCounterexampleF11
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshCoordinate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshTripleRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCollinearMismatchCharge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterInterleavedCollapseNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceOperator
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceLocalRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferencePencilPropagation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPropagationPlotkinNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MaximalMinorIdealCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceMaximalMinorBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceUnrestrictedKernelRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallSubsetRankLocalization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W7RateHalfFingerprintSeal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterNextLatticeFourCoreBarrier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCollapsedClusterInjection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterComplementaryCores
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCrossCoreScalar
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterFreshPetalAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreUnionSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterEqualSlopeHighCores
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCorePetalGrowth
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterEqualSlopeJohnsonClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreUnifiedClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreCompleteResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreSharpSecantExtraction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourLongOutsiderCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourRegularSignatureRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleCollinearity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourThreeHoleSaturation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourFourHoleClasses
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSharedHolePrimitive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSyndromeDegeneracy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreClosed
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSyndromeReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSignatureRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSixRootSupport
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSixLongStratum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSixSignatureRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSevenRootFiber
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSevenLongStratum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterExceptionalDirectionPuncture
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCoreThirteenClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCapGlobalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionSourceAlignment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCoreBandSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterFreshPetalPruning
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterGlobalPetalSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPetalOverlapGrowth
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPetalIteration
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPetalSelectionRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R396PolynomialLinePluckerSyzygy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCocircuitRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterAbstractCocircuitRefuted
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeCommonFactor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeAnchorRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFour
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourPopulation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SeventeenThirtyTwoDeltaStarFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfRadiusEvenThirdBlockObstruction
-- §2.3 live reduction dossier (#371 closed, #389 open):
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarPinAllWitness
import ArkLib.Data.CodingTheory.ProximityGap.PinBeyondJohnson
import ArkLib.Data.CodingTheory.ProximityGap.PackingDeepBandMiss
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBelowUDR
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiberCodewordList
import ArkLib.Data.CodingTheory.ProximityGap.MonomialSupplyChoose
-- §2.5 live routes (LD⇒MCA frontier):
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import ArkLib.Data.CodingTheory.ProximityGap.CurveCloseSetTargetBound
import ArkLib.Data.CodingTheory.ProximityGap.FoldedCurveCloseSetBound
import ArkLib.Data.CodingTheory.ProximityGap.SeparationSurvivalCount
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignLineDecodable
-- §2.6 GM-MDS route:
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma22
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep
import ArkLib.Data.CodingTheory.GMMDS.LovettDivisibility
-- §3 THE SHAW OPERATOR — the unified unknown + the closed prize conjecture:
import ArkLib.Data.CodingTheory.ProximityGap.ShawOperator
-- §3 (W6) the machine-checked second-moment / L² no-go + far-restriction + falsification:
import ArkLib.Data.CodingTheory.ProximityGap.ShawSecondMoment
-- §Y the historical entropy candidate, its counterexamples, and the discrete ladder ceiling:
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyPinRefuted
-- §D THE DEMAND-SIDE LANE (#389) — the CensusDomination #bad-scalar count, r=3 closed (O172):
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR3Bound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR4Bound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR5Bound
import ArkLib.Data.CodingTheory.ProximityGap.FactorizationRigidity

/-!
# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║   THE PROXIMITY PRIZE WORKBENCH  ·  one file, everything you need, write here  ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

**Mission (proximityprize.org / ABF26 = Arnon–Boneh–Fenzi 2026, ePrint 2026/680).**
Produce a *novel, complete, closed* theorem (no further open math, no incomputable lemma) for
*explicit, constant-rate, smooth* Reed–Solomon codes in the **prize regime**.  The MCA and list
decoding challenges are distinct fixed-code thresholds.  Known implications between them change
the radius, the code, or the constants; they do not identify the two exact `δ*` values for free.

⚡ **READ FIRST — the current dossier is `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`** (v3,
supersedes the v2/#464 dossier): the complete map of what is proven, refuted, and open as of
2026-07-01. The freshest state-of-play summary is **§5 below** (added 2026-07-01); the sections
§1.5/§R.* below it are the historical layers of the campaign (kept because each pivot is itself
load-bearing context). The δ* target now has an **exact-rational form**: `δ* = (1−ρ) − m*/n`
(master-gap identity), so "pin δ*" = "compute the integer m*" = the wall.

────────────────────────────────────────────────────────────────────────────────
## §0.  THE PRIZE REGIME — pin this or you are wasting time
────────────────────────────────────────────────────────────────────────────────
* Code: `C = RS[F, L, k]`, `L` a **smooth** (FFT/NTT, multiplicative-subgroup `μ_n`)
  evaluation domain, `n = |L| = Fintype.card ι`.
* Rate: `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}` — **constant rate**, so `k = Θ(n)` (`prizeRates`).
* Threshold: `ε* = 2^(-128)` (`epsStar`); operationally `q·ε* ≈ n` for `q ≈ n·2^128`.
* Field: `q = |F|` large, `q ≈ n·2^128` (so `q·ε* ≈ n`); positive rate `0 < k`.
* Target window: pin `δ*` in the **window interior** `(1−√ρ, 1−ρ−Θ(1/log n))` — the
  beyond-Johnson, below-capacity band. Johnson `1−√ρ` is already done; capacity `1−ρ` is
  the wall. **Anything that reduces to Johnson, to capacity-for-constant-DIM, or to an
  incomputable lemma is OUT.**

⚠️ **DEGENERACY TRAP (do not target these).** The *real-valued* `grandMCAChallenge` /
`grandListDecodingChallenge` collapse: `grandMCAChallenge_iff_epsMCA_one` (radius-one only),
and `not_grandListDecodingChallengeRS_of_pos` (the LD one is *false* for `0<k`, `ε*<1`).
**The faithful fixed-code targets are the operational supremum `mcaDeltaStar` (§2) and the
finite-lattice specification `GrandChallengesLattice.mcaPrizeLatticeResolved`.**  The uniform
`mcaConjecture` is a separate, substantially stronger sufficient route; it is not definitionally
equivalent to determining the four prize instances.

────────────────────────────────────────────────────────────────────────────────
## §1.  THE EXACT TARGET  (choose the convention explicitly)
────────────────────────────────────────────────────────────────────────────────
**(T1) The operational fixed-code threshold.** Prove an equality for
  `MCAThresholdLedger.mcaDeltaStar`, the supremum of the good real radii.  A jump certificate has
  the honest asymmetric shape: every `δ < δ₀` is good and `δ₀` is bad, hence
  `mcaDeltaStar = δ₀`.
**(T2) The faithful finite-lattice threshold.** Supply
  `GrandChallengesLattice.mcaPrizeLatticeResolved domain τ`.  Its specification says exactly that
  `τ j` is good and maximal among the meaningful radii `i/n`.  At an interior bad jump `s/n`, the
  lattice answer is the predecessor index `s-1`, whereas the operational supremum is `s/n`.
  This one-lattice-step distinction is intentional and must not be erased.
**(T3) The uniform MCA conjecture** `ProximityGap.mcaConjecture` (ABF26 §4.5):
  `∃ c₁ c₂ c₃, ∀ RS[F,L,k], ∀ δ < 1−ρ,  ε_mca(RS,δ) ≤ (1/q)·n^{c₁}/(ρ^{c₂}·η^{c₃})`,
  `η = 1−ρ−δ`. Constants quantified BEFORE the ∀-over-codes. Proving this resolves the
  MCA witness problem at every rate (`nonempty_mcaLowerWitness_of_mcaConjecture` → `mcaPrize`),
  but it is stronger than T1/T2 and should not be advertised as their equivalent.
**(T4) Treat the list-decoding threshold as a separate target.** ABF26 Theorem 5.1 sends an LD
  bound to MCA with a square-root radius loss; Theorems 5.2/5.3 send sufficiently small CA to an
  LD statement under additional hypotheses and, in one case, for a related code.
  `GG25MCAFromCurveDecodability` is an upstream sufficient condition for MCA, not an
  MCA-to-LD equivalence.  Invoke only the direction whose hypotheses and parameters are proved.

Do **not** use `GrandMCAResolution` as an interior-jump synonym for T1: its `bound` field requires
the cutoff itself to be good.  Consequently it cannot represent the common case in which `δ₀`
is the first bad real radius and `mcaDeltaStar = δ₀`.  Use T1 or T2 instead.

The `YOUR CONJECTURE HERE` slot at the bottom is where the closed-form `δ*(ρ,ε*,n)` and its
proof go. It must be **complete**: a single computable `δ*`-expression, proven, no residual.

────────────────────────────────────────────────────────────────────────────────
## §1.5  GROUND-TRUTH PIVOT (2026-06-17) — the target reframed; read before attacking
────────────────────────────────────────────────────────────────────────────────
Late-2025/2026 results moved the goalposts (writeup: `docs/kb/prize-groundtruth-pivot-…`).
All claims below are exact-checked (verify-don't-believe):
* **Capacity `1−ρ` is DISPROVEN**, not merely "the wall": up-to-capacity proximity fails
  for explicit RS — Crites–Stewart (ePrint 2025/2046), Diamond–Gruen (2025/2010), BCHKS
  (2025/2055). So "pin δ* just below capacity" is the WRONG target; the §0 window's upper
  edge is now a *theorem-backed* impossibility, not an open wall.
* **The honest live target is above-Johnson `O(1)/|F|` FRI soundness**, which Chai–Fan
  (2026/861) reduces to **Conjecture 7.1** (*sparse-worst-case dominance*: the worst general
  direction is dominated by 3-position-sparse witnesses). In-tree machinery already built:
  `ActionOrbitFRI` (Thm 2.1: bad-`α` set of the two-monomial pencil = a union of
  `⟨μ^{b−a}⟩`-orbits ⟹ `O(1)/|F|`), `ActionOrbitGeneralF` (orbit compression is
  monomial-ONLY: `eigen_forces_monomial`; general `f` → the BGK incidence wall),
  `BridgeLoop41`, `Frontier/LaneB_Q2_SparsityExclusive`, `Frontier/_ChaiFanBasePanelGate`.
* **Status of the two open inputs:**
  · **(UPDATE 2026-07-07, rounds 15–18 — read dossier §25–§28 FIRST):** Problem B is now the
    OFF-DIAGONAL constant-C tower (raw away-Wick REFUTED as universal); rungs ≤ 2 are
    Weil-classical (r=2@deg2 discharged mod `WeilQuarticPairs`, a pure Mathlib gap); the deg-2
    face ⟺ Karatsuba thin-shift sup (two-sided, `_R18Deg2FaceConverse`); first genuinely-open
    object = the r=3 sextic family cancellation in the β∈(4,6) gap + the deep `r ≈ ln q` wall.
  · **Q1** (Chai–Fan Conj 4.12, the conjugate-norm non-vanishing) is GENUINELY NON-character-sum
    and PROVEN at `d=16` at prize scale (`Frontier/_wfLB2_Q1Direct_d16`: `V_16^prim = ∅` all
    char, bad-reduction threshold 881 ≪ 16⁴); route-(i) self-similarity breaks in char-`p` at
    `d=32` (`Frontier/_wfLB_Q1RouteICharPGap`), so `d≥32` needs the direct resultant route.
  · **Q2 = Conj 7.1 is THE OPEN GATE.** `LaneB_Q2_SparsityExclusive` proves the orbit
    compression is *two-monomial-exclusive* (a 3-monomial's two free coeffs rescale by
    `μ^{b−a}≠μ^{c−a}`), so the general/≥3-monomial worst case is "thrown back on a genuine
    counting/character-sum bound = BGK/Paley/BCHKS 1.12". Coset-exhaustive evidence: at `N=8`
    the worst above-Johnson bad-count is `4 = O(1)/|F|` (a 3-position witness — Conj 7.1's
    dominating class), but the UNRESTRICTED worst-case bad-count GROWS with `N` (`N=16: ≥7`).
    Net: `above-Johnson O(1)/|F| ⟺ assume Conj 7.1`.
* **Bottom line for this file:** the reframe LOCALIZES the wall (whole-window → the
  sparse-dominance step) but does not remove it — Conj 7.1's `≥3`-monomial case IS the same
  BGK √-cancellation core that §3 (the Shaw operator) already targets:
  `M(μ_n) ≤ C·√(n·log(p/n))`, `C` empirically `≈ 1.31–1.51` at `β=4`, provably unreachable
  by the 6 known moment/algebraic levers (phase-blindness dichotomy). A winning closed `δ*`
  must still beat that core — whether stated in the `δ*`/`mcaConjecture` form (§1) or the
  above-Johnson/Conj-7.1 form. Pick the surface; the open math is one object.
* **δ\*-side scaffold is now AIRTIGHT in Lean (so you only need the one inequality).**
  `Frontier/_PrizeFloorOfBGK.prizeFloor_window_of_BGK_and_incidence` (axiom-clean) converts the
  above-Johnson incidence bound `WorstCaseIncidenceBounded C δ B` (= BCHKS Conj 1.12, the per-frequency
  `√q·B` cancellation over the annihilator hyperplane) into the δ\* prize WINDOW
  `δ_win ≤ mcaDeltaStar (evalCode …) ε* ≤ (1−ρ)−1/(C·L)` — FLOOR via the proven
  `OpenCoreConditionalPin.worstCaseIncidence_pin`, CEILING via the proven
  `KKH26AsymptoticCeiling.kkh26_mcaDeltaStar_le_capacity_sub_log`. So: **prove the incidence Prop and
  this lemma turns the crank to δ\* with zero further gaps.** ⚠ CAVEAT (don't waste effort): the bare
  BGK sup-bound `max_{b≠0}‖η_b‖ ≤ M` alone is necessary-but-INSUFFICIENT — its only in-tree route to
  incidence (`lineIncidence_le_mean_add`) pays the naive `q·B` (no inter-frequency cancellation),
  vacuous at the prize budget. The OPERATIVE open input is the incidence/`√q·B` form (BCHKS 1.12),
  strictly stronger than the sup-bound. ⇒ `YOUR CONJECTURE HERE` = `WorstCaseIncidenceBounded` at the
  window radius (equivalently the `√q·B` hyperplane cancellation), NOT the bare sup-bound.

────────────────────────────────────────────────────────────────────────────────
## §2.  THE SUBSTRATE  (PROVEN, axiom-clean, ready to apply — build on these)
────────────────────────────────────────────────────────────────────────────────
**The governing law** (`MCAThresholdLedger`):
  `mcaDeltaStar C ε* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}`.
  · `le_mcaDeltaStar_of_good`  — lower bound on δ* from a good radius (incidence ≤ q·ε*).
  · `mcaDeltaStar_le_of_bad`   — upper bound on δ* from a bad witness.
  · `FarCosetExplosion.epsMCA_ge_far_incidence` — `ε_mca ≥ incidence/q` (the law's engine).

**Capacity side — SOLVED for constant DIMENSION `k=O(1)`** (NOT the prize, but the template):
  · `KKH26CeilingMarch.interiorCeiling_march` — worst-case `incidence(1−r/2^μ) ≤ C(n,r)/r`
    (iSup over ALL stacks), ⟹ FFT-domain RS reaches `δ*=(1−ρ)−1/n` for `k=O(1)`.
  · `KKH26CeilingMarch.march_badScalars_card_mul_le` — `#bad·(d+2) ≤ C(n,d+2)` (the count).

**Granularity ladder** (`GranularityLadderRS.mcaDeltaStar_rs_eq_granularity`):
  `δ* = j/n` on bands `3(j−1)+k ≤ n`, `j+1+k ≤ n`, `j+1 ≤ q`, `ε*∈[j/q,(j+1)/q)`. EXACT.

**Boundary law** (`BoundarySupExactness.rs_boundary_epsMCA_eq`):
  `ε_mca(RS, δ) = n/q` for `3∣n`, `6<n`, `k=n−4`, `2 ≤ δ·n < 3`.

**Ownership count — PROVEN TIGHTLY BRACKETED** (`OwnershipCensusSharpened`):
  · `sharpened_badScalars_card_mul_choose_le` — `#bad·C(w₀+1,d+1) ≤ C(n,d+1)·(n−d−1)` (LOWER).
  · `deviation_ownership_card` — the CEILING: deviation stacks realize EXACTLY `C(w−1,d+1)`,
    so NO per-witness-subset bound can do better. **This surface is PROVEN EXHAUSTED (§3).**
  · `sharpened_epsMCA_le` — wires the sharpened count to `epsMCA`.

**Energy / sub-Johnson list chain** (`GVHBKEnergyReduction`, `AdditiveEnergyRepBound`):
  `GVRepBound G M` (`r(c)≤4|G|^{2/3}`) ⟹ `E(G)³ ≤ 260|G|⁸` ⟹ list `T ≲ n^{11/6} ≪ n²`.
  **√-loss is FATAL** (`T² ≤ |G|·E`; even `E=|G|²` → list `n^{3/2}`, sub-Johnson not capacity).

**Paper-bound bridges** (`GrandChallenges`, all wired to witnesses):
  GKL24 `MCALowerWitness.ofLinearOnePointFiveJohnsonGKL24`, BCHKS25 `…ofJohnsonBCHKS25` /
  `…ofJohnsonJumpBCHKS25AutoRadius`, CS25 `…ofRSBreakdownCS25` (capacity-side ε_ca=1),
  KK25 `…ofLowerCapacityBCHKS25KK25`, DG25 `…ofSamplingDG25`.

────────────────────────────────────────────────────────────────────────────────
## §2.5  LIVE ATTACK ROUTES  (freshest in-progress machinery — the actual frontier)
────────────────────────────────────────────────────────────────────────────────
Three routes from the latest literature connect the LD challenge to the MCA challenge (solve
one ⟹ solve both). Each is mostly built in-tree; its GAP is the one open piece to attack.

**(R1) GG25 curve-decodability ⟹ MCA** (Guruswami–Gabizon, ePrint 2025/2054).
  · `ProximityGap.CurveDecodable C ℓ δ a b` / `MarkedCurveDecodable` — a degree-`ℓ` curve
    through `a` close points explains `≥ b` of them. (`GG25CurveDecodability`, `GG25MarkedCurve`.)
  · `GG25Lemma32.disagree_spread_bound` (Lemma 3.2) + `GG25MCAFromCurveDecodability`
    (`all_seeds_relClose`) — **curve-decodability ⟹ MCA (Thm 3.3), DONE** modulo the input.
  · **GAP:** GG25 proves curve-decodability only for FRS / multiplicity / random RS (field
    LINEAR in `n`), NOT explicit plain RS (the prize). Plain-RS curve-decodability is open.

**(R2) CZ25 subspace-design list-recovery** (the GG25 §4.3 curve-decodability argument).
  · `ProximityGap.exists_determining_tuple` — a tuple `v ⊆ T` whose coordinates **determine**
    a dim-`≤ r` list span `H`, when design param `θ < θ' = 1−δ`. Axiom-clean (`SubspaceDesignLineDecodable`).
  · `SeparationSurvivalCount.card_surv_ge` — combined separation + agreement count.
  · **GAP:** needs the list-recovery input `CZ25CoordFiberCap` (the `δ`-close codewords span dim `≤ r`).

**(R3) GM-MDS / Lovett higher-order MDS ⟸ δ*** (Lovett arXiv:1803.02523, AGL24).
  · `ArkLib/Data/CodingTheory/GMMDS/Lovett*` (10+ files) — the chain `δ* ⟸ L(δ) ⟸ higher-order
    MDS` reduces to the last residual `AGL24.GMMDSDualZeroPatternTheorem` (dual zero pattern).
  · **GAP:** the dual-zero-pattern theorem.

**(R4) The SYMMETRIC-FUNCTION / coset-rigidity route — the direct far-line incidence, reduced.**
  The far-line incidence is `Z/n`-dilation-invariant, so the extremal directions are monomials
  `X^a` (`FarLineIncidenceEquivariance`); the subgroup directions `X^{n/2}` are CORRELATED and
  discarded (`MonomialSubgroupCorrelated.lean`: `X^{n/2}=±1` on `μ_n`; jointly close on `μ_{n/2}`).
  For a NON-correlated direction `(X^a, X^b)`, working `mod m_S = ∏_{x∈S}(X−x)` (`S` the agreement
  set, `|S| = w = (1−δ)n`) the residues `X^{w−1+j} mod m_S` have complete-homogeneous-symmetric
  coefficients, so the bad scalar is a fixed symmetric function `γ = σ(e_•(S))` under vanishing
  of further symmetric functions of `S`. CLEANEST case `dir(k+1,k+2)`, `w=k+2` (PROVEN reduction,
  `probe_symmetric_function_reduction.py`, verified vs exact list-decode):
    `B = { −e_1(S) : S ⊆ μ_n, |S| = k+2, e_2(S) = 0 }`.
  · **MEASURED (the prize-regime facts):** the worst non-correlated incidence is **q-INDEPENDENT**
    and **`O(n)`** (`dir(5,7)`: `64,72,40,40` over `q=97..353`; `dir(5,6)→n`), crossing the prize
    level `q·ε* = n` strictly **inside the window** `(1−√ρ, 1−ρ)` (between `δ=0.562` and `0.625`
    at `n=16,ρ=1/4`). The bad set is a union of `μ_{n'}` cosets (`n'=n/gcd(b−a,n)`).
  · **GAP (the conjecture to prove — beats W4):** the symmetric-function value set
    `{ σ(S) : S ⊆ μ_n, |S|=w, vanishing-symmetric constraints }` has **`O(1)` `μ_n`-cosets**, i.e.
    worst non-correlated incidence `≤ C·n`. This is a CONCRETE, **q-independent** cyclotomic
    symmetric-function statement — it does NOT route through the incomplete-Gauss-sum-over-`F_q`
    wall (W4); the `q`-independence (proven by `mca_badscalar_general`, `#bad ≤ C(n,w)`) makes the
    whole quantity finite combinatorial. Proving the `O(n)` coset bound + the incidence/`δ*`
    calibration (worst incidence `= n` at `δ = δ*`) closes the MCA prize directly. The dilation
    `γ_S ↦ g^{b−a}γ_S` forces the coset structure; the open content is the *rigidity* (why all
    consistent `S` collapse to `O(1)` cosets).

Each GAP is a candidate `YOUR CONJECTURE HERE`: a closed plain-RS curve-decodability bound (R1),
a closed `CZ25CoordFiberCap` list-recovery dim bound (R2), the dual-zero-pattern theorem (R3),
or the `O(n)` symmetric-function coset-rigidity bound (R4) — any one, proved in the prize regime
without residual, closes the prize via its bridge.

────────────────────────────────────────────────────────────────────────────────
## §3.  THE WALLS  (PROVEN dead ends — every accessible technique stops here)
────────────────────────────────────────────────────────────────────────────────
**(W1) Per-witness counting is PROVEN EXHAUSTED.** `deviation_ownership_card` caps ownership
  at `C(w−1,d+1)`; production `k=Θ(ρn)` (`r=Θ(n)`) needs ownership `e^{Θ(n)}` while the
  scheme caps at `r+1`. The δ* prize needs *a genuinely different counting surface* — none known.
**(W2) Energy is the wrong lever.** Open at exponent `2+o(1)` (hard `7/3` barrier); above
  `p^{2/3}` no nontrivial subgroup-energy bound exists; and the √-loss (W-chain above) caps
  any energy bound at sub-Johnson. `WeilRegimeClosure` "capacity" = LARP (supply ≠ incidence).
**(W3) Confluent-Stepanov `n^{2/3}`** (the energy route's sharp input) needs the `a`-mixing
  Wronskian rep-point multiplicity — explicit caps at order 2, moment-combination trivial,
  same-`a`/distinct-roots/2-relation all fail (5 angles). Multi-week, no separable entry brick.
**(W4) Weil/√q wall.** `|η_b| ≪ √q` is vacuous for `|G|<√q`; coordinate-pigeonhole incidence
  surface refuted (target is the low-weight-error syndrome *variety*, not a coordinate ball).
**(W5) The budget/supply route pins δ* but ONLY ABOVE the window — PROVEN.** The all-stack
  `allWitnessDom_epsMCA_le` (`iSup` over *every* word stack — a *different* counting surface than
  W1's per-witness one) composed with the KKH26 upper witness PINS `δ* = 1−r/2^μ`
  UNCONDITIONALLY for the bulk/low-degree range, no `CensusDomination`
  (`KKH26AllWitnessPin.kkh26_deltaStar_pin_allWitness`; the budget-below-supply arithmetic is
  discharged outright for all `r ≤ √(2^μ)` by `choose_bulk`, giving the infinite family
  `kkh26_deltaStar_pin_lowdegree`; concrete `δ*=3/4` at `kkh26_deltaStar_pin_allWitness`'s
  `deltaStar_pin_concrete_F4129`; all axiom-clean). BUT this pins `δ*` at `ε* = supply/p`, and
  `1−r/2^μ = 1−ρ−Θ(2^{−μ})` sits in the near-capacity strip `(1−ρ−Θ(1/log n), 1−ρ)` — STRICTLY
  ABOVE the window-upper `1−ρ−Θ(1/log n)` for *every* `(μ,r)` (verified `in-win? = False`,
  `scripts/probes/probe_deltastar_window_calibration.py`). So the budget/supply machinery, though
  unconditional and general, structurally CANNOT reach the window interior: the prize `ε*=2^{−128}`
  is a *different, smaller* point on the `δ*(ε*)` curve where the line–ball incidence must be
  *sub-exponential* (= the open W4 incidence / incomplete-Gauss-sum problem). Do not expect a
  sharper budget/supply count to win the prize — it provably pins the wrong point.
**(W6) The second-moment / Fourier-L² method is PROVEN EXHAUSTED (machine-checked, `ShawSecondMoment`).**
  The Shaw operator's exact second moment `∑_{s₀}‖𝒮‖² = |V|·M`, `M = ∑_{ψ≠0,ψ⊥s₁}‖Ŝ(ψ)‖²`
  (`shawError_second_moment`) brackets the prize's worst case
  `max_{s₀}‖𝒮‖ ∈ [√M, √(|V|·M)]` (`exists_shawError_sq_ge` + `shawError_sq_le_second_moment`) — a
  multiplicative gap of EXACTLY `√|V| = q^{n/2}` (the union tax over the `|V|` base points). So no
  L²/moment/union argument can *certify* `‖𝒮‖≤B`; it can only *falsify*
  (`not_mcaShawConjecture_of_lt_secondMoment`: `B²<M ⟹` the bound fails — an unconditional δ* CEILING).
  The far-coset restriction is FORCED, not a convention: a fully-contained line gives `𝒮 = |V|−|S|`
  exactly (`shawError_of_line_subset`, `not_mcaShawConjecture_of_line_subset`). **REGIME TRAP (avoided):**
  the single-Hamming-ball model makes the prize trivial (`incidence ≤ ⌊w₁/(w₁−R)⌋ < budget`); the TRUE
  object is `S = δ-neighborhood of the CODE C`, so `M = ∑_{ψ∈C^⊥, ψ⊥s₁, ψ≠0} |K(wt ψ)|²` — the
  **dual-code Krawtchouk sum**, whose uniform worst-`u₀` bound IS W4 (and equals the list-size bound, so
  one bound closes BOTH challenges). The prize needs genuine uniform √-cancellation of THAT sum, beyond
  any L² estimate.

────────────────────────────────────────────────────────────────────────────────
## §4.  WHAT A WINNING CONJECTURE MUST DO  (the closure contract)
────────────────────────────────────────────────────────────────────────────────
1. Give a **single computable** `δ*(ρ, ε*, n)` (or an `ε_mca(RS,δ)` bound) — no `∃`-over-
   incomputable objects, no named residual, no further open lemma.
2. Hold in the **prize regime** (constant `ρ`, `k=Θ(n)`, `q≈n·2^128`) — verify it does NOT
   collapse to Johnson (`1−√ρ`) or to the constant-DIM capacity result (`interiorCeiling_march`).
3. Beat the per-witness wall (W1): the incidence bound must NOT route through per-witness
   subset ownership (proven `e^{Θ(n)}`-short). It needs a new counting surface.
4. Be **machine-checkable**: instantiate at one concrete prize-shaped RS code and `decide`/
   prove the bound, then prove the general statement.

Once proved, wire it to an actual `mcaDeltaStar` equality (T1) or
`mcaPrizeLatticeResolved` (T2).  Only claim the stronger uniform `mcaConjecture` (T3) if its
all-fields/all-domains quantifiers have really been discharged; then use the applicable LD bridge
(T4).

────────────────────────────────────────────────────────────────────────────────
## §5.  STATE OF PLAY 2026-07-01 — the #464 campaign outcome (read this, then attack)
────────────────────────────────────────────────────────────────────────────────
The #464 campaign (dossier v2 + 179 comments, 2026-06-22 → 06-27) is consolidated in
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`. What changed since the sections below were written:

**(1) The target is now an exact rational.** `δ* = (1−ρ) − m*/n`, `m* ∈ [m_floor, m_KKH26]`,
ceiling `m_KKH26 = Θ(n/log n)` PROVEN (`kkh26_mcaDeltaStar_le_of_TZ`). `m* = m_KKH26 ⟺` the wall
(`_EnergyRatioMonotoneReduction`). Pinning δ* ≡ computing the integer `m*`.

**(2) A production counting interface exists — the line-list stack** (on main, verified):
`LineListReduction` → zero-agreement strata → coordinate fibers → MDS uniqueness `#S ≥ k` ⟹
fiber ≤ 1 → singleton-defect → support-ratio covers — discharges everything EXCEPT low-profile
(`t < k`) fibers on large-zero-safe lines. All raw envelopes are formally REFUTED
(`LineListArithmeticObstruction` etc.); exact failure scanners exist at every layer. ✅ The
prize-facing weld (`LineListMCAWeld.mcaDeltaStar_ge_of_farLineListBudgeted`: δ* floor ⟸ far-line
budget `Λ ≤ L ≲ ρ·n`) is on main (`LineListMCAWeld.lean`, re-landed axiom-clean). The open
production obligations are now the
low-profile fiber theorem; the mixed-profile top-fit arithmetic (`*MixedChooseProfileTopSumsFit`);
the second-witness/multiplicity floor (`NoUniqueBadScalarWitness`); `CandidateListExactSuccessor`
(or its adjacent-rung counterexample).

**(3) The windowed-guard discipline.** Guard-free `SumsetExtremal` is FALSE
(`not_sumsetExtremal`, below-window countermodel). Any dominance/extremality hypothesis must carry
the prize-window guard (`SumsetExtremalityGuard.lean`). The **windowed SumsetExtremal** — a
≥2-Fourier-component spread cannot beat every monomial component *in the window* — is the guarded
crux; sockets `mcaDeltaStar_pin_of_finsetGuardCover(_orOutside)` await a real catalogue.

**(4) The off-BGK floor is RESOLVED — as obstruction-removal.** floor-bad(16) = {17},
floor-bad(32) = {97} (exact scanners); Thorner–Zaman sub-quartic 12/5 CONFIRMED unconditional for
dyadic moduli ⟹ every prize prime is floor-good unconditionally. But δ*-pin ⟹ floor-good, NEVER
conversely (ε_mca is a sup over all stacks; the floor bounds one direction) — necessary, not
sufficient. Still open: the uniform-in-μ characterization; the floor→δ* arrow.

**(5) The fixed-depth side is closed at every scale.** The canonical width-four/resultant lane
(`canonicalRatioPoly n = (X⁴+1)^n − (X²+1)^n`) is discharged concretely at n = 16 … 32768
(`CanonicalWidthFourConcreteTZ*`), exact bad-prime sets pinned (n=16: {17}; n=32 primitive:
{97,641,673,1153} — NOTE width-four-bad ≠ floor-bad, `ne_singleton97`). No finite-r cutoff: every
fixed-r face closes off-BGK. The residual is 100% the joint limit `r ≈ ln q`, `n = 2^30`.

**(6) More doors closed as theorems** (see dossier §4/§8): the door-(iv) gap-combinatorial face
(gap values/curvature/DFT-rank/runs all dilation-invariant or wrong-direction); graph-relation
reformulations (tautological); six non-period angles; three √-cancellation-breaking templates;
five beat-SOTA mechanisms; FHK log-correlated EVT (killed by EXPERIMENT — the {log|η_b|} field is
independent-Gaussian, not log-correlated); effective-Katz (vacuous in thin regime); Toda/isospectral
(gauge); 2026 literature D0–D5 gates (`_D*Gate.lean`). Moment-exponent quantification:
`θ(r,β) = (β+r−1)/(2r) > 1/2` always — the moment route IS the route to Paley; the arithmetic is
now re-landed in `MomentExponentThreshold.lean`.

**(7) What survives (ranked, dossier §6):** ① windowed SumsetExtremal; ② the line-list low-profile
obligations (2); ③ Hankel-positivity/Lax-pair spectral-shift on the Jacobi turnover `k*` (the one
non-magnitude seam); ④ uniform-in-μ floor-bad; ⑤ the announced-never-run di Benedetto effective-1/2
push at β=4; probes not run: anti-resonance (2605.15434), non-backtracking Ihara–Bass (2606.27075),
D2 Rogers–Siegel decision. Tool-shape principle: any survivor must be an L∞/sup-control method fed
by computable second-order data (Talagrand γ₂ is the canonical candidate shape).

**(8) The sharpest localization — the independence form.** The prize = CERTIFYING the measured
independent-Gaussian behaviour of the period field: sub-Gaussian tail `P(|η_b| > tn) ≤ exp(−ct²n)`
to depth `r ≈ log p`, equivalently `E_r⁺(μ_n) − n^{2r}/p ≤ C^r·r!·n^r` at logarithmic depth.
Difficulty is certification, not distribution shape.

⇒ **The `▼ YOUR CONJECTURE HERE ▼` slot's current best targets (post rounds 1–2, 2026-07-01;
see dossier §14/§15):** (a) the low-profile fiber bound `D(t)`, `t < k`, feeding
`mcaDeltaStar_ge_of_farLineListBudgeted` (the PRIMARY surface; `_LowProfileFiberBound` +
`_R2B_LargeZeroWitnessSplit` narrow it); (b) the **bounded spread-excess law at C = 3**
(`_SpreadExcessLaw.SpreadExcessLaw` — the replacement for windowed SumsetExtremal, which is
REFUTED at n=16: spread beats every monomial in-window, DISPROOF `466-r1-windowed-extremal-…`;
C=2 is also dead); (c) the floor successor theorem `CandidateListExactSuccessor` (floor-bad(64)
is compute-undecidable — theorem or nothing); (d) `WorstCaseIncidenceBounded` at the window
radius via any genuinely L∞ method fed by non-second-order data (the §1.5 framing below remains
valid; note round 2 KILLED the positivity/Christoffel upgrade — any such proposal must first
beat the lone-spike countermodel, DISPROOF `466-r2-cmk-lonespike-refuted`). All are faces of the
ONE open inequality `M(μ_n) ≤ C·√(n·log(p/n))` — dossier v3 §2 forms (A)–(D).

────────────────────────────────────────────────────────────────────────────────
## §R.  HISTORICAL RESEARCH SYNTHESIS 2026-06-13 — superseded target claim
##      every published route provably misses the prize regime (plain RS, s=1).
##      (full map: `docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md`)
────────────────────────────────────────────────────────────────────────────────
⚠️ The paragraph below is retained as campaign history, but its conclusion that the two exact
thresholds are identical is too strong: the displayed bridges have radius/code/constant losses.
It is not part of the closure contract in §1/§4.

**THE HISTORICAL REDUCTION CLAIM.** The earlier campaign treated the grand MCA challenge and the
grand list-decoding challenge as sharing the *same* `δ*`:
  · MCA ⟹ list  (ABF26 Thm 5.2 [BCHKS25 1.9] / Thm 5.3 [CS25 2]): `ε_mca ≤ ε*` ⟹ `|Λ| ≲ ε*·|F|`.
  · list ⟹ MCA  (ABF26 Thm 5.1 [GCXK25 3]): `|Λ(C,δ)| ≤ L` ⟹ `ε_mca(C, 1−√(1−δ+η)) ≤ L²δn/(η|F|)`.
With `ε*=2⁻¹²⁸`, `q≈n·2¹²⁸`, so `ε*·|F| ≈ n`, hence the prize core is exactly:

  **`δ*_prize = sup{ δ : |Λ(RS[F, μ_n, k], δ)| ≤ ε*·|F| ≈ n }`**  — the radius where the
  *worst-case list size of explicit smooth-domain RS* crosses `~n`. Pin THIS and both fall.

**THE THREE PUBLISHED ROUTES AND THEIR FATAL GAPS (exhaustive — none reaches plain RS, s=1):**
  1. **List⇒CA** (GCXK25 Thm 3): has a **√-loss in the radius** (`δ → 1−√(1−δ)`) that ABF26 proves
     is FALSE to remove in general (Thm 5.4 [BGKS20] counterexample). OUT unless smooth structure.
  2. **Subspace-design / line-stitching** (JLR26 = arXiv 2601.10047 / GG25 = 2025/2054): proves
     `ε_mca ≤ (C₁/q)(n/η+1/η³)` up to capacity δ=1−R−η, BUT is **FRS-only** — needs folding
     `m=Ω(η⁻²)`; plain RS (`s=1`) has `τ(r)=R+O(r)`, useless. Its lemma chain is ~70% in-tree:
     Claim 5.8 = `subspaceDesign_list_dim_bound`, Lemma 5.4 = `curve_agreement_card_le` (both
     landed), Def 4.3 = `IsSubspaceDesign`, Lemma 5.5 = `exists_separating_*` (fleet); only line
     stitching (5.7) + peeling (5.10) remain — relevant for the FRS arm, NOT the prize.
  3. **Syndrome-space + witness reduction** (Yuan–Zhu arXiv 2605.07595, May 2026): `ρ<1−R−ε`
     up to capacity WITHOUT list decoding — but **random linear codes only** (random parity-check
     model); it works precisely because the random syndrome avoids `μ_n`'s additive structure.

**THE SINGLE NAMED OPEN TARGET (the prize core, no open-ended search).** Transferring route 3 to
explicit `μ_n` is the **line–ball incidence in syndrome space** (face iv, `epsMCA_ge_far_incidence`):
the bad-scalar count is `max over far-direction lines |{γ : syn(u₀)+γ·syn(u₁) ∈ B_{⌊δn⌋}}|`, where
`B_w` is the weight-`w` syndrome ball = high-frequency DFT image of weight-`≤w` errors over `μ_n`.
Pinning `δ*` is bounding this incidence; the controlling quantity is the **additive-energy / Sidon
structure of `μ_n`** (the in-tree energy + this-session antipodal work). A winning closed conjecture
states `max-incidence(δ) ≤ f(n,ρ,δ)` in closed form, with `f` crossing `n` at the claimed `δ*`, and
respecting the near-capacity lower bound `ε_mca ≥ n^{Ω(1)}/|F|` (ABF26 Table 1). This is the
`▼ YOUR CONJECTURE HERE ▼` slot's precise target — a syndrome line–ball incidence bound for `μ_n`.

## §R.2  SESSION 2026-06-13b — energy⟹sup-norm reduction, the EXACT constant √2, and the proven
##        BGK partial bound (connecting the Shaw operator of §3 to known number theory).

The §3 Shaw operator's even moments ARE the `r`-fold additive energies `E_r(μ_n)` of the syndrome
incidence, so the prize bound is a bound on `E_r(μ_n)`. Three results this session:

  **(1) Reduction, LANDED axiom-clean** (`SubgroupGaussSumEnergyReduction.eta_pow_le_energyR`):
  `max_{b≠0}‖η_b‖^{2r} ≤ q·E_r(μ_n) − |μ_n|^{2r}`, via the in-tree moment ladder
  `∑_b‖η_b‖^{2r}=q·E_r` (pure orthogonality, no Weil). Converts ANY `E_r` bound into a Shaw/η bound.

  **(2) The EXACT prize constant √2** (char-0 Wick). For `n=2^μ`, `{ζ^0..ζ^{n/2−1}}` is a ℚ-basis of
  `ℚ(ζ_n)`, so the char-0 `r`-fold energy is a pure matching count `E_r^ℂ(μ_n)=(2r−1)!!·n^r`
  (μ_n ≈ complex Gaussian; r=1→n, r=2→3n²−3n in-tree-exact). At the critical `r≈ln q` this yields
  `max‖η_b‖ ≤ √(2·n·ln q)`. The controlled quantity is the EXCESS over the equidistribution baseline,
  `Excess(r):=E_r−n^{2r}/q=(1/q)∑_{b≠0}‖η_b‖^{2r}`; the prize ⟺ `Excess(ln q) ≤ (2r−1)!!·n^r`. The
  `r=2` case is PROVEN in-tree (pinned `E_2=3n²−3n`, `n⁴/q≈2⁻⁹⁶` negligible) but gives only a trivial
  sup bound — the √2 needs `r≈ln q`, the open regime.

  **(3) Proven PARTIAL bound (BGK).** The prize needs only ENOUGH cancellation, not the sharp √2:
  the sharp sup-norm needs equidistribution to relative precision `e^{−Θ(n)}` (absurd) and was an
  over-strong side-target. Throughout the ENTIRE prize regime `n=2⁴⁰ ≥ p^{0.156}` (fixed `δ` since
  `p≤2²⁵⁶`), Bourgain–Glibichuk–Konyagin gives a PROVEN power-saving `max‖η_b‖ ≤ n^{1−ε}`,
  `ε=ε(0.156)>0`. Via the in-tree `SubgroupGaussSumMomentBound.rEnergy_le` (with `M=n^{2−2ε}`) this is
  a proven `Excess(r) ≤ n^{2r−1−2ε(r−1)}` — strictly past Johnson, but `≫ Wick` for small `ε`, so it
  does NOT reach the window edge `1−ρ−Θ(1/log n)`.

So the prize is bracketed by two in-tree-expressible bounds on the SAME Shaw/`E_r` object: BGK
(proven, past Johnson) below, Wick-√2 (conjectured, window edge) above. The open core is exactly the
sharp per-frequency `Z/n` block estimate of `FarLineIncidenceEquivariance` (§3) — sharper than BGK,
= `Excess(ln q) ≤ (2r−1)!!n^r`. Full derivation + numerics:
`docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md` §§13–14b.

## §R.3  SESSION 2026-06-13c — the IRREFUTABLE closed bound (fabricate-then-refute).

Filling the §R.2 bracket [BGK proven, below | sharp open, above] with a refutation-tested closed
form for the §3 Shaw-operator magnitude `S(n,p) = max_{b≠0}|∑_{x∈μ_n} e_p(bx)|`:

  **`S(n,p) ≤ 2·√(n · ln p)`   (uniform);   `S(n,p) = (1+o(1))·√(n ln p)`  (sharp law).**

Refutation ladder (FFT-exact, 2197 (n,p) pairs, n≤512, p≤250k, adversarial Fermat/2-power-heavy
primes + depth sweep): `C=1` REFUTED, `C=√2` (the char-0 Wick value of §R.2/§14) REFUTED,
`C=√e=1.6487` survives (sup 1.6378), `C=2` IRREFUTABLE (0/1690 violations). The char-p anomaly that
§R.2 left open is now valued: a BOUNDED Gumbel tail `max|η_b|²≈n(ln p+G)`, `G` peaking (≈19) at the
Fermat prime 65537 and NOT growing with `n` or 2-adic depth — so the constant is universal, between
`√2` (char-0) and `√e` (with anomalies). Mechanism: `η_b=(1/m)∑_{ψ∈μ_n^⊥,ψ≠1}ψ̄(b)τ(ψ)`,
`|τ(ψ)|=√p`, extreme value of `p` Gauss-phase terms.

**Closes both challenges (modulo proof of the bound).** Bias `θ=S/n ≤ 2√(ln p/n) → 0`; at the prize
point `n=2⁴⁰, p≤2²⁵⁶`, `θ ≤ 2^{-15}`. A `θ`-pseudorandom smooth RS code keeps list size `≤2^128`
through the window, so `δ* = 1−ρ−Θ(1/log n)` (ABF26 Thm 4.16 met). Via §3
`incidence_pinned_of_shawBound`, the closed bound `S ≤ 2√(n ln p)` IS the resolution: set the §3
`MCAShawConjecture` budget `B := 2√(n ln p)`. The remaining (tractable) proof target is a Gumbel-tail
bound on `∑_ψ ψ̄(b)τ(ψ)` (Deligne equidistribution + union bound over `b`) — replacing the FALSE
sharp-`√2` route. Refutation-tested CONJECTURE (n≤512 verified; n=2⁴⁰ is inductive extrapolation),
not a proof. Full record: `docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md` §15.

## §R.4  SYNTHESIS 2026-06-13d — δ* is the CAPACITY term (Incidence-Genericity Dichotomy + refutation).

⛔ **CORRECTED (KB §37): this section's "δ* = capacity term" claim is WRONG.** Kambiré
(arXiv:2604.09724, native to μ_{2^t}) PROVES δ* is the WINDOW EDGE `1−ρ−2/(K·log₂n)`=`1−ρ−Θ(1/log n)`,
NOT the capacity term. The in-tree historical candidate
`PrizeEntropyDeltaStar.prizeDeltaStar(ρ, q·ε*)` was proposed as that window edge, but its generic
finite equality and the obvious rate-and-log-unit repair are now refuted in
`PrizeEntropyPinRefuted`; whether a corrected asymptotic law has the same leading scale remains open.
Genericity ALSO INVERTED: bad count = DISTINCT r-fold sumset `|H^{(+r)}|`, so LARGE sumset FUELS the
disproof. Treat §R.4 as superseded by KB §37.

CORRECTION to the §R.3/window-edge reading, synthesizing the issue thread's Incidence-Genericity
Dichotomy with the fabricate-then-refute certificate.

  **`δ*(dyadic μ_{2^μ}, ε*) = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)`**  (the list-decoding CAPACITY radius;
  ≈ `1 − ρ − h(1−ρ)/log₂q` to first order).

WHY (not the window edge): the KK25/BCHKS bad construction `δ*≤1−ρ−Θ(1/log n)` (Thm 4.16) is the
worst case over ALL domains — its construction is F₂-linear/special-sumset. The GENERIC dyadic
prime-field `μ_n` BEATS it and reaches the capacity term, because it is incidence-generic:
  · `B(μ_n) = max_{b≠0}|∑_{x∈μ_n}e_p(bx)| ≤ 2√(n ln p)` (refutation, §R.3) and
    `B(μ_n)/B_random ≈ 0.48–0.64 ≤ 1` — μ_n is at most as additively concentrated as a RANDOM
    n-subset (whose worst sum is also `√(n ln p)`);
  · `E(μ_n) = 3n²−3n` exactly (in-tree `RootsOfUnityEnergyExact`) = the CLEAN generic value
    (`E⁺/3n(n−1)=1`), the antipodal `−1∈μ_n` accounted for, NOT an inflation.

The historical draft therefore claimed a shared capacity threshold.  That claim is superseded by
§1: only the parameter-checked one-way implications are valid.  The associated open core was:
deployed-regime
genericity `E(μ_n)=O(n²) ⟺ B(μ_n)=O(√(n·polylog))` (the 25-yr wall) — PROVEN for `p>2^n`
(cyclotomic resultant, in-tree), refutation-certified for deployed `p≈2^168≪2^{2^40}`, BGK-floored
`B≤n^{1−ε}`. The two remaining open links: the dichotomy's forward direction (generic ⟹ capacity δ*)
and the asymptotic genericity proof. Issue #389 comment 4699815321; KB §19.
-/

set_option linter.unusedSectionVars false
-- the prize objects (mcaDeltaStar, choose-budget) are heavy to elaborate; give a solver room:
set_option maxHeartbeats 1000000

namespace ProximityGap.Workbench

open scoped NNReal ENNReal
open ProximityGap ProximityGap.GrandChallenges
open ArkLib.ProximityGap.KKH26  -- evalCode: the explicit smooth RS code object used by the §2.4 pins
-- Substrate namespaces — every §2 lemma is now directly accessible by its short name:
open ProximityGap.MCAThresholdLedger      -- mcaDeltaStar, le_mcaDeltaStar_of_good, mcaDeltaStar_le_of_bad
open ProximityGap.FarCosetExplosion       -- epsMCA_ge_far_incidence (the law's engine)
open ProximityGap.SpikeFloor              -- mcaDeltaStar_rs_eq_granularity (the ladder)
open ArkLib.ProximityGap.KKH26CeilingMarch          -- interiorCeiling_march, march_badScalars_card_mul_le
open ArkLib.ProximityGap.OwnershipCensus            -- sharpened_*, deviation_ownership_card (the CEILING)
open ArkLib.ProximityGap.AdditiveEnergyRepBound     -- GVRepBound, additiveEnergy_cube_le_of_gvRepBound
open ProximityGap.BoundarySupExactness    -- rs_boundary_epsMCA_eq (the boundary n/q law)

/-! ## SMOKE TEST — every §2 substrate lemma resolves here (the "good experience" check).
If any `#check` below errors, the workbench is missing an import/open and must be fixed before
a solver relies on it. -/

-- §1 targets
#check @mcaConjecture
#check @GrandChallenges.mcaPrize
#check @GrandChallenges.mcaConjectureBound
#check @GrandChallenges.nonempty_mcaLowerWitness_of_mcaConjecture   -- conjecture ⟹ prize witness
-- §2 the law
#check @mcaDeltaStar
#check @le_mcaDeltaStar_of_good
#check @mcaDeltaStar_le_of_bad
#check @epsMCA_ge_far_incidence
-- §2 capacity-for-constant-DIM (the template, not the prize)
#check @interiorCeiling_march
#check @march_badScalars_card_mul_le
-- §2 granularity + boundary exact laws
#check @mcaDeltaStar_rs_eq_granularity
#check @rs_boundary_epsMCA_eq
-- §2 ownership bracket (W1: the proven-exhausted surface)
#check @sharpened_badScalars_card_mul_choose_le
#check @deviation_ownership_card
-- §2 energy / sub-Johnson list chain (W2/W3: the √-loss-capped route)
#check @additiveEnergy_cube_le_of_gvRepBound
-- §2 paper-bound witness bridges
#check @MCALowerWitness.ofJohnsonBCHKS25
#check @MCAUpperWitness.ofRSBreakdownCS25
-- §2.5 live LD⇒MCA routes (the frontier)
#check @CurveDecodable
#check @MarkedCurveDecodable
#check @exists_determining_tuple

/-! ## Sanity handles — the target objects are in scope and usable.

These trivial `example`s confirm the prize objects elaborate here, so a solver can write the
real statement directly against them. (They are not the prize; they certify the workbench.) -/

/-- The uniform MCA conjecture is the named target `Prop`. -/
example : Prop := mcaConjecture

/-- The MCA prize (all four rates, `ε* = 2^-128`) is in scope for any smooth domain. -/
example {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (domain : ι ↪ F) : Prop :=
  GrandChallenges.mcaPrize domain

/-- The operational threshold `mcaDeltaStar` is in scope (the law's δ*). -/
noncomputable example {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (C : Set (Fin n → F)) (εstar : ℝ≥0∞) : ℝ≥0 :=
  MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C εstar

/-! ════════════════════════════════════════════════════════════════════════════
    ║                     ▼▼▼   YOUR CONJECTURE HERE   ▼▼▼                       ║
    ════════════════════════════════════════════════════════════════════════════

    State the closed-form `δ*(ρ, ε*, n)` (or the `ε_mca` bound), prove it in the
    prize regime, beat the per-witness wall (W1), and wire it to an operational
    `mcaDeltaStar` equality (T1) / `mcaPrizeLatticeResolved` (T2), with the stronger
    `mcaConjecture` only if its uniform quantifiers are proved (T3), then the LD bridge (T4).
    Keep it CLOSED — no
    residual, no incomputable lemma. Prove a concrete prize-shaped instance first,
    then the general statement.

    Example skeletons (uncomment, replace `sorry` — but the prize needs NO sorry):

      -- def prizeDeltaStar (ρ : ℝ≥0) (n : ℕ) : ℝ≥0 := …            -- the closed form
      -- theorem prize_deltaStar : mcaDeltaStar C epsStar = prizeDeltaStar ρ n := … -- T1
      -- theorem prize_lattice : mcaPrizeLatticeResolved domain τ := …              -- T2
      -- theorem prize_mcaConjecture : mcaConjecture := …                            -- T3

    ════════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════════
    ║   §3   THE SHAW OPERATOR — the closed Proximity-Prize conjecture           ║
    ════════════════════════════════════════════════════════════════════════════

    UNIFICATION (proven, axiom-clean, `ProximityGap.ShawOperator`).  Every reduction of the prize
    δ* — the residual `(R) = worst − average`, the higher-order-MDS failure-correction `κ_d`, the
    off-diagonal spectral error of the line–ball incidence operator, the worst-case incomplete
    character sum `max|η_b|`, the higher additive energies `E_r` — is **one** quantity, the

        **Shaw operator**   `𝒮(S; s₀, s₁) = Σ_{ψ≠0, ψ⊥s₁} Σ_{s∈S} ψ(s₀−s)`

    (`ShawOperator.shawError`), the off-trivial spectral error of the line–ball incidence.

    SOLVE FOR δ* (proven, axiom-clean).  `ShawOperator.incidence_eq_average_add_shaw`:

        `#{γ : s₀+γ·s₁ ∈ S} · |V|  =  |F| · (|S| + 𝒮)`     — incidence = average + Shaw, EXACTLY.

    Since `δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger.mcaDeltaStar`), δ*
    is a *closed function* of the worst-case Shaw operator.  `incidence_pinned_of_shawBound` turns a
    Shaw budget into two-sided control of the incidence with **no open residual**.

    THE CLOSED CONJECTURE (the single open input).  `ShawOperator.MCAShawConjecture S B`:

        `∀ s₀ s₁,  ‖𝒮(S; s₀, s₁)‖ ≤ B`.

    With the prize budget `B = q·ε*·|V|/|F| − |S|` on the explicit smooth-domain δ-ball this is
    EXACTLY δ* reaching the prize window.  It is irreducible: NOT Johnson (the average term is
    strictly capacity-side), NOT a Weil/Parseval bound (W4-weak on `s₁^⊥` for `n ≪ √q`).  This is a
    closed bound on a single named operator — no residual, no incomputable lemma.  Proving it (the
    cyclic block-diagonal `Z/n` per-frequency estimate of `FarLineIncidenceEquivariance`) is the
    whole prize. -/


/-! ### A concrete, unconditionally-proven witness of the δ* law

`MCAShawConjecture` above is the open input *in the prize regime* (`n = 2³²`, cryptographic
`ε*`). In the **provable supply regime** `r² ≤ 2^μ + 1` the *same* `δ* = 1 − r/2^μ` law closes
with **no open residual** — a genuine *beyond-Johnson* exact pin. We record the smallest clean
instance as a falsifiable, fully-proven anchor: it is the honest closed analogue of the
conjecture (same law, same beyond-Johnson placement), differing only in needing *explicit* prime
supply (provable here; asymptotically the open core in the `n = 2³²` prize regime). -/

/-- `4129` is prime (instance for `Field (ZMod 4129)`). -/
instance : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- `g = 2386` has order exactly `8 = 2³` in `F_4129ˣ`, so `⟨g⟩ = μ_8`
(`g^4 = −1 ≠ 1`, `g^8 = 1`, by `orderOf_eq_prime_pow`). -/
theorem orderOf_g8_witness : orderOf (2386 : ZMod 4129) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ¬ (2386 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
  have h8 : (2386 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
  simpa using orderOf_eq_prime_pow (x := (2386 : ZMod 4129)) h4 h8

/-- **Closed witness of the δ* law (beyond Johnson, below capacity).**  For the explicit
smooth-domain RS code `evalCode 2386 8 1` on `μ_8 = ⟨2386⟩ ⊆ F_4129ˣ` at
`ε* = ⌊C(8,3)/3⌋/4129 = 18/4129`, the mutual-correlated-agreement threshold is **exactly**

> `δ*(C, ε*) = 1 − 3/2³ = 5/8`,

strictly above Johnson `1 − √ρ = 1/2` (`ρ = 1/4`) and strictly below capacity `1 − ρ = 3/4`.
Proven unconditionally in the `r² ≤ 2^μ + 1` (`9 ≤ 9`) supply regime, where `4129 > 8⁴ = 4096`
carries the `≡ 1 (mod 8)` prime supply the [KKH26] counting needs.  No residual, no `sorry` — the
honest closed analogue of `MCAShawConjecture` for a concrete falsifiable instance. -/
theorem deltaStar_pin_mu8_F4129_witness :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (2386 : ZMod 4129) 8 (3 - 2))
        ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 5 / 8 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hpin : mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
      (evalCode (2386 : ZMod 4129) 8 (3 - 2))
      ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 1 - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) :=
    kkh26_march_deltaStar_pin_canonical
      (p := 4129) (g := (2386 : ZMod 4129)) (μ := 3) (r := 3) (n := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) orderOf_g8_witness (by norm_num)
  rw [hpin]; refine tsub_eq_of_eq_add ?_; norm_num
/-! ════════════════════════════════════════════════════════════════════════════
    ║   §P.  THE PRODUCTION INCIDENCE CORE IS EXACTLY PROJECTIVE                  ║
    ════════════════════════════════════════════════════════════════════════════

  `WorstCaseIncidenceBounded` counts one affine chart of each two-row pencil.  For every
  `E < |F|`, `worstCaseIncidenceBounded_iff_projective` proves this is EXACTLY equivalent to
  bounding all `|F|+1` projective bad slots.  There is no `+1` loss: a good affine slot can be
  moved to infinity, and `badSlotCount_row_mix` proves the census is invariant under every
  invertible row mix.  The strict budget is sharp; the `F_2`, three-coordinate boundary theorem
  refutes the equivalence at `E = |F|`.

  `epsMCA_le_iff_projective` identifies the operational error budget with this projective census,
  and `mcaDeltaStar_eq_of_projective_jump` converts its first failure into an exact threshold.
  Codeword translation shows that the census depends only on the two quotient classes.  For every
  budget `E >= 1`, dependent quotient rows contribute at most one slot, so only genuine rank-two
  pencils remain.  `mcaEventProj_iff_quotientPencilSupport` states each bad slot exactly as a class
  lying in a witness support subspace which does not contain the whole quotient pencil.  The open
  math is the resulting worst-case incidence estimate.  `ProjectiveProperQuotientBall` retains this
  local properness clause, gives an unconditional exact projective incidence for every pencil, and
  supplies its affine-plus-infinity decomposition and exact affine Fourier expansion.

  `badSlotCount_le_lowCosetWeightCount` gives the unconditional metric envelope, and becomes an
  equality under global `not jointProximity`.  `quotientSyndromeBall` is the finite union of all
  admissible support subspaces.  `ProjectiveMetricUnification` proves that this is exactly the
  coset-weight sublevel set, while `ProjectiveQuotientBall` identifies basis-free `PencilJointFar`
  with `not jointProximity`.  The resulting projective line--ball incidence splits into its affine chart
  and infinity point, while the affine chart feeds into
  `LineIncidenceSpectral.lineIncidence_spectral`. -/

/-! The tempting field-uniform ceiling of `n` proper points on every half-radius MDS syndrome
  line is false.  R383 has nine proper affine points on the dyadic `[8,4]` Reed--Solomon frame
  over `F_17`.  The `[9,2]` countermodel over `F_11` still has ten proper projective points with
  `e+k+1<n` and `k<=n/4`.  Rich-point pruning now closes the exact predecessor at rate at most
  `1/8` at the intrinsic cutoff `h>=1699`.  At saturated rate `1/4`, the residual core band is
  `k+2` through `3k-4`; triples in high-core clusters are forced toward determinant collapse,
  while intermediate cores force a new secant petal of size at least `floor(k/3)+2`.  One high
  core forces a petal of size at least `floor(k/2)+3`, and sharp Johnson closes the equal-slope
  branch covered by half-core lines.  The live high-core residuals are the automatic reduced-
  budget failure, uncovered scalars, and the unequal-slope forbidden-capacity witness; global
  companion selection remains open.

  **2026-07-10 correction:** the universal rate-quarter half-predecessor `n`-scalar law is
  REFUTED.  `HalfPredecessorRateQuarterSmoothCounterexampleF97` kernel-checks 36 bad scalars
  on the smooth `RS[32,8]` domain over `F_97`, exceeding `n=32`.  At the first prize-shaped
  prime, the exact executable fibre lift and maximal private thickening give `n+2` bad scalars
  at radius `23/48-2/(3n)`.  `P1RateQuarterScaleFinalConsumer` kernel-checks the literal count,
  strict `2^-128` mass inequality, and resulting operational `mcaDeltaStar` upper bound.
  The full unique-decoding connector supplies the unconditional lower bound `3/8`.
  Threshold-level Reed--Solomon reindexing transports the entire fibre result to the literal
  `evalCode g N (k-1)` surface, giving `3/8 <= mcaDeltaStar <= 23/48-2/(3n)`.
  The saturated common-factor stack and its exact `n+2` bad-label count strengthen the literal
  upper endpoint unconditionally to `43/96+1/(3n) < 1/2`.

  Exact equality at that endpoint is proved only if the immediately preceding lattice radius is
  good.  `PredecessorStructuredFloorResidual canonicalDomain` and the guarded
  `CanonicalLargeBadFourPencilExtraction` are two named interfaces for this missing step; they are
  each equivalent to the same uniform predecessor bad-count target, and neither is discharged.
  The four-pencil payload now needs only four favorable two-fresh source pencils, with no saturated
  core-size lower bound, but its global large-family guard does not weaken the target logically.
  The source-six long-stratum mirror below is local `k=4` geometry, not a discharge of either
  predecessor interface.

  Projective equivariance now shrinks every hypothetical over-budget predecessor stack further:
  its quotient rows are independent and every nonzero projective row combination is near the code.
  In every invertible row chart, translating the mixed direction by its nearby codeword now gives
  an exact dichotomy: either the remaining support exceeds `55,920,000`, or zero-direction
  unsafety supplies a threshold-size joint RS agreement which transports back to the original
  rows.  Indeed the zero-safe sub-branch has exact affine weight `1,013,444,618`, and remains
  below `n` after paying for the omitted projective slot.  The raw interleaved-collapse route
  cannot finish the job: its prize arithmetic requires a uniform list cap `L <= 1`, and that
  premise is formally refuted at the zero stack.  Exact integer-cell optimization of the improved
  BCHKS25 Guruswami--Sudan/Hensel bound still gives more than `10,719*n` exceptions, so it also
  cannot fire from the predecessor's `n+1` trigger.

  The threshold joint-witness branch is now quantified separately.  Ordinary exact-diagonal
  Johnson bounds its interleaved RS list by five, and every MCA event must expose a coordinate
  outside any fixed joint-agreement set.  An over-budget family of selected escape coordinates
  therefore has three scalars sharing one fresh coordinate.  This is a sharp pigeonhole output:
  two complement-size fibers fit below `n`, but three exceed it, while a concrete arbitrary
  `F_3` set code proves that the bare MCA clauses do not make the escape charge injective.  A
  kernel-checked `RS[8,2]` example over `F_11` goes further: three distinct bad scalars can share
  a genuinely fresh coordinate even at rate `1/4`.  Thus a generic-RS triple exclusion is false;
  and the proposed P1-only exclusion is false as well.  A root-product construction on every
  injective literal P1 domain gives a threshold joint set and `480,946,859` distinct bad scalars
  through one fixed fresh coordinate.  In particular `SharedFreshTripleFree` is refuted; its
  conditional bad-family consumer remains logically valid but cannot close this branch.
  Pairwise witnesses
  do force a joint pencil on their intersection, witness sets are incomparable, a `K`-point
  overlap with the known joint set absorbs the fresh coordinate, and a collinear triple forces
  joint agreement on `352,321,537 >= K` points.  None contradicts the event threshold.  The
  correct collinear statement is instead global: whenever all selected decoded witnesses lie on
  one fixed codeword pencil, nonjointness chooses a mismatch coordinate and the affine agreement
  equation determines the scalar uniquely there.  This injective mismatch charge bounds the
  whole collinear family by `n`; only genuinely non-collinear/global configurations can remain
  over budget.

  Abstract pair/core incidence constraints are also insufficient.  The missing simultaneous
  constraint is now a genuine support-dependent divided-difference linear map: supported decoded
  families lie in its kernel and global polynomial pencils form the evident kernel.  Unrestricted
  two-anchor rigidity is formally refuted by the finite-domain vanishing polynomial.  At any
  coordinate supplied with two distinctly labelled anchors, kernel membership is exactly local
  affine-stack consistency, so no stronger purely local-row constraint remains.  Two degree-`<K`
  candidate pencils do propagate when, at each of `K` injective points, they agree at a supplied
  pair of distinct labels; that pair may vary by coordinate.  This conditional consumer does not
  extract the overlaps, and secant-core cardinalities alone cannot force them at P1: the
  corresponding Plotkin denominator is nonpositive and even two disjoint `K`-cores fit.  Because
  a fixed maximal minor can vanish while the full operator stays injective, the adaptive target
  is a maximal-minor-family ideal certificate: expressing a power of the symbolic Vandermonde
  through selected maximal minors forces one of them to survive every injective label
  specialization.  Coefficient reconstruction, the exact gauged concrete matrix, and both the
  concrete-injectivity and symbolic-certificate consumers now bridge this criterion all the way
  to degree-restricted rigidity.  What remains is the actual P1 symbolic matrix specialization
  and its Vandermonde/maximal-minor Bezout certificate.  After restricting every component to
  decoded degree `<K`, the corrected rigidity hypothesis again forces one global pencil and joint
  RS agreement.  That degree-restricted rank statement remains open.  Therefore the exact
  rate-quarter delta-star remains open. -/

#check @ProximityGap.MCAProjectiveEquivariance.rowMixSlotEquiv
#check @ProximityGap.MCAProjectiveEquivariance.badSlotCount_row_mix
#check @ProximityGap.MCAProjectiveEquivariance.badSlotCount_eq_of_quotient_mk_eq
#check @ProximityGap.ProjectiveWorstCaseIncidence.worstCaseIncidenceBounded_iff_projective
#check @ProximityGap.ProjectiveWorstCaseIncidence.epsMCA_le_iff_projective
#check @ProximityGap.ProjectiveWorstCaseIncidence.mcaDeltaStar_eq_of_projective_jump
#check @ProximityGap.ProjectiveWorstCaseIncidence.projectiveWorstCaseIncidenceBounded_iff_rankTwo
#check @ProximityGap.ProjectiveRankTwoAPI.rowsIndependentModCode_iff_finrank_quotientPencil_eq_two
#check @ProximityGap.ProjectiveQuotientSupport.mcaEventProj_iff_quotientPencilSupport
#check @ProximityGap.ProjectiveCosetWeight.badSlotCount_le_lowCosetWeightCount
#check @ProximityGap.ProjectiveCosetWeight.badSlotCount_eq_lowCosetWeightCount_of_not_jointProximity
#check @ProximityGap.ProjectiveCosetWeight.card_slotQuotientPoints_of_rowsIndependent
#check @ProximityGap.ProjectiveQuotientBall.badSlotCount_le_projectiveBallIncidence
#check @ProximityGap.ProjectiveQuotientBall.badSlotCount_eq_projectiveBallIncidence_of_pencilJointFar
#check @ProximityGap.ProjectiveQuotientBall.affineBallIncidence_spectral
#check @ProximityGap.ProjectiveMetricUnification.mem_quotientSyndromeBall_iff_cosetRelWeight_le
#check @ProximityGap.ProjectiveMetricUnification.projectiveBallIncidence_eq_lowCosetWeightCount
#check @ProximityGap.ProjectiveQuotientBall.pencilJointFar_quotientPencil_iff_not_jointProximity
#check @ProximityGap.ProjectiveQuotientBall.badSlotCount_eq_projectiveBallIncidence_of_not_jointProximity
#check @ProximityGap.ProjectiveQuotientBall.affineBallIncidence_spectral
#check @ProximityGap.ProjectiveMetricUnification.mem_quotientSyndromeBall_iff_cosetRelWeight_le
#check @ProximityGap.ProjectiveMetricUnification.projectiveBallIncidence_eq_lowCosetWeightCount
#check @ProximityGap.ProjectiveProperQuotientBall.properQuotientBall_subset_quotientSyndromeBall
#check @ProximityGap.ProjectiveProperQuotientBall.properQuotientBall_eq_quotientSyndromeBall_of_pencilJointFar
#check @ProximityGap.ProjectiveProperQuotientBall.badSlotCount_eq_properProjectiveBallIncidence
#check @ProximityGap.ProjectiveProperQuotientBall.properProjectiveBallIncidence_eq_affine_add_infty
#check @ProximityGap.ProjectiveProperQuotientBall.properAffineBallIncidence_spectral
#check ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.exists_more_than_eight_proper_points
#check ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.conjecture_hypotheses_hold
#check ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.unrestricted_halfRadius_mds_line_refuted
#check ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily.tangentPoint_eq_secant
#check ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily.tangentInfinity_eq_secant
#check ArkLib.ProximityGap.Frontier.HalfRadiusConicSecantBoundaryFamily.conic_family_numerics
#check ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.no_fourColumnSpan_contains_line
#check ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.representative_ne_zero
#check ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.every_representative_proper
#check ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.strict_low_rate_hypotheses
#check ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly.badScalarRichPointFamily_card_le_two_mul
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin.epsMCA_halfPredecessor_rateSixteenth_le
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin.evalCode_mcaDeltaStar_eq_half_of_rateSixteenth
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.badScalarRichPointFamily_card_le_two_mul
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin.epsMCA_halfPredecessor_rateEighth_le
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin.evalCode_mcaDeltaStar_eq_half_of_rateEighth
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCutoffArithmetic.johnson_strata_at_union_cutoff
#check ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound.constantWeight_plotkin_div
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse.card_le_two_mul_of_pair_inter_le_succ
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse.card_le_two_mul_or_exists_large_pair
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse.card_le_two_mul_or_exists_pair_core_ge_half_add_two
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse.badScalar_count_le_two_mul_of_directionAgreementCapSucc
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine.lineBadScalars_card_le_fourteen_of_support_le_two
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine.lineBadScalars_card_le_sixteen_of_support_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine.zeroAgreementStratum_five_card_le_four_of_support_four
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine.fullSupportSixStratum_card_le_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine.zeroAgreementStratum_eight_card_le_one_of_support_four
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine.lineBadScalars_card_le_six_stratum_add_fourteen_of_support_four
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSixStratumRefuted.supportFour_sixStratum_cap_four_refuted
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceCoupling.lineBadScalars_card_le_eighteen_of_support_four_of_eight_nonempty
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceCoupling.lineBadScalars_card_le_sixteen_of_support_four_of_eight_nonempty_of_six_card_le_six
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceResidual.lineBadScalars_card_le_sixteen_of_top_three_overlap_card_le_six
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSmoothCounterexampleF97.thirtyTwo_lt_badScalar_filter_card
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterMu16Locator.locatorC_eq_affine
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic.maximal_bad_count
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic.agreement_mass_eq_threshold
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic.unsafeConstant_pow_N_ne_one
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleOperationalCountConnector.mcaDeltaStar_le_twentyThree_over_fortyEight_correction_of_badScalar_filter_card
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer.N_lt_badScalar_filter_card
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer.prizeEpsilon_lt_rateQuarter_epsMCA_half
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer.rateQuarter_mcaDeltaStar_lt_half
#check ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer.rateQuarter_mcaDeltaStar_le_twentyThree_over_fortyEight_correction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterOperationalBracket.rateQuarter_mcaDeltaStar_mem_operational_bracket
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge.evalCode_rateQuarter_mcaDeltaStar_le_advertised
#check ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalOperationalBracket.evalCode_rateQuarter_mcaDeltaStar_mem_operational_bracket
#check ArkLib.ProximityGap.Frontier.RateQuarterCommonFactorOwnershipAmplifier.amplified_ownership_budget
#check ArkLib.ProximityGap.Frontier.RateQuarterCommonFactorOwnershipAmplifier.amplified_threshold_le_saturated_of_degree
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic.delta_eq_fortyThree_over_ninetySix_correction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic.unsafeCosetIdentifier_injective
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorBadCount.saturated_badScalar_filter_card_ge_N_add_two
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorBadCount.rateQuarter_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorCanonicalBridge.evalCode_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorCanonicalBridge.evalCode_commonFactor_mcaDeltaStar_lt_half
#check ArkLib.ProximityGap.Frontier.MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_iff_predecessor_good_of_upper
#check ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorGenericSplit.predecessorDelta_le_mcaDeltaStar
#check ArkLib.ProximityGap.Frontier.P1RateQuarterAdjacentExactPin.evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_structured
#check ArkLib.ProximityGap.Frontier.RateQuarterSaturatedFiveCoreBarrier.not_five_saturated_cores_in_primitive_cluster
#check ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity.fourTwoFreshCluster_label_card_le_universe
#check ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity.fourSaturatedCluster_label_card_le
#check ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction.P1.mcaBadCount_le_N_of_favorableFourTwoFreshPencilExtraction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterFourPencilExactPin.CanonicalLargeBadFourPencilExtraction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterFourPencilExactPin.evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_largeBad_fourPencil
#check ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorResidualEquiv.predecessorStructuredFloorResidual_iff_largeBadFourPencilExtraction
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit.projectivelyStructuredRankTwo_of_N_lt_badCount
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit.projectivelyNear_exists_support_le
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveStructuredSplit.predecessorStructuredFloorResidual_of_projectivelyStructured
#check ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand.predecessor_lineBadScalars_card_le_N_of_support_le_twoTier
#check ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand.predecessor_mcaEvent_filter_card_le_N_of_support_le_twoTier
#check ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand.predecessor_mcaEvent_filter_card_le_N_of_zero_card_ge_twoTier
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit.twoTierClosedBudget_add_one_lt_N
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit.support_gt_twoTierCap_or_zeroDirectionUnsafe_of_N_lt_badCount_rowMix
#check ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit.support_gt_twoTierCap_or_transported_jointAgreement_of_N_lt_badCount_rowMix
#check ProximityGap.JointWitnessCharge.mcaEvent_exists_fresh_coordinate
#check ProximityGap.JointWitnessCharge.card_le_complement_of_injective_fresh_charge
#check ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge.predecessorJointList_card_le_five
#check ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge.N_lt_johnsonCap_mul_freshComplement
#check ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge.exists_fresh_coordinate_with_three_charges_of_threshold_overBudget
#check ProximityGap.JointWitnessCharge.ClauseOnlyCounterexample.not_exists_injective_fresh_charge
#check ArkLib.ProximityGap.Frontier.RateQuarterSharedFreshCoordinateCounterexampleF11.shared_fresh_triple
#check ProximityGap.SharedFreshPencil.pairJointAgreesOn_inter
#check ProximityGap.SharedFreshPencil.witness_not_subset
#check ProximityGap.SharedFreshPencil.pencil_absorption
#check ProximityGap.SharedFreshPencil.collinear_agrees_on_pairCover
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate.SharedFreshTripleFree
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate.badFamily_card_le_N_of_sharedFreshTripleFree
#check ArkLib.ProximityGap.Frontier.SharedFreshRealizabilityF11.sharedFreshTriple_realizable
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleRefuted.sharedFresh_family_card
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleRefuted.not_sharedFreshTripleFree
#check ArkLib.ProximityGap.Frontier.P1RateQuarterCollinearMismatchCharge.card_le_domain_of_collinear_witnesses
#check ArkLib.ProximityGap.Frontier.P1RateQuarterInterleavedCollapseNoGo.collapseNumerator_le_N_iff
#check ArkLib.ProximityGap.Frontier.P1RateQuarterInterleavedCollapseNoGo.not_uniform_interleavedList_card_le_one
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator.supportDividedDifference
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator.anchoredKernelRigid_iff_gauged_ker_eq_bot
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceOperator.pairJointAgreesOn_of_anchoredKernelRigid
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceLocalRigidity.eval_eq_local_affine_of_mem_ker
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceLocalRigidity.mem_ker_iff_exists_supportedAgreement
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation.polynomialPencil_eq_of_coordinatewise_two_labels_agree_on
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation.polynomialPencil_eq_of_two_labels_agree_on
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation.all_labels_agree_of_coordinatewise_two_labels_agree_on
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferencePencilPropagation.all_labels_agree_of_two_labels_agree_on
#check ArkLib.ProximityGap.Frontier.P1RateQuarterPropagationPlotkinNoGo.secantCore_plotkin_denominator_nonpositive
#check ArkLib.ProximityGap.Frontier.P1RateQuarterPropagationPlotkinNoGo.domain_sub_two_secantCore_weights
#check ArkLib.ProximityGap.Frontier.MaximalMinorIdealCertificate.mulVec_injective_of_maximalMinor_certificate
#check ArkLib.ProximityGap.Frontier.MaximalMinorIdealCertificate.mulVec_injective_of_symbolicVandermonde_certificate
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge.gaugedCoefficientMatrix_mulVec_gaugedCoefficientVector
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge.degreeAnchoredKernelRigid_of_gaugedCoefficientMatrix_injective
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge.degreeAnchoredKernelRigid_of_symbolicVandermonde_certificate
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.not_anchoredKernelRigid_of_third
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.DegreeAnchoredKernelRigid
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.component_eq_zero_of_twoZeroCoverage
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.degreeAnchoredKernelRigid_of_commonAnchorCoverage
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.degreeAnchoredKernelRigid_of_coordinateBootstrap
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.degreeAnchoredKernelRigid_of_bootstrap
#check ArkLib.ProximityGap.Frontier.SupportDividedDifferenceUnrestrictedKernelRefuted.pairJointAgreesOn_of_degreeAnchoredKernelRigid
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.p1_card_mul_K_le_projectedBudget_of_seven_le
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.p1_card_mul_K_le_projectedBudget_of_three_le
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.p1_singletonHallBad_card_le_six
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.p1_singletonHallBad_card_le_two
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.exists_anchor_pair_covering_singletonHallBad
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.pair_projectedBudget_add_exactThree_eq_singletons
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.exactThree_gt_singleton_surplus_of_pair_bad
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.p1_no_four_pair_obstruction_ledger
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.not_four_disjoint_pairHallBad
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.exists_six_cover_of_not_four_disjoint
#check ArkLib.ProximityGap.Frontier.P1RateQuarterSmallSubsetRankLocalization.exists_six_label_pairHall_cover
#check ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeFourCoreBarrier.exists_pair_inter_card_ge_three_mul_add_one_of_three_next_cores
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity.threeLineDeterminant_eq_zero_of_core_card_sum_sub_domain_gt
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity.threeLineDeterminant_eq_zero_of_jointCore_card_sum_sub_domain_gt
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.lineDeterminant_eq_zero_of_two_mul_pred_add_coreUnion_lt_coreSum
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection.card_le_domain_of_collapsed_fresh_petals
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_small_core_complement
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_saturated_small_complement
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_saturated_half_cores_inter_le_two
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_core_union_eq_univ
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCrossCoreScalar.slope_diff_ne_zero_and_scalar_eq_of_cross_core
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalAssembly.card_le_domain_of_collapsed_clusterCoreUnion
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy.card_le_two_mul_of_half_core_fresh_target_supply
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy.equal_reference_slope_or_card_le_or_uncovered_or_starved_scalar
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply.card_le_two_mul_of_aggregate_high_core_fresh_supply
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply.card_le_two_mul_or_uncovered_or_forbidden_capacity
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores.directionDisagreement_card_le_pred_of_distinct_relevant_equalSlope_halfCores
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores.G_card_le_halfCoreLines_mul_pred_of_equalSlope_cluster
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth.second_high_core_or_reduced_budget_failure
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth.exists_saturated_high_core_petal_ge_half_add_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure.halfCoreLines_mul_denominator_le_numerator
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure.G_card_le_two_mul_of_equalSlope_halfCore_cover
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnifiedClosure.card_le_two_mul_or_uncovered_or_nonEqualSlope_forbidden_capacity
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreCompleteResidual.reduced_budget_failure_or_uncovered_or_nonEqualSlope_forbidden_capacity
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier.relevant_high_core_not_reduced_budget_of_global_cap
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreSharpSecantExtraction.card_le_or_second_high_core_or_sharp_secant_residual
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreSharpSecantExtraction.card_le_or_second_high_core_or_exact_three_hole_residual
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse.eight_le_regularOutsideLine_card_of_card_gt_sixteen
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis.card_le_sixteen_of_two_distinct_eight_cores
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis.card_le_sixteen_or_unique_eight_core_or_no_eight_intermediate
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity.exists_overlap_three_core_eq_eight_of_three_regular_same_rootTriple
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleCollinearity.exists_second_eight_core_or_crossTriple_six_seven_core
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer.exists_uniqueCoreCrossTripleResidual_of_card_gt_sixteen
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer.uncovered_subset_fullAgreement_of_eight_seven_overlap_two
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo.offResidualSecant_affine_plane_normal_form
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo.regularOffResidualSecant_card_four_five_of_six_le_secant_core
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer.crossTriple_threeHole_population_or_fourHole
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourThreeHoleSaturation.regularOffResidualSecant_card_eq_four_of_six_le_secant_core
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourThreeHoleSaturation.crossTriple_threeHole_four_population_or_fourHole
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourFourHoleClasses.allFourHolePopulation_card_le_four
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourFourHoleClasses.crossTriple_threeHole_population_or_fourClassWall
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSharedHolePrimitive.residual_exists_four_regular_pair_source_hole_escapes
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome.uniqueEightCoreResidual_quotient_degenerate
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy.uniqueEightCoreResidual_not_exactly_one_contained_column
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy.dependent_punctured_rows_route_to_exceptional_band
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreClosed.uniqueEightCoreResidual_false
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreClosed.card_le_sixteen_or_no_eight_intermediate
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction.noEight_sparse_syndrome_dichotomy
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSignatureRefuted.abstractNoEightSignatureCap_REFUTED
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixRootSupport.sourceSix_weight_four_support_coupling
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixLongStratum.three_add_root_inter_le_sourceMissed_union_of_noEight_source_six
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixLongStratum.three_le_sourceMissed_union_of_noEight_source_six
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixLongStratum.third_outside_mem_pointsOn_secant_of_sourceSix_root_missed_balance
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixLongStratum.false_of_five_sourceSix_outsiders_root_missed_balance
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixSignatureRefuted.abstractNoEightSixSignatureCap_REFUTED
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport.two_add_root_inter_le_missed_union_of_noEight_source_seven
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootFiber.sourceSeven_outside_regularFiberCapped_or_missed_card_le_two
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum.three_le_missed_union_of_noEight_source_seven
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum.third_outside_mem_pointsOn_secant_of_root_missed_balance
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum.false_of_five_outsiders_root_missed_balance
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted.balancedWitnesses_card_le_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted.exists_balancedWitnesses_card_eq_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenMultiplicityRefuted.thirteenRegularSignaturesForceFourBalancedWitnesses_REFUTED
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted.thirteen_three_column_representations
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightBareSyndromeRefuted.annihilator_direction_ne_zero
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture.card_le_sixteen_or_exceptional_direction_core_band
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure.card_le_sixteen_of_direction_core_card_eq_thirteen
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure.card_le_sixteen_or_exceptional_direction_core_band_twelve
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe.zeroAgreementStratum_six_card_le_three_of_support_four_of_not_safe
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe.family_card_le_eleven_of_direction_core_twelve_of_not_safe
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe.card_le_sixteen_or_exceptional_direction_core_band_eleven_or_safe_twelve
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapGlobalConsumer.card_le_sixteen_or_coreResidual_and_exceptionalDirectionResidual
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionSourceAlignment.uniqueEight_direction_eq_sourceSlope_of_twelve_le
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionSourceAlignment.noEightSeven_direction_eq_sourceSlope_of_thirteen_le
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis.card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning.card_le_two_mul_or_saturated_high_core_or_intermediate_with_third_petal
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning.card_le_two_mul_of_saturated_intermediate_secantPetal_cap
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalPetalSynthesis.card_le_two_mul_or_high_core_half_petal_or_intermediate_third_petal
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth.determinant_collapse_or_three_large_petals_union_growth
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth.canonical_secant_petals_collapse_or_union_growth
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration.canonical_three_secants_collapse_or_companion_increment
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration.exists_large_anchor_with_uniform_companion_increments_of_saturated_intermediate
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalSelectionRefuted.weighted_overlap_eq_two_mul_pred
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalSelectionRefuted.three_companion_petals_do_not_exhaust
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis.exists_anchored_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
#check ArkLib.ProximityGap.Frontier.R396PolynomialLinePluckerSyzygy.lineDeterminant_cocycle
#check ArkLib.ProximityGap.Frontier.R396PolynomialLinePluckerSyzygy.eval_lineDeterminant_eq_zero_of_two_eq_zero_of_firstComponent_ne
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCocircuitRigidity.extension_word_eq_smul_of_support_subset
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterAbstractCocircuitRefuted.abstract_short_affine_count_le_ground_REFUTED
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity.off_line_root_caps_saturated_of_overlap_three
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization.overlap_three_two_block_reconciliation
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor.overlap_three_cubic_recursive_reconciliation
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeAnchorRigidity.overlap_three_three_distinct_equal_quotient_anchors
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour.overlap_three_kfour_constant_quotient_reconciliation
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour.unique_line_intersection_of_common_factor
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse.outsideLineAtLeast_ten_card_le_one_of_card_gt_sixteen
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse.eight_le_regularOutsideLine_card_of_card_gt_sixteen
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation.offBothPoints_card_le_ten_of_relevant_core_cap
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation.card_le_sixteen_of_equal_slope_overlap_three_core_cap
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual.overlap_three_core_cap_saturation_of_sixteen_lt_card
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure.offBothPoints_card_le_nine_of_unequal_slope
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure.card_le_sixteen_of_overlap_three_core_cap
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis.lineDeterminant_eq_zero_of_three_relevant_half_core_lines
#check ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis.card_le_two_mul_or_high_core_or_intermediate_core_without_complement
#check ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoDeltaStarFloor.secondPrime_rateSixteenth_deltaStar_bracket
#check ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction.thirdBlock_sharedSubmodule_is_supportImproper
#check
  ProximityGap.ProjectiveWorstCaseIncidenceBoundary.worstCaseIncidenceBounded_iff_projective_fails_at_full_field

/-! ════════════════════════════════════════════════════════════════════════════
    ║   §Y.  THE HISTORICAL ENTROPY CANDIDATE IS REFUTED FINITELY                ║
    ════════════════════════════════════════════════════════════════════════════

  `PrizePinConjecture` is false as stated.  It passes the polynomial degree ratio `k/n` to
  `prizeDeltaStar`, although `evalCode g n k` has dimension `k+1`.  It also mixes Mathlib's
  natural-log `Real.binEntropy` with the base-two denominator `Real.logb 2 B`.

  At the unconditional dimension-one pin over `F_12289`,

  `mcaDeltaStar (evalCode 4043 8 0) (14/12289) = 3/4`.

  The historical degree-rate side is `1`; the same mixed-base expression at the actual rate
  `1/8` is strictly ABOVE `3/4`; and the obvious base-consistent repair is strictly BELOW `3/4`.
  All three statements are machine-checked in `PrizeEntropyPinRefuted`.  Therefore none is a
  generic finite exact formula.  These counterexamples do not refute a suitably corrected
  asymptotic law or any of the four production instances.

  The independent discrete ladder theorem `prizeDeltaStar_ceiling` remains valid: it proves
  `δ* ≤ 1-r/2^μ` at a certified rung under the stated collision-resultant hypothesis.  It does
  not prove equality with either entropy expression.  The production worst-case incidence/list
  upper bound remains the open core. -/

#check @ProximityGap.PrizeEntropy.prizeDeltaStar
#check @ProximityGap.PrizeEntropy.prizeDeltaStar_ceiling
#check @ProximityGap.PrizeEntropy.prizePinConjecture_degreeZero_F12289_REFUTED
#check @ProximityGap.PrizeEntropy.actualRateEntropyPin_degreeZero_F12289_REFUTED
#check @ProximityGap.PrizeEntropy.actualRateBitsEntropyPin_degreeZero_F12289_REFUTED
/-! ════════════════════════════════════════════════════════════════════════════
    ║   §D   THE DEMAND-SIDE LANE (#389) — CensusDomination #bad-scalar count    ║
    ════════════════════════════════════════════════════════════════════════════

    A SECOND, COMPLEMENTARY attack surface (parallel to the Shaw operator §3): instead of the
    spectral error of the line–ball incidence operator, count the **deep-band bad scalars
    directly** and dominate them by the supply budget. The established reduction (#389 dossiers
    `scripts/probes/genlaw/o165_census_demand/`, `o172_qthreshold/`):

      **CensusDomination** : the prize reduces to the deep-band #bad-scalar count being
      `≤ K = 2^r · C(n/2, r)`  (pinned `k_c = (r−2)m+1, a₀ = rm+1, deficit 2, m = 1`).

    Here `#bad` is the number of DISTINCT bad scalars `γ` of the deep-band witness pencil
    `X^{k+1} + γ·X^k` over the smooth domain `μ_n` — the demand side of the line–ball incidence.
    It is `q`-INDEPENDENT and finite-combinatorial: O172 proves the production `q` is the WORST
    case (a saturating envelope, char-0 supremum), so the char-0 count transfers to production.

    ──────────────────────────────────────────────────────────────────────────────
    §D.1  THE r = 3 BRICK — CLOSED, all n, axiom-clean (`DeepBandR3Bound`, O172).
    ──────────────────────────────────────────────────────────────────────────────
    Parametrising `n = 4g` (`n/4 = g`, `h = n/2 = 2g`):
      · `deepBandBadCount g = n·C(n/4, 2) + 1 = 2g²(g−1)+1`  (`deepBandBadCount_eq_choose`).
      · `deepBandBudget g  = 2^3·C(2g, 3) = K|_{r=3}`.
      · `deepBandBadCount g ≤ deepBandBudget g` for `g ≥ 2`  (`deepBandBadCount_le_budget`) —
        the r = 3 CensusDomination obligation, PROVEN for ALL n divisible by 4 (`n ≥ 8`).
      · the exact margin identity `12·(K − #bad) = (2g−2)(2g)(13·2g−16) − 12`, i.e.
        `K − #bad = (h−2)·h·(13h−16)/12 − 1 > 0`  (`twelve_mul_budget_sub_count`).
      · the mechanism is the in-tree Vieta pin `γ = −∑_{ζ∈S} ζ`
        (`badscalar_eq_neg_subset_sum`, = `SinglePencilSharper.witness_pin_eq_neg_sum`); the
        count `deepBandBadCount` is the cardinality the in-tree spectrum bound
        `witness_badscalar_card_le_spectrum` is upper-bounded by.

    The geometric-count↔closed-form bridge is `R3CensusCountValue` ([COMPUTED] — config count
    `n·C(n/4,2)` field-independent + the proven `pair_sums_ne_modp` distinctness); the obligation
    holds conditional on it (`r3_censusDomination_of_countValue`) AND the closed-form arithmetic
    is unconditional. -/

open ArkLib.ProximityGap.DeepBandR3

-- SMOKE TEST — the r = 3 demand-side brick resolves here:
#check @deepBandBadCount             -- #bad(r=3) = n·C(n/4,2)+1
#check @deepBandBudget               -- K|_{r=3} = 2^3·C(n/2,3)
#check @deepBandBadCount_eq_choose   -- the O172 closed form
#check @deepBandBadCount_le_budget   -- #bad ≤ K, all n (the r=3 obligation, PROVEN)
#check @twelve_mul_budget_sub_count  -- the exact K−#bad margin identity
#check @badscalar_eq_neg_subset_sum  -- γ = −∑ζ (the in-tree Vieta pin, re-exported)
#check @r3_censusDomination_of_countValue  -- the full obligation conditional on the COMPUTED count

/-- The r = 3 deep-band CensusDomination bound is in scope and usable (sanity handle). -/
example (g : ℕ) (hg : 2 ≤ g) : deepBandBadCount g ≤ deepBandBudget g :=
  deepBandBadCount_le_budget g hg

/-! §D.2  THE r = 4 RUNG — PROVEN axiom-clean (`DeepBandR4Bound`, O177). 2-adic descent to r=3:
      `deepBandBadCount4 g = g^4 - 2g^3 + 4g + 1 = 1 + n·deepBandBadCount(n/8)` (n=4g).
      `deepBandBadCount4_le_budget` (#bad₄ ≤ K, g≥2) AND `deepBandBadCount4_le_half_budget_of_prize`
      (#bad₄ ≤ K/2, g≥3, the whole prize domain) — both Lean-proven. Exactness #bad=formula is
      COMPUTED (descent bijection, n=16/32/64); the ≤K and ≤K/2 bounds are PROVEN. -/
open ArkLib.ProximityGap.DeepBandR4 in
example (g : ℕ) (hg : 3 ≤ g) :
    2 * deepBandBadCount4 g ≤ deepBandBudget4 g :=
  deepBandBadCount4_two_mul_le_budget g hg

/-! §D.3  THE r = 5 RUNG — PROVEN axiom-clean (`DeepBandR5Bound`, O181). #bad₅(g) =
      (4g⁴ + 3g³ − 10g² + 12)/12 (g=n/4) = 1 + (n/2)·full_orb, full_orb=(4g³+3g²−10g)/24.
      `deepBandBadCount5_le_budget` (≤K) AND `deepBandBadCount5_two_mul_le_budget` (≤K/2),
      both g≥3 (whole prize domain), Lean-proven. KEY: #bad₅ is DEGREE 4 in g while K is
      DEGREE 5 ⟹ #bad/K → 0 (K/#bad = 20,97,284,684 diverging) — an extra degree of headroom
      vs r=4. Maximizer = the d=n/2 half-order resonance line (n/2+1, n−1). Exactness COMPUTED
      (n=16/32/64/128 via the divided-difference orbit kernel); ≤K, ≤K/2 PROVEN. -/
open ArkLib.ProximityGap.DeepBandR5 in
example (g : ℕ) (hg : 3 ≤ g) :
    2 * deepBandBadCount5 g ≤ deepBandBudget5 g :=
  deepBandBadCount5_two_mul_le_budget g hg

/-! ════════════════════════════════════════════════════════════════════════════
    ║              ▼▼▼   DEMAND-SIDE GENERAL-r CONJECTURE HERE   ▼▼▼             ║
    ════════════════════════════════════════════════════════════════════════════

    The r = 3 brick is CLOSED (§D.1). The OPEN demand-side core is the general-`r` deep-band
    #bad-scalar bound. State and prove `deepBandBadCount_r r n ≤ K(r,n) = 2^r·C(n/2, r)`.

    WHAT IS KNOWN (calibrate against this — do NOT contradict it):
    · r = 3 is closed all-n (the brick above): `#bad(3) = n·C(n/4,2)+1`, divisor family `x^{n/2}`.
    · The worst-case monomial family is DIVISOR-DEPENDENT: `x^{n/2}` saturates at r = 3; at r = 4
      that line degenerates (#bad = 1) and the `x^{n/4}` family takes over. So a SINGLE closed
      form across r is unlikely — expect a max-over-divisors / per-band statement.
    · #bad is NON-MONOTONE in r (n = 16 faithful: r = 3..8 → 97,145,89,113,225,104 vs
      K = 448,1120,1792,1792,1024,256), but `≤ K` with margin 2.46×–20.1× (n=16), 5.0× (n=32, r=3),
      33× (n=32, r=4). General-`r ≤ K` is MEASURED only — this is the open analytic core.
    · The literal alignable-SETS form is FALSE (O171 lossy overcount: #align ≫ K). The correct
      object is the #bad-SCALAR count (distinct `γ`), via the Vieta pin + distinctness.
    · The count is `q`-independent; production `q` is the worst case (O172 saturating envelope).

    THE SHAPE OF A WINNING DEMAND-SIDE CONJECTURE (drop it in, wire it to the budget):

      -- The general-r deep-band distinct-bad-scalar count (smooth μ_n).  [to be DEFINED — the
      -- subset-sum spectrum cardinality of the pinned witness; cf. witness_badscalar_card_le_spectrum]
      -- def deepBandBadCount_r (r n : ℕ) : ℕ := …

      -- The budget at general r.  K = 2^r · C(n/2, r).
      def deepBandBudget_r (r n : ℕ) : ℕ := 2 ^ r * (n / 2).choose r

      -- ▼ THE CONJECTURE ▼  (prove this — it closes the demand-side route to δ*):
      -- theorem deepBand_censusDomination (r n : ℕ) (hn : …) (hr : …) :
      --     deepBandBadCount_r r n ≤ deepBandBudget_r r n := …

    The r = 3 brick (`deepBandBadCount_le_budget`) is the proven instance `r = 3` of exactly this
    statement (with `deepBandBudget_r 3 (4*g) = deepBandBudget g`). Reuse its method: pin the bad
    scalar to a subset-sum spectrum value (`witness_pin_eq_neg_sum`), bound the spectrum
    cardinality, then discharge the resulting `Nat`/poly inequality against `2^r·C(n/2,r)`.

    Once proved, wire to the CensusDomination reduction → an `mcaDeltaStar` equality (T1) or
    `mcaPrizeLatticeResolved` (T2).  Do not infer the uniform `mcaConjecture` (T3) without its
    extra quantifiers; use the applicable LD bridge as T4, exactly as §4's closure contract requires.
    ════════════════════════════════════════════════════════════════════════════ -/

/-- The general-`r` budget `K = 2^r · C(n/2, r)`, ready for the conjecture above to consume.
At `r = 3, n = 4g` this is `deepBandBudget g` (the proven r = 3 brick's budget). -/
def deepBandBudget_r (r n : ℕ) : ℕ := 2 ^ r * (n / 2).choose r

/-- The r = 3 budget specialises the general budget: `deepBandBudget_r 3 (4g) = deepBandBudget g`.
This wires the proven r = 3 brick into the general-`r` conjecture slot. -/
theorem deepBandBudget_r_three (g : ℕ) :
    deepBandBudget_r 3 (4 * g) = deepBandBudget g := by
  unfold deepBandBudget_r deepBandBudget
  congr 2
  omega

/-! ════════════════════════════════════════════════════════════════════════════
    ║   §R.5  SESSION 2026-06-13e — the EXACT δ* (Kambiré window edge) + the      ║
    ║         FACTORIZATION-RIGIDITY proof machinery for the demand-side budget   ║
    ════════════════════════════════════════════════════════════════════════════

    **The exact conjecture (worst case included).** For explicit smooth RS[F_q, μ_n, k] in the
    prize regime (n = 2^μ, q = n^β, ρ = k/n, ε* = 2^-128):

        δ*  =  1 − ρ − 2ρ·ln(1/(2ρ)) / log₂(q·ε*).                      (★)

    This is the Kambiré window edge (arXiv:2604.09724, fleshing out Krachun–Kazanin). The bad
    scalars at radius (1−ρ)−2/s live on the monomial line {X^{rm}+λX^{(r−1)m}} with
    λ ∈ H^{(+r)} = the distinct r-fold sumset of the subgroup H = μ_s; #bad = |H^{(+r)}|, which
    is EXACTLY the demand-side budget `deepBandBudget_r r n = 2^r·C(n/2, r)` (the sumset-growth
    value, here at the maximal divisor). So (★)'s UPPER bracket is the Kambiré construction
    (PROVEN, in-paper); the LOWER bracket (★ is not smaller — no line beats the coset line) is the
    demand-side `deepBand_censusDomination` conjecture above, `#bad ≤ K`.

    **The proof machinery for the lower bracket (this session's contribution):**
    (1) `FactorizationRigidity.mem_range_expand_iff` / `isRoot_smul_of_mem_range_expand` —
        PROVEN, axiom-clean: `∏_{z∈S}(X−z)` is m-sparse ⟺ S is a union of μ_m-cosets; and the
        root set of any X^m-polynomial is μ_m-invariant. (#check'd accessible below.)
    (2) COSET-SATURATION (verified n=16,32; MDS-dichotomy skeleton): for a monomial line
        X^a+γX^b, d=gcd(a−b,n), beyond Johnson EVERY large agreement set is a μ_d-coset-union.
        Proof identity (verified): for x in the agreement set, `ωx ∈ S ⟺ c(x)=c_ω(x)` where
        `c_ω(x)=ω^{−a}c(ωx)` is another codeword; the equivariance subgroup `H={ω: c=c_ω}≤μ_d`
        forces S to be an H-coset-union, and ω∉H give distinct codewords agreeing ≤k−1 (MDS).
    (3) R1 monomial extremality (verified): the worst line is a monomial pencil — a combination
        over-constrains the m-sparse factorization, giving strictly fewer bad scalars.
    (4) R2 (Kambiré optimization): the divisor m maximizing |H^{(+r)}| is the Kambiré choice,
        landing the budget at `deepBandBudget_r`.
    (1)+(2)+(3)+(4) ⟹ #bad ≤ K for every line ⟹ (★) is tight. (1) is PROVEN-in-Lean; (2)(3)(4)
    are verified with proof routes (the one open analytic step is the sharp thin-bound in (2)).
    This reduces the δ* open core (line-list upper bound) to a char-p-FREE combinatorial count —
    escaping the incomplete-Gauss-sum / Weil wall (§3, faces 3↔4). Full detail + refutation
    history: docs/kb/prize-407-exact-deltastar-kambire-conjecture.md. -/

-- The proven factorization-rigidity machinery is accessible here (axiom-clean):
#check @ArkLib.ProximityGap.FactorizationRigidity.mem_range_expand_iff
#check @ArkLib.ProximityGap.FactorizationRigidity.isRoot_smul_of_mem_range_expand
#check @ArkLib.ProximityGap.FactorizationRigidity.isRoot_smul_of_support

end ProximityGap.Workbench
