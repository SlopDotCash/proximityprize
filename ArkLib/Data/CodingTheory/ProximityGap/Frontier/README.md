# Proximity Gap — Frontier scratch lanes (#334 → #444 → #464 → #466)

Drop-in starting points for the actionable open targets. Each file:
- imports ONLY its minimal substrate (fast `lake env lean`, ~30s, no build lock),
- states the precise target as an honest named `Prop`/hypothesis (no `sorry`, no fake `axiom`),
- documents the reference + the in-tree substrate API to consume.

**Iterate:** `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<File>.lean`
**Land:** one real `lake build <Module>` (autoImplicit=false) + axiom audit, then the push loop.
**Lane hygiene:** files starting `_` are scratch/lane files (most are git-tracked — treat them as
lane state, not throwaway); copy `_TEMPLATE.lean` to start a new lane.
Read the parent `CLAUDE.md` (build/concurrency/honesty rules) before touching anything.

## Live targets (2026-07-01)

**The current campaign is #466.** The ranked live frontier is
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6 (as re-ranked by the §14/§15 round logs) and
`../PROXIMITY_PRIZE_WORKBENCH.lean` §5 — go there for what to attack; this README only records
the status of the original #334-era lane files below.

**2026-07-10/11 state change — read dossier v3 §42 first.** The r=3 B-side rung is now the
lossless graded ladder `OffDiagQuadrupleBound ⟹ FourthMomentBound ⟹ DistStratumEnergyBound`
(lossless = `FullDFTFlat`; R297–R304, rungs m=3/6/9 discharged, all three ladder Props OPEN);
the P1 rate-quarter predecessor D-charge cone is COMPLETE with pin =
`SmallPoolClosure ∧ StallResidual` (heavy window closed, three architectures kernel-refuted,
two-cover window REALIZED); W15 safe branch closed at UD-plus (window
`LargeZeroSafeLineListBudgeted` open). Machine-checked convergence: both cones terminate at the
same beyond-Johnson wall. Bracket unchanged; core open. Full record:
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §42.

## The BGK depth-ladder lane (2026-07-10)

**DC correction (2026-07-11).**  The later raw endpoint
`DepthSevenFlatnessResidual : E₇ ≤ 2¹⁸|G|⁷` is formally refuted at production: the mandatory
zero-frequency term gives `2⁴²⁰ ≤ qE₇`, while the raw residual and `q≤2¹⁵⁹` give
`qE₇≤2³⁸⁷`.  The live successor is the DC-subtracted residual

`qE₇ - |G|¹⁴ ≤ q·2¹⁸·|G|⁷`,

formalized with its full consumer in `_BGKDepthSevenFlatnessResidualRefuted.lean`.  Do not attack
the historical raw Prop in `_BGKDepthSevenFlatnessResidual.lean`.
`_BGKRenergyRepresentationBridge.lean` identifies the BGK lane-local energy with the standard
library energy and proves that standard `DCEnergyBound G 7` implies the repaired coefficient-`2^18`
residual, so the census and BGK lanes now share one exact centered object.

**Centered convolution collapse (2026-07-11).**
`_BGKCenteredConvolutionCollapse.lean` gives the repaired object an exact one-dimensional form.
If `f₆` is the six-fold additive representation function and
`C₆(δ)=Σ_d f₆(d)f₆(d+δ)`, multiplicative invariance gives

`qE₇-|G|¹⁴ = |G|·Σ_{u∈G}(qC₆(1-u)-|G|¹²)`.

Thus the live coefficient-`2^18` residual is equivalent to a **signed** average along `1-G`, not
a positive packet count.  At `|G|=2^30`, `q≤2^159`, the normalized sum has the explicit target
`Σ_{u∈G}(qC₆(1-u)-|G|¹²) ≤ 2^357`.  The centered autocorrelation has exact global mean zero, so
absolute-value or packet-positive envelopes destroy precisely the cancellation this formulation
exposes.  A primitive-character audit also proves that `|G|` times this signed sum is exactly
`Σ_{b≠0}|η_b|^14`; in particular the total sum is nonnegative.  The collapse is therefore a
structural one-dimensional rerouting of the off-zero moment, not a moment-method bypass.
The updated research control plane is the
[`10 x 10 centered attack matrix`](../../../../../docs/kb/deltastar-466-ten-by-ten-centered-attack-matrix-2026-07-11.md),
with the focused 2026 theorem screen in
[`depth-seven per-prime literature audit`](../../../../../docs/kb/deltastar-466-depth7-per-prime-literature-audit-2026-07-11.md).

**Weighted collision and Jacobi audit (2026-07-11).**
`_BGKWeightedCollisionMoment.lean` generalizes the Fourier/collision identity to arbitrary
integer coefficient patterns. In particular, the leading one-repeat partition is the exact
centered mixed moment
`sum_(b != 0) eta_(2b) eta_b^5 eta_(-b)^7`, giving the repeated-sector lane a concrete signed
socket rather than a positive union bound. `_AJT13CenteredMomentEquivalence.lean` closes a
different audit: the proposed 13-variable annihilator Jacobi tensor is exactly the centered
fourteenth moment after deleting the principal character. Its `m^7` bound is therefore an
equivalent dual-coordinate target, not an independent orthogonality saving.
`_AJT13CenteredBoundaryBridge.lean` then proves that a centered Wick-coefficient bound
(`13!!=135135`) absorbs the `1/m` translation inside the public coefficient `2^18` whenever
`m>=21`; the principal-character boundary is no longer a separate Wick-scale residual.

**Dyadic two-scale recursion (2026-07-11).** `_DQR23TwoScaleCenteredRecursion.lean` proves the
exact sibling law `eta_(G union aG)(b)=eta_G(b)+eta_G(ba)`, the full signed binomial ledger at
moment 14, and the quadratic anticorrelation `sum_(b != 0) eta_G(b)eta_G(ba)=-|G|^2`.
`_DQRSecondMomentAnticorrelationNoGo.lean` shows why the last identity is not yet a contraction:
a rational mean-zero sibling array can have negative cross-correlation while its coarse
fourteenth moment grows far beyond the Gaussian factor `2^7`. The live DQR residual is therefore
a higher mixed-moment sign law, not a second-moment estimate.

**Projective accident packets (2026-07-11).**  `_ANT46RungTwoAccidentOrbit.lean` now closes the
full projective `S₄` classifier.  For an odd-characteristic accident the identity fibre has size
`1`, `2`, or `6`; the two-pair pattern is lawful, and the certified production `-3` exclusion
removes the `3+1` pattern.  Hence every production accident orbit has size `24` or `12`, and the
total accident count is divisible by `12`.  This does not prove accident-freeness: the exact next
socket is any independent bound `<12` (or a direct emptiness/resultant certificate).

The `_BGK*` files landed 2026-07-10 hang the ENTIRE depth ladder off the single named open
Prop `WorstCaseIncompleteSumBound` (the BGK sup-bound), end to end at literal prize numbers:
`_BGKSupBoundMomentTower` (every-depth moment tower) → `_BGKDepthREnergyLaw` (exact
`∑‖η_b‖^{2r} = q·E_r`; §8 independence form mod BGK) → `_BGKProductionDepthFiveWeld` /
`_BGKInjectiveFiveWeld` / `_BGKFiberSquareCensusBridge` (BGK ⟹ the G112 production socket's
exact conclusion, replacing its open variance certificate) → `_BGKNineBitGap` (**the sharpest
open sub-target**: trivial anchor `M = 2⁶⁰` proven; weld fires at `M ≤ 2⁵¹`; the whole
depth-five lane = a 2⁹ sup-bound saving over trivial, i.e. `‖η_b‖ ≤ |G|^0.85`). See
`docs/kb/deltastar-466-bgk-moment-tower-and-production-welds-2026-07-10.md`.

## Status of the original #334 lane files

| file | target | status (2026-07-01) |
|------|--------|---------------------|
| `ThornerZamanS128.lean` + `ThornerZamanInstance.lean` | discharge `TZPrimeSupply` (window `[n^β, 2n^β]` has ≥ supply primes `≡ 1 mod n`) | **Concrete ladder LANDED** (axiom-clean, explicit-prime certificates): β=2 through `n = 32768` (`tzPrimeSupply_{8,16,…,32768}_two`), β=3 through `n = 64`, β=4 through `n = 64`, β=5 at `n = 8` — all in `ThornerZamanInstance.lean` (+ `CanonicalWidthFourConcreteTZ.lean`). The *general/asymptotic* Thorner–Zaman PNT-in-APs form remains a named open hypothesis (dossier v3 §6 Tier 3, "largely dischargeable"). |
| `CurveDecodability.lean` | [GG25] Def 3.1 curve decodability → [Jo26] half | OPEN, multi-brick (dossier v3 §6 Tier 3; folded-RS capacity pin via `curveDecodable_of_structured_close_set_budget` is the live adjacent lane) |
| `EquivariancePin.lean` | Lean equivariance pin for the n=12 orbit reduction | LANDED → `../MCAEquivariance.lean` (engine) + `../MCAEigenstackOrbitLaw.lean` (orbit law, counting) |

Historical note: predecessors #334/#357/#444/#464 are CLOSED, each distilled into its
successor; the `_`-prefixed files in this directory are the accumulated lane record of those
campaigns plus the live #466 lanes. Check `../DISPROOF_LOG.md` (`466-r*` round tags, still
accumulating) before re-attempting anything.
