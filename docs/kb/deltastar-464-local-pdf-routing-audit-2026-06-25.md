# Issue #464: local PDF routing audit

Date: 2026-06-25.

Status: no prize proof. This note records the local PDF/library pass after the current
Issue #464 loop. The purpose is to prevent duplicate attacks: each source below is routed
to the existing Lean/KB surface it supports, or to the still-open theorem it really needs.

## Inputs checked

Primary local PDFs checked with Poppler metadata/text extraction:

- `/Users/shawwalters/Desktop/2026-680.pdf`
  - Open Problems in List Decoding and Correlated Agreement, 47 pages, 2026-04-08.
- `/Users/shawwalters/Desktop/math/2604.09724v1.pdf`
  - Antonio Kambire, Proximity Gaps Conjecture Fails Near Capacity over Prime Fields, 6 pages.
- `/Users/shawwalters/Desktop/math/2026-861.pdf`
  - Raullen Chai and Xinxin Fan, Action-Orbit FRI Soundness Above the Johnson Radius, 36 pages.
- `/Users/shawwalters/Desktop/math/2025-2054.pdf`
  - Rohan Goyal and Venkatesan Guruswami, Optimal Proximity Gaps for Subspace-Design Codes and
    (Random) Reed-Solomon Codes, 37 pages.
- `/Users/shawwalters/Desktop/math/2304.09445v6.pdf`
  - Alrabiah, Guo, Guruswami, Li, Zhang, Random Reed-Solomon Codes Achieve List-Decoding
    Capacity With Linear-Sized Alphabets, Advances in Combinatorics 2025:8.
- `/Users/shawwalters/Desktop/math/2025-2055.pdf`
  - Ben-Sasson, Carmon, Kopparty, Habock, Saraf, On Proximity Gaps for Reed-Solomon Codes.

Adjacent roots-of-unity and cyclotomic PDFs were also identified on disk: Mann 1965,
Conway-Jones, Aliev-Smyth, cyclotomic-field metric/class-group papers, and related
Galois-module notes. They are relevant background for char-0 vanishing-sum rigidity and
height estimates, but they do not by themselves supply the missing char-p sup bound.

## Routing table

### ABF26 open-problems survey

ABF26 is a target map, not a closure theorem. It confirms that the operational quantity is the
above-Johnson plain-RS proximity/MCA term used in FRI soundness, and that folded/interleaved
variants do not settle the plain smooth-domain RS target. This agrees with the current #464
consumer: the missing input is a worst-case incidence or MCA bound, not a one-family obstruction
check.

Local surfaces:

- `docs/kb/prize-407-faithful-problem-map-from-abf26.md`.
- `ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackCandidateFamilyMax.lean`.

Verdict: ABF26 tells us what the prize-facing consumer is. It does not lower the BGK/Paley wall.

### Kambire 2604.09724

Kambire supplies a ceiling/refutation near capacity over prime fields. The construction chooses
parameters and primes to show proximity gaps fail close to capacity. That is the correct
existential polarity for a negative result, but it is the wrong polarity for proving a universal
delta-star floor over all prize primes/stacks.

Local surfaces:

- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.
- `ArkLib/Data/CodingTheory/ProximityGap/KambireDeepBandFloor.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AssaultV2_FloorLocalizationN32.lean`.
- `docs/kb/deltastar-464-floor-necessary-not-sufficient-critique-2026-06-25.md`.

Verdict: Kambire is a ceiling source. It cannot be inverted into the floor without a universal
worst-case domination theorem.

### Chai-Fan action-orbit paper

The action-orbit paper gives an attractive symmetry mechanism for cyclic domains. Its extracted
abstract states an unconditional result for sparse adversary inputs and a reduction for general
inputs to a sparse-worst-case dominance conjecture. This is exactly where the prize pressure sits:
the sparse orbit theorem is useful only after the unrestricted stack supremum is dominated by the
sparse family.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ChaiFanBasePanelGate.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/C71SparseOrbitGap.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/C71BinomialIncidence.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/C71SparseStrataWindow.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackCandidateFamilyMax.lean`.

Verdict: the open theorem is not "use orbits"; it is sparse dominance/classification for the
unrestricted stack maximum. Without that, action-orbit remains a conditional route.

### GG25 subspace-design and random RS proximity gaps

Goyal-Guruswami proves strong proximity/MCA statements for subspace-design codes, folded RS,
multiplicity-code variants, and random RS domains. These are real positive results, but the issue
target is explicit smooth-domain plain RS. The required bridge is a derandomization or transfer
from those code families/domains to the fixed multiplicative subgroup. Existing local gates already
record that this bridge is not formalized by the GG25 theorem itself.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GG25CurveDecodabilityOpener.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GG25CurveDecodNextBrick.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GG25LineToAffine.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GG25AffineFactorInstance.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/DerandomizationFrontier.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/FoldingTransferNoGo.lean`.

Verdict: GG25 proves nearby positive theorems, not the explicit smooth-domain theorem. The missing
piece is a domain/code-family transfer, and that transfer is itself a hard derandomization problem.

### Random RS list-decoding capacity

The random-RS capacity paper is relevant because stronger list decoding is a prerequisite or
companion for stronger proximity gaps. But its randomness is in the evaluation set. The #464 wall is
the opposite regime: a fixed highly structured subgroup `mu_n`, where the bad sums are Gauss-period
or Paley-type quantities.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/DerandomizationFrontier.lean`.
- `docs/kb/Iinf-campaign/18-literature-landscape-folded-solved-plain-is-BGK.md`.

Verdict: useful evidence for what random domains can do; no direct smooth-subgroup bound.

### BCHKS proximity gaps

BCHKS supplies the classical positive/negative proximity-gap landscape up to the Johnson-centered
regime and shows why stronger proximity gaps interact with list-decodability improvements. It is not
the missing above-Johnson smooth-domain delta-star pin. Its negative constructions also reinforce
the need to track quantifiers: an existence construction can refute a universal conjecture, but a
universal lower pin needs every relevant far direction controlled.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/`.
- `ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean`.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.

Verdict: foundational landscape; no new bypass of the current sup-norm/incidence wall.

### Roots of unity, Mann, Conway-Jones, Aliev-Smyth, and cyclotomic height

These sources are the right background for char-0 vanishing-sum rigidity and finite-support
cyclotomic algebra. They explain why some low-weight or antipodal configurations are rigid over
characteristic zero. The current core, however, is not merely char-0 rigidity. It is the char-p
transfer at prize scale and depth, or an equivalent bound on the maximum dyadic-subgroup additive
character sum.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_wfS7_oddpart_transfer.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PolynomialPrimeExponentialHeightGate.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_IdealLatticeMinkowskiCorrected.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_OnsetWildBuildoff.lean`.

Verdict: char-0 and height tools are useful only after their char-p loss is below the prize scale.
Generic exponential height/resultant bounds are too large.

### Least-prime and Thorner-Zaman/Linnik-style inputs

The off-BGK floor route needs a dyadic least-prime-in-AP input below `n^4` only for a specific
floor/binder obstruction. Even if that input is proved, the conclusion is binder-family goodness at
prize primes. It is necessary obstruction removal, not a universal stack upper bound.

Local surfaces:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AssaultV2_FloorLocalizationN32.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorLinnikTZClosure.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PowerfulTZThetaGate.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorLevelDepthPrimeScaleGate.lean`.

Verdict: a sub-4 dyadic least-prime theorem would close a useful obstruction-removal lane, not the
delta-star prize.

## Remaining honest theorem targets

After routing this PDF set, the remaining non-duplicative targets are narrow:

1. Prove sparse dominance/classification for the unrestricted stack maximum in the Chai-Fan/action
   orbit surface.
2. Prove a char-p hypercontractive or deep-moment theorem that directly implies
   `M(mu_n) <= C * sqrt(n * log(p/n))` in the dyadic subgroup regime.
3. Prove a genuine worst-case incidence theorem in the `OpenCoreConditionalPin` interface, avoiding
   conversion through a merely averaged or smoothed tail.
4. Prove the dyadic least-prime exponent below 4 and the uniform floor-localization theorem, while
   keeping the result scoped as obstruction removal.
5. Find a symmetric-function/coset-rigidity theorem that controls every monomial stack, not only the
   binder or sparse subfamilies.

Everything else in this local PDF batch maps back to an already named gate.
