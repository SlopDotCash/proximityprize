# Proximity Prize results and requirements for a complete proof

The general operational thresholds for both grand challenges remain open. A reviewer can check the specification, the endpoint convention, and several exact instances now. The missing mathematical deliverable is a pair of answers that determine the cutoffs for the supplied code across the claimed range of inputs. Defining an index by minimization over all received words leaves its numerical value undetermined. A certified finite calculation can establish the value for a specified input. The sponsor explicitly asks for the radius and does not require an efficient list decoder. [Sponsor statement](https://proximityprize.org/) · [Arnon, Boneh and Fenzi, §1](https://eprint.iacr.org/2026/680) · [Existing lattice existence theorems](../../../ArkLib/Research/ProximityGap/Lattice2/Spec.lean)

## Statement to check

The review specification takes a finite field, a smooth evaluation domain of length `n`, a tolerance, an MCA answer indexed by dimension, and a list answer indexed by dimension and interleaving width. It tests the exact rates `k/n ∈ {1/2, 1/4, 1/8, 1/16}` whenever that rate exists on the supplied domain. For every real radius in `[0,1]`, each proposed answer must characterize the corresponding canonical security predicate. The compiled declaration `FullPrizeReview.correctForDomain` is a **specification**. A complete solution must supply mathematically determined answer functions and a theorem proving this specification throughout its advertised parameter regime. The sponsor gives 128-bit security as an example. The companion paper highlights smooth evaluation domains for which the code dimension `k` is at most `2^40` and the field size is below `2^256`. A theorem limited to those parameters should state that scope. [Lean specification](../../../ArkLib/Research/ProximityGap/FullPrizeContract.lean) · [Smooth domain definition](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) · [Companion paper, p. 5](https://eprint.iacr.org/2026/680)

The endpoint convention changes the literal statement. On a finite domain closed Hamming balls stay constant between successive integer counts. If the first failure is at error count `e`, the safe real radii are exactly `[0,e/n)` and the last safe integer count is `e−1` when `e>0`. A first failure at zero gives an empty safe set. If every count passes, radius one is an attained maximum. For MCA a greatest good real radius exists exactly when radius one is safe. For positive RS dimension and interleaving width the radius-one list contains all `q^(km)` words, exceeding `εq` when `ε<1`. The attained-maximum list statement is then false over every finite field. These facts establish a correction to the wording. The intended decoding question still requires the location of the first failing step. In the agreement convention, `1−a*/n` for the minimum safe agreement count is the last safe **grid** radius. [MCA maximum criterion](../../../ArkLib/Research/ProximityGap/Frontier/_MCAGoodRadiusMaximum.lean) · [List closed form](../../../ArkLib/Research/ProximityGap/ListClosedForm.lean) · [Integer list threshold](../../../ArkLib/Data/CodingTheory/ProximityGap/ListThresholdWellDefined.lean)

## Missing proofs

| Obligation | What a complete result must supply |
|---|---|
| MCA safety | On every covered code and for every pair of received rows, bound the count of scalar choices that produce an apparent RS agreement without a joint explanation on the same coordinates. At the last safe step this count must be at most `⌊εq⌋`. |
| MCA failure | At the next step exhibit or prove existence of one received pair with more than `⌊εq⌋` bad scalars. Prove the whole interval safe instead when that is the calculated answer. |
| List safety | Bound the number of distinct interleaved codewords close to **every** received center in column Hamming distance, at each specified positive width. The scalar projection theorem transfers the budget predicate under its field-size hypotheses. |
| List failure | Prove that **one** center at the next step contains at least `⌊εq⌋+1` distinct codewords. Identify the boundary as a function of the actual code parameters. |

## What the current proofs determine

Over the 246-bit prime field of order `65·2^239+1`, the 128-point subgroup has exact answers for **both** challenges at every positive interleaving width. At length `2^30` over that same field, Lean gives two-sided MCA bounds for every smooth coset. Each safe radius in the table meets the 128-bit target and each failing radius exceeds it. Thus the longer-domain results still allow multiple possible first failing Hamming counts. [Joint length-128 proof](../../../ArkLib/Research/ProximityGap/Frontier/FourRateSmoothMca128.lean) · [Length-128 list counts](../../../ArkLib/Research/ProximityGap/Frontier/FourRateList128.lean) · [Length-$2^{30}$ endpoint tests](../../../ArkLib/Research/ProximityGap/Frontier/ProductionMcaIntervals.lean)

| Rate | MCA at length 128 | First failing list count at length 128 | Safe MCA radius at length `2^30` | Failing MCA radius at length `2^30` |
|---|---|---:|---:|---:|
| 1/2 | First failure at 62 errors | 63 | 39/128 | 31/64 |
| 1/4 | Safe through radius one | 97 | 67/128 | 95/128 |
| 1/8 | Safe through radius one | 113 | 86/128 | 111/128 |
| 1/16 | Safe through radius one | 121 | 99/128 | 239/256 |

At length `n=2^30`, other field sizes give exact answers. For every prime-field subgroup with `268435458 ≤ ⌊p/2^128⌋ ≤ 536870913`, the four first failing MCA counts in rate order are `268435456`, `min(⌊p/2^128⌋, 402653184)`, `min(⌊p/2^128⌋, 469762048)` and `min(⌊p/2^128⌋, 503316480)`. On the first named prime, whose budget is `n`, rates 1/8 and 1/16 have operational supremum 1/2. Quarter and half rate still have separated bounds. [Exact four-rate window](../../../ArkLib/Research/ProximityGap/Frontier/SharpApolarMCA.lean) · [First-prime results and references](integration-assessment-2026-11-21.md)

On the second named prime, whose budget is `2n`, the end-to-end Lean theorem at rate 1/16 puts the first failing count between **647627102 and 715827882** inclusive. A written argument using a normalized Hessian resultant proves safety through **678536752** errors, raising the written first-failure floor to **678536753**. Its executable certificate checks the integer inequalities. The deduction from arbitrary received rows through the geometric incidence bound remains a written proof. Matching the known three-core failure requires bounding every received pair by `2n` bad scalars at **715827881** errors. An earlier violation would lower the ceiling. [Lean bracket](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeConditionedThreshold.lean) · [Written Hessian bound](second-prime-normalized-hessian.md) · [Integer certificate](../../../scripts/probes/probe_second_prime_normalized_hessian.py)

One route to general MCA safety still requires prime-field character cancellation and an above-Johnson bound on bad scalars. Direct counting has supplied other endpoints. [Conditional incidence reduction](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeFloorOfBGK.lean)

For lists, changing the field can change the answer even at fixed length and rate. At length 128 and quarter rate, the degree-27 extension example first fails at 94 errors. The prime in the table first fails at 97. At length `2^30` a separate prime with budget two gives an exact half-rate first failure at 268435457 errors. In the general case the missing result is the threshold for the worst received center. Below field size `2^256`, scalar and positive-width interleaved lists cross the 128-bit budget at the same radius, so determining the scalar cutoff suffices in that range. [Extension-field threshold](../../../ArkLib/Research/ProximityGap/Frontier/SubfieldQuarterListThreshold.lean) · [Length-$2^{30}$ list example](../../../ArkLib/Research/ProximityGap/Frontier/QuarterBudgetTwoThreshold.lean) · [Scalar projection](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListProjection.lean)

The theorem `ProximityPrize.KnownDomainReview.correctForPrime246` instantiates the full review specification with the length-128 tables. It covers all four eligible dimensions, every positive list width and every real radius in the unit interval at the 128-bit tolerance. [End-to-end proof](../../../ArkLib/Research/ProximityGap/KnownDomainReview.lean)

Two more MCA results clarify the role of the field and the domain.

- For sequences of injective prime-field domains with lengths tending to infinity, rates tending to `ρ ∈ (0,1)`, and `log(p)/n` tending to `c > 0`, the operational radius tends to `1−ρ` when `c < H(ρ)`. When `c > H(ρ)`, every radius through one is eventually safe. Here `H` is binary entropy with natural logarithms. The critical case and exact cutoffs at finite lengths remain open in general. [Prime-field phase theorem](../../../ArkLib/Research/ProximityGap/Frontier/PrimeFieldEntropyPhase.lean)
- At `n = k + 2e` with `k,e > 0`, Lean gives a sharp bound on the number of bad scalars at `e` errors over the choice of domain and received pair. The bound is `n−e+1` if `e+1` divides `n+1`, and the largest multiple of `e+1` at most `n+1` otherwise. For each prime `p > n` with `e+1` dividing `p−1`, the proof exhibits a domain attaining the bound. Attainment on a particular supplied smooth domain requires its own proof. [Apolar endpoint bound and witness](../../../ArkLib/Research/ProximityGap/Frontier/ApolarEndpointExact.lean)

## Reproducing the Lean evidence

Start in a fresh checkout of the review commit with the pinned toolchain and dependency manifest. Give this checkout **its own project build directory**. Two local worktrees linked to the same `.lake/build` produced a stale import during the audit. A fresh client could see the earlier conditional module despite the new unconditional source being present. Rebuilding the changed modules into private output restored the exact declarations. Warm external dependency caches may be reused with matching pins.

```sh
git rev-parse HEAD
./scripts/lake-locked.sh exe cache get
./scripts/validate.sh --axioms
```

The default build includes the Research library. The test target imports the theorem modules and checks independently stated numerical conclusions. The flagship manifest checks the transitive axioms of the reviewer endpoints against `propext`, `Classical.choice`, and `Quot.sound`. The optional library-wide regression sweep has its own roots and historical baseline. A green library sweep and an endpoint-level audit answer different questions. [Review client](../../../ArkLib/Tests/ProximityPrize/GrandChallengeReview.lean) · [Endpoint manifest](../../../scripts/flagship_axioms.txt) · [Sweep scope](../../../scripts/AxiomSweep.lean)

At `18f6fa36e`, a private rebuild of the 59 PR-changed project modules in the external review clients' dependency paths passed using cached unchanged dependencies. The clients checked the length-128 numerical statements, the sharp half-rate window with its predecessor discharged, the second-prime bracket, and the endpoint semantics. All nine audited declarations used only the three standard axioms. This is evidence for those named statements. The general answer functions and their proofs remain the condition for signing off a complete result.

For a future complete claim, record its immutable revision and exact theorem names, the field and domain quantifiers, rates, width, tolerance and endpoint semantics. Check the full signatures for mathematical assumptions, audit their transitive proof dependencies, and replay those exact exports with an independent checker. A machine-checked claim needs a proof or a checked certificate for each mathematical or numerical premise it uses.

## Prize submission

The sponsor welcomes significant partial results and encourages formal verification. Its published guidelines require acceptance by a reputable field-appropriate conference or journal, a public version on an academic repository such as ePrint or arXiv, and an emailed PDF explaining the result, how it addresses the challenge, and its relationship to prior work. The judges evaluate award eligibility and significance. [Submission guidelines and FAQ](https://proximityprize.org/)
