# Retention mapping: error budgets and locator probes — 2026-09-05

Three further scripts from the original unreferenced inventory were inspected
and replayed. Together with the earlier [finite-probe](probe-retention-semantic-batch-2026-09-05.md),
[BGK](probe-retention-bgk-batch-2026-09-05.md), and
[F101 Lean](probe-retention-f101-lean-2026-09-05.md) batches, nineteen of the
original 92 artifacts now have semantic retention records. No artifact is deleted.

The scripts use standard-library arithmetic and seeded sampling, with no network
access or file writes. All three completed with exit zero and empty stderr in
isolated temporary working directories. The [execution record](probe-retention-bounds-locators-2026-09-05.json)
contains exact source fingerprints, arguments, output, and parameter checks.

## Error-budget arithmetic

`probe_fsme_bivariate_johnson_error_floor.py` maps to the
[existing error-floor comparison](../deltastar-466-rate-quarter-bchks25-eq13-exact-barrier-2026-07-10.md).
It reproduces the exact rational predecessor value `240473429/536870912`,
strictly between `3/8` and `1/2`, and the scalar budget
`2^63 * 10^7 = 92233720368547758080000000`. The budget exceeds `N=2^30`
by a factor of `85899345920000000`. Logarithms and displayed decimals are
approximations; the asserted budget comparisons use exact integers or fractions.

The replay also checks that the displayed worst-case joint-core lower bound is
below `K` even at interpolation degree zero. That is an insufficiency of this
lower-bound argument, not a proof that interpolation fails for every input.
Likewise, the convexity bound suffices with six sets and is below `K` with five;
the latter does not itself construct a five-set counterexample. The script's
large modulus is an arithmetic parameter here; this run does not certify its
primality or recheck the cited Lean theorem.

## Complementary pair fibers

`probe_pair_locator_torus_fibers.py` implements the diagonal projectivity retained
in the [R397 route](../deltastar-466-r397-complementary-pair-projective-route-2026-07-09.md).
With `p=97`, `n=16`, generator `5`, seed `397`, and 1,000 sampled anchor/petal
configurations, the largest observed fiber has size two. For each configuration,
all complementary pair choices are enumerated exactly. The configurations
are sampled, so two is not a universal maximum. This is the `k=4` pair model,
not its general higher-degree counterpart.

## Single-image projective lines

`probe_subset_locator_projective_lines.py` enumerates all blocks and pair-defined
projective lines for each sampled petal. With `p=97`, `n=32`, generator `5`, seed
`399`, and ten configurations, the successive observed maxima are 32 and 34.
The 34-point line has equation coefficients `(1,16,5)` for the recorded anchors
and petal. This already exceeds both `2k=16` and `4k=32` for a single image.

This ten-trial run does not reproduce the 35 mentioned in the
[R399 note](../deltastar-466-r399-common-locator-line-hypothesis-2026-07-09.md),
and it does not test the intersection of two locator images on one fixed line.
It therefore neither proves nor refutes that note's surviving intersection
conjecture. The initial 45-second attempt timed out; the unchanged inputs
completed with a 180-second execution limit.

For both locator runs, 97 was separately checked prime by trial division,
all 96 powers of generator 5 were checked distinct, and the derived domains
were checked to have exactly 16 and 32 elements. These are finite arithmetic
checks, not Lean certificates.

## Replay

Run from the repository root:

```sh
probe_repo="$(pwd)"
probe_run="$(mktemp -d)"
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_fsme_bivariate_johnson_error_floor.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_pair_locator_torus_fibers.py" 97 16 5 --trials 1000)
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_subset_locator_projective_lines.py" 97 32 5 --trials 10)
```
