# Retention mapping: four-line mu16 extensions — 2026-09-05

`scripts/probes/probe_rate_quarter_mu16_universal_four_extensions.py` is retained
as an exact finite census related to the
[four-line split-cubic discussion](../deltastar-466-rate-quarter-thickened-isolated-upper-2026-07-10.md).
This adds one artifact beyond the [SYZ30 batch](probe-retention-syz30-2026-09-05.md):
21 of the original 92 unreferenced artifacts are mapped; 71 remain. No research
artifact is deleted.

The unchanged default script completed with exit zero and empty stderr in an
isolated temporary directory. It uses standard-library integer arithmetic and
has no network or file-writing operations. The [execution record](probe-retention-mu16-extensions-2026-09-05.json)
contains its source hash, exact output, and independent parameter checks.

## Exact finite census

For each prime the script constructs the order-16 subgroup from its chosen
primitive root. It enumerates all 560 distinct three-root locators and all
nonzero scalar multiples, keeping fourth cubics whose differences from two
fixed cubics also occur in this finite split-cubic collection. The triangle is
fixed by root triples `(0,1,8)`, `(2,9,10)`, and `(3,5,7)`; this does not enumerate
all possible starting triangles.

| Prime | Root-triple records |
|---:|---:|
| 97 | 31 |
| 193 | 29 |
| 257 | 29 |
| 353 | 29 |

The intersection contains 29 records. All four moduli were independently
verified prime by trial division, and the selected generators were checked to
have orders `p-1` and 16 respectively. Arithmetic is reduced modulo these small
primes, without floating-point approximation.

## Limits of the result

The output field `universal_survivors` names patterns surviving these four
particular fields and chosen generators. It does not certify a characteristic-
independent polynomial identity, all split primes, or all primitive-root choices.
The record stores three root triples, not a universal coefficient witness.
The finite intersection is useful for choosing candidates for a later algebraic
proof, but cannot substitute for that proof.

This run does not revalidate the cited construction's collision budgets or its
production-radius bounds, and it does not settle Delta Star.
