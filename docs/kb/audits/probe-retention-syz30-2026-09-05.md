# Retention mapping: SYZ30 partition sampling — 2026-09-05

`scripts/probes/probe_syz30_partition_blockcount.py` is retained as finite
combinatorial evidence for the [SYZ30 lemma discussion](../deltastar-466-syz30-lemmas-2026-07-11.md).
This adds one artifact to the previous nineteen semantic retention records:
twenty of the original 92 unreferenced artifacts are now mapped; 72 remain.
No artifact is deleted.

The unchanged script and its two imported helper sources were inspected before
execution. The default run completed with exit zero and empty stderr in an
isolated temporary directory. The [execution record](probe-retention-syz30-2026-09-05.json)
contains exact source hashes, output, and an independently checked boundary
example. Imported SYZ28/29 main programs were not executed.

## Reproduced finite results

The script uses seed 7 and 4,000 candidate trials for each `(n,D)` pair. It
retains distinct-core, full-cover, over-budget samples and enumerates all set
partitions of each accepted sample. The six accepted counts are:

| n | D | Accepted samples | Minimum two-block slack |
|---:|---:|---:|---:|
| 16 | 4 | 3387 | 0 |
| 16 | 5 | 3807 | 1 |
| 20 | 4 | 3410 | 1 |
| 20 | 5 | 3818 | 2 |
| 24 | 4 | 3145 | 0 |
| 24 | 5 | 3703 | 1 |

All 21,270 accepted samples selected a one-block minimizing partition with zero
slack. The code keeps the first minimizer on ties, so this does not establish
uniqueness; the zero two-block slacks explicitly show ties. The claim that
two-block slack is always exactly zero is not the output of every parameter
setting. No negative slack appeared in this sample, which is not a universal
all-cover theorem.

## Boundary and theorem scope

The actual size sampler adds `ceil(2*n/3)` to its nominal strict-band sizes.
At `n=24` this includes size 16, outside the strict inequality `2*n < 3*s`.
Four distinct size-16 cores can cover all 24 points and satisfy the over-budget
condition while a three-block partition has union sizes `(17,16,16)`. Its
envelope is `13` at `k=12`, giving slack `1`, not `2`. The JSON contains all four
cores and the exact partition for independent reconstruction.

This example limits the probe header's blanket slack-at-least-two claim on the
expanded sampling domain. It does not refute a Lean theorem requiring the
strict interior band, and no Lean theorem was revalidated here. The script
performs integer set arithmetic; it does not calculate code ranks, establish
field independence, discharge the remaining SYZ30 hypotheses, or settle Delta
Star. Retain it for reproducible sample behavior and this explicit domain caveat.
