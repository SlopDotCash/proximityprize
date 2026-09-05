# Retention mapping and correction: G320/G321 rank probes — 2026-09-05

Two archived outputs now have verified producer replays:
`_out_320_krylov_d2_countermodel_stdlib.txt` and
`_out_321_rank_reflection_n12_p13.txt`, both under `scripts/probes/`.
Together with the [mu16 batch](probe-retention-mu16-extensions-2026-09-05.md),
23 of the original 92 unreferenced artifacts are mapped; 69 remain. Both
producer scripts already had direct references and do not add to this count.
No archived output is changed or deleted.

## Exact-rank correction

`g320_krylov_d2_countermodel_stdlib.py` used floor division during its purported
exact row elimination. On `[[2,1],[1,0]]` it returned rank 1, although determinant
`-1` proves rank 2. The corrected implementation replaces each lower row by
`pivot * row - entry * pivot_row`, using exact integer operations. The nonzero
pivot makes this a rank-preserving row operation over the rationals, and it
zeros the current entry without a divisibility assumption. Built-in regression
assertions cover the nonsingular example and a dependent-row example.

Both original example outputs remain byte-for-byte identical after correction.
An independent Fraction-based rank calculation and permutation-formula
determinant provide additional certificates:

| n | p | Seed rank | Augmented rank | Nonzero minor rows | Determinant |
|---:|---:|---:|---:|---|---:|
| 8 | 1009 | 3 | 4 | `(0,1,2,4)` | -285768 |
| 10 | 2011 | 3 | 4 | `(0,1,2,3)` | 308582838 |

The second cell's originally selected `(0,1,2,4)` minor is zero. That alone does
not determine the augmented rank; the new independent certificate supplies a
nonzero minor. The producer docstring now uses the actual second modulus 2011
and removes its incorrect claim that one zero minor would refute the pattern.

## Reflection replay

`g321_rank_reflection_n12_p13.py` reproduces its archived output exactly. It
checks the finite rank-reflection identities at `(n,p)=(12,13)`, including
`A5=A8=-12`, and the `(8,17)` comparison `A3=A6=-1344`. These are exact integer
computations of the script's defined profiles. All four moduli were independently
verified prime by trial division.

The [execution record](probe-retention-rank-checks-2026-09-05.json) includes before
and after hashes, the failing regression, preserved output text, and the explicit
minor matrices. Replays ran in isolated temporary directories with exit zero and
empty stderr. The exact certificates concern these cells only. No corresponding
Lean proof was recompiled in this audit, and no general rank obstruction or
Delta Star theorem is inferred.
