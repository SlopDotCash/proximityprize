# δ* / #466 — G170: the general-D envelope characterization of cross-core generation

Date: 2026-07-11
Lane: direct Opus 4.8 CORE (cron)
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G170GeneralEnvelopeCharacterization.lean`
Probes: `scripts/probes/probe_466_g170_envelope_partition.py` (exact general-D characterization),
`scripts/probes/probe_466_g170_incremental_prefix_nogo.py` (incremental-prefix no-go)
Branch: `research/proximity-prize`

## The question

SYZ33 assembled the rate-1/2 strip theorem as a case split whose ONLY open analytic residual is
**lemma 2** — strip-interior MDS generation. Given an over-budget cover of `[n]` by `s`-cores
`C_1..C_D` in the interior `1/4 < δ < 1/3` (so `2n/3 < s < 3n/4`, `k = n/2`), does the union of
RS-dual restrictions `⋃_i H|_{C_i}` span the full `(n−k)`-dim dual `W`? SYZ28 settled `D = 3`
(deficiency = pair-union subadditivity defect). G170 pins the general-`D` invariant and separates
the provable half from the open half.

## Result 1 — candidate general-D characterization (probe-supported, not a proved all-D theorem)

On the checked domain, the joint RS-dual generation deficiency equals the best (smallest)
envelope-partition count deficit:

```
d = max(0, (n − k) − min over set-partitions P of  Σ_{G∈P} (|⋃_{i∈G} C_i| − k)_+ )
```

Matched (not merely bounded) on: (a) a seeded-reproducible random sample of 2836 covers,
`D ∈ {3,4,5}`, `n ∈ {12,16,20,24}`, full strip interior, `p = 65537`; and (b) an EXHAUSTIVE
enumeration of all 43780 over-budget covers at `n=12,k=6,s=10,D=3`. Both zero mismatches;
deficiency recomputed by direct nullspace of the overlap-agreement system. This is a CANDIDATE
characterization: it generalizes SYZ28's `d = max(0,(n+k) − min_pairing(|C_i∪C_j|+|C_l|))`
(`D = 3`, single pair-vs-singleton partition) to arbitrary `D` and arbitrary set-partitions, and
is corroborated on the checked cases only. It is NOT proved for arbitrary `D`; only the
deficiency-forcing (upper-bound) direction (Result 2) is a theorem. The matching lower bound
(the envelope partition is attained) is the open MDS-genericity residual (Result 3).

## Result 2 — the deficiency-forcing half is an axiom-clean theorem (Lean)

The upper-bound / no-go direction is a pure dimension count, hence field-independent — the formal
reason interior deficiency is field-independent. Formalized in `_G170GeneralEnvelopeCharacterization.lean`,
all axiom-clean `[propext, Classical.choice, Quot.sound]`:

- `partialSup_le_block_envelope` — general-`D` two-block split: `partialSup A m ≤ B` ⟹
  `partialSup A (m+t) ≤ B ⊔ partialSup (fun j => A (j+m)) t`.
- `finrank_partialSup_le_block_envelope` — `finrank ≤ finrank B + finrank(tail)`.
- `block_envelope_forces_deficiency` — envelope deficit `< finrank W` ⟹ generation fails.
- `block_envelope_specializes_to_D3` — `m=2,t=1` recovers SYZ28 `partialSup_three_le_envelope`.

## Result 3 — the matching NO-GO (why lemma 2's positive direction stays open)

The lower bound (`d ≤` best partition count, i.e. the envelope partition is attained) is
MDS-arithmetic-essential and CANNOT be supplied by covering combinatorics. `probe_466_g170_incremental_prefix_nogo.py`:
there exist concrete over-budget interior RS covers admitting NO incremental-prefix ordering (no
ordering makes each core meet the prefix-union in `≥ k` points), yet generation still resolves by
RS-dual computation (`d = 0` on some, `d = 1` field-independently on the near-dup-pair sibling).
Example (`n=16,k=8,s=11,D=3`): cores
`[[2,3,5,6,7,8,10,11,12,13,14],[1,3,4,5,7,8,11,13,14,15,16],[1,3,5,7,8,9,11,13,14,15,16]]`
has `d = 1` over `p ∈ {101,1009,65537,10⁶+3}` and no incremental-prefix ordering. So:

1. SYZ26 `incremental_of_large_cores` (needs `|G|+k ≤ 2s`, i.e. `δ ≤ 1/4`) genuinely fails in
   the interior — confirmed sharply.
2. Generation `d=0` holds on covers where it fails — the truth is not overlap-combinatorial.

The missing lemma-2 proof must attack the RS-dual `no_common_low_degree_annihilator` object
directly (Schwartz–Zippel / determinant-nonvanishing on a fixed field), not overlap counting.

## Consistency and scope

The `d=1` witness is exactly the SYZ28 near-duplicate-pair defect; its yield-cap
`Σ(n−s_i) = 15 = n−1` saturates the SYZ22 budget with zero slack — budget-safe, strip NOT
falsified. Reproduced independently. G170 adds (a) the general-`D` upper-bound theorem and (b) the
incremental-prefix no-go on top of SYZ28's `D=3` result. No new unconditional δ* claim; no
cancellation / anti-concentration / capacity. CORE remains OPEN / ON-BGK.
