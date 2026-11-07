# wf407-w2 / L5-s256 — census coverage: ℓ¹ row, and a conditional s = 256 row (B3 follow-up)

**Date:** 2026-06-14 · **Thread:** L5-s256 · **Verdict:** ℓ¹ row proved; s = 256 row conditional
on an open census statement; the claimed `2^{3N/2}` resultant bound is REFUTED (2026-10-28 audit)
**Issue:** #407 ← #334 B3

## Correction (2026-10-28 audit, R-323)

The original TL;DR below claimed that Parseval halving gives `|Res| ≤ 2^{3N/2}` for an arbitrary
`{−1,0,1}`-coefficient antipodal differential, and hence unconditional census coverage to
s = 256. That resultant bound is **false**:

- At `N = 16` (`m = 5`) the differential of `E = {1,2,4,5,7,8,9,10,14,19,22,27,28,29,31}` has norm
  against `X^16+1` equal to the prime `412876481 > 2^24`. Over `𝔽_412876481` with the primitive
  32nd root `7881733`, `∑_{e∈E} g^e = 0` although `E` is not antipodal-closed. So the named
  statement `ParsevalCensusResultantBound 5` is false, kernel-checked as
  `not_parsevalCensusResultantBound_five` in `Frontier/WF407W2_L5_s256.lean`.
- At `N = 128` (`m = 8`) the Rudin–Shapiro differential has an exact norm of 425 bits, above
  `2^192`. That refutes the resultant bound at s = 256. A large norm alone does not exhibit a
  prime `p > 2^192` with a collision at a selected root, so `ParsevalCensusResultantBound 8` is
  neither proved nor refuted. It stays an open hypothesis with no valid proof route currently
  known.

The correct Parseval/AM–GM bound is `|Res| ≤ (∑ cᵢ²)^{N/2} ≤ N^{N/2}`. At `|F| < 2^256` that
generic ternary threshold covers s = 128 (`2^192`, for primes `p > 2^192`) but not s = 256
(`2^448`). See `coverage_s128_parsevalCorrect` and `no_coverage_s256_parsevalCorrect`; the
Parseval bound itself is not formalized. The exhaustive probe check below covers only
`m ≤ 4` (`N ≤ 8`), where the bound happens to hold. All census thresholds are LOWER bounds
on `p`. The ceiling `p < 2^256` does not supply them.

The table and TL;DR that follow are kept as the historical claim. Read the `ℓ²` row and every
"unconditional s = 256" statement as superseded by this correction.

## TL;DR (historical, superseded where it conflicts with the correction above)

At a *fixed* prime field `|F| = p < 2^256`, the depth-1 collision/halo census of a dyadic
fold scale `s = 2^m` (half-period `N = s/2 = 2^{m-1}`) is **halo-free** (finite-field census =
char-0 census, no exotic mod-`p` coincidences) once the cyclotomic resultant of the antipodal
differential (`{−1,0,1}`-coeff polynomial of degree `< N`) is `< p`. The frontier of
unconditional coverage at `|F| < 2^256`:

| engine | resultant bound | threshold log₂ | s=64 | s=128 | s=256 | s=512 |
|--------|-----------------|----------------|:----:|:-----:|:-----:|:-----:|
| ℓ¹ (coarse, IN TREE) | `|Res| ≤ N^N` | `N·(m−1)` | 160 ✓ | 384 ✗ | 896 ✗ | 2048 ✗ |
| ℓ² (Parseval halving) | `|Res| ≤ 2^{3N/2}` | `3N/2` | 48 ✓ | 96 ✓ | **192 ✓** | 384 ✗ |

**Result: the Parseval halving extends unconditional census coverage from s = 64 (ℓ¹ ceiling)
to s = 256, and s = 256 is the exact frontier — s = 512 needs 2^384 > 2^256.**

## What is proved vs. what is walled

**Unconditional & axiom-clean (this brick, `Frontier/WF407W2_L5_s256.lean`):**
- `haloFree_l1` — the in-tree ℓ¹ engine re-exposed end-to-end (`= sum_pow_eq_zero_iff_antipodalClosed`).
- `coverage_s64_l1` : `32^32 = 2^160 < 2^256` (s=64 in via ℓ¹).
- `no_coverage_s128_l1` : `2^256 ≤ 64^64 = 2^384` (s=128 out of ℓ¹ reach).
- `coverage_s256_parseval` : `2^{3·128/2} = 2^192 < 2^256` (s=256 in via Parseval).
- `no_coverage_s512_parseval` : `2^256 ≤ 2^{3·256/2} = 2^384` (s=512 out — frontier pinned).
- `haloFree_of_parseval_bound`, `haloFree_s256` — the s=256 consumer chain.

**Walled to one named `Prop` (`ParsevalCensusResultantBound m`):** the assertion that an
arbitrary `{−1,0,1}`-coeff antipodal differential of degree `< N` has cyclotomic resultant
`≤ 2^{3N/2}`. This is the conclusion of the Parseval engine. Its two sub-steps ARE in this
tree — `SidonParsevalNthRoots.parseval_fourTerm_nthRoots` (Parseval over `μ_{2^m}`) and
`SidonParsevalBound.prod_le_of_sum_le` (AM–GM over the `φ(2^m)=N` primitive roots) — but the
full assembly (`HaloFreeThresholdParseval.lean`, the `not_isRoot_of_l2On_parseval_lt` engine of
the #357 worktrees) is **NOT in this checkout** (re-landable). The named Prop packages exactly
that conclusion; never an axiom.

## Numerics (exact, machine-checked)

- `scripts/probes/wf407w2_L5-s256_census_coverage.py` — the full threshold table above.
- `scripts/probes/wf407w2_L5-s256_resultant_verify.py` — EXACT verification of the Parseval
  AM–GM resultant bound `|Res|² ≤ 8^N` over **all** non-antipodal-closed `E ⊆ [0,2^m)` for
  m = 2,3,4: Parseval identity `Σ_{μ}|f|² = 2^m·‖f‖₂²` holds exactly; `|Res|²` rises to
  `2^{22.46}` vs `8^8 = 2^24` at m=4 (never violated for m ≤ 4). This does NOT confirm
  `|Res| ≤ 2^{3N/2}` in general: the bound fails at m = 5 (norm `412876481 > 2^24`) and at m = 8
  (see the correction above).

## Why this is the right tool / why it is orthogonal to the prize

- This is the **fixed-field** census-coverage route (`p > M`), NOT the **polynomial-field**
  Thorner–Zaman route (`p = Θ(n^β)`, conditional on effective PNT-in-APs). It is exactly the A3
  Parseval-threshold line (DISPROOF_LOG O151), which "opened s=64 unconditionally"; this pushes
  the same lever to s=256.
- It is **orthogonal to the δ\* prize core** (which is the worst-case combinatorial / Gauss-
  period wall): a clean landable correctness win, not a prize-closing step. Census coverage at
  larger s certifies that the *char-0 census count* transfers to `F_p` — useful infrastructure
  for the lower-half count, but the prize wall (the true sub-Johnson list count / B-form) is
  untouched.

## Cross-refs

- Engine: `HaloFreeThreshold.lean` (ℓ¹, in tree), `KKH26SumsOfRootsOfUnity.not_isRoot_of_l1On_pow_lt`.
- Parseval substrate: `SidonParsevalBound.lean`, `SidonParsevalNthRoots.lean`.
- TZ poly-field sibling: `Frontier/WF407_B3_s128.lean` (s=128 poly-field, walled to EffectiveTZLowerBound).
- DISPROOF_LOG O148, O151 (the s∈[64,256] pricing + Parseval restoration).

🤖 wf407-w2/L5-s256 · Claude Opus 4.8 · honesty contract held
