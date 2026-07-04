# #466 Round 12 (LANE F): the FRONTAL assault on the wall `W_r ≤ n^{2r}/p` — REDUCES-TO-WALL at an exact-finite step (2026-07-04)

**Verdict: REDUCES-TO-WALL**, with the exact step pinned, plus one genuinely-new axiom-clean
small-rung fact (the gate collapse). This round did NOT seek a new escape route (the no-go
cartography is complete after 11 rounds); it made a frontal attempt ON the wall itself via the
norm/conjugate-count decomposition, and terminated cleanly at the wall with the precise reason the
sole unconditional tool is vacuous at the prize.

## The object

The wall (cleanest form, from W1 `_WallBetaPlusOneLocalization`): `W_r ≤ n^{2r}/p` at `r = β+1`,
where `W_r = E_r^{(p)} − E_∞ ≥ 0` is the **wraparound count**: the number of `(h₁…h_{2r}) ∈ μ_n^{2r}`
with `Σ εᵢhᵢ ≡ 0 (mod p)` minus the char-0 count. Equivalently, `α = Σ εᵢhᵢ` is a **nonzero** element
of the degree-1 prime `𝔭 | p` — a sparse `±1` sum of `≤ 2r` `n`-th roots of unity whose algebraic
norm `N(α)` is a nonzero multiple of `p`.

## What the frontal assault found

### (1) The norm-divisibility reframe is an EXACT identity (probe-validated)

`probe_466r12_frontal.py` (n=8, exact algebraic norms via the `φ(n)=4` conjugates): the count of
sparse `±1` root sums with `p | N(α)`, `N(α) ≠ 0` equals `W_r` exactly at r=2,3. Since `p` splits
completely, `α ≡ 0 (mod 𝔭)` with `α ≠ 0` ⟺ `p | N(α)`. The reframe is a genuine identity, not an
approximation — the wall IS "sparse `±1` root sums rarely have `p | N(α)`."

### (2) PROVEN small-rung: the conjugate-count gate `(2r)^{n/2} < p ⟹ W_r = 0`

The in-tree `RootSumNorm.abs_norm_sum_rootsOfUnity_le` gives `|N(α)| ≤ (2r)^{φ(n)} = (2r)^{n/2}`
(each conjugate has `|σ(α)| ≤ 2r`; `φ(2^μ) = n/2`). So a nonzero `α` with `(2r)^{n/2} < p` has
`|N(α)| < p`, hence `p ∤ N(α)`, hence NO wraparound: **`W_r = 0` exactly** (the in-tree
`_AvND_NormDiameterThreshold.no_wraparound_at_depth`). Probe-confirmed SOUND: the empirical onset
`r_0 = min{r : W_r > 0}` sits at or just above the gate reach `r_gate = ⌊½·p^{2/n}⌋`:

| n | r_gate | onset r_0 | slack | W_r/(n^{2r}/p) at post-onset rungs |
|---|---|---|---|---|
| 8 | 4 | 8 | 4 | 0 through r=7 (gate not tight but W stays 0) |
| 16 | 2 | 5 | 3 | 0.007 / 0.096 / 0.144 (three primes, r=5) |
| 32 | 1 | 4–5 | 3–4 | 0.615 (r=4) |

The wall HOLDS at every measured post-onset rung (max ratio 0.615 < 1).

### (3) The GATE COLLAPSE — the new axiom-clean content

At the prize `p = n^β = n^4`, `p^{2/n} = n^{8/n} → 1`, so the provable reach collapses:
`r_gate = ⌊½·n^{8/n}⌋`: n=8→4, n=16→2, n=32→1, **n≥64→0**. Brick
`Frontier/_FrontalConjugateGateCollapse.lean` (axiom-clean, 4 decls, real-build binders explicit):

- `two_pow_half_gt_n_pow_four`: `n^4 < 2^{n/2}` for even `n ≥ 64` (the even crossover is n=44; for
  dyadic n it fails at 32 and holds at 64: `64^4 = 16777216 < 4294967296 = 2^32`).
- `gate_vacuous_at_prize`: for `n ≥ 64` and EVERY `r ≥ 1`, `(2r)^{n/2} ≥ n^4` — the gate `(2r)^{n/2}
  < p` fails at every rung, so the norm bound certifies `W_r = 0` at NO rung on the prize surface.
- `gate_vacuous_n64_r1`: the concrete `n=64, r=1` witness.

This **sharpens** the prior asymptotic-in-p `_AvND_NormDiameterThreshold.threshold_lt_saddle` (which
compared `r_gate` to the saddle `r* ~ log p`) to an EXACT FINITE prize-point boundary: past the gate
already at the very first rung `r = 1` once `n ≥ 64`. At the prize scale `n = 2^30` the
conjugate-count method is vacuous on the entire open surface `[1, β+1]`.

## The exact step of the reduction

For any `(n, p, r)`: EITHER the gate closes it (`(2r)^{n/2} < p ⟹ W_r = 0`), OR one is in the
post-gate region where the sole open content is `WallBetaPlusOne.WraparoundBelowDC` (`p·W_r ≤
n^{2r}`). `gate_vacuous_at_prize` shows the first disjunct is **unreachable** at the prize for every
`r ≥ 1`. So the wall is exactly the second, and a magnitude-only argument provably cannot enter it:
the conjugate product `|N| = ∏|σ|` can exceed `p` even when no single `|σ| ≤ 2r` is large, so
bounding the COUNT of large-norm `p`-divisible sparse sums requires inter-conjugate **phase
cancellation** = BGK/Paley. This is the same wall named by dossier §9 (conjugate-count no-go) and W1,
now reached from the norm side with the exact-finite reason the unconditional tool is vacuous.

## Honest scope

No wall closure; no new named decomposition target beyond the standing `WraparoundBelowDC`. The
value is (a) the exact-finite quantification of *why* the norm/conjugate-count method dies precisely
at the prize (vacuous at r=1 for n≥64, not merely "eventually below the saddle"), and (b) the
machine-checked confirmation that the reframe `W_r = norm-divisibility count` is exact. **CORE OPEN,
ON-BGK.**

## Files

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FrontalConjugateGateCollapse.lean` (axiom-clean)
- `scripts/probes/probe_466r12_frontal.py` → `_out_466r12_frontal.txt`
- `scripts/probes/probe_466r12_gate.py` → `_out_466r12_gate.txt`
- DISPROOF tag `466-r12-frontal-conjugate-gate-collapse`
