# δ* sweep A01 — Height-gate norm bound: re-land + structure-aware no-go (2026-06-14)

**Actionable A01** (`goal407/actionables.json`): *Structure-aware cyclotomic norm bound past
n=32 + re-land HeightGateNormBound.*

**Status: PARTIAL** — the `n ≤ 32` gate is re-landed as a real axiom-clean theorem; the
"structure-aware bound pushes the proved-closed regime past n=32" hope is **refuted for the
worst case** (the prize regime), two independent ways.

## Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/HeightGateNormBound.lean`
  (axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`).
- Probe: `scripts/probes/sweep_A01_normwitness.py`.

## What the gate is

`n = 2^a`, prime `p` with `n ∣ p−1`, `ζ ∈ F_p` a primitive `n`-th root. A *spurious vanishing
set* is `S ⊆ {0..n−1}` with `Σ_{i∈S} ζ^i = 0` in `F_p`. With `g_S = Σ_{i∈S} X^i` the `#S`-term
0/1 indicator polynomial, `N(α) = Res(Φ_n, g_S)` (the field norm of `α = Σ z^i`, `z` complex).
The elementary chain (`CyclotomicNormDefectThreshold.lean`):

- archimedean house: `|N(α)| ≤ (#S)^{φ(n)} ≤ n^{φ(n)} = n^{n/2}`;
- `p`-divisibility: `F_p`-vanishing ⟹ `p ∣ N(α)`;
- char-0 nonvanishing: `α ≠ 0` ⟹ `N(α) ≠ 0`.

⟹ `p ≤ n^{n/2}`. **Contrapositive (the gate):** `p > n^{n/2}` ⟹ every `F_p`-spurious `S`
vanishes in char 0, hence (Lam–Leung for `2`-powers) is *antipodal*.

## What is PROVEN here (n ≤ 32)

- `prime_le_of_Fp_spurious`, `no_Fp_spurious_of_card_pow_lt`: the gate, for the 0/1 indicator
  polynomial, consuming the substrate `prime_le_of_cyclotomic_signed_sum`.
- `gate_fires_8/16/32`: `n^{n/2} < prizePrimeLB n = n·2^128` for `n ∈ {8,16,32}`
  (`8^4=2^12`, `16^8=2^32`, `32^16=2^80`, all `< 2^131..133`).
- `gate_NOT_fires_64`: `prizePrimeLB 64 = 2^134 < 64^32 = 2^192`. Crossover at n=64; vacuous
  n ≥ 128.

The antipodal conclusion uses the named `Prop` `Char0VanishImpliesAntipodal` (the elementary
Lam–Leung structure theorem for `N = 2^a`; Mathlib has no Lam–Leung, so it is a named obligation,
NOT a vacuous placebo — its char-0 input is honestly true).

**Crucially, §4 contains NO `:True` placebo.** The "norm bound rescues the gate" hope is encoded
as a genuine inequality `Prop` `HeightBoundRescuesGate L n p` (every nonzero sum of distinct
`n`-th roots has `Algebra.norm < p`), and `heightBoundRescuesGate_REFUTED` PROVES its negation
for `n = 2^k`, `k ≥ 11` at the prize prime — a real machine-checked refutation, not a named
hypothesis.

## The no-go (why structure-aware ≠ a path past n=32)

The optimistic reading of the n=128 slack ("realized ~2^131 ≪ house ~2^192") fails for the
worst case.

1. **Exact block witness** (`block_sum_norm`, `block_norm_exceeds_prize`, axiom-clean): the
   explicit *non-antipodal* block `S = {0,…,n/2−1}` has the EXACT realized norm
   `N(Σ_{i<n/2} ζ^i) = 2^{n/2−1}` (mechanism: `B·(ζ−1) = ζ^{n/2}−1 = −2`, `N(ζ−1)=Φ_{2^k}(1)=2`,
   `N(−2) = (−2)^{φ(n)} = 2^{n/2}`). This exceeds any fixed prize prime for `n ≥ 512`
   (`2^{n/2−1} > 2^{k+128}` proven for `k ≥ 11`), and at the prize point `n = 2^30` it is
   `2^{2^29−1}` ≫ `p ~ 2^158`. The gate must control `max_S |N(α)|`; the realized worst-case
   norm is unbounded in `n`, so NO norm bound (however structure-aware) keeps the gate alive
   past the elementary `n ≤ 32`.

2. **Numerical straddle** (probe): random non-antipodal `56`-subsets at `n = 128` have realized
   `log₂|N|` over `[117.6, 147.1]`, **median 2^135.8** — straddling the prize prime `~2^135`.
   `|N(α)| < p` is already FALSE for a large fraction of non-antipodal `S` at n=128. (Note: the
   contiguous block `0..55` gives a degenerate `|N|=2^7` because `g=(X^56−1)/(X−1)` nearly
   divides `Φ_128`; the *antipodal-free random* sets are the honest worst case.)

This also corrects the actionable's optimistic "~2^61 slack ⟹ push past n=32": the slack vs the
`(#S)^{φ(n)}` house bound is in fact much larger (~2^100+), but it is *irrelevant* because the
worst-case realized norm itself blows past `p`.

## Verdict

The height/norm route is a **genuine but bounded** advance: it closes the small-n shadow
(`n ≤ 32`) of the prize as a real theorem and Lean-pins exactly where (`n = 64` crossover) and
why (`max_S |N| = 2^{n/2−1} ≥ p`) it stops. It does **not** scale to the prize point
`n = 2^30`; the open prize wall remains the sub-√q Paley/Gauss character-sum object
(`B = max_{b≠0}|η_b|`), which the norm route does not touch. No closure claimed.

## Cross-refs

- substrate: `Frontier/CyclotomicNormDefectThreshold.lean` (the resultant chain).
- prior scratch: `Frontier/_BlockSumNormNoGo.lean` (same block witness; had a Mathlib-drift
  `Algebra.norm_algebraMap` rewrite bug at the `N(−2)` step — fixed here via an explicit `hkey`
  step `Algebra.norm ℚ (−2:L) = (−2)^{Module.finrank ℚ L}`).
- #407 comments 2026-06-14T21:00:59Z (gate proved for n≤32) and 21:11:30Z (FpVanishingBridge:
  abundant spurious vanishing at large n, `|N| ~ n^{n/4}`).
