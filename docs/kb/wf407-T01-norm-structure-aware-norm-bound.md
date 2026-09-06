# wf407 / T01-norm — structure-aware cyclotomic norm bound (§5.0 binding direction)

**Date:** 2026-06-14 · **Thread:** 407-T01 / G1 · **Verdict: PARTIAL** (Landau ℓ² extends the
proved-closed regime by exactly one doubling, `n ≤ 32 → n ≤ 64`; prize `n = 2^30` stays open,
walled by the worst-case `max_S |N|` = the √-cancellation/Paley character-sum object).

## The question

`§5.0` binding direction: the height gate certifies "`p ∣ N(Σ_{i∈S} ζ_n^i) ⟹ S` antipodal" for
every non-antipodal `S ⊆ range n` **iff** `max_{non-antipodal S} |N(α)| < p`, with prize prime
`p ~ n·2^128`. The house (archimedean triangle) bound `|N| ≤ (#S)^{φ(n)} = (#S)^{n/2} ≤ n^{n/2}`
fires only for `n ≤ 32`. The T01 attack asked: does a **structure-aware** bound
(Mahler-measure / Landau ℓ² `M(g) ≤ √(Σ coeff²)`, or Desnanot–Jacobi ratio-of-minors) predict the
realized norm and push the closed regime past `n = 32` (toward `n ≥ 112`)?

## Findings (all EXACT, machine-verified)

### 1. The Landau / Mahler ℓ² ceiling IS the right structure-aware bound — and it is true.

`|N| = ∏_{ω prim} |g_S(ω)| ≤ ‖g_S‖₂^{φ(n)} = (#S)^{φ(n)/2} = (#S)^{n/4}` — a genuine **√-improvement**
over the house exponent `φ(n)`. Verified **EXHAUSTIVELY** (0 violations over all `2^8` and `2^16`
subsets; max ratio of `|N|^{1/φ}` to `√(#S)` is exactly `1.0`).

**Elementary proof chain (verified, `wf407_T01-norm_parseval_route.py`):**
- Parseval (full roots): `Σ_{ω^n=1} |g_S(ω)|² = n·#S` (exact, orthogonality).
- Primitive subset: `Σ_{Φ_n(ω)=0} |g_S(ω)|² ≤ φ(n)·#S` (= `‖g_S‖₂²·φ(n)`; max ratio = 1.0
  exhaustively at `n=8,16`).
- AM–GM (`Real.geom_mean_le_arith_mean`): geo-mean of the `φ(n)` reals `|g_S(ω)|²` ≤ arith-mean
  `≤ #S` ⟹ `|N|² = ∏|g_S(ω)|² ≤ (#S)^{φ(n)}` ⟹ `|N| ≤ (#S)^{φ(n)/2}`.

### 2. The T01 "2^61 slack" premise used a TYPICAL witness, not the worst case.

At `n = 128`, the contiguous block `S = {0,…,55}` realizes only `|N| = 2^7 = 128` (geometric
cancellation — NOT 2^131). The "2^131" figure in `sweep_A01_normwitness.py` was a *random* 56-subset
(median ~2^135.8). But the gate needs `max_S`, not a typical `S`. The **worst-case** hill-climb gives
`max_{non-antipodal S} |N(α)| ≈ 2^189` at `n = 128`, which EXCEEDS `p ~ 2^135` and nearly saturates
the Landau ceiling `n^{n/4} = 2^192`. So the optimistic reading is refuted: there is no exploitable
worst-case slack at `n = 128`.

### 3. Landau extends the gate by EXACTLY one doubling, then dies.

`φ(2^a) = n/2`, Landau exponent `φ(n)/2 = n/4`. Gate fires iff ceiling `< p ~ n·2^128`:

| bound | ceiling at `n` | fires for |
|-------|----------------|-----------|
| house  | `n^{n/2}` | `n ≤ 32` (`32^16 = 2^80 < 2^133`) |
| Landau | `n^{n/4}` | `n ≤ 64` (`64^16 = 2^96 < 2^134`) — **house already FAILED here** (`64^32 = 2^192`) |
| either | — | FAILS `n ≥ 128` (Landau `128^32 = 2^224 > 2^135`; worst-case norm `2^189 > 2^135`) |

The structure-aware lever moves the proved-closed binding direction from `n ≤ 32` → `n ≤ 64`, a
genuine but bounded gain of one doubling. It is `2^25` doublings short of the prize point `n = 2^30`.

## The wall (why it cannot reach the prize)

The worst-case `max_{non-antipodal S} |N(α)| ≈ 2^{(n/4)log₂ n}` (Landau-ceiling-saturating) is
itself the √-cancellation / **generalized-Paley character-sum** object — wall **W2** (additive-energy
√n-loss) / **W4** (moment-method √(log)-short). The block witness `S={0,…,n/2−1}` already has exact
`|N| = 2^{n/2−1}` (`HeightGateNormBound.block_sum_norm`), `2^{2^29−1}` at the prize — astronomically
above any `p`. NO norm bound (Landau, Desnanot–Jacobi, Newton-polygon, or even the EXACT worst-case
norm) keeps the gate alive past `n = 64`. The height/norm route is a small-`n` shadow of the
character-sum wall, as `probe_heightgate_nogo_407.py` and `BlockSumNormNoGo.lean` already established
for the asymptotics; this thread pins the **exact crossover** (`n = 64`) and identifies the operative
structure-aware bound (Landau ℓ², not Desnanot–Jacobi).

## Artifacts

- `Research/ProximityPrize/Frontier/WF407_T01NormLandauCeiling.lean` — axiom-clean
  (`[propext, Classical.choice, Quot.sound]`): `landau_gate_fires_64` (the extension, decidable),
  `house_gate_NOT_fires_64` (house dies one doubling earlier), `landau_gate_NOT_fires_128`,
  `landau_no_go_ge_128` (asymptotic no-go, `a ≥ 7`), `landau_gate_boundary`, and the named Prop
  `LandauNormCeiling` (the ℓ² ceiling, proven elementarily + exhaustively, open in Lean).
- `scripts/probes/wf407_T01-norm_structure_aware.py` — house vs Landau vs realized; worst-case
  climb; Landau ceiling 0/24 violations.
- `scripts/probes/wf407_T01-norm_landau_crossover.py` — exhaustive Landau ceiling (0 viol over
  `2^8`,`2^16`); worst-case crossover (n=64 fires, n=128 fails); exact block norms.
- `scripts/probes/wf407_T01-norm_parseval_route.py` — the Parseval + AM–GM proof structure.

## What remains

- The full `resultant = ∏-over-roots` Lean formalization of `LandauNormCeiling` (multi-lemma on top
  of `CyclotomicNormDefectThreshold.lean` + `Real.geom_mean_le_arith_mean`) is a clean follow-up
  brick, but it does NOT move the prize (the gate dies at `n = 64` regardless).
- The prize core is unchanged: bound `max_{non-antipodal S} |N|` BELOW `n^{n/4}` would require
  beating √-cancellation on the generalized-Paley graph `Cay(F_q, μ_n)` — the W2/W4 wall.
