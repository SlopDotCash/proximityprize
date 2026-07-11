# δ* #466 — Cross-cone bridge: the P1 swarm's moment layer IS the B-side lag machinery (formal identity bridge, first cross-cone import); the OPEN layers are a calibrated NON-bridge (2026-07-11)

**Lane:** cross-cone (P1 rate-quarter × B-side R297–R309 arc) — ninth round of the
2026-07-11 session.  First formal bridge attempt between the campaign's two cones.
**Probe:** `scripts/probes/probe_rate_quarter_p1_cross_cone_bridge.py` (identities
exact at `M = 257`, calibration exact at prize constants).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterCrossConeBridge.lean`
(pg-iterate OK 11s; 6 theorems; full axiom lists read manually via `lake env lean`:
all exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx, no warnings).
Build note: `_R309TowerRungFour` olean built once via lake-locked — **the first file
importing both cones** (`_R309TowerRungFour` + `_P1RateQuarterPencilHarvestCap`).

## The analysis (exact, on paper first)

**P1 swarm side, rewritten exactly.**  Swarm riders on a direction `w` against the
stack `(u₁, −D)` are FIBERS of the ratio map `ρ_w = (u₁ − w)/D`: rider scalar `s`
collects `h(s) = #{x ∈ X : ρ_w(x) = s}` votes.  The fiber-count function's DFT is
the **incomplete exponential sum** `ĥ(a) = Σ_{x∈X} ψ(a·ρ(x))` — polynomial/rational
arguments over the multiplicative-2-group-structured domain: the exact BGK object.

**B-side.**  The lag sums `Σ_j J_{j+t}J̄_j` are ℤ/m-autocorrelations of a family of
COMPLETE character sums over `F_q`, consumed through `hatF`/`autocorr` identities.

## Outcome (ii): the partial bridge — REAL and now formal

Both cones' second/fourth-moment layers are instances of ONE generic identity
family (moments of `ĥ` for a nonnegative arithmetic weight `h`):

* `hatF_fiberCount` — `ĥ(a) = Σ_{x∈X} ψ(a·ρx)`: the P1 obstruction object in the
  B-side's DFT vocabulary (kernel).
* `swarm_secondMoment_bridge` — `Σ_a‖ĥ‖² = M·(fiber energy)`: `hatF_parseval` at
  the swarm weight.
* **`swarm_fourthMoment_lag_bridge`** — `Σ_a‖ĥ‖⁴ = M·Σ_t‖autocorr h (t)‖²`:
  LITERALLY the B-side's `fourthMoment_eq_lag_energy` at `f = fiberCount`.  The P1
  swarm moment layer and the Jacobi-ladder lag machinery are the same theorem with
  different weights (B-side: `h` = Jacobi ladder on ℤ/m; P1: `h` = fiber counts on
  `ZMod P`).
* `swarm_lag_bridge_at_prize` — the instance at the literal prize modulus
  (`F = ZMod P`), valid for any domain subset and ratio map (in particular
  `X ⊆ μ_{2^30}`, `ρ_w = (u₁−w)/D`).

## Outcome (iii): the calibrated NON-bridge at the open layers

1. **Completeness ratio** (`swarm_sub_burgess`, kernel): the swarm's incomplete
   sums have length `N = 2^30` over `F_P` with `N⁴ < P < N⁶`, i.e.
   `θ = log_P N ≈ 0.19 < 1/4` — strictly BELOW the Burgess range; only
   subgroup-specific (BGK) methods exist there.  The B-side's `J_j` are COMPLETE
   (ratio 1; individually `√q` by Weil).
2. **Moment depth**: B-side open inputs are fixed-depth family averages
   (`OffZeroLagBound ~ √m·q` at depth 1; `OffZeroQuadLagBound ~ m^{3/2}q²` at
   depth 2 / r = 4); the swarm needs a LIST-level statement — the exact second
   moment gives Chebyshev counts `~ P^{k−2}`, astronomically above the budget.
   Kernel calibration `swarm_single_map_chebyshev_scale`: the single-ratio-map
   Chebyshev scale `(k−1)N/a²` at the pair-pencil floor `a = 2T−N` is exactly
   bracketed in `[N(k−1)/24a², N(k−1)/23a²]` → `23` — it counts heavy fibers of
   ONE map, not the number of swarm directions.
3. A formal reduction would have to transport bounds across the completeness
   ratio (`2^{−128} ↔ 1`) AND the depth (`list ↔ r = 4`); character-sum
   technology does neither.  **The campaign's "one wall" convergence is
   CLASS-level (one exponential-sum master family), not reduction-level.**

## Bonus finding (named next target, not landed)

The fiber-vocabulary rewrite exposes a potential REFINEMENT of the stall ledger:
per-direction rider counts obey a fiber-Chebyshev `#{s : fiber ≥ b} ≤ (k−1)F/b²`
(each fiber ≤ k−1 as root counts), which beats the derecursion's vote bound
`F/b` exactly when `b = T − A > k − 1` — i.e. on the LOW-alignment part of the
stall window.  This does not bound #directions (the wall), but it could shrink
the per-direction ledger in the swarm regime.  Formalizing it needs pool-root
counting (`pool_separation`-style) — flagged for a future round.

## Honesty

Neither `SwarmResidual` nor the B-side lag inputs are discharged or transported —
the bridge is at the (closed) identity layer; the open layers are provably
different objects.  No δ* movement; bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)`
untouched.

## Session status (nine rounds, 2026-07-11)

P1 arc (8 rounds, 68 theorems) + this cross-cone round (6 theorems): 74 kernel
theorems, 7 probes.  Campaign residual map: `SwarmResidual` (P1, sub-Burgess
incomplete-sum list problem on `μ_{2^30}`) ∥ `OffZeroLagBound ∧
OffZeroQuadLagBound` (B-side, complete-sum family moments) — same master family,
different walls, now with the distinction kernel-pinned.
