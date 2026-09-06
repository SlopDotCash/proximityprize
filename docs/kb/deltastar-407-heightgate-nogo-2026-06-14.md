# #407 — the height-gate "structure-aware norm bound" lever is a NO-GO for the prize (2026-06-14)

**Context.** Burn-down of the full 163-comment thread on #407. The audit confirmed the
consolidated picture: ONE open-irreducible core (thin-subgroup BGK / Paley √-cancellation,
~20 equivalent faces), everything else PROVEN / REFUTED / REDUCE-TO-WALL. The single
*actionable* open lever flagged in the thread (c.157/c.159) was the **height-gate**:
push the proved-closed regime of `NoSpuriousVanishing` past `n ≤ 32` with a "structure-aware
(resultant/Newton-polygon) norm bound" replacing the loose house bound `(#S)^{φ(n)} = n^{n/2}`.

## The gate and what it needs

`HeightGateNormBound.gate_2power_antipodal` certifies
`p ∣ N_{ℚ(ζ_n)/ℚ}(Σ_{i∈S} ζ^i) ⟹ S` antipodal
**whenever** `|N(Σ_S)| < p` for every non-antipodal `S ⊆ range(n)`. So the gate closes at
level `n` ⟺ `max_{non-antipodal S} |N(Σ_S)| < p(n)`, where the prize prime `p(n) = n·2^128`.

## Verdict: NO-GO for the prize (small-n shadow only)

1. **Exact block norm (PROVEN, axiom-clean).** The explicit non-antipodal block
   `S = {0,…,n/2−1}` has `Σ = (ζ^{n/2}−1)/(ζ−1) = −2/(ζ−1)`, so with `N(ζ−1)=Φ_{2^a}(1)=2`
   and `N(−2)=(−2)^{φ(n)}=2^{n/2}`:
   > `N(Σ_{i<n/2} ζ^i) = 2^{n/2−1}`.
   Lean: `ArkLib/.../Frontier/BlockSumNormNoGo.lean` (`block_sum_norm`, `block_sum_norm_ge_prize`;
   `[propext, Classical.choice, Quot.sound]`). This single explicit `S` already has
   `|N| = 2^{n/2−1} ≥ p` for all `n ≥ 512`, and `2^{2^{29}−1} ≫ p ~ 2^{158}` at the prize
   point `n = 2^{30}` — a ~5.4×10⁸-bit violation. No norm bound can make `|N| < p` there.

2. **Worst-case `max_S |N|` IS the wall.** Hill-climb over non-antipodal `S` gives best-found
   vs the AM-GM/Parseval value `(#S)^{φ(n)/2} = (#S)^{n/4}`: 11.2/12.7, 31.1/32, 78.8/80,
   189.6/192 (log₂, n=16/32/64/128). So `max_S |N| ≈ (#S)^{n/4}`, crossing `p ~ 2^128` already
   at `n ≈ 128`. Bounding it below `p` for worst-case `S` = cyclotomic house-maximization =
   thin-subgroup BGK.

**Net.** An exact-norm gate closes only to `n ≈ 128–256`; the prize point `n = 2^{30}` is
unreachable by *any* norm bound, since `max_S |N|` grows super-exponentially (`≈(#S)^{n/4}`;
exact `2^{n/2−1}` on the block) while the prize prime stays `~2^128`. The gate's `n ≤ 32`
closure (§5.0) stands as a genuine small-n shadow; pushing it further is the BGK core itself.

## Also verified (c.150/c.151, load-bearing)

Short **non-antipodal ±1 excess relations** exist at structured primes
(`p=97,n=16: g⁰+g¹−g³−g⁵≡0`; `p=12289,n=64: g⁰−g¹−g²−g³−g⁷−g²⁵≡0`), so `W(n,p)=O(1)`
(not `≥ 2⌈log m⌉`) and `GaussianEnergyBound` (`E_r ≤ Wick` at `r≈log m`) is FALSE at
prize-regime structured primes. The moment-certificate route stays REFUTED; `δ*=floor`,
though empirically true, needs a non-moment, thinness-essential argument.

## Files / repro
- `Research/ProximityPrize/Frontier/BlockSumNormNoGo.lean` (axiom-clean)
- `scripts/probes/probe_heightgate_nogo_407.py`
- `scripts/probes/probe_short_excess_relation_407.py`
- `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` (two new entries, 2026-06-14)
- issue comment: lalalune/ArkLib#407 (2026-06-14 burn-down)

**Bottom line.** The prize remains OPEN. Every comment finding now has a verdict; the one
irreducible core is the 25-year thin-subgroup BGK/Paley √-cancellation wall, and the last
flagged lever (structure-aware norm bound) is a proven no-go for the prize.
