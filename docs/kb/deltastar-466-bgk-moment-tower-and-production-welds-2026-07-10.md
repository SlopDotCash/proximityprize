# #466 — BGK moment tower + production depth-five welds (2026-07-10)

**Session goal:** "prove BGK". Honest outcome: BGK (`WorstCaseIncompleteSumBound`, the
~25-year-open generalized-Paley-graph sup-bound) is **not** discharged — it cannot be, short of
resolving the open conjecture. What landed instead is the complete formal reduction making the
depth ladder hang off that single named Prop, end to end at the literal prize numbers.

## Landed (all axiom-clean: `propext, Classical.choice, Quot.sound`; real `lake build`)

1. `Frontier/_BGKSupBoundMomentTower.lean` (commit `f5c554cb5`)
   - `offZero_secondMoment`: exact off-zero Parseval `∑_{b≠0}‖η_b‖² = q|G| − |G|²`.
   - `etaMomentTower_of_worstCase`: **the tower** — for every `r ≥ 1`,
     `∑_{b≠0}‖η_b‖^{2r} ≤ M^{r−1}(q|G| − |G|²)`; relaxed form and the `r = 5` tenth-moment
     corollary. One chaining step (`x^r ≤ M^{r−1}x` on `0 ≤ x ≤ M`) + the exact base case.

2. `Frontier/_BGKDepthREnergyLaw.lean` (commit `f5c554cb5`)
   - `moment_eq_card_energy`: **exact depth-`r` Parseval/energy law**
     `∑_b‖η_b‖^{2r} = q·E_r(G)` with `E_r` = ordered `r`-tuple sum-collision census
     (`rEnergy`). Unconditional, pure orthogonality; proved via `Finset.sum_pow'` +
     an inline `addChar_map_sum`. Generalizes the in-tree depth-2 `addEnergy` identity to all
     depths at once.
   - `rEnergy_le_of_worstCase`: the dossier §8 independence form as a theorem modulo BGK:
     `q·E_r ≤ |G|^{2r} + M^{r−1}·q·|G|` for every `r ≥ 1`.

3. `Frontier/_BGKProductionDepthFiveWeld.lean` (commit `9b692408d`)
   - `rEnergy_le_production_ceiling` / `bgk_production_depthFive_weld`: at the literal prize
     instance (`|G| = 2³⁰`, `q ≥ 2¹⁵⁸`; `productionQ_ge` checks the prize field), ANY BGK
     sup-bound `M ≤ 2⁴⁰` (round-30 scale `C·n·log n ≈ 2³⁵`) forces
     `E₅ ≤ 2²³⁵ = productionCollisionCeiling`, hence composed with the kernel-checked G112
     arithmetic `E₅·productionDepthFiveBase ≤ productionWick`. Margin:
     `E₅ ≤ 2¹⁴² + 2¹⁹⁰ ≪ 2²³⁵` (≥ 45 bits of headroom).

4. `Frontier/_BGKInjectiveFiveWeld.lean`
   - `injEnergy_le_rEnergy`: the injective five-tuple census (the ACTUAL G112 production map,
     `productionSource = n.descFactorial 5`) embeds in the ordered energy (pure monotonicity).
   - `bgk_production_injective_weld`: the production envelope transfers to the injective map,
     same hypotheses, same single open input.

## Upshot for the campaign map

The G86/G111/G112 depth-five production socket and, more generally, EVERY finite-depth moment
rung is now formally exactly ONE named inequality away from closed: prove
`WorstCaseIncompleteSumBound ψ G M` at any `M ≤ 2⁴⁰` on the prize subgroup and the depth-five
Wick envelope (both ordered and injective censuses) follows by landed theorems. The converse
caution from `_PrizeFloorOfBGK.lean` stands: the sup-bound feeds the energy/moment lane; the
far-line incidence input (BCHKS 1.12 hyperplane upgrade) remains the second, independent open
input for the δ* floor itself.

## Lean gotchas (recorded for reuse)

- `exponentiation.threshold` defaults to 256: `norm_num` will NOT evaluate `2^300`; raise via
  `set_option exponentiation.threshold 512` (plus `maxRecDepth 8192`) or restructure with
  `pow_mul`/`pow_add`.
- `add_le_add_right h _` can mis-unify on ℝ sums of pow-atoms; `add_le_add h le_rfl` is robust.
- Frontier files importing other Frontier files need the imported module's olean:
  `lake-locked.sh build <Module>` once; `pg-iterate.sh` alone fails on a missing olean.
- The build lock can queue ≥10 min behind concurrent agents; run locked builds in background.
