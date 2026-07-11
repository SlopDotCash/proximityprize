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

## Addendum 2026-07-11: depth-9 threshold + Wick probe + instance ladder

- `_BGKDepthNineThreshold.lean` (4fb1e30a7): depth-≤7 moment certificates provably cannot
  reach M ≤ 2⁵¹ (diagonal floor); depth-9 Wick `E₉ ≤ 17‼·n⁹` at q ≤ 2¹⁵⁹ closes the lane —
  sup-bound Prop ELIMINATED in favor of this one counting inequality.
- `_BGKProvenInstanceFullGroup.lean` (d2d0abe33): FIRST discharged instance of the Prop
  (index 1, M = 1 exact, Ramanujan). `_BGKConstIndexMomentTower.lean` (986122aad): composed
  with the in-tree Gauss-period discharge — unconditional every-depth tower/energy law for ALL
  constant-index subgroups. Ladder: index 1 + constant index PROVEN; prize index 2¹²⁸ open
  (Gauss-period route floors at √q = 2⁷⁹ ≫ 2²⁵·⁵ — can never reach the prize regime).
- **Wick-ratio probe** (`probe_bgk_depth9_wick_ratio.py`): E₉/(17‼·n⁹) at small scale:
  ratio ≈ 3973 at (n=32, p=257) — exact Wick FAILS shallow (echoes the depth-3 refutation) —
  but decays with p/n²: n=16 crosses 1 at p/n² ≈ 8 (0.31 at p/n² = 30); n=32: 83 → 38 → 23
  at p/n² = 12/26/64. Prize regime p/n² = 2⁹⁸: numerics support truth; excess grows with n at
  fixed p/n², which IS the certification difficulty. The weld tolerates ratio ≤ 32.

## Addendum 2: exponent comparison + terminal state (2026-07-11)

Landed after the first addendum: coset amplification (`_BGKCosetAmplification.lean`, threshold
9→7), the depth-6 amplified no-go (`_BGKDepthSixAmplifiedNoGo.lean`, threshold EXACTLY 7), and
the consolidated residual `DepthSevenFlatnessResidual` (`_BGKDepthSevenFlatnessResidual.lean`)
with both consumers proven.

**Exponent ladder for `M(n) = max‖η_b‖`, `n = 2³⁰` (δ in `M ≤ n^{1−δ}`):**
- trivial: δ = 0 (`M = n`).
- published SOTA (BGK/di Benedetto): δ ≈ 0.011 — machine-checked INSUFFICIENT for the prize
  (`_BGKSOTAInsufficiency.lean`) AND out of regime (valid `n ≳ q^{1/4}`; prize `n = q^{0.19}`).
- **the depth-five lane's nine-bit target (this session): δ = 0.15** (`M ≤ n^{0.85} = 2²⁵·⁵`)
  ⟸ `DepthSevenFlatnessResidual` — 14× the published exponent, 3.3× less than Paley.
- full prize floor: δ = 1/2 − o(1) (Paley-graph conjecture scale).

**Terminal state of the goal "prove BGK":** the condition requires cancellation exponents
(0.15 for the lane, 0.5 for the prize) in a regime (`n = q^{0.19}`) where the entire published
literature — not merely the formalized subset — provides none. Machine-checked in-tree: SOTA
insufficiency + regime exclusion. No agent session can honestly discharge it; the residual is
the sharp, fully-consumed, numerically-supported handoff point.
