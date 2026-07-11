# The census face of δ*: complete dossier (2026-07-11)

One-page index of the census/descent programme (24 landings, one session, all axiom-clean,
branch `research/proximity-prize`, coordination #505 → #466). Read this before touching the
face.

## The theorem chain (all unconditional unless marked)

| Layer | File | Content |
|---|---|---|
| Assembly | `_G89AllDepthWickAssembly` | all-depth Wick assembly, split budget caps |
| Semantics | `_G95CardinalityDeepCapNoGo` | pigeonhole floor `#A^2r ≤ q·E_r`; raw counting provably insufficient — 1/p weighting mandatory; `depthFiber` partition |
| Weld | `_G96DepthMomentWeld` | `rEnergy = Σ depthFiber`; centered per-depth consumer for `DCEnergyBound` |
| Bridge | `_G97RelativizedSectorBound` | depth invariant under value maps; true fibers obey counted envelopes; shallow discharge |
| Descent | `_G121DescentMatchingIdentity`, `_G123TriangularMomentLadder` | exact cross-rung identities: m-th matching moment = `(r)_m²·#A^m·E_{r−m}`, unconditionally ≥ 0; row m blind to depths > r−m |
| LP | `_G124MomentLPDepthConstraints`, `_G127MomentLPDual` | linear triangular constraints on the census; Farkas dual = mechanical no-go generator |
| Isolation | `_G125DisjointSectorIsolation` | `E_r ≤ fiber_rr + explicit lower-rung descent` |
| Gates | `_G126DisjointCensusGate` | `q·(census + overhead) ≤ q·Wick + DC-mass ⟹ DCEnergyBound` |
| Budgets | `_G128…`, `_G129…`, `_G130…`, `_G131…`, `_G132…` | descent overhead ≤ half DC mass at every rung 11–110 (four uniform induction gates replace ~100 kernel checks) |
| **Tower** | `_G133CensusTower` | strong induction: census family (11–110) + anchors (≤10) ⟹ `DCShape`/`DCEnergyBound` at ALL rungs ≤ 110 |
| Pins | `_G134ProductionCrossoverPin` | bump at rungs 5–6 = kernel fact; in-tree rung-2 anchor does NOT cover production (Sidon threshold fails astronomically) |
| End-to-end | `_G135CensusToSupBound` | census family + anchors ⟹ `‖η_b‖^220 ≤ q·219!!·n^110` (M ≤ ~2^19.7) — conditional |

## The wall (the only open objects on this face)

1. **Production anchors, rungs 2–10** (`DCShape F G t` at #G = 2^30, certified primes):
   bump at rungs 5–6 (kernel fact); prime-individual arithmetic (the (64,16778497,5)
   failure is prime-exceptional — autopsy); zero in-tree coverage (G134 audit).
   Heuristics favorable (expected nontrivial quadruples ≈ 2^-68 at rung 2). BGK-face.
2. **Deep census family, rungs 11–110**: `2·q·depthFiber G t t ≤ 2·q·Wick_t + n^{2t}`.
   Zero evidence against; passes 28/28 accessible cells; far from all bumps.

## Empirics (all exact-integer, reproducible)

- `probe_466_depth_anomaly_census.py`: per-depth anomalies; odd-nonpos law at n ≤ 16,
  REFUTED at n = 32 (G106) — uniform laws dead.
- `probe_466_anchor_regime_scan.py`: the crossover bump; ratios graze 1 at each regime's
  crossover; e=4/t=5 across n: 0.51 → 1.01 → 0.93 (no monotone growth).
- Counterexample autopsy: disjoint census healthy (0.09), failure = crossover descent.

## For other lanes

- HBK/cube-root, ℤ-lift: the anchor list above is your consumption target; anchor t=5 at
  production is `q·E_5 ≤ 945·q·n^5 + n^10`, n = q^0.19.
- Orbit-class/S₀ (ex-#509): `depthFiber G t t` is the kernel-mass census object; both routes
  meet at `DCEnergyBound`.
- Counterexample hunters: `census_claim_refuted` (G127) mechanizes refutations; test
  candidates against the census shape first.
