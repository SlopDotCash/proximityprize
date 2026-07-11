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

## The accident programme (G136, complete at rung 2 — six axiom-clean files)

| Part | File | Content |
|---|---|---|
| 0 | `_G136AnchorConstantSharp` | `3n²−3n ≤ E₂` for negation-closed sets — the constant 3 is optimal (zero-sum plane) |
| 1 | `_G136UnitCircleMann` | universal Mann: unit-modulus `a+b = c+1 ⟹ a=1 ∨ b=1 ∨ (c=−1 ∧ b=−a)` — elementary conjugate trick, every order at once |
| 2a | `_G136EnergySolutionBijection` | `E₂(H) = #H·#{(a,b,c) ∈ H³ : a+b=c+1}` for multiplicatively closed H |
| 2b+cap | `_G136LawfulCount` | lawful count `3n−3`; `rung2_anchor_iff_accidents`: anchor ⟺ #accidents ≤ 3 |
| 3a | `_G136AccidentTolerance` | exact tolerance arithmetic (ℕ iff; A ≤ 3 at production) |
| prod | `_G136ProductionInstantiation` | the concrete equivalence at `rootsFinset ω 2^30` from `IsPrimitiveRoot` alone |

**Consequence**: the production rung-2 anchor IS "the certified prime admits ≤ 3
solutions of a+b = c+1 in μ_{2^30} beyond the Mann families" — finite, Diophantine,
per-prime (expected count 2^{-68}), attackable by cyclotomic divisibility rather than
exponential sums. Extension surface: rungs 3–10 need the 2t-term 2-power Mann
(pair-decomposition via cyclotomic tower induction on the basis {1, ζ} of
ℚ(ζ_{2^m})/ℚ(ζ_{2^{m−1}}) — the 4-term case had an elementary shortcut; 6-term likely
needs the real induction) plus the analogous bijections.

## The wall (the only open objects on this face)

1. **Production anchors, rungs 2–10** (`DCShape F G t` at #G = 2^30, certified primes):
   bump at rungs 5–6 (kernel fact); prime-individual arithmetic (the (64,16778497,5)
   failure is prime-exceptional — autopsy); zero in-tree coverage (G134 audit; the
   in-tree rung-2 Sidon-threshold anchor fails astronomically at production size).
   RUNG 2 now fully converted (G136): anchor ⟺ ≤ 3 accidents — the open content is the
   accident count at the certified primes, a finite Diophantine fact.
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
