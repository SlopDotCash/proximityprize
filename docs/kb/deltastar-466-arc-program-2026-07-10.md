# The Arc Program (#466, 2026-07-10): δ* ⟺ one small-difference statement, machine-checked on every side

**Status:** consolidation note for the ten-lane arc program landed 2026-07-10 (Fable session
`013QaNxgRNS8yvBSCn6934As`, with concurrent-session integrations). CORE OPEN / ON-BGK.
All Lean files in `ArkLib/Data/CodingTheory/ProximityGap/Frontier/`, all theorems exactly
`[propext, Classical.choice, Quot.sound]`, all real locked builds.

## 1. The endpoint (what a next agent should know first)

The δ*-side prize bound `M = sup_b ‖η_b‖ = O(√(n log q))` is now **machine-check-equivalent**
(consumers formal in both directions, both norms, explicit constants) to ONE classical
statement:

> **The small-difference certificate.** For every coset `C = b·μ_n` and window `W = p/K`,
> `K ≈ √(2πn/log q)`:
> `#{(u,z) ∈ C² : u ≠ z, u−z ∈ Strip(W)} ≤ n²·(2W/p)·O(1) + n·polylog(q)`,
> where `Strip(W) = {w : val w ≤ W ∨ val w ≥ p−W}` (signed window).

Equivalently (sup form): every arc occupancy of every dilate is within `ε ≍ log q` of uniform.
This is the Cilleruelo–Garaev small-difference / short-interval-concentration object verbatim,
for dilations by the shifted subgroup `μ_n − 1`. Known technology (CG/BGK/HBK) reaches only
`|H| > p^{1/3}`-type regimes (β < 3); the prize regime β ≫ 3 is the wall.

## 2. The lane inventory

| lane | file | content |
|------|------|---------|
| G80 | `_G80ArcOscillationWeld.lean` | chord-arc bound; grouped oscillation `≤ #pts·wid`; equally-spaced centers sum to 0 exactly (B=0); abstract arc-increment extraction |
| G80Z | `_G80ZArcArithmeticInstantiation.lean` | `arcIndex = ⌊K·val/p⌋` on ZMod p; floor-width `≤ 2π/K` by construction; **forward**: `‖charSum‖ ≥ A ⟹ arc deviation ≥ (A − #S·2π/K)/K` |
| G80Y | `_G80YArcEquivalenceConverse.lean` | **converse**: arc ε-uniformity ⟹ `‖charSum‖ ≤ K·ε + #S·2π/K` (recentring legal via B=0) |
| G80X | `_G80XArcCertificateEndpoint.lean` | formal AM-GM over K: `‖charSum‖ ≤ 2√(2π·#S·ε) + ε`; strength pin `ε ≍ log q` (no weaker suffices — G80Z; no stronger needed) |
| G80W | `_G80WArcPairCountIdentity.lean` | same-arc pair count = `Σ_j n_j²` exact; ℓ² discrepancy = pair excess; pair-form consumer `‖charSum‖ ≤ √K√Δ + #S·2π/K` (√K-lossy — sup form is binding) |
| G80V | `_G80VArcDilationCoincidenceReduction.lean` | grand identity `Σ_b pairCount(bH) = |H|·Σ_d R(d)`, `R(d)` a Fourier-free floor object; `R(1) = p−1`; coset invariance (sup over Gauss-period cosets); **mean is a theorem, max is the prize** (max/mean measured 1.4–1.8) |
| G80T | probe `probe_466_g80t_arc_lattice_height_weld.py` | **REFUTED**: unsigned lattice-height (λ₁) predictors for R anomalies — negative correlation; anomaly is DIRECTIONAL (positive small ratios near diagonal) |
| G80S | `_G80SDirectionalStripReduction.lean` | same-arc ⟹ difference in `Strip(p/K)` (the signed object G80T demanded); `R(d) ≤ StripCount(d−1)`; exact all-c strip average; pair certificate ⟹ shifted-subgroup strip concentration |
| G80Q | `_G80QSmallDifferencePairForm.lean` | bijection `(d,z) ↦ (dz,z)` collapses the ratio sum: **terminal form** `pairCount(bH) ≤ |H| + smallDiffPairs(bH, p/K)` |
| G80P | `_G80PReducedFractionRigidity.lean` | integer rigidity below √p (congruent cross-products equal); coset-interval ↪ small-ratio census ρ_H(W); **regime disjointness**: rigidity window K > √p vs saddle K ≈ √(2πn/log q) overlap only at β ≤ 1 — the CG p^{1/3} barrier derived in-chain |

Supporting session bricks: OC-EQUI (`_OCGaloisEmbeddingEquidistribution.lean` — Galois
equidistribution kills the distinct-embedding seam), OC-TAIL (`_OCStackingTailCensusCeiling.lean`
— cross-prime finiteness of stacked violators).

## 3. The three formalized failure modes (why nothing known applies)

1. **Phase-blindness** (barrier map, G77): L²/energy functionals can't see `arg`; the signed
   route is a Fourier gauge.
2. **Archimedean-blindness** (F3 fence; G80T): unsigned valuation/height/λ₁ functionals can't
   see the DIRECTION of small-ratio approach; R anomalies are directional.
3. **Integer-liftability** (G80P): rational/height rigidity works only at K > √p, regime-
   disjoint from the prize saddle (overlap requires β ≤ 1).

A viable certificate must be: phase-sensitive, direction-sensitive, genuinely modular. The
one route not excluded by these three fences: **modular-native occupancy arguments** — e.g.
Stepanov auxiliary polynomials evaluated against arc structure without integer lifting
(the in-tree unconditional Stepanov engine `legendreCubicHasseC_unconditional` is the proof
of concept that Hasse-strength bounds are reachable without Weil).

## 4. What NOT to redo

- Do not re-derive consumers: every ε/Δ/ρ-form partial certificate already has a zero-slack
  formal pipeline to δ* (this program).
- Do not retry unsigned height/λ₁ predictors (G80T), integer-lifting below the saddle (G80P),
  flat chaining (G70), multi-shift SV (G73), signed-route pairings (G77), per-tuple Weil at
  depth (r18), Fourier-derived spreadness (G78 circularity).
- The b-averaged and coset-averaged forms are THEOREMS (G80V, G80S mean); only the max/sup
  over the `(p−1)/n` cosets is open.

## 5. Addendum (same day): the unconditional interval milestone (G80O → G80N → G80M)

| lane | file | content |
|------|------|---------|
| G80O | `_G80OProductDivisorInterval.lean` | CG product trick: `T(W)² ≤ D·n` below √p; fiber ↪ divisors; input = Nat-only `DivisorBound` |
| G80N | `_G80NDivisorFourthPowerBound.lean` | **`d(y)⁴ ≤ 19680·y` proven** (per-prime constants 41/10/4/3/2/2; first machine-checked constant-exponent divisor bound) |
| G80M | `_G80MUnconditionalIntervalBound.lean` | 🏁 **`T(W)⁸ ≤ 19680·W²·n⁴`, zero hypotheses** — `T(W) = O(√n·W^{1/4})`, e.g. `T(n) = O(n^{3/4})`; first machine-checked nontrivial subgroup-interval concentration bound |

Honest ladder note: the crude k-fold generalization (fiber ≤ `d(y)^{k-1}`) gives WORSE
exponents than k = 2 (e.g. `n^{5/6}` at k = 3); the genuine CG/BGK bootstrap replaces the
crude fiber bound with multiplicative-energy control — exactly the open content. Do not land
the crude ladder; the prize-ward continuation is energy-refined fibers, or the saddle-side
certificate directly.
