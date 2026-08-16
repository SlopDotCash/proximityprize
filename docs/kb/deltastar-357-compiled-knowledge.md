# Issue #357 compiled knowledge base — the δ* campaign, distilled by theme

> Provenance: full archive of issue #357 (lalalune/ArkLib, "Exact MCA/proximity-gap threshold
> δ* for smooth-domain Reed–Solomon codes") — the issue body plus all 283 comments
> (2026-06-11 → 2026-06-12), available from the
> [public historical issue](https://github.com/lalalune/ArkLib/issues/357) and repository history.
> This page reorganizes that history
> by theme, not chronology. Every Lean file named below was existence-checked against
> `ArkLib/Data/CodingTheory/ProximityGap/` at compile time of this document (exceptions
> flagged inline). All "axiom-clean" claims mean `#print axioms` reports exactly
> `[propext, Classical.choice, Quot.sound]`, zero `sorry`. Comment references are `cN`
> (= the N-th comment, 0-indexed) with the GitHub comment id in parentheses where load-bearing.

---

## 1. The problem

Throughout: `C := RS[F, L, k]` over a **smooth** evaluation domain `L` (multiplicative
subgroup of size `n = 2^μ`), rate `ρ := k/n` ∈ {1/2, 1/4, 1/8, 1/16}, `|F| < 2^256`,
`k ≤ 2^40`, error threshold `ε* = 2^-128`, distance `d = n − k + 1`, `q = |F|`.

- `ε_mca(C, δ)` is the **mutual-correlated-agreement** error (ABF26 Definition 4.3; in-tree
  `Errors.lean:231`, `mcaEvent` at `:216`): a sup over word stacks `(u₀, u₁)` of the
  fraction of *bad* line points — a point `u₀ + γu₁` is bad when some witness set `S`
  (size ≥ (1−δ)n) carries a codeword for the combined word but admits **no joint
  explanation** of the stack. Hierarchy `ε_pg ≤ ε_ca ≤ ε_mca`; MCA is what WHIR/FRI-style
  soundness actually consumes.
- `δ*(C, ε*) := sup { δ : ε_mca(C, δ) ≤ ε* }` — formalized as `mcaDeltaStar` in
  `MCAThresholdLedger.lean`, with the two bracket lemmas `le_mcaDeltaStar_of_good` and
  `mcaDeltaStar_le_of_bad`. The good-radius set is downward closed
  (`mca_good_set_downward_closed`), so δ* is a genuine supremum.
- **"Pinning δ*"** means: produce *matching* brackets — `ε_mca(C, δ*) ≤ ε*` and
  `ε_mca(C, δ) > ε*` for all `δ > δ*` — as two axiom-clean `mcaDeltaStar` bracket
  instantiations that **meet** (the issue's acceptance criterion).
- **The window.** Both edges are held by formalized literature: the Johnson radius
  `1 − √ρ` from below (BCGM25 / Hab25 / BCHKS25, full MCA) and
  `1 − ρ − Θ_ρ(1/log n)` from above (KKH26 / Kambiré); the at-capacity conjectures are
  FALSE (CS25, KK25, DG25 — formalized in `MCAUpToCapacityFalse.lean` and friends). So δ*
  lies strictly inside the open window `(1 − √ρ, 1 − ρ − Θ_ρ(1/log n))`, and the entire
  problem is to pin it there. CS25/BCHKS25 couple any upper-bound progress past Johnson to
  **beyond-Johnson list decoding of explicit RS codes — a ~25-year-old open problem**; that
  coupling is the honest measure of difficulty (issue body §1; c1).
- Radius quantization: `ε_mca` sees δ only through the agreement floor `⌈(1−δ)n⌉`, so
  `ε_mca` is a step function and δ*(ε*) is its generalized inverse; the window question is
  literally "where are the jumps of the production-scale staircase between Johnson and
  capacity, and what are the step heights?" (c39, c45). `MCAFiniteTable.lean` collapses any
  δ* determination to ≤ n+1 finite floor checks.
- Companion quantity: the interleaved list-decoding threshold; the LD⇔MCA dictionary
  (§2.6) makes the two problems share one ledger.

The campaign opened with two parallel nine-hypothesis dossiers (c0/c1, ids
4679526195/4679532059 — note their R/N/S labels are permuted relative to each other) under
a standing discipline: constraints → why-nobody → larp-check → falsification probe →
formalize; every refutation lands in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` as a sorry-free constraint lemma.

---

## 2. Exact results proven (Lean, axiom-clean)

### 2.1 Exact δ* pins and threshold curves

| result | value | file / theorem | comment |
|---|---|---|---|
| **First exact MCA threshold anywhere**: RS[F₅, F₅ˣ, 2], ε* = 2/5 | δ* = 1/4 | `DeltaStarExactPinF5.lean` `mcaDeltaStar_C542_eq_quarter` (794d186bf); lane variant `MCADeltaStarExactPoint.lean` `mcaDeltaStar_RS5_eq_quarter` (c3def4543) | c2/c4/c5 |
| **First complete ε_mca profile of any code**: RS[F₅,⟨2⟩,2] at *every* radius (1/5 on [0,1/4), 4/5 above) + full δ*(ε*) curve | — | `MCAExactProfile.lean` `epsMCA_rs_profile` | c45 |
| **First exact δ* for an infinite family**: RS[F, D, n−2], every field/domain, ε* ∈ [1/q, 2/q) | δ* = 1/n | `MCADeltaStarHighRateFamily.lean` `mcaDeltaStar_rs_highRate_eq`; strengthened to all k ≤ n−2 as `mcaDeltaStar_rs_eq_inv_card` | c51, c56 |
| Full-band capstone: RS[F, μ_n, n−2], every ε* ∈ [1/q, n/q) | δ* = 1/n | `MCADeltaStarFullBand.lean` `mcaDeltaStar_rs_smooth_full_band` | c78 |
| Complete MCA landscape of RS[F, μ_n, n−2] at every (δ, ε*) incl. plateau ε_mca = n/q on [1/n, 1] | — | `MCAStaircaseCollapse.lean` (`epsMCA_rs_highRate_plateau`, `mcaDeltaStar_rs_highRate_top`) | c89 |
| **Second pin, deployed rate 1/2**: RS[F₁₇, ⟨2⟩, 4] (smooth n=8) | δ* = 1/4 on ε* ∈ [2/17, 3/17) | `DeltaStarSecondPinF17.lean` `mcaDeltaStar_C84_eq_quarter` (35360aa38) | c92 |
| Widened: same code, 6 certified bad scalars | δ* = 1/4 on [2/17, 6/17) | `DeltaStarSecondPinF17Widened.lean` | c244 |
| **Maximal**: ε_mca(C84, 1/4) = 7/17 exact (B6 = 7) | δ* = 1/4 on **[2/17, 7/17)**, formally maximal | `DeltaStarSecondPinF17Maximal.lean` `mcaDeltaStar_C84_eq_quarter_maximal`, via the far-coset law `mcaEvent_iff_line_explainable` in `FarCosetExplosion.lean` | c265, c271 |
| **Granularity-ladder closed form**: δ* = j/n for ε* ∈ [j/q, (j+1)/q) under collapse+spike budgets | δ* = ⌊ε*q⌋/n | `UniversalStaircaseCollapse.lean` `mcaDeltaStar_eq_granularity` (33990ea4c/4be964209); packaged `MCAStaircaseDeltaStar.lean` `mcaDeltaStar_eq_band_edge` (2714f6d10; sup NOT attained — half-open good set); RS instantiation `GranularityLadderRS.lean` `mcaDeltaStar_rs_eq_granularity` (800904f82, any injective domain) | c141, c151, c156 |
| **Multi-window curve**: F₁₇ˣ = ⟨3⟩, n = 16 — five consecutive exact windows δ* = j/16 on [j/17,(j+1)/17), j = 1..5 (rate 1/4); three windows at rate 1/2 | first machine-checked δ*(ε*) curve segment | `VVectorN16.lean` (`mcaDeltaStar_rate_quarter`, `mcaDeltaStar_deepest`) | c245 |
| Strip-edge pins: δ* = g/n on ε* ∈ [g/q, (n/g)/q), g ∣ n, n−3g < k ≤ n−2g | widest pinned ε*-bands | `StripEdgeDeltaStar.lean` `mcaDeltaStar_eq_strip_edge` (40b6978b4) | c190 |
| Strip-interior pin: δ* = 3/n on ε* ∈ [(n/2)/q, n/q), 4 ∣ n, k = n−5 (good side = an explosion value) | — | `StripSupExactness.lean` `mcaDeltaStar_eq_strip_interior` | c264 |
| Boundary pins: δ* = (b−1)/n on ε* ∈ [(b−1)/q, n/q), b ∣ n, b ≤ 4, k = n−2b+2 (spans n−2 granularity steps at b = 3) | — | `CosetCliqueBoundary.lean` `mcaDeltaStar_eq_boundary` (7b4e74b61) | c227 |
| **Production floor**: at ε* = 2⁻¹²⁸, δ* ≥ (⌊(n−k)/3⌋+1)/n ≈ (1−ρ)/3 unconditionally, every production-shape smooth RS | — | `MCADeltaStarProductionFloor.lean` `mcaDeltaStar_rs_ge_at_secpar` | c255 |
| First exact window-interior ε_mca value: RS[F₁₁,(1..5),2] at δ = 2/5 (strictly between Johnson and capacity) | ε_mca = 10/11 = C(5,3)/q | `MCAWindowInteriorExact.lean` | c93 |
| In-window saturation as a theorem: ε_mca(RS[F₁₇,μ₈,2], 5/8) = 1 exactly | δ* ≤ 5/8 ∀ ε* < 1 | `SmoothWindowSaturation.lean` `epsMCA_window_saturates` | c123 |
| Exact points at UDR and Johnson for (F₁₇, μ₈, 2): census = exactly μ₈ (count 8 = n), two-sided | — | `HalfPairSliceExact.lean`, `JohnsonExactPoint.lean` (agreement-set-maximality device `coreJ_of_mcaEvent`) | c115, c127 |

### 2.2 The universal staircase (the three-regime law)

For every band `b` (radii with δ·n ∈ [b−1, b)), the value of `ε_mca·q` as a function of
distance — consolidated in `docs/wiki/deltastar-exact-staircase-results.md` (the paper
seed, c280):

| distance regime | value | files |
|---|---|---|
| d ≥ 3b−2 (deep) | **= b** (both sides) | `MCAStaircaseMaster.lean` (collapse ≤ b, one induction), `UniversalSpikeFloor.lean` (`epsMCA_ge_j_div_card`, bad side of every band), `MCAStaircaseExact.lean` / `MCAStaircaseRS.lean` (exactness), `BandCollapse.lean` + `BandExactness.lean` (`epsMCA_band_exact`), `BandFloor.lean` (δ* ≥ j/n unconditional) |
| d = 3b−3 (top strip row) | **= n/(b−1)** for (b−1) ∣ n, (b−1)(2b−3) ≤ n | `StripSupExactness.lean` `rs_topStrip_epsMCA_eq` ⊕ `MonomialStripExplosion.lean` `strip_eps_ge` (960fcedaf) |
| d = 3b−4 (second strip row) | ≥ n/(b−1), ≤ n (bracket) | `strip_eps_ge` ⊕ `BoundarySupExactness.lean` `nearTop_epsMCA_le` |
| 2b ≤ d ≤ 3b−5 (lower strip) | ≥ n/(b−1) (sup side OPEN) | `strip_eps_ge` |
| b+1 ≤ d ≤ 2b−1 (boundary), b ∣ n | ≥ n | `CosetCliqueBoundary.lean` `clique_eps_ge` (f7c841c4a) |
| d = 5, b = 3, 3 ∣ n | **= n** (both sides) | ⊕ `BoundarySupExactness.lean` `rs_boundary_epsMCA_eq` (57c0ace52) |
| d = 5, b = 3, 3 ∤ n | ≤ n−1; = n−1 at n = 8 | `BoundaryDefectBound.lean` (193d3f72b, mod-3 strict clump induction) ⊕ `DeltaStarSecondPinF17Maximal.lean` |

The band-collapse arc: universal band 2 (`MCABandTwoCollapse.lean`/`MCABandTwoExact.lean`/
`MCABandTwoRS.lean`, ε_mca = 2/q exactly for d ≥ 4, c63/c74), universal band 3
(`MCABandThreeAssembly.lean`, `MCABandThreeExact.lean`, ε_mca = 3/q exactly for d ≥ 7,
c114/c117), then all bands at once at the **3b−2 threshold** — sharpened from 4j to 3j
during formalization (c119) and proven to be THE law for general linear codes *and* RS
(no MDS separation at threshold level; §3). The thresholds 3b−2 / 3b−3 / 2b−1 are exactly
support-union thresholds (frame absorption vs disjoint tiling; clump induction at d = 3e−1).
Production reading: n = 2^μ has 3 ∤ n and b ∣ n for every 2-power band — boundary rows
recur at every halving of the distance budget with cap n−1, and strip explosions fire at
every band (c213). At d = 2b the boundary value becomes **arithmetic** — governed by
rational points of a determinant quadric (`MCARSBoundaryArithmetic.lean`, RS[F₁₀₁] instance
with bad γ ∈ {0,1,2,33}; c176, c253).

### 2.3 Upper engines (ceilings on ε_mca valid into the window)

- `MCAWitnessCountEngine.lean` — ε_mca ≤ #witness-family/q, every linear code (c58).
- `MCAAntichainEngine.lean` — witnesses of distinct bad scalars form an antichain;
  ε_mca(C, 1/n) ≤ n/q (c62).
- `MCALYMCeiling.lean` — `epsMCA_le_choose_div`: ε_mca ≤ C(n,t)/q at every agreement floor
  t ≥ n/2 (truncated Sperner/LYM), covering the entire window at production rates;
  attained at the first window cell (c90, c93).
- `SpernerCeiling.lean` (915ff93bc) — ε_mca ≤ C(n,⌊n/2⌋)/q at EVERY radius, the first
  ceiling valid above δ = 1/2 (c173).
- `DeviationSupSplit.lean` + `SparseDeviationExtremality.lean` (`rows_close_of_two_bad`) —
  every stack with ≥ 2 bad scalars is an O(δ)-deviation of a codeword pair; ε_mca ≤
  max(1/q, deviation-family sup): the threshold search space IS the sparse-deviation
  family (c54, c59).
- `MCAEquivariance.lean`, `MCAProjectiveEquivariance.lean`, `MCAMonomialEquivariance.lean`,
  `MCAEigenstackOrbitLaw.lean` — the symmetry engine: `epsMCA_eq_iSup_rep` orbit
  reduction; the MCA symmetry group is projective (GL₂); eigenstack bad sets are
  rotation-orbit unions (c6, c11, c14, c71).
- `MCASyndromeSup.lean` / `MCASyndromeFactorization.lean` — ε_mca lives on q^{2(n−k)}
  syndrome pairs (`epsMCA_eq_iSup_syndromePairs`, `epsMCA_eq_iSup_syndromeProb`): the
  reduction that makes exact computation feasible at all (c13, c15).

### 2.4 Census theorem stack (bad scalars = subset-sum/vanishing-sum combinatorics)

- `KKH26CensusLaw.lean` `badScalar_iff_subsetSum` — λ bad for (X^r, X^{r−1}) at agreement
  r ⟺ λ = −ΣT, T an r-subset of the domain (c18).
- `KKH26ConstrainedCensusLaw.lean` `badScalar_iff_constrainedSubsetSum` — general code
  degree: the vanishing-power-sum band e₂ = … = e_{a−k} = 0 (c34).
- `KKH26GapCensusLaw.lean` `badScalar_iff_gapBand` — arbitrary two-monomial stacks (c42).
- `ExcessCensusLaw.lean` / `GeneralGapCensusLaw.lean` — the corrected (post-take-over)
  monic-cofactor excess-witness census objects, exact iff (c98, c102).
- `KKH26FiberStructural.lean` — fiber unions satisfy the band structurally (KKH26 Prop 1
  re-derived inside the framework) (c48).
- `KKH26CharZeroCollisionLaw.lean` `sum_eq_iff_freePart_eq` (char-0 collision law) and
  `KKH26ExactCensusCharZero.lean` `card_image_sum` — the exact char-0 census closed form
  Σ_j 2^{r−2j}·C(2^{k−1}, r−2j) (c29, c44).
- `KKH26CensusExact.lean` — census = stratified count EXACTLY above threshold; the
  KKH26-family ceiling is census-extremal within its construction class (c49).
- `CensusLowerBound.lean` `census_le_epsMCA` — the census is an unconditional ε_mca lower
  bound; `CensusConditionalPin.lean` `mcaDeltaStar_eq_of_censusCrossing'` — δ* = the census
  crossing, conditional on the named extremality surface (c39, c47).
- Towers: `CensusClassificationCharZero.lean` (depth 1: zero-sum ⟹ antipodal-closed,
  fiber unions), `CensusTowerDescent.lean` (depth 2), `tower_closed_of_dyadic_sums_zero`
  (all dyadic depths, char 0), `HaloFreeThreshold.lean` (depth-1 halo empty above
  `(2^{m−1})^{2^{m−1}}`), `CensusTowerFinite.lean` `tower_closed_finite` (F_p, all depths,
  one threshold) (c61, c83, c86, c91, c95).
- Parseval sharpening: `tower_closed_finite_parseval` halves the threshold exponent to
  `(2^m)^{2^{m−2}}` — unconditional census coverage to n = 128 at |F| < 2^256 (c106).
  **Tree-status caveat:** `KKH26ParsevalThreshold.lean` and `HaloFreeThresholdParseval.lean`
  were pruned by the #353 cleanup (1d1bd5c86), restored per DISPROOF_LOG O151, but at
  archive time are not in the committed fork/main tree (restorations exist as untracked
  working-copy files); the Frontier consumer is `Frontier/ThornerZamanS128.lean`.
- `MobiusPencilEnergy.lean` — Möbius pencil energy E₂ = Θ(n³) smooth-domain separation
  (a spectrum-moment fact, *not* δ*-controlling — see N1's refutation, §3).

### 2.5 Interleaving, dictionary, towers, transfer

- `MCAListBracketInterpolation.lean` — `mcaDeltaStar_eq_of_certificates_meet`: "pin δ*"
  ≡ "close the certificate gap" between list-profile good certificates and bad-stack
  certificates, formally (the ABF26 §5 collapse quantified) (c22).
- `MCADeltaStarSandwich.lean` `mcaDeltaStar_sandwich` — δ* is formally sandwiched by pure
  list-decoding data (c33); `MCADictionaryBracket.lean` `mcaDeltaStar_eq_of_dictionary_meet`
  with explicit loss factors (good side 1+2δn·L, bad side L/p) (c145).
- `ReverseDictionary.lean` `exists_interleavedList_card_gt_of_epsMCA_gt` — the dictionary
  run backward: exact MCA values force interleaved list-size lower bounds (c201).
- `TowerMonotonicity.lean` + `TowerMonotonicityRS.lean` `epsMCA_rs_tower` (940e369c5) —
  hypothesis-free fold-tower monotonicity for smooth RS: window lower bounds at small
  scales become production lower bounds (c192, c217).
- `CrossingPin.lean` `mcaDeltaStar_eq_inverse_binomial` (648beb63a) — δ*(ε*) as the inverse
  binomial staircase, all conditionality in the named `FullLayerSupply` (c199);
  `MCAFullLayerSupply.lean` is the supply engine (c97).
- S2/obstruction layer (generator exactness): `Jo26ObstructionCount.lean`
  (`epsMCAG_interleaved_eq_of_obstructionBound` — the A(q,s) factor removed),
  `Jo26ObstructionRowCount.lean`, `Jo26DeviationKernels.lean` (obstructions are deviation
  kernels), `Jo26FullyCloseAssembly.lean`, `Jo26MissingLineSmallSeed.lean` (MissingLine
  TRUE for |Ω| ≤ q), `ExactnessWithoutCoverability.lean` (c3, c20, c25, c26, c30, c31).
- `FarWordSupplyCounting.lean` (e5d63b113) — the §6 named surface `FarWordSupply`
  discharged by counting for every nondegenerate linear code; un-conditions the GG25/Jo26
  curve-decodability equivalences (c182).
- Fold transport: `KKH26FoldTransport.lean`, `KKH26FoldQuotientStack.lean`,
  `KKH26FoldStability.lean` — the KKH26 bad family is a fold **fixed point** at even
  cofactor (the R2 refutation's positive content), with the kill-challenge β = −w (c12,
  c13, c15).

### 2.6 Production-regime assembly and the regime split

- `ProductionRegimeBracket.lean` — `production_good_ladder` (unconditional (1−ρ)/3 floor at
  production shape) + `production_good_johnson_of_packageSupply` (full Johnson range
  conditional on `CellPackageSupply`) (c250).
- `ProductionJohnsonBudget.lean` — `production_johnson_reach`: at ε* = 2⁻¹²⁸, M = 64,
  n ≤ 2^30, every q ≥ 2^192 puts the whole Johnson range below δ* modulo only
  `CellPackageSupply` (c250).
- `KKH26RegimeSplit.lean` — the weld `kkh26_deltaStar_pin_of_johnsonDischarge_and_regimeIII`:
  `JohnsonDischargeStatement` ⊕ `RegimeIIIGoodness` ⊕ arithmetic ⟹ δ* = 1 − r/2^μ exactly;
  and `gs_johnson_lt_jump` — regime III is **nonempty at every live parameter point**, so
  the Johnson lane alone never reaches the pin (c246).
- Worst-case character-sum anchor: `SubgroupGaussSumWorstCase.lean` — for d-torsion G and
  every nonzero frequency, ‖Σ_{y∈G} ψ(by)‖ ≤ √q (classical Gauss-sum completion, no Weil
  input). With the Parseval average √|G| from below, the analytic kernel is pinned at
  exactly √q quality from both sides (c244).
- HBK lane: `ArkLib/ToMathlib/MonomialShiftDivisibility.lean` `monomial_lemma` ([HBK00]
  Lemma 6, new to Mathlib) — average-side subgroup-addition input, explicitly NOT
  pin-closing (c261/c262).

### 2.7 The Johnson lane (BCIKS20 §5/A discharge; files under `BCIKS20/`)

The Hab25 Johnson-discharge chain (`Hab25Johnson*.lean`, ~10 files) was driven down to a
single named residual through a brick sequence with two machine-checked course corrections
(findings 13/14, §3):

- E1′ inventory: `BCIKS20/HasseIndexShift.lean` — Hasse-coefficient degree shape,
  `leadingCoeff_dvd_evalX_hasseDerivY_top` (the W-divisibility credit),
  `weight_Λ_le_of_shape`, `hasseCoeffRepr𝒪_weight_le_of_shape` (c206–c214).
- E2′ assembly: `BCIKS20/StructuredWeightInduction.lean` — `structuredBound`,
  `βHensel_weight_bound_zero_structured` (base exact at the tight anchor),
  `βHensel_weight_bound_structured`, the rebased pair
  `βHensel_weight_bound_zero_rebased`/`βHensel_weight_bound_rebased` (exact at every anchor
  D ≥ totalDegree H), per-term theorems `structuredSuccTermBound_of_budgets`/
  `_of_B_budget`, closing inequalities `harith_of_reduced`/`_top`, and the (P1) capstone
  `βHensel_weight_bound_of_cell_budgets` (c218, c229–c239).
- The repair: `BCIKS20/ClearedRecursion.lean` — `B_coeffC` (the paper-faithful W-cleared
  cell coefficient), the repaired recursion `βHenselC`, and
  **`βHenselC_weight_bound_anchored_loose`** — the complete Claim-A.2 loose weight bound
  Λ(β_t) ≤ (2t+1)·d_R·D, EVERY cell, no per-cell hypotheses, no named Props (c268, c272,
  c274, c276). `BCIKS20/Finding14Countermodel.lean` proves the in-tree (A.1) recursion
  diverges from the paper's at order 1 for non-monic H (the reason the repair exists).
- The wiring: `Hab25JohnsonPackageSupply.lean` — `CellPackage` (the per-cell BCIKS20 §5
  heavy-agreement package: centre x₀, Hypotheses instance, Y-root divisor w with
  (X−C w) ∣ R, matching sets, kill-target weight budget, heavy pinning set S₀),
  `CellPackageSupply`, and the PROVEN consumer chain
  `himpr_of_cellPackageSupply` → `johnsonDischargeStatement_of_packageSupply` (c241).
  Also fully proven: `BCIKS20/SlicedCompositionWip.lean` (the sliced-composition
  improvement disjuncts) and `BCIKS20/CellPinning.lean` (Claim 5.10 assembly).

Net Johnson-lane state: **`CellPackageSupply` is the single residual** (its `hmonic` field
is the live design tension — finding 15, §5), and even discharged it covers only regimes
I–II (δ < gs_johnson); the pin additionally needs `RegimeIIIGoodness` (c241, c246, c278).

---

## 3. Refutations and dead ends (mirror of DISPROOF_LOG.md)

The institutional rule: every dead direction is reduced to a sorry-free constraint lemma in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` (entries O129–O156 plus the #357
sections cover this campaign). The campaign disposed of **28 attack hypotheses**; the major
kills, each with its artifact:

**Slate-level kills (rounds 1–2):**
- **Halving renormalization** (iterate T: (δ,ε) ↦ (δ/2-ish, ε/2)) — one step exits the
  window from anywhere below capacity; unique fixpoint 0. `HalvingWindowExit.lean`
  `halving_exits_window` (c3).
- **R2 fold strict-shrink** — folding does NOT strictly shrink the KKH26 bad family: at
  even cofactor the fold transports the same family one level down
  (`fold_same_KKH_pair_once_of_even_cofactor`; DISPROOF_LOG "#357 R2"); salvage = the
  fixed-point/kill-challenge theory of §2.5 (c7, c9, c15).
- **N1 pencil-energy law** (δ* a function of E₂) — exact bad-count is domain-independent in
  the saturated band while E₂ varies 10×; refuted by
  `probe_n1_energy_vs_badcount.py`; later CORRECTED: the probes only reach the saturated
  band, interior separation stays open, N1′ (extremal pencil / M3) revived (DISPROOF_LOG
  "Fable N1" + correction entry).
- **Universal MissingLine/ObstructionBound** — refuted exactly AT the Johnson radius
  (F₂/F₃ defeaters, `MissingLineDefeater.lean`); below Johnson it holds; for |Ω| > q the
  generous form is false (`Jo26MissingLineGenerousRefuted.lean`,
  `Jo26MissingLineBigSeedRefuted.lean`); the boundary is exactly the seed count |Ω| ≤ q
  (c24, c26, c36).

**The extremality-surface lineage (the census programme's red-team spine):** census v1
(killed: empty rungs contradict the 1/q floor — `CensusExtremalFloor.lean`) → census+floor
v2 (killed: the (X⁹,X⁸) take-over carries 16 = n field-independent bad scalars at an empty
adjacent rung — `TakeoverCountermodel.lean`, found by `probe_takeover_death_radius.py`) →
monomial v3 `MonomialDomination` (killed twice: spike bands —
`MonomialDominationKilled.lean`; boundary row, 7 > 4 via the two-triangle stack —
`MonomialDominationBoundaryRefuted.lean` `epsMCA_quarter_ge_seven`) → **v4 hybrid
two-family max** `HybridDomination` + pin `mcaDeltaStar_eq_of_hybridCrossing`
(non-vacuous: `HybridPinInstance.lean` recovers the F₅ pin), consistent with every theorem
and probe in the tree (c52, c55, c67, c68, c208, c211, c256, c258).

**Staircase-threshold corrections (all self-inflicted and formalized):**
- `halfDistanceStaircaseConjecture` (general codes, d ≥ 2b) — FALSE: doubled-column
  countermodel, `MCAHalfDistanceGeneralRefuted.lean`; first MDS-vs-general-linear
  separation for an MCA quantity; ε_mca below Johnson is NOT a function of (n,d,q) alone
  (c101).
- `GeneralStaircaseConjecture` (d ≥ 2b+1) — REFUTED at b = 4 (tripled-column [15,3,9]
  code), `MCAGeneralStaircaseRefuted.lean`; the **3b−2 law** is the real threshold (c118,
  c121).
- **The MDS rank conjecture — FALSE for RS too**: the perfect-square pencil identity
  rA² − hAB + pB² = ρλ²T^{f+2(b−1)} supplies n/(b−1) bad scalars on the whole strip
  [2b−1, 3b−3]; `MCAMDSStaircaseRefuted.lean` `mdsStaircaseConjecture_refuted`
  (f2cbf6288; 5 certified bad scalars at band 4); discovered by
  `probe_mds_pencil_explosion.py`. Consequence: 3b−2 is THE law for RS as well; the exact
  RS staircase ends at δ ≈ (1−ρ)/3, not (1−ρ)/2 (c157, c166).

**Johnson-lane course corrections (machine-checked):**
- **Finding 13** (DISPROOF_LOG O155): the rebased `hbudget` is UNSATISFIABLE at genuine
  m = d_R cells — the rebased constant double-counts degW; the paper's base case hides an
  anchor assumption `totalDegree H = d_H + degW`; correct frame = the ANCHORED engine
  (c247).
- **Finding 14** (O156 → `BCIKS20/Finding14Countermodel.lean`): the in-tree (A.1)
  transcription's B is un-cleared — `βHensel 1 = −1 ≠ −Z²` at an explicit ZMod 5 instance;
  (P2)'s `hroot` targeted the wrong object; repaired by the cleared `B_coeffC`/`βHenselC`
  (c248, c266).
- Johnson no-gos (c169): pairwise difference quotients and fold-section saturation
  provably die at exactly 2δ; "many rooted specializations ⟹ rational root" is FALSE
  (Y² − (Z²+c) counterexample); no elementary collapse reaches Johnson (3j is sharp).

**Other recorded kills:** the dossier §28(b) overclaim (no in-tree reduction of the pin to
N ≪ |G|^{3/2}; retracted twice, c243/c246); "JohnsonDischargeStatement ⟹ pin" (regime III
nonempty — c246); G5 locus-overlap corrections (union bound measure-tight, c16); char-0 →
mod-p lifting (fails at n = 64, measured exactly; mod-p censuses below threshold carry
hundreds-to-thousands of spurious coincidences — only integer ℤ[ζ] sweeps are ground
truth, c147/c167/c175/c249); the coset-core conjecture (fails at a = 9: a genuinely new
2n-size family, c225); circuit-collision at the optimum (sampling artifact, c254); the
window cocycle stab (exact but empty — pairwise witness intersections can be empty in the
window; the 28th disposed hypothesis, c281); deviation-LYM (vacuous, c251); the
slanted-frame census 928 (p-contaminated; true char-0 value 544, c175). Pre-campaign
failed approaches §3 of the issue body (vanishing explosion, capacity-disproof transfer,
moment methods past Johnson, spike attacks, A3 instance programme, boundary-card routes,
q-denominator removal) all remain standing constraints.

**Anti-laundering incidents:** `KKH26ParsevalThreshold.lean` wrongly pruned as
"superseded" by the #353 cleanup and restored (O151) — prune commits need grep-the-theorem
scrutiny too (c106). The `.lake` self-referential-symlink infrastructure incident
(c170 → recovery c177).

---

## 4. The census programme

Map: `docs/wiki/census-programme.md`. One paragraph: for adjacent/two-monomial stacks the
bad scalars are **exactly** pivot coefficients of band-constrained subsets of the domain
(census laws, §2.4); band-constrained subsets of 2-power smooth domains are **exactly**
fiber unions (char-0 tower + finite tower above explicit thresholds); the census is an
unconditional ε_mca lower bound; and the two-family profile law
`ε_mca·q = min(q, max(staircase, census))` matches every exact data point ever computed
(9 instances, 14+ field combos, 3 red-team cycles — including a prime-order domain where
the census equals the prime Lam–Leung predictions, c108).

**The two-layer law** (O143/O144): `census_p = (char-0 vanishing-sum locus mod p) +
(surplus exactly on the finite cyclotomic-norm spectrum S(n,k))`; the parity law (image of
e₂ under ℤ[ζ] → F₂) kills rows a ≡ 2, 3 (mod 4) — half of all window rows are clean at
every depth (`WindowTwoLayerThreshold.lean`, `AdjacentPairDepthOneClean.lean`,
`oddRow_no_badScalar`; c40, c50, c152). The depth-1 dictionary is two-sided and
p-independent above threshold (`depthOne_badScalar_iff_char0`, c155); the generic mod-p
transfer engine is `FoldedSumThreshold.lean` `foldedSum_vanishing_iff_char0` (c160), with
the sharp per-instance criterion via resultant divisors (`PairSumRigidityModP.lean`,
c158/c161) and the census-wide upgrade `CollinearityCensusTransfer.lean` /
`SlantedTransferThreshold.lean` (c177, c277).

**The wide-circuit matroid census.** The dual pencil law (`MCADualPencilLaw.lean`
`dependent_iff_collinear`) re-poses the sub-threshold census as classical incidence
geometry: count collinear triples of Γ_n = {(ζ^i+ζ^j, ζ^{i+j})} (c120). The strata:

- **Horizontal** (equal products / exponent-sum classes) — closed unconditionally at all n:
  `equal_products_iff_same_class`, count (n/2)[C(n/2,3)+C(n/2−1,3)] (c131).
- **Vertical** (equal sums) — C(n/2,3) in char 0 (`MCAVerticalStratumCharZero.lean`) and
  over F_p above threshold (`PairSumRigidityModP.lean`); same-parabola triples are NEVER
  circuits (`MCAParabolaStratification.lean`, the first negative law) (c128, c139, c158).
- **Slanted** — chord law (`TwoPlusAntipodalChordLaw.lean`: collinear ⟺ 2k ≡ i+j+d),
  shape-I/II seed families on a rational collinear curve (`SecondLayerSeedFamily.lean`),
  matching frame (`CollinearityMatchingFrame.lean`: collinearity ⟺ decidable antipodal
  balance), supply weld (`SlantedSupplyWideCircuits.lean`); per-class counts and the
  **grand total n(n−4)²/8** proven (`ChordFamilyCount.lean` `chord_family_grand_total`)
  (c180, c197–c203, c216–c226).
- **Closure (the fourth family)** — absent at n = 8, appears at n = 16; signed
  difference-class relation ±d₁±d₂±d₃ ≡ 0 (mod n/2); `MCAClosureFamily.lean`
  `dependent_of_closure`; count n(n−4)(n−8)/6 (verified blind at n = 128) (c167, c249).
- **Exact integer censuses:** μ₈ = 40 = 20H+4V+16S (`MCAZeta8CensusCheck.lean`
  `census8_check`, ZERO axioms — raw 262144-tuple kernel sweep; capstone
  `MCAZeta8CensusCapstone.lean`); μ₁₆ = 1328 = 728+56+288+256; μ₃₂ = 23520 =
  16240+560+3136+3584 — four families, three scales, zero exceptions (c164, c171, c174).
- **The doubling recursion** B(n) = n²(n−8)/8 + 2·B(n/2): all three generators proven
  (`CensusDoublingMap.lean`, `CensusDoubling.lean`); the second layer is Galois-generated
  ((n−8)/4 seed orbits per scale) (c193, c205, c240).
- **The exactness converse** (nothing else is collinear): trichotomy
  (`WideCircuitTrichotomy.lean`), 14-case matching analysis (c230/c232), antipodal branch
  PROVEN (`ChordConverseCore.lean`, 96 cases), and the no-antipodal branch
  **machine-generated**: `secondLayer_of_no_antipodal` (in `SecondLayerConverseCore.lean`,
  wrapped by `ChordConverseWrapper.lean`) — a 1571-line proof emitted by
  `gen_noantipodal_lean.py` from the exact integer certificates of
  `probe_noantipodal_branch_tree.py` (10395 pairings, 10387 killed, 8 survivors) — the
  certificate-to-Lean generator as industrial method (c263, c269; commit 85c692499).

**Balanced-set / boundary-explosion census (depth-1 window rows):** closed forms
N₄(n) = n(n−3)/4, N₅(n) = n(n−4)/4, N₆ = N₇ = 0 (parity); a=4 census =
(2^{m−1}−1)² above threshold (`A4CensusValue.lean`); a=5 census = n, one rotation orbit,
**unconditional in p** (`A5CensusValue.lean` — the flat-n law); structure laws
`BalancedFourLaw.lean`/`BalancedFiveLaw.lean`/`PairSumsWiring.lean`/`CosetAugmentation.lean`/
`A8CosetStructure.lean`; the a=9 sporadic one-orbit family (size 2n, doubling-persistent)
(c178, c186, c189, c202, c207, c215, c221, c222, c224, c228, c231).

**The 4-adic quartet recursion** (items 11/13/14): quartets {±x, ±ix} have characteristic
polynomial T⁴ − x⁴, so the constrained census recurses down the 4-adic tower
(`QuartetTowerLaw.lean`); consequence: the adjacent-pair family's window interior has **no
field-independent floor** — any interior pin from this family must come from the char-p
(Weil-fluctuation) layer, i.e. from below-√q character-sum information (c259, c260;
DISPROOF_LOG items-11/13/14 entry).

**Boundary-row laws:** band-3 value = n − [3 ∤ n] (coset triangles; n = 10 needs
non-coset triangles); at every band, d = 2b−1 with b ∣ n gives value n (μ_b-coset cliques
sharing a common 2-plane) — the production sub-Johnson profile is a three-phase periodic
structure (c196, c204, c212, c213).

---

## 5. The open core, precisely

After ~120 axiom-clean files and 28 disposed hypotheses, the honest residue is two named
objects, one equivalence, and one reformulation:

1. **`CellPackageSupply`** (`Hab25JohnsonPackageSupply.lean`) — the BCIKS20 §5 per-cell
   package: for every large irreducible factor cell of every stack, produce the centre,
   the Y-root divisor w with (X − C w) ∣ R, matching sets and the kill-target weight
   budget (Claim 5.7-style production). The full consumer chain to
   `JohnsonDischargeStatement` is proven. **Finding 15** (c278): the package's `hmonic`
   field is the design tension — at monic H the finding-14 divergence vanishes but the
   anchor D = d_H is infeasible for monicized GS factors; two mapped repairs: (a)
   repackage with the original non-monic H (the landed `βHenselC` closes (P1) outright at
   the feasible anchor D₀ = d_H + degW), or (b) a weighted-shape supplier exploiting the
   GS interpolant's (1,k−1)-weighted structure. Attack surface:
   `RationalFunctionsCore` Hensel/βrec + `Claim510Supply.weight_killTarget_le`.
2. **`RegimeIIIGoodness`** (`KKH26RegimeSplit.lean`) — ε_mca ≤ ε* on
   [gs_johnson, 1 − r/2^μ): the type-enforced honest gap between the Johnson lane and the
   pin. Even a full Johnson discharge covers only δ < 1−√ρ−o(1); regime III is nonempty at
   every live parameter point (c246).
3. **The above-Johnson bad-side family**: every landed lower-bound family (spike,
   sunflower, pencil, triangle, widened-pin) is O(n)/q — silent at ε* = 2⁻¹²⁸. Certifying
   any bad radius < 1 at production scale needs a single stack with **> q·2⁻¹²⁸ ≈ 2^64+
   bad scalars** — no known construction comes within polynomial range (c250).
4. **The incidence reformulation**: `FarCosetExplosion.lean` `epsMCA_ge_far_incidence` —
   ε_mca ≥ (line-explainability count)/q for far directions (commit 609a282d2): the
   top-down attack surface posing the window question as far-direction line vs
   weight-ball/syndrome incidence. Equivalently (c243): bad scalar at band b ⟺ s₀+γs₁
   lies on a union of coordinate subspaces of parity-check columns; sup-exactness =
   line-vs-secant-variety incidence capacity. The slope census in syndrome coordinates IS
   the line–ball incidence count of the LD⇔MCA dictionary — the 25-year wall in different
   clothes (c254).
5. **The equivalences**: via the in-tree CS25 coupling, the window sup side is equivalent
   in its regime to **beyond-Johnson list decoding of explicit smooth-domain RS codes**;
   the analytic kernel is pinned at exactly √q from both sides (Parseval average √|G|
   below, `SubgroupGaussSumWorstCase` √q above) — the open core is **beating √q
   per-frequency on smooth multiplicative subgroup character sums**, met independently
   from six directions (KKH26 census, char-0 collision law, M3/pencils, additive energy,
   vertical thresholds, divisibility events) (c129, c149, c244, c250, c259).
6. **Quarantined externals** (none δ*-decisive): `TZPrimeSupply` (Thorner–Zaman PNT-in-APs,
   the only route to s ≥ 128 census rows), paper-interface residuals
   (`CapacityBoundsProofs.lean`), GKL24 witness covers, CS25 refutation inputs (c227).
7. **Smaller named opens**: b ≥ 4 lower-strip sup side and boundary rows d ≤ 2b−2 (the
   absorption inequality provably fails — a genuinely new mechanism is needed); the
   general 3 ∤ n defect-certificate family (probe-exact n−1; GP-triangle conjecture, c282);
   `FullLayerSupply` instances; the uniform MDS rank certificate (3-term
   bordered-determinant identity — the gateway from the (1−ρ)/3 floor to (1−ρ)/2, c270);
   the census exactness-converse arithmetic uniform in n; Lam–Leung W(pqr) positivity
   (c137).

**The conditional production answer** (census programme): δ*(production smooth RS, 2⁻¹²⁸)
= 1 − a_c/n at the true census crossing, machine-checked end-to-end except (i) census-band
sup-extremality (≡ the wall, item 5), (ii) the true subset-sum count at s ∈ [128, 256]
(TZ/lacunary-gated), (iii) the beyond-Johnson floor. If the char-0 forecasts hold, the
answer reads **δ* = capacity − c(ρ) with c(ρ) ≈ 2/s\* a constant** — sharper than the
published capacity − Θ(1/log n) (c72, census-programme.md).

The 26-item program (c162, id 4682186937 — the full-comment review that became the second
half of the campaign) finished at **19 of 26 decided** (c277), with the consolidated
results page `docs/wiki/deltastar-exact-staircase-results.md` (c280) as the paper seed.

---

## 6. Probes and data (`scripts/probes/`, #357-relevant)

Exact-arithmetic, pre-registered, cross-validated (≥ 3 primes + char-0 anchor rule).
One line each; O-numbers refer to DISPROOF_LOG entries.

**Ground truth / exact ε_mca:** `probe_exact_epsmca_ladder.py` (exact ε_mca via the
syndrome reduction — first exact computations anywhere); `probe_epsmca_sampled_rungs.py`,
`probe_epsmca_field_drift.py`, `probe_epsmca_orbit_exact_n12.py` (n=8/12 rungs; the flat-12
numerator); `probe_exact_pin.py` (F₅ pin ground truth); `probe_c2r_second_pin.py` /
`probe_c2r_band3_wide.py` (the (17,8,4) second pin and band-3 sweep);
`probe_band3_exact_value.py` (B6 = 7 exhaustive); `probe_band3_cert_extractor.py` (widened-pin
certificates); `probe_strip_sup_exactness.py` + `probe_boundary_sup_exactness.py` (7
exhaustive cells confirming strip/boundary sup-exactness); `probe_middle_band_ladder.py`
(splitting-ladder heights n/g); `probe_mds_pencil_explosion.py` (the pencil explosion that
killed the MDS rank conjecture, 6 instances).

**Fold/tower lane:** `probe_kkh26_fold_transport.py` + `probe_r2_kkh26_fold_transport.py`
(fold fixed point over 32,512 cells); `probe_k1_fold.py`, `probe_fold_slices.py`,
`probe_tower_fiber.py`, `probe_tower_level2_census.py`, `probe_prime_power_descent.py`.

**Census laws and spectra:** `probe_o137_kkh26_extremal.py` (KKH26 stack attains the F₅
worst case); `probe_o138_flat_numerator_solved.py`; `probe_o139_window_interior_census.py`
(first in-window census data); `probe_o140_death_radius_n32.py` /
`probe_o140_death_radius_rate_half.py` (family death radii; reach grows with n);
`probe_o141_mitm_fakepoint_census.py` + `probe_o141_norm_divisibility_spectrum.py` (the
fake-point reformulation; norm spectra); `probe_o142_rate_quarter_spectrum.py` /
`probe_o142_structural_classification.py` (fiber-union classification at 5 primes);
`probe_o143_two_layer_law.py` (the two-layer law); `probe_o144_parity_law.py` (|A| mod 4);
`probe_o145_a4_closed_form.py` / `probe_o145_classification_instances.py` (N₄ = n(n−3)/4;
one-orbit halo law); `probe_o147_excess_census_two_layer.py` (CA/MCA gap = the
coset-witness layer); `probe_o148_takeover_row_pinned.py` + `probe_o148_exact_minor_norms.py`
(take-over row = n at every prime; exact ℤ[ζ] norms); `probe_o149_halo_norm_mechanism.py`
(halo monogamy); `probe_o150_depth2_classification.py`; `probe_o152_prime_domain_redteam.py`
(prime-order domain red team, zero deviations); `probe_n2_zero_slack.py` (census =
stratified count exactly); `probe_char0_death_law.py` (the 4-adic quartet recursion);
`probe_takeover_death_radius.py` (found the take-over); `probe_jump_subsetsum.py`.

**Wide-circuit/matroid census:** `probe_matching_converse_patterns.py` (the 14 matching
patterns); `probe_converse_kill_certificates.py`; `probe_antipodal_branch_tree.py` (105
leaves, 2 survivors); `probe_noantipodal_branch_tree.py` (10395 pairings → the 8 seed
systems; certificates feed `gen_noantipodal_lean.py`); `probe_collision_branch_tree.py`;
`probe_slanted_char0_census.py` + `probe_slanted_stratum_census.py` (slanted census 544 @
n=16, supply completeness); `probe_two_plus_antipodal_chord_law.py`;
`probe_pairsum_rigidity_modp.py` (violation spectra divide resultants).

**Balanced-set census:** `probe_balanced_four_law.py`, `probe_a4_census_value.py`,
`probe_census_a5_a6.py` (N₅ blind-confirmed at n=64), `probe_a5_coset_shape.py`,
`probe_a58_census_table.py` (full n=16 table), `probe_8set_coset_structure.py`,
`probe_a9_exceptional_family.py`, `probe_coset_core_conjecture.py` (fails at a=9).

**Boundary rows:** `probe_boundary_row_incidence.py`, `probe_boundary_triangle_stratum.py`,
`probe_boundary_n10_three_triangles.py`, `probe_boundary_n12_coset_triangles.py`,
`probe_band4_boundary_coset_cliques.py`, `probe_boundary_sup_exactness.py`.

**Obstruction/MissingLine lane:** `probe_missing_line_search.py`,
`probe_missing_line_rungs.py` / `_f5_rungs.py` / `_l3.py` / `_heavy_fast.py`,
`probe_defeater_exactness.py`, `probe_exactness_at_defeater.py`.

**Hypothesis falsifiers:** `probe_n1_energy_vs_badcount.py` (killed N1),
`probe_n1_maximizer_audit.py`, `probe_monomial_domination_falsifier.py`,
`probe_s3_eigenstack_orbit_law.py` / `probe_s3_extremal_orbits.py` /
`probe_s3_twisted_inversion_merger.py` (the S3 orbit laws), `probe_k4_slack.py` /
`probe_k4_ud_window.py`, `probe_above_johnson.py`, `probe_interior_ceiling.py`,
`probe_kkh_ceiling_numeric_reach.py`, `probe_kkh26_stratified_spread.py`.

Sub-directories with results ledgers: `genlaw/` (general rung law + the char-0→mod-p
falsifier), `incidence/` (difference-loci incidence laws, O129–O146 batch),
`moments/` (the M3 domain-separation channel).

---

## 7. Comment index (the load-bearing comments)

283 comments total; all by lalalune except c16/c17/c46/c191/c195 (NubsCarson's incidence
lane and two draft-PR handoffs). The spine:

| c# | id | content |
|---|---|---|
| c0 / c1 | 4679526195 / 4679532059 | The campaign opening: two parallel nine-hypothesis dossiers (permuted R/N/S labels), the three walls, execution queues |
| c2, c4, c5 | 4679734924, 4679791402, 4679810494 | **The first exact pin**: δ*(RS[F₅,F₅ˣ,2], 2/5) = 1/4, two lanes |
| c18 | 4680095533 | The census law `badScalar_iff_subsetSum` — ceiling welded to subset sums |
| c22 / c33 | 4680135185 / 4680241633 | LD⇔MCA bracket interpolation + the δ* sandwich ("pin δ*" ≡ certificates meet) |
| c29 / c43 | 4680199215 / 4680357356 | Round-1 and round-9 verdict tables; the slate fully decided; the single analytic core named |
| c45 | 4680385070 | First complete ε_mca profile of any code (`MCAExactProfile`) |
| c51 / c56 | 4680458481 / 4680504680 | First exact δ* theorem for an infinite family; strengthened to all k ≤ n−2 |
| c52, c55, c67, c68 | 4680462915, 4680494850, 4680679559, 4680682684 | The red-team arc: extremality refuted → floor repair → take-over → two-family max |
| c64 | 4680594794 | Generation-1 scoreboard + generation-2 slate |
| c72 | 4680725868 | O148: δ* localized to one number per rate; the capacity − c(ρ) forecast |
| c92 | 4681212780 | The second pin theorem at deployed rate 1/2 |
| c93 | 4681251927 | First exact window-interior ε_mca value (10/11) |
| c104 | 4681373624 | Monomial-domination pin v3 (later corrected to v4) |
| c110 | 4681438652 | `docs/wiki/census-programme.md` — the programme map |
| c118 / c157 / c166 | 4681551237 / 4682127865 / 4682254884 | The staircase-threshold kills: b=4 refutation; MDS rank conjecture false; Lean kills landed; 3b−2 is THE law |
| c129 | 4681727699 | The honest production-scale map (two-regime law, B(n,t,q) decomposition) |
| c141 / c151 / c156 | 4681902326 / 4682034726 / 4682119010 | The granularity-ladder closed form δ* = ⌊ε*q⌋/n and the production-family split at q ≈ n·2¹²⁸ |
| c162 | 4682186937 | **The 26-item program** — full review of all 159 prior comments |
| c164 / c167 / c174 | 4682208882 / 4682257702 / 4682286719 | Zero-axiom n=8 census; the fourth family; complete closed-form char-0 census |
| c169, c181, c185, c187 | 4682272958, 4682393213, 4682443883, 4682496356 | O154: the Johnson discharge mapped to its last node, then ONE statement |
| c199 | 4682701312 | `CrossingPin`: δ*(ε*) as inverse binomial staircase |
| c211 / c220 | 4682871242 / 4683094426 | MonomialDomination boundary refutation + v4 surface |
| c218 / c239 / c241 | 4683053119 / 4684193908 / 4684234371 | Johnson E2′ assembly → (P1) capstone → **reduction to the single residual `CellPackageSupply`** |
| c244 / c246 | 4684510577 / 4684591179 | Widened pin + √q anchor; the regime split (`RegimeIIIGoodness` — Johnson lane ≠ pin) |
| c250 / c251 / c255 | 4685019567 / 4685052172 / 4685410930 | Round 24: the production regime assembled; the (1−ρ)/3 floor at ε* = 2⁻¹²⁸ |
| c259 / c260 | 4685470067 / 4685514886 | The 4-adic quartet-tower law: no field-independent window-interior floor |
| c264 / c265 / c271 | 4685818945 / 4685935537 / 4685988610 | Strip sup-exactness; B6 = 7; **the maximal second pin [2/17, 7/17)** |
| c266 / c276 / c278 | 4685937090 / 4686327110 / 4686370506 | Finding 14 machine-checked; Johnson (P1) repaired & fully assembled; finding 15 (`hmonic` tension) |
| c273 / c279 | 4686140296 / 4686380846 | Boundary sup-exactness (3 ∣ n) + the defect bound (3 ∤ n ⟹ ≤ n−1) |
| c280 | 4686397525 | The consolidated results page / paper seed |
| c281 / c282 | 4686413064 / 4686427306 | The window cocycle stab honestly disposed; the explicit n−1 defect pencil + GP-triangle conjecture |

Operational/unclassifiable comments (not knowledge content): validation liturgies and
session scoreboards (c65, c87, c112, c135, c159–c160, c234–c235); lane claims and
coordination notes (c8, c10, c12, c134, c137, c150, c163, c165, c242–c243, c267); the
`.lake` symlink incident and recovery (c170, c177); race-dropped-import repairs and the
sibling-commit-sweep incident (c145, c158); NubsCarson draft-PR handoffs #364/#365 (c191,
c195); one transcription-garbled duplicate (c262, duplicating c261's landing).

## Addendum: the #371 boundary-band solution (2026-06-12, rounds 64–75)

The successor-issue campaign solved the deepest above-Johnson band exactly.
Chain of results (all axiom-clean; see `docs/wiki/deltastar-programme.md` for
the file table, and the #371 comment thread for the round-by-round record):

1. **Boundary-slice exact law** (R64): at `k < (1−δ)n ≤ k+1`, strongly-far
   directions, `badSet = {−e_t(u₀)/e_t(u₁)}` over injective `(k+1)`-tuples,
   both inclusions.
2. **Schur-ladder + master modular reduction** (R65–66): `e_t(Q∘dom) =
   (Q %ₘ P_t).coeff k · e_t(x^k)` — the whole census is remainder-coefficient
   arithmetic in `F[X]/P`; ladder ratios are negated node sums.
3. **Farness discharge** (R67): degree-exactly-`k` directions are automatically
   strongly far — the exact laws are unconditional in the radius window.
4. **Spectrum fusion** (R68–69): subset sums of an antipodally closed power
   domain are exactly the realizable signed sums; the ladder bad count at the
   boundary is `Σ_{a∈A(h,k+1)} 2^a·C(h,a)` — the first exact bad count above
   Johnson (validates the probe census 40 at h=4, k=2).
5. **Full-band ladder law + cliff** (R70, R74): the ladder is `0` below the
   band and the spectrum mass in it — the first complete `ε_mca` curve.
6. **Generic-far pin** (R71–72): when `C(n,k+1)² ≤ q`, a collision-free stack
   attains `#badSet = C(n,k+1)` (Lagrange divided differences + Vandermonde
   kernel + hyperplane union bound).
7. **Universal bound + all-stacks solution** (R73): `#badSet ≤ C(n,k+1)` for
   EVERY stack at EVERY radius below capacity (gluing + joint-pair assembly);
   with (6), the boundary sup over all stacks is exactly `C(n,k+1)`.
8. **Band packing + attainment** (R74–75): at band `k+m < (1−δ)n ≤ k+m+1`,
   `⌊n/(k+m+1)⌋ ≤ sup #badSet ≤ C(n,k+1)/C(k+m+1,k+1)` (≤k-overlap packing of
   witness cores; disjoint-blocks construction).

Remaining open (#371): the band-`m` bracket gap (extremal design) and the
production regime (`C(n,k+1)² > q`).

## The supply wall (#389), two faces, one open problem (2026-06-13)

The #371 → #389 successor isolated the entire remaining δ* question to ONE
statement: a per-word bound on the explainable `(k+m+1)`-core count over a smooth
multiplicative domain `μ_n ⊂ F_p` (`SmoothDomainTwoRegimeLaw`, the production form;
`ExplainableCoreSupply` / `SubJohnsonSupplyResidual`, the abstract forms). The
fleet attacked it from two independent directions, and **both reduce to the same
open subgroup-rigidity input** — a `poly(n)`-field transfer of a sum-product /
vanishing-sum bound on `μ_n`. This is the precise current location of the wall.

**Countermodels (all machine-checked) — why it is domain-coupled.** Any proof MUST
use the absence of additive structure in `μ_n`; the supply blows up on every
additively-structured domain:
- abstract set systems stop at Johnson sharply (`AffinePlaneSharpness`, pole at
  `t² = s·n`);
- prime-subfield Frobenius secants (`FrobeniusSubfieldBlowup`, `Θ(n²)`, char `p`);
- ANY composite subfield, every band (`SubplaneSupplyFloor`: sheared `AG(2,K)`,
  `(r²+r)·C(r,2+m+1)`; covers char 2 / binary towers);
- random words at `q = Θ(n)` (`TwoBranchSupplyCountermodel`, no subfield needed).
The capped general-domain optimum IS the trivial pair bound `C(n,k)`, attained
(`subJohnsonSupplyResidual_pairCount_tight`). So no improvement is possible from
counting alone — the gain must come from the domain.

**Face A — additive (energy / Garcia–Voloch).** The cubic/Sylvester word `x³` has
supply exactly the zero-sum-triple count (`cubicSupply_eq_sumZeroCard`); Cauchy–
Schwarz ties it to the additive energy `E(μ_n)` (`zeroSumTriples_sq_le_card_mul_energy`).
The named input `GVRepBound` (Garcia–Voloch `|G∩(G+μ)| ≤ 4|G|^{2/3}`, HBK via
Stepanov) gives `E ≤ 6.4|G|^{8/3}` (`additiveEnergy_cube_le_of_gvRepBound`), hence
`cubicSupply < 2.54·n^{11/6} ≪ n²` (`cubicSupply_pow_le_of_gvRepBound`) and, on the
Fourier side, no Gauss-sum frequency reaches the Johnson scale up to `n ≈ 2⁴⁸`
(`card_johnson_scale_le_gv`). Non-vacuity: `gvRepBound_H16`, `cubicSupply_mu16_F257_eq_zero`.

**Face B — multiplicative (Mann / esymm fibre).** The monomial word `x^{k+m+1}` has
supply exactly the elementary-symmetric fibre `{T : e_1=…=e_{m+1}=0}` (`EsymmFiber`).
The 2-power Lam–Leung/Mann theorem makes a zero-sum SET of `2^ν`-th roots antipodally
closed (`subset_neg_mem_of_sum_zero`), pinning the char-0 fibre to `N_fib` exactly;
`LadderListModP` transfers it to `F_p` above a resultant threshold.

**The shared wall.** Face A needs `GVRepBound` at `p = poly(n)` (Stepanov substrate
`StepanovHighMultVanisher` has the linear-algebra existence half; the Frobenius-reduced
√q-saving generator family is open). Face B's `LadderListModP` threshold is
`p > (2r)^{n/2}` (super-exponential, **vacuous at production**: `p = 2¹²⁸` fixed, `n`
growing); the sharp statement is that violating primes divide a folded resultant — the
same `poly(n)`-field rigidity transfer. **Both faces are machine-checked up to that one
transfer; it is open research (HBK `E ≪ |G|^{5/2}` for `|G| ≲ p^{2/3}` is the
closest published result, but production needs `n ≪ √q`, where Weil alone is provably
insufficient — `SubgroupCharacterSumNoGo`). Do not fabricate its closure.**
