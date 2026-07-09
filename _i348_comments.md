=== 2026-06-11T04:41:11Z ===
## Union-bound generic: ALL protocol-independent pieces now landed (`RunPrefixMarginal.lean` + `RbrKnowledgeFlip.lean`, axiom-clean)

Item 3 of this issue is reduced to per-instantiation game matching only. The complete generic skeleton of `Pr[accept] ≤ Σᵢ Pr[flip at i] ≤ Σᵢ εᵢ`:

| piece | theorem | status |
|---|---|---|
| deterministic first-crossing (knowledge form) | `KnowledgeStateFunction.exists_challenge_flip_of_full` | ✅ landed |
| fiber-constancy comparison | `probEvent_bind_le_probEvent_of_fiber` | ✅ landed |
| support backbone (continuation preserves prefix) | `continueFromTo_entry_eq` | ✅ landed |
| **the prefix-marginal** (simulated, subsingleton state — both fence settings) | `probEvent_take_simulated_runToRound_le` | ✅ landed |
| finite union bound | `probEvent_exists_finset_le_sum` | ✅ landed |
| per-protocol challenge-round game matching | (`ChallengeCoherence` layer, e.g. `probEvent_run'_simulateQ_addLift_getChallenge_bind`) | per-instantiation, tools landed |

The remaining matching step per protocol: rewrite `runToRound i.succ` at a challenge round into prefix ≫ `getChallenge` (the `processRound` V_to_P branch) and align with the rbr game's `runWithLogToRound` shape via `runWithLogToRound_discard_log_eq_runToRound` — exactly what the per-round flip-bound proofs in `Stir/SubUnitRbr.lean` already demonstrate.

**Item 1 status note**: the per-cell production is actively progressing in-tree (`Hab25CellDichotomyWiring.lean` in flight in the working tree as of this writing) — it composes directly with the landed `exists_pinning_pair_of_heavy_agreement` consumer chain.

**Item 2** unchanged: gated on the genuine-fold prover construction (the honest scope finding stands).


=== 2026-06-11T04:51:49Z ===
## Interface note for the active cell lane (`Hab25CellDichotomyWiring` WIP): the Johnson-regime `himpr` branch wires to the landed pinning chain

`exists_dichotomyData_of_cell_improvement`'s per-cell input `himpr` (large cell ⟹ improving pair `d₀ d₁` with `∀ z ∈ E, ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0`) has its Johnson-regime producer ready, in two landed steps:

1. **`BCIKS20.Claim510CellPinning.exists_pinning_pair_of_heavy_agreement`** — per cell carrying a §5 heavy-agreement package (centre `x₀`, `ClaimA2.Hypotheses` for the cell's branch, the decoded surface `w` with `(Y′−C w) ∣ R` and `natDegree < n`, base-pointed matching sets with fold readings, the `killBudget` cardinality): the polynomial pair `(v₀, v₁)`, `natDegree < n`, pinning every Taylor section as `v₀ + γ·v₁`. (All `π_z(ξ) ≠ 0`/separability legs sliced/free per the landed honesty patches.)
2. **the improvement lemma in `Hab25AffineCapture`** (landed): an affine-captured scalar yields the disagreement point with vanishing affine gap — converting the pinned pair (as word vectors `d₀ := v₀∘domain, d₁ := v₁∘domain`, with the McaDecode witness sets) into exactly the `himpr` improvement form.

So the single remaining production for item 1 is the **per-cell §5 package instantiation from the cell vocabulary** (`R` irreducible + uniform decode family dividing the `R`-fibers ⟹ centre selection + surface + matching sets + numerics) — the centre/certificate selection that `S10ToBundlePair`/`Section5GlobalAssembler` already does globally, restricted per cell. Everything downstream of that instantiation, on both sides of the funnel (`badCount_le_of_cell_improvement` → `johnsonNumericBound` on yours; pinning → `hsteps57`/`mca_johnson_bound_CONJECTURE_pair_*` on mine), is proven and axiom-clean.


=== 2026-06-11T04:54:08Z ===
## Hypothesis portfolio for THE remaining gap (per-cell §5 package instantiation) — 5 known + 5 advanced, with constraints/larp-checks

**Literature re-check (fresh)**: [ePrint 2026/680](https://eprint.iacr.org/2026/680) (open-problems survey — confirms the per-cell production has no external treatment; it is a formalization seam, not a known-math gap) and [ePrint 2026/891](https://eprint.iacr.org/2026/891) (interleaving stability for MCA + curve decodability — relevant to GA3 below; note the in-tree `Jo26InterleavingBound`/`InterleavingStabilityMCAP` lanes already track it). Key fact from the earlier BCIKS20 §5 deep read (comment-4674128237): **the paper never does per-cell centre selection** — Claim 5.6 picks ONE centre `x₀` with ALL specialized discriminants nonzero, THEN pigeonholes onto one `(R, H)`. The formal gap is transporting that order into the cell vocabulary.

### Known-math hypotheses
**GK1 (single global centre).** *Constraints*: needs `|F| >` the product-discriminant degree budget. *Larp-check*: this IS the paper's Claim 5.6; novelty is only the formal transport — the per-cell packages share ONE `(x₀, root-family, ξ/branch certificates)`; only the matching sets are per-cell. *Hypothesis*: `exists_global_centre_for_cells` — one `x₀` + one root family serving every factor cell of `exists_cell_production_total` simultaneously, via the product certificate (`ConditionDiscProduct`/`PerPlaceSeparabilitySupply` lanes).
**GK2 (surface from the S10-converse).** Per cell, the decoded surface `w` with `(Y′−C w) ∣ R` comes from the cell's uniform decode family + counting — exactly the `S10ToBundlePair.exists_bundle_pair_of_S10_converse` output restricted to the cell. *Larp-check*: actively the cell lane's work; my side should CONSUME, not re-prove.
**GK3 (matching sets by carve-out).** The per-cell heavy sets = the cell minus the certificate-vanishing loci (Bézout-bounded carve-outs, the `Section5GlobalAssembler` pattern), with cardinality from `killBudget + certificate degrees < |E|`.
**GK4 (fold readings from rich coordinates).** `hfold`/`hbaseA` at the nodes from `exists_rich_coordinates` (landed Claim 5.11 half) + `decodeAgreesAt` — pure wiring.
**GK5 (numeric consolidation).** One arithmetic lemma turning the cell-size threshold `T = n·|constraintIndices|·gs_degree_bound` into the `killBudget·d_H < |matchingSet|` leg after the GK3 carve-outs — explicit polynomial inequalities, no new math.

### Advanced hypotheses
**GA1 (centre-free pinning).** Replace the Taylor-at-`x₀` reading by direct Vandermonde extraction at the nodes — would DELETE Claim 5.6 entirely. *Why nobody*: the paper's 𝒪/Λ machinery is centre-anchored; the in-tree Vandermonde globalization (`Claim59Vandermonde`) shows the eval-free style works at the coefficient level. High risk: the Hensel uniqueness (Seam B) is intrinsically centred.
**GA2 (cell-free unification).** Skip cells: apply the pinning at the WHOLE bad set with the unique-rich-factor (landed R-K2) replacing the Claim-5.7 pigeonhole — the count then pays `deg_Y Q` once instead of per-cell. Novel simplification if the uniform threshold survives; suspect the per-z factor multiplicity breaks it (probe).
**GA3 (interleaving transfer).** Lift the pair-case conjecture to ℓ-ary via 2026/891-style interleaving stability — the in-tree `mcaDeltaStar_interleaved_eq`/`epsMCA_interleaved_eq` are the landed seeds.
**GA4 (degenerate-cell absorption).** Fold the `none`-cell's explicit bound into the threshold so `T` (hence the final constant) shrinks — pure budget surgery on the landed funnel.
**GA5 (char-p orbit packages).** Per-cell packages via Galois-orbit sums in char p (richness is a class function) — the only route to field-uniform constants; probe-only.

**Execution order**: GK2 is the active lane's (consume on landing); GK1+GK3+GK4+GK5 compose into the package once GK2's surface exists — I'll land what's independent of GK2 now (GK5's arithmetic, GK4's wiring shapes); GA2 gets a feasibility probe next session.


=== 2026-06-11T04:55:14Z ===
## GA2 probe verdict (cell-free unification): REFUTED as a simplification — and a structural alignment found instead

Read against the landed `exists_cell_production_total_div`: the cells are ALREADY the canonical attribution fibers — `Index = Option (irreducible factors of ONE global GS interpolant Q₀)`, with a single uniform decode `P : F₀ → F₀[X]`, the degenerate (`none`) cell explicitly bounded by `n·|constraintIndices|·(gs_degree_bound/(k−1))`, and each factor cell carrying the fiber divisibility `(Y′−C(P γ)) ∣ R(γ)`. So there is no "cell-free" simplification to be had: the cell structure IS the trivariate-level mirror of my `factorBudgetIndex` attribution (`Hab25FactorBudgetSupply`), with `Q₀` playing the bivariate interpolant's role one level up. GA2 closes with a *negative* verdict and a *positive* by-product: the two attribution decompositions (theirs at `Q₀ : (F₀[X])[X][Y]`, mine at `Q : F₀[X][Y]`) are the same construction at adjacent altitudes — a DRY target once the dust settles.

**Updated precise statement of the one remaining production** (GK1+GK2 composition, per factor cell `R ∣ Q₀`): select the centre `x₀` (ONE for all cells — the paper's Claim 5.6 product-discriminant move, GK1) and the fiber factor `H ∣ evalX (C x₀) R` with its `ClaimA2.Hypotheses`, the cell surface `w` (from the cell's uniform decode by S10-converse counting — GK2, the active lane), and the carved matching sets (GK3) — then `exists_pinning_pair_of_heavy_agreement` fires and `himpr`'s improvement branch follows through the `Hab25AffineCapture` lemma. Every consumer and every producer EXCEPT this selection step is landed and axiom-clean.


=== 2026-06-11T05:03:05Z ===
2026-06-11 validation/audit update: `./scripts/validate.sh` currently reaches a concrete Hab25 rich-factor wiring failure in `ArkLib/Data/CodingTheory/ProximityGap/Hab25UniqueRichFactor.lean`.

Representative output:

```text
ArkLib/Data/CodingTheory/ProximityGap/Hab25UniqueRichFactor.lean:78:46: Unknown identifier `WordStack`
ArkLib/Data/CodingTheory/ProximityGap/Hab25UniqueRichFactor.lean:216:14: Unknown constant `witnessRich_of_weld_data`
```

The file still prints several standard-axiom-only declarations before the failed constant, but the module itself is not green. Please treat this as a wiring/import/name drift blocker for the Johnson endgame path, not as a candidate for a new axiom or vacuous residual.

Focused acceptance target:

```bash
lake env lean ArkLib/Data/CodingTheory/ProximityGap/Hab25UniqueRichFactor.lean
```

then rerun `./scripts/validate.sh` far enough to confirm this frontier is past the build.


=== 2026-06-11T05:05:08Z ===
## hypothesis-execution result: the Johnson-regime `himpr` is DISCHARGED from the package (`75aea78da`, axiom-clean) — the funnel's per-cell input now has its Johnson producer

Executing the portfolio (this is GK1+GK2's consumer side, proven ahead of the selection): **`Hab25CellPencilJohnson.lean`**:

- **`pencil_of_pinning_and_section`** — the Johnson pencil: the pinning-pair output (every Taylor section of the cell surface is `v₀ + γ·v₁`) + the section link (`hsec`: each decode IS the surface's Taylor section) ⟹ `(v₀', v₁')` with `natDegree < k` and `∀ γ ∈ E, P γ = v₀' + C γ·v₁'` — the RS degree bounds recovered by the same two-point trick as the window pencil;
- **`cell_improvement_of_pinning_package`** — the funnel's `himpr` input (`exists_dichotomyData_of_cell_improvement`'s only hypothesis), discharged from the per-cell §5 package legs + `hsec`, through the landed `McaDecode.affineCaptured` + `affineCaptured_improve` — the exact Johnson mirror of `cell_improvement_of_window`.

**The composition tree is now complete above the selection**: package legs + `hsec` → `cell_improvement_of_pinning_package` → `exists_dichotomyData_of_cell_improvement` → `badCount_le_of_cell_improvement` → `johnsonNumericBound_of_claim1_cells` → `mca_johnson_bound_CONJECTURE`. What remains, precisely: per large factor cell of `exists_cell_production_total_div`, (a) the **section link `hsec`** — a mechanical lemma (irreducible `R` + `(Y′−C w) ∣ R` force `R ≅ Y′−C w`, so the cell divisibility `(X−C(P γ)) ∣ R(γ)` pins `P γ = w_γ` = the Taylor section via `sum_taylor_eq` mapped along `eval γ`; monic-linear divisibility in a domain) — and (b) the **selection legs** (centre `x₀`, branch `H` with `ClaimA2.Hypotheses`, base-pointed heavy sets, `ξ`-weight, numerics — GK1+GK3, the Claim-5.6 product-certificate move). (a) is bounded next-brick work; (b) is the genuine remaining selection, now consumable field-by-field.


=== 2026-06-11T05:18:10Z ===
## SECTION LINK PROVEN (`1ba3f0385`, axiom-clean): item-1's remaining surface is now the selection legs ALONE

**`section_link`** is no longer a hypothesis: irreducibility makes `R` an associate of `Y′−C w`; the fiber splits as a unit times `X − C w_γ`; monic-linear divisibility in a domain pins `P γ = w_γ`; and Taylor's formula (mapped along `eval γ`) writes `w_γ` as the range-`n` section sum. Consequently **`cell_improvement_of_pinning_package'`** discharges the funnel's `himpr` from the cell's OWN divisibilities (`hdec` + `hdvdR` — both direct outputs of `exists_cell_production_total_div`) plus the §5 package legs only.

**The complete remaining surface of this issue's item 1, after tonight** (each a hypothesis of `cell_improvement_of_pinning_package'`, all with named in-tree producer lanes): the centre/branch selection (`x₀`, monic irreducible `H`, `ClaimA2.Hypotheses` — the Claim-5.6 good-specialization lane), the surface `w` with `(Y′−C w) ∣ R` (the S10-converse/SectionFactor lane), the tail (the landed sliced truncation capstone), the base-pointed heavy sets with fold readings (`exists_rich_coordinates` + carve-outs), and the `ξ`-weight/cardinality numerics. A selection-legs production workflow was dispatched and intentionally stopped (rate budget); its recon-stage brief survives in the session workflow script (`issue348-selection-legs-wf_35981584-72a.js`) for direct resumption.

Composition tree, fully proven above the selection: `cell legs → cell_improvement_of_pinning_package' → exists_dichotomyData_of_cell_improvement → badCount_le_of_cell_improvement → johnsonNumericBound_of_claim1_cells → mca_johnson_bound_CONJECTURE`.


