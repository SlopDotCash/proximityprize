=== COMMENT 2026-06-09T19:58:09Z ===
## First unconditional discharges of the §5 core: the vacuous-regime map (`5478761c4`, `dfdf7d6df`, axiom-clean)

Attacked the `StrictCoeffPolysResidual` core via its geometric form `CurveCommonAgreementResidual` (the BCIKS20 §6 common-agreement counting, isolated in `CoeffExtractionResidual.lean`; the bivariate-Lagrange reduction `strictCoeffPolysResidual_of_commonAgreement` is already proven). New file `BCIKS20/Curves/CoeffExtractionVacuous.lean`, 7 theorems, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Mechanism.** The residual carries the probability hypothesis `Pr > k·errorBound`; since every probability is `≤ 1` (`PMF.coe_le_one`), the residual holds **unconditionally** once `1 ≤ k·errorBound`:
- `curveCommonAgreementResidual_of_one_le_mul` / `strictCoeffPolysResidual_of_one_le_mul` — the abstract form.
- `_of_card_le` — composing the existing `errorBound_ge_const : n/q ≤ errorBound`: the core holds for **every field with `q ≤ k·n`** — in particular every *full-domain* RS code (`n = q`) at any curve dimension `k ≥ 1`.
- `errorBound_ge_e7` + `_of_card_le_e7` — the sharp Ioo-branch constant: in the strict interior `m = min(1−√ρ−δ, √ρ/20) ≤ 1/20`, so `(2m)⁷ ≤ 10⁻⁷` and `errorBound ≥ deg²·10⁷/q`; hence the core holds for **every field with `q ≤ k·deg²·10⁷`**. At FRI-scale `deg = 2^40` this covers all fields up to `~k·2^103` unconditionally.

**Honest scope.** These are vacuous-regime discharges: they prove the BCIKS20 probability threshold is unsatisfiable there, so the conditional content is empty. The genuinely open #304 content is now machine-checked to be **exactly the large-field band `q > k·max(n, deg²·10⁷)`** (the deployed STARK setting with `q ≈ 2^128..2^256`, smooth subdomain `n ≪ q`) — where the §5 Guruswami–Sudan/Hensel route (`Section5StrictDataFin` ← `betaCurveInput_of_section5`, whose single deep input is the Faà-di-Bruno numerator identification `hβ`, proven in the monic case) must produce the common agreement. Also confirmed en route: the sibling `BoundaryCardResidual` is **refuted as stated** (in-tree `ZMod 5` witnesses at `k=1,2`) — boundary work must keep a stronger hypothesis; the strict-interior residual is the correct target.

=== COMMENT 2026-06-09T20:00:11Z ===
## Correction + the exact #304 frontier (post-L13 architecture)

My previous comment cited the Faà-di-Bruno numerator identification `hβ` as the single deep input of the §5 producer chain. That is **stale**: the `L13` split (`L13Milestone.lean`, kernel-clean, 0 sorries) made the β-identification **unconditional** — the strong numerator `β_strong` has the embedding identity as its *defining property* (`betaEmbedEqStrong_holds`, no hypothesis), so every `hβ`-shaped residual in the chain is supplied by definition.

**The exact current frontier.** The strict-radius §5 keystone `correlatedAgreement_affine_curves_strongBeta_of_betaRecFin` reaches `δ_ε_correlatedAgreementCurves` (the CA bound STIR/WHIR/FRI need) from a SINGLE remaining input: the per-word-stack geometric bundle

`hInput : (prob threshold) → (strict Johnson interior) → BetaCurveInputFin u`

whose construction from the GS interpolant decomposes into exactly:
1. **GS factor data** `(R, H irreducible factor, Hypotheses)` — partially supplied (`GSFactorData`, `Section5Concrete*`, `gs_existence_over_ratfunc`).
2. **The App-A.4 weight budgets** `hbB`/`hBzero`/`hbξ` (Λ-weight bounds on the canonical Faà-di-Bruno coefficients) — this is the **#138 core** (`SuccDivWeightLe_of_monic`, still open even in the monic case).
3. **Matching geometry** `mpPoint`/`hcardFin` — the §6 matching-point counting on a large set.
4. **Per-z Hensel data** `hHensel`/`hdeg` — the `MatchingDvdInput` route exists (`hPz_of_henselDatum`).

So #304 = (2) + (3) + remaining glue of (1)/(4), with (2) the deepest known open core. Combined with the vacuous-regime bricks (`q ≤ k·max(n, deg²·10⁷)` covered unconditionally, `5478761c4`/`dfdf7d6df`), the open region is the large-field band with these four producers as the work items.

=== COMMENT 2026-06-09T20:24:39Z ===
## Today's landings: vacuous-regime CA + §6 geometry producers (axiom-clean)

1. **`CorrelatedAgreementSmallField.lean`** — the first **hypothesis-free** in-tree instances of the BCIKS20 correlated-agreement theorems: `RS_correlatedAgreement_affineLines_of_card_le(_e7)` (Thm 1.4, lines) and `correlatedAgreement_affine_curves_of_card_le(_e7)` for `q ≤ k·n` resp. `q ≤ k·deg²·10⁷` (vacuous regime; boundary impossible at strict δ).
2. **`MatchingGeometryProducers.lean`** — item (3) of the frontier, the §6 matching geometry: the bad-set counting core (`card_gt_of_compl_subset`), the finite-range cardinality family, **the `hcardFin` producer** (`hcardFin_of_badSet`, chained through the verified L9/L10 weight collapse), the `mpPoint` producer upgrade (`haP_coeff` discharged uniformly via degree truncation; unit readings t-uniform; remaining per-(t,z) input isolated to the genuine L12 α-identity `hαβ`), and capstone glue `section5DataFin_of_producers_badSet`.

Remaining open core: (2) the App-A.4 weight budgets (#138 `SuccDivWeightLe_of_monic`) and the L12 α-identity + discriminant/bad-set instantiation — the genuine research-grade items.

=== COMMENT 2026-06-09T20:34:20Z ===
**Breakthrough lead found (end of session):** `B_coeff_weight_le` is ALREADY CLOSED in-tree (HenselNumerator.lean wave 6, axiom-clean): `weight_Λ_over_𝒪 (B_coeff …) D ≤ (natDegreeY R − Σλ)·(D+1−natDegreeY H) + degreeX p` — structurally the `hbB` weight budget the producer chain needs. Per the file's own note, the only sharpening to the paper's exact `(D−Σλ)` constant is the **pure P2-independent degree-tracking lemma `degreeX p ≤ D − Σλ`**. So item (2) of the frontier (the weight budgets, previously believed the deepest core) may reduce to: one degree-tracking lemma + convention bridging (natDegreeY↔natDegree, D+1↔D) + the `hBzero` vanishing (attack via `B_coeff = prefactor • hasseCoeffRepr𝒪`). This re-prioritizes the work plan: hbB first.

=== COMMENT 2026-06-09T20:44:56Z ===
**hBzero core LANDED** (`379524bcf`, axiom-clean): `B_coeff_eq_zero_of_natDegree_lt` (`BCoeffVanishing.lean`) — for `Σλ > R.natDegree` the outer Hasse derivative is already zero, so `B_coeff = prefactor • 0 = 0`. This is the load-bearing half of the `hBzero` weight-budget producer item (covers the `i₁ ≥ 1` threshold case directly); remaining: the `i₁ = 0` equality-boundary case + the staged `degreeX p ≤ D − Σλ` lemma for `hbB` (recipe on this issue + memory). The weight-budget item (2) is now actively yielding.

=== COMMENT 2026-06-09T20:45:56Z ===
**hBzero boundary finding (honest constraint):** `prefactor = Nat.multinomial …` (HenselNumerator.lean:416) is always positive, and at the `i₁ = 0` equality boundary `Σλ = R.natDegree` the outer Hasse derivative is the (generally nonzero) Y-leading coefficient — so the canonical `Bcoeff` does NOT satisfy the producer's `hBzero` at that boundary. The landed `B_coeff_eq_zero_of_natDegree_lt` covers exactly `Σλ > R.natDegree` (all `i₁ ≥ 1` thresholds). Consequence: the `BetaCurveInput` instantiation must either use the strict-threshold form or carry a boundary-adjusted `Bcoeff` (zeroing the single `(i₁=0, Σλ=natDegree)` cell, compensated in `hβ`). Do not attempt to prove the literal `i₁=0` equality case — it is false for the canonical coefficients.

=== COMMENT 2026-06-09T20:48:45Z ===
**bξ unlock lead (final session finding):** `ξ = mk(ξ_pre)` where `ξ_pre` is an explicit polynomial (`RationalFunctionsCore.lean:2377`) with `natDegree_ξ_pre_le` (:2572) and the top-coefficient bound (:2596) **already proven**; in the monic case the `coeff(d−1)/W` division vanishes (`W=1`). The `hbξ` budget therefore likely follows by the exact `B_coeff_weight_le` proof pattern (`weight_Λ_over_𝒪_le_of_mk_eq` + `weight_Λ_le_natDegreeY_mul_add_degreeX` + the ξ_pre degree lemmas). Combined with `betaRec_weight_le` (pluggable budgets, `BetaWeightInduction.lean:221`), the closed `B_coeff_weight_le`, the landed `B_coeff_eq_zero_of_natDegree_lt`, and trivial monic `bW`: **the entire weight-budget item (2) may close with NO new mathematics** — pure assembly of existing proven pieces. This supersedes the earlier "open research" assessment of #138-adjacent content in the monic regime.

=== COMMENT 2026-06-09T20:50:58Z ===
**bξ absorption question resolved — second statement-level constraint found:** the generic weight route gives `(d−1)(D+1−d_H) + degreeX(ξ_pre)`, but the producer's `hbξ` budget is `(d−1)(D+1−d_H)` exactly — zero X-headroom — while `ξ_pre`'s coefficients (`P.coeff i · W^{d−2−i}`, `RationalFunctionsCore.lean:2377`) are nonconstant X-polynomials. The canonical `ξ` therefore likely violates the literal `hbξ` shape (analogous to the `hBzero` `i₁=0` boundary). **Verify the `hbξ` statement semantics before attempting its proof** — the producer's weight budgets appear to carry two statement-level tightnesses that the canonical objects do not meet; the fix is a budget reshape (X-headroom term) or a sharper per-coefficient weight route, not a deeper proof.

=== COMMENT 2026-06-09T20:52:28Z ===
**Correction to the previous comment — `hbξ` is likely TRUE and provable:** the zero-X-headroom concern applies only to the lossy *generic* route (`weight_Λ_le_natDegreeY_mul_add_degreeX`). The **per-coefficient route** via `weight_Λ_le_iff` works: Y-coefficient `n` needs `n·(D+1−d_H) + deg_X(coeff n) ≤ (d−1)(D+1−d_H)`, which has headroom `(d−1−n)(D+1−d_H)` for every `n < d−1`, and the top coefficient (`n = d−1`, needing a constant) is exactly what the proven `natDegree_ξ_pre_coeff_top_le` (`RationalFunctionsCore.lean:2596`) addresses. Proof design: `weight_Λ_over_𝒪_le_of_mk_eq` → `weight_Λ_le_iff` → top case via `:2596`, lower cases via coefficient-degree bounds + headroom arithmetic. With this, the **entire weight-budget item (2) is now a designed, no-new-math assembly** (betaRec_weight_le + B_coeff_weight_le + hBzero core + monic bW + this hbξ design).

=== COMMENT 2026-06-09T21:00:09Z ===
**Parameterized `hbξ` reduction LANDED** (`067402e8d`, axiom-clean): `xi_weight_le_of_coeff_bounds` — the ξ weight budget follows from per-coefficient degree bounds on `ξ_pre` via `weight_Λ_over_𝒪_le_of_mk_eq` + `weight_Λ_le_iff` (the honest GS-bundle input shape, using the per-coefficient headroom identified in the previous comments). **The weight chain's abstract slots are now all filled**: `betaRec_weight_le` (pluggable budgets) + `B_coeff_weight_le` (closed) + `B_coeff_eq_zero_of_natDegree_lt` (landed) + this reduction. Remaining for item (2): instantiate the per-coefficient bounds from the GS interpolant degree data carried by the bundle.

=== COMMENT 2026-06-09T21:03:10Z ===
**Monic `bW` budget LANDED** (`8b703907a`, axiom-clean): `W𝒪_weight_le_zero_of_monic` — `W𝒪 = 1` when `H` is monic, so its `Λ`-weight is `≤ 0`. **Status of weight-budget item (2): all four budget inputs are now proven theorems** — `bW` (this), `bB` (`B_coeff_weight_le`, closed), the `hBzero` vanishing core (landed), and the `hbξ` per-coefficient reduction (landed) — feeding the pluggable `betaRec_weight_le`. The single remaining step for item (2) is instantiating the `hbξ`/`hbB` per-coefficient degree bounds from the GS bundle's concrete degree data.

=== COMMENT 2026-06-09T21:05:19Z ===
**Weight chain: final composition plan — all pieces now located and proven.** Discovered in-tree: `weight_ξ_bound` (`RationalFunctionsCore.lean:2854`) supplies `hbξ` exactly, and `B_coeff_weight_le_graded` (`HenselNumerator.lean:1134`) supplies the graded `hbB` (the staged degree-tracking lemma `degreeX_hasseCoeffRepr_le` was already done under the paper grading `hR : ∀ j, degreeX (R.coeff j) ≤ D − j`). Combined with the landed monic `bW` and `hBzero` core: **every budget input is a proven theorem.** Caveat: the graded `hbB` shape is looser than `betaRec_weight_le_concrete`'s, so the composition must go through the *pluggable* `betaRec_weight_le` (`BetaWeightInduction.lean:221`) with `bB := graded shape` plus an `htele` ℕ-arithmetic lemma for that shape (template: `wβ_tight`/`wβ_tight_le_loose` in `BetaWeightCollapse`). That single arithmetic lemma + the assembly is all that remains of weight-budget item (2).

=== COMMENT 2026-06-09T21:08:57Z ===
**`betaRec_weight_le_excl` LANDED** (`d205d96f6`, axiom-clean): the weight induction with the telescoping hypothesis required **only on non-forbidden pairs** — the form the graded App-A budgets actually satisfy (at `(i₁=0, σ=1)` the only partition is the forbidden `{s+1}`, where the graded arithmetic genuinely fails; everywhere else the hand-verified budget `wβ t = α(2t−1)+β`, `α = (d−1)(E+1)+D+(E+1)`, `β = E+1`, `E = D−d_H` closes, using `D(k−1) ≥ E+1 ⟸ d_H ≥ 1`). **Remaining for the weight chain:** formalize that hand-verified `htele` arithmetic (pure ℕ, with `betaRec_partsCount_two_mul_sub` for the parts sum) + assemble `betaRec_weight_le_graded` = excl-induction ∘ {graded `hbB`, `weight_ξ_bound`, monic `bW`, base case} — all ingredients proven.

=== COMMENT 2026-06-09T21:11:47Z ===
**The graded `htele` arithmetic LANDED** (`452672701`, axiom-clean): `graded_htele_arith` — the per-term telescoping inequality at the slack budget `wβ t = α(2t−1)+β` (`α = d·A+D+A`, `β = A`, `A = D−d_H+1`), valid for all non-forbidden pairs, with shapes matching `weight_ξ_bound` and `B_coeff_weight_le_graded` exactly. **Weight-budget item (2) status: every component is now a proven theorem** — the exclusion induction (`betaRec_weight_le_excl`), all four budgets (graded `hbB`, `weight_ξ_bound`, monic `bW`, `hBzero` core), and the telescoping arithmetic (this). The single remaining lemma is the **assembly** `betaRec_weight_le_graded` (compose the above + the `σ=1`-forbidden bridge via `parts_sum` + the `Σ count·wβ(l)` expansion via `betaRec_partsCount_two_mul_sub`), then the GS-bundle instantiation.

=== COMMENT 2026-06-09T21:21:58Z ===
## WEIGHT-BUDGET ITEM (2): PROVEN (`6bb95c0ec`, axiom-clean)

**`betaRec_weight_le_graded`** (`BetaWeightGradedAssembly.lean`) — the canonical-`Bcoeff` weight theorem: under monic `H`, `natDegreeY R ≥ 2`, the paper grading `hR : degreeX(R.coeff j) ≤ D−j`, and the standard degree budgets,

`weight_Λ_over_𝒪 (betaRec x₀ R H hHyp (B_coeff H x₀ R) t) D ≤ α(2t−1) + A`, with `α = d·A+D+A`, `A = D−d_H+1`.

Assembled from: `betaRec_weight_le_excl` (exclusion induction, landed earlier today) + `B_coeff_weight_le_graded` (in-tree) + `weight_ξ_bound` (in-tree) + the monic `bW` (landed) + `weight_mk_X_le` (base case, new) + `partsCount_affine_sum` (sum expansion, new) + `graded_htele_arith` (telescoping, landed) + the `σ=1`-forbidden bridge.

**The item that opened this session classified as "the deepest open research core (#138-adjacent)" is now a closed theorem for the canonical coefficients in the monic graded regime.** Remaining on the weight side: only the consumption plumbing (feeding this budget into `hcardFin_of_concrete`/the bundle in place of the `(2t+1)·d·D` shape, or proving the wβ-form bridge). The #304 frontier is now: that plumbing + `hαβ` + the discriminant instantiation + GS factor glue.

=== COMMENT 2026-06-09T21:25:26Z ===
**Consumption plumbing LANDED** (`ca8078e78`, axiom-clean): `hcardFin_of_graded` — the finite-range `hcardFin` bridge at the graded budget, feeding `betaRec_weight_le_graded` directly into the exact `Section5StrictDataFin.hcardFin` field for the **canonical** `Bcoeff`. **Weight-budget item (2) is now closed end-to-end**: theorem + consumption. The #304 producer list now stands at: (1) GS factor glue (partial), (2) ~~weight budgets~~ **DONE** (monic graded regime), (3) matching geometry — `hcardFin` done, `mpPoint` done modulo `hαβ`, (4) per-z Hensel — route exists. The genuine remaining mathematics: the L12 `hαβ` identity + the discriminant/matching-set instantiation (compose with the landed `DiscriminantBadSet` + the fleet's S5 results).

=== COMMENT 2026-06-09T21:27:21Z ===
**Discriminant instantiation LANDED** (`c4e3ce875`, axiom-clean): `gradedCardBudget`(+monotonicity) and `gradedConcreteFin_of_disc` — a nonzero discriminant whose non-vanishing locus lies in the matching set, with **one** top-index field-size bound, yields the whole `[k,T]` graded cardinality family. **The full graded cardinality chain is now proven end-to-end for the canonical `Bcoeff`:** `disc ≠ 0` + `|F|` large → matching-set family (`gradedConcreteFin_of_disc`) → `hcardFin_of_graded` → `Section5StrictDataFin.hcardFin`. Remaining #304 mathematics: the L12 `hαβ` identity (the per-`z` specialization `coeff t (aβ z) = π_z(betaRec t)/(w^a·x^e)`) and the GS factor glue — with the discriminant input now connectable to the fleet's landed S5 results (`separable⇒discr≠0`, char-zero + char-p discharges).

=== COMMENT 2026-06-09T21:28:57Z ===
**`hαβ` attack route identified:** `PlaceGeometrySupply` documents `hαβ` as the single irreducible per-`(t,z)` input ("no in-tree lemma derives it"). However, `aβ` is a **free input** of the producer — the caller chooses the local series. Route: set `aβ z := π_z`-projection of the **strong** α-series, so `hαβ` becomes the `π_z`-projection of the *unconditional* L13 identity `beta_strong_embedEq` (`embedding(β_strong t) = α_t·W^{t+1}·ξ^{e_t}`), discharged by a `π_z`∘embedding commutation lemma + unit division (`w, x ≠ 0` already given). The needed new mathematics reduces to the commutation of the place-evaluation with the `𝒪 H → 𝕃` embedding — a ring-hom factoring question, not a Hensel computation. Next deliverable: `mpFin_of_strong`.

=== COMMENT 2026-06-09T21:33:28Z ===
**Denominator-free L12 interface LANDED** (`4e67f6ffe`, axiom-clean): `bridgeData_of_mul_form` — `BridgeData` from the multiplied-out reading `coeff t aβ · (w^a·x^e) = π_z(betaRec t)` (equivalent to the division form via `eq_div_iff`). Since `αFromBeta` is **definitionally** `emb(betaRec)/(W^{t+1}·emb(ξ)^{e_t})` in `𝕃 H`, the supplier obligation is now exactly the shape a `π_z`-evaluation of the **cleared** L13 relation produces — no localization machinery needed. The `hαβ` frontier is reduced to: evaluate the cleared 𝒪-level relation `coeff-witness · W^{t+1}·ξ^{e_t} = betaRec t` (descended from 𝕃 by `emb`-injectivity) under the ring hom `π_z` — ring-hom algebra over proven identities.

=== COMMENT 2026-06-09T21:36:23Z ===
**`hαβ`: complete formal plan (all-standard steps).** `βHenselAssembled` coefficients live in the localization `𝒪[1/ξ] ⊆ 𝕃` (monic: `W=1`). The discharge: (1) `L′ := Localization.Away ξ`, with `𝒪 → L′ ↪ 𝕃` (injective, domain); (2) **descend** the proven 𝕃-root `assembledSeries_isRoot_of_monic` to `L′` by injectivity; (3) `π̂_z := IsLocalization.lift π_z` (the unit condition is exactly the given `π_z(ξ) = x ≠ 0`); (4) transport the root through `PowerSeries.map π̂_z` (ring-hom/eval commutation); (5) coefficients read off as `π_z(βt)/(w^{t+1}x^{2t−1})` = the landed `bridgeData_of_mul_form` interface → `BridgeData` → `mpFin` → `Section5StrictDataFin` (with the landed `hcardFin` chain) → **keystone fires**. Every step is standard Mathlib (`IsLocalization.lift`/injectivity); ~150 lines; no remaining mathematical unknowns in this chain. This is the last #304 construction.

=== COMMENT 2026-06-09T22:02:18Z ===
**Step (3) LANDED** (`2054ca0ad`, axiom-clean): `π_hat_z` — the localized place evaluation `Localization.Away ξ →+* F` via `Localization.awayLift` (unit condition = the in-data `π_z(ξ) ≠ 0`), with `π_hat_z_comp` (restricts to `π_z` on `𝒪 H`). Steps remaining in the `hαβ` construction: (2) the injection `Localization.Away ξ ↪ 𝕃` (awayLift of `embeddingOf𝒪Into𝕃`, injective since `𝒪` is a domain and `emb` injective) + descent of the proven monic 𝕃-root; (4) `PowerSeries.map π̂_z` transport; (5) coefficient read-off into the landed `bridgeData_of_mul_form`.

=== COMMENT 2026-06-09T22:10:14Z ===
**Step (2) LANDED** (`ac22498b2`, axiom-clean): `embLoc : Localization.Away ξ →+* 𝕃 H` with `embLoc_comp` (restriction) and **`embLoc_injective`** — via `lift_injective_iff`, with `IsDomain (𝒪 H)` derived (irreducible `H_tilde′` → prime span → quotient domain) and domain cancellation through `eq_iff_exists`. Steps (2)+(3) of the `hαβ` construction are now both proven; remaining: (4) descend the monic 𝕃-root through `embLoc_injective` and transport via `PowerSeries.map π̂_z`, (5) coefficient read-off into the landed `bridgeData_of_mul_form`. Gotchas recorded: `IsLocalization.injective` hits an instance diamond on the quotient ring (use `eq_iff_exists` + cancellation instead); the injectivity proof needs `maxHeartbeats 1000000`.

=== COMMENT 2026-06-09T22:12:33Z ===
**Q-descent factoring LANDED** (`23591a879`, axiom-clean): `emb_mk_C` — `liftToFunctionField = emb ∘ mk ∘ C` for every coefficient (generalizing `embed_W𝒪`). With this, `coeffHom`'s 𝕃-lift factors through `𝒪`, so both `Q = R.map coeffHom` and the assembled series coefficients have canonical localization preimages. **`hαβ` construction state: steps (2), (3), and the factoring for (4) are all proven** (`embLoc`+injectivity, `π̂_z`, `emb_mk_C`); remaining: the descent/transport assembly (calc skeleton drafted) and the coefficient read-off into `bridgeData_of_mul_form`.

=== COMMENT 2026-06-09T22:15:22Z ===
**Step-(4) core LANDED** (`b39bd3338`, axiom-clean): `coeffHom_loc` (the canonical `Localization.Away ξ`-valued preimage of `coeffHom`), its coefficient formula, and **the descent commutation square** `PowerSeries.map embLoc ∘ coeffHom_loc = coeffHom` (coefficient-wise via `embLoc_comp` + `emb_mk_C`). `Q = R.map coeffHom` now has the canonical localization preimage `R.map coeffHom_loc`; with `embLoc_injective` + `PowerSeries.map_injective`, the proven monic 𝕃-root descends to the localization where `π̂_z` evaluates. **`hαβ` construction: steps (2), (3), (4)-core all proven and landed** — remaining: the final descent/transport application (one assembly theorem) + the coefficient read-off into `bridgeData_of_mul_form`.

=== COMMENT 2026-06-09T22:20:46Z ===
## Satisfiability audit of the keystone surfaces + the first satisfiable assembly (`bdc534b24`, axiom-clean)

Two constructibility obstructions in the existing §5 surfaces, found while wiring the producer chain, plus the repair:

**(1) The centred route is permanently undischargeable.** `Section5StrictDataFin` / `KeystoneAssembly.section5DataFin_of_producers` state `hγ`/`hrep`/`hPz` against the in-tree `γ x₀ R H hHyp`, which is built from the legacy `RationalFunctions.β` — an `Exists.choose` of the weight-only `β_regular`. Nothing beyond `choose_spec` (the weight bound) is provable about an `Exists.choose`, so the `hβ` residual (`∀ t, β R t = betaRec …`) — and with it `hγ` and `hrep`-against-`γ` — can **never** be discharged. The centred producer assembly organizes hypotheses but can never be instantiated. (Independently, `hsubst` forces `x₀ = 0` — the known F1 caveat.)

**(2) The off-centre bundles are unsatisfiable as stated.** `BetaCurveInputOffcentre`/`…OffcentreFin` (and the centred `BetaCurveInput`/`…Fin`) quantify their `hPz` field over **all** `P : F → Polynomial F` with no decoded-family constraint. But `hrep`+`hdegX` guarantee the linear-representative premise is satisfiable, so once `RS_goodCoeffsCurve u δ ≠ ∅` the conclusion `∀ z ∈ good, P z = …` must hold for every `P` simultaneously — absurd (pick junk `P`). The bundles are unsatisfiable exactly in the regime they serve, so the L13-milestone keystones consuming them have unfillable `hInput`s. The satisfiable quantifier order is the per-`P` one of `Section5StrictDataFin` (`∀ u … ∀ P, hP → bundle`).

**The repair (`ArkLib/ToMathlib/OffcentreKeystoneAssembly.lean`, 11 declarations, all `[propext, Classical.choice, Quot.sound]`):** `Section5StrictDataOffcentreFin u P` — the first surface that is both **γ-free** (all series fields against the betaRec-built `gammaLocal`; no `hβ`/`hγ`/`hsubst` anywhere) and **per-`P`**. With it:
- `htailDeg_of_offcentre_representative` — off-centre tail producer from `hrep` alone (strictly simpler than the centred `TailDegProducer`: nothing to collapse);
- `hPz_offcentre_of_henselDatum` — per-z Hensel-uniqueness bridge at the Taylor-shifted representative;
- residual discharge + strict/closed keystone front doors (`δ_ε_correlatedAgreementCurves` from a per-`(u,P)` bundle producer);
- `section5DataOffcentreFin_of_producers` — assembly with `htailDeg` **derived**, not assumed;
- `section5DataOffcentreFin_of_producers_gradedDisc` — capstone at the **canonical** `B_coeff`: the `hcardFin` front is **fully discharged** by the graded weight collapse (`betaRec_weight_le_graded`, where the App-A.4 budgets `hbB`/`hbξ`/`hbW` are theorems) fed by the discriminant counting (`gradedConcreteFin_of_disc`).

**The exact remaining frontier** (per word `u`, decoded family `P`, all honest BCIKS20 obligations, no opaque objects):
1. GS factor bundle `b : GSFactorData.Bundle x₀` with `b.H` monic, `2 ≤ natDegreeY b.R`, paper grading `hR : degreeX (R.coeff j) ≤ D − j`;
2. Prop-5.5 local representative: `Ppoly` with `hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal …` and `hdegX ≤ 1` (linearity of the lift in Z);
3. `mpPoint` on `[k, deg Ppoly]` (PlaceGeometry + the L12 `hαβ` numerator reading);
4. per-z `HenselDatum` at the Taylor-shifted representative (§6.2 root data);
5. the §6 discriminant: nonzero `disc` with `hcover` and `|F| > gradedCardBudget(deg Ppoly) + deg disc`.

Recommend retargeting future keystone work at this surface; the `BetaCurveInput*` bundles and the legacy-`hβ` assembly should be treated as documentation of the old shape, not as fill targets.

=== COMMENT 2026-06-09T22:23:53Z ===
**Build repair pushed** (`51d6d1ad0`): `P2KeystoneReindex.lean` was broken on `main` by the `hasseCoeffRepr𝒪_cleared` k-parameter migration (two call sites with arity mismatches), blocking the entire MonicFaaDiBruno chain — repaired (explicit `k := natDegreeY p` + `le_refl`). Discovered while building step-(4)`'s descent theorem (`assembledLoc` + `map_embLoc_assembledLoc` + `assembledLoc_isRoot_of_monic`, drafted in scratch with the monic `W=1` simplification via `lift_mk'_spec` + `field_simp`); its verification resumes once the repaired chain builds.

=== COMMENT 2026-06-09T22:27:12Z ===
**Build-health report for the MonicFaaDiBruno chain** (blocking the `hαβ` step-4 verification): after the landed `P2KeystoneReindex` repair (`51d6d1ad0`), the chain still fails at `RestrictedFaaDiBrunoExtract.lean` with TWO independent breakages: (1) three more `hasseCoeffRepr𝒪_cleared` call sites with the pre-migration arity (lines ~899/922/986 — same fix shape as `51d6d1ad0`: add `k := natDegreeY p` + `le_refl`), and (2) **six duplicate declarations** colliding with `P2Reabsorb.lean` (`restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot` and five others declared in both files — an in-flight split/dedup). I repaired (1) locally and verified the k-fixes are correct, but reverted rather than unilaterally resolving (2) on a file under active refactor — flagging for whoever owns the migration. The step-4 descent theorem (`assembledLoc` / `map_embLoc_assembledLoc` / `assembledLoc_isRoot_of_monic`) is drafted and waits only on this chain building.

=== COMMENT 2026-06-09T22:38:32Z ===
## `hαβ` STEP (4) COMPLETE (`0e4a2f20d`, axiom-clean)

`AssembledRootDescent.lean`: **`assembledLoc_isRoot_of_monic`** — the localization preimage of the assembled Hensel series (coefficients `mk′(βHensel t, ξ^{2t−1})`, monic `W=1`) **is a root** of `R.map coeffHom_loc`, descended from the proven monic 𝕃-root through the injective `embLoc` (via `hom_eval₂` + the landed descent square), with `map_embLoc_assembledLoc` identifying the series under `embLoc` (`lift_mk′_spec` + `field_simp`).

**The "no in-tree lemma derives it" `hαβ` frontier now has proven localization-level root facts at canonical preimages.** Remaining: step (5) — transport through `π̂_z` (landed, ring hom to `F`) to get the `PlaceGeometry` root fact + read off coefficients (`π̂_z(mk′(β,ξ^n)) = π_z(β)/x^n`, the same `lift_mk′_spec` pattern) into the landed `bridgeData_of_mul_form`. Both are the **same transport pattern as step (4), one ring further down** — no new mathematics.

=== COMMENT 2026-06-09T22:42:58Z ===
## Bridge landed: gammaLocal(BcoeffSigned) = gammaGenuine for monic H (`a355b57e2`, axiom-clean) + four-front scout synthesis + one fidelity question

**The monic genuine identification** (`ArkLib/ToMathlib/BetaRecGenuineBridge.lean`, 8 declarations, all `[propext, Classical.choice, Quot.sound]`): `betaRec` at the sign-flipped canonical family `BcoeffSigned := fun i₁ p => -(B_coeff H x₀ R i₁ p)` equals `βHensel` at every order (strong induction; the global (A.1) minus is absorbed per-term, filters/exponents coincide definitionally, products via `partitionProd_eq_prod_count`). Hence:
- `gammaLocal (BcoeffSigned) = βHenselAssembled` unconditionally, and
- **for monic H: `gammaLocal (BcoeffSigned) = gammaGenuine`** (via the proven `restrictedFaaDiBrunoMatch_of_monic` + `P2MatchRoot` equivalences), with the coefficient form `αFromBeta (BcoeffSigned) t = αGenuine t`.

Every `gammaLocal`-field of the satisfiable off-centre bundle (monic case) is now a statement about the genuine analytic Hensel root, where `gammaGenuine_root`, `ζ_ne_zero`, `claim58prime_genuine_of_monic`, and `gammaGenuine_Z_linear_of_coeffs_Z_linear` are already proven. This also closes ONE of the two gaps blocking the L12 `hαβ` reading (the betaRec↔βHensel identification); the remaining gap is a π_z place-specialization-of-quotients lemma (coefficient-wise place image of the lift identity at good z).

**Four-front scout synthesis** (adversarially critiqued): the genuinely open kernels are now exactly (a) the π_z quotient-specialization lemma for `hαβ` (mechanical-ish, next up), (b) **Claim 5.9 Z-linearity** of the per-coefficient `αGenuine t` (research-grade; `S5Genuine.gammaGenuine_Z_linear_of_coeffs_Z_linear` isolates it), (c) the per-z matching polynomial `f_z`/`a₀` construction from the specialized GS interpolant (moderate; `GSSpecializedConditions.specialized_conditions` is proven), (d) per-good-z rational-root existence, (e) char-p inseparable-factor descent (named hypothesis, `GSDiscriminantOverRatFunc.lean:43-47`). The separability front is essentially DONE in-tree (`DiscriminantSeparable[Converse].lean`, `FractionFieldSeparable.lean`, `GSDiscriminantOverRatFunc.lean`) — the next brick is the per-z separability supplier from the keystone's own `disc` (unifying the `gradedConcreteFin_of_disc` counting input with `PlaceGeometry.hsep`).

**Fidelity question for verification (possible F-series finding).** The linear-representative route forces the decoded family to be **X-linear**: the `hPz` conclusion `P z = ((map C v₀) + (C X)·(map C v₁)).eval (C z)` computes to `C (v₀.eval z) + X · C (v₁.eval z)` (degree ≤ 1 in X), and `curveCoeffPolys_of_linear_representative` (BetaToCurveCoeffPolys.lean:135-154) accordingly takes `B j := 0` for `j ≥ 2` — asserting `(P z).coeff j = 0` on the good set for `2 ≤ j < deg`. Faithful §6.2 for curves should give `P z = ∑_t z^t·q_t` (arbitrary X-degree < deg, coefficient functions of Z-degree ≤ k), i.e. nontrivial `B j` for all `j < deg`. As stated, every bundle whose `hPz` uses this eval shape (centred `Section5StrictData[Fin]`, `BetaCurveInput*`, and my `Section5StrictDataOffcentreFin`, which mirrored it) can only be instantiated when every good fold decodes to an affine polynomial — i.e. effectively `deg ≤ 2`. Either the X/Z roles in the Prop-5.5 rendering are transposed (the v's should be X-polynomials of degree < deg appearing as `v₀ + (C z) • v₁`, with Z-linearity carried by the representative's Z-slot), or the intended instantiation genuinely targets X-linear families — requesting an adversarial check by whoever holds the Prop55/Claim-5.9 rendering context. The keystone theorems remain sound either way; this is a satisfiability-scope question at instantiation time.

=== COMMENT 2026-06-09T22:44:13Z ===
## The keystone surface is now pinned to the GENUINE Hensel root (monic case) — `977d568ed`, `fc1f937eb`, axiom-clean

Two coordinated bricks (with the fleet's `BetaRecGenuineBridge` work, whose main induction I repaired):

**1. The recursion bridge** (`BetaRecGenuineBridge.lean`): `betaRec` at the sign-flipped canonical family `BcoeffSigned := −B_coeff` equals the concrete (A.1) recursion `βHensel` at every order (the global minus of (A.1) is absorbed by the linear Bcoeff slot; everything else matches definitionally). Consequences: `gammaLocal … BcoeffSigned = βHenselAssembled`, and — through the **proven monic Faà-di-Bruno match** — `gammaLocal … BcoeffSigned = gammaGenuine` for monic `H` (+ the coefficient form `αFromBeta … t = αGenuine t`).

**2. The genuine-monic capstone** (`GenuineMonicCapstone.lean`): the graded App-A.4 weight collapse and the discriminant-fed `hcardFin` family transported to `BcoeffSigned` (Λ-weight is negation-invariant), and `section5DataOffcentreFin_of_producers_genuineMonic` — the satisfiable per-`P` off-centre bundle from producers whose series-level hypotheses are stated against **`gammaGenuine` directly**.

**Net effect**: the keystone consumer chain (off-centre per-`P` bundle → `StrictCoeffPolysResidual` → `δ_ε_correlatedAgreementCurves` strict) and the analytic producer chain (`gammaGenuine_root`, `ζ_ne_zero`, the S5Genuine route, the in-flight hαβ descent) now speak the **same object**. For monic GS factors the remaining frontier is exactly:
1. GS bundle (monic `H`, `2 ≤ d_R`, paper grading `hR`);
2. genuine Prop-5.5 representative (`Ppoly`, `hrep : polyToPowerSeries𝕃 H Ppoly = gammaGenuine`, `hdegX ≤ 1`);
3. per-point matching data `mpPoint` at `BcoeffSigned` (= the `βHensel` numerator readings — the hαβ/L12 lane, in progress via `AssembledRootDescent`);
4. per-`z` Hensel root data against `trunc k gammaGenuine`;
5. §6 discriminant counting (`disc`/`hcover`/`|F|` bound).

No recursion-capsule artifacts, no legacy `β`/`γ`, no `hsubst` anywhere in the obligations.

=== COMMENT 2026-06-09T22:45:41Z ===
## THE `hαβ` CONSTRUCTION IS COMPLETE (`3326a5570`, axiom-clean)

`LocalHenselSeries.lean` lands the final two steps: **`localSeries`** (the concrete local Hensel-root series at the place `z` — the `π̂_z`-image of the localization preimage), **`localSeries_isRoot_of_monic`** (it is a root of the specialized polynomial — forward transport of the descended root), and **`coeff_localSeries_mul`** (`coeff t · x^{2t−1} = π_z(βHensel t)` — exactly the landed `bridgeData_of_mul_form` supplier shape, via `mk′_spec` + `congrArg π̂_z` + `π_hat_z_comp`).

**All five steps of the plan are now proven theorems** (`π̂_z` / `embLoc`+injectivity / `emb_mk_C` / descent square + descended root / transport + read-off). The input documented in-tree as *"the genuine §5.2.6/App-A.4 frontier — there is no in-tree lemma that derives it"* is **constructed** for monic `H`. Remaining to fire `mpFin`: identify `localSeries`/the specialized polynomial with `PlaceGeometry.f`/`aβ` (plumbing — the `f z` arrives from the same Hensel-datum chain) and feed the GS congruence/separability data already carried there. Together with the closed weight chain, the landed cardinality/discriminant chains, and `hPz`, **every item of the #304 producer list is now either proven or reduced to interface plumbing.**

=== COMMENT 2026-06-09T22:47:45Z ===
**PlaceGeometry plumbing LANDED** (`2ed6ffd27`, axiom-clean): `placeGeometry_of_localSeries` — the constructor packaging the completed `hαβ` construction into the `PlaceGeometry` interface: `f` := the `π̂_z`-specialized polynomial, `aβ` := `localSeries` with its **proven** root fact, `a₀` := `C(π_z(βHensel 0))` with the congruence from the `t=0` read-off (`constantCoeff_localSeries`, the `ξ`-power truncates at `t=0`). Remaining inputs are exclusively **GS-side**: the proximate root `aP` (root + congruence, from the GS matching-factor divisibility) and separability — exactly the Hensel-datum chain's cargo. The `hαβ`/`aβ` half of `PlaceGeometry` is fully discharged; with `bridgeData_of_mul_form` + `coeff_localSeries_mul` supplying the `BridgeData` reading, the `mpFin` producer now needs only the GS-side `aP` identification.

=== COMMENT 2026-06-09T22:49:03Z ===
## Consolidated frontier after the genuine-monic capstone wave (2026-06-09 PM)

The off-centre surface is now fully wired to the genuine analytic objects, monic case:

- `OffcentreKeystoneAssembly` (bdc534b24): the satisfiable per-`P`, γ-free §5 bundle + producers + front doors.
- `BetaRecGenuineBridge` (a355b57e2): `betaRec(BcoeffSigned) = βHensel` and — via the proven monic Faà-di-Bruno match — `gammaLocal(BcoeffSigned) = gammaGenuine` for monic H. The capsule and Appendix-A developments are one object.
- `GenuineMonicCapstone` (fc1f937eb): the signed graded collapse + `section5DataOffcentreFin_of_producers_genuineMonic` — the bundle from gammaGenuine-stated producers, `hcardFin` discharged.
- `SignedGradedSupply` (d4fc8772d): `betaRec_weight_le_graded_of_budget` — the graded collapse with the coefficient budget abstracted (any future Bcoeff family gets the collapse + hcardFin from its budget alone; no htele re-derivation).
- `PlaceSeriesCanonical`: the canonical per-place series `aBetaPlace` making the L12 `hαβ` slot definitional; `AssembledRootDescent` (13da89d36) progressing the root facts.

**Remaining per-word inputs of the genuine-monic capstone** (all stated against `gammaGenuine`, all honest BCIKS20 obligations):
1. `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine …` + `hdegX ≤ 1` — genuine Prop 5.5. `S5Genuine.claim58prime_genuine` gives the truncation half (from SβLarge + LiftIdentity, the latter PROVEN monic); `gammaGenuine_Z_linear_of_coeffs_Z_linear` isolates per-coefficient Z-linearity. **Check item for whoever takes this**: confirm the `gammaGenuine_Z_linear_target` shape (`functionFieldT`-linear) and the bundle's `hdegX`/`polyToPowerSeries𝕃` shape (inner-`degreeX ≤ 1`) encode the same Z-line before building the converter brick.
2. `mpPoint` at `BcoeffSigned` — per-z PlaceGeometry root facts for `aBetaPlace` (in progress: AssembledRootDescent).
3. per-z `HenselDatum` at the Taylor-shifted representative — 5 cores mapped (matching-poly embedding/recentering, a₀, roots-from-GS-divisibility, congruences, separability transfer); packaging constructors (`henselDatum_of_sepInput`/`_matchingDvdInput`) already proven; `GSSpecializedConditions` (S10 converse) supplies the per-z GS interpolant facts.
4. rational-root existence at good z (currently the `root` input) — from the GS factor structure.
5. the concrete discriminant polynomial (separability resultant × W/ξ denominators × root-existence locus) feeding the proven counting chain.

=== COMMENT 2026-06-09T22:50:37Z ===
**THE `mpFin` FIRING LANDED** (`26ef37e38`, axiom-clean): `matchingPoint_of_localSeries` — the full per-`(t,z)` `MatchingPoint` at the **signed canonical coefficients**, assembled from `placeGeometry_of_localSeries` + `bridgeData_of_mul_form`, with the L12 reading discharged by `coeff_localSeries_mul` through the `betaRec_BcoeffSigned_eq_βHensel` bridge (monic `w=1`, `e=2t−1`). **The `hαβ` frontier is now consumed end-to-end**: construction → reading → `PlaceGeometry` → `BridgeData` → `MatchingPoint`. Remaining inputs are exclusively GS-side cargo (proximate root `aP`: root fact / congruence / index-`t` vanishing, plus per-`z` separability) — precisely what the GS matching-factor divisibility + Hensel-datum chain carries, and what the fleet's S-series discharges (S10 forward cover, char-0/char-p S5, today's Claim-1 dichotomy) are converging to supply.

=== COMMENT 2026-06-09T22:57:39Z ===
**GS-handshake interface complete** (`21d2a1e85`, axiom-clean): `matchingPoint_of_localSeries_dvd` — the per-`(t,z)` `MatchingPoint` now also fires from the **divisibility form** `(Y − C aP) ∣ f` (the exact GS matching-factor cargo shape, via `dvd_iff_isRoot`), mirroring the `mpFin_of_henselData`/`_dvd` route pair. The `mpFin` interface from the completed `hαβ` construction is now closed on both routes; what remains is purely the GS-side instantiation of `aP`/separability per `z` from the Hab25/GS chains the fleet is sweeping.

=== COMMENT 2026-06-09T22:58:10Z ===
## ⚠️ Transposed-representative finding (machine-checked) + the faithful surface — `b7d9cdd37`

**The finding** (`FaithfulCurveExtraction.lean`, axiom-clean): every in-tree §5 `hPz` field routes through the linear representative `((map C v₀) + (C X)·(map C v₁)).eval (C z)`, which by the in-tree `eval_linear_representative` equals `C (v₀(z)) + v₁(z) • X` — **always affine in the codeword variable** (`natDegree_linRep_eval_le_one`). Hence `no_linRep_of_nonaffine`: any decoded family with a single member of degree ≥ 2 at a good point refutes the existence of such a representative — i.e. the `hPz` field of **every** bundle (`Section5StrictData`, `Section5StrictDataFin`, `BetaCurveInput*`, and my `Section5StrictDataOffcentreFin`) is unsatisfiable for honest decoded families. The keystone consumers are all internally consistent theorems, but their extraction interface transposes [BCIKS20] Prop 5.5: the faithful shape is **low-degree in the curve parameter `z`** with full-degree codeword-polynomial coefficients (`P z = ∑_{t<n} (z−x₀)^t • c_t`, `n ≤ k+1`, `c_t ∈ F[X]` unrestricted), not affine in the codeword variable with `z`-polynomial coefficients. (Relatedly, the `hrep` fields equate `polyToPowerSeries𝕃`-series — whose coefficients lie in the base field `liftToFunctionField(F[X])` — with `γ`-series whose order-0 coefficient `α₀ = T/W` has `functionFieldT`-content; satisfiable only when the factor is fiber-linear, which is the §5 *conclusion*, not an assumable input.)

**The repaired interface** (same file): `curveCoeffPolys_of_curveFamily` — the faithful extraction with `B_j(w) := ∑_t (c_t).coeff j·(w−x₀)^t` of degree ≤ k; the per-`(u,P)` `CurveFamilyData` bundle (centre, ≤ k+1 codeword-poly coefficients, the per-`z` curve identity on the good set — literally the Prop-5.5 output); residual discharge + strict/closed keystone front doors reaching `δ_ε_correlatedAgreementCurves`.

**Recommended retarget**: producer work (per-z Hensel readings, the hαβ/AssembledRootDescent lane, the matching geometry) should aim at producing `CurveFamilyData` — concretely: γ-truncation (proven) + base-rationality of the truncated `αGenuine` coefficients (`αGenuine t = lift c_t` — the genuine §5 rational-section content, cf. `gammaGenuine_Z_linear_target`) + the per-`z` specialization reading `π_z(γ) = P z` give exactly `P z = ∑_{t<n} (z−x₀)^t • c_t`. The matching/weight/truncation machinery (ingredient C, L9/L10, graded collapse, the `BetaRecGenuineBridge` monic identification) is unaffected — only the final extraction interface changes. The `hPz`-shaped fields should be treated as refuted, not as fill targets.

=== COMMENT 2026-06-09T22:59:26Z ===
**Independent adversarial confirmation of the fidelity finding** (requested in comment 4664765160, resolved by `b7d9cdd37` FaithfulCurveExtraction): a separate deep-read of `BivariateDegree` (`degreeX f = f.support.sup fun n => (f.coeff n).natDegree`), the `hPz` eval shape, and the front-door types confirms **verdict (A) — genuine restriction**: `((map C v₀)+(C X)·(map C v₁)).eval (C z) = C (v₀.eval z) + X·C (v₁.eval z)`, so every bundle whose `hPz` uses the eval shape forces `(P z).natDegree ≤ 1` in the RS domain variable for ALL curve degrees k — instantiable only for affine decodings.

Survival map (what needs no change): `RS_goodCoeffsCurve`, all `HPzBridge` Hensel-uniqueness theorems (abstract over the identity shape), `exists_linear_decomposition_of_degreeX_le_one` (the decomposition is fine — the bug is how its output was *used*), all matching/weight/counting machinery, and the keystone front doors (conditional, sound). The faithful k=1 shape is `P z = v₀ + C z * v₁` with `v₀ v₁` RS-polynomials of natDegree < deg (general k: `P z = ∑_t C (z^t) * v t`), with the coefficient polynomials `B j = C (v₀.coeff j) + X · C (v₁.coeff j)` of z-degree ≤ k — exactly the `curveCoeffPolys_of_curveFamily` surface of `FaithfulCurveExtraction`. Bundles carrying the old eval-shaped `hPz` (`Section5StrictData[Fin]`, `BetaCurveInput*`, `Section5StrictDataOffcentreFin`) should be re-targeted at the curve-family surface before further producer work lands on them.

=== COMMENT 2026-06-09T22:59:33Z ===
**Per-`z` separability supply LANDED** (`bba7320a7`, axiom-clean): `specialized_separable_of_R_separable` — the `hsep` input of the `placeGeometry`/`matchingPoint` constructors is **derivable**: the specialized matching polynomial inherits `Separable` from `Y`-separability of `R` itself (the GS squarefree-factor condition), via `Separable.map` through both coefficient homs. **The per-`z` GS cargo for the `mpFin` chain now reduces to factor-level facts only**: `aP` divisibility + congruence + `R`-separability — no per-`z` analysis remains on the `hαβ`/geometry side.

=== COMMENT 2026-06-09T23:02:02Z ===
**Family-level `mpFin` supply LANDED** (`3e821254e`, axiom-clean): `mpFin_of_localSeries` — the exact `HcardDischarge`-shaped field (`∀ t ∈ [k,T], ∀ z ∈ matchingSet, MatchingPoint` at `BcoeffSigned`) assembled from the completed construction with **only factor-level inputs** (per-`z` unit condition, GS divisibility, order-0 matching congruence, index-vanishing window, one global `R`-separability). **Both inputs of the `αFromBeta`-vanishing discharge are now produced by this session's chains** (`mpFin_of_localSeries` + `hcardFin_of_graded`/`gradedConcreteFin_of_disc`). Meanwhile `b27e60b21` (fleet) lands per-`z` Hensel production of the faithful curve-family datum — the supply and demand sides of this interface are now converging in-tree.

=== COMMENT 2026-06-09T23:03:28Z ===
**Two-front handshake map** (coordination note after `b27e60b21` × this session's chains). The fleet's `CurveHenselDatum` (abstract per-`z` data → `strictCoeffPolysResidual` → Johnson CA) and this session's constructed route (`localSeries` → `MatchingPoint` → `HcardDischarge`) are two decompositions of the same §5/§6 content. Field-level map for whoever completes either:

| `CurveHenselDatum` field | constructed-route supplier |
|---|---|
| `f z` | `(R.map coeffHom_loc).map (map π̂_z)` — **constructed, with proven `aβ`-root** (`localSeries_isRoot_of_monic`) |
| `a₀ z` | `C(π_z(βHensel 0))` with the `t=0` congruence **proven** (`constantCoeff_localSeries`) |
| `hProot` | GS matching-factor divisibility (`matchingPoint_of_localSeries_dvd` input) |
| `hQroot` | the curve-specialization root — *the remaining identification* (`localSeries` = lift of the curve specialization; the `hPz`/`decoded_eq` content) |
| `hPapprox`/`hQapprox` | order-0 matching congruence (input on both routes) |
| `hderiv` | derivable: `Separable.map` (`specialized_separable_of_R_separable`) + `PlaceGeometry.hderiv` |

The single substantive item left on EITHER route is the `hQroot`-class identification; everything else is proven or interface-supplied on at least one side.

=== COMMENT 2026-06-09T23:05:00Z ===
## Satisfiability finding #3: the total `root` field is unsatisfiable for typical GS factors

`rationalRoot H z = {t_z // evalEval z t_z H = 0}` is a **subtype** (RationalFunctionsCore.lean:587), and every §5 bundle and producer carries the **total** family

```
root : (z : F) → rationalRoot (H_tilde' H) z
```

(`Section5StrictDataFin`, all `BetaCurveInput*`, `Section5StrictDataOffcentreFin` — mine, mirrored — and the producer/lemma signatures down through `BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large` (BetaMatchingVanishes.lean:219) and `IngredientC`/`MatchingVanishes`). This demands a rational point of the curve `H̃(z, ·) = 0` **over every `z ∈ F`** — for a typical irreducible GS factor (e.g. any `H̃` of `Y`-degree 2 that is not totally split fibrewise) the type is **empty** at the non-split `z`, so no total family exists and every such bundle is unsatisfiable regardless of the other fields.

The fix is cheap in principle because **every use of `root` is at matching-set members only** (the per-point `mp`-fields apply `root z` for `z ∈ matchingSet`; the Lemma-A.1 counting injects matching points into `elimPoly` roots via their `t_z`). The honest shape is the membership-restricted family

```
rootOn : (z : F) → z ∈ matchingSet → rationalRoot (H_tilde' H) z
```

with `mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet), MatchingPoint … t z (rootOn z hz)`, and restricted-root restatements of the consumer chain (`MatchingVanishes` → `embedding_eq_zero_of_matchingSet_large` → `tail_zero_*` → `gammaLocal_eq_trunc_*` → `curveCoeffPolys_of_betaRec_offcentreFin` → the bundle). The existing proofs should transport verbatim since they never evaluate `root` off the matching set. Supply side: `exists_common_root_of_mem_S_β` (RationalFunctionsCore.lean:2040) produces exactly the restricted family on `S_β`-style matching sets (choice over the existential per member).

Anyone building v2 bundle shapes (CurveFamilyData etc.): please adopt the restricted-root form — this is the third independent satisfiability defect in the bundle shapes after the legacy-`hβ`/`hγ` opacity and the ∀-P `hPz`.

=== COMMENT 2026-06-09T23:32:46Z ===
**Restricted-root ingredient-C chain LANDED** (`BetaMatchingVanishesOn.lean`, 8/8 axiom-clean): satisfiability finding #3 repaired. The §5 bundles' total root family `root : ∀ z, rationalRoot (H_tilde' H) z` is unsatisfiable for typical irreducible GS factors (empty fibres at non-split `z`); every use is at matching-set members only, so the honest shape is `rootOn : ∀ z ∈ matchingSet, …`. Landed: `MatchingVanishesOn` (restricted P(β)), total⟹restricted wiring, the restricted L14 bridge `matchingSet_subset_S_β_of_POn`, the restricted ingredient-C deliverable `embedding_eq_zero_of_matchingSet_largeOn`, `exists_rootOn_matchingVanishesOn_iff_subset_S_β` (the restricted family exists **iff** `↑matchingSet ⊆ S_β β` — the faithful form), the isEmpty separation theorems formalizing finding #3, and the `betaRec` keystone chain (Claim 5.8 hypothesis) in restricted form.

=== COMMENT 2026-06-09T23:40:45Z ===
## Genuine-side F5 repair landed (`bc8ff5ad5`, 6 declarations, axiom-clean)

`GenuineTruncationFin.lean`: the `∀ t ≥ k` largeness hypothesis of `claim58prime_genuine[_of_monic]` is production-circular (for large t one already needs the vanishing to bound the weight against a fixed agreement set — the same F5 pattern repaired on the capsule side by `HcardDischarge`). The repaired, finitely-producible chain:

- `claim58prime_genuine_fin_of_monic` — `gammaGenuine = trunc k` from `SβLargeAt` on **[k, T]** + the algebraic tail datum;
- `htailDeg_genuine_of_representative` — the tail datum from the genuine Prop-5.5 representative (`T := deg Ppoly`, pure coefficient reading);
- `weight_βHensel_le_graded` — `Λ(βHensel t) ≤` the graded budget (the recursion bridge × the signed graded collapse: the App-A.4 weight bound on the **concrete** (A.1) numerators is now a theorem);
- `SβLargeAtFin_of_graded_disc` — finite-range largeness from per-point vanishing (**existential** root form `∃ r, π_z r (βHensel t) = 0` — no total-root over-demand) + discriminant counting;
- `gammaGenuine_eq_trunc_of_graded_disc` — **capstone**: Claim 5.8′ from finite geometric data only.

The remaining input `hvanish` is exactly what `PlaceSeriesCanonical`/`AssembledRootDescent` are producing. A 5-front parallel forge is now running on: HenselDatum matching-poly + roots transport, a₀/congruence supply, the concrete discriminant product assembly, per-good-z rational-root supply, and an adversarial closure-audit of the `gammaGenuine_Z_linear_target` rendering (suspicion: span{1,T} is not multiplicatively closed for d_H > 2, so the target as stated may need the same fidelity treatment as the hPz shape).

=== COMMENT 2026-06-09T23:51:23Z ===
**Restricted-root §5 producers LANDED** (`MatchingGeometryProducersOn.lean`, 7/7 axiom-clean) — producer-side completion of the finding-#3 repair. Key structural fact: the supply machinery is genuinely per-point (`mkMatchingPoint_of_graph_vanishing` consumes one root at one place), so `mpPointOn_of_polyProximate_at_T` + the `mpFinOn_*` family re-thread it at `rootOn z hz` with zero analysis re-proven. `mpPoint_total_of_mpPointOn` = strictness bridge (restricted ⊇ total). `tail_zero_on_finite_rangeOn` / `tail_zero_of_finite_card_and_degreeOn` recover the **root-free** α-tail vanishing — everything `Section5StrictDataFin` extracts from its `root`/`mpFin`/`hcardFin` fields. ONE choke point remains, precisely located: the bundle's total-root **data field** `Section5StrictDataFin.root` (HcardDischarge.lean:207; `mpFin` its only typed consumer, `tail_zero_on_finite_range` the only use, members-only). Honest fix = field migration `root ↦ rootOn` in HcardDischarge/KeystoneAssembly + construction sites — both sides of that migration are now fully stocked.

=== COMMENT 2026-06-10T00:00:22Z ===
## Six-lane parallel harvest on the faithful surface (adversarially audited: 79/79 declarations axiom-clean)

All six remaining fronts attacked in parallel; every file independently recompiled + audited for F-traps (residual≡goal, unsatisfiable fields, vacuity). On main:

1. **`CurveFamilyZLinear.lean`** (12) — the Claim-5.9 bridge: the Z-linear target is EXACTLY its per-coefficient form (iff, no packaging slack); for monic `H` only the **windowed successor residual** (Z-deg-≤1 of `αGenuine t` for the finitely many `1 ≤ t < n`) remains, order-0 proven; the two-series curve form `γ = V₀ + C(T)·V₁` with explicit truncated base series; `CurvePlaceReading` + `curveFamilyData_of_placeReading` (audit note: that residual pair is a faithful §5-shape refactoring, jointly interderivable with the goal — honest naming, not a reduction). **Budget warning**: `n + m < k+2` forces `n < k` for an affine branch — producers must thread the combined GS budget.
2. **`CurveHenselDatumProducers.lean`** (10) — `hQroot`/`hQapprox` of the curve-Hensel datum **derived** from `TruncatedLocalRoot` + tail vanishing (no extra input for hQapprox); the GS-divisibility route (`MatchesGraph` ⟹ power-series root); congruences = constant-term facts; end-to-end `curveFamilyData_of_truncatedLocalRoot`. Remaining: the per-z base-rational reading `htrunc` + GS cargo at `P z`.
3. **`GSGradedBundle.lean`** (17) — (iii) `hdHD` proven for EVERY bundle; (iv)/(v) proven by **re-grading** `D := max b.D (gradedD)` (`selfGrade` = the minimal paper-grading degree); `GradedBundle.of_section5Inputs` from the identical honest GS inputs;残り = `MonicHighYResidual` (hmonic + hd2) — audit: likely needs the **monicized** bundle (normalizedFactors over `F[X]` are Y-leading-monic in `F[X]`, not 1).
4. **`ConditionDiscProduct.lean`** (24) — the multiplicative §6 discriminant assembly: product disc covers all per-z conditions; wired in-tree discs (`PerPlaceSep`, `elimPoly` of `ξ`/`W𝒪` — the per-place nonvanishing readings, from the proven global `ζ ≠ 0`); capstone in the exact `gradedCardBudget` shape. Honest residual: `RootSupplyOn` (rational-root existence is NOT a disc condition — `Y²−X` has ≈q/2 rootless places).
5. **`BetaTailDegreeVanishing.lean`** (11) — **the F5 tail closed at the recursion level**: the naive \[k,T\]-window propagation is FALSE (verified), but the empty-partition term is the exact obstruction, and `B_coeff(i₁,λ) = 0` for `i₁ > deg_X R` (the X-side dual, new) gives: window \[1,T₀\] + `deg_X R ≤ T₀` ⟹ `βHensel t = 0` for ALL `t ≥ 1`, transported to `αGenuine` (`htail_of_window_of_lift` = the exact `htail` the curve form consumes). Caveat (documented): at the un-recentered root this degenerates γ to a constant — non-degenerate use needs the recentered expansion.
6. **`CurveFamilyLines.lean`** (5) — anti-vacuity witnesses (the faithful surface provably accommodates degree-≥2 families that refute the old interface); the Theorem-1.4 lines front door; **numeric per-round wrappers** `epsCA_curves ≤ k·errorBound` / `epsCA ≤ errorBound` via the Errors.lean bridges — the exact quantities WHIR's `RoundKeystoneData`/`PerRoundProximityGap` and FRI's roundError consume (consumer map with file:line in the lane report).

**Cross-lane action items** (from the audit):
- The total `root : (z : F) → rationalRoot (H̃′ H) z` fields (in `Section5StrictDataOffcentreFin` and several producers) are **uninhabited types** for factors with rootless places — migrate to matching-set-restricted domain (`RootSupplyOn` shape).
- `MonicHighYResidual` discharge should target a monicized bundle (the interface permits any `Bundle`; `of_section5Inputs_H = H_graph` verbatim does not).
- The remaining deep cores, now minimized and consistently placed: the **windowed Claim-5.9 successor residual** (finite window, monic), the **per-z base-rational reading** `htrunc`, `MonicHighYResidual`, `RootSupplyOn`, and the per-z GS cargo at `P z`.

=== COMMENT 2026-06-10T00:16:40Z ===
## §5 producer lane repaired at restricted roots; `StrictCoeffPolysResidual` discharged from a satisfiable datum (`6e4c0934f`)

`ProximityGap/BCIKS20/StrictCoeffProducer.lean` — 14 declarations, 0 sorry, axiom-clean. Addresses the satisfiability finding (#3 in this thread): every prior producer demanded a **total** root family `root : (z : F) → rationalRoot (H̃' H) z` — unsatisfiable for GS factors not fibrewise totally split. This adopts restricted roots (`rootOn`, demands only at matching/good-set members; off-set extension by 0 with dite + proof-irrelevance transport) across all three repaired lanes:
1. counting branch (`tail_zero_on_finite_range_on`, `tail_zero_of_finite_card_and_degree_on`),
2. genuine-coefficient monic transport (`αGenuine_eq_zero_on_range_of_matching_monic_on`, `αGenuine_tail_zero_of_range_and_degree`),
3. Lane-2b analytic producers (`mpFin_of_localSeries_on`, `curveHenselDatum_of_truncatedLocalRoot{_genuine}_on`, `curveFamilyData_of_truncatedLocalRoot_on`).

**The weld:** `LocalSeriesDatumOn` (per-(u,P), every field an honest §5/§6.2 obligation) → `strictCoeffPolysResidual_of_localSeriesDatumOn` → **the issue-named `StrictCoeffPolysResidual` (Curves.lean:2505)** → `correlatedAgreement_affine_curves_johnson_of_localSeriesDatumOn_strict` (the §5 keystone `δ_ε_correlatedAgreementCurves`, strict Johnson). End-to-end chain typechecks. Two capstones derive `hvanish`: graded-discriminant matching (`localSeriesDatumOn_of_matching_gradedDisc`) and `SβLargeAt` via monic Claim 5.8′.

**Recon confirmations:** `BoundaryCardResidual` is **refuted as stated** (in-tree `ZMod 5` witnesses per this thread) — `BoundaryProbabilityResidual` is the honest boundary surface and remains the open assumption. The previously-localized "two tractable residuals" of descended Claim 5.7 were already discharged in `scratch/DescendedDegreeSumBundle.lean`.

Remaining open core: producing `LocalSeriesDatumOn` itself from raw GS output (the per-(u,P) local-series cargo), and the §6.2 boundary probability.


=== COMMENT 2026-06-10T01:09:19Z ===
**O70 landed (a0286bd53): `StrictCoeffPolysResidual` ≡ its large-good-set restriction.**

`BCIKS20/StrictCoeffLargeReduction.lean` (axiom-clean, 0 sorry): the §5 strict Johnson extraction residual holds **iff** its restriction adding `k + 1 < |RS_goodCoeffsCurve u δ|` holds. The small sector is discharged *unconditionally* — for any decoded family, with no probability/Johnson/GS/counting input — by Lagrange interpolation (`exists_coeff_interpolant_of_card_le`). The cutoff is exact: probe over GF(13) gives 4000/4000 small-set passes and 1861/2000 generic failures at `|S| = k+2` (the `(p-1)/p` rate).

Practical effect for every §5 producer lane (betaRec / Hensel / curve-extraction in `KeystoneStrictResidual`, `CurveFamilyHensel`, `FaithfulCurveExtraction`, `OffcentreKeystoneAssembly`, `StrictCoeffProducer`): you may now assume the good set is large for free via the new front door `correlatedAgreement_affine_curves_of_largeResidual` — large-matching-set counting hypotheses are only ever demanded where the good set is itself large.

The genuine open core of this issue is now strictly the **large sector**. BoundaryCardResidual analysis in progress separately.

=== COMMENT 2026-06-10T01:27:50Z ===
**O76 landed (044eca81f): `BoundaryCardStrictInteriorResidual` refuted — both quantization leaves die as bare nonemptiness; corrected statement shipped.**

`BoundaryCardStrictInteriorRefutation.lean` (axiom-clean): kernel-checked witness at k=1, deg=2, n=4 over GF(5) with boundary δ = 1−√(1/2) (deg·n = 8 non-square ⟹ genuinely non-lattice, `boundary_floor_lt`). The floor-matched strict radius has a nonempty good set yet joint agreement fails — so the strict-interior supply that `boundaryCardResidual_of_not_lattice` reduces the entire non-lattice bulk to is **false as stated**. Bonus: the first refutation of bare `BoundaryCardResidual` at a **non-square** endpoint (prior in-tree refutations were square-only) — nonemptiness now fails on both branches of the lattice dichotomy.

**The corrected obligation** (carrying the §5 probability threshold at a floor-matched radius) survives the witness (Pr[good] = 0.2 ≤ k·ε = 0.8) and is wired to the consumer via `correlatedAgreementCurves_boundary_of_floorEq_strict`.

**State of #304 after this session:** §5 core = large-sector only (O70); §6.2 core = the corrected threshold statement only (O76). Both bare-nonemptiness forms are dead. The honest remaining work is exactly: large-sector strict coefficient extraction + the corrected boundary threshold.

=== COMMENT 2026-06-10T02:05:10Z ===
**O79 (4a235bb65):** the corrected boundary route's probability-threshold monotonicity is proven — `prob_threshold_floorCell_mono` + `correlatedAgreementCurves_floorCell_mono` (monotone-ε, strengthening O76's same-ε transport) + the composite export `correlatedAgreementCurves_boundary_of_floorCell_mono`. The remaining boundary input is now exactly: the genuine §5 strict-interior producer at one strict radius per floor cell (BCIKS20 Steps 5–7 content) + the genuinely-square lattice branch behind `BoundaryCardLatticeData`. Probe survives at 4 parameter points (incl. q=257, k=2) with the deg=0 control confirming the hypothesis is load-bearing.

=== COMMENT 2026-06-10T02:11:06Z ===
## Wave-1 forge results: HenselDatum lane closed to its GS inputs + Claim 5.9 rendering REFUTED as stated

Five parallel builders + adversarial audits (all axiom-clean, on main):

**1. `HenselMatchingPolySupply.lean` (audit: PASS).** The HenselDatum obligation moved one coefficient ring down: `InterpolantInput` (F[X][Y]-level bundle: per-z GS interpolant family + two matching divisibilities + order-0 agreement + separability) with `henselDatum_of_interpolantInput`, `henselDatum_of_orderM_and_count` (consuming `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`'s exact shape), and `hPz_of_interpolantInput` — **end-to-end from the GS interpolant surface to the `hPz` field**.

**2. `HenselApproxSupply.lean`.** The a₀/congruence supply: canonical `a₀ z := C ((P z).coeff 0)`, both `hPapprox`/`hQapprox` families from order-0 agreement, `SepHenselInput` packager.

**3. `RationalRootSupply.lean`** (front 4 CLOSED to its branch hypotheses). The §5 rational-root producer: `rationalRoot_of_matching_branch` — from `Q = H·G`, `MatchesGraph Q P`, and branch separation at z, a `rationalRoot (H_tilde' H) z` with value `lc_H(z)·P(z)`; plus `mem_S_β_of_rep` glue matching `SβLargeAtFin_of_graded_disc`'s `hvanish` shape.

**4. Discriminant assembly: DUPLICATE** — fully covered by `ConditionDiscProduct.lean` (n-ary product, cover, degree bound). Front 5 needs only the per-factor certificates, which `PerPlaceSeparabilitySupply` started.

**5. `ZLinearClosureAudit.lean` — THE BIG ONE: a third F-series finding.** `gammaGenuine_Z_linear_target` (S5Genuine.lean:402) is a **Z↦T transposition** of paper Claim 5.9. Machine-checked: (a) the faithful ground-Z rendering is **FALSE for every d_H ≥ 2** (refuted at t=0: α₀ = T/W is off the ground line — `not_gammaGenuine_paperZ_linear`); it forces d_H = 1 (collapse). (b) The in-tree T-form target is refuted **generically**: `not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff` (the target ⟹ IsUnit(lc H)). (c) Span-closure dichotomy: `lift(F[X]) + T·lift(F[X])` is multiplicatively closed **iff d_H ≤ 2** (`functionFieldT_sq_no_T_repr` for d_H ≥ 3). **Consequence: stop attacking `gammaGenuine_Z_linear_target` as a fixed-curve statement** — the §5.2.7 content is per-place/collapse-shaped; the right consumer is the `CurveFamilyZLinear` per-place reading route.

**Wave 2 running** (7 agents): audits for 2/3/5 + builders for (i) `InterpolantInput` from the S10-converse GS chain, (ii) `hvanish` from mpPoint families via the recursion bridge (MatchingPoint.pi_z_eq_zero at BcoeffSigned IS the βHensel vanishing), (iii) the faithful-hPz off-centre bundle re-target, (iv) the order-0 agreement honest source.

