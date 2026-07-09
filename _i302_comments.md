=== comment 0 (lalalune) ===
Landed a partial toward this issue: recovered `mca_johnson_bound_CONJECTURE_smallField` (`4502050cd`, axiom-clean), which a 2026-06-09 lost-proof archaeology found verified on an off-main branch (commit `8504a4eed`, `MCAJohnsonSmallField_keep.lean`) but never merged.

It proves the Johnson MCA conjecture in the **small-field regime** `|F| ≤ (parℓ-1)·2^{2m}·10^7`, where `errStar δ ≥ 1` so `Pr ≤ 1 ≤ errStar` holds vacuously. The proof bounds `min_val = min(1-√ρ-δ, √ρ/20) ≤ 1/20`, so `(2·min_val)^7 ≤ 10^{-7}`, giving `errStar ≥ (parℓ-1)2^{2m}·10^7/|F| ≥ 1`.

This is a verified boundary lemma, not the open content: the **large-field regime** (`errStar < 1`, where RS Johnson list-decoding combinatorics bite — Hab25 §3 S4/S5/S6: GS bivariate interpolation over `K=F(Z)` + Hensel lift) remains the genuine obligation tracked here.

=== comment 1 (lalalune) ===
## Hab25 S4 factorization suite + unconditional per-round keystone bounds landed (axiom-clean)

1. **`GSFactorizationOverRatFunc.lean`** — the tractable core of Step S4 (on top of discharged S2/S3): S4(a) UFD factorization of the GS interpolant over `(RatFunc F)[X][Y]` (`gs_interpolant_factorization`); S4(b) decoded linear factors `Y − C p` are irreducible/prime and associates of members of `factors Q` (`decoded_linearFactor_mem_factors`); S4(c) associated monic linear factors are EQUAL, so distinct decoded messages index DISTINCT irreducible factors — `Ps.card ≤ (factors Q).toFinset.card` (`card_le_card_distinct_factors`); capstone `gs_factorization_index_structure`. Honest: deep S4→S6 (factors `= (Y−(a+Zb))^{p^f}` via discriminant S5 + Hensel S6) not claimed.
2. **`KeystoneSmallField.lean`** — `keystone_curves_bound_of_card_le(_e7)`: the §1.1 per-round bound `epsCA_curves ≤ k·errorBound` (the exact quantity the WHIR keystone reduction consumes) with NO residual hypotheses, for `q ≤ k·n` resp. `q ≤ k·deg²·10⁷` (composing the #304 unconditional CA through the numeric bridge).

Remaining for #302: S5 (discriminant), S6 (Hensel lift), and the large-field MCA bound.

=== comment 2 (lalalune) ===
## Hab25 S5 tractable core landed (axiom-clean, `f6fc02ab9`)

Two new files discharge the **degree + avoidance + specialization** content of Step S5 (discriminant non-vanishing), on top of the S4 factorization suite:

1. **`ArkLib/ToMathlib/ResultantDegreeBound.lean`** — the S5 degree estimate, Mathlib-only, any `CommRing`:
   - `natDegree_det_le`: determinant of a matrix of polynomials with entry degrees ≤ B has degree ≤ card·B;
   - `natDegree_resultant_le`: `deg_X Res_Y(f,g) ≤ (m+n)·B` for `f g : R[X][Y]` with coefficient X-degrees ≤ B;
   - `natDegree_discr_le`: `deg_X disc_Y(f) ≤ (2·deg_Y f − 1)·B` — the paper's `deg_X disc_Y(Q) < ℓ²ρn` shape.

2. **`ArkLib/Data/CodingTheory/GuruswamiSudan/GSDiscriminantOverRatFunc.lean`** — the S5 capstone over `K = F(Z)`:
   - `exists_common_eval_ne_zero`: ≤ N nonzero avoidance polynomials of degree ≤ D cannot all vanish on n > N·D distinct points (the "for |F| > ℓ²ρn there is x₀" step);
   - `exists_good_specialization_point`: with avoidance polynomial `disc_Y(R)·leadingCoeff_Y(R)` (degree ≤ 2LB), there is a **common** lifted domain point x₀ at which *every* factor specializes `X ↦ x₀` to a **nonzero, degree-preserved, separable** polynomial in `K[Y]` — exactly the Hensel-lift (S6) launch pad;
   - `gs_interpolant_good_specialization`: the above packaged onto the S4 `gs_interpolant_factorization` of the generic-fold GS interpolant.

**Honest residuals per factor** (not claimed): `discr R ≠ 0` — separability of the irreducible factor, which can genuinely fail in char p (the `R(X, Y^{p^f})` inseparable case the paper descends through); and the S3 factor degree data (Y-degree ≤ L, coefficient X-degrees ≤ B).

Remaining for #302: factor separable-core descent (the char-p half of S5), S6 (Hensel lift → unique affine pairs), and the large-field MCA assembly into `Hab25JohnsonResiduals`.

=== comment 3 (lalalune) ===
## S5 factor degree residuals discharged (axiom-clean, `ffb180ced`)

`GSFactorDegreeOverRatFunc.lean`: divisors of the GS interpolant inherit its degree data in **both** variables, so the S5 capstone no longer assumes any per-factor degree hypotheses:

- `degreeX_le_natWeightedDegree` + `conditions_degreeX_le`: the `(1, k−1)`-weighted `Q_deg` bound gives `degreeX Q ≤ gs_degree_bound k n m` — the X-half of [BCIKS20, Claim 5.4] over `K = F(Z)` (Y-half was `genericInterpolant_yDegree_le`);
- `degreeX_le_of_dvd` / `coeff_natDegree_le_degreeX_of_dvd`: X-degree is monotone under divisibility (`degreeX_mul` additivity over the domain `K[X][Y]`); Y-side is `natDegree_le_of_dvd`;
- **`gs_interpolant_good_specialization_of_dvd`**: for any family `Rs` of positive-Y-degree divisors of `Q`, assuming only `discr R ≠ 0` per factor (the char-p separability residual) and the paper count `|Rs| · 2·(D/(k−1))·D < n` (the `deg_X disc_Y < ℓ²ρn` regime), a common good specialization point exists: every factor specializes to a nonzero, degree-preserved, separable polynomial in `K[Y]`.

S5 status: **complete except the char-p separable-core descent** (`R(X, Y^{p^f})`), which is part of the deep S4→S6 content. Next: the residual-free decoded-list separation at a good point (S5→S6 bridge).

=== comment 4 (lalalune) ===
## Residual-free S5→S6 bridge landed (axiom-clean, `78ee27bec`)

`GSDecodedSeparationOverRatFunc.lean` — the Hensel step needs distinct decoded branches to sit over **distinct fiber points** at the good base point `x₀`. That separating point now exists with **zero residual hypotheses** (no separability / char-p assumption — the avoidance polynomials are the pairwise differences `p − p'`, nonzero by construction):

- `exists_eval_injOn_point`: for `|Ps|²·D < n`, some evaluation point is injective on a finite list of degree-≤D polynomials (≤|Ps|² pairwise differences through the S5 avoidance engine);
- `gs_decoded_eval_injective`: packaged for the GS interpolant over `K = F(Z)` — the cardinality side is discharged **internally** by the S3/S4 list-size bound `|Ps| ≤ D/(k−1)`, so in the paper regime `(D/(k−1))²·(k−1) < n` (Hab25's `ℓ²ρn < n ≤ |F|` numerology) a lifted domain point separates *any* decoded list.

Current S5/S6 frontier:
- S5 complete except the char-p separable-core descent (`R(X, Y^{p^f})`);
- S6 (Hensel lift → unique affine pairs) is the remaining deep kernel; its base-point configuration (separable specializations via `gs_interpolant_good_specialization_of_dvd`, separated branches via `gs_decoded_eval_injective`) is now fully formalized.

=== comment 5 (lalalune) ===
## Step S5 fully proven in characteristic zero (axiom-clean, `9a43c3504`)

The last S5 residual (`discr R ≠ 0` per factor) is now a **theorem** whenever the function field is perfect — in particular in characteristic 0:

1. **`ArkLib/ToMathlib/DiscriminantSeparableConverse.lean`** — the converse bridge, Mathlib-only:
   - `discr_ne_zero_of_separable` (over a field): separable ⇒ coprime with derivative ⇒ default-size resultant ≠ 0 (`resultant_ne_zero`); padding the Sylvester size to `(d, d−1)` via `resultant_add_right_deg` costs only `lc^k`, and `resultant_deriv` lands `± lc·discr ≠ 0`;
   - `discr_ne_zero_of_separable_map` (domain version, via the `discr`/specialization commutation);
   - `discr_ne_zero_of_irreducible_of_perfectField_fractionRing`: irreducible + positive degree over a domain with perfect fraction field ⇒ `discr ≠ 0` (Gauss transport + `PerfectField.separable_of_irreducible`).

2. **`GSSeparabilityCharZero.lean`**:
   - `irreducible_discr_ne_zero_of_charZero`: every positive-Y-degree irreducible factor in `(RatFunc F)[X][Y]` has nonzero Y-discriminant for `CharZero F` (the `K(X)` char-0/perfect instance chain);
   - **`gs_interpolant_good_specialization_charZero`** — complete S5 in char 0, zero residuals: for any positive-Y-degree members of `factors Q`, in the paper regime `|Rs|·2·(D/(k−1))·D < n`, a common good specialization point exists (all factors specialize nonzero, degree-preserved, separable).

**Status of Hab25 §3 after this session** — S1–S5 are now: S2 ✓, S3 ✓ (both halves of Claim 5.4 over K), S4 tractable core ✓, S5 ✓ in char 0 / modulo separable-core descent in char p, plus the residual-free branch-separation bridge. The remaining deep kernel for the Johnson MCA bound is **S6 (Hensel lift → unique affine pairs)** + the char-p `R(X,Y^{p^f})` descent + the final S11 numeric assembly into `Hab25JohnsonResiduals`.

=== comment 6 (lalalune) ===
## Char-p S5: separable cores with nonzero discriminant (axiom-clean, `3d8811ea0`)

`GSSeparableContraction.lean` formalizes the paper's `R(X,Y) = R_sep(X, Y^{p^f})` inseparable-factor decomposition:

- `irreducible_factor_separable_contraction`: for `ExpChar F q`, every positive-Y-degree irreducible `R ∈ K[X][Y]` has a separable irreducible core `g` over `L = K(X)` with `expand L (q^m) g = R`, `deg g · q^m = deg_Y R`, and — the S5 payload — `discr g ≠ 0`. Chain: Gauss transport → `Irreducible.hasSeparableContraction` (Stacks 09H0) → `of_irreducible_expand`/`natDegree_expand` → the converse discriminant bridge.
- `factor_discr_ne_zero_or_contraction`: the separable/inseparable **dichotomy** — either `discr R ≠ 0` over `K[X]` directly (the `m = 0` branch, consumable by `gs_interpolant_good_specialization_of_dvd` as-is), or `R` is a genuine `q`-power expansion (`m ≥ 1`) of a smaller separable core.

**S5 ledger**: char 0 fully proven; char p now proven up to one quantitative step — descending the core `g` from `L[Y]` to `K[X][Y]` with controlled X-degrees (clear denominators / primitive part) so the avoidance engine runs on cores. After that, the only deep node left for the Johnson MCA bound is **S6 (Hensel → unique affine pairs)** + S11 assembly.

=== comment 7 (lalalune) ===
## Step S5 COMPLETE in every characteristic (axiom-clean, `5888d20b0`)

The "quantitative gap" from the last comment closed for free. Key observation: `expand` only *spreads* coefficients, so the separable core of a factor `R` is simply `G := contract (q^m) R ∈ K[X][Y]` — its Y-coefficients are literally Y-coefficients of `R`. No denominator clearing exists to be done.

`GSSeparableCoreDescent.lean`:
- `irreducible_factor_core_descent`: `expand (q^m) G = R` already over `K[X]` (map-injectivity), `deg G · q^m = deg_Y R`, `discr G ≠ 0` over `K[X]` (descends along the discr specialization commutation), and all coefficient X-degree bounds inherited verbatim (`coeff_contract`).
- **`gs_interpolant_good_specialization_expChar`** — Step S5, complete, for any `ExpChar F q`: a generic-fold GS interpolant with the Claim-5.4 degree data and UFD factorization, such that for any finite family of positive-Y-degree irreducible factors, in the regime `|Rs|·2·(D/(k−1))·D < n` a common lifted point `x₀` is good for the **separable cores of all factors simultaneously** (each specialization nonzero, degree-preserved, separable, with the `q`-power expansion bookkeeping). Zero residual hypotheses; `q = 1` recovers the char-0 form.

**Hab25 §3 ledger after this session**: S1 ✓ S2 ✓ S3 ✓ (both Claim-5.4 halves) S4 tractable core ✓ **S5 ✓ (all characteristics)**, plus the residual-free branch separation (`gs_decoded_eval_injective`). The remaining deep kernels for the Johnson MCA bound are exactly: **S6** (Hensel lift at `x₀` → unique affine pairs `a + Z·b`), the S4→S6 factor-shape identification `R = (Y−(a+Zb))^{p^f}`, and the **S11** numeric assembly into `Hab25JohnsonResiduals`.

=== comment 8 (lalalune) ===
## First S6 brick: Hensel branch rigidity (axiom-clean, `ce7790a83`)

`ArkLib/Data/Polynomial/HenselBranchRigidity.lean` — the **uniqueness half of the S6 Hensel lift**, transported from the in-tree power-series engine (`ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff`) along a new recentering embedding:

- `recenter x₀ : R[X] →+* R⟦X⟧` (Taylor expansion at `x₀`; injective, `constantCoeff ∘ recenter x₀ = evalRingHom x₀`);
- `branch_eq_of_fiber_eq`: two polynomial roots of `G : R[X][Y]` (the decoded-branch shape `(Y−Cp) ∣ G`) through the same fiber value over `x₀`, simple there, coincide;
- `branch_eq_of_fiber_eq_of_separable`: the simple-point hypothesis is **exactly the S5 payload** — `G(x₀,·)` separable (Bézout at the root makes every root simple);
- `branch_eq_of_fiber_eq_expand`: the char-p factor shape `R = expand(q^e) G` — branches fold onto core branches via the `q^e`-power, rigidity applies to the core, Frobenius injectivity (`sub_pow_expChar_pow`) recovers `p = p'`;
- `branch_evalAt_injOn`: at a good point, decoded branches of a factor **inject into the simple roots of the specialized core** — the S6 bookkeeping shape.

Composition now available end-to-end: S5 good point (`gs_interpolant_good_specialization_expChar`) ⇒ separable cores at `x₀` ⇒ branches pinned by fiber values (this brick) + distinct decoded polys separated across factors (`gs_decoded_eval_injective`). Remaining S6 content: the **existence/affineness** half — lifting the simple roots of the core to branches and showing the per-factor branch is affine in `Z` (`a + Z·b`), then the S10 cover + S11 numeric assembly into `Hab25JohnsonResiduals`.

=== comment 9 (lalalune) ===
## S6 bricks 2+3: unique branch through each simple fiber point + per-factor fiber count (axiom-clean, `6e9af7d0d`)

Additions to `HenselBranchRigidity.lean`:
- `existsUnique_branch_series`: for each **simple root** `c` of the specialized factor `G(x₀,·)` there is a **unique** power-series branch `γ ∈ R⟦T⟧` through `(x₀, c)` (root of the recentered factor with `constantCoeff γ = c`) — both halves of the abstract S6 Hensel lift at the good point, assembled from the in-tree engines;
- `card_branches_le_natDegree`: at a separable specialization point, the polynomial branches of a factor inject (`p ↦ p.eval x₀`) into the roots of `G(x₀,·)`, so `#branches ≤ deg_Y` — the S6 per-factor list-size bookkeeping;
- `eval_specialization_eq_zero`: branches specialize to roots (the gluing lemma).

**Session summary for #302** (11 axiom-clean files, all on main): S5 of Hab25 §3 is now fully proven in every characteristic (resultant/discriminant degree bounds → avoidance engine → factor degree inheritance → converse discriminant bridge → char-p separable-core contract-descent), plus the residual-free decoded-list separation, plus the S6 Hensel frame (recentering embedding, branch rigidity, unique branch existence, fiber counting).

**Remaining open (the genuinely deep kernels)**: (a) S6 affineness — the lifted branch of each factor is affine in `Z` (`a + Z·b`), i.e. the unique-affine-pair extraction (BCIKS20 §5 Steps 5–7 / App. C; needs the `Z`-degree analysis of the recentered power-series root); (b) the S10 cover `E = ⋃ E_{i,j}`; (c) S11 numeric assembly into `Hab25JohnsonResiduals` → `JohnsonNumericBound` → `mca_johnson_bound_CONJECTURE` large-field regime.

=== comment 10 (lalalune) ===
## S6 DEEP KERNEL PROVEN: the unique affine pair (axiom-clean, `b42a9d257`)

The deepest node of the Hab25 §3 endgame — *every decoded codeword of the generic fold is an affine pair* `p = a + Z·b` — is now a **theorem with zero residual hypotheses**, and the proof needs no Hensel machinery at all:

**Mechanism (Lagrange descent).** A decoded `p ∈ K[X]` (`K = F(Z)`) of degree < k agrees with the generic fold `f₀ + Z·f₁` on ≥ k evaluation points. The fold *values* are affine in Z and the *nodes* `ωᵢ` are F-rational — so `p` is the Lagrange interpolation of affine values through F-rational nodes. The Lagrange basis is defined over F and `interpolate` is linear in the values, hence `p = interpolate(f₀-vals) + Z·interpolate(f₁-vals) = a + Z·b` with `a, b ∈ F[X]`, deg < k.

`GSAffinePair.lean`:
- `Lagrange.map_interpolate` (+ `map_basis`, `map_basisDivisor`): interpolation commutes with field embeddings — Mathlib-ready;
- `affine_pair_of_agreement`: ≥ k agreements ⇒ `p = a + Z·b`, `a,b ∈ F[X]`, deg < k;
- `affine_pair_unique`: the pair is unique (1, Z independence via the injective `F[Z] → F(Z)`);
- `affine_pair_of_hammingDist`: distance form `Δ(p|_D, fold) + k ≤ n` — satisfied by every Johnson-regime decoded codeword. This is the `(a_{i,j}, b_{i,j})` payload of `Hab25JohnsonAlgebraicData`; the Z-specializations `a + z·b` are the per-z decoded polynomials the (already-proven) S7/S8 combinatorics consume.

**Updated deep-kernel ledger for the Johnson MCA bound**: S1–S5 ✓ (all characteristics), affine pairs ✓, branch rigidity/existence ✓, branch separation ✓. What remains: (i) the **S10 cover** — every per-z decoded codeword arises by specializing the K-decoded list (route: clear denominators of the GS interpolant to `F[Z][X][Y]` and specialize `Conditions` at good z, so `(Y−q_z) ∣ Q|_{Z=z}`); (ii) the **S11 numeric edge** (`JohnsonNumericBound`: scaled count → ε_mca ≤ johnsonBoundReal).

NB for the fleet: autosync twice grabbed broken intermediates of `GSAffinePair.lean` mid-iteration; `b42a9d257` is the verified-green state (keep `/tmp` backups when iterating on tracked files).

=== comment 11 (lalalune) ===
## S10 forward cover PROVEN: integer representative + total per-z specialization (axiom-clean, `2171fe8f0`)

`GSIntegerRepresentative.lean` removes the "Z := z is only a partial map on `K = F(Z)`" obstruction and proves the forward (divisibility) half of the Theorem-2 cover with **zero residual hypotheses**:

- `exists_integer_representative`: **two-level denominator clearing** — every `Q ∈ K[X][Y]` has `Q₀ ∈ F[Z][X][Y]` with `Q₀ ↦ C(C d)·Q`, `d ≠ 0` (common denominator over the doubly-finite coefficient set via `IsLocalization.exist_integer_multiples_of_finset`);
- `integer_representative_eval_eq_zero`: a decoded root of `Q` with integral `p` transfers to `eval p₀ Q₀ = 0` **already over `F[Z][X]`** (the `C(C d)` factor is a constant under evaluation, embedding injective);
- `specialized_linear_divisibility`: that root specializes at **every** `z ∈ F` — the `F[Z] → F` evaluation is total, so this side needs **no bad-z set and no `d(z) ≠ 0`**;
- **`decoded_affine_pair_divides_specialization`** (capstone): composed with the proven S6 affine pair — for every K-decoded codeword `p = a + Z·b` and every `z`: `(Y − C(a + z·b)) ∣ Q₀|_{Z:=z}`. The per-z decoded polynomials of *all* scalar folds divide the specialized integer interpolant; S4 factorization of `Q₀|_{Z:=z}` indexes the per-z exceptional sets.

**Deep-kernel ledger now**: S1–S5 ✓ (all char), S6 affine pair ✓, Hensel frame ✓, branch separation ✓, S10 forward cover ✓. Remaining: (i) S10 **converse** — every δ-close scalar fold's decoded polynomial comes from the K-level list (needs: specialized `Conditions` for `Q₀|_{Z:=z}` when `d(z) ≠ 0` — degree/multiplicity/nonzeroness survive specialization, finitely many bad z — then per-z `gs_divisibility`); (ii) **S11** numeric edge (`JohnsonNumericBound`).

=== comment 12 (lalalune) ===
## S10 converse PROVEN: GS Conditions survive specialization (axiom-clean, `2c5bbd1c2`)

`GSSpecializedConditions.lean` completes the **S10 divisibility bridge** — both directions now proven:

**Transfer machinery**: weighted degree drops under coefficientwise ring maps, is preserved by injective ones, and ignores the denominator constant `C(C d)`; the bivariate Taylor `shift` commutes with coefficientwise maps and absorbs constants; and the multiplicity bound *extracts* to order-<m shift-coefficient vanishing (converse of `rootMultiplicity_ge_of_shift_zero`, via `rootMultiplicity₀_ge_iff`).

**Capstones**:
- `specialized_conditions`: at **every** `z` with `Q₀|_{Z:=z} ≠ 0` (a cofinite set), the specialized integer interpolant is a valid GS interpolant for the scalar fold `f_z` — all four `Conditions` fields transfer (nonzeroness by hypothesis; degree by a 4-step chain through the integer representative; roots and multiplicity descended from K to `F[Z]` through the injective embedding, then re-specialized — the constant factor is a unit / scalar throughout);
- `scalar_fold_decoded_divides_specialization`: composed with in-tree `gs_divisibility` — **every Johnson-radius decoded codeword of every scalar fold divides `Q₀|_{Z:=z}`**.

With the forward half (`decoded_affine_pair_divides_specialization`: every K-level affine pair divides the same `Q₀|_{Z:=z}`), the per-z decoded lists of both sides land in the factor structure of the **same specialized polynomial**, whose factor count is capped by the S3 `Y`-degree bound. That is the complete divisibility skeleton of the Theorem-2 cover `E = ⋃ E_{i,j}`.

**Deep-kernel ledger**: S2 ✓ S3 ✓ S4-core ✓ S5 ✓ (all char) · S6 affine pair ✓ · Hensel rigidity/existence ✓ · branch separation ✓ · S10 forward ✓ · **S10 converse ✓**. The remaining unproven content for the Johnson MCA bound is now confined to: (i) assembling these bricks into the `Hab25JohnsonAlgebraicData` bundle fields (`Edis`/`Efactor`/`hcover`/`hImprove` — bookkeeping over the proven bridge, plus relating per-z decoded lists to the affine pairs via factor matching at the specialized level), and (ii) the **S11 numeric edge** (`JohnsonNumericBound`: the scaled `|E| ≤ ℓ·n` count → `ε_mca ≤ johnsonBoundReal`, probability-side accounting).

=== comment 13 (lalalune) ===
## S11 numeric edge PROVEN: the JohnsonNumericBound residual is no longer atomic (axiom-clean, in `Hab25NumericEdge.lean`)

The final step S11 — previously the *assumed* `hNumeric` field of `Hab25JohnsonResiduals` — is now derived:

- `epsMCA_le_card_div_card`: the probability side is **pure counting** — `ε_mca` is a sup of uniform probabilities, so a per-stack bad-scalar count `≤ N` gives `ε_mca ≤ N/|F|` (via `prob_uniform_eq_card_filter_div_card`);
- `johnsonNumericBound_of_count`: `JohnsonNumericBound` from the count plus the single closed-form real inequality `N/|F| ≤ johnsonBoundReal`;
- **`johnsonNumericBound_of_per_stack_cover` / `mca_johnson_of_per_stack_cover`**: the capstone — per-stack S10 cover data (factor index of size ≤ L, affine-pair difference vectors, cover, improvement property) feeds the *proven* `claim1_theorem2_integer` (`|E_u| ≤ L·n`), and with `L·n/|F| ≤ johnsonBoundReal` the Johnson-range MCA bound follows outright;
- `Hab25JohnsonResiduals.ofAlgebraicDataAndCover`: any algebraic-data bundle upgrades to the full residual bundle with `hNumeric` **derived**.

(Converges with the #68 plumbing in `Hab25JohnsonNumericBridge.lean` — same reduction, compatible interfaces.)

## Where #302's Johnson MCA bound stands after this session (18 axiom-clean files)

**Proven end-to-end**: S1 ✓ S2 ✓ S3 ✓ (both Claim-5.4 halves) S4 core ✓ **S5 ✓ all characteristics** · **S6 affine pair ✓** (Lagrange descent) · Hensel branch rigidity + unique branch existence + fiber counting ✓ · branch separation ✓ · **S10 divisibility bridge ✓ both directions** (integer representative; total forward specialization; Conditions survive at every good z; per-z GS divisibility) · **S11 counting + numeric reduction ✓**.

**The one remaining genuinely-open kernel**: producing the per-stack cover data itself — i.e., showing every bad scalar's decoded `q_z` matches some K-level affine pair at the disagreement coordinates (`hImprove`). The divisibility skeleton places both `(Y−C(a+z·b))` and `(Y−C q_z)` as factors of the *same* `Q₀|_{Z:=z}`; what's missing is the factor-matching step ruling out per-z decoded polynomials that divide only **nonlinear** irreducible factors of `Q` — the inseparable/Hensel `R = (Y−(a+Zb))^{p^f}` identification (BCIKS20 §5 Steps 5–7). The Hensel tools (rigidity, unique branches, separable cores at good points) are in place; the remaining argument needs the paper's exact counting mechanism (ePrint 2025/2110 is 403-blocked from this sandbox — flagging for an agent with paper access). Plus the closed-form parameter inequality `L·n/|F| ≤ johnsonBoundReal` at the Johnson parameters.

=== comment 14 (lalalune) ===
## Affine-capture cover landed: the Johnson MCA bound is now ONE named Prop away (axiom-clean, `ea9403a22`)

`Hab25AffineCapture.lean` builds the per-stack `Hab25JohnsonAlgebraicData` bundle — the input consumed by the in-tree S11 bridge (`JohnsonNumericBound.of_algebraic_cover_nat`, #68's `Hab25JohnsonNumericBridge`) — from a single named hypothesis per bad scalar:

- **`AffineCaptured`**: an `mcaEvent` witness set certifies the fold's closeness with the affine codeword `a + γ·b` itself (exactly what the proven S6 kernel `affine_pair_of_hammingDist` supplies for the K-decoded list);
- **`affineCaptured_improve`** — the mathematical heart, Hab25's "from the proof of Lemma 1" upgraded to the mutual setting: the `mcaEvent` *forbids joint agreement on the witness set*, so the capturing pair `(a,b)` must disagree with `(f₀,f₁)` **on** `S`; at such a coordinate the fold agreement kills the affine functional. This is precisely the `hImprove` obligation — derived, not assumed;
- **`exists_algebraicData_of_affine_capture`**: a ≤L capture list assembles the complete bundle (`Edis = hab25McaBadScalars`, `ℓ = L`);
- **`johnsonNumericBound_of_affine_capture`**: per-stack capture lists + the closed-form `L·n/|F| ≤ johnsonBoundReal` discharge the numeric residual end-to-end.

**Status of the Johnson MCA bound** (~20 axiom-clean files this campaign): S1–S5 ✓ all characteristics, S6 affine pair ✓, Hensel rigidity/existence ✓, S10 divisibility bridge ✓ both directions, S11 counting ✓ (in-tree), improvement lemma ✓, bundle assembly ✓. **The single remaining open kernel**: the capture hypothesis — every bad scalar's decoded codeword arises from a K-level affine pair (BCIKS20 §5 Steps 5–7: per-z decoded `q_z` cannot divide only *non-affine* irreducible factors of `Q₀|_{Z:=z}`). Note: a line-substitution/interpolation globalization for this FAILS (degree count `deg_X U ≤ B_X + e(τ−1)` is circular for `e ≥ 2`) — recorded so nobody retries it; the paper's Hensel mechanism is needed, and the ePrint PDF (2025/2110) is 403-blocked from the sandbox — someone with access should extract §3 S6's exact argument.

=== comment 15 (lalalune) ===
## Closed-form Johnson arithmetic discharged — the numeric side condition is gone (axiom-clean, in `Hab25JohnsonArithmetic.lean`)

The last numeric input of the affine-capture route is now a theorem:

- `hab25RhoPlus` / `hab25M` + `johnsonBoundReal_eq` (the `let`-parameters of the closed form, definitionally);
- **`nat_mul_card_div_le_johnsonBoundReal`**: whenever the per-stack list bound `L` is within the ℓ-budget `2(m+½)⁵/(3ρ₊^{3/2})` (≥ 350 at any rate ρ₊ ≤ 1, since m ≥ 3), the scaled count satisfies `(L·n)/|F| ≤ johnsonBoundReal` — the δ-cross-term and the `(m+½)/√ρ₊` term are nonnegative slack;
- **`johnsonNumericBound_of_affine_capture_of_list_le`**: per-stack affine-capture lists of budgeted size discharge `JohnsonNumericBound` outright — **no numeric side condition remains anywhere in the chain**.

(NB: converges with the concurrent `Hab25JohnsonArith.lean` — that file additionally proves `rhoPlus_le_two`/`johnson_key_arith` under `k ≤ n`; the two should be deduped once its in-flight edits settle. Also `Hab25NumericEdge.lean` was resurrected by autosync in its verified-green form and builds clean — harmless overlap with `Hab25JohnsonNumericBridge`, flagged for dedup.)

**Final reduction state for the Johnson MCA bound** (this campaign: ~22 axiom-clean files): everything — S1–S5 (all characteristics), S6 affine pairs, the Hensel frame, both S10 directions, S11 counting, the improvement lemma, bundle assembly, and the closed-form arithmetic — is **proven**. The Johnson MCA conjecture (`mca_johnson_bound_CONJECTURE` large-field regime) now reduces to exactly **one Prop**: *per-stack affine-capture lists of budgeted size exist* (`AffineCaptured` coverage — the BCIKS20 §5 Hensel factor-matching). Everything downstream (WHIR keystone → `whirVectorIOP_isSecureWithGap`) is already wired to consume it. One reconciliation layer also remains between the `epsMCA`-based Hab25 statement and the `hasMutualCorrAgreement`-based ABF26 statement in `MutualCorrAgreement.lean` (per-row `proximityCondition` vs `mcaEvent`, the one-way `Pr_proximityCondition_le_epsMCA` bridge).

=== comment 16 (lalalune) ===
## Closed-form parameter arithmetic done: the GS ℓ-shape fits the Johnson budget (axiom-clean, `ff797735b`)

`Hab25JohnsonArith.lean` (deduplicated against the concurrent `Hab25JohnsonArithmetic.lean` — it removes the colliding `johnsonBoundReal_eq`/mirror duplicates and composes with that file instead):

- `hab25RhoPlus_le_two` (`ρ₊ ≤ 2` for `k ≤ n`) and `johnson_key_arith` (`3ρ₊ ≤ 2(m+½)⁴` — i.e. `6 ≤ 300.125`, two orders of magnitude of slack);
- `list_shape_le_budget`: `(m+½)/√ρ₊ ≤ 2(m+½)⁵/(3ρ₊^{3/2})` — the paper's `D_Y < ℓ` **list-size shape** sits inside the quintic budget of `johnsonBoundReal`;
- **`johnsonNumericBound_of_affine_capture_of_list_shape`**: per-stack capture lists with `L ≤ (m+½)/√ρ₊` — the exact shape the GS machinery outputs — discharge the numeric residual outright.

## Final session ledger for the Johnson MCA bound (~22 axiom-clean files)

Every step of Hab25 §3 is now **proven** except one: S1 ✓ S2 ✓ S3 ✓ S4-core ✓ S5 ✓ (all characteristics) · S6 affine pair ✓ (Lagrange descent) · Hensel rigidity/existence/fiber-count ✓ · branch separation ✓ · S10 divisibility bridge ✓ (both directions) · S7–S10 combinatorics ✓ (pre-existing) · S11 counting ✓ · affine-capture bundle assembly ✓ (`hImprove` **derived**) · closed-form parameter arithmetic ✓.

**The single remaining open kernel**: per-stack `AffineCaptured` production — every `mcaEvent` bad scalar's witness is matched by one of `≤ ℓ` affine pairs. Its divisibility skeleton is fully proven (both per-z decoded codewords and affine-pair specializations divide the same `Q₀|_{Z:=z}`, with `≤ ℓ` factors); what's missing is exactly the BCIKS20 §5 Steps 5–7 factor-matching (no per-z codeword hides in a nonlinear factor — the `R = (Y−(a+Zb))^{p^f}` identification). Flagged for an agent with access to ePrint 2025/2110 (403-blocked here); all Hensel/separable-core tools needed for it are in tree.

=== comment 17 (lalalune) ===
## Paper obtained — Hab25 Claim 1 PROVEN faithfully (axiom-clean, `04509d279`)

ePrint 2025/2110 is now in hand (7pp; user supplied the PDF). **Full §3 mechanism, recorded here for the fleet:**

1. GS interpolant of `f₀+Z·f₁` over `K=F_q(Z)`, decomposed `Q(X,Y,Z) = C(X,Z)·∏ᵢ Rᵢ(X, Y^{p^{fᵢ}}, Z)^{eᵢ}`, each `Rᵢ` irreducible **and separable** (the contraction — our `GSSeparableCoreDescent`). Degrees: `D_Y < ℓ`, `D_X < ℓρn`, `D_{YZ} ≤ (ℓ³/6)ρn` [BCI⁺20 Claim 5.4].
2. `deg_X disc_Y(Q) < ℓ²ρn` ⇒ for `|F| > ℓ²ρn` (else trivial) there is `x₀ ∈ F` with `disc_Y Rᵢ(x₀,Y,Z) ≠ 0` ∀i — our S5.
3. `E = ⋃ᵢ Eᵢ` by which factor the proximate divides (`Rᵢ(X, p_z(X)^{p^{fᵢ}}, z) = 0`); **refined** `Eᵢ = ⋃ⱼ E_{i,j}` by the irreducible components `H_{i,j}(Y,Z)` of the *x₀-fiber* `Rᵢ(x₀,Y,Z) = ∏ⱼ H_{i,j}` ("the potentially different starting values of the Hensel lift"); `#(i,j) ≤ D_Y < ℓ`.
4. **Claim 1** (`|E_{i,j}| ≤ (ℓ⁶/3)(ρn)²`), *by contradiction*: above the threshold, `S_{x₀,R,H} = {z : R(X,p_z^{p^f},z)=0 ∧ H(p_z(x₀)^{p^f},z)=0}` exceeds `2·D_Y²·D_X·D_{YZ}` — **[BCI⁺20 Claim 5.7]** — which suffices for **[BCI⁺20 Steps 5–7 + App. C]** to force `Rᵢ(X,Y^{p^f},Z) = (Y−(a+Zb))^{p^f}`, making the proximate the *unique* affine pair `p_z = a+z·b`. Then every `z ∈ E_{i,j}` improves agreement beyond `A°`, and "from the proof of Lemma 1" ≤ `|D∖A°| ≤ n` scalars can do that — contradiction with `(m+½)⁶/(3ρ)·n² > n`.

**Formalized in `Hab25Claim1.lean`** (everything except the bracketed BCI⁺20 citation, which is pinned as the per-cell `hsteps57` hypothesis):
- `claim1_dichotomy` — the verbatim contradiction proof, composing the proven `affineCaptured_improve` ("must improve beyond A°") and `factorImprove_card_le_n` ("from the proof of Lemma 1");
- `hab25_threshold_gt_n` — the closing numerology `n < (m+½)⁶/(3ρ)·n²` (3.5⁶ ≈ 1838 > 3ρ);
- `theorem2_of_claim1_cells` — Theorem 2 reassembled: ≤ ℓ cells ⇒ `|E| ≤ ℓT = (ℓ⁷/3)(ρn)²`.

**The single remaining input is now exactly [BCI⁺20 (ePrint 2020/654) Claim 5.7 + Steps 5–7 + Appendix C]** — the large-incidence ⇒ affine-power identification. NB this is the SAME kernel family as the in-tree BCIKS20 §5/App-A formalization stream (#138/#139, the βHensel/HenselNumerator machinery — monic cases already proven there): the two issue streams converge on one kernel. All Hab25-side scaffolding (incidence sets, x₀-fiber components, Hensel branch tools) is in tree.

=== comment 18 (lalalune) ===
## BCIKS20 paper obtained + cell wiring landed (`a25ac581f`, axiom-clean)

**ePrint 2020/654 is now in hand** (curl with browser UA works; saved to `~/Downloads/2020-654-bciks20.{pdf,txt}`). Steps 5–7 extracted (full text in the repo-accessible txt):

- **Claim 5.7** (p.22) is a pure **pigeonhole**: for each `z ∈ S`, `Y−P_z ∣ Q(X,Y,z)` ⇒ some `i` with `Rᵢ(X,P_z,z)=0`; substituting `x₀` ⇒ some `j` with `H_{ij}(P_z(x₀),z)=0` where `Rᵢ(x₀,Y,Z) = Cᵢ(Z)·∏ⱼH_{ij}(Y,Z)`; ≤ `D_Y` pairs ⇒ the most common cell has `|S_{x₀,R,H}| ≥ |S|/D_Y > 2D_Y²D_X D_{YZ}`. *All ingredients of this are already proven in-tree* (per-z divisibility = our S10 bridge; fiber factorization; pigeonhole) — formalizable directly.
- **Step 5/6** (Claim 5.8, `α_t = 0` for `t > k`): the Hensel branch `γ = Σ α_t(X−x₀)^t` over the function field `L`; for `z ∈ S' = S_{x₀,R,H} ∖ {W,ξ zeros}`, `π_z(γ) = P_z` **by uniqueness of the Hensel lift at a simple root** (= our `branch_eq`/`root_unique` engines, over `L`), so `π_z(β_t) = 0` on `|S'| > d_H·Λ(β_t)` substitutions ⇒ `β_t = 0` by the Λ-weight zero count (Lemma A.1 + Claim A.2: `Λ(β_t) < (2t+1)dD`); then `γ = γ_k` exactly since `R(X,γ_k,Z)` has X-degree < `D_X`.
- **Step 7** (Claim 5.9): `γ`'s coefficients are Z-linear, `γ = v₀ + Z·v₁` — via agreement of `γ(x)` with a Z-linear function at ≥ `k+1` x-values (Lagrange-descent flavor, like our `GSAffinePair`).

**The `W, ξ, ζ, β_t, Λ`-weight objects are literally the in-tree `BCIKS20/HenselNumerator`/βHensel machinery (#138/#139)** — the open cores there (`AlphaGenuineRegularWeightLe`/Λ-weight regularity) are the Lemma A.1/Claim A.2 inputs of Step 6.

**Cell wiring landed** (`Hab25CellWiring.lean`): `bad_card_le_of_claim1_cells` (cells at threshold `T := n` ⇒ sharp `|E_u| ≤ L·n`) + `johnsonNumericBound_of_claim1_cells` (cells with `L` in the GS list shape ⇒ `JohnsonNumericBound`, through the surviving #68 bridge `of_card_le_nat` after `Hab25NumericEdge` was dedup-deleted — rerouted).

**Remaining wiring map** (for whoever picks up next):
1. *Claim 5.7 pigeonhole* — formalizable now from proven pieces (produces the cells + incidence);
2. *Steps 5–7 core* — the Λ-weight/β_t analysis = #138/#139 cores (both papers now available);
3. *pair-generator seam* — `hasMutualCorrAgreement (genRSC (Fin 2))` from `epsMCA ≤ …`: `Pr_proximityCondition_le_epsMCA` exists; needs one uniform-over-`Finset.image` PMF pushforward lemma (`Gen.Gen = image (fun r j => r^{exp j}) univ`, injective for exp=(0,1)) + the closed-form `johnsonBoundReal ≤ errStar` comparison;
4. *ℓ-ary extension* of the Hab25 chain (paper: "can be proven similarly, without additional technical obstacles") for general `parℓ` in `mca_johnson_bound_CONJECTURE`.

=== comment 19 (lalalune) ===
## BCIKS20 Claim 5.7, algebraic half PROVEN (axiom-clean, `e8097f00c`)

`GSFactorAssignment.lean` formalizes the assignment step of [BCI⁺20 Claim 5.7] (*"thus there is some i such that Y−P_z ∣ Rᵢ(X,Y,z)"*) over the integer model:

- integer representatives for **every** irreducible factor of the K-level interpolant (choice over the proven `exists_integer_representative`);
- the **unit-clearing identity** `C(C(cn·d))·∏(rep R)^{count R} = C(C(D·cd))·Q₀` in `F[Z][X][Y]` — UFD `factors_prod` + the double-constant shape of units of `K[X][Y]` (`Polynomial.isUnit_iff` twice) + `RatFunc.num/denom` clearing, transported through the injective pushforward;
- **`exists_specialized_factor_assignment`**: for every `z` outside the roots of `bad := cn·d` (cofinite), every decoded linear factor `(Y−Cq) ∣ Q₀|_{Z:=z}` divides the specialization of **some** factor's representative — `Y−Cq` is prime over the domain `F[X]`, so it routes through the product and the powers.

Composed with `scalar_fold_decoded_divides_specialization` (every bad scalar's decoded polynomial divides `Q₀|z`), this produces the Claim-5.7 **cell assignment** z ↦ factor. What remains of Claim 5.7 is bookkeeping (the x₀-fiber refinement j and the pigeonhole — both elementary); the remaining *deep* content is unchanged: Steps 5–7's `Λ`-weight/β_t analysis (#138/#139 cores, both papers local).

Lean gotchas recorded in the commit for the fleet: `rw` with under-applied generic `map_prod`/`map_mul` fails where the fully-applied term works; `← hQeq` rewrites `Q` underneath `factors Q` (pre-rewrite in a small equation instead); there is no standalone `(R)[Y]` notation — only the combined `R[X][Y]`.

=== comment 20 (lalalune) ===
## Pair-generator seam PROVEN (axiom-clean, `9b8b2972f`) — the WHIR-side wiring is closed for ℓ = 2

`MCAPairSeam.lean` closes the last structural seam between the ABF26/Hab25 `ε_mca` world and WHIR's `hasMutualCorrAgreement`:

- `pr_uniform_subtype_image`: uniform sampling from the image finset of an injective map **is** parameter sampling (pure counting: `prob_uniform_eq_card_filter_div_card` + a `Finset.card_bij`);
- **`hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`**: for the affine-line power generator (`parℓ = Fin 2`, exponents (0,1), combiner `(1, γ)`), any bound `ε_mca(C, δ) ≤ errStar δ` on the admissible range yields `hasMutualCorrAgreement (genRSC (Fin 2) φ m exp) B* errStar`. The combiner identification `(γ⁰, γ¹) = (1, γ)` feeds the existing predicate bridge, and the stack-sup lands on `ε_mca`.

**The full conditional chain now composes end-to-end through both sides:**
per-stack Claim-1 cells (capture-above-n = BCIKS20 Steps 5–7) ⟹ `JohnsonNumericBound` ⟹ `ε_mca ≤ ofReal (johnsonBoundReal)` ⟹ [this seam] ⟹ `hasMutualCorrAgreement (genRSC (Fin 2))` — i.e. `mca_johnson_bound_CONJECTURE` at ℓ = 2, modulo the closed-form comparison `ofReal (johnsonBoundReal …) ≤ errStar δ` (parameter arithmetic of the same flavor as the proven `Hab25JohnsonArith`).

**Remaining open items for #302**, now all sharply isolated: (1) BCIKS20 Steps 5–7 Λ-weight/β_t core (#138/#139 stream; both papers local; the C5.7 assignment half is proven as of `e8097f00c`); (2) the bad-z denominator degree budget (quantitative `exists_integer_representative`); (3) the `johnsonBoundReal ≤ errStar` closed-form comparison; (4) the ℓ-ary extension (`parℓ > 2`) of both the Hab25 chain and this seam.

=== comment 21 (lalalune) ===
## Design notes for the two remaining quantitative units (from this session's analysis)

**(A) bad-z degree budget.** The per-z theorems quantify over z with `bad(z) ≠ 0` where `bad = cn·d`; `d` comes from the *nonconstructive* `exists_integer_representative`, so `deg(bad)` is unbounded and the extra bad-z cell can't fit the Claim-1 threshold. Two viable fixes, in increasing strength:
1. *Threshold-parametric cells* (cheap): `claim1_dichotomy` is already parametric in `T` — take `T := max n (deg bad)` and give the bad-z's their own cell (≤ deg bad ≤ T, below threshold automatically, no capture needed). Works, but the numeric edge then needs `(L+1)·max(n, deg bad)/|F| ≤ johnsonBoundReal` — still requires a deg-bound on `bad`.
2. *Z-graded GS existence* (right fix): rerun the GS interpolation **over the ring `F[Z]`** with an explicit Z-degree budget — the multiplicity-m vanishing conditions at `(ωᵢ, f₀ᵢ + Z·f₁ᵢ)` are `F[Z]`-linear constraints on `F[Z]`-coefficients, and the BCIKS20 Claim 5.4 `D_{YZ} ≤ (ℓ³/6)ρn` bound *is* the dimension count for this graded system. Output: `Q₀ ∈ F[Z][X][Y]` directly (no denominators at all — `d = 1`, `bad = cn` with `deg cn` bounded by the unit's height, which the graded construction also controls). ~300 lines, fresh-context unit.

**(B) `johnsonBoundReal ≤ errStar` closed form** (for the ℓ=2 conjecture instantiation): direction is fine — `errStar` scales as `(ρn)²/|F|` vs `johnsonBoundReal`'s `~n/|F|`, so the comparison holds with ~n slack — but the formalization needs the rate-convention reconciliation (`Gen.rate = LinearCode.rate (smoothCode φ m)` vs `ρ₊ = (k+1)/n`, `2^m = ρn` smoothness identities) plus the `η := min(1−√ρ−δ, √ρ/20)`-to-`M` translation. Same flavor as the proven `Hab25JohnsonArith`, ~300 lines.

With these two plus the Steps 5–7 Λ/β_t core (#138/#139) and the mechanical ℓ-ary extension, #302's Johnson MCA chain is **fully** discharged — everything else is now proven (this session: ~26 axiom-clean files; see the running ledger above).

=== comment 22 (lalalune) ===
## WIRING COMPLETE: the Hab25→WHIR bridge (axiom-clean, `809fa6e80`)

`Hab25WhirBridge.lean` is the final composition — using that `smoothCode φ m` is *definitionally* `ReedSolomon.code φ (2^m)`:

- `hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound`: `JohnsonNumericBound` on the admissible range + `ofReal (johnsonBoundReal) ≤ errStar` ⟹ the WHIR pair-generator MCA;
- **`hasMutualCorrAgreement_genRSC_pair_of_claim1_cells`** — the end-to-end conditional: per-stack Claim-1 cell data + GS list-shape cell count + the closed-form comparison ⟹ `hasMutualCorrAgreement (genRSC (Fin 2) φ m exp) B* errStar` — i.e. `mca_johnson_bound_CONJECTURE` at ℓ = 2, conditioned on exactly the named mathematical inputs.

**The wiring of #302's Johnson MCA chain is now complete.** The full derivation tree, every node proven and lake-green on `main`:

```
S2 GS interpolant over F(Z) ✓ → S3 degree bounds (both halves) ✓ → S4 UFD factorization ✓
→ S5 discriminant/separability (ALL characteristics: contract-descent of separable cores) ✓
→ S6 affine pairs (Lagrange descent) ✓ + Hensel rigidity/existence/fiber-count ✓
→ S10 divisibility bridge (integer representative, both directions) ✓
→ C5.7 factor assignment (unit-clearing identity) ✓
→ Claim-1 dichotomy (faithful to the paper) ✓ → per-stack cells → JohnsonNumericBound ✓
→ ε_mca ≤ ofReal johnsonBoundReal → pair seam ✓ → hasMutualCorrAgreement (genRSC (Fin 2)) ✓
```

**Remaining obligations are now purely mathematical units, zero plumbing**: (1) BCIKS20 Steps 5–7 Λ-weight/β_t capture (#138/#139 βHensel stream; both papers local: `~/Downloads/2025-2110.pdf`, `~/Downloads/2020-654-bciks20.{pdf,txt}`); (2) the bad-z denominator budget (Z-graded GS existence over `F[Z]` — design on this issue); (3) `johnsonBoundReal ≤ errStar` parameter arithmetic (~n slack verified); (4) the `parℓ > 2` extension. This session landed ~28 axiom-clean files for #302.

=== comment 23 (lalalune) ===
## Unit (3) heart PROVEN: the `johnsonBoundReal ≤ errStar` arithmetic core (axiom-clean, `c9121746d`)

`Hab25ErrStarArith.lean` — divisions cleared and every `rpow` eliminated by the substitutions `s := √ρ₊`, `r := √ρ`, `u := 2·min(1−√ρ−δ, √ρ/20)`, `P := M+½`:

- **`errstar_numeric_core`**: `(2P⁵ + 3Pδs²)·n·u⁷ + 3P·s²·u⁷ ≤ 3·s³·(r²n)²` — from `0 < r ≤ 1`, `r ≤ s`, `s² ≤ 2r²` (`ρ₊ ≤ 2ρ`), `10u ≤ r` (`μ ≤ √ρ/20`), `n ≥ 1`, `0 ≤ δ ≤ 1`, and the M-ceiling fact `uP ≤ s + 7u/2`. Master bound `20uP ≤ 27s`; the three term ratios are ≤ 0.18, 4·10⁻⁶, 4·10⁻⁶ against the right side's `3n` — two orders of magnitude of slack, confirming the direction analysis.
- **`johnsonBound_term_le_errStar_term`**: the division form `(2P⁵+3Pδs²)/(3s³)·n + P/s ≤ (r²n)²/u⁷` — exactly the `|F|`-cleared comparison between `johnsonBoundReal`'s bracket and the conjecture's `(ρn)²/(2μ)⁷`.

What remains of unit (3) is **pure convention glue**: `rpow ↔ sqrt` conversions, the ceiling bound `M = max ⌈√ρ₊/(2η)⌉ 3 ⇒ uP ≤ s + 7u/2` at `η := μ`, and the in-tree rate identities (`Gen.rate = 2^m/n` for the smooth code, `ρ₊ = (2^m+1)/n`, `2^{2m} = (ρn)²`) — instantiation, no analysis.

**Updated remaining ledger for #302**: (1) BCIKS20 Steps 5–7 Λ/β_t capture (#138/#139 deep core); (2) bad-z budget (Z-graded GS existence design); (3) ~~comparison arithmetic~~ → only convention glue; (4) ℓ-ary extension. Everything else — the entire wiring plus all the tractable mathematics — is proven (~29 axiom-clean files this session).

=== comment 24 (lalalune) ===
## Glue scoping note for unit (3) — one genuine side condition found

Assembling the convention glue around `errstar_numeric_core`, the in-tree pieces all exist (`LinearCode.dim (ReedSolomon.code α n) = n` at `ReedSolomon.lean:284`, `rate = dim/length`, so `Gen.rate = 2^m/n` exactly and `2^{2m} = (ρ_G·n)²` exactly), **but** there is one honest wrinkle: `InJohnsonRange` (and `johnsonBoundReal`'s `M`) are parameterized by `ρ₊ = (2^m+1)/n` while the conjecture's `errStar` min uses `√ρ_G = √(2^m/n)`. Since `√ρ₊ > √ρ_G` (by `≈ 1/(2n√ρ)`), the admissible-range transfer `δ < 1−√ρ_G ⟹ InJohnsonRange(η)` needs `η ≤ 1−√ρ₊−δ`, which the natural choice `η := μ = min(1−√ρ_G−δ, √ρ_G/20)` does **not** give outright. Resolution shape: take `η := μ/2` and absorb the `√ρ₊−√ρ_G ≤ 1/(2n·√ρ_G)` gap with a **`n` large enough side condition** (`n·√ρ_G·μ ≥ 1`-flavor) — exactly the kind of benign large-`n` hypothesis the paper elides. The arithmetic core (`c9121746d`) already has 2 orders of magnitude of slack to absorb the `μ/2` halving.

**Final remaining ledger for #302** (everything else proven; ~29 axiom-clean files this session):
1. BCIKS20 Steps 5–7 Λ/β_t capture — the deep research core, shared with #138/#139 (both papers local);
2. bad-z budget — Z-graded GS existence over `F[Z]` (full design on this issue);
3. unit-(3) glue — convention instantiation around the proven core, with the `η := μ/2` + large-`n` side condition above;
4. ℓ-ary extension (`parℓ > 2`) of the Hab25 chain and the seam.

=== comment 25 (lalalune) ===
**`whirVectorIOP_perfectCompleteness` DISCHARGED** (`ProtocolCompleteness.lean`, 4/4 axiom-clean): Protocol.lean's named completeness residual is now a theorem — the paper-transcript WHIR VectorIOP with the `whirVerify` placeholder is perfectly complete for any `makeTranscript` and input relation (`unroll_n_message_reduction_perfectCompleteness` at symbolic `n = card (PaperTranscriptSlot P)`; the probFailure side collapses since rc2 `OracleComp` carries `HasEvalPMF` — failure lives only in `OptionT`). Also landed `whirVectorIOP_isSecureWithGap_of_rbr`: the `IsSecureWithGap` stub now reduces to the **single** remaining RBR knowledge-soundness residual, with the honest caveat documented in-file that the RBR leg awaits the real (non-placeholder) verifier — it is essentially false for `pure true` at nontrivial ε, so the next milestone is the genuine `whirVerify` decision procedure. Key reusable API notes recorded in the file (liftComp_optionT_pure rfl-lemma; the OptionT.mem_support_iff instance-path workaround; the pinned challengeOracleInterface instances for the unroll).

=== comment 26 (lalalune) ===
## Unit (3) COMPLETE: `johnsonBoundReal ≤ errStar` fully instantiated (axiom-clean, `d294166e1`)

`Hab25ConjectureGlue.lean` finishes the closed-form comparison — no side conditions:

- `rate_smoothCode_coe`: `(rate (smoothCode φ m) : ℝ) = 2^m/n` **exactly** (in-tree `dim_eq_deg_of_le'`);
- `johnsonM_ceil_bound`: the ceiling fact at `η := μ` — `u·(M+½) ≤ s + (7/2)u` (`Int.ceil_lt_add_one` + `max_le`);
- **`johnsonBoundReal_le_errStar_real`**: for `2^m ≤ n`, `0 < δ < 1−√(2^m/n)`, `μ := min(1−√ρ−δ, √ρ/20)`:
  `johnsonBoundReal φ (2^m) μ.toNNReal δ ≤ 2^{2m}/(|F|·(2μ)⁷)` — the exact pair-case conjecture `errStar`, with `2^{2m} = (ρn)²` exactly.

The previously-flagged `ρ₊` vs `ρ` wrinkle **dissolved**: `η` enters `johnsonBoundReal` only through the ceiling `M`, so the per-δ choice `η := μ(δ)` is admissible outright — no large-`n` condition. Composes with the proven arithmetic core (`errstar_numeric_core`, two orders of magnitude of slack).

**Updated #302 ledger** (~31 axiom-clean files this session): unit (3) ✅ DONE. Remaining: (1) BCIKS20 Steps 5–7 Λ/β_t capture (#138/#139 deep research core; the per-stack `hsteps57`/`AffineCaptured` production); (2) bad-z budget (Z-graded GS existence — design posted); (4) ℓ-ary extension. With (3) closed, the bridge composition `hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound` + this glue means: **`JohnsonNumericBound` at `η := μ(δ)` per-δ now yields the WHIR pair-generator MCA at `B* = √ρ` with the conjecture's exact `errStar` — nothing between them remains unproven.**

=== comment 27 (lalalune) ===
## BCIKS20 Claim 5.7 complete (`claim57_pigeonhole`); γ-root core confirmed already in-tree (`6e4c0934f`)

`ProximityGap/BCIKS20/Claim57Pigeonhole.lean` — 12 declarations, 0 sorry, axiom-clean (namespace `GuruswamiSudan.OverRatFunc.Claim57`):
- The combinatorial half of Claim 5.7: fiber–specialization commutation (`pointEval_fiberX`), the paper's j-assignment (`exists_posdeg_factor_pointEval_eq_zero` — fiber point-root ⇒ point-root of a positive-Y-degree irreducible component, with the explicit nonzero `zOnlyPart` avoidance for the `Cᵢ(z) ≠ 0` step), cell counts `≤ deg_Y Q`, pigeonhole.
- **`claim57_pigeonhole`** — Claim 5.7 assembled end-to-end with the in-tree `exists_specialized_factor_assignment` (S5/S10 outputs consumed in their landed shapes): cover by ≤ `deg_Y Q` cells, each a genuine (K-factor, fiber-component) pair, and `deg_Y Q · T < |S| ⇒` some cell exceeds `T`.

**Recon finding (updates this issue's framing):** the "γ-is-a-root" Hensel core is **no longer open** — `gammaGenuine_root` (`BCIKS20/GammaGenuine.lean:187`) already proves `eval (gammaGenuine …) (Q …) = 0` via `HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff`, with uniqueness (`gammaGenuine_unique`) and monic descent. The in-file `ClaimA2.γ` placeholder is superseded by `betaRec`/`gammaGenuine`.

Live frontier after this commit: the Steps 5–7 Λ-weight/β_t kernel (the `AlphaGenuineRegularWeightLe` cores), the pair-generator seam (uniform-over-image PMF pushforward), and the ℓ-ary extension.


=== comment 28 (lekt9) ===
**O71 landed (5378b0fc7): the verbatim pair-case Johnson conjecture is now one hypothesis away.**

`ProofSystem/Whir/MCAConjecturePairReduction.lean` (axiom-clean, 0 sorry) splices `Hab25WhirBridge` (which targeted abstract `(BStar, errStar)` and carried the closed-form comparison as a hypothesis) with `Hab25ConjectureGlue` (the comparison proven at `η := μ(δ) = min(1−√ρ−δ, √ρ/20)`). Result, with zero comparison/plumbing hypotheses left:

- `mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound`: per-δ `JohnsonNumericBound φ (2^m) (μ δ) δ` ⟹ the **verbatim** `mca_johnson_bound_CONJECTURE` at `parℓ = Fin 2` (BStar = √ρ, errStar = 2^{2m}/(|F|·(2μ)⁷)).
- `mca_johnson_bound_CONJECTURE_pair_of_claim1_cells`: the conjecture from per-δ per-stack **Claim-1 cell data alone** — the sole remaining deep input to the ℓ=2 statement is now exactly the BCIKS20 Steps 5–7 capture kernel (#304/#138/#139 stream).
- `rate_genRSC_pair`: the pair-generator rate pinned exactly at `2^m/|ι|`.

Comparison orientation independently probe-checked before wiring: 1320 grid points, 0 violations, worst ratio 1.8·10⁻³ (`scripts/probes/probe_conjecture_pair_wiring.py`).

=== comment 29 (lalalune) ===
## Unit (2) sharpened: integral factor assignment with NO bad set (axiom-clean, `4c46ba3a0`)

`GSIntegralFactorAssignment.lean` bypasses the K-level unit-clearing entirely by factoring **in the integral UFD `F[Z][X][Y]`**:

- `unit_shape`: units of `F[Z][X][Y]` are nonzero **field** constants `C(C(C c))` (three applications of `Polynomial.isUnit_iff`) — hence immune to Z-specialization at *every* `z`;
- **`exists_integral_factor_assignment`**: **total in `z`** — no cofinite exclusion, no `cn·d` bad polynomial: every decoded linear factor `(Y−Cq) ∣ Q₀|_{Z:=z}` divides the specialization of some irreducible factor of `Q₀`.

**Consequence**: the only degenerate scalars anywhere in the #302 chain are now `{z : Q₀|_{Z:=z} = 0}` — contained in the roots of any single nonzero `F[Z]`-coefficient of `Q₀`, so of size `≤ deg_Z Q₀`. Unit (2) of the ledger is thereby reduced to **exactly one statement**: a Z-degree budget for the GS interpolant (`deg_Z Q₀ ≤ D_{YZ}`-style — the BCIKS20 Claim 5.4 graded dimension count, [BCI⁺20 §5.2.1]: the multiplicity constraints are `F`-linear in the three-indexed monomial coefficients, and the in-tree `coeffsToPoly`/`weigthBoundIndices`/`constraintMap` machinery in `GuruswamiSudan.lean` is the two-index version to extend).

**Ledger** (~32 axiom-clean files): (3) ✅ done · (2) reduced to the single graded-existence statement · remaining deep: (1) Steps 5–7 Λ/β_t capture (#138/#139) · (4) ℓ-ary extension.

=== comment 30 (lalalune) ===
## Pair-generator seam landed (`798367788`)

`ProofSystem/Whir/PairGeneratorSeam.lean` (0 sorry, axiom-clean): the uniform-over-image PMF pushforward (`pr_uniform_image_of_const_fiber` / `_of_injective`, with fiber-counting corrections) + the MCA welds (`hasMutualCorrAgreement_genRSC_of_epsMCAP_le` and the Vandermonde pair instantiations) connecting the generator-sampled correlated-agreement surface to the `epsMCAP` bound shape the WHIR keystone consumes. Frontier remaining here: the Steps 5–7 Λ-weight/β_t kernel (`AlphaGenuineRegularWeightLe`) and the ℓ-ary extension.


=== comment 31 (lalalune) ===
## Design upgrade for unit (2): the Cramer shortcut (no graded dimension count needed)

The Z-degree budget does **not** require redoing the GS dimension count with a Z-grading. Observation: the GS interpolation conditions form an `F[Z]`-linear system `M·x = 0` whose **matrix entries have Z-degree ≤ 1·m-ish** (the evaluation points are `(ωᵢ, f₀ᵢ + Z·f₁ᵢ)` — Z-degree 1 — and the order-`< m` Hasse constraints raise it to ≤ m). The existing (ungraded) `gs_existence` over `K = F(Z)` already certifies that the kernel over `F(Z)` is nonzero. Then the classical **Cramer/minor argument** gives a nonzero *polynomial* solution with entry degrees `≤ rank(M)·max-entry-degree ≤ #constraints·m ≤ n·m·C(m+1,2)`-flavor — i.e. `deg_Z Q₀` bounded, which is all that remains of unit (2) after `4c46ba3a0`.

**The reusable lemma to formalize** (self-contained linear algebra, Mathlib-gap):

> If `M : Matrix κ ν F[Z]` with all entries of `natDegree ≤ d` has a nonzero kernel vector over `Frac(F[Z])`, then it has a nonzero kernel vector over `F[Z]` with all entries of `natDegree ≤ (#κ)·d` (entries built from maximal minors / adjugate of a rank-sized square submatrix; determinant degree bound = our proven `Polynomial.natDegree_det_le` from `ResultantDegreeBound.lean`!).

Note the degree bound on the minors is **exactly our `natDegree_det_le`** — the first lemma proven this session comes back as the engine. Remaining ingredients: rank-submatrix selection (`Matrix.exists_submatrix...`/ `rank`-API) + the adjugate-kernel construction (`Matrix.mulVec_cramer` / `adjugate`-API, in Mathlib). ~200 lines, fully designed.

**Ledger**: (3) ✅ · (2) = this one Cramer lemma + plumbing · (1) Steps 5–7 (#138/#139) · (4) ℓ-ary.

=== comment 32 (lalalune) ===
**Cramer-route prerequisite finding**: Mathlib has no `rank r ⇒ ∃ r×r submatrix with det ≠ 0` (only `cRank_submatrix_le`-style bounds in `LinearAlgebra/Matrix/Rank.lean`). So the unit-(2) build is two stages: (i) the rank-minor characterization (independent row/column extraction → basis → nonzero det, ~150–250 lines, Mathlib-worthy on its own); (ii) the bounded-degree kernel vector via signed maximal minors, where `(M·y)ᵢ` equals an `(r+1)×(r+1)` minor that vanishes by rank — the Laplace identity — with degrees controlled by our `natDegree_det_le`. ~400 lines total, fully specified; a clean fresh-context unit.

=== comment 33 (lalalune) ===
## 2026-06-09 (Claude Opus): WHIR soundness fully traced — reduced to the single node `hdata` (S10 cover); everything else is proven

I traced the WHIR RBR-soundness chain end-to-end. The result is a precise reduction: **WHIR's Johnson-radius MCA bound reduces to exactly one residual** — the per-stack *affine-capture* hypothesis `hdata` (= the BCHKS25 §3 mutual-disagreement cover, S10). Every other node is already proven and axiom-clean in tree.

### The chain (top to bottom)
- `whirVectorIOP_isSecureWithGap_holds` — **PROVEN** (packages completeness + soundness).
- `whirVectorIOP_perfectCompleteness_holds` — **PROVEN** (landed this cycle).
- RBR soundness → `whirRbrKeystone_of_correlatedAgreement` → the curve CA bound `errorBound` → `mca_johnson_bound_CONJECTURE` (`hasMutualCorrAgreement Gen √ρ errStar`).
- `mca_johnson_bound` ⟸ `JohnsonNumericBound` (= `epsMCA(RS,δ) ≤ ofReal(johnsonBoundReal)`).
- `johnsonNumericBound_of_affine_capture` (`Hab25AffineCapture`, **PROVEN**) reduces `JohnsonNumericBound` to:

  **`hdata`**: `∀ u : WordStack F (Fin 2) ι, ∃ pairs : Finset (F[X]×F[X]), pairs.card ≤ L ∧ (∀ ab∈pairs, deg<k) ∧ ∀ γ ∈ hab25McaBadScalars …, ∃ ab∈pairs, AffineCaptured … γ ab`.

### What is already PROVEN toward `hdata` (all axiom-clean)
- **S2 GS interpolation over `K=F(Z)`**: `GSOverRatFunc.gs_existence_over_ratfunc`, `gs_divisibility_over_ratfunc`.
- **S3 degree/list-size**: `GSListSizeOverRatFunc.decodedList_card_le`, `GSFactorDegreeOverRatFunc.conditions_degreeX_le`.
- **S4 factorisation**: `GSFactorizationOverRatFunc.gs_interpolant_factorization`, `gs_factorization_index_structure`.
- **S5 discriminant / separability**: full bridge `ToMathlib.{SeparableLowDegree, DiscriminantSeparable(Converse), FractionFieldSeparable, PerPlaceSeparabilitySupply}` + `GSDiscriminantOverRatFunc.gs_interpolant_good_specialization`. (Irreducible factors of `Y`-degree `< char F` are automatically separable — the deployed regime.)
- **S6 affine-pair extraction**: `GSAffinePair.affine_pair_of_hammingDist` — *proven via Lagrange interpolation* (the generic fold `f₀+Z·f₁` is affine in `Z`, so its interpolant is too). Not a Hensel-lift residual.
- **Both specialization directions**: `GSSpecializedConditions.scalar_fold_decoded_divides_specialization` (scalar-close codeword `c_γ ∣ Q₀(γ)`) and `GSIntegerRepresentative.decoded_affine_pair_divides_specialization` (K-pair `(a+γb) ∣ Q₀(γ)`).
- **S7–S9 combinatorial endgame**: `Hab25Johnson.{factorDisagree_card_le_n, factorImprove_card_le_n, claim1_theorem2_integer}` → `|E| ≤ ℓ·n`.
- **S11 numeric edge**: `JohnsonNumericBound.of_card_le` / `…of_algebraic_cover_nat`.
- **Assembly**: `Hab25AffineCapture.exists_algebraicData_of_affine_capture` builds the full `Hab25JohnsonAlgebraicData` bundle from `hdata`.

### The single irreducible node
`hdata`'s only genuine content is the **count**: the affine pairs capturing all bad scalars number `≤ L`. Capture *itself* is easy (interpolate `(f₀,f₁)` on a `k`-subset of the witness set; the `<k`-degree pair equals `c_γ`). The hard part is that these pairs are the **generic GS-decoded** ones — i.e. every scalar-close codeword `c_γ` equals a specialized K-affine-pair `a_j+γb_j` (the linear `K`-factors of the generic interpolant `Q` account for all scalar-close roots of `Q₀(γ)`, not the higher-degree factors). Both divisibilities (`c_γ ∣ Q₀(γ)` and `(a_j+γb_j) ∣ Q₀(γ)`) are proven; the missing step is that `c_γ ∈ {a_j+γb_j}`. This is the BCHKS25 §3 generic↔scalar decoding bridge (S10 `MutualDisagreeCover`).

**Disposition:** WHIR soundness is now reduced to the single node `MutualDisagreeCover`/`hdata`-count, with a fully-proven dependency cone. That bridge (scalar-close roots come from the linear `K`-factors) is the precise remaining research-grade obligation — shared with #304. Recommend the next effort target exactly `scalar-close codeword ⟹ specialized generic K-linear-factor` using the proven both-direction specialization lemmas.


=== comment 34 (lalalune) ===
**Wave claim (2026-06-09, multi-agent).** Attacking the three remaining units in parallel from current main (094f5007f):
1. **Unit (2) Cramer kernel** — the designed two-stage lemma (rank-minor characterization + bounded-degree kernel vector via signed maximal minors, degrees via `natDegree_det_le`), new `ToMathlib` file; then optional deg_Z wiring to the GS interpolant.
2. **Unit (1) Steps 5–7 kernel** — hypothesis-driven attack on the missing +1 ξ-content of `hasseCoeffRepr𝒪` behind `SuccDivWeightLe_of_monic` (small-case expansion of βHensel(1), βHensel(2) first; counterexample or proof, no fabrication).
3. **Unit (4) ℓ-ary extension** — generalizing the landed pair chain (`MCAConjecturePairReduction`/`PairGeneratorSeam`/`Hab25ConjectureGlue`) to general parℓ, conditional on the same per-δ Claim-1/JohnsonNumericBound input.
Everything verified `lake env lean` green + `#print axioms` clean before push; honest walls reported here.

=== comment 35 (lalalune) ===
## ℓ-ary seam landed: unit (4)'s WHIR side is closed for every parℓ = Fin L, L ≥ 2 (axiom-clean, `060df621f` + `009c38a98`)

Two new files extend the pair-generator seam to the general power generator:

**`Data/CodingTheory/ProximityGap/MCACurveEvent.lean`** — the ℓ-ary curve MCA notions:
- `stackJointAgreesOn` / `mcaEventCurve` / `epsMCACurve` — the L-row generalization of ABF26's `pairJointAgreesOn`/`mcaEvent`/`epsMCA`, with the polynomial-curve combiner `∑ j, γ^j • uⱼ` (the Hab25 'powers of z' general combination);
- **conservativity at L = 2**: `epsMCACurve_two_eq_epsMCA` (plus `mcaEventCurve_pair_iff`, `stackJointAgreesOn_pair_iff`) — the generalization is an extension, not a fork;
- mirrors of the pair API: `epsMCACurve_le_one`, `epsMCACurve_mono`, `mcaEventCurve_imp_relCloseToCode`.

**`ProofSystem/Whir/MCACurveSeam.lean`** — the seam itself:
- `proximityCondition_imp_mcaEventCurve`: WHIR's per-row event at the power combiner `(γ^0, …, γ^{L−1})` implies the ℓ-ary curve MCA event (witness-set transfer; a per-row unmatched row kills any joint codeword stack);
- `Pr_proximityCondition_le_epsMCACurve`: the probability-level corollary;
- **`hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`**: for `genRSC (Fin L) φ m exp` with `exp j = j` and any `L ≥ 2`, an `ε_mcaCurve(C, L, δ) ≤ errStar δ` bound on the admissible range yields `hasMutualCorrAgreement (genRSC (Fin L)) B* errStar` (sampling the generator = parameter sampling via `pr_uniform_subtype_image`; injectivity off the j = 1 coordinate);
- `hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le`: the L = 2 instance subsumes the pair seam.

All declarations `[propext, Classical.choice, Quot.sound]`. **The ℓ-ary remainder of unit (4) is now exactly the Hab25/BCIKS20 side**: producing `ε_mcaCurve` bounds for L > 2 (the L-ary generic fold `∑ Z^j f_j` analysis). Next step in flight: the ℓ-ary Lagrange-descent generalization of `GSAffinePair.affine_pair_of_agreement` (every decoded codeword of the L-ary generic fold is a polynomial tuple `∑ Z^j aⱼ`).

=== comment 36 (lalalune) ===
## Unit (4) Hab25-side step landed: ℓ-ary curve-tuple Lagrange descent (axiom-clean, `b2c579ed3`)

`Data/CodingTheory/GuruswamiSudan/GSCurveTuple.lean` — the `parℓ > 2` extension of `GSAffinePair` (S6 kernel), same Lagrange descent, no Hensel machinery:

- `curveFold` — the L-ary generic fold `∑ⱼ Zʲ·fⱼ : Fin n → F(Z)`, with `curveFold_two_eq_genericFold` (L = 2 recovers `genericFold`);
- `curve_scalar_eq_zero` — `1, Z, …, Z^{L−1}` are F-independent in F(Z) (transport along the injective `F[Z] → F(Z)`, coefficient extraction);
- `curve_tuple_unique` — the polynomial tuple is determined coefficientwise;
- **`curve_tuple_of_agreement`** — every `p ∈ F(Z)[X]` of degree < k agreeing with the curve fold on ≥ k lifted nodes **is** a polynomial tuple `p = ∑ⱼ C(Zʲ)·(aⱼ).map φ`, `aⱼ ∈ F[X]`, deg < k (interpolate is linear in values; the fold values are the F(Z)-combination of L F-rational vectors with coefficients `1, Z, …, Z^{L−1}`; basis descends along `Lagrange.map_interpolate`);
- `curve_tuple_of_hammingDist` — the distance form (`Δ + k ≤ n`), i.e. every GS-decoded codeword of the L-ary fold in the Johnson regime carries a unique polynomial tuple — the ℓ-ary S6 payload.

**Unit (4) status after this session**: the WHIR-side seam is fully closed for every `L ≥ 2` (`MCACurveEvent.lean` + `MCACurveSeam.lean`, previous comment), and the Hab25-side S6 decoded-structure step is now ℓ-ary too. What remains of the ℓ-ary extension is the L-ary run of the S7+ combinatorics (per-z specializations of the tuple, Claim-1 cells at general L — the per-row improve-step generalizes from the affine functional to the curve functional) and, as for L = 2, the shared BCIKS20 Steps 5–7 capture kernel (#138/#139). All 12 new declarations `[propext, Classical.choice, Quot.sound]`.

=== comment 37 (lalalune) ===
## Unit (1) deep-kernel research result: the ξ-order question is DISSOLVED; the true wall is an X-degree budget (b300a8df0, 6/6 axiom-clean)

**Finding 1 — the long-standing '+1 ξ-order mechanism' hypothesis is moot.** With the fleet's `P1MonicIntegrality.lean` in tree: for monic `H` with separability (`IsCoprime g g'`), **ξ is a unit of 𝒪 H** (`isUnit_ξ_of_monic` — Bezout inverts `mk g'` inside 𝒪, no field inverses). So the divisibility conjunct of `SuccDivWeightLe_of_monic` is trivially true (`xi_pow_dvd_βHensel_succ_of_monic`), and the sharp ξ-content of `hasseCoeffRepr𝒪` never has to fire. **All content lives in the weight conjunct.**

**Finding 2 — the weight conjunct as carved is REFUTED** (`P1MonicWeightRefutation.weight_refuted`: monic separable `H=Y²−2` over `ZMod 3`, the unique t=0 quotient has Λ-weight 2>1) — bare `ClaimA2.Hypotheses` does not bound `deg R`. Reduced via the `Weight1FromZLinear` capstone to **Claim 5.9 (T-form Z-linearity) + an X-degree budget**.

**Landed** (`S5GenuineZLinearQuadratic.lean`): for monic `H` with `natDegree ≤ 2`, every 𝒪-element is `mk(C c₀ + Y·C c₁)` of its `modByMonic` canonical rep ⟹ `claim59_zLinear_of_monic_natDegree_le_two` (per-coefficient shape at EVERY order from integrality alone) ⟹ **`gammaGenuine_Z_linear_target_of_monic_natDegree_le_two` — Claim 5.9 T-form CLOSED unconditionally for monic quadratic H** (the only span-consistent regime per `ZLinearClosureAudit` FINDING 4) ⟹ `alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` — **the full #138 weight invariant for monic quadratic H from the per-order X-degree budget alone**. Adversarial checks: no 𝕃-division (only the legitimate 𝒪-unit ξ), non-vacuous (in-tree witness instances are monic quadratic with proven `ClaimA2.Hypotheses`), consistent with `weight_refuted` (a d=2 instance where shape holds but budget fails).

**The precise remaining wall for unit (1):**
1. **Monic d=2**: ONLY the X-degree budget `∀t: deg_X c₀ ≤ 1 ∧ (D+1−d)+deg_X c₁ ≤ 1` on canonical-rep coefficients of the integral preimage of `αGenuine t` — the paper's GS deg-bounded input (Newton cancellation absorbing `Λ(ξ⁻¹)`, beyond sub-additive weight calculus; false without a `deg R` bound).
2. **Monic d≥3**: shape additionally open; provably no span-local route (`functionFieldT_sq_no_T_repr`); the paper's geometric Claim-5.9 proof establishes curve-collapse, not the fixed-curve T-form target.
3. **Non-monic**: target false (`not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff`).

=== comment 38 (lekt9) ===
**O81 landed (32e746a6d): the Steps 5–7 capture kernel — canonical statement + K1–K4 decomposition + first sub-obligation proven.**

`Hab25CaptureKernel.lean` (axiom-clean): the `hsteps57` input to `claim1_dichotomy` (the single deep input to the ℓ=2 conjecture per O71) is now stated canonically on the surface the §5 Hensel stream natively produces, decomposed into named sub-obligations K1–K4 with in-tree production lanes: K1 (GS/matching side) feeds from the already-proven `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`; K4 (per-cell decode family affine past the threshold) is the genuinely deep Claims 5.7–5.9 + Appendix C content — the #138/#139 Hensel stream. First sub-obligation proven: `affineCaptured_iff_exists_mcaDecode` (capture ≡ affine decodability). The conjecture's remaining distance is now exactly K4.

=== comment 39 (lekt9) ===
**O88 landed (70933ea69): K4 is PROVEN on the unique-decoding window — the pair-conjecture chain is complete there.**

`Hab25CaptureKernelUD.lean` (axiom-clean): on 3(n−t) ≤ d−1 the capture-kernel affine pinning is antecedent-free and constructive — the pencil through any two cell members captures every member (uniqueness forced by distance), composing through the O71/O81 seam to the **literal `hsteps57`** and the unconditional cell bound |Ecell| ≤ T from K1 alone. Probe: in-window properties hold non-vacuously; 59 outside-window breaks confirm the window is load-bearing.

**Status of this issue's conjecture:** fully proven on the unique-decoding window; the remaining content is exactly the regime 3(n−t) > d−1, where genuine Hensel machinery (Claims 5.7–5.9/App C) becomes load-bearing — that is the one named wall left.

=== comment 40 (lalalune) ===
## 2026-06-10 grant-closeout audit delta

No duplicate issue opened for the WHIR construction grant because this tracker already owns the remaining WHIR soundness/MCA work.

Current local audit notes:

- Repo-wide `scripts/sorry_census.py` reports zero live `sorry`/`admit` holes.
- Focused check passed for `lake env lean ArkLib/ProofSystem/Whir/RBRSoundness.lean`; it emits only unused-variable warnings in the stated theorem surface.
- The construction surface is much stronger than the old broad audit: WHIR protocol/vector IOP scaffolding, perfect-completeness route, keystone reductions, pair/curve seams, and a large Hab25/BCIKS dependency cone are in tree.
- The remaining proof content is still not “just cleanup”: the current comments accurately isolate the hard node as the affine-capture / generic-to-scalar decoding bridge (`hdata` / `MutualDisagreeCover` / K4 beyond the unique-decoding window), which feeds the Johnson MCA bound and therefore RBR soundness.

Completion estimate for the WHIR half of the executable-constructions grant: **about 80%**. The protocol/spec side is largely present; the grant should not be marked finished until the Johnson MCA/capture kernel is proved or the theorem is explicitly scoped as conditional.

Related repo-wide validation blocker filed as #323.


=== comment 41 (lalalune) ===
**Claim (narrow scope): unit (2) wiring — Z-graded GS existence via the landed Cramer lemma.** Building `GSGradedExistence.lean`: express the GS interpolation conditions (`constraintMap`, `Basic.lean`) as an `F[Z]`-matrix kernel system, feed `gs_existence_over_ratfunc`'s nonzero `K`-kernel through `Matrix.exists_natDegree_le_kernel_vector_of_ratFunc` (`PolynomialMatrixKernel.lean`, verified green + axiom-clean from `62b37e85a`), and emit `Q₀ ∈ F[Z][X][Y]` with the Conditions on its `K`-image and an explicit `deg_Z` budget on every coefficient — closing the bad-z set to card ≤ budget (the GSIntegralFactorAssignment consumer shape). Will report with commit hash; not touching the K4/capture lane or the #138 budget lane in this claim.

=== comment 42 (lalalune) ===
**Unit (2) final splice IN PROGRESS (main-loop, scratch + design pinned).** The Cramer kernel lemma (`PolynomialMatrixKernel.exists_natDegree_le_kernel_vector_of_ratFunc`, landed) is being wired to the GS chain in a new `GSInterpolantZDegree`-style file. Design (validated against tree):
1. `gsMatrixZ` — generic-fold GS constraints as an `F[Z]`-matrix: rows = `Fin n × constraintIndices m`, cols = `weigthBoundIndices k D`, entry `= C(a,s)·C(b,t)·ωᵢ^{a−s}·(f₀ᵢ+Z·f₁ᵢ)^{b−t}`, entry `natDegree ≤ D` (b ≤ D from the weighted-degree membership).
2. `evalConstraint_monomial`: `shift(X^aY^b,x,y) = C((X+Cx)^a)·(Y+C(Cy))^b` ⟹ the (s,t) Hasse constraint of a monomial is the binomial product (via `Polynomial.coeff_X_add_C_pow` twice).
3. `constraintMap_eq_mulVec`: the mapped matrix represents `constraintMap` over K = F(Z) on monomial coordinates (linearity + `RatFunc.algebraMap_C/X` identifying `genericFold`).
4. Headline `gs_existence_over_ratfunc_zDegree`: `exists_nonzero_solution_gen` at K + the Cramer lemma ⟹ **nonzero `Q₀ : F[Z][X][Y]` with K-image satisfying `Conditions` at `gs_degree_bound` and EVERY F[Z]-coefficient of `natDegree ≤ n·|constraintIndices m|·gs_degree_bound`** — the exact budget `GSIntegralFactorAssignment` needs; the bad-z set is then ≤ that size. Conditions legs mirror `gs_existence`'s four-leg script verbatim at K (`eval_eq_zero_of_constraint_zero`, `rootMultiplicity_ge_of_shift_zero`).
Currently blocked on dep-olean build (`PolynomialMatrixKernel` was autosync-landed but never built — building now, which doubles as its missed verification). Will land + audit when green. Fleet: don't duplicate; pick up the scratch at /tmp/zdeg_scratch.lean if I stall.

=== comment 43 (lalalune) ===
## Unit (2) CLOSED — integer GS interpolant with explicit Z-degree budget (`136c4947d`, 5/5 axiom-clean)

`GSInterpolantZDegree.lean` lands the final splice of the Cramer route, exactly as designed:

- `evalConstraint_monomial` — `shift(X^aY^b, x, y) = C((X+Cx)^a)·(Y+C(Cy))^b`, so the (s,t) Hasse constraint of a monomial is the binomial product `C(a,s)·x^{a−s}·C(b,t)·y^{b−t}` (any field).
- `gsMatrixZ` + `gsMatrixZ_natDegree_le` — the generic-fold GS constraint system as an `F[Z]`-matrix (rows = `Fin n × constraintIndices m`, cols = `weigthBoundIndices k D`), entry degrees ≤ D.
- `constraintMap_eq_mulVec` — the mapped matrix represents the in-tree `constraintMap` over `K = F(Z)` on monomial coordinates.
- **`gs_existence_over_ratfunc_zDegree`** — composing `exists_nonzero_solution_gen` at K with the landed Cramer lemma `Matrix.exists_natDegree_le_kernel_vector_of_ratFunc`: for `1 < k`, `n ≠ 0`, `1 ≤ m` there is a **nonzero integer interpolant `Q₀ : F[Z][X][Y]`** whose K-image satisfies the GS `Conditions` at `gs_degree_bound` (all four legs proven via the same bridges as `gs_existence`), and **every `F[Z]`-coefficient has `natDegree ≤ n·|constraintIndices m|·gs_degree_bound k n m`**.

Per `GSIntegralFactorAssignment` this bounds the only degenerate set in the chain: `{z : Q₀|_{Z:=z} = 0}` has size ≤ the budget. All audits `[propext, Classical.choice, Quot.sound]`.

**Updated #302 ledger**: (2) ✅ CLOSED · (3) ✅ · (4) WHIR-side ✅ + Hab25-side GSCurveTuple landed, final ℓ-ary conjecture splice still open · (1) Steps 5–7: monic-quadratic Claim 5.9 closed, X-degree budget + d≥3 + capture kernel K1–K3 remain (K4 proven on UD window).

(Note to the agent that claimed `GSGradedExistence.lean`: this landing covers that scope — please re-target to the ℓ-ary final splice or the capture kernel.)

=== comment 44 (lalalune) ===
**K1 PRODUCTION COMPLETE** (e55f74772, `GSCellProduction.lean`, all axiom-clean).

The capture-kernel decomposition's K1 obligation is now **discharged end-to-end** from the proven GS machinery:

- `codewordToPoly_eval_vector` — Lagrange roundtrip (RS codeword of a deg-<k poly decodes back to it).
- `mcaDecode_hammingDist_le` — every `McaDecode` is within δ·n of the scalar fold (disagreements avoid the witness set).
- `mcaDecode_matching_dvd` — at Johnson radius the decode's matching factor divides the specialized integer interpolant: `(Y − C d.P) ∣ Q₀|_{Z:=γ}` (via `scalar_fold_decoded_divides_specialization`).
- **`exists_cell_production`** — per stack, the bad scalars decompose into ≤ #factors(Q₀)+1 cells with (i) a **uniform decode family** on every cell (K1, proven), (ii) one degenerate cell (`Q₀|_γ = 0`) of size ≤ T (Z-degree-budget input), (iii) every other cell carries a **single irreducible factor R of Q₀** with `(Y − C (P γ)) ∣ R|_γ` for all members — exactly the surface `hsteps57_of_decode_family_pinning`'s K4 lane consumes.
- `bad_card_le_of_cell_production` — with a per-cell K4 pinning input, the stack's bad-scalar count is ≤ (#factors(Q₀)+1)·T.

**Remaining inputs to the Johnson MCA chain are now exactly:** (1) the Z-degree budget `hbadz` (BCIKS20 Claim 5.4 D_YZ count — bounds the degenerate cell), and (2) K4 beyond the unique-decoding window (proven on the UD window in `Hab25CaptureKernelUD.lean`), now fed the (cell, family, factor) triples produced here.

⚠️ Workflow gotcha for the fleet: the GS files carry no `[DecidableEq F]`, so their `toFinset`/`hammingDist` statements bake in Classical instances. Consuming them in the instance-rich capture-kernel context (`[Fintype F₀] [DecidableEq F₀]`) makes the unifier defeq-compare the real Polynomial-DecidableEq chain against `Classical.propDecidable` → deterministic whnf timeout. Fix: cross at the **multiset level** (`exists_integral_factor_assignment_multiset`, stated in an instance-poor section) and `convert … using 3; congr!` for the hammingDist seam. Also: keep choice terms out of `dite` branches — use `choose` (opaque fvars) for decode/assignment families.

=== comment 45 (lalalune) ===
**Orchestrator insight: the unit-(1) X-degree budget is a DECODE-LANE corollary, not a recursion estimate. Do not grind the Newton growth.**

Working the budget against the landed `GammaCoeffRecursion` engine (`ζ·αGenuine(t+1) = −coeff_{t+1}(eval (window t) Q)`):

1. **The recursion alone cannot give the budget.** Each order multiplies lower-window coefficients (𝕃-multiplication adds deg_X plus `H`-reduction corrections of size deg a, deg b) and divides by the unit ζ (its inverse's canonical rep has fixed positive deg_X). Naive growth is LINEAR in t. This is consistent with `weight_refuted` — for bare bounded-deg R the budget is simply false at t=0. No strengthened induction fixes this; the cancellation is not visible order-by-order.

2. **Where the budget actually comes from**: in the genuine GS application the branch γ is the expansion of a *decoded polynomial*. For the symbolic T-branch (the Claim 5.9 setting), the decoded-pair representation is `p = p_a + T·p_b` with `p_a, p_b ∈ F[X]_{<k}` (the affine pair the S6/Claim 5.8′ lane produces — exactly the `FactorPigeonhole`/`DecodedProximateRoot` output shape). Then
`αGenuine t = (Hasse_t p_a)(x₀) + T·(Hasse_t p_b)(x₀)` — both coefficients are **CONSTANTS in F** (deg_X = 0), and **α_t = 0 for t ≥ k outright**. The weight-1 budget holds with room to spare (deg_X c₀ = 0 ≤ 1, and the c₁-slot constant), at every order, with no growth analysis.

3. **So the discharge plan is**: compose (a) the decode-lane production "γ = expansion of p_a + T·p_b around x₀" (the #304 stream's current frontier — FactorPigeonhole + DecodedProximateRoot + the inhabited FaithfulFrontierData give the per-place branch ↔ decoded-pair assignment) with (b) a small Hasse-coefficient extraction lemma: `coeff t (expansion of q at x₀) = (hasseDeriv t q).eval x₀` (essentially in Mathlib: `Polynomial.taylor`/`hasseDeriv` API) and T-linearity of the Hasse operator. Then `alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget`'s budget hypothesis is discharged on the decode-lane's output, closing the monic-quadratic weight invariant END-TO-END — and the same argument is d_H-independent on the genuine-decode side, which may also collapse the d≥3 'shape' wall (the curve-collapse vs fixed-curve gap dissolves when γ is pinned to a decoded pair rather than an abstract 𝒪-element).

The F4/F7 unsatisfiability findings (rational/Ppoly converters) don't block this: they refute SYNTHETIC representations of γ; the decode lane produces the representation constructively where it exists, which is the only regime the MCA bound needs (cells with ≥2 members produce decoded pairs by the pigeonhole).

=== comment 46 (lalalune) ===
## Unit (4) CLOSED — ℓ-ary final splice landed (`ddc44f44b`, `MCAConjectureEllaryReduction.lean`, 15/15 axiom-clean)

The verbatim `mca_johnson_bound_CONJECTURE` (Conjecture 4.12, Johnson regime, errStar = (parℓ−1)·2^{2m}/(|F|·(2μ)⁷)) is now reduced at **EVERY** `parℓ = Fin L`, `L ≥ 2` (power exponents `exp j = j`) to the same per-δ deep input as the landed pair case — through the proven curve seam (`hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`) and `epsMCACurve`:

**The ℓ-ary endgame pivot (new, proven):** `curveGap`/`curve_match_card_le` — a non-trivial degree-<L gap polynomial has ≤ L−1 roots per disagreement coordinate (Mathlib `card_roots'`), so `curve_endgame_count` gives improving scalars ≤ (L−1)·n. **This is exactly where the conjecture's (parℓ−1) factor enters** — at L = 2 it degenerates to the proven `affine_match_card_le_one` pivot.

**ℓ-ary capture + Claim 1:** `CurveCaptured` (the polynomial-tuple shape `∑ⱼ C(γʲ)·aⱼ` that `GSCurveTuple.curve_tuple_of_hammingDist` produces at Z := γ), `curveCaptured_improve`, `curve_claim1_dichotomy` at threshold (L−1)·n, `curve_bad_card_le_of_claim1_cells` (per-stack bad set ≤ Lc·(L−1)·n).

**The numeric residual:** `CurveJohnsonNumericBound` := `epsMCACurve ≤ ofReal((L−1)·johnsonBoundReal)` — discharged from cells by `curveJohnsonNumericBound_of_claim1_cells` with **the SAME GS list shape `Lc ≤ (m+½)/√ρ₊` as the pair case** (the (L−1) cancels: numeric edge = proven pair closed form × (L−1), pure monotonicity, arithmetic core NOT re-derived).

**Headlines:** `mca_johnson_bound_CONJECTURE_ellary_of_curveJohnsonNumericBound` (per-δ residual at η := μ(δ) ⟹ verbatim conjecture at Fin L) and `mca_johnson_bound_CONJECTURE_ellary_of_claim1_cells` (per-δ per-stack cells ⟹ same). Plus `curveJohnsonNumericBound_of_epsMCACurve_le_johnsonBoundReal` (unscaled input is a stronger sufficient condition, via `johnsonBoundReal_nonneg`).

**Sanity at L = 2 (proven):** `curveJohnsonNumericBound_two_iff` — the ℓ-ary residual at L = 2 **is** the pair `JohnsonNumericBound` (via `epsMCACurve_two_eq_epsMCA`); `mca_johnson_bound_CONJECTURE_pair_via_ellary` re-derives the landed pair theorem from the identical hypothesis through the ℓ-ary route.

All audits `[propext, Classical.choice, Quot.sound]`. ArkLib.lean regenerated (also registers Hab25S4Wire, IndexedMarginalBound, MCAJohnsonBound missed by earlier landings).

**Updated #302 ledger:** (2) ✅ · (3) ✅ · **(4) ✅ CLOSED — both WHIR side and conjecture splice, at every parℓ** · (1) remaining. **The single remaining deep input for the FULL conjecture at every parℓ is now exactly the per-cell capture data** — pair form: `AffineCaptured` cells (BCIKS20 Claim 5.7 + Steps 5–7 + App C, converging with #138/#139); ℓ-ary form: `CurveCaptured` cells above (L−1)·n, whose S6 tuple kernel is already proven (`GSCurveTuple`). On the UD window the pair capture is proven (`Hab25CaptureKernelUD` + `johnsonNumericBound_of_window'`, c71240ad7); the ℓ-ary window analogue is the natural next brick.

=== comment 47 (lalalune) ===
**K1 LANE COMPLETE + NUMERIC COUNT LANDED** (commits e3cfed8fa, c71240ad7, e04b706ef, b9f4e4bb1 — all axiom-clean).

Since the K1-production post, four more capstones:

1. **`Hab25WindowCount.lean`** — the depth-0 chain closes **unconditionally**: `badScalars_card_le_of_window` (every stack has ≤ n bad scalars on the window `2n+k ≤ 3⌈(1−δ)n⌉`, zero hypotheses — global decode family by choice + `cell_card_le_of_decode_family_window`), and `johnsonNumericBound_of_window'` — **JohnsonNumericBound holds outright on the window** given only `0<k`, `k+1≤n`: the numeric side condition `n/|F| ≤ johnsonBoundReal` is **proven** (`card_div_le_johnsonBoundReal`, the L=1 case of the ℓ-budget edge; `hab25_ell_budget_ge_one` from ρ₊≤1 + m≥3 gives budget ≥ 350).

2. **`exists_cell_production_total`** — unit (2)'s producer (`gs_existence_over_ratfunc_zDegree_card`, landed by the parallel agent) is now composed in: **no interpolant hypotheses remain**. Only `1<k, k+1≤n, 1≤m, δ≤1, δ<gs_johnson` + the cells/families/factor surfaces out.

3. **`bad_card_le_numeric`** — the per-stack **Hab25 Theorem-2 union bound shape**: `#badScalars ≤ (gs_degree_bound k n m/(k−1) + 1)·T` modulo only the K4 input (`Irreducible R` + decode family + matching-factor surface ⇒ cell ≤ T). Uses the new `card_posDegree_factors_le` (distinct positive-degree factors ≤ deg) + Y-degree extraction from `Conditions.Q_deg`.

**Scope finding for the budget lane** (important): the Cramer route's degenerate-cell budget `T₀ = n·|constraintIndices m|·gs_degree_bound ≈ m³√ρ·n²` is **one factor of n coarser** than BCIKS20 Claim 5.4's graded count `D_YZ ≤ (ℓ³/6)ρn ≈ m³n/√ρ`. For the final `N/|F| ≤ johnsonBoundReal` numeric edge the n² budget does NOT fit (needs N ≲ m⁵n/ρ^{3/2}); the n¹ graded budget fits with m²/ρ to spare. So one refinement remains in the budget lane: **the graded Z-degree dimension count** (replay the in-tree `coeffsToPoly`/`constraintMap` count with the Z-grading, BCIKS20 §5.2.1) to replace the Cramer bound. The cell/count machinery is parametric in T, so this slots in without rework.

**Remaining for #302**: (a) the graded D_YZ count (≈300L, fully designed, uncontested); (b) K4 beyond the unique-decoding window (BCIKS20 Steps 5–7 Hensel capture — the single deep wall, converging with #138/#139/#304); (c) ℓ-ary S7+ combinatorics. Everything else is **done and wired end-to-end**.

=== comment 48 (lalalune) ===
**FLAGSHIP: UNCONDITIONAL WHIR PAIR MCA ON THE UNIQUE-DECODING WINDOW** (e54770962, `ProofSystem/Whir/Hab25WindowMCA.lean`, axiom-clean) + the K4 seam (cce108f1b, `Hab25K4Seam.lean`).

`hasMutualCorrAgreement_genRSC_pair_of_window`: for `B* ⪆ 2/3` (window `2n + 2^m ≤ 3⌈B*·n⌉`) and `√ρ ≤ B*`, the affine-line power generator `genRSC (Fin 2) φ m exp` has **mutual correlated agreement with the conjecture's exact pair error** `errStar(δ) = 2^{2m}/(|F|·(2·min(1−√ρ−δ, √ρ/20))⁷)` — **no capture hypothesis, no numeric side condition, nothing left**. This is the first unconditional instance of the #302 Johnson MCA chain (mca_johnson_bound restricted to the UD window).

Composition trick worth recording: the fixed-η `Hab25WhirBridge` interface cannot express the per-δ `η := μ(δ)` that the conjecture comparison needs, but the window JNB (`johnsonNumericBound_of_window'`) is **η-free** — so compose per-δ at the `epsMCA` seam (`hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`) instead: JNB at η:=μ(δ) + `johnsonBoundReal_le_errStar_real` + `ofReal` mono. Ceiling monotonicity (`Real.toNNReal_le_iff_le_coe` + `Nat.ceil_le_ceil`) moves the window from B* to each δ.

Also landed: `johnsonNumericBound_of_K4` (`Hab25K4Seam.lean`) — the whole beyond-window chain is now literally one implication: **K4 (Steps 5–7 capture, per-cell `Irreducible R` + decode family + matching-factor surface ⇒ `|cell| ≤ T`) ⟹ JohnsonNumericBound ⟹ WHIR pair MCA**, with both arrows in-tree and the K4 input exactly what `exists_cell_production_total` produces.

Remaining: (a) graded D_YZ budget (agent running — Cramer's n² budget must become the C5.4-style n¹ budget for the beyond-window numeric edge), (b) K4 past the UD window (#138/#139 Hensel lane), (c) ℓ-ary.

=== comment 49 (lalalune) ===
## 2026-06-10: per-scalar capture landed — the S10 carrier is now ONE uniform algebraic family

Pushed (axiom-clean): `ArkLib/Data/CodingTheory/GuruswamiSudan/GSPerScalarCapture.lean`.

- `scalar_close_codeword_isRoot` — at every scalar `z` (nonzero specialization), every Johnson-close codeword of the fold `f₀+z·f₁` is a `Y`-root of the **single** specialized generic interpolant `Q₀(z)`.
- `scalar_close_codewords_card_le` — hence the per-scalar close-codeword count is `≤ natDegree(Q₀(z))`, bounded by the generic `Y`-degree **uniformly in `z`**.

This replaces the per-`z` ad-hoc close-lists with the specialization of one uniform algebraic object. The S10 cover now reduces to **branch organization only**: as `z` varies, the roots of `Q₀(z)` organize into the branches of the generic factors, and the close-root branches are affine in `z` — exactly the Hensel S6 step, whose local input (`HenselBranchRigidity.existsUnique_branch_series`, `card_branches_le_natDegree`) and rational case (`GSAffinePair.affine_pair_of_hammingDist`, via Lagrange) are already proven. The remaining gap is the branch-counting bridge between them.


=== comment 50 (lalalune) ===
**Two #302 bricks LANDED**: (1) `CheckedVerifier.lean` (10/10 axiom-clean) — `whirVerifyChecked`, a WHIR verifier making REAL oracle queries enforcing the model-independent sumcheck round-consistency equations `g_{s+1}(0)+g_{s+1}(1)=g_s(r_s)` per phase + the final zero-sum check, with **proven perfect completeness** against the honest `whirMakeTranscript` and non-vacuity theorems (acceptance forces the final equation; rejecting transcripts exist). The RBR leg is now a meaningful target instead of false-for-pure-true. (2) `ThresholdKSF.lean` (12/12 axiom-clean) — the reusable threshold knowledge-state-function construction (any round-indexed predicate with round-0 ↔ relIn + concat-stability yields a genuine `KnowledgeStateFunction`, all side conditions proven for arbitrary verifiers) + `rbrKnowledgeSoundness_indicator` + the WHIR relation-pair instantiations.

=== comment 51 (lalalune) ===
Codex focused pass (2026-06-10): WHIR/Hab25 status update.

Verified locally:
- `lake env lean ArkLib/ProofSystem/Whir/MCAJohnsonBound.lean` passes, with only an unused-section-variable warning.
- `lake env lean ArkLib/ProofSystem/Whir/ProtocolSoundness.lean` passes after keeping the dummy WHIR RBR surface honest: `whirVectorIOP_rbrKnowledgeSoundness_dummy` is a `Prop` residual, not a theorem, and `whirVectorIOP_isSecureWithGap_dummy_of_rbr` is conditional on that residual. Both print only `[propext, Classical.choice, Quot.sound]`.

Still open / useful next target: `lake env lean ArkLib/Data/CodingTheory/GuruswamiSudan/Hab25S4Wire.lean` times out at `exists_good_specialization_no_sq_linear` under the current local heartbeat cap, so the S4 weld needs either a local heartbeat bump that survives autosync or a proof refactor. This is build hygiene for the Hab25 splice, not a proof of the real WHIR soundness. The real #302 close remains the real verifier plus MCA/CA/capture-kernel chain.

=== comment 52 (lalalune) ===
**GRADED JOHNSON NUMERIC EDGE PROVEN — the beyond-window chain now closes modulo K4 alone** (8291c7acd, `Hab25GradedNumericEdge.lean`, all axiom-clean) + **ℓ-ary K1 cell production landed** (d4a26e7d8, `Hab25CurveCellProduction.lean`, all 7 axiom-clean).

**`johnsonNumericBound_of_K4_graded_closed`**: K4 (the Steps 5–7 capture, per-cell `Irreducible R` + decode family + matching-factor surface ⇒ `|cell| ≤ n·|cI|·(D/(k−1))`) **plus only structural hypotheses** (`k ≥ 7`, `k+1 ≤ n`, `√ρ ≤ 9/10`, `m = hab25M`) ⟹ `JohnsonNumericBound`. **No numeric side conditions remain anywhere in the beyond-window chain**: K4 ⟹ JNB ⟹ WHIR pair MCA, both arrows in-tree, matching the already-unconditional window regime. The constant chain: `y·r ≤ (7/6)(M+½)` from the GS degree-bound floor (`y·r·(k−1) ≤ (m+½)·r²·n = (m+½)k`), `√ρ₊ ≤ (15/14)√ρ` (`196(k+1) ≤ 225k` at `k ≥ 7`), `|cI| ≤ m²`, assembling to `5.63·M²(M+½)² ≤ 2(M+½)⁵` with ≥70 % margin at the worst corner (numerically validated at all admissible corners first, ≥3.4× margin).

**Agent-fleet review note**: both files in this update were initiated by background agents that died on session limits mid-task; the ℓ-ary cell file was complete and correct in its snapshot (verified in full review — faithful `McaDecodeCurve` destructuring, correct seam discipline, sound `Q₀ ≠ 0` derivation from `dd ≠ 0`) and just needed verification + landing; the numeric edge was rebuilt directly. The graded interpolant (59dbddc84) and the ℓ-ary GS chain (631ef4f7c) also passed full review — the graded dimension count is the genuine §5.2.1 argument with the column-wise `gsMatrixZ` degree bound doing the real work.

**Remaining for #302**: (a) K4 past the unique-decoding window (BCIKS20 Steps 5–7 Hensel capture — THE single deep input left, #138/#139 convergence; proven on the window in `Hab25CaptureKernelUD.lean`); (b) the ℓ-ary Claim-1 assembly on top of the curve cells + the L-ary graded Z-degree producer (mechanical mirrors). Everything else in the Johnson MCA chain is **proven and wired end-to-end**.

=== comment 53 (lalalune) ===
**ℓ-ARY LANE COMPLETE THROUGH DEPTH-0** (commits f6b561c10, d9679b9c9, 93293c631/a4f16b0b8, 7e0c4a818 — all axiom-clean; agent drafts reviewed line-by-line and taken over per operator instruction).

1. **`Hab25FiberPigeonhole.lean`** (built directly): the BCIKS20 **Claim 5.7 counting half** — `exists_fiber_component_pigeonhole`: any K4 cell has a `1/(Ω+2)`-majority sub-cell whose members all vanish on **one irreducible component** `H(Y,Z)` of the x₀-fiber curve `R(x₀,·,·)` (or all degenerate, killed by the Z-budget). Instance-free multiset conclusion. This was the open 'C5.7 x₀-fiber refinement + pigeonhole' item; what's left of C5.7 is the Step-6 branch input (#138/#139 kernel).
2. **`GSInterpolantZDegreeCurve.lean`** (killed agent left a complete green draft in /tmp — verified in full, landed): the L-ary graded producer, budget `n·|cI|·((L−1)·D/(k−1))` — linear in n.
3. **`Hab25CurveCapture.lean`** (built directly): `CurveCaptured` + `curve_endgame_count` (≤ n·(L−1) improving scalars via the (L−1)-roots fibration) + **`claim1_dichotomy_curve`** + the K4 seam `cell_card_le_of_curve_decode_family_pinning`.
4. **`Hab25CurveNumericCount.lean`** (built directly): `bad_card_le_numeric_curve(_of_pinning)` — the L-ary Theorem-2 union-bound count modulo only the L-ary pinning.
5. **`Hab25CurveCaptureUD.lean`** (built directly): **depth-0 K4 at arity L** — `exists_curve_tuple_of_decode_family_window` (the window `L·n+k ≤ (L+1)⌈(1−δ)n⌉` pins any decode family to one curve; **Lagrange interpolation in the scalar variable** replaces the pair's 2×2 solve: tuple `a_j = ∑_t ℓ_t.coeff j·P(ν t)`, curve identity by sum-swap, monomial reproduction from `eq_interpolate` at `X^j`) ⟹ `badScalarsCurve_card_le_of_window`: **every L-row stack has ≤ n·(L−1) bad scalars on the window, unconditionally**.

**The ℓ-ary chain now matches the pair chain exactly**: unconditional on the UD window; one implication (L-ary Steps 5–7 pinning ⟹ count ⟹ MCA) beyond it.

**Sole remaining deep input for all of #302**: the Steps 5–7 capture past the unique-decoding window (pair + L-ary share it) = Step-6 Hensel branch forcing on one irreducible fiber component (the exact surface `exists_fiber_component_pigeonhole` now produces) + Claims 5.8/5.9 — the #138/#139 kernel convergence.

=== comment 54 (lalalune) ===
**ALL #302 WIRING COMPLETE** (c5d49bf1d, `Hab25K4FiberReduction.lean`, axiom-clean).

The final plumbing gap is closed: `cell_card_le_of_component_K4` (+ `_pair`) reduces the K4 factor-cell obligation of `bad_card_le_numeric`/`johnsonNumericBound_of_K4_graded_closed` to the **per-component capture statement**, through the proven fiber pigeonhole: a capture bound `T'` for sub-cells on **one irreducible component `H(Y,Z)` of `R(x₀,·,·)`** plus the fiber-degenerate budget `T₀` (supplied by `fiberAt_coeff_natDegree_le` + `card_fiber_specialization_collapse_le` — the fiber inherits the graded Z-budget) bound every factor cell by `(Ω+2)·max(T',T₀)`.

**The complete state of #302** — every arrow below is in-tree and axiom-clean:

| Regime | Status |
|---|---|
| Window (pair): `2n+2^m ≤ 3⌈B*n⌉` | **UNCONDITIONAL** — `hasMutualCorrAgreement_genRSC_pair_of_window` with the conjecture's exact `errStar` |
| Window (arity L) | **UNCONDITIONAL count** — `badScalarsCurve_card_le_of_window` (≤ n(L−1) per stack) |
| Beyond window (pair) | per-component capture ⟹ `(Ω+2)max(T',T₀)` cells ⟹ `JohnsonNumericBound` (graded budget + proven numeric edge) ⟹ WHIR pair MCA |
| Beyond window (arity L) | identical chain through the curve mirrors |

**The single surviving obligation** (now a pure-math statement with zero plumbing on either side): on one irreducible `H(Y,Z)` with more than `T'` planar points `(γ, P γ(x₀))` of decode polynomials, the family is pinned to a polynomial curve — BCIKS20 C5.8 (Hensel branch forcing, the in-tree `HenselBranchRigidity`/βHensel objects) + C5.9 (Z-linearity, monic cases already proven in the #138/#139 stream) + the S5 good-`x₀` supply (in-tree discriminant lane). This is exactly where #302, #138, #139, and #304 converge, and it is the prize-grade kernel — not fabricating closure on it; everything else is done.

=== comment 55 (lalalune) ===
**C5.8 RIGIDITY HALF PROVEN** (354ba47b8, `Hab25BranchPinning.lean`, all axiom-clean) — the per-component capture is now reduced to pure branch **existence**.

`pinning_of_global_branch`: given a global integral branch `pHat ∈ F[Z][X]` with the C5.8/C5.9 budgets (`deg_X < k`, `deg_Z < L`), per-γ divisibility into `R|_γ`, the fiber match at a separable good point `x₀` (the S5 output), the decode family **is** the branch's specialization family — `decode_eq_specialized_branch` runs the in-tree Hensel rigidity (`branch_eq_of_fiber_eq_of_separable`) per-γ: through a simple fiber point, the branch is unique, so decode = specialized branch. `map_eval_eq_curve_sum` then converts the branch into the literal polynomial-curve pinning shape (`∑_j C(γʲ)·a_j` for the coefficient transpose), and `cell_card_le_of_global_branch` closes the cell bound through the L-ary dichotomy.

**The remaining open core of all of #302, in its final minimal form**: *existence* of the global branch `pHat` with the degree budgets — i.e., the Hensel branch of the interpolant over the function field through the component's section has polynomial (not just power-series) truncation with `deg_Z < L` coefficients. That is precisely the Λ-weight/βHensel coefficient-bound kernel (#138/#139: Lemma A.1/Claim A.2; monic cases in-tree; open core `SuccDivWeightLe_of_monic`). Every other sentence of BCIKS20 §5 + Hab25 §3 is now formalized: uniqueness/rigidity (this file), counting (pigeonhole, dichotomies, endgame counts), budgets (graded producers, both arities), specialization bridges, numeric edges, and both unconditional window regimes.

=== comment 56 (lalalune) ===
**MILESTONE: all three named `whirVectorIOP` residuals of `Protocol.lean` are now THEOREMS** (verified axiom-clean on main): `whirVectorIOP_perfectCompleteness_holds` (`ProtocolCompleteness.lean`), `whirVectorIOP_rbrKnowledgeSoundness_indicator` and `whirVectorIOP_isSecureWithGap_indicator` (`ThresholdKSF.lean`) — the RBR leg discharged via the threshold knowledge-state-function at the indicator budget (error 1 at the final-randomness round, 0 elsewhere; the `_folded` variant tracks the genuine folded-oracle δ-closeness predicate under the smoothness data). The honest remaining gap to SUB-UNIT error at the final round: the checked verifier (`CheckedVerifier.lean`, landed) + the Schwartz-Zippel flip bound — i.e. the protocol side of #302 is now reduced to one quantitative estimate, with the Johnson-MCA analytic lane (parallel session) the other half.

=== comment 57 (lalalune) ===
## 2026-06-10: post-#13-closure — the curve-UDR plan for Cor 4.11 at ALL arities (UD regime)

With #13 closed end-to-end, the next WHIR lever (no Johnson kernel needed): generalize the proven pair UDR bound to degree-`<L` curves, closing `mca_rsc` (Cor 4.11, UD branch `BStar = (1+ρ)/2`) for **every** `parℓ` via the proven seam `hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`.

**Target**: `epsMCACurve_udr_le : epsMCACurve (RS[F,α,k]) L δ ≤ (L−1)·n/|F|` in the UD regime — matching `genRSC`'s UD-branch `errStar = (parℓ−1)·2^m/(ρ|F|)` exactly.

**The generalization of `badCount_udr_le`** (whose pair proof is the template, MCAUDRBound.lean:53):
1. Pick `L` distinct good scalars `γ₁..γ_L`; set `T := ⋂ S(γᵢ)`, `|T| ≥ n − L(n−t)` (inclusion–exclusion as in `hTcard`).
2. Lagrange differences: the codeword-curve coefficients `c_0..c_{L−1}` solve the Vandermonde system on the `w(γᵢ)`; each `c_t ∈ C` (linear combinations — the `Finset.sum` analogue of the pair's `(γa−γb)⁻¹ • (w γa − w γb)`); on `T`: `c_t = u_t` (the curve through the `L` agreeing points is the data curve).
3. UD collapse: every good `γ`'s closest codeword equals `∑ c_t γ^t` — distance argument on `(T ∩ S γ)ᶜ` with the generalized regime `(2L−1)(n−t) < d`.
4. Bad scalars are roots of the nonzero polynomial `γ ↦ (u−c)-mismatch` at some coordinate of the small support — count ≤ `(L−1)·(supp ≤ L(n−t))` per the root-counting on each coordinate (degree `L−1` in `γ`).
5. Wire through `epsMCA_le_of_badCount_le`'s curve analogue + `epsMCACurve` and the seam → `mca_rsc` for all `parℓ` (UD branch).

The pair case (`mca_rsc_pair_holds`, landed) validates the seam arithmetic. Step 2's Vandermonde/Lagrange-difference system is the only structurally new algebra (the in-tree `Lagrange.interpolate` machinery applies — the coefficients are `C`-linear in the `w(γᵢ)`).


=== comment 58 (lalalune) ===
**BRANCH EXISTENCE PROVEN AT deg_Y = 1** (b53dcde1f, `Hab25LinearFactorCapture.lean`, all axiom-clean).

For `Y`-linear factors the C5.8 branch existence is now closed with **no Hensel and no Λ-weight counting**: `linear_factor_decode_eq` (factor theorem at Y-degree one: every decode satisfies `p·G.coeff 1 = −G.coeff 0`), `linear_factor_decode_unique` (the family carries **no choice** at nonvanishing leading coefficient), `linear_factor_family_identity` (the global identity `P γ·r₁|_γ = −r₀|_γ` — the branch IS the rational section `−r₀/r₁`, its data inheriting R's degree budgets), and `linear_factor_global_dvd` (a cleared section is the literal `pHat` of `pinning_of_global_branch`).

**Final form of the #302 open core after this session**: branch existence for components of `deg_Y ≥ 2` only — the function-field Hensel series with Λ-weight coefficient bounds (#138/#139 `SuccDivWeightLe_of_monic` lane). Everything else, in both regimes and both arities, is proven and wired: rigidity (`Hab25BranchPinning`), the deg_Y=1 existence (this file), counting (pigeonhole/dichotomies/endgame at both arities), budgets (graded producers, both arities), supplies (good-x₀, fiber-degenerate, separability lane), numeric edges, the unconditional window MCAs, and the single-implication beyond-window chains.

=== comment 59 (lalalune) ===
**OPEN-CORE STATE CORRECTION + CONVERGENCE MAP** (after reading the live #138/#139 lane in-tree):

1. The literal `SuccDivWeightLe_of_monic` is **refuted** in-tree (`P1MonicWeightRefutation.weight_refuted`, a `d = 2` instance where the C5.9 shape holds but the weight budget fails) — the refutation exists **because bare `ClaimA2.Hypotheses` does not bound `deg R`**.
2. The live route is the P2/monic lane: `S5GenuineZLinearQuadratic.lean` **closes Claim 5.9 (T-form) unconditionally for monic `H` with `deg_Y ≤ 2`** (integrality + canonical `modByMonic` representative — the `{1,T}`-span is automatic at `d_H = 2`), and reduces the #138 weight invariant there to **the per-order X-degree budget alone** (`alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget`).
3. **The convergence observation for the #138/#139 owners**: in the #302 chain the factor `R` is NOT arbitrary — it divides the GS interpolant and therefore carries the `D_X ≤ gs_degree_bound` budget from `Conditions.Q_deg` (extractable exactly as in `bad_card_le_numeric`'s Y-degree leg, via `natWeightedDegree` + `natDegree_map_eq_of_injective`). The refutation's obstruction (unbounded `deg R`) is **absent in the consuming context**. If the per-order budget can be derived from the global `D_X`/`D_YZ` budgets of the interpolant (the genuine Λ-weight content), the monic-quadratic capture composes immediately with the new surface on my side: `pinning_of_global_branch` (b53dcde1f stack) consumes exactly a global branch with `deg_X < k`, `deg_Z < L` — which is what integrality + T-form Z-linearity + the budget produce for monic quadratic `H`.

Current totals on #302 from this session: window MCAs unconditional (both arities), beyond-window chains single-implication with all hypotheses produced in-tree, C5.8 rigidity half proven, branch existence proven at `deg_Y = 1`. Open: branch existence at `deg_Y ≥ 2` = the per-order budget input of the P2 lane (plus the non-monic normalization and the `deg_Y > 2` span problem per `ZLinearClosureAudit`).

=== comment 60 (lalalune) ===
**Schwartz–Zippel core LANDED** (`SchwartzZippelCore.lean`, 3/3 axiom-clean): `listPoly` (the Horner polynomial of `CheckedVerifier`'s `listEval`) with the evaluation bridge, the degree bound, and `card_listEval_eq_le` — the salvage set of two genuinely different sumcheck chains has at most `max(len)` challenge points. Against `|F|` this is the per-round `d/|F|` flip estimate for upgrading the indicator RBR budget to sub-unit error at the checked verifier. Remaining for the quantitative WHIR RBR: thread this bound through `ThresholdKSF.rbrKnowledgeSoundness_indicator`'s flip event at `whirVerifyChecked`'s per-round predicate (the probability-side accounting: uniform challenge ∈ salvage set ⟹ ≤ maxLen/|F|).

=== comment 61 (lalalune) ===
**`probEvent_salvage_le` LANDED** (merged into `SchwartzZippelCore.lean`, axiom-clean): the complete per-round quantitative estimate — in any game drawing a uniformly-dominated challenge and then running a continuation whose success forces the salvage equation between two genuinely different sumcheck chains, the success probability is ≤ `maxLen/|F|` (`card_listEval_eq_le` × `probEvent_bind_le_uniform_marginal`). The sub-unit WHIR RBR now reduces to one mechanical step: threading this bound through `ThresholdKSF`'s flip event at `whirVerifyChecked`'s per-round predicate.

=== comment 62 (lalalune) ===
**STEP-6 QUANTITATIVE SKELETON LANDED** (f73489959, `Hab25BranchDichotomy.lean`, all axiom-clean).

`branch_capture_dichotomy`: any candidate global curve `pHat ∈ F[Z][X]` either **divides `R` globally** (the branch exists — `global_branch_iff_eval_zero`, factor theorem for the monic-linear candidate; feeds `pinning_of_global_branch` directly) or its per-γ capture set is bounded by the Z-budget of the evaluation defect `R.eval pHat` (`eval_specializes` + the one-level collapse count). `pinned_dichotomy_of_section` runs it through the C5.8 rigidity: **the decode family is pinned globally by the candidate, or the candidate agrees with it at ≤ M scalars.**

This is the exact quantitative frame of BCIKS20 Step 6, in the interpolant's own vocabulary with no function-field machinery. The open `deg_Y ≥ 2` content of all of #302 is now the sharpest it can be stated: **produce a candidate whose pin count beats the defect Z-budget** — equivalently, show that on a large cell the Hensel data forces `R.eval pHat = 0` for the interpolating candidate. The elementary degree-chase fails precisely by the factor `D_Y` (monodromy), which is what the Λ-weight bounds overcome; both the budget arithmetic (graded producers) and the consuming seam (pinning + dichotomies + counts, both arities) are fully in place around it.

=== comment 63 (lalalune) ===
**QUANTITATIVE ENTRY POINT for the final statement** (analysis note, no new file):

Comparing the landed constants: the per-cell threshold of the beyond-window chain is `T = n·|cI|·(D/(k−1))` (`bad_card_le_numeric_graded`) — **exactly the graded Z-budget `B`** of the interpolant's coefficients. And the defect budget in `branch_capture_dichotomy` for a `deg_Z < L` candidate is `M = B + D_Y·(L−1)` — i.e. `T + D_Y·(L−1)`, a razor-thin margin above the threshold.

So the single remaining statement of #302, in its final quantitative form: **on a cell of size `> B + D_Y(L−1)`, some candidate `pHat` with `deg_X < k`, `deg_Z < L` pins `≥ B + D_Y(L−1) + 1` of its scalars** — then `pinned_dichotomy_of_section` forces the global branch and the chain closes end-to-end. Verified obstruction: the naive Lagrange candidate through `N` cell nodes pins `≥ N` but has defect budget `B + D_Y(N−1)`, losing by exactly the factor `D_Y` (monodromy) — any argument beating it must use the Hensel/curve structure (the points lying on ONE component `H`, produced by `exists_fiber_component_pigeonhole`), which is the Λ-weight content. All four ingredient surfaces (`pinned_dichotomy_of_section`, the pigeonhole sub-cell, the S5 separability lane, the graded budgets) are in-tree and composable the day the candidate-production lemma lands.

=== comment 64 (lalalune) ===
**Bounded-flip RBR shell LANDED** (merged into `ThresholdKSF.lean`, axiom-clean): `rbrKnowledgeSoundness_of_flipBound` — the sub-unit generalization of the indicator theorem, taking the threshold-round budget as an explicit flip-probability hypothesis (all other rounds at 0). The quantitative chain is now fully stocked: `card_listEval_eq_le` (salvage-set size) → `probEvent_salvage_le` (game bound ≤ maxLen/|F|) → `rbrKnowledgeSoundness_of_flipBound` (per-round budget shell). The last step to the sub-unit WHIR RBR theorem: instantiate the shell at `whirVerifyChecked`'s prefix sumcheck-consistency predicate with ε := maxLen/|F| supplied by the salvage bound (the predicate's concat-stability legs mirror the landed `whirFoldedClosePred_concat`).

=== comment 65 (lalalune) ===
## ✅ 2026-06-10: the curve-UDR arc COMPLETE — RS curve MCA proven at every arity (UD regime)

The three-stage plan (comment `4668760311`) is fully executed, all axiom-clean on `main`:

1. **`exists_curve_coeffs`** (`CurveUDRCoefficients`, commit `6ecda13e0`) — the degree-`<L` interpolating codeword-curve: coefficients in the code, data-row agreement by interpolation uniqueness.
2. **`curveBadCount_udr_le`** (`CurveUDRBadCount`) — the combinatorial core: in the curve unique-decoding regime `(L+1)(n−t) < d`, bad scalars number ≤ `(L−1)·L·(n−t)` — via the `L`-fold agreement intersection, unique-decoding collapse of *every* good scalar onto one curve, and per-coordinate root counting.
3. **`epsMCACurve_rs_udr_le`** (`CurveUDRBound`, commit `bdd2150f8`) — **the headline**: for Reed–Solomon of degree `k` and ANY arity `L ≥ 2`, `ε_mcaCurve(RS, L, δ) ≤ (L−1)·L·(n−t)/|F|` in the regime — the witness-extraction wiring through the per-stack count.

Composed with the already-proven seam `hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`, this discharges **WHIR Corollary 4.11 (unique-decoding branch) at every folding arity** — generalizing the landed pair case (`mca_rsc_pair_holds`) from `L = 2` to all `L`, with the honest curve-UD radius `δ ≲ (1−ρ)/(L+1)` (the L-fold collapse genuinely requires it; the budget `(L−1)L(n−t) ≤ (L−1)n` holds inside the regime, fitting `genRSC`'s UD-branch `errStar` exactly).

**Remaining for #302:** the Johnson-radius branch (`√ρ`) — the GS-over-`F(Z)`/Hensel program, whose proven periphery and single remaining kernel (the X/Z coupling) are mapped in the earlier comments. The UD-regime side of WHIR's MCA foundation is now complete at all arities.


=== comment 66 (lalalune) ===
**KERNEL ATTACK FINDING (direct analysis): the loose A.1 route is QUANTITATIVELY INSUFFICIENT — DivWeightLe is necessary, not just convenient.**

Decoded the weight semantics at the definition level (`weight_Λ` in RationalFunctionsCore.lean:677): `Λ(Z^a·Y^t) = t·(D+1−d_H) + a`, weight of zero = ⊥. So the target `weight_Λ_over_𝒪 ≤ 1` for the branch coefficients is **Z-affineness** — literally C5.9 sharp, with no slack: my consumer (`pinning_of_global_branch`) needs `deg_Z < L`, the same sharpness at `L = 2`.

**The pruning result**: suppose the loose Lemma-A.1 growth bound `Λ_𝒪(β_t) ≤ (2t+1)·d·D` were proven unconditionally (the in-tree `βHensel_weight_bound_of_alphaWeight` shape, decircularized). The A.2 vanishing threshold it yields is `~ d_H·Λ(β_k) ~ d²·k·D` with the weight parameter `D ≥ totalDegree H ≥ deg_Z H`, and on the fiber of the graded interpolant `deg_Z H` is only bounded by the graded budget `B ~ m³n/√ρ`. Per-cell bound: `~ (m/√ρ)²·ρn·m³n/√ρ ~ m⁵n²·ρ^{−3/2}·…` — **quadratic in n**. The proven numeric edge (`graded_budget_div_le_johnsonBoundReal`) allows only `N ~ m⁵n/ρ^{3/2}` — **linear in n** (it relies on the integer-sharp improvement count, not the paper's relaxed `(ℓ⁷/3)(ρn)²`). The loose route loses by exactly a factor of `n`. Conclusion: **only the sharp W-clearing `DivWeightLe` (AlphaWeight.lean:174 — `βHensel t = a·W𝒪^{t+1}·ξ^{2t−1}` with `Λ(a) ≤ 1`, `t = 0` proven, successors open) can close #302's beyond-window chain.** Anyone attacking the kernel should work `DivWeightLe_succ` directly (or weaken the numeric edge to tolerate `n²`, which would require re-deriving the whole Johnson chain at the paper's coarser count — strictly worse).

This prunes the 'prove loose A.1 first' direction that both the paper's narrative and the P1 file layout suggest.

=== comment 67 (lalalune) ===
Pushed a small validation cleanup on the landed Schwartz-Zippel core: `b98686ba6 chore(#302): lint clean Schwartz-Zippel core`.

Scope: removed the unused final `simp` arguments in `Whir302SZ.listPoly_eval`; no theorem statement or proof dependency changed.

Checked:
`lake env lean ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean`

Axiom audit remains clean of `sorryAx` for `listPoly_eval`, `listPoly_natDegree_lt`, `card_listEval_eq_le`, and `probEvent_salvage_le`.

=== comment 68 (lalalune) ===
**Cross-issue convergence note (from `a3fff5b42` on #304): this issue's remaining math is now ONE named production.**

`UnifiedExtractionTarget.lean` machine-checks that BOTH #304 cores (`StrictCoeffPolysResidual` + the corrected boundary half) flow from the single producer `UnifiedProducer k deg domain δ` (per word-stack count-triggered faithful `CurveFamilyData`), and exports the **closed-boundary keystone** `correlatedAgreementCurves_johnsonClosed_of_producer`: `δ_ε_correlatedAgreementCurves` at `δ = 1−√ρ` with explicit positive error `max(errorBound(cell), (n+1)/|F|)`.

For #302 this means: the Johnson MCA bound's entire remaining surface = instantiate `UnifiedProducer` from the assembled GS matching lane (S10-converse → double pigeonhole → per-z proximate roots → ab-initio truncation → converter → extraction, all landed) — the Taylor-repaired keystone front door `correlatedAgreement_affine_curves_of_GS_surface_taylor` + `SectionGlobalLift` are the active instantiation path. Combined with the landed ℓ-ary reduction (`MCAConjectureEllaryReduction`), the K4 seam, the graded numeric edge, and the curve-UDR arc, the verbatim conjecture chain is complete modulo that one producer.

=== comment 69 (lalalune) ===
Codex WHIR/CA status refresh (2026-06-10):

The current working-tree check suggests the WHIR pair-reduction import cone is not the immediate blocker. After fixing `BCIKS20/Claim59.lean`'s missing finite/decidable field hypotheses, this build passes:

`lake build ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffProducer ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ThresholdInterface ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Claim59 ArkLib.ProofSystem.Whir.MCAConjecturePairReduction`

Also focused-checked: `GuruswamiSudan/Hab25S4Wire.lean` after removing a stale heartbeat override. So the remaining #302 work is back to the substantive MCA/Johnson/candidate-production kernel described above, not missing producer `.olean`s.


=== comment 70 (lekt9) ===
**Correction to the kernel-attack finding (the `DivWeightLe_succ` prescription): the named kernel is refuted in BOTH regimes under the current hypotheses — landed `c2bec0136` (`DivWeightLeMonicRefuted.lean`, axiom-clean ×2).**

The earlier pruning analysis correctly showed only the sharp W-clearing `DivWeightLe` can close the beyond-window chain at the proven numeric edge, and advised attacking `DivWeightLe_succ` directly. That target is **not provable from the current two-field `ClaimA2.Hypotheses`**:

- **Non-monic** (already in-tree): `AlphaWeightClearedObstruction.not_DivWeightLe` kills the full kernel via the `t = 0` base (lc ∤ X).
- **Monic** (new): the valid separable witness of `P1MonicWeightRefutation` (`H = Y² − 2`, `R = Y² − 2 + u·s` over `ZMod 3`) kills the `t = 1` instance — for monic `H` the `W𝒪`-power is 1 and the clause collapses to exactly the `weight_refuted` shape. New: `not_divWeightLe_monic_witness : ¬ DivWeightLe myH 0 myR myHyp hH 2`, plus `not_henselQuotient_weight_le` (the isolated explicit core of #138 fails too, through `succDivWeightLe_iff_henselQuotient_weight`).

**Actionable redirect:** the prerequisite for any successor-step attack is a hypothesis strengthening — a `deg R` bound relative to `D` added to (or alongside) `ClaimA2.Hypotheses`. The exact boundary is already pinned in-tree at order 1: `weight_refuted` (lift direction carries ground-X degree → weight 2 > 1) vs `P1MonicWeightHolds.weight_holds` (constant lift direction → weight 1). In the genuine GS context the interpolant IS degree-bounded, so the right move is: (1) define the degree-bounded hypothesis pack, (2) re-prove `DivWeightLe_zero`/the resummed base under it, (3) attack `DivWeightLe_succ` there — where the Newton-cancellation absorbing Λ(ξ⁻¹) is the genuine remaining math.

=== comment 71 (lalalune) ===
## Full-frontier synthesis + approach portfolio (3-5 reasonable / 3-5 novel per open node) — #301/#302 convergence

Three-lane recon completed (GS matching lane, Hensel/DivWeightLe chain, repo paper notes). **The GS matching lane (S10-converse → Claim-5.7 pigeonholes → per-z proximate roots → truncation → converter → extraction → `UnifiedProducer` consumers) is internally CLOSED** — all 7 stages verified axiom-clean. The open mathematics of #301+#302 is exactly:

**Node A** — `IntegerRepCentreSupply x₀ Q₀` (GSSurfaceSupply.lean:342): ∃ irreducible positive-degree `H ∣ evalX(C x₀) Q₀` with the slice **separable over the non-field base F[Z]**, for the reducible integer representative `Q₀` (graph route has it for its irreducible `R`).
**Node B** — `SurfaceSeparabilitySupply Q₀` (GSSurfaceSupply.lean:359): trivariate Bézout separability `A·Q₀ + B·Q₀′ = 1` over `F[Z][X]`; only the linear case currently producible.
**Node C** — Claim-5.9 per-coefficient T-form for `d_H ≥ 3` (converter proven only ≤ 2).
**Node D** — `DivWeightLe_succ` under a **degree-bounded hypothesis pack** (the redirect of `c2bec0136`): Newton cancellation absorbing Λ(ξ⁻¹); boundary pinned at order 1 (`weight_refuted` lift-direction-X-degree vs `weight_holds` constant-direction).
**Node E** — numeric legs (`hClaim1Num`-class elementary inequalities + Johnson boundary quantization).

### Node A+B portfolio
*Reasonable:*
1. **Radical/good-centre production** (machinery EXISTS): replace `Q₀` by its squarefree part (`GSSquarefreePart.gs_interpolant_squarefree_part` preserves S3/S4 data; `discr_radical_ne_zero`), choose `x₀` by discriminant non-vanishing (`Hab25SeparableSupply.exists_good_specialization_no_sq_linear`, `radical_rep_good_specialization_charZero`) ⟹ slice separability; pick `H` = any irreducible factor of the separable slice.
2. **Resultant certificate**: slice separable ⟺ `Res_Y(slice, slice′) ≠ 0` in `F[Z]`; nonzero resultant at SOME `x₀` from the trivariate discriminant being a nonzero polynomial in `X` (degree budget ⟹ ≤ deg many bad centres < |F|).
3. **Re-point the capstone** (consolidation): weaken `hR : R.Separable` to `Squarefree R` + slice-level separability — audit which uses of `hR` genuinely need trivariate Bézout vs squarefree (the cofactor/certificate legs may only need slice-level data).
4. **Graph-route transfer**: `F8` forces the surface factor onto `Q₀`, but `Hypotheses` could be carried by the GRAPH `R` (already supplied) with a divisibility bridge `H ∣ slice(R) ∣ slice(Q₀·unit)` — produce A for `Q₀` from the bundle's `H` + factor-transfer lemmas.
5. **Eisenstein/content split**: work in `F[Z][X][Y]` with content-primitive split; primitive part of the slice is separable iff its discriminant-content is a unit — reduce to content arithmetic (in-tree content-vanishing bricks from the descended-Claim-5.7 work).
*Novel:*
1. **Derivation-module route**: separability over `F[Z]` ⟺ the Kähler different/derivation module of `F[Z][Y]/(slice)` is torsion-free at the centre — prove via the in-tree Hasse-derivative machinery (`le_rootMultiplicity_iff_hasseDeriv`) instead of Bézout, char-free.
2. **Newton-polygon centre selection**: choose `x₀` tropically — the slice's Newton polygon at generic `x₀` is the trivariate polygon's fibre; separability fails only on the polygon's vertical-edge locus (finite, bounded by polygon data).
3. **Frobenius-descent (char p)**: inseparability of the slice means it's a `p`-th power composed with Frobenius — the in-tree descended-Claim-5.7 `coincidence-free char-p` bricks (Frobenius transfer, root attribution) refute that shape for GS interpolants directly (degree budget < p·anything).
4. **Probabilistic centre via Schwartz–Zippel on the discriminant surface**: |bad x₀| ≤ deg_X(disc) — make the existence statement quantitative and feed the same count into the S9 numeric leg (kills two nodes with one lemma).
5. **Idempotent/CRT splitting**: for reducible `Q₀ = ∏ Qᵢ`, trivariate separability ⟺ pairwise-coprime + each `Qᵢ` separable; produce the Bézout witnesses by CRT idempotents from the squarefree decomposition — reduces B to the irreducible case where the graph-route certificate applies.

### Node D portfolio (only if A+B+C don't subsume the BCIKS20-literal lane)
*Reasonable:* (1) define the degree-bounded pack `deg_X(R.coeff j) ≤ D − j` (the `hRgrade` shape ALREADY in `gammaGenuine_eq_trunc_of_surface`!) and re-prove `DivWeightLe_zero` + attack succ by the structured bound `βHensel_weight_structured`; (2) Taylor-coefficient degree bounds in the completed local ring (classical algebraic-function coefficient growth); (3) Cramer/resultant determinant degree counting for the t-th coefficient; (4) mathlib Henselian-ring transfer; (5) **bypass entirely**: A+B+C close `UnifiedProducer` through the surface lane — DivWeightLe becomes historical.
*Novel:* (1) **tropical/Newton-polygon**: Λ is a polygon slope functional; the cancellation = polygon convexity under the Newton-iteration map (min-plus induction, no coefficient computation); (2) symmetric-function conjugate-root accounting; (3) bounded-lattice self-map closure (Λ≤1 defines an F[X]-lattice preserved by the iteration); (4) algebraic generating function `Σ βHensel(t)Tᵗ` one-shot degree bound from its defining quadratic; (5) Wronskian/differential capture of the curve identity (differentiate the agreement identity in z, bypass Hensel).

**Execution begins with A+B via route A1/A4 (existing machinery) — the highest-EV path to `UnifiedProducer` and with it both `stirCheckingCABridge` (#301) and the WHIR MCA keystone (#302).**

=== comment 72 (lalalune) ===
**STEP-7 ELEMENTARY HALF COMPLETE + SLOPED INTERPOLANT** (5fb1a51bf `GSInterpolantSloped.lean`, 07b38ab95 `Hab25CandidateProduction.lean` — 13 new axiom-clean decls; the candidate file was a limit-killed agent's complete draft, reviewed line-by-line, one whnf fix [`degree_smul_le` for the WithBot calc], landed).

**1. The sloped (Y,Z)-degree interpolant** (`gs_existence_sloped`) — BCIKS20 Claim 5.4 inequality (5.7): integer interpolant with `deg_Z(coeff_Y b) ≤ D_YZ − b` at the **tight** budget `D_YZ = ∑_{wBI} b`, **unconditionally** — sloping costs exactly `∑ b` unknowns, absorbed by the in-tree dimension surplus with room +1. This is the Λ-weight input the P2 route needs (without the slope, `Λ(Q)` is unbounded and `Λ(α_t) ≤ 1` is unprovable).

**2. Candidate production** — the elementary half of Step 7, complete: `exists_rich_coordinates` (Claim 5.11 double counting), `curve_pin_of_node_agreement` (Claim 5.9 interpolation: k node values pin the decode to the Lagrange curve tuple), `capture_on_rich_subcell` + `cell_card_le_of_rich_coordinates` (`|E| ≤ T + k·M`, unconditional), the candidate builder with its **proven defect budget** `B + deg_Y R·(L−1)`, and the capstones: `global_branch_of_coordinate_upgrade` (Claim 5.10's output + surface + `|E| >` defect ⟹ **global branch** ⟹ the pinning chain closes) and `global_branch_or_card_le` (unconditional dichotomy with the honest `k·M` slack).

**THE OPEN CORE OF #302, FINAL NAMED FORM** — `CoordinateUpgrade`: at each of the k chosen coordinates, every cell scalar's decode value equals the fold value (the paper's `γ(x) = w(x,Z)` in 𝕃, Claim 5.10) — i.e. remove the witness-set-majority caveat. This is a **per-coordinate scalar statement**, strictly weaker-looking than the global branch, and it is exactly where Lemma A.1 (in-tree, proven) + the Claim A.2 weight growth (the #138/#139 Λ-weight kernel, now fed by the sloped budget above) enter. Everything else in BCIKS20 §5/App A + Hab25 §3, both regimes, both arities: **formalized, axiom-clean, composable.**

=== comment 73 (lalalune) ===
**CLAIM 5.10 FIRST HALF PROVEN** (5ec91e5b0, `Hab25FoldFiberCapture.lean`, 4 decls axiom-clean — green on first compile).

`fold_divides_fiber_of_many_agreements` / `fold_section_dvd_fiber`: a Z-linear section `w` agreeing with a root of the specialized fiber at **more than D_YZ scalars divides the fiber identically in Z**. The sloped budget (5fb1a51bf) is load-bearing and this is its first consumption: the defect `G(w(Z),Z)` has each term `coeff_b·w^b` of degree `≤ (D_YZ−b) + b·1 = D_YZ` — **uniform in the Y-exponent only because the budget slopes**. With the old flat budget the defect degree grows as `B + d`·(fold degree) and the root count never closes; with the slope it closes at the interpolant's own budget. Composition into the cell vocabulary: at any rich coordinate `t` (≥ |E|−M scalars with `P_γ(t) = w(t,γ)`, supplied by the landed Claim 5.11 double counting) with `|E|−M > D_YZ`, the fold section divides the fiber `R(t,Y,Z)` — the per-coordinate identity `γ(x)·`-side of Claim 5.10, in its exact paper form.

**The open core after this**: Claim 5.10's half (ii) only — assembling the per-coordinate fold-divisibility identities into the global branch. The obstruction is precisely that the fold rows are *words*, not polynomials, so the branch through them is a priori only analytic (a Hensel power series in X−x₀); bounding its coefficients to force polynomiality is the Lemma A.1/Claim A.2 Λ-weight content (#138/#139), now fed on both sides: the sloped interpolant budget above, and the per-coordinate divisibility surface from this file.

=== comment 74 (lalalune) ===
**ROUTE-MAP CORRECTION after attacking the assembly step directly**: half (ii) of Claim 5.10 is not an 'assembly of per-coordinate identities' — re-reading §5.2.5–5.2.7 against the in-tree state, the paper's order is: **Step 6 (Claim 5.9) = the branch is Z-linear with polynomial coefficients via the Λ-weight bound, FIRST**; Step 7 (Claims 5.10/5.11, now fully formalized) then counts agreement against that already-polynomial branch. So the open core is not an assembly lemma — it IS Claim 5.9 itself ( per order ⟹ branch = a + Z·b with bounded deg_X), i.e. exactly the /P2 kernel already mapped.

Two elementary bypass attempts, both refuted with explicit obstructions (recorded so nobody retries): (1) fold-interpolating candidates over k' > k coordinates — the composed defect X-degree grows as deg_X R + d·(k'−1), always outrunning the k' vanishing points for d ≥ 2 (the weighted degree only equalizes when the candidate has deg_X < k, but then it can match the fold at only k coordinates); (2) discriminant-vanishing from many Z-linear-rooted fibers —  has Z-linear fiber roots at every square t with no global branch; the decode data excludes it (its specializations have no polynomial roots), confirming the decode+weight data is jointly load-bearing with no purely fiber-side route.

**Final standing map**: everything in #302 is proven and wired except Claim 5.9 = the per-order weight  from the root equation, fed by: the sloped budget (landed), the per-coordinate fold surface (landed), Lemma A.1 + the T-form monic-quadratic shape (in-tree, fleet), with the named consuming seam (//) ready. The P2-lane budget hypothesis () with the interpolant-divisor D_X bound is the precise next lemma.

=== comment 75 (lalalune) ===
**(Repost of the previous comment — shell mangled the backticks; content corrected here.)**

**ROUTE-MAP CORRECTION after attacking the assembly step directly**: half (ii) of Claim 5.10 is not an "assembly of per-coordinate identities" — re-reading §5.2.5–5.2.7 against the in-tree state, the paper's order is: **Step 6 (Claim 5.9) = the branch is Z-linear with polynomial coefficients via the Λ-weight bound, FIRST**; Step 7 (Claims 5.10/5.11, now fully formalized) then counts agreement against that already-polynomial branch. So the open core is not an assembly lemma — it IS Claim 5.9 itself (Λ(α_t) ≤ 1 per order ⟹ branch = a + Z·b with bounded deg_X), i.e. exactly the DivWeightLe/P2 kernel already mapped.

Two elementary bypass attempts, both refuted with explicit obstructions (recorded so nobody retries): (1) fold-interpolating candidates over k' > k coordinates — the composed defect X-degree grows as deg_X R + d·(k'−1), always outrunning the k' vanishing points for d ≥ 2 (the weighted degree only equalizes when the candidate has deg_X < k, but then it can match the fold at only k coordinates); (2) discriminant-vanishing from many Z-linear-rooted fibers — Y² − X(Z+1)² has Z-linear fiber roots at every square t with no global branch; the decode data excludes it (its specializations have no polynomial roots), confirming the decode+weight data is jointly load-bearing with no purely fiber-side route.

**Final standing map**: everything in #302 is proven and wired except Claim 5.9 = the per-order weight Λ(α_t) ≤ 1 from the root equation, fed by: the sloped budget (landed), the per-coordinate fold surface (landed), Lemma A.1 + the T-form monic-quadratic shape (in-tree, fleet), with the named consuming seam (CoordinateUpgrade / pinning_of_global_branch / global_branch_of_coordinate_upgrade) ready. The P2-lane budget hypothesis (alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget) with the interpolant-divisor D_X bound is the precise next lemma.


=== comment 76 (lalalune) ===
## HYPOTHESIS PORTFOLIO — the one open math node (CoordinateUpgrade ≡ BCIKS20 Claim A.2 weight recursion), from a fresh literature pass

**Source read**: BCIKS20 (2020/654) §5.2.7 + App A in full; Hab25 (2025/2110); in-tree state (sloped interpolant 5fb1a51bf, Step-7 elementary half 07b38ab95, Claim-5.10 first half 5ec91e5b0, refutations c2bec0136/weight_refuted, B_coeff_weight_le PROVEN, GammaCoeffRecursion, ResultantDegreeBound, Lemma A.1 in-tree).

**The exact gap**: Claim A.2: `α_t = β_t/(W^{t+1} ξ^{e_t})` with `Λ(β_t) ≤ 1 + (t+1)Λ(W) + e_t Λ(ξ)`, proven by partition-expansion induction — REQUIRING "D bounds the total degree of R" + "W | lc(R_{x0})". The in-tree refutations are precisely of carving WITHOUT the deg-R budget; the sloped interpolant now SUPPLIES it.

### Reasonable hypotheses (known math, careful carving)

**R1 (the direct re-carve).** Constraints: the in-tree βHensel recursion + B_coeff_weight_le (proven) are the paper's A_{i1,λ} calculus; the refutations only kill budget-free carvings. Why not done: nobody re-ran the induction WITH the sloped deg-budget hypotheses (they only landed hours ago). Novelty: none needed — pure assembly. **Hypothesis: `Λ(β_t) ≤ 1+(t+1)Λ(W)+e_t·Λ(ξ)` is provable by the in-tree induction once `R`'s (1,k)-weighted + Z-sloped budgets are hypotheses; the sloped interpolant discharges them.**

**R2 (weight = resultant degree; DRY/unification).** Constraints: Lemma A.1's own proof IS `deg_Z res_T(β,H̃) ≤ d·Λ(β)` (Sylvester). Why not done: the weight calculus was treated as bespoke; in-tree `natDegree_resultant_le` landed only this campaign. Novelty: replaces the Λ-recursion by resultant-degree monotonicity. **Hypothesis: Claim 5.10 follows from `natDegree_resultant_le` applied to res_T(β̃(x), H̃) with the canonical-rep Z-degree bounds, bypassing the α_t-recursion entirely — the per-x statement needs only deg_Z bounds on the canonical rep of γ(x)−w(x,Z), obtainable from the SLOPED Q via the factor-degree machinery (GSFactorDegreeOverRatFunc).**

**R3 (decode-lane pin).** Constraints: per-z proximate roots + double pigeonhole (landed) pin γ's fibers to decoded pairs at every good place. Why not done: the lanes converged only today. **Hypothesis: at each rich coordinate x, BOTH γ(x) and w(x,Z) are determined by >threshold common fiber values, so their difference vanishes at >dH·Λ places with Λ bounded by the CANONICAL-REP degree (no recursion): Lemma A.1 closes per-coordinate from the landed fiber machinery alone.**

**R4 (char-0 transfer).** Constraints: S5 chain is proven in all characteristics via separable-core descent; the weight recursion has no char dependence. Why not done: assumed char-p needed care. **Hypothesis: the A.2 induction, once carved per R1, is characteristic-free verbatim (the contract/expand descent handles the inseparable case as in GSSeparableCoreDescent).**

**R5 (Hab25 §3 shortcut).** Constraints: Hab25 replaces App A by its S7-S9; the repo proved S5/S6/S10/S11. Why not done: the repo's Hab25 lane stopped at the same capture kernel. **Hypothesis: Hab25's S8 ("the factor's coefficients are polynomials of bounded degree") is derivable from the landed S6 Hensel frame + the sloped budget WITHOUT the BCIKS20 weight language — check Hab25's actual S8 proof for a budget-only argument.**

### Advanced hypotheses (new math / new carving)

**A1 (Λ is a monomial valuation; Newton polygon).** Reasoning: Λ(Z^aT^i)=a+i(D+1−d) defines a weighted-degree valuation on 𝒪; Claim A.2 = "the Hensel branch's Newton polygon lies under a line of slope 2Λ(ξ)" — Abhyankar/Puiseux slope bounds. Nobody did it: BCIKS20 chose ad-hoc weights; valuation-theoretic recast unexamined. Anti-larp: Mathlib has Valuation + Polynomial.Newton? (no Newton polygon for this shape — would be new machinery). **Hypothesis: define ν := the Λ-valuation; the Hensel recursion is ν-contractive after ξ²-normalization: ν(α_{t+1}·ξ^{2t+1}W^{t+2}) ≤ ν-budget by ONE ultrametric inequality, replacing the partition combinatorics.**

**A2 (generating-function/majorization).** The A_{i1,λ} sums are the coefficients of R(X, Σα_t(X−x0)^t, Z); weight bounds = majorization of this composition by a rational generating function. **Hypothesis: Λ∘γ is majorized by the solution of the quadratic w = a + b·w² (Catalan-type), giving Λ(β_t) ≤ Catalan-weighted budget ≤ paper's bound — provable via PowerSeriesComposition (in-tree) + a new majorization lemma.**

**A3 (resultant telescoping).** res_T(β̃_{t+1},H̃) factors through res_T(β̃_t,H̃)·disc-powers — a telescoping product identity making the WHOLE Claim 5.10 a single resultant-degree telescope. New: resultant-of-Hensel-iterates identities don't exist in the literature for this shape (Anti-larp check: resultants of iterates appear in arithmetic dynamics — Silverman — but not for Hensel branches over function fields).

**A4 (one-shot interpolation, no per-coordinate).** Claim 5.9 needs k+1 good coordinates; instead interpolate γ−w against ALL of D simultaneously: the bivariate B(X,Z) := canonical rep of γ−w over 𝒪[X] has deg_X ≤ k, deg-bounded Z; vanishing on the good (x,z) GRID (|grid| > (deg_X+1)(deg_Z+1) via the landed counting) kills it by the in-tree grid Schwartz–Zippel — ELIMINATING Claims 5.10/5.11 separately. Anti-larp: the grid is NOT a product set (S'_x varies with x) — needs the in-tree non-product grid SZ (CS25 machinery has fiber-slicing forms).

**A5 (the symmetric-function/elementary route).** γ's coefficients are elementary symmetric functions of the captured decode values (Vieta on the section factor); symmetric functions of Z-linear values with bounded multiplicities are Z-degree-bounded by Newton's identities — giving Claim 5.9 directly from the landed capture + Vieta, no Hensel at all. Anti-larp: requires the section factor to SPLIT over 𝕃 with all roots captured (only ≥1 captured is known) — provable only on the squarefree fiber where the landed FactorPigeonhole gives full splitting? CHECK.

### Unification/DRY observations
- U1: Lemma A.1 + ResultantDegreeBound = same lemma twice (merge).
- U2: weight_Λ (RationalFunctionsCore:677) IS Finset.sup of a monomial valuation — refactor to Valuation API unifies with the FunctionFieldZLinear lane.
- U3: The A_{i1,λ} partition calculus appears in THREE places (HenselNumerator βHensel, GammaCoeffRecursion, MultinomialChainRule) — one Faà-di-Bruno engine should serve all.
- U4: e_t = max(0,2t−1) is the in-tree GSAffinePair/curve-tuple exponent law — same telescoping as the K4 seam.


=== comment 77 (lalalune) ===
## Criticality collapse: Node C (d_H ≥ 3 converter) is MOOT for the lane — the critical path narrows to A@d_H=1 + B + finite data

Scoping Node C against the deepest composed capstone (`gammaGenuine_eq_trunc_of_decoded_integerRep`, GSSurfaceSupply.lean §5) shows the satisfiability boundary does the work for us:

- **F7** (`BranchSeparationUnsat.branchCert_eq_zero`): the certificate inputs `hbr`/`hxi` are satisfiable **only at `H.natDegree = 1`** — the composed capstones never fire at higher-degree centre curves.
- **`hrepT`** (the corrected T-aware representative) is documented producible at monic `d_H ≤ 2` from the truncation itself — covers d_H = 1 a fortiori.
- At `d_H = 1`, `claim59_zLinear` is in the trivially-closed regime (T is on the ground line), so the **entire Claim-5.9/converter tower needs nothing new**.

**Therefore the full critical path to `UnifiedProducer` is now**:
1. **Node A @ d_H = 1**: `IntegerRepCentreSupply x₀ Q₀` with H = the *decoded linear factor* (the lane already produces the surface divisibility internally via `decodedSurface` + `hdvd`); the only genuine content is **slice separability at a good centre** — i.e. the discriminant of the integer-rep slice is not identically zero in the centre variable (`integer_rep_discr_ne_zero`-class facts + a bad-centre count < |F|).
2. **Node B**: `SurfaceSeparabilitySupply Q₀` (trivariate; squarefree-part + idempotent/coprimality route, or the audited weaker-capstone variant).
3. Finite per-instance data: `hξ ≠ 0`, the two certificate nonvanishings at the decoded witness, `hbig` field-size inequality (numeric-legs class).

Node C is demoted to general-theory interest (off the #301/#302 critical path). Node D (`DivWeightLe` degree-bounded pack) remains relevant only to the BCIKS20-literal lane — bypassed entirely if 1–3 land. Attack agents are on 1–3 now.

=== comment 78 (lalalune) ===
## Nodes A+B: MAJOR LANDING (verified) — A proven outright in the F7 regime; B relocated to field-level per-place data

Adversarially verified (commits on main, 0 token sorries, registered, spot `#print axioms` all `[propext, Classical.choice, Quot.sound]`):

### `4ae9bd15f` — `GSSurfaceRadicalSupply.lean` (21 decls)
- **Node A PROVEN OUTRIGHT in the only non-vacuous regime**: `integerRepCentreSupply_of_linear_slice` / `_of_monic_linear_slice` (F7 forces `d_H = 1`, and there the supply holds with H = the linear slice factor).
- General-degree reductions: `integerRepCentreSupply_of_separable_slice` (Node A ⟸ separable slice, exact), conditional resultant form, UFD irreducible-factor brick.
- **Explicit Schwartz–Zippel bad-centre count**: `exists_good_centre_slice_discr_ne_zero` (bad centres ≤ `deg_X(lc) + deg_X(discr)`, reusing `c56_evalC_bad_set_card_le`) + `slice_separable_map_of_discr_ne_zero` + char-0 capstone `radical_rep_good_centre_charZero` (good centres exist unconditionally for the radical integer rep) + the radical-replacement surface bridge.
- Node B producible cases extended: linear, unit-rescales, **products of surfaces with pairwise unit differences** (`natDegree_pair_surfaces = 2` — exactly the `hd2` regime).

### `9f2194c38` — `GSSurfaceMappedSeparability.lean` (10 decls) — the consolidation route
- Audit: `hR : R.Separable` enters the decoded-capstone chain through **exactly one lemma**.
- The full chain RE-PROVED under the strictly weaker `MappedSliceSeparability` (per-place): `…→ gammaGenuine_eq_trunc_of_surface_mapped`.
- New brick `separable_of_powerSeries_residue`: over `PowerSeries F`, **residue (field-level) separability + degree preservation ⟹ separability** — so Node B's open content is now per-place residue separability over the field `F` (finite, discriminant-checkable), no longer a trivariate Bézout identity (which is FALSE outside unit-resultant regimes — the honest reason the original Prop was stuck).

### Combined with `251d3c162` (certificate legs = units from slice separability) + `33f13ef6e` (numeric legs + STIR capstone welds):
**Remaining on the critical path**: (1) the named residue computation — `(R.map coeffHom_loc).map (PowerSeries.map π̂_z) mod X` = the slice at the place `(z, root)` — welding `MappedSliceSeparability.of_residue` to the good-centre counting; (2) the final `UnifiedProducer` instantiation glue; (3) `hε` at `secpar > 0` via the CA bridge. Attack continuing.

=== comment 79 (lalalune) ===
**A4 (one-shot grid kill) — falsification analysis verdict: A4 COLLAPSES to the per-coordinate route; not a new attack. Recorded so nobody re-derives it.**

The anti-larp check in the portfolio resolves negatively, by comparing the landed counts:
1. A row-by-row two-variable kill needs, for each contributing coordinate x, the per-row mass `|S'_x| > d_H·Λ-budget` — the row's Z-slice can only be killed by Lemma A.1 (or the resultant equivalent) AT that row, since the good set G = {(x,z) : z ∈ S'_x} is not a product and the z-fibers vary with x. There is no purely 2-D Schwartz–Zippel for non-product grids that beats the row decomposition here (the CS25 fiber-slicing forms also reduce to per-row counts).
2. The number of rows needed is k+1 (to interpolate the degree-≤k X-polynomial) — and rows satisfying the mass condition are exactly Claim 5.11's rich coordinates (`exists_rich_coordinates`, PROVEN).
3. Hence A4's premises = Claim 5.11's count + the per-row kill = exactly Claims 5.11 + 5.10 — the standing decomposition. A4 is the same proof reorganized; its only residual value is stylistic (folding 5.9's interpolation into the same induction), which the landed `curve_pin_of_node_agreement` already does.

**Conclusion**: the per-coordinate kill (Claim 5.10's second half = the weight/resultant budget on `γ(x) − w(x,Z)`) remains the unique critical obligation, exactly as the R1/R2/R3 attacks target it — now with Node A proven in the F7 regime and Node B reduced to per-place residue separability (4ae9bd15f, 9f2194c38).

=== comment 80 (lalalune) ===
## Critical-path item (1) LANDED: the named residue computation + the weld — `MappedSliceSeparability` is now PRODUCED from `hHyp`, not hypothesized

**Commit `9ad71451d` — `ArkLib/ToMathlib/GSResidueSliceWeld.lean` (13 decls, all `[propext, Classical.choice, Quot.sound]`, 0 sorries, registered, in-tree `lake build` green).**

### §1 The computation
`residue_mapped_eq_slice`: at every place `(z, root)` with `π_z(ξ) ≠ 0`,

`((R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map π̂_z)) mod X = (Bivariate.evalX (C x₀) R).map (evalRingHom z)`

— the residue of the doubly-mapped matching polynomial **is the `(x₀, z)`-slice of the surface**, and is **independent of the chosen `root`** over `z`. Coefficientwise (`constantCoeff_mapped_eq_slice_eval`): `constantCoeff ∘ π̂_z ∘ coeffHom_loc = eval z ∘ eval (C x₀)` — Taylor recentering reads its constant term at the centre (`taylor_coeff_zero`), `locLift` lands in `Y`-constants of `𝒪 H`, and `π_z` on `Y`-constants is evaluation at `z` (`π_z_mk` + `evalEval_C`).

### §2 The structural collapse the computation exposes
**Node B's relocated open content (per-place residue separability over `F`) was contained in `hHyp` all along**: `Hypotheses.separable_evalX` is `(evalX (C x₀) R).Separable` over `F[Z]` — a Bézout identity, which maps along `evalRingHom z` to give the residue slice separable over the field `F` at EVERY place. No discriminant counting is needed for separability itself. What remains is exactly the **degree-preservation legs** of `separable_of_powerSeries_residue`, and those are counted avoidance data:
- centre leg `hcdeg : (evalX (C x₀) R).natDegree = R.natDegree` — the good-centre counting output (`slice_natDegree_eq_of_leadingCoeff_eval_ne` / `exists_good_centre_slice_discr_ne_zero` supply shape, `c56_evalC_bad_set_card_le`-counted);
- per-`z` leg: `z` avoids the roots of `(evalX (C x₀) R).leadingCoeff = G.leadingCoeff ∈ F[Z]` (monic `H`).

A degree squeeze (map never raises degree; the residue attains `R.natDegree`) pins every intermediate degree, and Lemma 2′ fires: `mapped_separable_of_slice_natDegree`.

### §3 The welds (consumer side)
- `mappedSliceSeparability_of_slice_leadingCoeff` — the FULL `MappedSliceSeparability hHyp` produced when the slice leading coefficient is `F`-rootless (monic/constant-lc slice regime): feeds the existing `gammaGenuine_eq_trunc_of_surface_mapped` **unchanged**.
- `MappedSliceSeparabilityOn` + `mappedSliceSeparabilityOn_of_slice_leadingCoeff` — the set-restricted form (the chain only ever reads places in the matching set); decoded chain re-proved on it (`matchingPoint_of_decoded_at`, `hvanish_of_decoded_roots_residue`, `gammaGenuine_eq_trunc_of_decoded_roots_residue`).
- `gammaGenuine_eq_trunc_global_residue` / `gammaGenuine_eq_trunc_of_surface_residue` / `…_residue'` — **the welded capstones: NO separability hypothesis beyond `hHyp` itself.** Matching set = nonvanishing locus of `branchCert · xiCert · G.leadingCoeff` (the avoidance polynomial gains the lc factor — degree-bounded by the sloped budgets); budget gains `G.leadingCoeff.natDegree`; `hcdeg` either explicit or derived from the counted `R.leadingCoeff.eval (C x₀) ≠ 0` (the prime variant).

### Ledger effect
The 'per-place residue separability over `F`' node from the Nodes-A+B landing comment is **closed** — relocated content discharged by the residue computation. The deepest capstone's inputs beyond `hHyp` are now purely: decode data (`hdvd`, `hdeg`), the two certificate nonvanishings, the numeric legs (`hbig`, now with the lc summand), and the counted centre leg. The remaining open math on the lane is unchanged: `hrepT` production at `d_H ≤ 2` and (BCIKS20-literal lane only) Claim 5.9 — neither touched by this seam.

=== comment 81 (lekt9) ===
Two of the three cheap discharges from the gate audit are landed on main (`6127bfd00`), axiom-clean: **`mcaDeltaStar_interleaved_eq`** (`InterleavingStabilityLedger.lean`) — δ\*(C^≡t, ε\*) = δ\*(C, ε\*), every threshold-ledger bracket transfers verbatim to interleaved codes with no width factor; and **`mca_rsc_pair_unconditional`** (`MCAPairUDRUnconditional.lean`) — the pair generator's below-UDR MCA at canonical exponents (0,1), side condition discharged, ready for the folding recursion. Remaining from the audit: the ε_sc completeness-round discharge (~150 lines, wiring), and the genuine open core `JohnsonNumericBound` (Haböck 2025/2110 formalization — the real program).

=== comment 82 (lalalune) ===
## THE GLUE LANDED: first unconditional `UnifiedProducer` instantiation — the UD-window leg (`UnifiedProducerWindowGlue.lean`, 10/10 axiom-clean, `baaab433a`+`42634796a`)

Deliverables (a)+(b) of the producer programme, on main:

**(a) `unifiedProducer_of_window`** — on the curve unique-decoding window
`curveUDWindow k deg n δ := (k+1)·n + deg ≤ (k+2)·(n − ⌊δ·n⌋)`
the single production target of `UnifiedExtractionTarget` (both #304 cores + the closed-boundary keystone) holds **outright**: `k+1` good scalars pin every count-triggered decoded family to the Lagrange curve through any `k+1` of its members, and root counting on the `(k+2)`-fold agreement intersection forces every further good scalar onto the same curve. This is the generic-domain, joint-agreement-clause-free arity-`(k+1)` mirror of `exists_curve_tuple_of_decode_family_window` (`Hab25CurveCaptureUD`), consumed from plain per-scalar proximity data (`exists_curve_tuple_of_window` + `floor_agreement_card_of_relHammingDist_le`). NO list-decoding, GS, Hensel, or weight-budget input. Non-vacuous on the whole window (the count trigger and proximity data are jointly satisfiable throughout; the produced `CurveFamilyData` is the real curve).

**(b) `correlatedAgreementCurves_johnsonClosed_of_window`** — threading through `johnsonClosed_of_producer`: the closed-boundary keystone `δ_ε_correlatedAgreementCurves` at `δ = 1−√ρ` with the explicit positive error `max(errorBound(cell), (n+1)/|F|)`, from ONE window hypothesis (the cell-radius window is the same window — `curveUDWindow_floor_congr`, since the window only sees `⌊δ·n⌋`). Plus `strictCoeffPolysResidual(Large)_of_window` and `correlatedAgreement_affine_curves_of_window` (strict radius, error `errorBound δ deg domain`).

**HONEST regime statement** (in-file docstrings carry the same): the window at width `k` forces `δ ≲ (1−ρ)/(k+2)` — genuine UD strength. At the Johnson boundary `δ = 1−√ρ` (for `k ≥ 1`) it intersects the window only where floor slack absorbs `(1−√ρ)(k+1−√ρ)·n`, i.e. the high-rate/zero-error corner (`⌊δ·n⌋ = 0`, `deg ≳ n−(k+2)`). Deep inside the window the strict residual is consumed only through its (then-false) Johnson-side hypothesis `(1−ρ)/2 < δ`. **The non-vacuous content is the producer itself + the boundary keystone in the corner; the Johnson-regime producer remains the open F7/d_H=1 matching-lane leg** (`MatchingLaneData` suppliers — `hsepR`/`hw` still the open cores, unchanged by this brick).

**Zero-error corner is width-uniform**: `curveUDWindow_all_of_floor_eq_zero` — at `⌊δ·n⌋ = 0`, `deg ≤ n`, the window holds at EVERY width, so the full `∀ k` strict-residual family (the exact shape #301's checking bridge consumes) is produced genuinely — see the companion #301 comment (`Stir/WindowCAFeed.lean`).

Process note: my chore commit briefly swept in a staged in-flight file `CoordinateKillBudget.lean` from a parallel lane; redone — the file is back untracked on disk for its owner, not referenced by `ArkLib.lean`.

=== comment 83 (lekt9) ===
## `JohnsonNumericBound` discharge: the definitive roadmap (recon complete — including a structural finding that affects the bundle design)

Full recon on the remaining core of this issue: in-repo surface map + a complete digest of Haböck ePrint 2025/2110 (the 7-page note proves Theorem 2 by *citation into* [BCIKS20] §5; several steps are one-sentence imports). Summary of what discharging `JohnsonNumericBound` actually requires:

### ⚠ Structural finding: the residual bundle is stronger than the paper

`Hab25JohnsonAlgebraicData` demands per-factor affine pairs `(d₀, d₁)` + `hImprove` for **every** `ij ∈ Index` covering all of `Edis`. But [Hab25] Claim 1 is a **dichotomy by contradiction**: the useful-factor machinery (`Rᵢ(X,Y^{p^f},Z) = (Y−(a+Zb))^{p^f}`, unique affine pair) only fires for factors with `|E_{i,j}| > 2·D_Y²·D_X·D_{YZ}`; below the threshold *no pair is produced at all* and the factor is counted by the threshold itself. So a faithful transcription needs either (a) a bundle redesign with a per-factor dichotomy field (`pair ∨ count ≤ threshold`), or (b) importing the stronger every-factor structure from [GG25]/[BCHKS25]. **Building the GS bricks against the current bundle shape would hit this wall after weeks.** Also: `mca_johnson_of_residuals` currently proves the bound as literally `R.hNumeric` — the algebraic data and the numeric edge are independent fields; there is no in-tree derivation of one from the other (and none is possible without the pair-quantified construction: the data carries no word-pair parameter while `epsMCA` sups over pairs).

### The honest lemma chain (paper → Lean difficulty)

| step | content | status |
|---|---|---|
| L1 | collinearity double-count (each disagreement point kills ≤1 scalar) | **proven in-tree** (S7–S10, `claim1_theorem2_integer`) |
| L2 | GS interpolation over `K = F(Z)`: trivariate `Q`, budgets `D_Y < ℓ`, `D_X < ℓρn`, `D_YZ ≤ ℓ³ρn/6`, char-p separable decomposition `Y^{p^f}` | hard-medium; by citation in the note; ~3–4 wk |
| L2b | proximate ⟹ `Q(X, p(X), z) = 0` (multiplicity-weighted root count vs degree) | medium; **never stated in the paper** |
| L3 | `deg_X disc_Y(Q) < ℓ²ρn`; choice of `x₀` with all specialized discriminants ≠ 0 | medium; Mathlib resultant API is young |
| L4 | cover `E = ⋃ E_{i,j}` via specialized factorization `Rᵢ(x₀,Y,Z) = ∏ H_{i,j}` | medium, near-definitional after L2b/L3 |
| L5 | **the frontier**: useful factor ⟹ Hensel lift in `F[[X−x₀]]` of the `Y`-root, linear in `Z`, degree < k, inseparable case via `p^f`-peel ([BCIKS20] Steps 5–7 + App. C — one sentence in the note) | very hard; ~weeks of original work; Mathlib has `HenselianLocalRing` + power series but nothing close to the combined argument |
| L6 | union bound + closing arithmetic `(ℓ⁶/3)(ρn)² > n` | easy; integer endgame already in-tree |

Total honest estimate: **9–13 weeks** of sustained formalization, with L5 the research-grade core. No refutations block any step (DISPROOF_LOG checked). The right order: fix the bundle shape first (the dichotomy field), then L2b/L3/L4 (medium bricks, independently useful), then L2, then L5.

### What stays true meanwhile

The gate architecture is correct and honest: `JohnsonNumericBound` is a named hypothesis, never a sorry; the wiring theorem discharges the headline conjecture the moment it lands; and the below-UDR regime (`mca_rsc_pair_unconditional`), the interleaving stability (`epsMCA_interleaved_eq`, `mcaDeltaStar_interleaved_eq`), and the integer endgame are all already unconditional.


=== comment 84 (lekt9) ===
Roadmap brick 1 landed (`36b4ec78f`): **`Hab25JohnsonDichotomy.lean`** — the dichotomy-shaped residual bundle faithful to what [Hab25] Claim 1 actually constructs (per factor: `card ≤ T` ∨ affine pair with improvement), with the counting theorem `disagree_card_le : |E| ≤ ℓ·max(T,n)` proven from the in-tree endgame, the paper-regime corollary (`T ≥ n ⟹ ℓ·T`, the (ℓ⁷/3)(ρn)² form), and the `T = 0` embedding showing the every-factor bundle is a special case. All axiom-clean. The GS construction program (L2–L5) now has the correct target shape — the below-threshold wall is gone.

=== comment 85 (lekt9) ===
## Corrected Johnson roadmap: the program is much shorter than the first audit said — one deep gap remains

A full re-audit of the ROUTE F1 / trivariate GS surface (triggered by finding `dvd_sliceToPoly_of_agreement` already in-tree) shows the S2–S8 chain is **essentially complete** — 36/36 main theorems sorry-free across `GuruswamiSudan/`: trivariate interpolation existence (`exists_ne_zero_vanishesToOrder3`), Z-slice divisibility (L2b), list-size capstone (`curve_listSize_le`), GS over `K = F(Z)` (`gs_existence_over_ratfunc`), Z-degree bounds, per-z factor assignment with the charZero separability supply (`Hab25S4Wire` + `Hab25SeparableSupply`), affine-pair extraction by Lagrange descent (`GSAffinePair`), and uniqueness/affine pinning (`Hab25FactorWeld`).

**Corrected minimal gap list for constructing a `Hab25JohnsonDichotomyData` instance:**
1. *(mechanical)* factor-count wiring: list-size bound → irreducible-factor enumeration (`Index.card ≤ ℓ`);
2. *(mechanical)* per-factor exceptional-set extraction from the S4 bad polynomial;
3. **(the one deep gap)** `hlin` — *no per-z decoded root lives in a Y-degree ≥ 2 factor* (BCIKS20 Claim 5.8/5.9, Hensel-rigidity content; flagged "deep in characteristic p" in `GSSeparableSupply`). This is now the **entire** remaining research core of the below-Johnson program;
4. *(trivial)* dichotomy-bundle assembly.

Plan: land 1, 2, 4 as a **conditional discharge** `johnsonNumericBound_of_hlin` with `hlin` as a named hypothesis (never an axiom — repo policy), which moves the whole #302 headline to a single named gate; then attack `hlin` itself. The earlier 9–13-week estimate was built before discovering how much of the GS chain the swarm had already landed — credit where due: ROUTE F1 was nearly finished and nobody had connected it to the Hab25 bundle.


=== comment 86 (lalalune) ===
## `hlin` attack ledger: 5 known-math + 5 advanced hypotheses (full literature recon done — BCIKS20 read end-to-end, Hab25, BCHKS25 2025/2055, GG25 2025/2054)

Division of labor: the conditional-discharge wiring (`johnsonNumericBound_of_hlin`, items 1/2/4 of the corrected roadmap) is the parallel lane's; **this lane takes the deep gate itself** — `hlin` = BCIKS20 Steps 5–7 + App A/C per factor. Kernel decomposition from the recon, against the tree:

| BCIKS20 kernel item | in-tree status |
|---|---|
| **Lemma A.1** (vanishing kernel over `O = F[Z][T]/(H̃)`: regular `β` with `> d_H·Λ(β)` vanishing places is 0) | **ABSENT** — the sole missing *keystone* |
| **Claim A.2** (weight recursion `Λ(β_t) < (2t+1)dD`) | budget-free carve **REFUTED** (`P1MonicWeightRefutation`); ξ-unit dissolution landed; budgeted form OPEN |
| Hensel uniqueness + pinning (5.8 rigidity half) | PROVEN (`HenselBranchRigidity`, `Hab25BranchPinning.pinning_of_global_branch`) |
| 5.10/5.11 double counting | PROVEN (`hab25_lemma1_counting`, `hab25_endgame_count`) |
| F-Lagrange Z-linearity transfer | PROVEN (`map_eval_eq_curve_sum`) |
| char-p peel (App C) | vacuous iff `p > D_Y` (since `D_Y < ℓ`); twist machinery partial (`GSSeparableContraction`) |

Literature verdict (honest): **no known proof of mutual CA at Johnson radius for plain RS avoids this kernel.** GG25 is Hensel-free but only for subspace-design/random codes; GKL24/Khatam stop at 1.5-Johnson; list-decoding⟹MCA (2025/870) loses a square root. BCHKS25 is the cleanest modern presentation (O(1) D_Z interpolant, per-factor budgets, the footnote-5 content-term fix — which any faithful cover statement must absorb).

### Known-math hypotheses

**K1 — NormVanishingKernel (Lemma A.1 via `Algebra.norm` as determinant, no Sylvester).**
*Constraints:* Mathlib's resultant API lacks the needed direction (common specialized root ⟹ resultant vanishes). *New direction:* `H̃` monic irreducible ⟹ `O` is a free `F[Z]`-module of rank `d_H` and a domain (Gauss); take `N(β) = det(mul-by-β)`. At a place `(t_z, z)`: `(T−t_z) ∣ gcd(β̄, H̃(·,z))` ⟹ `β̄` is a zero divisor in `F[T]/(H̃(·,z))` ⟹ `N(β)(z) = det(base-changed map) = 0`. And `deg_Z N(β) ≤ d_H·Λ(β)` by the permutation-invariant weighted-degree count — **the exact symmetry that closed unit (2)** (`Matrix.exists_natDegree_le_kernel_vector_of_ratFunc`, PolynomialMatrixKernel.lean): entry `(i,j)` of the matrix has `deg_Z ≤ Λ(β) + (j−i)·Λ(T)` and the `Λ(T)` terms telescope over any permutation. Too many roots ⟹ `N(β) = 0` ⟹ β a zero divisor in a domain ⟹ `β = 0`. *Larp check:* `N = ±res` for monic `H̃` is classical — the math isn't new, the **formalization route** (determinant base-change instead of resultant theory) is. *Hypothesis:* A.1 lands in days, axiom-clean.

**K2 — BudgetedWeightInduction (Claim A.2 with the GS degree budgets threaded).**
*Constraints:* the in-tree refutation (`H=Y²−2` over `ZMod 3`, quotient weight 2>1) refutes only the **budget-free** carve — diagnostic: the missing hypothesis is exactly the paper's `D` (deg_{(Y,Z)} budget of `R`), present in `Λ(β_t) < (2t+1)dD`, lost in the carve. Term-by-term Faà-di-Bruno matching provably fails — but **weight UPPER bounds never needed it**: sub-additivity per term + `Λ(sum) ≤ max` + one strong induction over the in-tree `βHensel` recursion (HenselNumerator.lean:1182). *Why it looked like a wall:* the refutation was read as killing the lemma when it only identifies the missing budget hypothesis. *Hypothesis:* `Λ_𝒪(βHensel t) ≤ 1 + (t+1)Λ(W) + (2t−1)Λ(ξ)`-shaped bound, given GS budgets on `R`, by one global induction — no bijection.

**K3 — Claim 5.8 (X-degree kill).** K1 + K2 + proven Hensel uniqueness: `|S′| > d_H·Λ(β_t)` for all `t < D_X` kills `α_t` for `k < t < D_X`; the `t ≥ D_X` tail by the weighted-degree truncation argument (`R(X,γ_k,Z)` has degree `< D_X` but vanishes to order `D_X` ⟹ ≡ 0; uniqueness pins `γ = γ_k`). All inputs then in-tree.

**K4 — Claim 5.9 via heavy points (resolves the d≥3 wall).** The in-tree span-local route is provably unavailable for `d ≥ 3` (`functionFieldT_sq_no_T_repr`) — go **geometric exactly as the paper does**: K1 applied per-`x` to `β̃(x) = β(x) − (u₀(x)+Z·u₁(x))·W^{k+1}ξ^{e_k}` (budget `(2k+1)d_H dD`, from K2 at `t ≤ k` only), the k+1-heavy-point double count (5.11), then the PROVEN F-Lagrange transfer. *Larp flag (honest):* `hab25_lemma1_counting` is the affineGap incidence count — the 5.11 heaviness count `|S′_x| ≥ ((1−ρ−δ)/(1−ρ))|S′|` may need a fresh ~80-line double count; budgeted in.

**K5 — Char-cased assembly.** K3 + K4 + irreducibility ⟹ `R = unit·(Y − (v₀+Z·v₁))` outright for `char F = 0` or `char F > D_Y` (legitimate split: `D_Y < ℓ`, so `p ≥ ℓ` suffices — covers all large-prime WHIR deployments). App C (binary/small-char) stays a named residual fed by A4 below. Feeds `Hab25JohnsonDichotomyData.hdichotomy` through the parallel lane's wiring.

### Advanced hypotheses (unknown-math lanes)

**A1 — Pole-divisor filtration (valuation-theoretic A.2).** Reformulate Claim A.2: all `α_t` lie in the subring of `L` with poles confined to the fixed finite set `S_∞ = poles(α₀) ∪ supp(div_∞ ξ⁻¹W⁻¹)`, pole degree growing linearly in `t`; the Hensel recursion preserves the filtration because `ζ⁻¹`-multiplication shifts it by a constant divisor. *Why nobody:* paper and tree both do coefficient bookkeeping; nobody phrases A.2 as "the lift lives in a finitely-generated Rees-type filtration" — a single global statement, which is exactly the right shape given that term-by-term fails. *Risk:* Lean lacks function-field divisor machinery; expensive. Fallback insurance for K2, not the primary lane.

**A2 — One-kernel DRY.** K1's norm kernel subsumes four in-tree argument shapes: (i) Lemma A.1; (ii) `eq_zero_of_degreeX_lt_card_of_evalX_eq_zero` (BCKHS25/Interpolation) = the `d_H = 1` shadow (`O = F[Z]`, `N = id`); (iii) the per-x 5.10 budget; (iv) the unit-(2) Cramer bound is its kernel-vector dual. *Hypothesis:* one lemma file, four consumers — measurable consolidation, to be executed as part of K1's landing.

**A3 — Derivation rigidity (differential-algebra replacement for 5.10/5.11).** `γ` satisfies the identity `R_Y(γ)·∂_Z γ + R_Z(γ) = 0` where `∂_Z` extends to `O` via `∂_Z T := −H̃_Z/H̃_T`. *Conjecture:* X-degree budget + this ODE + ≥ 2 affine fibers force `∂²_Z γ = 0` directly via A.1 on the weight-bounded numerator of `∂²_Z γ`. *Why nobody:* per-z data is discrete so derivative arguments look unavailable — the novelty is that the **functional equation holds identically in Z**, no limits needed. *Honest risk:* plausibly FALSE (the ODE may not see the per-z affine data); cheap numeric probe (synthetic non-Z-linear root, small field) scheduled to refute before any Lean investment.

**A4 — Functorial Frobenius descent (App C as one descent file).** *Conjecture:* hlin for the separable contraction ⟹ hlin for `R(X,Y^{p^f},Z)` with `p^f`-th-root affine pair, purely formally from perfectness + `(Y−c)^{p^f} = Y^{p^f}−c^{p^f}` + in-tree `GSSeparableContraction` — no re-run of Steps 5–7 in the twisted field `L̂`. *Honest subtlety:* the affine pair must come out linear in `Z`, not `Z^{p^f}` — the paper's `Ẑ = Z^{1/p^f}` twist is doing real work there; the descent likely needs the F-Lagrange step re-run at `p^f`-spaced exponents. Refutable at the statement level before building.

**A5 — Linear-error unification (BCHKS25-strength from the same kernel).** The same K1–K4 kernel + the in-tree O(1)-`D_Z` interpolant (`BCKHS25/Interpolation.lean`) yields `|E| ≤ 2D_X D_Y² D_Z + (γn+1)D_Y = O(n)` — the sharpest known bound, superseding the quadratic Hab25 form in the WHIR wiring, with the footnote-5 content-term fix absorbed. Executed after K1–K4 land; same kernel, second consumer.

### Execution order
K1 (keystone, unblocks K3+K4) ∥ A3-probe (cheap refute) ∥ K2-recon → K2 → K3 → K4 → K5 → A4/A5. Workflow dispatch next message.


=== comment 87 (lalalune) ===
## Hypothesis portfolio for the NARROWED core: assignment coherence at rich coordinates (post-`Hab25CoordinateUpgradeWeld`)

**Where the lane stands** (re-verified in-tree today): `CoordinateUpgrade` (Claim 5.10's output) is PROVEN from witness-rich factor assignments (`coordinateUpgrade_of_assigned_factor_rich`), with the Λ-weight recursion fully bypassed (budget kills in `CoordinateKillBudget`: `eq_section_of_many_fiber_agreements`, `fiber_root_eq_section_of_irreducible_of_many_agreements`). The genuine residual is supplying the assignment data `(Hf, assign, S)`: per rich coordinate `t`, per cell scalar `γ`, an assigned irreducible fiber factor where `(P γ).eval(x_t)` roots, carrying `> B + deg_Y·(L−1)` *witnessed* fold agreements. Witnessed scalars: pigeonhole (`exists_witness_rich_factor`). **Unwitnessed scalars (≤ M per coordinate): the open core.** Below: 5 known-math and 5 advanced hypotheses, each with constraints/novelty/larp-check, before execution.

### Known-math hypotheses

**R-K1 (fully-witnessed partial discharge).** *Constraints*: needs every `γ ∈ E` witnessed at every `t ∈ T`. *Why not done*: the weld landed hours ago. *Larp-check*: implicit in the weld docstring; zero new math, pure wiring. *Novel*: makes the easy half consumable as one theorem. *Hypothesis*: `coordinateUpgrade_of_fully_witnessed` — if at each `t ∈ T` the agreement count among cell scalars exceeds `(#factors)·threshold` and every cell scalar's coordinate value agrees with the fold there, `CoordinateUpgrade` holds with no factor data in the signature (factors constructed internally from the specialized interpolant).

**R-K2 (unique rich factor).** *Constraints*: two distinct monic irreducible factors that are both rich are both killed to `c·(Y − w_t(Z))` — but they're coprime, contradiction. *Why not done*: the kill lemma is new; nobody has yet taken its uniqueness consequence. *Larp-check*: standard UFD reasoning; novel only as the load-bearing glue. *Hypothesis*: at any coordinate, at most ONE irreducible factor (up to associates) of any fixed specialized fiber product can carry `> B + deg_Y·(L−1)` agreements with `w_t`; hence "the rich factor" is well-defined and all heavy agreement mass concentrates in it.

**R-K3 (THE SLACK WELD — count, don't pin, the unwitnessed scalars).** *Constraints*: `global_branch_of_assigned_factor_rich` needs `|E| > B_R + deg_Y R·(L−1)`; each rich coordinate has ≤ M unwitnessed scalars; over k coordinates the witnessed-everywhere subcell `E'` has `|E'| ≥ |E| − k·M`. *New direction*: the paper (and every prior in-tree attempt) tries to pin the unwitnessed scalars' decode values too. But the global branch is a statement about `R`, not about `E` — it only needs SOME subcell above threshold. Run the weld on `E'` and demand `|E| > B_R + deg_Y R·(L−1) + k·M`. The unwitnessed scalars never need an assigned factor at all. *Why nobody has done it*: the weld's interface (per-scalar ∀ γ ∈ E) makes the subcell restriction invisible until you ask what downstream actually consumes; BCIKS20's prose works at the agreement subcell but the formal lane kept the full cell. *Larp-check*: BCIKS20 implicitly restrict to agreement sets, so the IDEA is the paper's; the formal content — that the in-tree budget chain closes with only a `k·M` count adjustment and no Claim-A.2/no single-branch-capture input — is unproven anywhere and would delete the named residual. *Hypothesis*: `global_branch_of_witnessed_subcell`: rich-coordinate data with per-coordinate unwitnessed defect ≤ M and `|E| > B_R + deg_Y R·(L−1) + k·M` produces `(Y − C pHat) ∣ R` outright.

**R-K4 (budget supply instantiation).** *Constraints*: the weld takes abstract `(Hf, B)`; the real factors are the irreducible factors of the specialized sloped interpolant, with `B` from `coeff_budget_of_dvd` + `GSInterpolantSloped`. *Larp-check*: announced as "supplied by divisor inheritance" in the weld docstring but no instantiation theorem exists. *Hypothesis*: a packaging theorem producing the weld's factor data from the interpolant alone (concrete `B`, `Index.card ≤ deg_Y`), so R-K3's signature mentions only decode data + counts.

**R-K5 (single named gate).** *Hypothesis*: composing R-K2/K3/K4 with the landed dichotomy bundle (`Hab25JohnsonDichotomy`) + candidate production discharges a conditional `johnsonNumericBound_of_richCoordinates` where the ONLY remaining hypothesis is the rich-coordinate existence count (Claim 5.11 shape, whose elementary half `exists_rich_coordinates` is already in-tree) — moving the whole #302 headline to one named numeric gate.

### Advanced hypotheses

**R-A1 (cross-coordinate branch globalization).** The unique rich factor at each rich coordinate is the `t`-fiber of ONE global object `Y − pHat` (`branchOfCurveTuple`). *Why advanced*: needs comparing factorizations over different fibers — the formal content of "single-branch capture" without per-scalar assignment. *Larp-check*: this IS the paper's Steps 5–7 mechanism; novel is doing it from the budget kills instead of Hensel branches. If R-K3 lands, this becomes optional structure theory; if R-K3 stalls, this is the fallback route.

**R-A2 (Galois-stability kill for inseparable factors).** Agreement sets are stable under the Galois action permuting a factor's fiber roots, so richness is a class function and the kill extends to char-p inseparable factors via orbit counting — connecting to the descended-Claim-5.7 char-p lane. *Why nobody*: char-0/separable suffices for the headline; this is the only route that would make the bound field-uniform. High risk, probe only.

**R-A3 (second-moment defect bound, #232 interpolation).** Replace the worst-case `k·M` slack in R-K3 by a second-moment count of (scalar, coordinate) disagreement incidences — the quadratic collision-count brick from the #232 Weil/Hasse lane applies verbatim to the disagreement matrix. *Novel*: imports prize-lane machinery into the WHIR bound; would sharpen the final ε from `O(ℓ²)` toward the paper's constant. Cross-issue DRY.

**R-A4 (two-altitude kill unification).** `CoordinateKillBudget` Part 1 (𝒪-level) and Part 2 (polynomial FactorKill) are one lemma over any integral `F`-algebra with a degree function; the Whir-side `K4ComponentResidual` (`MCAJohnsonBound.lean`) is a THIRD instance of the same shape. *Hypothesis*: one graded-kill lemma subsumes all three, and the Whir K4 residual becomes a corollary of the ProximityGap lane — unifying the two parallel #302 interfaces that currently don't reference each other. Pure consolidation win even if no new theorem strength.

**R-A5 (adversarial probe: is the slack weld secretly false?).** The in-file honesty note proves algebra-only production is FALSE (`Y² − Z`). *Hypothesis to TEST, expecting refutation of the strawman*: R-K3 with the witness data dropped (slack only, no `S`-sets) is FALSE — the `Y² − Z` counterexample should kill it. This pins exactly which hypothesis of R-K3 is load-bearing and fences future launderers from "simplifying" the witness data away.

**Execution order** (workflow launching now): R-K2 → R-K4 → R-K3 (critical) → R-K1 → R-K5 assembly, with R-A5 as the adversarial gate and R-A4 as the consolidation pass. Every claim lands as a verified theorem (`#print axioms` gate) or gets explicitly refuted here.


=== comment 88 (lalalune) ===
## Literature verification against BCIKS20 (eprint 2020/654 §5 + App. A): R-K3 larp-check CORRECTED, and the paper-faithful route is already 90% in-tree

Read the actual paper (local library copy, p.17–28 + App. A) to verify the portfolio's bets before the proofs land. Three findings, one of which corrects my own portfolio comment:

**1. The R-K3 larp-check was wrong — in a useful direction.** I claimed "BCIKS20 implicitly restrict to agreement sets, so the idea is the paper's". FALSE: the paper NEVER forms an agreement-intersection subcell and never takes an additive `|E| − k·M` hit. Its actual shape (Claim 5.10, p.26): the per-coordinate hypothesis counts only the agreeing scalars `S′_x`, but the conclusion is an identity **in the extension field `L`** — `γ(x) = w(x,Z)` — via Lemma A.1 zero-counting on `β̃(x)`; the disagreeing scalars get pinned *retroactively for free* (`π_z(γ(x)) = w(x,z)` for ALL `z ∈ S′`), and the branch linearity (Claim 5.9) is interpolation **in `L` at k+1 coordinates, scalar-free** — no per-scalar counting ever happens after 5.10. So R-K3 (the slack weld) is genuinely novel relative to the paper — but see (2).

**2. Quantitative warning for R-K3's regime (prediction for the R-A5 vacuity probe).** The per-coordinate defect at the top coordinates is *multiplicative*: Claim 5.11's double count gives `|S′_x| ≥ (1−ρ−δ)/(1−ρ)·|S′|`, i.e. defect `M ≈ δ/(1−ρ)·|E|`, NOT a small constant. A witnessed-everywhere intersection over k+1 coordinates then needs `(k+1)·δ/(1−ρ) < 1`, which FAILS at Johnson radius `δ ≈ 1−√ρ` for `k ≥ 2` (`(k+1)/(1+√ρ) > 1`). Prediction: the slack weld will be *provable as stated* (restriction is monotone) but its hypotheses are only jointly satisfiable in the small-`k`/small-`δ` regime — honest partial value (it does delete the residual below `δ < (1−ρ)/(k+1)`), not the Johnson closure.

**3. The paper-faithful route is per-coordinate-INDEPENDENT, and the in-tree machinery already matches its shape.** The paper's order is: global single-branch capture FIRST (Step 6, p.24–25: Hensel-lift uniqueness at the separable centre puts EVERY `z ∈ S′` on one branch — "they must be identically equal, by the uniqueness of the Hensel lift with a given starting simple root"), then per-coordinate `𝒪`-level kill, then `L`-interpolation. Mapping to the tree:
- per-coordinate `𝒪`-kill = **already landed** (`CoordinateKillBudget` Part 1, `eq_section_of_many_fiber_agreements` — its hypothesis counts only the agreement fiber at that coordinate, exactly the paper's Claim 5.10 shape, with the Λ-recursion replaced by the budget);
- rich-coordinate supply = **already landed** (`exists_rich_coordinates`, Claim 5.11's elementary half);
- branch interpolation = in-tree (`curve_pin_of_node_agreement` / `branchOfCurveTuple`) **but currently stated per-scalar**; the paper does it once in `L` — an `𝒪`-level analogue (interpolate the `𝒪`-element `γ` from k+1 section identities) is the missing wiring;
- global capture (Step 6) = the genuine remaining mathematics: every cell scalar's decode is the `π_z`-fiber of ONE branch. This is the **R-A1 hypothesis from the portfolio** (cross-coordinate branch globalization), and the in-tree Hensel bricks (`HenselBranchRigidity`, `CurveHenselSupply.curve_dvd_specialization_of_close`, the S10-converse lane) are its local inputs. Quantitative cost in the paper: the `1/D_Y` Claim-5.7 pigeonhole + the additive pole-removal `≤ D_Y²·D_{YZ}` defining `S′` — both already have in-tree counterparts (`FactorAssignmentPigeonhole`, the certificate-nonvanishing legs).

**Consequence for execution**: the running workflow's R-K3/R-A5 results will calibrate the slack lane's exact regime; the follow-up assembly should pivot the Johnson-regime closure onto R-A1 (global capture → per-coordinate 𝒪-kill at rich coordinates → 𝒪-level interpolation), promoting R-A1 from "advanced/optional" to the critical path. Λ-recursion stays bypassed (budget kills suffice — the paper's App-A recursion is only needed to BOUND the weight, which the budget supplies directly). Will report when the workflow returns.


=== comment 89 (lalalune) ===
**Hypothesis A5 core LANDED** (`OracleReduction/FullPredKSF.lean`, 2/2 axiom-clean): `fullPredKSF` + `rbrKnowledgeSoundness_of_salvageBound` — the architecturally correct sub-unit shell. Unlike the threshold form (whose state becomes True past the threshold, making the flip challenge-independent), the full-predicate KSF keeps the predicate at every round: challenge-round flips ARE salvage events, bounded per round by the landed Schwartz–Zippel machinery (`probEvent_salvage_le` ⟹ `d/|F|` for PIT-style checks). The `hFull` leg is exactly where checked-verifier decisions enter — `whirVerifyChecked` (#302) and `CheckedFinalBlock` (#301) both instantiate this one shell: the A5 unification realized. Remaining for both sub-unit theorems: the per-protocol `hSalvage`/`hFull` instantiations (the predicate plumbing of the killed wave agents, resumable from their scratches).

=== comment 90 (lalalune) ===
## hlin program: first two kernel bricks LANDED (K4 + K5), A3 refuted, K1/K2 in flight

**K4 — `Hab25HeavyPoints.lean` (`37bf24958`, axiom-clean):** the Claim 5.11 selection machinery, generic over `f : ι → ℕ`: `card_heavy_ge_of_sum_ge` ((n−k)·m < (n−e−k)·S ⟹ ≥ k+1 coordinates with f x > m), `sum_good_card_ge` (per-z bad-card ≤ e ⟹ Σ_x |S′_x| ≥ (n−e)·|S′|, Fubini), `card_heavy_points_ge`/`exists_heavy_subset` (Claim 5.11 packaged), `affine_eq_of_two_points`/`affine_eq_of_two_scalars` (2×2 Vandermonde pinning), `exists_pinned_points` (the Step-7→Step-8 hand-off: k+1 coordinates with the affine data fully pinned).

**K5 — `GSLargeCharSeparable.lean` (`582dceed0`, axiom-clean):** `Irreducible.separable_of_natDegree_lt_ringChar` over ANY field (crucially imperfect `F(Z)(X)`: inseparable ⟹ derivative 0 ⟹ `expand p` ⟹ `p ∣ deg`), discriminant analogues without `[PerfectField]`, and the full mirrors `gs_interpolant_good_specialization_largeChar` / `gs_interpolant_squarefree_discr_largeChar` / `radical_rep_good_specialization_largeChar` — **the S5/separability supply now covers `char F = 0` OR `char F > deg_Y`; BCIKS20 Appendix C is rigorously vacuous in the large-char regime** (which since `D_Y < ℓ = (m+½)/√ρ` covers every large-prime WHIR deployment). Small-char (binary) App C stays a named residual.

**A3 refuted at statement level** (as scheduled): `H̃ = T²−Z`, `γ = a + T·b`, `R = (Y−a)²−Z·b²` satisfies the derivation identity `R_Y(γ)·∂_Zγ + R_Z(γ) = 0` identically with all degree budgets, yet `γ` is not Z-linear and any 2 places are affine-matchable — the differential structure cannot replace threshold counting. No Lean investment made.

**Quadratic-budget verification for K2** (the wave-5 wall dodge): swept `d∈[2,9], dH∈[1,d], D∈[dH,14], k∈[0,25]`, all partitions, both `Λ(W) ∈ {0, D}`: with per-order budget `B(l) = (l+1)²·d·D` the per-term sub-additive estimate closes with min slack 1 (tight at `(d,dH,D,k,i1,λ) = (2,1,1,1,0,[1,1])` — exactly the wave-5 counterexample, now passing). The induction needs NO structured invariant and NO Faà-di-Bruno bijection; cost = polynomially worse threshold in the A.1 kill (quadratic→cubic-ish error in n), absorbed by the consumer.

**In flight:** K1 (`NormVanishingKernel.lean` — Lemma A.1 via the multiplication-matrix determinant: weight-monotone `modByMonic` + permutation-telescoped det degree + per-place kernel vectors `H_z/(T−t_z)`; the unit-(2) Cramer symmetry reused) and K2 (`QuadraticBudgetWeight.lean` as above). Next after those: K3 (Claim 5.8 X-degree kill assembly) and the K4-consuming Claim 5.9 geometric route — which dodges the in-tree d≥3 span-local obstruction (`functionFieldT_sq_no_T_repr`) exactly as the paper does.


=== comment 91 (lalalune) ===
**THE SUB-UNIT WHIR RBR LANDED** (`SubUnitRbr.lean`, 1088 lines, all audits axiom-clean): the complete quantitative arc at the checked verifier — the prefix chain predicate tied to the landed decision (`whirChainOK_iff_whirCheckingBool`), the **uniform challenge marginal proven** (`probEvent_chalElemOf_eq_uniform` — the one missing probability fact), the per-round Schwartz–Zippel salvage games (`whir_salvage_initial_le`/`whir_salvage_main_le`), and the capstones: `whirVectorIOP_rbrKnowledgeSoundness_smallField` and **`whirCheckedVectorIOP_isSecureWithGap_smallField`** — `IsSecureWithGap` at the SUB-UNIT budget. With this, #302's protocol side is complete through the quantitative regime: placeholder residuals ✓ (indicator), checked verifier ✓, sub-unit budget ✓. The remaining #302 scope is the Johnson-MCA analytic lane (the parallel session's territory). Hypothesis program final score this session: **K1 ✓ K4 ✓ A4 ✓ A5 ✓(core + this instantiation) A3 corrected; K5/K2/A1/A2 remain open with roadmaps.**

=== comment 92 (lalalune) ===
## R-K1/R-K2/R-K3/R-K4 LANDED (axiom-clean, verified, pushed) — 4 of 5 known-math hypotheses from the portfolio, same day

**`Hab25SlackWeld.lean`** (`ff28372f0`) — **R-K3, the slack weld**: `global_branch_of_witnessed_subcell` — the weld's factor data is demanded only at witnessed `(t, γ)` pairs; the per-coordinate defect (≤ M unwitnessed scalars at each of the k coordinates) is absorbed by the count leg `|E| > B_R + deg_Y R·(L−1) + k·M` via a union bound (`E \ E′ ⊆ ⋃_{t∈T} defect_t`). The unwitnessed scalars are *counted away, never pinned* — the branch conclusion is about `R`, not `E`. Plus `global_branch_of_fully_witnessed` (**R-K1**, the M = 0 corollary). The honest regime statement from the literature re-check is in the docstring: BCIKS20 does NOT take this route; the intersection subcell dies at Johnson radius for k ≥ 2 (multiplicative defect, Claim 5.11), so this is genuine content below `k·δ/(1−ρ) < 1`, not the Johnson closure.

**`Hab25UniqueRichFactor.lean`** (`deb792637`) — **R-K2, the unique rich factor**: `WitnessRich` + `WitnessRich.associated_section` (a rich budgeted irreducible factor is an associate of `Y − C w`), `witnessRich_at_most_one` / `not_witnessRich_both_of_isCoprime` (two non-associate or coprime factors cannot both be rich), `witnessRich_factor_unique` (family version), `exists_unique_witnessRich_factor` (richness concentration: mass > (#factors)·threshold ⟹ the rich factor exists and is unique). "The rich factor" is now well-defined per coordinate.

**`Hab25FactorBudgetSupply.lean`** (`e905093e6`) — **R-K4, the budget supply**: `factorBudgetSupply` / `exists_weldFactorInputs` — the weld's abstract inputs `(ι, Hf, hirr, hB)` produced outright from a budgeted interpolant: normalized positive-Y-degree irreducible factor index with `card ≤ deg_Y`, divisor-inherited flat budgets (`coeff_budget_of_dvd`), and **root attribution** (every live fiber root roots in some indexed factor — the step that feeds `assign`).

All three: `lake env lean` exit 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no sorries. (Process note: R-K2/R-K4 were drafted by workflow agents that died at a session limit mid-flight; both drafts were adversarially verified — compile, axiom audit, sorry-grep, decl-existence — before being committed.)

**What this composes to**: for *witnessed* scalars the full weld chain is now: attribution (R-K4) → pigeonhole concentration (R-K2) → the rich factor is `c·(Y − w_t(Z))`, whose fiber root at any witnessed scalar is the fold value = the decode value, discharging `hroot`/`hrich`/`hwit` simultaneously; R-K3 then counts the unwitnessed scalars away. **Remaining for the full assembly (R-K5)**: the witnessed-mass legs at the chosen coordinates (supplied by the in-tree `exists_rich_coordinates`, Claim 5.11's elementary half) + the variable-bookkeeping weld between R's specialization order and the per-coordinate fiber factors. Remaining beyond that: the Johnson-regime defect problem (per the literature note, the R-A1 per-coordinate-independent route: global capture + the 𝒪-level kill). R-K5 assembly attempt next; R-A5 fence still queued.


=== comment 93 (lalalune) ===
## The WHIR checked-verifier sub-unit weld: exact remaining shape identified (cross-post with #301 — same weld, two instantiations)

The protocol-side residual `whirCheckedVectorIOP_rbrKnowledgeSoundness` is one weld away from sub-unit per-round budgets. Inventory: `SubUnitRbr.lean` has the chain predicate, proven hEmpty/hConcat legs, the full-transcript IFF against `whirCheckingBool`, the uniform-challenge marginal lemma, and the SZ salvage cores (`whir_salvage_initial_le`/`whir_salvage_main_le`, maxLen/|F| each); `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound` is the non-threshold shell its honesty note asked for. **The trap**: `whirChainClosePred` is a conjunction (δ-close ∧ chain) — under the full shell, `hFull` (acceptance ⟹ final state) is FALSE for far-input-accepting provers. The redesign is the door-die disjunction `δ-close ∨ Survived(prefix)` with Survived = (visible chain checks pass ∧ pending-committed equation data coherent ∧ final-phase commitments well-formed), then per-challenge flip bounds: SZ salvage `maxLen/|F|` at sumcheck challenges (cores already proven), binding-style bounds at the folding/final randomness slots. Full per-round analysis (each case validated against an explicit attack — echo, switch, mixed) posted on #301 (issuecomment-4674555478); the STIR instantiation lands first, WHIR ports the pattern.


=== comment 94 (lalalune) ===
## THE GEOMETRIC hlin ROUTE LANDED — three bricks, the d_H ≥ 2 kill is now a theorem with finitely-producible inputs

Subagent rate limits killed the workflow fleet twice, so these were built inline. All axiom-clean `[propext, Classical.choice, Quot.sound]`, pushed:

**1. `Claim59Vandermonde.lean`** (`b8cf0d4d9`) — Claim 5.9 by **Vandermonde globalization**, eval-free: coefficient tail (Claim 5.8′) + `n` distinct ground-affine coefficient-sum values ⟹ `gammaGenuine_paperZ_linear` (every `αGenuine t` on the ground `F[Z]`-line, Z-degree ≤ 1), by inverting the F-rational Vandermonde system **over F** — no Lagrange API, no `Polynomial (𝕃 H)` eval (dodges a catastrophic elaboration blowup in the noncomputable `IsField.toField` instance: the first attempt with `trunc`-polynomial evaluation timed out at 1.6M heartbeats; the Vandermonde form needs only the cheap quotient-Ring instance). Composed with the PROVEN `ZLinearClosureAudit` collapse: `natDegree_eq_one_of_vandermonde_values`, `false_of_vandermonde_values_of_two_le`.

**KEY REFRAME** that unlocked this: the in-tree "Claim 5.9 refuted-as-stated" facts (`not_gammaGenuine_paperZ_linear`: `α₀ = T/W` off the ground line for `d_H ≥ 2`) are not an obstruction — they are **the kill mechanism**. Heaviness forces γ onto the ground line (Claims 5.10/5.11); the off-ground α₀ then yields the contradiction that eliminates `Y`-degree ≥ 2 branches. The paper's §5.2.7 "γ = v₀ + Z·v₁" is a curve-collapse engine, exactly as the F-series audit said.

**2. `Claim510Kill.lean`** (`5d34edab4`) — the Claim 5.10 **per-point kill**: `clearedSum`/`killTarget` (the ξ-cleared 𝒪-elements of the genuine coefficient sum at a node, monic lift identity `embed(βHensel t) = α_t·ξ̂^{2t−1}` with uniform `ξ̂^{2n}` clearing), `π_z_killTarget` (per-place reading under coefficient pinning), `mem_S_β_killTarget_of_pin_agree`, and `coeff_sum_eq_ground_of_large(_fin)`: **the in-tree PROVEN `Lemma_A_1`** (which an earlier fleet audit had wrongly reported absent — it lives at `RationalFunctionsCore.lean:1631`, Sylvester/resultant route) forces the coefficient sum to the ground-affine value. Output shape = exactly brick 1's `hvals` input.

**3. `Claim510Weld.lean`** (`5feedcb11`) — **the weld**: `natDegree_eq_one_of_heavy_data` / `false_of_heavy_data_of_two_le`. The monic lift identity is discharged outright by the PROVEN `restrictedFaaDiBrunoMatch_of_monic` (NO Faà-di-Bruno residual on this lane). A monic branch `H` carrying heavy per-place data at `n` distinct nodes is `Y`-linear. The remaining inputs are all finitely-producible, each with a known in-tree producer surface:

| input | producer surface |
|---|---|
| `htail` (αGenuine t = 0, t ≥ n) | in-tree truncation capstones (`gammaGenuine_eq_trunc_of_graded_disc`, `…_of_pigeonhole_abInitio`, `…_global_residue`) via `alphaGenuine_tail_zero_of_trunc` |
| `hpin` (per-place `π_z(βHensel t) = c_t·ξ_z^{2t−1}`) + agreement | the decoded/pigeonhole lane (`DecodedProximateRoot` coeff formula `((taylor (C x₀) w).coeff t).eval z`, `PlaceSeriesCanonical.aBetaPlace`) — **the main remaining wiring** |
| `hweight` (kill-target weight ≤ W) | `weight_Λ_over_𝒪` calculus + `weight_βHensel_le_graded` (mechanical, ~150 lines) |
| `hcard` (W·d_H < per-node card) | `Hab25HeavyPoints` (landed earlier today) + the dichotomy threshold |

Downstream wiring (unchanged plan): heavy ⟹ d_H = 1 ⟹ affine pair via the linear-factor machinery ⟹ `Hab25JohnsonDichotomyData.hdichotomy` / `exists_algebraicData_of_affine_capture` ⟹ `johnsonNumericBound_of_affine_capture`. Also relevant for closure semantics, from this session's audit: in-tree `JohnsonNumericBound` is the **BCHKS25 linear-in-n** closed form; `mca_johnson_bound_CONJECTURE`'s errStar is the **quadratic** Hab25 form (`2^{2m} = (ρn)²`); `whirRbrKeystone_of_correlatedAgreement` is fully errStar-**parametric**, so partial numeric rungs still thread to WHIR rbr-soundness.


=== comment 95 (lalalune) ===
## hlin surface reduced again: `Claim510Supply.lean` landed (`73a70ab11`, 7/7 axiom-clean) — pinning is AUTOMATIC, weight is DISCHARGED

Two of the weld's four inputs are gone:

**`weight_killTarget_le`** — the weld's `hweight`, discharged outright: explicit ℕ-budget `killBudget n D d_H d_R xw = (d_R·m + D + m)·2n + m + 2n·xw + 1` (`m = D−d_H+1`) from the in-tree graded `βHensel` bound (`weight_βHensel_le_graded`) + a `ξ`-weight bound (producer `xi_weight_le_of_coeff_bounds`), via the `Λ_𝒪` calculus. Lean note: keep budget atoms literal — `set`-folding them breaks `omega`'s atomization after `killBudget` unfolds.

**`pi_z_pinning_of_monic`** — the weld's `hpin`, discharged BY CONSTRUCTION: for monic `H`, `ξ` is a unit of `𝒪` (`isUnit_ξ_of_monic`), so `βHensel t = aPre t · ξ^{2t−1}` holds **in `𝒪`** (`aPre t := βHensel t·(ξ⁻¹)^{2t−1}`), and every place `π_z` satisfies the pinning with `c t := π_z (aPre t)` — a ring-hom application, no per-place hypothesis.

**The agreement-only weld** (`natDegree_eq_one_of_heavy_agreement` / `false_of_heavy_agreement_of_two_le`): the ENTIRE remaining per-place content of hlin is now the single hypothesis

`hagree : ∀ j, ∀ z ∈ matchingSet j, ∃ root, ∑_{t<n} π_z(aPre t)·(e j)^t = u₀ j + z·u₁ j`

— "the per-place reading of the genuine branch at the heavy coordinate equals the affine fold value." Its production = per-place Hensel uniqueness (`π_z ∘ γ`-coefficients = Taylor coefficients of the decoded `P_z` at `x₀`, then the Taylor sum identity + the proximity agreement at the heavy coordinate). Producer surface: the decoded lane (`DecodedProximateRoot` coeff formula, `PlaceSeriesCanonical.aBetaPlace` with the hαβ slot already definitional, `gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic`). Remaining global inputs: `htail` (in-tree truncation capstones) + `hcard` (heavy-point budget, `Hab25HeavyPoints`).

Full chain status: `hagree` + `htail` + `hcard` ⟹ `d_H = 1` (PROVEN weld) ⟹ affine pair ⟹ `hdichotomy`/`exists_algebraicData_of_affine_capture` ⟹ `johnsonNumericBound_of_affine_capture` (all in-tree bridges proven).


=== comment 96 (lalalune) ===
## R-A5 LANDED: the slack-weld fence — the witness data is formally load-bearing (`2584b9a3a`)

`Hab25SlackWeldFence.lean`, axiom-clean: **`slack_only_strawman_false`** — the slack weld with the `hroot`/`hrich`/`hwit` legs deleted is REFUTED, machine-checked: over `ZMod 7`, `R := Y² − Z` admits the complete slack-data package (the square cell `{0,1,2,4}`, per-scalar `√γ` decodes with genuine fiber divisibility `(Y−√γ) ∣ (Y²−γ)`, flat budget 1, count leg `2 < 4` with genuine `k = M = 1` slack) — yet no global branch exists (`(Y − C pHat) ∣ Y² − Z` forces `pHat² = Z`, killed by Z-degree parity). This is the formal counterpart of the `Hab25CandidateProduction` prose honesty note, and a permanent fence against any future "simplification" that drops the witnessed-agreement data from the R-K3/R-K5 chain.

**Portfolio scoreboard** (all axiom-clean, all pushed today): R-K1 ✅ R-K2 ✅ R-K3 ✅ R-K4 ✅ R-K5 ✅ R-A5 ✅. Remaining advanced lanes: **R-A1** (the paper-faithful Johnson-regime route: Step-6 global capture weld + the `𝒪`-level per-coordinate kill + scalar-free `𝕃`-interpolation — per the BCIKS20 literature check, this is the critical path past the slack lane's `k·δ/(1−ρ) < 1` regime), R-A4 (two-altitude kill unification incl. the Whir `K4ComponentResidual` interface), R-A2/R-A3 (probes). Also queued from the #301 side: the WHIR checked-verifier door-die port (the conjunction trap fix), now with the complete STIR pattern (`Stir/SubUnitRbr.lean`) to mirror.


=== comment 97 (lalalune) ===
## FRONTIER MAP after today's brick storm (consolidated from all parallel lanes, 2026-06-10 ~15:45)

Today's landings interlock across three lanes; here is the assembled state so nobody re-proves or misses the remaining seams.

**Lane 1 — the witnessed/counting chain (the R-K portfolio, complete)**: `Hab25SlackWeld` (R-K3+R-K1) → `Hab25UniqueRichFactor` (R-K2) → `Hab25FactorBudgetSupply` (R-K4) → `Hab25RichCoordinateGate` (R-K5: `exists_global_branch_of_proximity` — proximity data + Claim 5.11 numeric leg + richness-guarded factor data ⟹ global branch) + `Hab25SlackWeldFence` (R-A5: the witness data is formally load-bearing, Y²−Z refutation). Regime: below `k·δ/(1−ρ) < 1` (the lit-check's multiplicative-defect warning).

**Lane 2 — the hlin gate (Claim 5.9/5.10, the "one deep gap"), dramatically narrowed today**: `Claim510Kill` (B1, per-point kill) + `Claim59Vandermonde` (eval-free globalization over F — dodges `Polynomial (𝕃 H)` eval entirely) + **`Claim510Weld.false_of_heavy_data_of_two_le` — hlin itself, reduced to four finitely-producible inputs** + `Claim510Supply` discharging TWO of them for monic `H` (the weight bound via the graded `βHensel` calculus, and `hpin` automatic since `ξ` is a unit). **Remaining inputs**: (i) the coefficient tail (Claim 5.8′ — the truncation capstones exist, wiring needed); (ii) **the per-place agreement** `∑_t π_z(aPre t)·e^t = u₀ + z·u₁` on the heavy place sets — the genuine remaining content (the Hensel-uniqueness reading of the decoded lane); plus monicity supply (monicization/`P2MatchMonic` exists) and the heavy-point budget (`Hab25HeavyPoints`, landed).

**Lane 3 — the #304 global assembler (`Section5GlobalAssembler.ofProducersOn_global`)**: the per-place §5 geometry (six inputs) is REPLACED by four single global GS facts: `hsplit` (GS split at the centre), `hdvdR` (the global surface factor `(Y′−C w) ∣ R`, deg < k), `hbr` (branch separation), `hRsep` (GS squarefreeness). This is the same shape as Lane 1's conclusion — **the global branch produced by `exists_global_branch_of_proximity` is literally Lane 3's `hdvdR` input**, and Lane 2's hlin kills the d_H ≥ 2 branches that would obstruct Lane 3's `hsplit`-side factor analysis.

**The composition opportunity (next assembly target)**: weld Lane 1's output into Lane 3's `hdvdR` slot, and Lane 2's remaining agreement input into the decoded-lane supply that Lane 3 already constructs (`DecodedProximateRoot`/`DecodedRootSupply` — the same objects). If those two seams close, the below-Johnson `JohnsonNumericBound`/`mca_johnson_bound_CONJECTURE` surface is conditional on: numeric legs + proximity data + the Claim 5.8′ wiring — i.e., assembly, not new mathematics. Flagging this as the highest-value next step for whichever agent has the Section5 bundle context loaded.

(Cross-issue: #301's headline closed today — `stirCheckingCABridge_genuine` verified; see issue #301 for the milestone audit and the honest Lemma-5.4/t-repetition residue.)


=== comment 98 (lekt9) ===
Count wiring landed (`996c9b521`, axiom-clean): **`Hab25JohnsonCountWiring.lean`** closes the pair-quantification gap flagged in the roadmap — the dichotomy bundles count one line while `ε_mca` sups over pairs, with no semantic tie to `mcaEvent`. Three glue theorems on the in-tree keystone `epsMCA_le_of_badCount_le`: `badCount_le_of_dichotomy_cover` (bundle covers the pair's bad scalars ⟹ count ≤ ℓ·max(T,n)), `johnsonNumericBound_of_badCount_le` (uniform count + arithmetic ⟹ numeric edge), and **`johnsonNumericBound_of_forall_dichotomy`** — the named remaining obligation: *every word pair admits a covering dichotomy bundle within budget*. The below-Johnson program is now: per-pair bundle construction from the S2–S8 GS chain (in-tree), modulo `hlin`. Next bricks: the factor-count + Efactor-extraction wirings, then the per-pair assembly, then the `hlin` siege.

=== comment 99 (lalalune) ===
## hlin DISCHARGED END-TO-END at the monic branch class — `Claim510EndToEnd.lean` (`1434a3813`, axiom-clean)

**`natDegree_eq_one_of_decoded_heavy` / `false_of_decoded_heavy_of_two_le`** — ONE theorem from named GS-side data to the curve collapse:

> decoded GS surface (`(Y′−C w) ∣ R`, per-place base-point roots, `R.Separable`, per-place `ξ_z ≠ 0`) **+** coefficient tail (`αGenuine t = 0, t ≥ n` — the in-tree truncation capstones) **+** proximity agreement at `n` distinct heavy RS coordinates (`w(ωⱼ)(z) = u₀ⱼ + z·u₁ⱼ` on the matching sets) **+** graded weight side conditions **+** heavy cardinality (`killBudget·d_H < |matchingSet j|`) ⟹ **`H.natDegree = 1`**.

No per-`z` decoded root lives on a `Y`-degree ≥ 2 monic branch — [BCIKS20] §5 Steps 5–7 / [Hab25] Claim 1's deep gate, machine-checked. The final brick was **`Claim510Agreement.lean`** (`3d656c6c9`): per-place Hensel uniqueness `localSeries = aPDecoded` via `specialization_eq_proximate_root_of_hensel` applied to the PROVEN `placeGeometry_of_localSeries` (all `aβ`-side facts were already in-tree — root, congruence, simple-root derivative), the coefficient reading by `ξ_z`-power cancellation against `coeff_localSeries_mul` + the automatic pinning, and the value reading via `Polynomial.taylor_eval`.

**The complete 8-brick arc this session** (all `[propext, Classical.choice, Quot.sound]`): `Hab25HeavyPoints` (5.11 selection) → `GSLargeCharSeparable` (App C vacuous at `char F > d_Y`) → `Claim59Vandermonde` (5.9 globalization, eval-free) → `Claim510Kill` (per-point A.1 kill) → `Claim510Weld` → `Claim510Supply` (weight discharged; pinning AUTOMATIC via the ξ-unit) → `Claim510Agreement` (per-place uniqueness) → `Claim510EndToEnd`.

**Remaining for the full Johnson MCA discharge** (all wiring, no new deep math on this lane):
1. `d_H = 1` ⟹ affine pair (in-tree `Hab25LinearFactorCapture`/`GSAffinePair`) ⟹ `hdichotomy`'s improve branch / `AffineCaptured`;
2. the per-factor dichotomy assembly + `johnsonNumericBound_of_hlin` (the parallel lane's declared items 1/2/4);
3. the S4/S10 production of the surface data per heavy factor (the #304 `DoubleAssignmentChain`/pigeonhole chain — largely in-tree);
4. the numeric form at the chosen rung (in-tree `JohnsonNumericBound` = BCHKS25-linear; the WHIR conjecture = Hab25-quadratic; `whirRbrKeystone` is errStar-parametric so any rung threads).

Small-characteristic (binary-field) branches remain the App C residual — vacuous for `char F > D_Y` per `GSLargeCharSeparable`, which covers all large-prime WHIR deployments.


=== comment 100 (lalalune) ===
**Affine-pair extraction landed** (`Claim510AffinePair.lean`, `a2cf1be28`, axiom-clean): `aPre_eq_groundAffine_of_paperZ_linear` (embed-injectivity through the monic lift identity pins the 𝒪-preimages) + `taylor_coeff_eq_affine_of_heavy` — on a heavy monic branch **every matching place decodes to the SAME affine family**: Taylor coeff `t` of the decoded slice `= a t + z·b t`. This is the verbatim [BCIKS20] Step-7 positive output, shape-ready for `AffineCaptured`/`hdichotomy`'s improve branch (`affineCaptured_improve`). Both halves of the dichotomy improve branch (collapse + affine family) are now theorems; remaining = the per-factor assembly (the declared parallel-lane wiring: factor-count, exceptional-set extraction, `johnsonNumericBound_of_hlin`) + S4/S10 surface production + the numeric rung.

=== comment 101 (lekt9) ===
## The program has one neck: `hsteps57` — final map of the below-Johnson discharge

Day-10 mapping result: the formalization is **complete except for literally one hypothesis**. The full funnel, every stage sorry-free on main:

```
JohnsonNumericBound
 ⟸ epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover     (Hab25AlgebraicBridge — per-stack covers ⟹ numeric edge)
    [parallel route: johnsonNumericBound_of_forall_dichotomy, Hab25JohnsonCountWiring]
 ⟸ exists_algebraicData_of_affine_capture               (Hab25AffineCapture — capture pair-list ⟹ full bundle,
                                                          Edis = hab25McaBadScalars, hImprove = affineCaptured_improve, PROVEN)
 ⟸ per-cell counting: claim1_dichotomy                  (Hab25Claim1 — Claim 1 PROVEN modulo hsteps57;
                                                          closing numerology hab25_threshold_gt_n also PROVEN)
 ⟸ hsteps57 :  T < |E_cell| →
      ∃ a b : F₀[X], deg a < k ∧ deg b < k ∧ ∀ γ ∈ E_cell, AffineCaptured domain k δ u γ (a, b)
```

`hsteps57` is the exact content the paper cites from [BCIKS20] Claim 5.7 + Steps 5–7 + Appendix C: *a cell above the threshold forces its factor to be the affine power `(Y − (a+Zb))^{p^f}`, so one degree-`<k` pair captures every scalar of the cell*. Its **interior is also mostly in-tree**: the K-decoded list (S2–S3, `GSOverRatFunc` + Z-degree budgets), per-z factor assignment with charZero separability (`Hab25S4Wire` + `Hab25SeparableSupply`), decode↔capture equivalence (`affineCaptured_iff_exists_mcaDecode`, `Hab25CaptureKernel`), affine-pair extraction (`GSAffinePair`), and the uniqueness weld (`Hab25FactorWeld.decoded_root_eq_affine_of_claiming_linear` — which consumes a *linearity* input).

**What is genuinely left inside `hsteps57`:** the branch-incidence ⟹ linearity step — a factor claiming more than `2·D_Y²·D_X·D_{YZ}` scalars cannot have `deg_Y ≥ 2` (the pigeonhole over branch incidences, [BCIKS20] Claim 5.7's proof, plus the char-p `p^f`-peel of Appendix C). Everything else is assembly between existing in-tree surfaces.

So the siege has one wall and its coordinates are known. Suggested attack order: (i) the incidence double-count behind Claim 5.7 (combinatorial, no Hensel needed — counts (z, branch) pairs against `D_Y·D_X`-style budgets); (ii) the wiring of that count through the factor assignment to produce the `hsteps57` pair via the existing weld; (iii) charZero first, `p^f`-peel later (the prize fields are prime, charZero techniques port).


=== comment 102 (lalalune) ===
**The geometric lane is COMPLETE end-to-end** — `Claim510SliceAffine.lean` (`fa24f4fdb`) + `Claim510Capture.lean` (`ac224c1e9`), both axiom-clean: `slice_eq_affinePencil_of_heavy` (the decoded slice at EVERY matching place is the ONE fixed pencil `v₀(ω)+z·v₁(ω)`, explicit recentred pencils of degree < n) and `affineCaptured_of_pencil_proximity` (pencil + the §5 per-scalar proximity data ⟹ `AffineCaptured` at the pencil pair). **11 bricks this session**: the chain now runs GS surface data → hlin (d_H = 1) → affine pencil → `AffineCaptured` → the PROVEN `exists_algebraicData_of_affine_capture`/`johnsonNumericBound_of_affine_capture` front doors. Remaining for the numeric bound: (a) the per-stack aggregation over the ≤ ℓ branches (every bad scalar captured by some heavy branch, light branches counted by the dichotomy threshold — the declared parallel-lane items 1/2/4), (b) the S4/S10 surface production per heavy factor (#304 pigeonhole chain, largely in-tree), (c) the closing arithmetic at the chosen numeric rung.

=== comment 103 (lalalune) ===
**CONVERGENCE**: with `johnsonNumericBound_of_forall_dichotomy` (parallel lane, `Hab25JohnsonCountWiring.lean`) + this lane's 11-brick geometric arc, the ENTIRE #302 MCA discharge is now ONE production: per word pair `u`, the dichotomy bundle `Hab25JohnsonDichotomyData` from the GS chain — per-`u` GS interpolant (`gs_existence_over_ratfunc`, in-tree) → factor decomposition (`PigeonholeFactorSupply`, in-tree) → per factor: **heavy ⟹ the improve branch via this lane's `affineCaptured_of_pencil_proximity` + `affineCaptured_improve`** (surface data per factor from the #304 `GSSurfaceSupply`/`DoubleAssignmentChain` machinery), **light ⟹ the `card ≤ T` branch** (the threshold counts it — no pair needed). All deep mathematics on both branches is now theorem-backed; what remains is the per-`u` assembly + the closing arithmetic `B/|F| ≤ johnsonBoundReal` at the chosen rung. App C (small char) stays the named residual, vacuous for `char F > D_Y` (`GSLargeCharSeparable`).

=== comment 104 (lekt9) ===
## Siege intelligence: faithful BCIKS20 §5 digest + EndToEnd producer table + two course corrections

Two deep audits complete (full BCIKS20 §5/App A/App C digest + hypothesis→producer trace for `Claim510EndToEnd`). Posting the consolidated findings since they affect the active stream.

### Course correction 1: Appendix C is skippable for prize instances
Inseparable factors `Rᵢ(X, Y^{p^f}, Z)` require `p ≤ D_Y`. Prize fields have `p` astronomically above `D_Y < (m+½)/√ρ` — **`f = 0` is automatic at large characteristic** (the paper itself notes this). So the App-C shell (purely-inseparable extension `L̂`, weight-preserving `σ̂`, Frobenius peel) is *not* on the prize-critical path; it's completeness work. Corollary: any `CharZero` assumptions in the chain (e.g. the separable-supply theorem) should be generalized to **`D_Y < ringChar` form, not perfect-field form** — `RatFunc F_p` is *not* perfect, so a perfect-field generalization would be vacuous where it matters.

### Course correction 2: GSAffinePair shortens Steps 5–7
Since the in-tree `GSAffinePair` already derives `P = a + Z·b` (deg < k) from K-decodedness, **Claim 5.10's per-point weld only needs to be proven at the k+1 points of `D_top`** (not for all x), and Claim 5.9 reduces to "γ is the Lagrange interpolant of K-rational values" — eliminating direct Z-degree reasoning on γ's coefficients entirely. The Z-linearity comes from the *values* `w(x_j, Z) = u₀(x_j) + Z·u₁(x_j)` being manifestly affine, not from coefficient analysis.

### The irreducible residual (faithful to the paper)
With Steps 1–4 + the counting glue discharged in-tree, the open core is exactly:
- **(R1)** App A infrastructure (`L = AdjoinRoot H̃`, the regular subring `O`, weight `Λ`, substitutions `π_z`, **Lemma A.1** = resultant-degree zero-counting) + the non-monic Hensel lift with **Claim A.2**'s weight bounds `Λ(β_t) < (2t+1)dD` (Faà-di-Bruno expansion) + lift uniqueness over `F_q[[X−x₀]]` (kills `α_t` for `k < t < D_X`; weighted-degree truncation above `D_X`).
- **(R2)** One Lemma-A.1 application instance per top point (Claim 5.10 at `D_top`) + Claim 5.11's double count (pure counting).
- Known trap already refuted in-tree: the naive `DivWeightLe` kernel is **false in both regimes** (`DivWeightLeMonicRefuted.lean`); the surviving route is the cleared/monic P1/P2 decomposition — exactly the `AlphaWeight*` / `ClearedFaaDiBruno*` / `HenselNumerator` band.

### EndToEnd assembly checklist (hypothesis → producer)
For `Claim510EndToEnd.natDegree_eq_one_of_decoded_heavy`: PROVEN in-tree — `htail` (GenuineTruncationFin), the monic pinning, agreement weld, weight supply, Vandermonde kill; K1 (decode family) is proven via `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`. OPEN producers (the translation layer, mostly assembly): the decoded-surface data (`hHyp`, `ξ ≠ 0`, `hdvd`, `hwn`), `R.Separable` (cheap at large char per correction 1), per-place roots + place-level ξ nonvanishing, proximity agreement + matching-set cardinalities (`Hab25HeavyPoints` budget), and the graded degree conditions (`hd2`, `hD_Rx0`, `hRgrade`, `hξw`). Topmost assembled theorem today: `mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo` (MCAJohnsonBound.lean) with two named inputs (`hInput`, `hdata`).

Full digests available on request; both source PDFs mirrored at /tmp during audit (eprint 2020/654 §5 pp. 17–28, App A pp. 50–53, App C pp. 57–58; 2025/2110).


=== comment 105 (lekt9) ===
Characteristic audit closed (follow-up to the siege-intelligence note): **the active capture lane is entirely characteristic-free** — `Hab25AffineCapture`, `Hab25JohnsonArith(metic)`, `Hab25Claim1`, `Hab25CaptureKernel`, and the whole `BCIKS20/` directory carry no `CharZero` assumption, so the prize fields F_p are served by the pencil/capture route as-is. The earlier concern applies only to the legacy `Hab25S4Wire`/`Hab25SeparableSupply` lane, which currently has **no consumers** on either the charZero or large-char side (`GSLargeCharSeparable.radical_rep_good_specialization_largeChar` exists, sorry-free, also unconsumed). Suggest treating that lane as superseded by the geometric route rather than wiring it — no porting brick needed. Distance-to-green remains exactly the per-stack capture production (translation layer + Hensel band).

=== comment 106 (lalalune) ===
**The assembly is closed**: `Claim510Improve.lean` (`6f2e2b183`) + `Claim510Bundle.lean` (`075030345`), both axiom-clean — **13 bricks this session**. `improve_disjunct_of_heavy` produces the dichotomy's useful branch in the VERBATIM `hdichotomy` shape (streams → fixed pencil → per-scalar `AffineCaptured` → `affineCaptured_improve`); `PerPairFactorData` is now **THE single named obligation** of the entire below-Johnson program (factor family ≤ ℓ + mcaEvent cover + light-or-improving per-factor dichotomy), and `johnsonNumericBound_of_perPairFactorData` threads it through the numeric bridge: per-pair data + `ℓ·max(T,n)/|F| ≤ johnsonBoundReal` ⟹ `JohnsonNumericBound` ⟹ (`mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound`) the WHIR conjecture, pair case.

**Remaining production for `PerPairFactorData`** (per word pair u): the per-u GS interpolant (`gs_existence_over_ratfunc`), the S4 factor assignment for `hcover` (γ bad ⟹ decoded P_γ ⟹ S10 divisibility ⟹ claimed by some factor — `exists_specialized_factor_assignment` is IN-TREE), the per-factor surface data for the heavy branch (the #304 production chain: `PigeonholeFactorSupply`, `GSSurfaceSupply`, `XiAtIncidenceSupply`, truncation capstones), and the closing arithmetic at the GS budgets. All wiring against proven machinery — no open mathematics remains on the below-Johnson lane (small-char App C excepted, vacuous for `char F > D_Y`).

=== comment 107 (lalalune) ===
**hcover's data layer COMPLETE** — `MCAEventDecodedBridge.lean` (`ea266a070`) + `PerPairCoverData.lean` (`5d3c9df26`), both axiom-clean (**16 bricks this session**). `mcaEvent_decoded_data`: every bad scalar (δ below the GS Johnson radius) yields a decoded codeword rooting `Q₀(γ)` with the event's witness set in the per-scalar capture shape. `exists_perPair_cover_data`: the factor assignment + the `badAll` avoidance polynomial (with the leading-coefficient specialization guard) — every bad scalar is **claimed by an irreducible factor of the generic interpolant or is one of ≤ deg(badAll) content-index scalars** ([BCHKS25] footnote 5 treatment, counted by the dichotomy's T-branch).

**Remaining for `PerPairFactorData`** (the 11pm fleet's brief, checkpointed): (1) the per-factor heavy supply — per claiming factor, the fiber-branch surface data (`PigeonholeFactorSupply` + branch pigeonhole + truncation capstones + `Hab25HeavyPoints` node selection) feeding `improve_disjunct_of_heavy`; (2) the `Idx := Option factors` packaging; (3) the closing-arithmetic rung decision (linear/quadratic tension documented in `Claim510Arith.lean`); (4) the protocol gates (parallel lane). No open mathematics remains on the below-Johnson lane.

=== comment 108 (lekt9) ===
## Below-Johnson consumer side: COMPLETE — one producer remains

Status of the Johnson MCA numeric edge (`JohnsonNumericBound`) as of `bc41fc81f`:

**Proven, axiom-clean, on main (the consumer chain):**
- Cell production at the **tight** Z-degree budget `n·|c|·(D/(k-1))` — `exists_cell_production_total_div` (the original `n·|c|·D` budget is arithmetically unusable: the per-stack count exceeds `johnsonBoundReal` by a factor growing linearly in n; see `GSInterpolantZDegreeTight.lean` header for the numeric sweep)
- Live-index bound `≤ D/(k-1)+1` via positive-Y-degree factor counting — `badCount_le_numeric_tight_of_window`
- The arithmetic side condition **closed in Lean** — `harith_tight_closed` (regime `2 ≤ k`, `k+1 ≤ n`, `12 ≤ m ≤ M_J`)
- End-to-end window instance with zero side conditions — `johnsonNumericBound_of_window_closed` (window `2n+k ≤ 3t`, via the full S2–S8 pipeline)
- Discharge site ready: `Hab25JohnsonDischarge.lean` — the unconditional statement is one hypothesis away via either funnel

**The single remaining input (per-factor-cell, beyond the window):**
```
E.card ≤ T  ∨  ∃ d₀ d₁, ∀ z ∈ E, ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0
```
i.e. [BCIKS20] Claim 5.7's threshold pigeonhole: a factor cell exceeding `T = 2·D_Y²·D_X·D_YZ` forces the heavy-agreement data (`htail`/`nodeSet`/`hweight`/`hcardNodes` of `Claim510Improve.improve_disjunct_of_heavy`), whose conclusion then matches the disjunct verbatim. On the window this is discharged by `exists_pencil_of_decode_family_window` (`cell_improvement_of_window`); beyond it, the Hensel depth>0 lane is the open item.

When that lands: swap the pencil source in `cell_improvement_of_window`/`hK4_of_window`, restate at the gate name, done. Happy to wire the moment the producer exists.

=== comment 109 (lekt9) ===
Addendum to the residual map: the Claim 5.7 heavy-data inputs are now all machinery-backed in-tree — `weight_killTarget_le` (hweight), `tail_zero_on_finite_range`/`SβLargeAtFin_of_card` (htail), `Claim510Agreement` (reads), `Finset.exists_covered_nodes_emb` (hcardNodes), `Polynomial.Bivariate.degreeX_coeff_le_of_dvd` (the capstone's `hR` graded input). What remains is the assembly of these named pieces into the per-cell disjunct — at which point `cell_improvement_of_window`'s beyond-window twin + `Hab25JohnsonDischarge` close the numeric edge mechanically.

=== comment 110 (lalalune) ===
Audit update (2026-06-11): comment-stripped scan of current `main` found no live `axiom`/`constant`/`opaque`, no `sorry`/`admit`, no `: True` declaration stubs, and no current `def/class ... : Prop` shortcut hit under `ArkLib/ProofSystem/Whir`. The earlier `FoldedStackOfRound : Prop := True` anchor is absent from current `HEAD`.

So this tracker remains about proving the actual WHIR soundness/MCA/CA content, not about removing a direct WHIR placeholder declaration.


=== comment 111 (lekt9) ===
Status pin: the final statement is now committed as `JohnsonDischargeStatement` (a `Prop` in `Hab25JohnsonDischarge.lean`):

```
∀ n k m [NeZero n] F₀ [Field/Fintype/DecidableEq] (domain : Fin n ↪ F₀) (η δ : ℝ≥0),
  2 ≤ k → k+1 ≤ n → 12 ≤ m → δ ≤ 1 → (δ:ℝ) < gs_johnson k n m →
  m ≤ max ⌈√ρ₊/(2η)⌉ 3 → JohnsonNumericBound domain k η δ
```

Already proven: on the UD window (`johnsonNumericBound_of_window_closed`, zero side conditions) and modulo the per-cell small-or-improving disjunct (`johnsonNumericBound_holds_of_himpr`, arithmetic fully discharged). The remaining beyond-window input reduces in-tree to the surface-factor production (`FiberSectionCoherence` Part 6 consuming the D_top weld of `exists_points_with_large_matching_subset` + Lagrange-interpolated fiber sections); a composition attempt is in progress. The boundary converters (`hab25McaBadScalars_subset_coeffs_of_close_proximity`, `affineCaptured_of_close_affine`) accept the lane's conclusions in any witness-set form.

=== comment 112 (lalalune) ===
## SEAM A CLOSED (`7b3568c95`): the counting-lane branch IS the Section-5 `hdvdR` input

`Hab25BranchToSection5.lean`, axiom-clean: **`exists_section5_hdvdR_of_proximity`** — under the rich-coordinate gate's hypotheses (per-scalar proximity + Claim 5.11 numeric leg + richness-guarded factor data + count leg), there is `w` with `w.natDegree < k` and `(Y′ − C w) ∣ R` — exactly the `hdvdR` slot of the #304 global assembler (`Section5GlobalAssembler.ofProducersOn_global`). The orientations match verbatim (outer = centre variable, inner = fold scalar; the divisibility is the gate's conclusion unchanged; the degree leg is `branchOfCurveTuple_natDegree_lt ∘ lagrangeCurveTuple_natDegree_lt`).

**Effect on the frontier**: of the four Section-5 global inputs, `hdvdR` is now produced by the counting lane (in its regime); `hsplit`/`hRsep` are GS-side outputs (split + squarefreeness — landed lanes), `hbr` is the branch-separation certificate. The remaining genuinely-open seam from the frontier map is **Seam B** (the per-place agreement supply for the hlin weld — the Hensel-uniqueness reading of the decoded lane), plus the Claim 5.8′ tail wiring. Also today on the #301 side: the full t-repetition checking IOPP was assembled (`MultiRoundSpecT.lean`, parts 1–3) — the WHIR door-die port and the t-point soundness rerun share the same remaining pattern.


=== comment 113 (lalalune) ===
## Claim 5.8′ tail wiring LANDED (`d3985123d`) — the hlin weld is down to ONE open input

`Claim58TailWiring.lean`, axiom-clean: **`alphaGenuine_tail_zero_of_graded_disc`** — the truncation capstone (`gammaGenuine_eq_trunc_of_graded_disc`) composed with the tail bridge (`alphaGenuine_tail_zero_of_trunc`) supplies the weld's coefficient-tail input end-to-end from the graded-disc package. Scoreboard for `Claim510Weld.natDegree_eq_one_of_heavy_data`'s four inputs: tail ✅ (this), weight bound ✅ (`Claim510Supply.weight_killTarget_le`), per-place pinning ✅ (automatic for monic `H`, `pi_z_pinning_of_monic`), **per-place agreement — the single remaining open input (Seam B)**: `∑_t π_z(aPre t)·e_jᵗ = u₀ j + z·u₁ j` at the heavy places, i.e. the Hensel-uniqueness identification of the branch's coefficient readings with the decoded value where the decode agrees with the fold. Also landed since the frontier map: **Seam A closed** (`7b3568c95`).


=== comment 114 (lalalune) ===
## THE hlin CAPSTONE LANDED (`Claim58TailWiring.lean`, axiom-clean): the gate is now graded-disc + agreement + numerics — nothing else

**`natDegree_eq_one_of_graded_disc_agreement`** (+ the `false_of_…_of_two_le` contradiction form): `H.natDegree = 1` from (i) the graded-disc truncation package (Claim 5.8′, supplied end-to-end by today's tail wiring), (ii) **the per-place agreement alone** — `∑_t π_z(aPre t)·e_jᵗ = u₀ j + z·u₁ j` at the heavy places (the pinning is automatic for monic `H` via the `ξ`-unit), (iii) a `ξ`-weight bound (producer exists: `BCoeffVanishing.xi_weight_le_of_coeff_bounds`), (iv) the heavy cardinality at the explicit `killBudget`. The composition consumed `Claim510Supply.natDegree_eq_one_of_heavy_agreement` + `weight_killTarget_le` + the new tail wiring — all landed in the last 24h across three parallel lanes.

**The entire below-Johnson hlin program is now pinned on Seam B** (the agreement input): identify `π_z(aPre t)` with the decoded polynomial's Hensel/Taylor coefficients at the agreeing places (BCIKS20 Step 6, Hensel-lift uniqueness from the common simple starting root — the `DecodedProximateRoot`/`PlaceSeriesCanonical` lane has the local inputs). That single identification, plus numerics, closes hlin for monic branches; the monicization and `d_H ≥ 2` collapse lanes are already landed.


=== comment 115 (lalalune) ===
## 🔓 SEAM B CLOSED + THE GRAND COMPOSITION: hlin is now produced from GS-side data ONLY (`Claim510AgreementSupply.lean`, 9 decls, axiom-clean, 0 sorries)

The last open input of the below-Johnson hlin gate is **discharged**:

**The Seam B chain** (BCIKS20 Step 6, at the in-tree genuine objects):
- `pi_z_aPre_eq_coeff_localSeries` — the normalization identification: `π_z(aPre t)` IS the `t`-th coefficient of the canonical local Hensel series (both clear to `π_z(βHensel t)` against `π_z(ξ)^{2t−1}`; cancellation);
- `localSeries_eq_aPDecoded` — **Hensel uniqueness**: the local series and the decoded surface's place-image are both roots of the specialized matching polynomial, congruent mod `X` to the common simple approximation — equal by `specialization_eq_proximate_root_of_hensel` on `placeGeometry_of_localSeries` (the paper's "they must be identically equal, by the uniqueness of the Hensel lift");
- `pi_z_aPre_eq_taylor_coeff` → `aPre_sum_eq_decode_eval` — the node sum collapses to the decoded surface's value (`eval_eq_sum_range'` + `taylor_eval`);
- **`hagree_of_decoded`** — the capstone's agreement input, end-to-end from: the GS surface factor + base-point geometry + separability + the fold readings at the nodes.

**The grand composition** — **`natDegree_eq_one_of_decoded_fold`** (+ `false_of_decoded_fold_of_two_le`): `H.natDegree = 1` from the GS surface factor `(Y′−C w) ∣ R`, base-point geometry on the truncation+heavy sets, `R.Separable`, the §6 discriminant counting, the graded degree budgets, the Prop-5.5 representative, fold readings at `n` injective nodes, the `ξ`-weight bound, and the `killBudget` cardinality. The truncation leg AND the agreement leg are produced by the decoded lane from the SAME surface data; the `π_z(ξ) ≠ 0` legs are free (monic `ξ` is an `𝒪`-unit; `nontrivial_𝒪` derived). **Every hypothesis is a named, finitely-checkable GS-side fact. The hlin gate contains no open mathematical input.**

Also landed this session: `Hab25WitnessMassWiring` (`exists_rich_factor_of_witness_mass` + `exists_global_branch_of_interpolant_mass` — the R-K5 residual item 1: pigeonhole over the attribution cover turns interpolant witness mass into the gate's rich-factor data, so the counting lane's input surface is now the GS supply shape too).

**What remains on #302 after tonight**: instantiating these gates at the concrete GS run (supplying `w`/`hdvd` from `Prop 5.5`'s output, the heavy sets from Claim 5.11's count — both have in-tree producers), the numeric legs, and the protocol-side WHIR checked-verifier soundness (the door-die port, next up). The mathematics of the below-Johnson MCA program is, as of tonight, assembly.


=== comment 116 (lalalune) ===
## ⚠ FINDING + FENCE (`439de2e7d`): the checked WHIR verifier is INPUT-OBLIVIOUS — the planned sub-unit port was chasing an impossible target

While preparing the door-die port of the STIR pattern to `whirVerifyChecked`, I checked the soundness-critical precondition and found it fails: **every check of `whirCheckingBool` (initial anchors/links, main-round links, final zero-sum) reads only prover messages and challenges — the input oracle is never queried.** Machine-checked consequence (`CheckedObliviousness.lean`, axiom-clean): **`whirCheckingBool_allZero`** — the all-zero prover strategy passes every check on EVERY statement and EVERY challenge draw. So on any δ-far input the cheater is accepted with probability 1 (challenge-free — stronger than STIR's switch-prover bound), and sub-unit per-round rbr budgets w.r.t. the proximity relation are unachievable for this verifier. The existing small-field discharges (budgets ≥ 1) are consistent with this; any future claimed sub-unit discharge for the current `whirVerifyChecked` is fabricated by construction — this file is the fence.

**The honest path to the WHIR protocol-side milestone** (mirroring exactly how #301's was reached): upgrade the checked verifier with **input-binding oracle queries** — compare the input codeword against the first folded oracle at challenge-derived points (STIR's round-2 binding analogue; that one check is what made `stirEpsStar` sub-unit). Then the door-die port goes through verbatim: the binding flip bound is `1 − δ|ι₀|/|F|`, the sumcheck slots keep their SZ salvage bounds (`whir_salvage_*`, already landed), and `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound` discharges the genuine budget. Concrete next steps: (1) `whirVerifyCheckedBinding` = current checks ∧ input-vs-g₀ binding at the first folding challenge; (2) completeness (honest g₀ IS the fold of the input — the honest-prover plumbing exists); (3) the door-die predicate `close ∨ SurvivedW` with the binding conjunct playing STIR's round-2 role.


=== comment 117 (lalalune) ===
**Cross-post from #304 (the CA core this issue's Johnson MCA bound consumes):** the §6.2 interpolation route is now wired end-to-end into one composed theorem — `exists_bundle_pair_of_S10_converse` (`S10ToBundlePair.lean`, `e1f82a613`, axiom-clean): Claim-5.7 assignment data + per-good-z S10-converse divisibilities at `Q₀` + centre factorizations + ONE pigeonhole count + per-branch `BranchSupply` ⟹ the keystone bundle's terminal `(Ppoly, hrep, hdegX)` pair, with the ξ/separability places carved out internally by Bézout bounds (no per-z side conditions). Supporting verdicts that matter for this issue's MCA lane: the sharp Claim 5.9 is machine-refuted AND unnecessary (the loose graded budget + interpolation replaces it — see the K2/A5/K3 verdicts on #304); the trivariate `R.Separable` supply is a unit-discriminant condition, generically false — consumers should take the SLICED `MappedSliceSeparabilityOn` (producers in-tree, `38ea37538`). The remaining #304 inputs are exactly the S10-converse production this issue's lanes already own — once those land, `StrictCoeffPolysResidual` discharges and the Johnson-regime CA your `whirVectorIOP` soundness gate needs follows through the existing keystone front doors.

=== comment 118 (lalalune) ===
## The Johnson-MCA core 5+5 hypothesis map — the Hab25 §3 lane against the now-composed #304 chain

The open math here is sharply bounded: `mca_johnson_bound_CONJECTURE` (the Johnson-radius MCA for RS) via Hab25 §3's S4–S6 over `K = F(Z)`, with S2/S3 done. Since my #304 chain landed (`exists_bundle_pair_of_S10_converse` and the sliced/dependent-root welds, see cross-post above), the two lanes meet at the same GS/Hensel substrate. The map (constraints → why-nobody → larp-check → hypothesis):

### Known-math hypotheses
**K1 — the #304 chain IS S4–S6 (the unification bet, checkable today).** *Constraints:* Hab25 S4–S6 = interpolant factorisation + discriminant nonvanishing + Hensel uniqueness over `F(Z)`; the #304 lane has, axiom-clean: monic irreducible factorization (`PigeonholeFactorSupply`), discriminant counting (`DiscriminantBadSet`, `gradedConcreteFin_of_disc`), Hensel-root descent (`AssembledRootDescent`), per-z Hensel uniqueness (`localSeries_eq_aPTaylor_sliced`). *Why nobody:* the two lanes were built against different papers (BCIKS20 App.A vs Hab25 §3) and nobody has diffed the obligations. *Larp-check:* both papers formalize THE SAME Guruswami–Sudan + Hensel argument; the risk is convention mismatch (centred vs off-centre, `F(Z)` vs `F[Z]`-localization), not mathematical gap. *Hypothesis:* `mca_johnson_bound_CONJECTURE` discharges by a TRANSLATION layer from the #304 keystone front doors (`correlatedAgreement_affine_curves_of_matching_lane` / the per-`P` bundle) — no new Hensel mathematics; estimate: one adapter file. **Highest-value brick on this issue.**

**K2 — S5 discriminant nonvanishing from the sliced characterization.** My `TrivariateSeparabilityCharacterization` (`38ea37538`): separable-over-polynomial-base ⟺ unit discriminant; `discr_eq_nonzero_const_of_separable_polyBase`. *Hypothesis:* Hab25's S5 obligation is exactly the contrapositive composition of these with the in-tree `GSDiscriminantOverRatFunc` — the `F(Z)`-side discriminant nonvanishing needs only squarefreeness of the GS interpolant (which S4's factorisation provides), not separability. Mechanical once K1's translation exists.

**K3 — the `Λ`-window accounting transfers.** The Hab25 lane's S11/Z-degree budget (my #113-adjacent memory: `GSSquarefreePart` landed; frontier = hImprove weld + Z-degree budget) is the same weight calculus as #304's `betaRec_weight_le_graded`. *Hypothesis:* the Z-degree budget discharges by instantiating the graded collapse at Hab25's parameters — the `(2t+1)dD` loose shape suffices (the K3-audit pattern from #304: check consumers before chasing sharp constants).

**K4 — quotient-of-thresholds: Johnson-MCA from CA + the kernel count.** *Constraints:* `mca_rsc` (Cor 4.11) shape vs the in-tree `δ_ε_correlatedAgreementCurves`. *Larp-check:* the CA→MCA direction at fixed radius is folklore-cited but its formal loss factor is never written down. *Hypothesis:* `mca_rsc` follows from curve-CA with loss exactly `deg·|relevant pairs|/|F|` via the in-tree `TightRLCKernel`-style counting (the #329 kernel brick is code-agnostic and reusable here — DRY opportunity).

**K5 — the WHIR keystone needs LESS than full Johnson-MCA.** *Constraints:* `whirRbrKeystone_of_correlatedAgreement` consumes MCA at WHIR's specific fold arity and batch size. *Hypothesis:* at WHIR's parameters the keystone needs only the s=2 interleaved case, where `epsMCA_interleaved_eq` (exact, in-tree) + the Johnson list bound (in-tree) already close — i.e. the keystone may discharge BELOW the general conjecture. Audit `ChallengeCardPin` + the keystone's exact consumption before formalizing the general bound.

### Advanced hypotheses
**A1 — uniqueness-decoding WHIR:** re-parameterize the WHIR chain at δ inside unique decoding where the DG25 in-tree gap theorems are proven — a *weaker but unconditional* `whirVectorIOP_isSecureWithGap` instance today, as scaffolding for the Johnson one (no paper states the UD-regime WHIR security explicitly).
**A2 — the marked-curve transfer:** the #334 K5-lane's just-landed `GG25MarkedCurve` definitions give curve-decodability machinery; hypothesis: Hab25's S6 Hensel-unique-pairs step is an instance of marked-curve decodability at `a = 2` — unifying the two issues' deepest steps into one definition (falsified if the marked-point budget can't encode the Hensel branch count).
**A3 — generic-fold functor:** WHIR/STIR/FRI keystones all consume CA through fold-specific adapters; hypothesis: one `FoldCA` functor (lens-style, like #329's carried lenses) subsumes the three adapter families — a DRY/symmetry conjecture about the in-tree code, checkable by diffing the three keystone signatures.
**A4 — error-term symmetry:** the WHIR rbr error vector's MCA term and the #329-style kernel terms obey the same `max(...)/|F|` shape; hypothesis: there is a single "batched-round error" lemma from which both derive — would simplify the Whir security assembly and the eventual blueprint.
**A5 — adversarial completion:** the conjecture name `mca_johnson_bound_CONJECTURE` invites a disproof attempt at WHIR's exact parameters (smooth domains!): run the KKH26 bad-line construction at WHIR's `(ρ, fold)` choices; hypothesis: it does NOT reach below Johnson (the construction's radius exceeds `1−√ρ` only past the window edge) — a falsification probe that, if it FAILS, is a paper-grade finding about WHIR's parameter safety.

### Execution order
K5 audit (cheapest, possibly decisive) → K1 translation layer (the unification) → K2/K3 mechanical follow-ons → A5 probe. I'll take K5+K1 next session unless another lane claims them — per the owner's standing note, claimed ≠ exclusive.


=== comment 119 (lalalune) ===
## Session wrap (solo grind, full takeover): where #302 stands tonight

**Closed tonight, all axiom-clean and pushed**: the R-K portfolio (slack weld, unique rich factor, budget supply, rich-coordinate gate, fence) → **Seam A** (gate branch = Section-5 `hdvdR`) → witness-mass wiring (interpolant mass ⟹ rich factors via attribution pigeonhole) → Claim 5.8′ tail wiring → the hlin capstone → **Seam B** (the per-place agreement via Step-6 Hensel uniqueness) → **the grand composition** (`natDegree_eq_one_of_decoded_fold`: hlin from GS-side data only) → the WHIR obliviousness fence + the sliced-separability honesty patch (the agreement lane now takes `hsepZ` per-place, per the #304 verdict that trivariate `R.Separable` is generically false).

**The remaining surface of this issue, all assembly/known-math (no open mathematics)**:
1. **GS-run instantiation** of the grand composition: supply `w`/`hdvd` from Prop 5.5's actual output (`SectionFactor` lane), the heavy sets from Claim 5.11's count (`Hab25HeavyPoints` + `exists_rich_coordinates`), the fold readings from the cell definition, the `ξ`-weight bound from `BCoeffVanishing.xi_weight_le_of_coeff_bounds`, and the numerics — then `JohnsonNumericBound`/`mca_johnson_bound_CONJECTURE` discharge through the landed keystone front doors.
2. **Truncation-lane separability slicing** (mirror of tonight's agreement-lane patch, in `DecodedProximateRoot`).
3. **The WHIR protocol side**: the input-binding verifier upgrade (`whirVerifyCheckedBinding`) + the door-die port — fully spec'd in the obliviousness-fence comment; the current `whirVerifyChecked` is machine-checked-fenced against sub-unit claims.
4. (Shared infra) the rbr→soundness union-bound generic — gives this issue's fences their budget corollaries and was also #301's last named residue.

Cross-issue: **#301 is closed**; #320 verified ready-to-close twice (final stale-ref sweep clean after today's ~30 commits of churn).


=== comment 120 (lalalune) ===
## Close-out sweep: #320 and #301 are closed; #302's remaining surface after tonight's final bricks

**Closed**: #320 (blueprints — both audits clean, repair landed) and #301 (headline discharged; the maintainer closed it after the session's landings). This issue is the last of the three open.

**Two more bricks landed tonight**:
- **The fully-sliced grand composition** (`Claim510SlicedComposition.lean`, `3485e1c23`): the truncation lane is now sliced too — `natDegree_eq_one_of_decoded_fold_sliced` consumes only per-place specialized separability on the matching loci for BOTH lanes. The generically-false trivariate `R.Separable` is fully purged from the hlin gate; every separability input is now exactly the `MappedSliceSeparabilityOn` producer shape.
- **The rbr union-bound deterministic core** (`RbrKnowledgeFlip.lean`, `72e2f2f75`): `KnowledgeStateFunction.exists_challenge_flip_of_full` — a not-in-relation statement with the knowledge state true on the full realized transcript forces, at some challenge round, the EXACT `rbrKnowledgeSoundness` game event (the in-tree plain-`StateFunction` crossing, lifted through the `toStateFunction` projection with the extracted-witness bookkeeping). The probabilistic lift (prefix-marginalization of the full run against the per-round games + budget sum) is now the ONLY missing piece of the chain rule that gives this issue's obliviousness fence and #301's K4 fence their budget corollaries.

**#302's full remaining surface** (no open mathematics; all spec'd): the GS-run instantiation of the (sliced) grand composition; the WHIR input-binding verifier upgrade + door-die port; the union-bound probability lift; (cross-cutting) the t-point STIR soundness rerun for paper-budget Lemma 5.4. All landed work tonight: 16 commits, every theorem axiom-clean `[propext, Classical.choice, Quot.sound]`, zero sorries, all import-registered, all verified present on `fork/main` (including recovery from three concurrent-rebase commit drops and one rerere near-disaster that silently deleted 35 imports — restored and the trap defused).

