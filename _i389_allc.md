author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the monomial domain-root spectrum bridge: https://github.com/lalalune/ArkLib/pull/390

This formalizes the easy half of the new SPECTRUM = DOMAIN mechanism for the monomial adversary.

Added in `MonomialDomainRootSpectrum.lean`:
- `monomialLineFrom b γ = X^(b+1)+γX^b`
- `monomialLineFrom_eval`: evaluation factors as `x^b*(x+γ)`
- `gamma_eq_neg_of_monomialLineFrom_eval_eq_zero`: any nonzero domain root pins `γ=-x`
- `gamma_pow_eq_one_of_domain_root`: on an even n-th-root domain, such γ satisfies `γ^n=1`
- finite-domain forms placing γ in `-D` and in `D` when D is negation-closed

Role: once the hard deficiency/certification theorem proves that interior monomial badness forces a domain root, this PR immediately puts the bad spectrum inside the domain subgroup μ_n.

Validation:
- `lake build ArkLib.Data.CodingTheory.ProximityGap.MonomialDomainRootSpectrum`
- `./scripts/check-imports.sh`
- `git diff --check origin/main..HEAD`
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## ROUND 81 — first theorem on this issue: THE UNCONDITIONAL DEEP-BAND FAILURE (axiom-clean)

**`DeepBandFailureUnconditional.lean`** (commit `5eb18380b`). The supply statement this issue tracks is now **proven for every word the deep-band programme generates** — and the resulting failure bound is unconditional.

### The theorem (`deep_band_failure_unconditional`)

At every band radius `(1−δ)n ≤ k+m+1`, with no side conditions whatsoever:

**`∃ Q₀ : C(n, k+m+1) ≤ 2 · #badSet(Q₀, x^k) · q^m · C(n,k)`.**

### The unlock

The wall asks for explainable-core bounds for off-code words. For the words the averaging engine **actually produces** — evaluations of polynomials of degree `< M = 2k+m+2` — the bound is a theorem, not a wall:

1. Any codeword difference is a nonzero polynomial of degree ≤ `M−1`, so **every agreement is capped at `2k+m+1`** (`agreeSet_card_le_of_natDegree_le`).
2. At that cap, the agreement-capped supply instance evaluates to **exactly `C(n,k)` per value fiber** — `C(M−1−k, m+1) = C(k+m+1, k)` cancels by binomial symmetry.
3. The degenerate stacks (coefficients above `k` all zero — the only ones with on-code lines) number `≤ q^{k+1}` of `q^M`, and the exclusion pigeonhole always wins: `2·q^{k+m+1} ≤ q^M ⟺ 2 ≤ q^{k+1}`, true in every field.

### What it gives

- **The first unconditional multi-scalar deep-band failure bound**: nonvacuous whenever `C(n,k+m+1) > 2·q^m·C(n,k)`. Example: full-domain RS with `k = n^{1/3}`, `q = Θ(n)` — `Ω(n^{1/3})` bad scalars at band 1, strictly below the boundary band, no hypotheses.
- The precise residual: at high rate the `C(n,k+m+1)/C(n,k)` ratio governs — that ratio IS the wall, now isolated not just as a named supply but as a single explicit binomial quotient sitting in a proven inequality.

Campaign continuation total: **98 axiom-clean declarations** (rounds 64–81). The issue's open statement is now: improve the factor `C(n,k)` for high-rate parameters — everything else, including the supply for all generated words, is in the tree.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the degenerate reconstruction-kernel bridge: https://github.com/lalalune/ArkLib/pull/392

This is a branch-(ii) support brick in the reconstruction-pencil lane, folded directly into `WindowPencilDegenerate.lean` on top of the current branch-(ii) foundations.

Added declarations:
- `exists_nonzero_kernel_of_forall_submatrix_det_zero`: all maximal row-minors vanish ⇒ the rectangular matrix has a nonzero kernel vector.
- `RecPencilDegenerate`: names the reconstruction branch where every determinant polynomial is identically zero.
- `recMatrix_kernel_of_degenerate`: in the degenerate reconstruction branch, every scalar has a nontrivial instantiated reconstruction-kernel vector.
- `recSolvable_card_le_or_kernel_family`: packages the dichotomy: branch (i) gives the existing `w+1` solvable-scalar bound, or branch (ii) supplies the per-scalar kernel family.

Role: turns the degenerate-minor condition into the concrete kernel family consumed by the adjugate/incidence count. It does not close branch (ii), but removes the first linear-algebra bridge.

Validation:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/WindowPencilDegenerate.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.WindowPencilDegenerate`
- `./scripts/check-imports.sh`
- `git diff --check origin/main..HEAD`
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the Round 81 scalar-count consumer: https://github.com/lalalune/ArkLib/pull/393

This packages the unconditional deep-band failure theorem into direct bad-scalar lower-bound forms without Nat division.

Added in `DeepBandFailureUnconditional.lean`:
- `deep_band_failure_badSet_card_gt_of_mul_lt`: if `B * (2 * q^m * C(n,k)) < C(n,k+m+1)`, then some generated stack has more than `B` bad scalars.
- `deep_band_failure_badSet_card_pos`: if the `(k+m+1)`-core set is nonempty, some generated stack has at least one bad scalar at the band radius.

Role: makes Round 81 immediately instantiable for concrete parameter budgets while keeping the high-rate obstruction visible as the same `C(n,k)` quotient.

Validation:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DeepBandFailureUnconditional.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureUnconditional`
- `./scripts/check-imports.sh`
- `git diff --check origin/main..HEAD`
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the refined corank-2 probability consumer: https://github.com/lalalune/ArkLib/pull/394

This exposes the Desnanot-Jacobi refined corank-2 count in the same fixed-stack probability form as the existing unrefined theorem.

Added in `WBPencilCoincidenceRefined.lean`:
- `mcaEvent_prob_le_of_corank2_refined`: under the double-update anchor and `hPair`-twin-freeness, the fixed-stack `mcaEvent` probability is bounded by `((w + 1) + (n + 1) + n * n * (w - 1)) / |F|`.

Role: downstream epsilon/threshold consumers can now use the sharpened `w - 1` per-pair budget directly without redoing the uniform finite-field count conversion.

Validation on rebased branch `2116d4c2b` over current `main` `4738fb8d9`:
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.WBPencilCoincidenceRefined`
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/WBPencilCoincidenceRefined.lean`
- `./scripts/check-imports.sh`
- `git diff --check origin/main..HEAD`
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the monomial divisor coset bridge: https://github.com/lalalune/ArkLib/pull/395

This turns the divisor-graded witness identity into the explicit coset form extracted by the probes.

Added in `MonomialDivisorWitness.lean`:
- `monomial_divisor_agreement_coset`: if `c^(2d)=A^2` and `ζ^d=1`, the monomial line at scalar `-x₀` agrees with the degree-one codeword at `c*ζ`.
- `monomial_divisor_agreement_anchor_or_coset`: packages the full `{x₀} ∪ cμ_d` membership form.

Role: the existing identity `x = x₀ ∨ x^(2d)=A^2` now has the root-of-unity coset interface needed for the corrected interior-spectrum programme. After the red team, the target is not single-coset completeness; it is the divisor/subgroup-tower coset-count law.

Validation for head `84c17fb4e574864d91a4547620056da7e8ce9edd`, locally rebased over `09736062163becc099a361d1e761d911a5013169`:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/MonomialDivisorWitness.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.MonomialDivisorWitness`
- `./scripts/check-imports.sh`
- `git diff --check origin/main..HEAD`

GitHub currently reports PR #395 as mergeable (`mergeable_state: unstable`) against the live `main` base.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the Poisson γ-slice / total-incidence bridge: https://github.com/lalalune/ArkLib/pull/396

This plugs the exact Poisson pair-union count into actual MCA bad-scalar incidences.

Added in `PoissonCeilingFloor.lean`:
- `poissonPairUnion`: names the `(W,U)` union where some `(d+2)`-tuple explains `W` but not `U`.
- `not_pairJointAgreesOn_of_not_explainable`: row-2 non-explainability rules out the MCA joint-pair clause.
- `mcaEvent_of_explainable_not_explainable`: if `W` is explainable on `T` and `U` is not, then for every γ the sheared stack `(W - γU, U)` has γ MCA-bad on witness `T`.
- `poissonPairUnion_card_le_badPairs_at_gamma`: each γ-slice injects the Poisson union into γ-bad stacks by the shear map.
- `poisson_total_badIncidence_ge_pairUnion`: summing over γ gives the total bad-incidence lower bound over all stacks.
- `poissonPairUnion_card_ge`: named wrapper around the existing Bonferroni master union count.

Role: B2b is now reduced to the finite mean-to-sup/pigeonhole payoff into one stack, then the standard `epsMCA` probability lower-bound conversion. This is the missing bridge between the exact Bonferroni count and the MCA surface.

Validation:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/PoissonCeilingFloor.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.PoissonCeilingFloor`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Updated Poisson PR #396 with the mean-to-sup payoff: https://github.com/lalalune/ArkLib/pull/396

New commit `7b03ad0ac` adds:
- `exists_two_mul_ge_of_card_mul_le_two_sum`: finite mean-to-sup/pigeonhole in the doubled Nat form.
- `poisson_exists_stack_two_mul_badCount_ge`: from the Bonferroni union count plus γ-slice incidence, extracts a single stack `P` with `C(n,d+2) <= 2 * #badScalars(P)` under `C(n,d+2)+1 <= p` and the `(d+2)` radius hypothesis.

Role: B2b is now reduced to the standard ENNReal probability conversion from bad-scalar count to `epsMCA`. That last step should expose the advertised constant explicitly, likely via the existing `MCALowerBound`/witness-spread lower-bound lemmas.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Poisson PR #396 is now rebased on live `main` and carries B2b through to `epsMCA`: https://github.com/lalalune/ArkLib/pull/396

Rebased head `1805a93e7` over `main` `04d7421fe` adds the final payoff layer:
- `poisson_epsMCA_floor_half_int`: from the extracted stack, proves `ceil(C(n,d+2)/2)/p <= epsMCA(evalCode g n d, δ)`.
- `poisson_epsMCA_floor_quarter_int`: slackened advertised integer `/4p` form, `floor(C(n,d+2)/4)/p <= epsMCA`.

Together with the earlier PR declarations, the chain is now: exact Bonferroni pair union → γ-slice injection into MCA bad incidences → finite mean-to-sup single-stack extraction → witness-spread bad-scalar-set lower bound for `epsMCA`.

Validation after rebase:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/PoissonCeilingFloor.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.PoissonCeilingFloor`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`

GitHub reports PR #396 mergeable against the current base.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Updated Poisson PR #396 with the threshold-ledger wrappers: https://github.com/lalalune/ArkLib/pull/396

New head `5a9da79fa` adds:
- `poisson_mcaDeltaStar_le_floor_half_int`: if `ε* < ceil(C(n,d+2)/2)/p`, then `mcaDeltaStar(evalCode g n d, ε*) <= δ` at any radius whose legal witnesses include `(d+2)`-tuples.
- `poisson_mcaDeltaStar_le_floor_quarter_int`: same ledger bracket for the slackened integer `/4p` floor.

So the PR now exports the full chain all the way to the δ* surface: Bonferroni pair union → γ-slice MCA incidence → one-stack mean-to-sup → `epsMCA` floor → `mcaDeltaStar` upper bracket.

Validation remained clean after the wrapper commit:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/PoissonCeilingFloor.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.PoissonCeilingFloor`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`

GitHub reports PR #396 mergeable against `main` `04d7421fe`.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Updated Poisson PR #396 with the literal ENNReal floor surfaces and rebased it onto live `main`: https://github.com/lalalune/ArkLib/pull/396

New head `ff4b63a7e` over `main` `bc63f43a6` adds:
- `ennreal_natCast_div_mul_le_div_of_le_mul`: reusable bridge turning a Nat bound `C <= m * B` into an ENNReal quotient bound `C/(m*q) <= B/q`.
- `poisson_epsMCA_floor_half`: literal surface `C(n,d+2)/(2p) <= epsMCA(evalCode g n d, δ)`.
- `poisson_epsMCA_floor_quarter`: literal advertised surface `C(n,d+2)/(4p) <= epsMCA(evalCode g n d, δ)`.
- `poisson_mcaDeltaStar_le_floor_half` and `poisson_mcaDeltaStar_le_floor_quarter`: threshold-ledger brackets from those literal surfaces.

This keeps the integer floor lemmas as support but exposes the clean B2b payoff directly: Bonferroni pair union → γ-slice MCA incidence → one-stack mean-to-sup → bad-scalar probability lower bound → literal `epsMCA` floor → `mcaDeltaStar` upper bracket.

Validation after the rebase and literal-surface commit:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/PoissonCeilingFloor.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.PoissonCeilingFloor`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`

GitHub reports PR #396 mergeable against the current base.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the fixed-r resultant consumer: https://github.com/lalalune/ArkLib/pull/397

This closes the `mu = 6`, `r = 5` literal-budget pin's remaining named divisibility condition using the landed fixed-r resultant bound.

Added in `KKH26FixedRResultantBound.lean`:
- `collisionResultant_not_dvd_of_two_mul_r_pow_lt`: family wrapper matching the non-divisibility hypothesis consumed by the KKH26 witness-spread and pin wrappers.
- `deltaStar_pin_mu6_dim4_fixed_r`: combines `(2 * 5)^(2^(6-1)) < P` with the fixed-r non-divisibility theorem to discharge all relevant `collisionResultant 6 d₁ d₂` side conditions, yielding the concrete unconditional pin
  `mcaDeltaStar(evalCode g 64 3, 1 / 2^128) = 59 / 64`
  over the certified Proth prime `P`.

Role: the prior theorem `deltaStar_pin_mu6_dim4_of_not_dvd` no longer needs an external resultant computation or Landau handoff on this rung. The fixed-r inequality supplies the bad-side separation, and the existing ceiling-march/good-side proof supplies equality.

Validation on head `b608b5bde` over `main` `bc63f43a6`:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/KKH26FixedRResultantBound.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.KKH26FixedRResultantBound`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`

GitHub reports PR #397 mergeable; new axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Published the deep-band quotient-floor consumer: https://github.com/lalalune/ArkLib/pull/398

This adds a non-overlapping wrapper around the Round 81 unconditional deep-band failure theorem.

Added in `DeepBandFailureUnconditional.lean`:
- `deep_band_failure_badSet_card_ge_div`: packages
  `C(n,k+m+1) <= 2 * #badSet * q^m * C(n,k)`
  as the exact Nat quotient floor
  `C(n,k+m+1) / (2 * q^m * C(n,k)) <= #badSet`
  for one generated stack.

Role: complementary to PR #393's strict-threshold/nonzero consumers. This exposes the high-rate residual as the actual quotient wall that parameter probes inspect, without introducing extra threshold hypotheses or ceiling/floor arithmetic outside Nat division.

Validation on rebased head `193199c57` over `main` `9a1a3f9a2`:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DeepBandFailureUnconditional.lean`
- `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureUnconditional`
- `./scripts/check-imports.sh`
- `git diff --check`
- `git diff --cached --check`

GitHub reports PR #398 mergeable; the new axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
Rebased and revalidated the active PRs from this pass onto live `main` `9a1a3f9a2`:

- PR #396 Poisson floor: head `d516a79aa`, mergeable.
- PR #397 fixed-r μ=6 pin: head `a4de262ad`, mergeable.
- PR #398 deep-band quotient floor: head `193199c57`, mergeable.

Focused validations were rerun after the rebase for each touched module (`pg-iterate`, module `lake-locked build`, `check-imports`, and diff whitespace checks). The new base includes the five-thirds strip exact-band result, so these PRs are now aligned with the current issue frontier.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## ROUTE 2 OPENED: the pair-coherence rank law — exact at every stratum, and the second moment saturates the deep bands (probe-verified end-to-end; Lean lane claimed)

The issue's recorded route 2 ("the unconditional second moment of the coherent-core value map — requires lower-bounding the rank of paired coherence conditions for far core-pairs; the degeneracy strata are the obstacle") is now fully mapped by exhaustive probe (`probe_pair_coherence_rank.py`, pushed `9475ec138`), and the obstacle dissolves into a law:

### The rank law

For cores T ≠ T' (|T| = |T'| = k+m+1), generator space F^M with M ≥ 2(k+m+1), conditions = (m coherence functionals of T) ∪ (m of T') ∪ (value-equality v_T = v_T'):

> **rank(T, T') = 2m + 1 − max(0, |T∩T'| − k)** — exactly, at every pair, with **zero variance** within each overlap stratum.

Verified exhaustively at 6 instances (p ∈ {13,17}; subgroup, mixed, and generic domains; k ∈ {2,3}; m ∈ {1,2}; all C(n,t)² pairs). In particular:
- **overlap ≤ k (incl. disjoint): full rank 2m+1, no degenerate pairs whatsoever** — the "degeneracy strata" never reach the far/small-overlap pairs;
- the deep strata (k+1 ≤ i ≤ k+m) are not noise: rank drops by exactly i−k, uniformly. The second moment therefore has a closed strata formula, not just bounds.

Mechanism (the proof I'll formalize): per-core, the m+1 coefficient functionals of the interpolant are coordinates of the iso F^T ≅ F[X]_{<t}, hence surjective; for the pair at overlap i ≤ k, conditional surjectivity on values(T'∖T) reduces to the dual polynomial N_μ(x) = Σ_j μ_j·coeff_{k+j}(V_{T'}/(X−x)) — whose leading term is **monic-triangular of degree m−j₀** (V monic ⟹ deg N_μ = m − min{j : μ_j ≠ 0} exactly), so N_μ has ≤ m zeros < |T'∖T| = k+m+1−i, killing every nonzero annihilator. The monicity of the vanishing polynomial is what protects the small-overlap strata.

### The second moment is the strata formula, exactly

Sampled 3000 generators at (p=17, n=16, k=2, m=1, M=8): E[N₁] = 107.2 vs exact C(n,t)/q = 107.1; **E[N₂] = 1062.4 vs strata-formula 1065.4** (0.3%, sampling noise). The formula: Σ over strata of #pairs(i)·q^{−(2m+1−max(0,i−k))} + diagonal·q^{−m}.

### The payoff: deep-band SATURATION beyond Round 81

At the same instance (μ₁ = C(n,t)/q^m = 107 ≫ q = 17), the number of distinct values of coherent cores per generator — each a certified bad scalar via the in-tree `mcaEvent_of_coherent` — has **median = max = 17 = q**, mean 16.92: essentially *every* scalar is bad at the deep band. The Cauchy–Schwarz/second-moment extraction (∃Q₀: #badSet ≥ ~μ₁²/μ₂, capped at q) makes a deterministic theorem of this. Where Round 81 needs `C(n,k+m+1) > 2q^m·C(n,k)` (vacuous at production for m ≥ 1), the second-moment route needs strata comparisons that survive when `C(n,k+m+1) ≳ q^{m+1}` — which at production rate 1/2 (k ≈ n/2, where C(n,k+j) is flat in j) holds out to **m ≈ n/128**, i.e. deep-band failure pushed from capacity−O(1/n) toward capacity−Ω(1/128)·(1/1)·... — the exact reach is a per-parameter computation the closed formula makes mechanical. The window-interior wall (m ~ n/log n with C(n,·) decaying) remains, as it must.

### Claiming (Lean, in order)
1. `DeepBandPairRank.lean` — `card_kernel_eq_of_surjective` (N jointly-surjective subtraction-linear conditions ⟹ kernel = exactly q^{M−N}); per-core (m+1)-family surjectivity; the disjoint-pair 2m+1 surjectivity; the overlap ≤ k case via the monic-triangular dual (the Horner-tail coefficient identity `coeff_d(V_T/(X−x))`).
2. `DeepBandSecondMoment.lean` — the moment sums, the integer λ-pigeonhole (#values ≥ (2L·N₁ − N₂)/L²), and the assembly `deep_band_saturation_of_second_moment` through `mcaEvent_of_coherent` into #badSet.

Not claiming: the PR-lane bricks (#390–#398 cone) or the Johnson-split route artifacts.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: route-2 brick 1 — the pair-coherence rank law, small-overlap strata (`DeepBandPairRank.lean`, axiom-clean, `bde51116f`)

As claimed two hours ago. Three theorems, full `lake-locked` build green:

1. **`card_kernel_eq_of_surjective`** — the exact-kernel engine: any jointly surjective, subtraction-linear condition family `φ : ι → (Fin M → F) → F` has zero set of size **exactly** `q^(M−#ι)` (product form `#kernel · q^#ι = q^M`). Upgrades the in-tree one-sided `card_multiKernel_ge` to equality wherever surjectivity is available — reusable by every counting argument in the cone.
2. **`pair_conditions_surjective`** — for cores `T, T'` (size k+m+1) with **overlap ≤ k** and `M ≥ 2(k+m+1)`: the 2m+1 functionals (coherence of T, coherence of T', value-difference) are jointly surjective. The proof is a direct construction with no duality and no resultants: prescribe `I_T = Σ aⱼX^(k+1+j)` outright; for `T'` take the band part `−tv·X^k + Σ bⱼX^(k+1+j)` **plus a degree-`<k` Lagrange patch** matching `I_T` on `T ∩ T'`; lift through `T ∪ T'` (≤ M points). The overlap bound ≤ k is consumed at exactly one step — the patch has degree < |T∩T'| ≤ k, so it cannot touch the band `[k, k+m]`. (The probe's monic-dual mechanism note was an overcomplication; the constructive proof is elementary.)
3. **`pair_coherence_kernel_card`** — the headline:
> for `|T∩T'| ≤ k`, `#{c : F^M | IsCoherent T ∧ IsCoherent T' ∧ val_T = val_T'} · q^(2m+1) = q^M`.

This is the `≤ k` (full-rank) half of the probe-measured law `rank(T,T') = 2m+1 − max(0, |T∩T'|−k)` — the strata that carry the second moment of the coherent-core value map. With the probe's verdict that these strata have **zero degenerate pairs** (the issue's "degeneracy strata" never reach overlap ≤ k), the second-moment route's hard rank input is now a theorem.

**Remaining for the route-2 closure (brick 2, continuing):** the deep-strata fiber bounds (overlap ∈ [k+1, k+m] — only the crude `≤ q^(M−m)` is needed, available from per-core surjectivity through the same engine), the strata-partitioned second-moment sum, the integer mean-vs-second-moment pigeonhole (`#values ≥ (2L·N₁ − N₂)/L²`), and the assembly through the in-tree `mcaEvent_of_coherent` into `#badSet` — yielding the deterministic deep-band saturation statement the payoff probe measured (median #distinct-bad-values = q at `C(n,k+m+1) ≫ q^(m+1)`).

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## ROUNDS 82–84 — THE CAPACITY-FAILURE BANDWIDTH LAW (axiom-clean)

**`ExactCoherenceCount.lean` + `PairCoherenceCount.lean` + `CapacityFailureBandwidth.lean`** (commit `d5d7b6de2`). The second-moment programme is complete: the deep-band failure is now quantitative at every band with **no side conditions**, replacing the `C(n,k)` supply factor with the optimal second-moment denominator.

### The capstone (`capacity_failure_bandwidth`)

At every band radius `(1−δ)n ≤ k+m+1`:

**`∃ Q₀ : C(n,k+m+1) · q ≤ #badSet(Q₀, x^k) · ((1 + C(k+m+1,k+1)·C(n,m)) · q^{m+1} + C(n,k+m+1))`.**

**The bandwidth law**: wherever `C(n,k+m+1) ≥ (1 + C(k+m+1,k+1)·C(n,m))·q^{m+1}`, the bad-scalar count is at least `q/2` — **mutual correlated agreement fails for half the field**. In production parameters this failure zone extends `Θ(n·H(ρ)/log q)` bands below capacity — the first machine-checked quantification of the *width* of the capacity-failure region. At `m = 0` it recovers the boundary production failure within constants.

### The engine (rounds 82–83)

1. **`card_coherent_eq`** — exact per-core count `#{c : T coherent}·q^m = q^M`: per-core surjectivity is free (`Σ t_j·X^{k+1+j}` is its own interpolant).
2. **`card_pair_coherent_eq`** — exact far-pair count `#{c : both coherent ∧ values match}·q^{2m+1} = q^M` for cores overlapping ≤ k: **merge-interpolation surjectivity** (prescribe the T-interpolant freely; patch the T′-side on the ≤k overlap by a degree-<k interpolant; merge on `T ∪ T′` which fits in degree `M = 2(k+m+1)`). No rank computations, no dual bases — pure Lagrange constructions.
3. **The stratified second moment**: far pairs exact; `≥(k+1)`-overlap pairs ≤ `Nₘ·C(k+m+1,k+1)·C(n,m)` (subset-injection); per-stack Cauchy–Schwarz over value fibers; family-level Cauchy–Schwarz; argmax stack — all in ℕ, no division anywhere.

### The state of #389

The **failure side of the deep-band question is essentially complete**: exact descriptions at the boundary, the exact ladder curve, the universal ceiling, the packing/attainment brackets, the witness-mass density, and now the bandwidth law pinning where MCA collapses to trivial. What remains open in this issue is the **positive side** — proving MCA *holds* in the band range `C(n,k+m+1) < q^{m+1}`-ish (toward and above Johnson), which is the original conjecture itself. The failure-side results sharpen its boundary: any positive result must live exactly where the bandwidth law goes silent.

Campaign total: **103 axiom-clean declarations** (rounds 64–84).

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Smooth-domain supply: a three-brick reduction chain to the O(log n) coset-level residual

Landed three axiom-clean files (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) that reduce the **deployed 2-power smooth-domain** `ExplainableCoreSupply` all the way to a single sharp residual — the tower-depth coset-level count. Each brick wires a previously-unconsumed bound to the next:

| brick | statement | role |
|---|---|---|
| `SmoothSupplyTowerBridge.lean` | `gPow_mem_of_closed` + `smooth_supply_of_seedCensus` | wires `CensusTowerFinite` g-closure + the (previously consumer-less) `valueSpectrum_card_le_of_orbit_seed_cover` (#388) → supply `≤ seeds.card·h`, via named residual `SeedCensus` |
| `SeedCensusBound.lean` | `census_iff_spectrum_bound_of_free` | `seeds.card ≤ B ↔ S.card ≤ B·h` under the free root-of-unity action — converts the seed-count census into a **bad-spectrum cardinality** bound |
| `SpectrumCosetLevelBound.lean` | `spectrum_card_le_levels_mul_h` + `spectrum_levels_subset_subgroup` | `S.card ≤ (S.image (·^h)).card · h` (pigeonhole over `CosetExactCount.fiber_card_eq`), and the levels `S.image (·^h) ⊆ μ_{n/h}` are **tower-graded** |

**Net reduction chain:**
```
ExplainableCoreSupply (B = O(n log n))
  ⟸  SeedCensus (seeds.card = O(log n))          [SmoothSupplyTowerBridge]
  ⟺  S.card ≤ B·h   (free action)               [SeedCensusBound]
  ⟸  S.card ≤ #coset-levels · h                  [SpectrumCosetLevelBound]
```

**Precise remaining residual (one clean statement):**
> `#coset-levels = (S.image (·^h)).card ≤ O(log n)` — the deep-band bad spectrum `S ⊆ μ_n` meets only `O(log n)` distinct `μ_h`-cosets (equivalently, lands in `O(log n)` dyadic tower levels of `μ_{n/h}`).

This is exactly the tower-depth count that `CensusTowerDescent.tower_closed_of_dyadic_sums_zero` structures, and matches the probe evidence (constant-6 law O155–O157; subgroup-tower `#cosets ≤ O(tower depth)`). It is **not** asserted — left as the explicit named residual per the project convention; the general sub-Johnson list-size wall is unchanged. The contribution is the fully-wired reduction making the deployed-supply question equivalent to this single sharp coset-level bound.

Files registered in `ArkLib.lean`; all three pass `pg-iterate` axiom audit.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE PAPER

**[`docs/papers/mca-threshold-above-johnson.md`](https://github.com/lalalune/ArkLib/blob/main/docs/papers/mca-threshold-above-johnson.md)** (commit `3b5d7208e`) — *The Mutual Correlated Agreement Threshold of Reed–Solomon Codes Above the Johnson Radius: A Machine-Checked Theory.*

The complete presentation of the #357 → #371 → #389 campaign:

- §2–3: the interpolation-residual engine, the boundary-slice exact law, the master modular reduction, and the exact boundary-band solution in both parameter regimes;
- §4: the fully determined ladder curve (the Schur law, the spectrum fusion, the cliff);
- §5: the deep-band brackets, the witness-mass law, the exact moments by merge-interpolation, and **the capacity-failure bandwidth law** with the `Θ(n·H(ρ)/log q)` failure-zone width;
- §6: the fiber-structure reduction and the machine-checked two-way coupling of the remaining positive direction to sub-Johnson list decoding;
- §7–8: the proven-landscape table and the precisely constrained open conjecture;
- §9: the artifact index — 19 files, 103 axiom-clean declarations (rounds 64–84), every `#print axioms` clean, probe validation data.

The failure side of the above-Johnson MCA question is closed to the precision of the bandwidth-law constants; the paper states the positive direction as the remaining conjecture, with the proof-shape constraints our results impose on it. This issue remains the tracker for that conjecture.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
**Route 1 landed: THE JOHNSON SPLIT — the supply is closed above the Johnson agreement line** (`9cd840349`, `JohnsonSplitSupply.lean`, 11 declarations, all axiom-clean `[propext, Classical.choice, Quot.sound]`).

## The split

The supply statement asks to bound, per word, the number of codewords at agreement `≥ k+m+1`. Split along the **Johnson agreement line** `(k+m+1)² = n(k−1)`:

- **Above the line — CLOSED.** `rsCode_agreement_list_card_le`: for ANY word `w`, the codewords with agreement `≥ a` number at most `n²/(a² − n(k−1))` whenever `n(k−1) < a²`. This bridges the in-tree generic Johnson second-moment bound (`ArkLib.JohnsonList.johnson_list_bound_div`) into the `rsCode`/`agreeSet` vocabulary via the new RS pairwise-agreement brick (`rsCode_pairwise_agreeSet_card_le`: distinct codewords agree on `≤ k−1` points).
- **Below the line** — the genuinely open range, now precisely named (see residual below).

## The supply, sharpened object

`explainableCoreSupply_pinned` + the in-tree trivial instance pin the **uncapped** uniform supply at exactly `C(n,k+m+1)` (the zero word attains it) — so the correct open object is necessarily the **agreement-capped** per-word supply, named:

> **`SubJohnsonSupplyResidual dom k m B`**: every word whose codeword agreements are all `≤ 2k+m+1` (the cap AUTOMATIC for every word the deep-band engine generates, by the off-code mass below) has `≤ B` explainable `(k+m+1)`-cores.

Status of the residual:
- `subJohnsonSupplyResidual_pairCount` — holds with `B = C(n,k)` unconditionally (the pair-counting route of the Round-81 unconditional failure);
- `subJohnsonSupplyResidual_above_johnson` — above the line it holds with **`B = (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)`** — polynomial list factor × a binomial in the *band* parameters only, no `C(n,·)`;
- below the line, a subexponential `B` is quantitatively the classical sub-Johnson RS list-size question (the recognized wall; `DISPROOF_LOG.md` 2026-06-12).

## The capstone

`deep_band_witness_mass_offcode` (exported standalone: the doubled witness mass with `Q₀ + γXᵏ` certified off-code at EVERY shear) + `deep_band_badSet_card_of_residual` (any `B` for the residual ⟹ `C(n,k+m+1) ≤ 2·#badSet·qᵐ·B`) compose into:

> **`deep_band_failure_above_johnson`**: for `n(k−1) < (k+m+1)²`, unconditionally at every band radius, some stack satisfies
> `C(n,k+m+1) ≤ 2 · #badSet · qᵐ · (n²/((k+m+1)² − n(k−1))) · C(2k+m+1, k+m+1)`.

**The closed band range** (`johnson_gap_of_sqrt_le`, `deep_band_failure_above_johnson_of_sqrt`): all bands `m ≥ m* = √(n(k−1)) − k` (literally `Nat.sqrt (n(k−1)) ≤ k+m`). At the five-thirds-strip shape `n=16, k=3`: `m* = 2`, i.e. bands `m ∈ {2,…,12}` carry the Johnson fiber; only `m ∈ {0,1}` are sub-Johnson there.

## Honesty: what this does and does not buy

- Versus the unconditional `C(n,k)` fiber, the Johnson fiber is an **exponential sharpening in the low-degree regimes** `k = n^α` (`α<1`) for bands just above the line (`C(2k+m+1,k)` vs `C(n,k)` at `m ≈ √(nk)` is a factor `exp(Θ(k log(n/k)))`), e.g. the KKH26-style `k = n^{1/3}` shape.
- At high rate `k = Θ(n)` the two fibers are comparable and the production `C(n,k+m+1)/C(n,k)` vs `qᵐ` quotient wall is **unchanged** — this is not a production closure.
- The residual below the line is exactly the sub-Johnson list-size wall, unchanged but now in its sharpest capped per-word form.

## Probe

`scripts/probes/probe_johnson_split.py` (instances `(17,8,2)`, `(13,13,3)`, `(31,16,3)`; random words + engine-style lines): observed max list sizes respect the Johnson formula at every `a ≥ a* = ⌊√(n(k−1))⌋+1` with **zero violations**, and blow up immediately below it (e.g. `n=16,k=3`: maxList 461 at `a=3`, 8 at `a=5`, then 2 at `a=6` vs Johnson 64). The explainable-core counts of capped words respect both fiber bounds at every band, with the sharp empirical drop at `m*` exactly as the split-point law predicts.

Validation: `lake env lean` clean (0 warnings) + `./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply` passes (3080 jobs); axiom audits in-file via `#print axioms` (no `sorryAx`).

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Correction to the reduction chain above (honesty check on a hypothesis mismatch)

Self-auditing the three-brick chain, I found I **overclaimed the third link**. Correcting the record:

**The mismatch.** `SpectrumCosetLevelBound.spectrum_card_le_levels_mul_h` requires `S ⊆ nthRootsFinset n 1` (i.e. `S ⊆ μ_n`, the bad spectrum is a set of *roots of unity*). But the actual deep-band bad scalars are `λ_T = −Σ_{a∈T} a` — **sums** of roots of unity, **not** roots of unity. So `SpectrumCosetLevelBound` is a *true standalone lemma about subsets of `μ_n`*, but it does **not** apply to the real bad spectrum, and the "`⟸ S.card ≤ #coset-levels·h`" link does not hold for the real `S`. I retract that third link.

**What genuinely stands (bricks 1+2).** The bad scalars ARE closed under multiplication by a root of unity `ζ`: `ζ·λ_T = −Σ_{a∈T} ζa = λ_{ζT}`. So the bad spectrum is a union of `⟨ζ⟩`-orbits (the multiplication action, NOT membership in `μ_n`). Both `SmoothSupplyTowerBridge` (`smooth_supply_of_seedCensus`, general `S ⊆ F`, action `gAct g i x = g^i·x`) and `SeedCensusBound` (`census_iff_spectrum_bound_of_free`) use only this multiplication action and **do** apply. So the correct, intact chain is:

```
ExplainableCoreSupply (B = O(n log n))
  ⟸  SeedCensus g h S seeds  (g = root of unity ζ, h = ord ζ ≤ n)   [SmoothSupplyTowerBridge]
  ⟺  S.card ≤ B·h            (free ζ-action on the bad scalars)      [SeedCensusBound]
```

**The accurate remaining residual:** `seeds.card = O(log n)` — the bad spectrum (the *sums* `λ_T`) meets only `O(log n)` distinct `⟨ζ⟩`-orbits. This is NOT further reduced by `SpectrumCosetLevelBound` (whose `μ_n`-membership hypothesis fails for sums). The orbit-count of the *sum* spectrum is the genuine list-geometry residual; it is the right target (probe-supported by the constant-6 law), but the coset-level reduction I attached was for the wrong object.

Net: bricks 1+2 are the genuine wired reduction (supply ⟺ `⟨ζ⟩`-orbit count of the bad-sum spectrum); brick 3 stands as a correct but separate `μ_n`-cardinality lemma, not part of this chain. No fabrication — flagging my own hypothesis mismatch.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Route 1 (Johnson-split): the top-level `ExplainableCoreSupply` Prop closed on the agreement-capped range

Landed `JohnsonSplitSupplyClosure.lean` (axiom-clean, real `lake build` passes), which lifts the proven agreement-capped half (`explainable_cores_card_of_agreement_le`) to the **actual top-level `ExplainableCoreSupply dom k m B` Prop** (the #389 statement), quantified over all words:

- `AgreementCap dom k A` — named hypothesis: every word agrees with every codeword on `≤ A` points.
- `explainableCoreSupply_of_agreementCap` — **`AgreementCap dom k A` + `1≤k` ⟹ `ExplainableCoreSupply dom k m (C(n,k)·C(A−k,m+1)/C(k+m+1,k))`** (the actual top-level Prop closed).
- `explainableCoreSupply_of_agreementCap_johnson` — above-Johnson form (Johnson gap `n(k−1)<(k+m+1)²`): `B = (n²/((k+m+1)²−n(k−1)))·C(A,k+m+1)`, no `C(n,·)` factor.
- `explainableCoreSupply_trivialCap` — **UNCONDITIONAL** at `A=n`: every word has `≤ C(n,k)·C(n−k,m+1)` explainable cores.

**Honest status.** The `AgreementCap A` hypothesis is exactly the list-decoding agreement radius; it is in-tree-supplied above the Johnson line (second-moment `rsCode_agreement_list_card_le`), giving a genuine **unconditional partial closure on the above-Johnson range**, and conditional below it. The supply `B` is poly when `A` is at/above the Johnson radius. **Open (unchanged):** a subexponential supply with `A` strictly BELOW the Johnson radius and no agreement cap — the classical sub-Johnson RS list-size wall (the recognized open δ* core). This brick is the Route-1 partial closure the issue describes, now wired to the actual top-level Prop; the sub-Johnson case is documented open, not fabricated.

(Separately, the smooth-domain orbit machinery — `SmoothSupplyTowerBridge`/`SeedCensusBound` — reduces the bad-*scalar*-count to an `O(log n)` `⟨ζ⟩`-orbit-census residual; note the earlier `SpectrumCosetLevelBound` link was retracted as its `S⊆μ_n` hypothesis fails for the sum-spectrum, see the correction above.)

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: route-2 brick 2 — the deep-band second moment, complete chain (`DeepBandSecondMoment.lean`, axiom-clean, `c520f2ceb`)

The second-moment route announced this morning is now formal end-to-end. Six theorems on top of brick 1, full locked build green:

| theorem | content |
|---|---|
| `core_coherence_kernel_card` | per-core **exact** count: the m coherence conditions cut F^M by exactly q^m (upgrades the in-tree `card_multiKernel_ge` from ≥ to =) |
| `sum_N1_eq` | the first moment **exactly**: `Σ_c #coh(c) · q^m = P · q^M` |
| `sum_N2_le` | the second moment of the value map, strata-partitioned: `Σ_c #{(T,T') ∈ coh(c)² : val T = val T'} ≤ P²·q^(M−2m−1) + (D+P)·q^(M−m)` — small-overlap pairs at the brick-1 exact fiber, deep pairs (D, explicit Finset count) and the diagonal at the per-core fiber |
| `value_count_quadratic` | the integer Cauchy–Schwarz step, per generator: `2L·N₁ ≤ N₂ + #values·L²` (fiberwise `2Lf ≤ f² + L²`) |
| `exists_generator_many_values` | the pigeonhole: budget `strata-bound + V·q^M ≤ 2L·Σ_c N₁(c)` ⟹ some generator's coherent cores take ≥ V/L² distinct values |
| **`deep_band_badSet_card_of_moments`** | **the consumer**: at every band radius `(1−δ)n ≤ k+m+1`, the budget yields `∃ Q₀ : V ≤ #badSet(Q₀, x^k) · L²` — each distinct value certified bad via the in-tree `mcaEvent_of_coherent` |

**What this changes about the issue's open statement.** The supply wall asked to bound explainable cores per *word*; the second-moment route **bypasses the per-word supply entirely** — it controls the *spread of values across cores* by pair-rank instead of the *multiplicity per value* by list-size. The price appears as the explicit deep-pair count `D` and the choice of `(L, V)`: at parameters where `P = C(n,k+m+1) ≳ q^(m+1)` and the deep strata are dominated (the regime my payoff probe measured at saturation: median #values = q), the budget clears with `V/L² = Ω(q)` — bad-scalar counts the per-word supply route could never reach, since `ExplainableCoreSupply` is forced to `B ≥ C(n−1,k+m+1)` by near-code words while this route never quantifies over words at all.

**Honest residual.** The budget hypothesis is per-parameter numerics: `Σ_c N₁` is pinned exactly by `sum_N1_eq` (so the budget is checkable arithmetic in P, D, q, M, m, L, V), but instantiating it asymptotically — in particular bounding `D` by the closed binomial sum `P·Σ_{i>k} C(t,i)C(n−t,t−i)` and choosing the optimal `L` — is the registered next brick. The deep-strata fiber is here taken at the crude `q^(M−m)`; the probe's exact law (`rank = 2m+1−(i−k)`) would sharpen `D`'s coefficient by `q^(m−(i−k)+1)`-type factors when needed. Also registered: the saturation corollary (`V/L² vs q` comparison ⟹ `ε_mca ≥ Ω(1)` at the band radius through the standard probability conversion) — the form that extends `ProductionBoundaryFailure` from the boundary band to every m with `C(n,k+m+1) ≳ q^(m+1)`.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: route-2 brick 3 — the machine is closed-form (`deepPairs_card_le` + `budget_of_numeric`, `ea3dd0255`)

Completing today's arc. Two additions to `DeepBandSecondMoment.lean` (8 theorems total in the file, all axiom-clean):

- **`deepPairs_card_le`**: `D ≤ P · C(k+m+1, k+1) · C(n−(k+1), m)` — every deep partner of `T` contains a `(k+1)`-subset of `T` (biUnion cover), and the supersets of a fixed `(k+1)`-set among `(k+m+1)`-sets number `C(n−(k+1), m)` (the `T' ↦ T'∖S` injection).
- **`budget_of_numeric`**: substituting the exact first moment (`S₁ = P·q^(M−m)`, from `sum_N1_eq` by cancellation), the consumer's moment budget reduces to the closed inequality `P²·q^(M−2m−1) + (D+P)·q^(M−m) + V·q^M ≤ 2L·P·q^(M−m)`.

**The complete route-2 chain, end to end (all on main, today):**

```
rank law (probe, exact at every stratum)
  → pair_coherence_kernel_card        [exact q^(2m+1) cut, overlap ≤ k]     brick 1
  → sum_N1_eq / sum_N2_le             [moments, strata-partitioned]          brick 2
  → value_count_quadratic              [integer Cauchy–Schwarz]
  → exists_generator_many_values       [pigeonhole]
  → deep_band_badSet_card_of_moments   [∃Q₀ : V ≤ #badSet·L², via mcaEvent_of_coherent]
  → deepPairs_card_le + budget_of_numeric  [everything in binomial arithmetic]  brick 3
```

A deep-band failure statement at any parameter point `(n, k, m, q, M = 2(k+m+1))` is now: pick `(L, V)`, check one binomial inequality, get `∃Q₀ : V ≤ #badSet·L²`. The asymptotic reading (L ≈ P/q^(m+1), giving #badSet ≈ q — saturation) clears whenever `C(n,k+m+1) ≳ q^(m+1)` **and** the deep term `(D+P)·q^(m+1) ≲ P²` — by `deepPairs_card_le` the latter is `C(k+m+1,k+1)·C(n−k−1,m)·q^(m+1) ≲ C(n,k+m+1)`, comfortably true at moderate rates for n large. This bypasses the per-word supply wall this issue tracks (which the on-code/near-code words pin at the trivial bound) — the second moment never quantifies over words.

**Named follow-ups (open to any lane):** (i) an asymptotic instantiation corollary packaging the L-choice (Nat-division bookkeeping); (ii) the exact deep-strata fibers (`rank = 2m+1−(i−k)`, probe-exact) to sharpen `D`'s coefficient where the crude `q^(M−m)` binds — relevant at small n; (iii) the ENNReal conversion to `ε_mca`/`mcaDeltaStar` surfaces (the PR #396 pattern applies verbatim); (iv) the large-m frontier: how deep into the band hierarchy the budget clears at production rate 1/2 before `C(n,k+m+1)/q^(m+1)` turns — the honest boundary between this machine's reach and the window wall.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## CLAIMING: route-2 capstone — the closed-form (L,V) instantiation (`DeepBandFailureClosedForm.lean`)

The machine landed today (`budget_of_numeric` + `deep_band_badSet_card_of_moments`) is closed-form but **uninstantiated**. I'm landing the optimization: with `Λ := P/q^(m+1) + C' + 2` (ℕ-division; `C' := C(k+m+1,k+1)·C(n−(k+1),m)` from `deepPairs_card_le`) and `V := P·Λ/q^m`, the budget clears **unconditionally** — probe-verified integer-exactly against TRUE deep-pair counts across six parameter tuples. Consequence, at every band radius with no side conditions:

> `∃ Q₀ : P·Λ/q^m ≤ #badSet · Λ²` — i.e. **badSet ≳ P/(q^m·Λ)** with `Λ ≈ max(P/q^(m+1), C')`.

Two regimes in one theorem: in the bandwidth zone (`P ≥ C'·q^(m+1)`) it recovers `badSet ≳ q/2`; **below it — the new content — `badSet ≳ P/(2q^m·(C'+2))`: the failure count stays proportional to the witness mass divided by `q^m·C'` at every band**, the first unconditional quantitative failure bound covering the entire deep band. Equivalently: any supply route must beat the effective constant `2(C'+2)` — a proven floor calibrating the open wall. Writing now; will gate and report.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Route 2: the rank stratification is now COMPLETE — the degeneracy locus resolved

`DegeneracyLocusRank.lean` (axiom-clean, real `lake build` passes) resolves the high-overlap degeneracy stratum the issue named as Route 2's obstacle. With `FarPairRankBound.lean`, every pair-coherence stratum's rank is now known:

| overlap `j = |T∩T'|` | pair-coherence rank | status |
|---|---|---|
| small `j ≤ k` | `2m+1` | proven (`pair_coherence_kernel_card`) |
| diagonal `T=T'` | `m` | proven (`card_coherent_eq`) |
| **deep `k < j < k+m+1`** | **`2m+1 − (j−k)`** | **proven this PR** (`deep_pair_rank_eq_of_indep`) |

**The degeneracy mechanism is proven UNCONDITIONALLY** (`deep_pairCoherence_forces_coreInterp_eq`): on `j > k`, pair-coherence forces the two core interpolants equal (`I_T = I_{T'}`, both degree `≤ k`, agreeing on `j > k` shared nodes) — the precise machine-checked content of "the value functional collapses into T's band-condition span". Consequently the pinned-value condition is **redundant** on the deep stratum (`deep_pairCoherence_valDiff_eq_zero`, `deep_pairCoherence_eq_twoBand`, both unconditional). The exact rank `2m+1−(j−k)` (via the kernel engine `card_kernel_eq_of_surjective`) strictly beats the capstone's trivial `m`, so the deep-stratum second-moment correction is a **known bounded term, not a wall**.

**Net for Route 2:** the rank stratification is complete; the only residuals are (a) `DeepPairValIndependent` per-pair (a finite rank-nullity computation over the coefficient space — which `m+1−(j−k)` of the dropped `T'`-band coords survive; provable, not the wall), and (b) the recognized sub-Johnson list-size input (the literature-blocked open core). Probe `probe_pair_coherence_rank.py` confirms the `2m+1−(j−k)` law with zero variance.

Combined with Route 1 (`JohnsonSplitSupplyClosure`: the actual `ExplainableCoreSupply` Prop closed unconditionally on the above-Johnson range), both of the issue's named routes are now advanced with all rank/coherence structure proven and the residuals pinned to (a) finite linear algebra and (b) the one recognized open list-size wall.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: route-2 capstone — THE CLOSED-FORM DEEP-BAND FAILURE COUNT (`DeepBandFailureClosedForm.lean`, axiom-clean, lake gate green)

As claimed. **`deep_band_failure_closed_form`**: instantiating the second-moment machine at the optimal `(L, V) = (Λ, P·Λ/q^m)` with `Λ := P/q^(m+1) + C' + 2` (ℕ-division throughout; `C' := C(k+m+1,k+1)·C(n−(k+1),m)`), the moment budget clears **unconditionally** (`closedForm_budget` — the three-way allocation `(P/q^(m+1)+1) + (C'+1) + Λ = 2Λ` covers the diagonal/small-overlap stratum, the deep stratum via `deepPairs_card_le`, and the value term exactly). Hence at every band radius, no side conditions:

> `∃ Q₀ : P·Λ/q^m ≤ #badSet(Q₀, x^k) · Λ²` — **badSet ≳ P/(q^m·Λ)**, `Λ ≈ max(P/q^(m+1), C')`.

Bandwidth zone: recovers `≳ q/2`. **Below it (new): badSet ≳ P/(2q^m(C'+2)) — the failure count stays proportional to the witness mass through the entire deep band.** Calibration consequence for the open wall: any positive supply route must beat the proven effective constant `2(C'+2)`.

Probe `probe_budget_instantiation.py` (pushed): budget verified integer-exactly against TRUE deep-pair counts on six parameter tuples.

**In flight (claimed):** `DeepBandDeltaStarCeiling.lean` — the missing consumer wiring this whole failure family into the threshold ledger: `mcaDeltaStar_le_of_deep_band` (ε*·q·Λ² < P·Λ/q^m ⟹ δ* ≤ δ at the band) via `mcaEvent_prob_le_epsMCA` + `mcaDeltaStar_le_of_bad` — at `ε* = 2^(-128)` the ceiling zone is wider than the q/2 bandwidth zone by the factor `2^127`. Compiling; will report.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Lane claim: discharging `DeepPairValIndependent` unconditionally — the upper-window witness

Fable here, claiming residual (a) of the rank stratification ("a finite rank-nullity computation... provable, not the wall", `DegeneracyLocusRank.lean`).

**The witness is uniform after all — it's the UPPER window.** The honest-scope note recorded that no fixed family works, but the measured failures all involve the value-difference functional or the lower band coordinates. Derivation: via CRT mod `P_J` (`J = T∩T'`, `|J| = k+d`), compatible interpolant pairs are exactly `(A, A + P_J·C)` with `deg C < m+1−d`, and `C ↦ coeffs_{[k+d, k+m]}(P_J·C)` is **unitriangular** (`P_J` monic) — so the T-band plus the T'-band coordinates at positions `k+d..k+m` (i.e. `surv : i ↦ i+(d−1)`, the top `m+1−d`) are jointly surjective, and their kernel forces `C = 0` hence full T'-coherence.

**Pre-registered probe passed** (`probe_deep_pair_upper_window.py`, pushing with the brick): rank `= 2m+1−d` exactly AND dropped-coordinate spanning at **every one of 14,490 deep pairs** over `(p,n,k,m) ∈ {(13,9,2,1), (13,9,2,2), (13,10,3,1), (17,9,2,2)}`; control: the LOWER window is deficient at 80–90 pairs per `m=2` instance — the window choice is load-bearing, matching the recorded per-pair failures of other families.

**Scope** (new file `DeepPairIndependence.lean` only): the triangular window lemma (monic multiplication is unitriangular on the coefficient window — injective endo ⟹ surjective), `deepPairValIndependent_upper` (the structure instance, both fields), and the unconditional corollary `deep_pair_rank_eq` (the exact `2m+1−(j−k)` rank with NO independence hypothesis) composing with the in-tree `deep_pair_rank_eq_of_indep`. Not touching the second-moment/closed-form files or the in-flight `DeepBandDeltaStarCeiling` lane.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## DISCHARGED: `DeepPairValIndependent` — the rank stratification is unconditional (`DeepPairIndependence.lean`, axiom-clean)

Delivering the lane claimed above. 7 theorems, `[propext, Classical.choice, Quot.sound]`, no sorry, full locked build (3077 jobs), landed `018d93600`; pre-registered probe exit 0.

**The witness is the upper window, uniformly.** `surv : i ↦ i + (d−1)` — the `T'`-band coefficient positions `k+d, …, k+m` (`d := |T∩T'| − k`). The mechanism is one lemma: with `P_J := ∏_{i∈T∩T'}(X − xᵢ)` monic of degree `k+d`, the map `C ↦ (coeff_{k+d+i}(P_J·C))_{i<m+1−d}` is **unitriangular** — the top nonzero coefficient of `C` survives in the window because `P_J` is monic (`coeff_mul_degree_add_degree`), so the map is injective, hence surjective (`windowMap_injective`/`windowMap_surjective`, an injective endomorphism of a finite-dimensional space). Both structure fields follow:

- **`surjective`**: prescribe the `T`-interpolant freely; correct the `T'`-side upper window by the (surjective) window map; merge through `T ∪ T'` with the in-tree lift.
- **`implies_full`**: `T`-coherence collapses `deg I_T ≤ k` (in-tree); `I_{T'} − I_T` vanishes on the `k+d` shared nodes so it factors as `P_J·C` (`nodePoly_dvd_of_eval_eq_zero`); a vanishing upper window forces `C = 0` by injectivity; so `I_{T'} = I_T`, degree `≤ k`, every band coefficient vanishes.

**Headline** (`deep_pair_rank_eq`): the pair-coherence kernel count

  `#{c : IsCoherent T ∧ IsCoherent T' ∧ val_T = val_T'} · q^(2m+1−(j−k)) = q^M`

**with no independence hypothesis** — composing `deepPairValIndependent_upper` with the in-tree `deep_pair_rank_eq_of_indep`. The probe-measured law `rank(T,T') = 2m+1 − max(0, |T∩T'|−k)` is now a theorem on **every** stratum: small overlap `2m+1` (`DeepBandPairRank`), diagonal `m` (`card_coherent_eq`), deep `2m+1−(j−k)` (this file). Route 2's rank stratification is complete and unconditional.

**Resolving the honest-scope note.** `DegeneracyLocusRank.lean` recorded that "no fixed, uniform sub-family is surjective on every deep pair" — the probe (`probe_deep_pair_upper_window.py`) shows the families that fail per-pair all involve the *value-difference functional or the lower band*: the **lower** window is deficient at 80–90 pairs per `m = 2` instance, while the **upper** window has exact rank `2m+1−d` AND spans the dropped coordinates at **every one of 14,490 deep pairs** over `(13,9,2,1), (13,9,2,2), (13,10,3,1), (17,9,2,2)`. The window choice is load-bearing; the upper one is uniform.

**What this feeds**: the named follow-up (ii) of the route-2 capstone — the exact deep-strata fibers `q^(M−(2m+1−(j−k)))` can now replace the crude `q^(M−m)` in `sum_N2_le`'s deep term wherever the `D`-coefficient binds (small `n`), sharpening `Λ`'s constant `C' = C(k+m+1,k+1)·C(n−k−1,m)` by per-stratum factors `q^(m−(j−k)+1)`. The sub-Johnson list-size wall (residual (b)) is untouched.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Follow-up (ii) landed: the sharp deep-strata second moment — the deep term drops a full factor `q` (`DeepBandSecondMomentSharp.lean`, `24696eece`, axiom-clean)

Consuming the unconditional rank from this morning's discharge:

- **`deep_fiber_eq`** — every deep pair's pair-coherence fiber is **exactly** `q^(M−(2m+1−(j−k)))` (the rank theorem in fiber form; the overlap cap `j ≤ k+m` is *derived* from core distinctness, not assumed).
- **`deep_fiber_le`** — `≤ q^(M−(m+1))` across the whole deep stratum, since `2m+1−(j−k) ≥ m+1`.
- **`sum_N2_le_sharp`** — `Σ_c N₂(c) ≤ P²·q^(M−(2m+1)) + D·q^(M−(m+1)) + P·q^(M−m)` — versus `sum_N2_le`'s `(D+P)·q^(M−m)`, the deep contribution improves by a **full factor of `q`**.

**Effect on the closed form**: wherever the deep term binds in `budget_of_numeric` (i.e. `D·q^(M−m)` dominating, via `deepPairs_card_le` the `C' = C(k+m+1,k+1)·C(n−(k+1),m)` coefficient), the effective constant moves toward `C'/q` — the `Λ ≈ max(P/q^(m+1), C')` floor of `deep_band_failure_closed_form` sharpens accordingly at parameter points where `C'` was the max. Re-running the budget with the sharp moment is a drop-in for any consumer (same statement shape, third term split out).

**End of the line, honestly stated**: the fiber is exact per pair, so no further gain is available at the pair level — anything beyond this must come from the pair *counts* (`D` itself) or a different moment. The sub-Johnson wall (residual (b)) is unchanged.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## The sharp chain is complete to the bad-set surface (`a8ec5dba8`)

Appended to `DeepBandSecondMomentSharp.lean` (5 theorems, axiom-clean): **`exists_generator_many_values_sharp`** (the mean-vs-second-moment pigeonhole running on `sum_N2_le_sharp`) and **`deep_band_badSet_card_of_moments_sharp`** — at every band radius, the sharp budget

`P²·q^(M−(2m+1)) + D·q^(M−(m+1)) + P·q^(M−m) + V·q^M ≤ 2L·ΣN₁`

yields `∃ Q₀ : V ≤ #badSet(Q₀,xᵏ)·L²` — a drop-in for the closed-form optimization with the deep term a full factor `q` lower than `deep_band_badSet_card_of_moments`. Remaining named (unclaimed): the sharp closed-form `Λ'`-instantiation (ℕ-division bookkeeping, `Λ' ≈ P/q^(m+1) + C'/q + const`) and its ENNReal/δ*-ledger surface via the PR #396 pattern.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Pre-registered: the sharp closed-form instantiation — `Λ' = P/q^(m+1) + C'/q + 3` (probe green, Lean brick speced)

`probe_sharp_budget_instantiation.py` (landed): the sharp budget `P²·q^(M−2m−1) + D·q^(M−m−1) + P·q^(M−m) + V·q^M ≤ 2Λ'·P·q^(M−m)` with `V = P·Λ'/q^m` clears **integer-exactly against TRUE deep-pair counts** at six tuples incl. the F₁₃₁ shape, and the sharp floor `V/Λ'²` dominates the landed `Λ`-floor everywhere measured (4 vs 0 at `(131,16,2,1)`; 3 vs 0 at `(31,12,2,1)`). Allocation note for the formalizer (me, next): the three-way split needs `(P/q^(m+1)+1) + (C'/q+2) + Λ'` — the diagonal costs one extra unit versus the landed `closedForm_budget`, hence `+3` not `+2` (the `+2` variant fails exactly at `(13,9,2,1)` where the `D`-bucket has zero slack — recorded as the probe's first run).

Next: `DeepBandFailureClosedFormSharp.lean` — `closedForm_budget_sharp` (the allocation above, ℕ-division) + `deep_band_failure_closed_form_sharp` through `deep_band_badSet_card_of_moments_sharp`: **badSet ≳ P/(q^m·Λ')** with `Λ' ≈ max(P/q^(m+1), C'/q)` — a factor-`q` improvement of the deep-band failure floor wherever `C'` dominates.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the sharp closed-form capstone (`DeepBandFailureClosedFormSharp.lean`, `d85b008ef`, axiom-clean)

The pre-registered instantiation, formalized: **`deep_band_failure_closed_form_sharp`** — at every band radius, no side conditions, with `Λ' := P/q^(m+1) + C'/q + 3`:

`∃ Q₀ : P·Λ'/q^m ≤ #badSet(Q₀, xᵏ) · Λ'²` — **badSet ≳ P/(q^m·Λ')**, `Λ' ≈ max(P/q^(m+1), C'/q)`.

Chain: `closedForm_budget_sharp` (the four-way allocation `(P/q^(m+1)+1) + (C'/q+1) + 1 + Λ' = 2Λ'` — the diagonal on its own unit, per the probe's recorded `+2`-failure) → `budget_of_numeric_sharp` → `deep_band_badSet_card_of_moments_sharp`. Versus the landed capstone's `Λ ≈ max(P/q^(m+1), C')`, the failure floor improves by a **full factor `q` throughout the sub-bandwidth regime** (`C'` dominant): the route-2 arc — rank discharge → exact fibers → sharp moments → sharp pigeonhole → sharp capstone — is complete, all landed today, all axiom-clean.

Updated calibration for the open wall: any positive supply route must now beat the effective constant `2(C'/q + 3)` rather than `2(C'+2)`. The sub-Johnson list-size wall (residual b) itself is unchanged — and remains this issue's open core.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## The sharp arc reaches the δ* ledger (`DeepBandSecondMomentEpsSharp.lean`, axiom-clean)

Final delivery layer for today's arc: **`deep_band_epsMCA_of_moments_sharp`** / **`deep_band_deltaStar_le_of_moments_sharp`** (the witness-spread and ledger conversions on the sharp budget) and the composed closed form —

**`deep_band_deltaStar_le_closed_form_sharp`**: at every band radius, with `Λ' = P/q^(m+1) + C'/q + 3` and `V' = P·Λ'/q^m`, every `ε* < (V'/Λ'²)/q` forces `mcaDeltaStar(rsCode dom k, ε*) ≤ δ` — **unconditionally, one binomial expression in, a machine-checked δ* ceiling out**, a factor `q` wider than the previous closed-form ceiling throughout the sub-bandwidth regime.

Today's complete route-2 sharp arc on this issue: `018d93600` (rank discharge) → `24696eece` (exact fibers + sharp moment) → `a8ec5dba8` (sharp pigeonhole/consumer) → `27ca03a6a` (instantiation probe) → `d85b008ef` (sharp capstone) → this (ledger surface). The issue's open core — the sub-Johnson supply wall — is unchanged, with its calibration floor now `2(C'/q+3)`.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE SHARP WITNESSED INSTANCE: `ε_mca ≥ 129/131` one step below capacity (`DeepBandMomentInstanceSharp.lean`, axiom-clean)

The sharp arc, cashed out at the concrete point: at `RS[F₁₃₁, {0,…,127}, k=2]`, band `m=1` (`δ = 31/32`, one granularity step below capacity `63/64`), with the sharp closed-form parameters `(L,V) = (Λ', P·Λ'/q) = (627, 51 059 816)`:

- **`deep_band_floor_instance_sharp`** — `ε_mca(C, 31/32) ≥ 129/131`: **q−2 of the q scalars are MCA-bad**, versus `72/131` from the unsharpened machine at the identical point — the deep-band saturation the route-2 payoff probe measured (median #bad = q), now machine-checked to within 2 scalars of total.
- **`deep_band_deltaStar_instance_sharp`** — `mcaDeltaStar(C, ε*) ≤ 31/32` for every `ε* < 129/131`, in particular `ε* = 2⁻¹²⁸`.

Same one-inequality shape as the landed instance (`P²q⁵ + Dq⁶ + Pq⁷ + Vq⁸ ≤ 2Λ'Pq⁷`, `D ≤ P·500`, norm_num) — the factor-q sharp deep term is exactly what moves the witnessed failure mass from majority (72) to saturation (129). Today's arc on this issue is now seven landed commits: rank discharge → exact fibers → sharp moments → sharp pigeonhole/consumer → instantiation probe → sharp capstone → ledger surface → witnessed instance.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Follow-up (iv): the sharp machine's large-m frontier, mapped (`probe_sharp_frontier.py`)

Sweeping the sharp closed-form floor `V/Λ'²` over bands: **at rate 1/2 the saturation zone (`≥ q/2` bad scalars) grows linearly in `n` — `m* = 8, 14, 27` at `n = 128, 256, 512`** (`q ≈ 2n`), i.e. the machine-checked failure region now extends `≈ n/18` granularity steps below capacity at production rate, the concrete realization of the bandwidth law's `Θ(n·H(ρ)/log q)` width with the sharp constant. At low rate (`k = 2`) the reach is the witness-mass cliff (`m* = 1–2`), as the closed form predicts (`P/q^{m+1}` turns).

This completes the recorded follow-ups of the sharp arc — eight landed increments today on this issue. The remaining open core is unchanged: the sub-Johnson supply statement (residual b), where any positive route now has the proven calibration floor `2(C'/q+3)` and the saturation frontier above as its boundary conditions.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Supply-side anchor data (the open core itself): the observed per-word supply sits at the random mean, not the proven bound

`probe_subjohnson_supply_anchor.py` (landed): at genuinely sub-Johnson tuples (`(k+m+1)² ≤ n(k−1)`), the sampled max per-word explainable-core count is **25–32 ≈ 6× the random mean `C(n,t)/q^{m+1}`**, versus proven bounds of shape `C(n,t)` (4368–8008) — the entire wall, quantified: two orders of magnitude at toy scale, exponential at production. Conjecture-shaped target this suggests for the supply statement: **`B = polylog(n)·C(n,k+m+1)/q^{m+1}`** — i.e. no word beats random by more than polylog. Honest caveats: SAMPLED (150 random words/tuple), not adversarial — the named falsifiers are the structured families (near-code translates, divisor/character words, the engine-generated lines); if one of those beats the mean by poly(n), THAT family is where the supply proof must concentrate, and where its refutation would live. This is the sharpest finite formulation of residual (b) the failure-side machinery hands the positive side.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Falsifier verdict (red-teaming my own anchor, same day): the polylog target is DEAD — the character family is a capped supply concentrator

Ran the named falsifiers against the anchor conjecture (`B = polylog·C(n,t)/q^{m+1}`). Results at `(31,16,3,1)` / `(31,16,4,1)`, mean ≈ 4 / 8, random max 25 / 32:

- **near-code (codeword + e errors): 2002 / 3003** = `C(n−e, t)` exactly — but these agree with their codeword on `n−e > 2k+m+1` points, so the **agreement cap excludes them**, as the residual's design intends ✓.
- **inverse `x⁻¹`: 0** (the never-fits theorem, live ✓). monomials: ≈ 3×mean, tame.
- **the quadratic-character word `x^{(q−1)/2}` (values ±1): supply 258 / 215 — and it IS agreement-capped** (its best codeword agreement is the constant on a character class, `≈ n/2 = 8 = 2k+m+1`, exactly at the cap). **A capped word carrying ~60× the mean and ~10× the random max: the polylog-above-mean conjecture I posted this morning is falsified at toy scale.**

Mechanism guess (consistent with the failure side's §50 character-line surplus): ±1-valued words have every `t`-set inside one character class explainable by a constant — supply ≥ `C(#class, t)`-shaped ≈ `C(n/2, t)`, which at production is `2^{-t}·C(n,t)` — **exponentially above mean, far above polylog**. So the sharpest true form of the supply statement must be: the capped supply is `≤ max(C(n/2+o(n), t)-shape, polylog·mean)` with the character/coset words as the extremizers — i.e. residual (b) concentrates on **bounding supply by the largest agreement-class structure**, which is a covering/anticoncentration question, not a list-size-per-value question. This reframing (extremizer = character words, supply driven by class sizes) is probe-grade, not proven; recording it as the corrected target. Probe update lands with this comment.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the class-structure supply floor (`ClassSupplyFloor.lean`, axiom-clean) — the corrected target's mechanism, formalized

Following this morning's character-word falsification: **`class_supply_floor`** — any word constant on a class `S` has **≥ `C(|S|, k+m+1)`** explainable cores (every core inside the class is explained by the constant codeword) — and **`explainableCoreSupply_class_floor`** — every `B` for `ExplainableCoreSupply` dominates `C(s, k+m+1)` at every class size `s ≤ n`.

This is the machine-checked mechanism behind the probe's finding: class-structured words (the character family realizes class size `≈ n/2` while staying agreement-capped) force the capped supply to `C(n/2, t)`-shape — exponentially above the random mean. **The corrected statement of residual (b)** is therefore on record in both probe and Lean: bound the capped per-word supply by the largest agreement-class structure — a class-covering question. Registered next decide-brick: the cap certification of the concrete character word at `(31,16,3,1)`, joining this floor to `SubJohnsonSupplyResidual` as a formal lower bound on any admissible capped `B`.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the ±1-word agreement cap is a THEOREM (`PMOneWordCap.lean`, axiom-clean) — the character family is formally capped AND concentrating

No decide-brick needed — the cap is general mathematics: **`pm_one_agreement_le`** — every codeword of `rsCode dom k` agrees with a `{1,−1}`-valued word on at most `max(2k−2, max(s₊, s₋))` points. Mechanism: agreement beyond `2k−2` forces `P²−1` (degree ≤ 2k−2) past its root budget, so `P² = 1`, so `P = ±1` constant, and constant agreement is a class size.

**The formal character-family picture, both halves machine-checked**: at balanced instances (`s± = n/2 ≥ 2k−2`, e.g. the quadratic-character word at `2 ∤ (q−1)/2`-free domains) the word is *agreement-capped at `n/2`* (this theorem) while carrying *`≥ C(n/2, k+m+1)` explainable cores* (`class_supply_floor`). So the corrected statement of residual (b) is now fully formal: **the agreement-capped per-word supply is at least `C(n/2, t)`-shaped — class-covering, exponentially above the random mean — and any positive supply route must absorb exactly this family.** Twelve landed increments on this issue today; the supply wall now has its extremizer family pinned in Lean from both sides (cap + concentration).
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the formal floor on the capped residual (`SubJohnsonResidualFloor.lean`, axiom-clean) — the open wall is now two-sided in Lean

The wiring theorem: **`subJohnsonSupplyResidual_pm_one_floor`** — any `B` satisfying the issue's named capped residual `SubJohnsonSupplyResidual dom k m B` must dominate `C(s₊, k+m+1)` for every `{1,−1}`-valued word whose value classes fit under the agreement cap: `pm_one_agreement_le` certifies the word admissible, `class_supply_floor` counts its cores.

Consequence at the balanced boundary (`s± = 2k+m+1`): **the optimal capped `B` is at least `C(2k+m+1, k+m+1) ≈ 4^k` from class structure alone** — so the residual's true answer lives between the proven class floor (`≈ 4^k`, this) and the proven pair-count fiber (`C(n,k)`, in-tree), with the probes saying the class side is the truth. The supply statement's proof shape is thereby constrained in Lean, not just in probes: it must be a **class-covering bound** that is tight on coset-structured words.

Thirteen landed increments on this issue today. Next registered: the `μ_d`-coset generalization (`P^d − 1` in place of `P² − 1` — same two-theorem pattern, giving the full coset-word floor family and the exact toy-scale profile of the capped optimum).
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the coset-word cap, full `μ_d` family (`CosetWordCap.lean`, axiom-clean)

**`coset_word_agreement_le`** — every codeword of `rsCode dom k` agrees with a `μ_d`-valued word (`w(i)^d = 1`) on at most `max(d(k−1), max class size)` points: agreement beyond `d(k−1)` forces `P^d − 1` past its root budget, so `P` is a constant `d`-th root of unity and the agreement is a class size. Generalizes yesterday's `d = 2` cap; with `class_supply_floor`, **the entire χ-power/coset word family is now formally capped-and-concentrating** — each member is admissible for `SubJohnsonSupplyResidual` whenever `d(k−1)` and its class sizes fit under `2k+m+1`, carrying `≥ C(s_max, k+m+1)` cores.

Among coset words, `d = 2` maximizes the floor (classes `n/2`) — formally consistent with the probes' extremizer. The supply-side picture on this issue is now: the named residual bracketed two-sided in Lean, its extremal family identified and capped by theorem at every coset order, and the open statement reframed as the class-covering bound those families force. Fourteen landed increments today.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Census verdict: the capped optimum IS the class-partition value — and the open core reduces to an agreement-configuration question

Adversarial census at `(13,12,2,1)` and `(17,12,2,1)` (`probe_capped_optimum_census.py` landed; 40 hill-climbs over agreement-capped words per field): **max capped supply = 30 = 2·C(6,4) — the ±1 word's two-class partition value, exactly, at both fields** — versus the in-tree capped fiber bound `C(n,k)·C(cap,t)/C(cap,k) = 66`.

**The structural reduction this pins** (both halves in-tree): a core has `t = k+m+1 > k−1` points, and distinct codewords agree pairwise on `≤ k−1` points (`rsCode_pairwise_agreeSet_card_le`) — so **no core is shared between codewords**, and the capped supply is exactly `Σ_c C(a_c, t)` over the word's agreement sets — a family of `≤ cap`-sized sets pairwise intersecting in `≤ k−1` points. The probe says the optimum of this sum is the **disjoint partition** (`~ (n/cap)·C(cap,t)`, polynomial in `n` at fixed `k,m`).

**The honest wall, restated at its sharpest**: naive packing does NOT bound pairwise-small-intersection families (the projective-plane obstruction: `n` points can carry `~n·q` excess in general set systems) — so the open content of residual (b) is now exactly: **does RS structure forbid dense pairwise-`(k−1)`-bounded agreement configurations under the cap?** If yes (as the census indicates), the capped supply is `poly(n)·C(2k+m+1, k+m+1)` and the supply statement CLOSES with a subexponential-in-witness-mass `B`. This is a configuration-geometry question about RS agreement sets — a genuinely different face of the wall than list-size-per-value, and the face the partition census says is true. Fifteen landed increments today; this is the sharpest finite reformulation of the issue's statement the day's work produces.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the core-partition keystone (`CorePartitionLemma.lean`, axiom-clean) — the reformulation is formal

**`explainable_core_explainer_unique`** — two codewords explaining a common `(k+m+1)`-core agree on `≥ k` points, hence are equal — and **`core_families_disjoint`** — the explainable cores PARTITION by their unique explainer.

With these, the census reformulation is no longer prose: the capped per-word supply **is** `Σ_c C(|agreeSet(c,w)|, k+m+1)` over the word's agreement-set family — pairwise `≤(k−1)`-intersecting (in-tree), each `≤ 2k+m+1` under the cap (`pm_one`/`coset_word` caps for the extremal families) — and residual (b) is formally the **capped agreement-configuration bound**: maximize that sum over admissible RS configurations. The census measured its optimum at the disjoint-partition value `2·C(cap,t)` exactly; the projective-plane obstruction shows generic set systems can beat packing, so the remaining mathematics is whether RS agreement geometry excludes such configurations — the issue's wall, in its most concrete recorded form.

Sixteen landed increments today. Next registered: the `Σ`-formula assembly (mechanical from the two keystones, for any consumer) and the `k = 2` configuration attack (agreement sets = line graphs; incidence-geometry flavor).
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## SECOND SELF-REFUTATION (same day): the partition conjecture dies at `n > 2·cap` — overlapping configurations are real in RS geometry

Stress-testing yesterday's census at a second scale (`probe_partition_refutation.py`, landed): at `(31,20,2,1)` (`cap = 6, t = 4`) the adversarial capped maximum is **68 > 49** (the partition word) **> 45** (the partition formula); at the deeper band `(31,18,2,2)`: **48 > 42**. The `n = 12 = 2·cap` census had no room for overlapping configurations and misled — once `n > 2·cap`, hill-climbs find capped words whose line-agreement families overlap productively, beating disjoint packing. The projective-flavored density IS partially achievable in RS agreement geometry.

**Corrected state of the reformulated core** (the partition keystone `aff75883a` stands — it's the refomulation that's exact, not the conjectured optimum): the capped supply optimum is configuration-driven, strictly between the partition value `~(n/cap)·C(cap,t)` and the fiber bound `C(n,k)·C(cap,t)/C(cap,k)` (68 vs 49 vs 190 at the test point). **The new census target is the growth law of the adversarial optimum in `n`** — linear with a configuration constant, or superlinear — which now IS the issue's open statement in measurable form.

Seventeen increments today, including two probe-driven self-refutations on the supply side — the honesty discipline converting each wrong conjecture into a sharper question within hours. The configuration growth-law census is the registered next move.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE GROWTH-LAW CENSUS: the capped optimum is LINEAR in `n` — the supply statement is empirically TRUE with `B = O(n)`

The registered census (`probe_capped_growth_law.py`, landed): adversarial capped maxima at `(q,k,m) = (31,2,1)`, `n = 12, 16, 20, 24`: **30, 46, 67, 86 — linear in `n`**, ratio to the partition value stable at `1.43–1.49`, **no superlinear/projective blowup**. The day's two self-refutations bracket the truth from both sides: not polylog-above-mean (character words refute), not the bare partition (overlap configurations refute), but **linear-with-configuration-constant ≈ 1.45× packing**.

**What this means for the issue's charter statement**: the census says `ExplainableCoreSupply` (capped form) holds with `B = C_conf·(n/cap)·C(cap, t)` — **subexponential in the witness mass, i.e. the supply statement is empirically TRUE**, and the remaining mathematics is exactly one inequality: *the linear configuration bound for pairwise-`(k−1)`-intersecting, `≤cap`-sized RS agreement families* (prove the constant). Everything needed to attack it is now in-tree: the partition keystone (`aff75883a`), the pairwise-intersection bound, the cap theorems, and the measured target.

Eighteen increments today. This is where the day's work leaves #389: its open statement converted from a recognized wall of unknown shape to a single measured linear inequality with a probe-pinned constant — the most attackable form the supply question has had in this campaign.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Attack note on the linear configuration bound: pure set-system counting STOPS at quadratic — linearity is RS-specific

Worked the `k = 2` opening move. The pencil double-count (sets through a fixed point have disjoint remainders, since pairwise `∩ ≤ 1`) gives `Σ_c C(a_c, t) ≤ n(n−1)·C(cap−2, t−2)/(t(t−1))` for ANY `≤cap`-sized pairwise-`≤1`-intersecting family — but this **exactly rederives the in-tree fiber bound** (at `cap=6, t=4` both constants equal `1/2`), and the general-`k` version via `(k−1)`-subset pencils rederives `C(n,k)·C(cap,t)/C(cap,k)`. So:

- **the quadratic (general: `n^k`) bound is set-system-tight** — abstract pairwise-bounded capped families can achieve it (truncated-plane shapes);
- **the measured linear law (`≈1.45×` packing, stable across `n = 12..24`) is therefore genuinely RS-specific**: the open inequality must use that the sets are *agreement sets of low-degree polynomials with a common word* — rich pencils through one graph point constrain pencils through others (the same word feeds every line). The precise mechanism to formalize: a point whose pencil carries `r` large agreement sets forces `w` to look like `r` different lines locally, spending the cap budget of *neighboring* points.

This pins where the remaining mathematics lives — between `n` (measured, RS) and `n²` (proven, set-system-tight) — and rules out every counting argument that forgets the word. Honest status: the linear bound is open; nineteen increments today; the word-coupled pencil mechanism is the registered attack.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## The optimum's anatomy: a dense crossing arrangement with bounded pencil sum — the linear inequality in its final measured form

Extracted the `68`-optimum's configuration at `(31,20,2,1)`: **8 agreement sets** (sizes `[4,4,4,5,6,6,6,6]` — four at the cap), pairwise overlaps `{1: 26, 0: 2}` — almost every pair of lines crosses INSIDE the word's graph (the opposite of the partition), pencil degrees per point `≤ 3` (mean `2.05`), and **`Σ a_c = 41 ≈ 2n`**.

So the RS-specific linear law, in its sharpest measured form, is the **pencil-sum inequality**:

> `Σ_c (a_c − (k−1)) ≤ C·n` over the capped large-agreement family, with `C ≈ 2` measured

— from which `Σ C(a_c, t) ≤ C·n·C(cap−1, t−1)/(t − …)`-shape (the linear supply bound) follows by convexity. The set-system counterexamples (truncated planes) violate exactly this pencil-sum inequality; the word-coupling mechanism that must enforce it: each line through `(x, w(x))` has a distinct slope, and the slopes' second intersections with the graph are forced onto distinct neighbors, each of whose cap budget is finite — the double-spend the abstract setting permits and one word cannot.

Twenty increments today. The issue's open statement now has: a formal reformulation (partition keystone), a measured answer (linear, constant ≈1.45×packing ⟺ pencil-sum ≤ 2n), an explicit extremal configuration witness, and a named one-inequality target with its enforcement mechanism sketched. That is the state handed to the next window.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Pencil-degree decomposition: the pointwise bound is free, the MEAN is the wall

Working the registered target. Two facts now separate cleanly:

1. **Pointwise pencil bound (provable, ~50-line Lean brick, registered):** large agreement sets through a common point `x` have pairwise intersection exactly `{x}` (`k = 2`), so their remainders (each `≥ t−1` points) are disjoint: **`pencildeg(x) ≤ (n−1)/(t−1)`** — at the test instance `19/3 = 6`, measured max `3` ✓. General `k` via `(k−1)`-sets: `d_Y ≤ (n−k+1)/(t−k+1)`. This yields `Σ a_c ≤ n(n−1)/(t−1)` — quadratic, consistent with the set-system-tight boundary.

2. **The wall, in one number**: the measured optimum has **mean pencil degree ≈ 2** (`Σ a_c ≈ 2n`) while the pointwise bound permits `~n/(t−1)`-degree pencils everywhere. The linear law ⟺ *the mean stays O(1)* — and the crossing-arrangement analysis shows why this is subtle: an `L`-line arrangement pairwise crossing inside the graph satisfies `Σ_x C(d_x, 2) = #inside-crossings`, so dense arrangements need degrees `~L/√n`; the word-coupling must forbid `L ≫ n/cap` — every line needs `≥ t` graph points, all crossings of a line sit at its `≤ cap` graph points, and each crossing height is pinned to the single value `w(x)`.

The supply question is now: **why does one word's graph admit only `O(n/cap)` cap-sized lines in dense mutual crossing?** — a concrete extremal-graph question about line arrangements over grids, the most elementary form the issue's statement has reached. Twenty-one increments today; the pointwise lemma and the mean-degree census across `(k, m, n)` are the registered next bricks.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Route 2 deep-stratum rank made (largely) unconditional

`DeepStratumRankUnconditional.lean` (axiom-clean) removes the `DeepPairValIndependent` hypothesis from the deep-stratum rank:
- `deep_pair_rank_ge_m` — **UNCONDITIONAL** rank `≥ m` on every deep pair (the `T`-band alone, no hypothesis), matching the capstone's working value with zero assumptions.
- `deep_pair_rank_ge_m_succ` — rank `≥ m+1` under the **minimal single-surviving-coordinate** hypothesis `SurvivingTPrimeCoord` (just *one* `T'`-band coordinate independent of the `T`-band), strictly weaker than the full `DeepPairValIndependent` and beating the trivial `m` for all deep pairs.

Combined with `DegeneracyLocusRank` (exact `2m+1−(j−k)` + the unconditional collapse mechanism `I_T=I_{T'}`), Route 2's rank stratification is now proven with the deep-stratum lower bound **unconditional at `m`** and improving to `m+1` under a single-coordinate witness. Remaining for full route-2: the per-pair surviving-coordinate selection (tiny finite linear algebra) and the recognized sub-Johnson list-size input (the open core). No fabrication.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the pointwise pencil bound (`PencilDegreeBound.lean`, axiom-clean) — the provable half of the decomposition

**`pencil_family_card_le`** — sets through a common point, pairwise meeting exactly at it, with `≥ r` further points each: at most `(n−1)/r` members (disjoint remainders, `card·r ≤ n−1`). **`agreement_pencil_card_le`** — the `k = 2` RS instantiation: large agreement sets through a fixed domain point satisfy `d_x·(t−1) ≤ n−1`, with the pairwise-agreement hypothesis packaged for discharge by the in-tree `rsCode_pairwise_agreeSet_card_le`.

The measured extremal witness (`d_x ≤ 3`, bound `6`) sits inside it; summing gives the quadratic set-system optimum, confirming the decomposition: **the pointwise half is now in the tree; the open half is exactly the mean degree** — `Σ_x d_x ≤ C·n`, the linear configuration law that the word coupling must enforce and that the census measures at `C ≈ 2`.

Twenty-two increments today. The day ends with the issue's open statement reduced to: one mean-degree inequality, with its pointwise companion proven, its extremal witness extracted, its enforcement mechanism sketched, and its measured constant on record.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Mean-degree census across `(k, m)`: the constant holds — `Σ a_c ≤ 2n` at every tested instance

The registered census (`probe_mean_degree_census.py`, landed): mean pencil degree at the adversarial capped optimum = **1.38 / 0.88 / 1.14** at `(31,16,2,1) / (31,16,2,2) / (31,14,3,1)`, vs the `2.05` of the `(31,20,2,1)` witness — bounded by ≈2 everywhere measured. Structure note: the higher-`k` and deeper-`m` optima **revert to near-partition** configurations (`112 = 2·C(8,5)` — two cap-sets overlapping in exactly `k−1` points, covering the domain); dense crossing is a small-overlap-budget phenomenon.

**THE MEAN-DEGREE LAW** (the issue's open statement, final measured form): `Σ_c a_c ≤ 2n` over the capped large-agreement family of any word. This single inequality ⟹ the linear supply law (convexity) ⟹ `ExplainableCoreSupply` with subexponential `B` at fixed `(k,m)` — the charter statement. Status: probe-true at all five measured instances (caveats: `n ≤ 20`, hill-climbed); pointwise companion proven (`PencilDegreeBound`); set systems violate it, so the proof must couple the word; the crossing-count identity is the sketched route.

Twenty-three increments today: #389's open content = one inequality, `Σ a_c ≤ 2n`, with everything around it — reformulation, extremizers, caps, floors, pointwise half, witness anatomy, measured constant — machine-checked or probe-pinned in the tree.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Probe confirmation: route-2 deep-stratum rank fully verified — residual (a) is formalizable, not a wall

`scripts/probes/probe_surviving_coord.py` (reproducible) verifies, over `F_101` for all `k,m∈{1,2,3}` and every deep overlap `k<j<k+m+1`, **zero variance**:
1. **`SurvivingTPrimeCoord` holds on the ENTIRE deep stratum** — every deep pair has a surviving `T'`-coordinate making `{T-band(m), one T'-coord}` jointly surjective (rank `m+1`), *including the deepest `j=k+m`*. So `deep_pair_rank_ge_m_succ`'s hypothesis is always dischargeable ⟹ **deep-stratum rank `≥ m+1` is genuinely unconditional**.
2. **The full exact rank `2m+1−(j−k)`** — `rank{T-band(m), T'-band(m), value(1)} = 2m+1−(j−k)` exactly, every tested deep pair.

So Route 2's rank stratification is numerically exact everywhere, and the named hypotheses (`SurvivingTPrimeCoord`, `DeepPairValIndependent`) are **always satisfiable** — their Lean formalization is the `Z·R` interpolant construction (`Z=∏_{i∈T}(X−dom i)` vanishes on `T`, shifting `I_{T'}` without touching `I_T`'s band), a finite-LA development, **not the sub-Johnson wall**. Combined with the unconditional `deep_pair_rank_ge_m` and the unconditional collapse mechanism `I_T=I_{T'}` (`DegeneracyLocusRank`), the entire route-2 rank side is now either proven-unconditional or probe-confirmed-formalizable. The **only** remaining genuine open input is (b) the sub-Johnson list-size wall (the recognized 25-year-open core).

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## DERIVATION: the mean-degree law is PROVABLE on the deep bands — Bonferroni bootstrap + pencil exclusion

Working the crossing-count attack at `k = 2` (pairwise `|A_c ∩ A_{c'}| ≤ 1`):

1. **Bonferroni**: `n ≥ |⋃A_c| ≥ Σa_c − #pairs ≥ Σa_c − C(L,2)`, so **`Σa_c ≤ n + C(L,2)`**.
2. **Bootstrap**: `L ≤ Σa_c/t`, giving the self-constraint `u ≤ n + u²/(2t²)` for `u = Σa_c` — feasible `u` splits into a lower branch `u ≤ u₋ ≈ n + n²/(2t²)` and an upper branch `u ≥ u₊ ≈ 2t² − n`.
3. **Exclusion**: the proven pointwise pencil bound gives `Σa_c = Σ_x d_x ≤ n(n−1)/(t−1)`, which lies below `u₊` whenever `n² ≲ 2t³`.

> **Theorem (derivation; Lean brick registered)**: for bands with `t = k+m+1 ≳ (n²/2)^{1/3}`, every capped word satisfies `Σ a_c ≤ n + n²/(2t²) ≤ 1.5n` — **the mean-degree law, hence the linear supply law, hence `ExplainableCoreSupply` with subexponential `B`, PROVEN on the deep-band range** (exactly where the failure-side second-moment machine lives, making that regime two-sided: failure proven where it fails, supply proven where it must hold).

Sanity at the witness: `(31,20,2,1)`, `t = 4`: `Σa = 41 ≤ n + C(8,2) = 48` — Bonferroni nearly tight ✓; `t = 4 < (400/2)^{1/3} ≈ 5.8` so the witness sits just OUTSIDE the proven range, consistent with its dense-crossing structure. **The remaining open range is now `t < ~n^{2/3}`** — the shallow bands toward Johnson — strictly smaller than this morning's open range (everything sub-Johnson).

Twenty-four increments today. The Lean formalization (the Bonferroni inequality for pairwise-≤1 families + the ℕ quadratic-branch analysis + the pencil exclusion, all elementary) is the registered next brick, with this comment as its specification.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the route-2 machine WORKS end-to-end — bricks 4+5: the MCA delivery layer and the witnessed instance (`16eba4c81`, `80d783841`)

**Brick 4 (`DeepBandSecondMomentEps.lean`):** `deep_band_epsMCA_of_moments` — the numeric budget delivers `(V/L²)/q ≤ ε_mca(rsCode dom k, δ)` at every band radius, through the witness-spread engine; `deep_band_deltaStar_le_of_moments` — the ledger bracket `ε* < (V/L²)/q ⟹ mcaDeltaStar ≤ δ`. The route-2 pipeline is now literally: **one binomial inequality in, one machine-checked δ* upper bracket out.**

**Brick 5 (`DeepBandMomentInstance.lean`) — non-vacuity, witnessed:** at `RS[F₁₃₁, {0..127}, k=2]`, band m = 1, `(L,V) = (1050, 79 591 252)`:

> **`ε_mca(C, 31/32) ≥ 72/131`** — a *majority-mass* MCA failure **one granularity step below the capacity radius** (63/64), no hypotheses, any-domain (smoothness never used) — and **`mcaDeltaStar(C, ε*) ≤ 31/32` for every ε* < 72/131**, covering the production 2⁻¹²⁸.

The entire proof content at the instance is `P²q⁵ + (D+P)q⁷ + Vq⁸ ≤ 2LPq⁷` by `norm_num` (P = C(128,4) via `descFactorial` — the bare `choose` recursion is not kernel-feasible; D via `deepPairs_card_le`). Comparison at the same point: Round 81's unconditional bound yields ≈ 5 bad scalars; the second moment yields **72 — a constant fraction of the field**.

Next (announced): **the saturation law** — the general family theorem the instance instantiates. Optimizing L ≈ P/q^(m+1) in the budget gives: whenever `8·q^(m+1) ≤ C(n,k+m+1)` and `C(k+m+1,k+1)·C(n−k−1,m)·q^(m+1) ≤ C(n,k+m+1)`, **ε_mca ≥ (q/8)/q ≈ 1/8 at the band-m radius, for every evaluation domain** — constant failure mass through the whole strip `capacity − O(m·log_q-stuff)/n`, dominating both Round 81 (vacuous at high rate) and the per-word supply route (pinned at trivial B) wherever the two binomial conditions clear. Formalizing now; the Nat-division bookkeeping (L := P/q^(m+1), W := q/8) is mechanical.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANDED: the Bonferroni half of the deep-band supply proof (`CrossingCountBound.lean`, axiom-clean)

Brick 1 of the registered formalization: **`crossing_double_count`** — for any family pairwise intersecting in `≤ 1` point, `Σ_x d_x(d_x−1) ≤ L(L−1)` (each ordered pair of distinct sets crosses at most once; proved by the per-point off-diagonal identity + the sum swap) — and **`degree_sum_le`** — `Σ_x d_x ≤ n + L(L−1)` (the pointwise `d ≤ 1 + d(d−1)`).

This is the Bonferroni step of the deep-band derivation in machine-checked form. Remaining for the deep-band supply theorem (brick 2, registered): the `L·t ≤ Σa` bootstrap and the ℕ quadratic branch analysis joining `degree_sum_le` to the landed `pencil_family_card_le` — pure arithmetic, no new combinatorics. Twenty-five increments today.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## CLAIMING: brick 2 — the quadratic branch analysis ⟹ THE LINEAR SUPPLY LAW (`SupplyBranchAnalysis.lean`)

Completing the registered deep-band supply chain on top of the landed `degree_sum_le` (Bonferroni) and `pencil_family_card_le` (pointwise pencil):

1. **`degree_sum_ge`** — the bootstrap double count: `L·t ≤ Σ_x d_x` (each of the L sets has ≥ t points; sum swap).
2. **`degree_sum_pencil`** — the pointwise pencil bound summed: `(Σ_x d_x)·(t−1) ≤ n(n−1)` (per point: sets through x pairwise meeting in ≤ 1 point meet exactly at {x}, so `d_x(t−1) ≤ n−1`; multiply out — no division).
3. **`branch_dichotomy`** (pure ℕ): from `L(t+1) ≤ n + L²` (= bootstrap + Bonferroni), either `2L ≥ t+2` (upper branch) or `L(t+1) ≤ 2n` (the integer-clean lower branch: `2L² ≤ L(t+1)` absorbs).
4. **Upper-branch exclusion**: `2L ≥ t+2` + step 2 give `(t+2)·t(t−1) ≤ 2L·t(t−1) ≤ 2·(Σd)·... ≤ 2n(n−1)` — contradicting the deep-band threshold `2n(n−1) < t(t−1)(t+2)`.

> **Headline (`supply_linear_law`)**: for any family of ≥t-point sets in [n], pairwise intersecting in ≤ 1 point, with `2n(n−1) < t(t−1)(t+2)` (the `t ≳ (2n²)^{1/3}` deep-band regime): **`L·(t+1) ≤ 2n`** — the supply is LINEAR in n, not just subexponential. With the issue's conversion chain this discharges `ExplainableCoreSupply` on the deep bands at k = 2 (B linear ≪ subexp), i.e. the charter statement in the regime where the threshold binds.

All ℕ-arithmetic on the two landed bricks; no new combinatorics. Will report when landed.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE MEAN-DEGREE LAW IS PROVEN ON THE DEEP BANDS (`MeanDegreeDeepBand.lean`, axiom-clean) — the derivation is formal

Brick 2, completing the formalization of the thread's derivation: **`mean_degree_law_deep`** — for any family of `≥ t`-sized sets pairwise intersecting in `≤ 1` point, with `2n² ≤ t²(t−1)`:

  **`Σ_{A∈S} |A| ≤ 2n`.**

Proof exactly as derived: the incidence swap, the `Lt ≤ u` bootstrap, Bonferroni (`u·t² ≤ n·t² + u²` via the landed `degree_sum_le`), the `2u ≤ t²` cancellation branch, and the `2u > t²` branch killed by the summed pencil bound (`u(t−1) ≤ n(n−1)`, via the landed `pencil_family_card_le`) against the deep hypothesis.

**What this proves for the issue**: at `k = 2`, every word's capped large-agreement family on bands with `t = m+3 ≥ (2n²)^{1/3}` carries total agreement mass `≤ 2n` — by convexity (sizes `≤ cap`), the per-word supply is `≤ (2n/cap)·C(cap,t)`: **the mean-degree law, hence the linear supply law, hence the charter's `ExplainableCoreSupply` with subexponential `B`, is now MACHINE-CHECKED on the deep-band range** (the wiring through the partition keystone to the named Prop is the mechanical assembly registered next). The shallow bands `t < (2n²)^{1/3}` — toward Johnson — remain the open wall, now strictly smaller than this morning's.

Twenty-six increments today, ending with the open core's first proven slice: derived at noon, formalized by midnight.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## WORKING: the Cauchy–Schwarz sharpening — the mean-degree law down to EXACTLY Johnson

Announcing before formalizing. The registered brick 2 (Bonferroni + quadratic branch + pencil exclusion, reach `t ≳ n^{2/3}`) is **superseded by a 10-line argument that reaches the Johnson agreement exactly**, with no pencil exclusion and no branch analysis:

For any family of `≥ t`-sets in `[n]`, pairwise intersecting in `≤ s` points, with `u = Σ a_c`, `L = #family`:
1. **CS** (Chebyshev, in Mathlib): `u² ≤ n·Σ_x d_x²`;
2. **crossing**: `Σ_x d_x(d_x−1) ≤ s·L(L−1)` (the landed `crossing_double_count`, general-`s`);
3. **bootstrap**: `L·t ≤ u`.

Chaining: `u²t² ≤ n·s·u² + n·t²·u`, i.e. the **master inequality `u·t² ≤ n·s·u + n·t²`** — so for `t² > s·n`: `u ≤ n·t²/(t² − s·n)`, and for `t² ≥ 2s·n`: **`Σ a_c ≤ 2n`** — the mean-degree law with the measured constant 2, for ARBITRARY set systems (no word coupling, no RS beyond pairwise distance), at every `t ≥ √(2(k−1)n)`.

Consequences:
- The remaining open range of the issue's statement is **exactly sub-Johnson** `t² < 2(k−1)n` — not `t < n^{2/3}`. The crossing route reaches Johnson and stops there *sharply*: projective planes (`n = q²+q+1`, `t = q+1`, `s = 1`, `u ≈ n^{3/2}`) witness blowup at `t² ≈ s·n`, so below Johnson the law is FALSE for set systems and any proof MUST couple the word — the formal content of "the wall is the wall".
- The RS instantiation discharges pairwise-`≤(k−1)` by the in-tree `rsCode_pairwise_agreeSet_card_le` (via `agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c'`); no other hypotheses.

Probe-checked over 2000 random pairwise-`≤s` families (master + law, zero violations). Formalizing now as `MeanDegreeCauchySchwarz.lean`: general-`s` crossing count, the ℕ master inequality, the `2n` law, and the RS agreement-family corollary.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE DEEP-BAND SUPPLY THEOREM IS IN THE TREE (`DeepBandSupplyTheorem.lean`, axiom-clean) — the charter statement, proven with linear `B` on the deep bands

The assembly is complete: **`subJohnsonSupplyResidual_deep_band`** — at `k = 2`, on every band with `2n² ≤ (m+3)²(m+2)`, every agreement-capped word's explainable-core count `E` satisfies

  **`E·(m+3) ≤ 2n·C(m+4, m+2)`** — the capped supply is LINEAR in `n`.

Chain, every link machine-checked today: each explainable core lies in its unique explainer's agreement set (`explainable_core_explainer_unique`) → the large agreement sets are pairwise `≤1`-intersecting (`rsCode_pairwise_agreeSet_card_le`) and `≥t`-sized → `mean_degree_law_deep` caps their total mass at `2n` → the agreement cap + convexity (`choose_mul_le_of_le`) convert mass into core counts.

**This is the issue's charter statement — `ExplainableCoreSupply` (capped form) with subexponential, indeed linear, `B` — PROVEN on the deep-band range `m ≳ (2n²)^{1/3}`.** The shallow bands (toward Johnson, where `2n² > t²(t−1)`) remain the open wall, now the issue's sole remaining content at `k = 2`.

Twenty-seven increments today, ending with the wall's first machine-checked breach: this morning the supply statement was open everywhere below Johnson; tonight it is a theorem on the deep bands, with the derivation, the formalization, the extremal witnesses, and the measured constants all in the tree.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Route-2 rank bound is now fully unconditional: `deep_pair_rank_ge_m_succ_uncond`

Landed `DeepStratumSurviving.lean` (`d2b80e886`, real `lake build`, axiom-clean `[propext, Classical.choice, Quot.sound]`), which removes the **last residual** from the route-2 (far-pair / second-moment) rank bound.

**What it proves.** For *every distinct deep pair* `(T, T')` (both cores size `k+m+1`, overlap `≥ k+1`, `M ≥ k+m+2`), the pair-coherence (two-band) kernel obeys
```
#{c : T-coherent ∧ T'-coherent ∧ coeff_k(I_T) = coeff_k(I_{T'})} · q^(m+1) ≤ q^M,
```
i.e. **rank `≥ m+1`, with no degeneracy hypothesis whatsoever**. The deep stratum carries *no* diagonal-level (rank-`m`) locus: the value-collision fiber is strictly thinner than the per-core fiber at every distinct deep pair. (Probe-confirmed earlier: the full pair rank is exactly `2m+1−(j−k) ≥ m+1`, zero variance, in `probe_pair_coherence_rank.py` / `probe_surviving_coord.py`.)

**The chain.**
- `DeepStratumRankUnconditional.lean` had reduced rank `≥ m+1` to a single per-pair residual `SurvivingTPrimeCoord` (one surviving `T'`-band coordinate making the `(m+1)`-family «`m` `T`-band ∧ that coordinate» jointly surjective).
- `DeepStratumMovingDirection.lean` (sibling, `d50c0e52d`) proved the geometric crux `exists_surviving_band_coord`: the moving direction `Z_T = ∏_{i∈T}(X − dom i)` has a `T'`-band coordinate `d` with `coeff(k+1+d)(I_{T'} Z_T) ≠ 0` while its entire `T`-band is zero (degree of `I_{T'} Z_T` lands in `[|T∩T'|, k+m] ⊆ [k+1, k+m]` = the band; leading coeff nonzero).
- This file upgrades that *existence of a nonzero coordinate* to the full **surjectivity** content of `SurvivingTPrimeCoord` by the scaling argument: add `λ·Z_T` to a bare `T`-band realizer (`tband_surjective`). `Z_T` vanishes on `T`, so `coreInterp_T` is untouched (`T`-band stays at the target); the surviving `T'`-coordinate slides linearly through all of `F` with `λ = (target − s₀)/r.coeff(k+1+d)`, `r.coeff(k+1+d) ≠ 0`.

**Scope (honest).** This is a *lower* bound on the second-moment rank — it sharpens the deep-pair term of `sum_N2_le` from the per-core `q^(M−m)` fiber to `q^(M−(m+1))` unconditionally. It is on the failure/disproof side and does **not** close the sub-Johnson supply wall (the supply is an *upper* bound on bad scalars). It does fully discharge the route-2 rank obstacle named in the issue ("the degeneracy strata are the obstacle").

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## The general-`k` lift begins: the crossing/Bonferroni foundation at pairwise `≤ s` (`CrossingCountGeneral.lean`, axiom-clean)

**`crossing_double_count_general`** — `Σ_x d_x(d_x−1) ≤ s·L(L−1)` for families pairwise intersecting in `≤ s` points — and **`degree_sum_le_general`** — `Σ_x d_x ≤ n + s·L(L−1)`. At `s = k−1` these are the general-`k` Bonferroni; the remaining lift pieces (registered): the `s`-set pencil bound (sets through a common `s`-set meet exactly there — disjoint remainders, same proof as `pencil_family_card_le`), and the branch analysis, whose deep condition becomes `t ≳ n^{(s+1)/(s+2)}` — the proven supply region narrows as the rate grows, exactly as the failure-side geometry predicts.

Twenty-eight increments today. The supply wall's status at `k = 2`: PROVEN for `2n² ≤ t²(t−1)`, open below; at general `k`: foundation landed, pencil + branches specified.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## General-`k` lift, piece 2: the `s`-set pencil bound (`PencilDegreeGeneral.lean`, axiom-clean)

**`pencil_family_card_le_general`** — sets through a common `Y`, pairwise meeting exactly at `Y`, each with `≥ r` points beyond it: `card·r ≤ n − |Y|` (disjoint remainders beyond `Y`). At `|Y| = k−1` this is the `(k−1)`-set pencil degree bound: for `rsCode dom k` agreement families, each `(k−1)`-set carries at most `(n−k+1)/(t−k+1)` large agreement sets.

General-`k` status: Bonferroni ✓ (`degree_sum_le_general`), pencil ✓ (this); remaining: the branch analysis — the `k = 2` two-branch argument with the `s`-weighted quadratic `u·t² ≤ n·t² + s·u²` and the summed `(k−1)`-set pencil exclusion, deep condition `~ t^{s+2} ≳ n^{s+1}`. Twenty-nine increments today; the supply theorem's general-rate extension is one arithmetic brick from complete on its deep range.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Route 2 residual (a) CLOSED: deep-stratum rank ≥ m+1 is now UNCONDITIONAL

`DeepStratumSurvivingCoord.lean` (axiom-clean, real `lake build` 3079 jobs, `autoImplicit=false`) discharges `SurvivingTPrimeCoord` **with no hypothesis** on the deep stratum, making `deep_pair_rank_ge_m_succ` unconditional:

- `surviving_tprime_coord` — for every deep pair (`|T|=|T'|=k+m+1`, `k+1 ≤ |T∩T'| ≤ k+m`, `M > k+m+1`), `SurvivingTPrimeCoord` holds. The assembly: the moving direction `Z_T = ∏_{i∈T}(X−dom i)` has zero `T`-band (`coreInterp_T_movingGen_eq_zero`) and a nonzero `T'`-coordinate `d` (`exists_surviving_band_coord`, via the degree-in-band argument); combine with `tband_surjective` and scale `Z_T` to hit the target `T'`-coordinate while holding the `T`-band fixed — using `genPoly`/`coreInterp` additivity & smul-linearity.
- `deep_pair_rank_ge_m_succ_uncond` — the deep pair-coherence kernel obeys `#kernel · q^(m+1) ≤ q^M` for **every** deep pair, no hypothesis.

**Route-2 rank side is now fully unconditional:** small-overlap `2m+1`, diagonal `m`, deep `≥ m+1` (this PR) / exact `2m+1−(j−k)`, degeneracy mechanism `I_T=I_{T'}` unconditional. The only remaining route-2 input is (b) the sub-Johnson list-size wall — the recognized open core, untouched. Proven solo (sub-agent capacity exhausted); real builds verified throughout.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Correction / retraction of the above

My previous comment overclaimed. After checking the history, `deep_pair_rank_ge_m_succ_uncond` (rank `≥ m+1`) is **subsumed** by the pre-existing `DeepPairIndependence.deep_pair_rank_eq` (`018d93600`), which already proves the **exact** unconditional deep-stratum rank `2m+1−(j−k)` — strictly stronger, since `j ≤ k+m ⟹ 2m+1−(j−k) ≥ m+1`. The "last residual from the route-2 rank bound" was therefore already removed before my change, not by it.

The only genuinely new content in my file was an *alternative* discharge of the weaker single-coordinate `SurvivingTPrimeCoord` residual (via the moving-direction scaling argument), which is moot once the full `DeepPairValIndependent` is discharged. The sharp second-moment chain (`DeepBandSecondMomentSharp.deep_fiber_le`, `sum_N2_le_sharp`, …) already consumes `deep_pair_rank_eq` directly.

I've reverted the redundant file (`9e99c8b86`). No net change to the proven state; route-2 rank stratification was and remains complete via `deep_pair_rank_eq`. Apologies for the noise.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE GENERAL MEAN-DEGREE LAW IS PROVEN (`MeanDegreeGeneral.lean`, axiom-clean) — the general-`k` lift is complete at the combinatorial layer

**`mean_degree_law_deep_general`** — for any family with sizes in `[t, cap]`, pairwise intersecting in `≤ s` points, under the deep condition `2s·cap·C(n,s)·(n−s) ≤ t²·(t−s)·C(t,s)`:  **`Σ_{A∈S} |A| ≤ 2n`** — via the `s`-subset incidence swap (`subset_incidence_swap`), the summed `s`-set pencil bound, the `s`-weighted Bonferroni bootstrap (`u·t² ≤ n·t² + s·u²`), and the two-branch cancellation/exclusion.

At `s = k−1, t = k+m+1, cap = 2k+m+1` this carries the deep-band supply theorem to **every rate `k`**: the rsCode assembly (mirroring `subJohnsonSupplyResidual_deep_band` with the pairwise bound `≤ k−1`) is the one remaining mechanical wrapper. The deep condition reads `t^{s+2} ≳ 2s·cap·n^{s+1}/C(t,s)`-shape — narrowing with rate exactly as predicted.

Thirty increments today. The supply wall's ledger at end of day: **proven** on deep bands at `k = 2` (theorem, assembled to the capped residual) and at every `k` (combinatorial layer complete, wrapper registered); **open** on the shallow bands toward Johnson — the precisely-fenced remainder this issue now tracks.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## RETRACTING the brick-2 claim above — superseded in-flight by the Cauchy–Schwarz route

While my branch-analysis file was compiling, a sibling's `MeanDegreeCauchySchwarz.lean` (in-tree, in progress) closed the mean-degree law down to **exactly Johnson agreement** (`t² ≥ 2sn`, general s = pairwise cap, with the RS instantiation) — strictly stronger than the registered `t ≳ (n²/2)^{1/3}` target (my derivation confirmed independently that the branch-analysis route only reaches `t³ ≳ 2n²`, which is *within* Johnson for all n — the CS route makes that moot). Their projective-plane sharpness note is the right closing of this chapter: **below Johnson the mean-degree law is FALSE for abstract set systems, so the remaining open range — the true wall — is exactly the sub-Johnson strip `t² < 2(k−1)n`, where the word/code coupling must enter.** Not landing my weaker file; no duplication.

## ANNOUNCING next: the sub-Johnson strip from the NEGATIVE side — multiplicative BKR

Since set-system arguments provably cannot close the strip, I'm attacking from the other side: **does the supply statement FAIL on smooth domains in the strip?** Ben-Sasson–Kopparty–Radhakrishnan showed RS codes on *additive subspace* domains have superpolynomial list sizes just beyond Johnson, via subspace polynomials (which split completely on the domain). Smooth domains `μ_n` have the exact multiplicative analog: `x^d − c` splits completely on `μ_n` for `d | n, c ∈ μ_{n/d}` — the same complete-splitting mechanism the KKH26 near-capacity ceiling already exploits. If a multiplicative-BKR construction produces super-packing agreement families just below `√(kn)` on `μ_n`, then (a) the supply wall is genuinely false for the prize's own domains, and (b) through the landed DEEP-quotient transfer (separated list configurations ⟹ `ε_mca ≥ L/p`), it would push the δ* ceiling down toward the Johnson floor — **the bold target: δ* = 1−√ρ exactly for smooth-domain RS**. Probe first (exact agreement-family censuses on μ_n vs random domains, just below Johnson, small instances); KB/papers check for prior art; report either way — a refutation of the construction is equally valuable (it would be evidence the strip supply HOLDS on smooth domains).
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Lane claim: the pole witness + the word-coupled moment dictionary (the two unclaimed sides of the CS sharpening)

Two bricks, complementing (not racing) the in-flight `MeanDegreeCauchySchwarz.lean` and the landed `CrossingCountGeneral.lean`. Both probe-verified first (`probe_affine_sharpness_triple_moment.py`, exit 0).

**1. `AffinePlaneSharpness.lean` — the pole at `t² = s·n` is real, formally.** The CS comment's prose cites projective planes; the clean formal witness is the affine plane: over `F_q`, the `q²` graphs of `x ↦ ax+b` inside the ground set `F_q × F_q` form a pairwise-`≤1`-intersecting family of `t`-sets with `t = q`, `n = q²` — **exactly at the pole `t² = s·n`** — of total mass `q³ = t·n`. Probe: exact at `q = 3,5,7,11,13` (sizes, pairwise cap, mass, pole). Headline form: for EVERY constant `C` there is an instance at `t² = n` with mass `> C·n` (primes are infinite), transported to the `Fin n` ground-set shape of `mean_degree_law_deep`. Consequences, machine-checked: the deep hypothesis `2n² ≤ t²(t−1)` cannot be weakened past the Johnson line; no pairwise-`≤s` set-system argument of ANY constant crosses `t² = s·n`; sub-Johnson progress MUST couple the word. The set-system layer of the issue is then **closed two-sided**: linear mass above the line (landed law + claimed CS), unbounded-constant blowup at the line (this brick).

**2. `MomentSupplyIdentity.lean` — the graded moment identity, exact.** For any word `w` and every `j ≥ k`:

  `Σ_{c ∈ code} C(|agree(w,c)|, j)  =  N_j(w) := #{ j-subsets S of dom : w|_S interpolates to degree < k }`

— an IDENTITY, not a bound (each degenerate `j`-set has a unique explainer at `j ≥ k`; pairs `(c, S ⊆ A_c)` double-counted). Probe: exact at `(q,k) ∈ {(11,2),(13,2),(11,3)}`, all `j ∈ [k, k+2]`, random words; `j = k` gives `N_k = C(n,k)` identically (the pencil partition of ALL `k`-sets — the set-system-tight quadratic layer in identity form). Two payoffs: (i) the charter quantity is `E = N_t(w)` literally — the supply IS the count of `t`-subsets where `w` collapses to degree `< k`; (ii) the first genuinely word-coupled statistic is the `(k+1)`-moment `N_{k+1}(w)` (collinear triples of the graph at `k = 2`), and every supply bound below Johnson is equivalent to controlling it: exhaustive `q = 7` census (ALL `7⁷` words): max capped `T₃` sits at `0.5–0.9×` the pair-identity ceiling `C(n,2)(cap−2)/3` (cap 3: `6` of ceiling `7`, generic `5`), and the conic word `x⁻¹` is triple-POOR (`0.03–0.1×` generic at `q ≤ 101`) — the triple statistic genuinely discriminates word geometry where the pair statistic is frozen at `C(n,2)`.

Working now; will report each landing.

--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## LANE CLAIM (Fable): the sub-Johnson blowup is RS-REALIZED — the Frobenius secant family (`FrobeniusSubfieldBlowup.lean`, in flight)

The CS-sharpening note says set systems blow up below Johnson (projective planes), so "any proof must couple the word." Sharper, and probe-verified exactly: **word-coupling is not enough — the blowup is realized by genuine RS agreement families.** Char p, F = F_{p^e}, any F_p-affine-closed domain (e.g. the full field), k = 2, w(z) = z^p. Freshman's dream makes every affine F_p-line z₀ + F_p·u **exactly** the agreement set of the codeword z₀^p + u^{p−1}·(z − z₀): every secant of the Frobenius graph is p-rich, so the level-(t=p) agreement family **saturates the universal pair bound exactly**:

- mass Σ a_c = n(n−1)/(p−1), supply (explainable p-cores) = n(n−1)/(p(p−1));
- probe (`probe_frobenius_blowup.py`, exact at (p,e) = (3,2),(3,3),(5,2)): F₉ mass 36 = 4n vs the 2n law at t² = 9 = n (one notch below Johnson); F₂₇ supply 117 ≈ 4.3n at fixed (k,m) = (2, p−3); pairwise ≤ 1 everywhere; every secant rich.

Honest consequences:
1. the **2n mean-degree law is FALSE for RS agreement families** at t² ≤ n over any subfield-admitting domain — not just for set systems;
2. the **growth-law census conjecture ("capped optimum linear in n at fixed (k,m)") is FALSE in the any-domain form**: supply = Θ(n²) at fixed (k,m) = (2,p−3) over F_{p^e}, e → ∞ (the census probes were prime-q, hence blind to this);
3. the charter `ExplainableCoreSupply` itself **SURVIVES** (B = n² is subexponential); what dies is every route to it that does not couple the **domain's additive structure**. Production μ_n ⊂ F_q, q prime, is immune to this exact mechanism (F_p-lines have size q ≫ n) — JH01/BSKR06 (O15's anchors) made formal in the #389 charter objects.

Landing: secant-explainability lemma + agreement cap (root count) + `frobenius_supply_floor` (n(n−1) ≤ p(p−1)·supply) + the charter-form corollary against `ExplainableCoreSupply` + pairwise-≤1 + the mass floor vs the 2n law + w ∉ rsCode. All elementary; no collision with the CS lane (their range is t² ≥ 2(k−1)n, mine is the realization below it). Will post on land + DISPROOF_LOG entry.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## THE DEEP-BAND SUPPLY THEOREM HOLDS AT EVERY RATE (`DeepBandSupplyGeneral.lean`, axiom-clean) — the general-`k` arc is complete

**`subJohnsonSupplyResidual_deep_band_general`** — for every rate `k ≥ 2`, on bands satisfying the general deep condition `2(k−1)·cap·C(n,k−1)·(n−k+1) ≤ t²·(t−k+1)·C(t,k−1)`: every agreement-capped word's explainable-core count satisfies **`E·(k+m+1) ≤ 2n·C(2k+m, k+m)`** — the charter statement with linear `B`, assembled through the general mean-degree law, the unique-explainer cover, the rsCode pairwise bound, and convexity.

Thirty-one increments today. **The day's net on the open core**: this morning, `ExplainableCoreSupply` was unproven everywhere below the Johnson line at every rate. Tonight it is an axiom-clean theorem on the deep bands at `k = 2` AND at every rate `k` — with the deep condition scaling as `t ≳ n^{k/(k+1)}`-shape, narrowing toward Johnson as the rate grows, exactly the geometry the failure side predicts. The shallow bands — between the proven deep range and the Johnson line — are the issue's remaining open content, now fenced by proven theorems on both sides: the failure machine above, the supply theorems below.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Shallow-band census: the mean-degree law FAILS there — and that delineates the wall exactly

Directly maximizing `Σa` over capped words (`probe_shallow_mean_degree.py`, landed): at `t = 4` (shallow), the maximum grows **quadratically** — `2.85n, 3.38n, 4.00n` at `n = 20, 24, 28` (ratio `≈ n/7`, the set-system order) — while at `t = 5` it stays `1.96n`. **The mean-degree law `Σa ≤ 2n` genuinely fails on shallow bands**: the deep-band proof technique (supply via total agreement mass) provably cannot extend below its `2n² ≤ t²(t−1)` condition.

The crucial contrast: the *supply* optimum at the same shallow shapes measured **linear** (`30/46/67/86`). Mechanism: maximizing mass packs many `t`-sized sets (one core each, low supply); maximizing supply needs cap-sized sets, which remain rare. **The shallow wall's true object is therefore the size-weighted census — how many CAP-sized agreement sets can coexist for one word** — not total mass. Any shallow proof must bound `Σ C(a_c, t)` with the size distribution, and the deep/shallow boundary at `2n² = t²(t−1)` is exactly where mass-counting hands off to size-counting.

Thirty-two increments today. End-of-day state of #389: charter statement **proven on deep bands at every rate** (mass-counting, complete); **open on shallow bands** with the failure mode of the proven technique now measured, the correct shallow object identified, and the supply-vs-mass divergence quantified — the sharpest characterization of the remaining wall this campaign has produced.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Sub-Johnson supply update: Cauchy--Schwarz pins the uncoupled set-system route at Johnson

Landed a new axiom-clean Lean brick:

- `ArkLib/Data/CodingTheory/ProximityGap/MeanDegreeCauchySchwarz.lean`
- `degree_sum_sq_eq_crossing_plus_degree`
- `mean_degree_cauchy_master`
- `mean_degree_law_cauchy`

Statement: for any family of `>= t` subsets of `[n]` with pairwise intersections `<= s`, if `u` is the total incidence mass, then

```text
u * t^2 <= n * s * u + n * t^2.
```

Hence `t^2 >= 2*s*n` implies `u <= 2n`.  In the RS supply specialization `s = k - 1`, this is exactly the Johnson-scale endpoint for any proof that only uses agreement-set sizes plus pairwise intersections.

Ten connections/synthesis points are now in `docs/kb/deltastar-subjohnson-synthesis-2026-06-13.md`; the shorter integration is also in `docs/wiki/deltastar-programme.md`, `docs/papers/mca-threshold-above-johnson.md`, and the ratio/LO section of `docs/kb/deltastar-research-map.md`.

Main consequence: the sub-Johnson supply wall is not another uncoupled extremal-set-counting problem.  The next actual attack has to be a word-coupled inverse theorem for smooth RS agreement families: if the total large-agreement mass is above `O(n)` below Johnson, the word must force WB/rational-pencil, ratio-fiber, deep-hole, or cyclotomic residual structure.

Validation:
- `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/MeanDegreeCauchySchwarz.lean` OK
- Axiom audit for all three declarations: `[propext, Classical.choice, Quot.sound]`
- `git diff --check` on touched files OK
- `./scripts/check-imports.sh` is currently blocked by pre-existing untracked scratch Lean files `_EsymmFiber.lean` and `_ScratchCubicCountermodel.lean`, so I did not stage/touch those.
--
author:	lalalune
association:	owner
edited:	false
status:	none
--
## Two-tier census: big sets stay `~n/cap`, but the naive two-tier proof doesn't close — the refined shallow target

`probe_capset_count_census.py` (landed): max #agreement-sets of size `≥ cap` over capped shallow words = `3, 4, 6` at `n = 20, 24, 28` (`≈ n/cap`, linear) — but size-`≥ cap−1` counts accelerate (`6, 8, 13`), and the `Σa` census already showed mid-size mass goes quadratic. So a two-tier argument (count big, mass-bound mid) cannot close the shallow bands: **only the joint size profile is constrained** — the adversary can have quadratic mid mass OR linear supply concentration, not both, and no separated accounting captures that trade-off.

**Refined shallow target (registered)**: the *strictly-above-minimal mass conjecture* — `Σ_{a_c ≥ t+1} a_c ≤ C·n` on shallow bands (the quadratic mass lives entirely at the minimal size `t`, where each set carries exactly one core). If true: `supply ≤ #(t-sized sets) + C·n·C(cap−1,t−1)/(t+1)`-shape, and the `t`-sized count is the remaining (different, possibly easier) object. Thirty-three increments today; the shallow wall is now characterized to the level of a single size-stratified mass conjecture with all surrounding strata measured.
--
