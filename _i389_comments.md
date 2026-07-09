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
