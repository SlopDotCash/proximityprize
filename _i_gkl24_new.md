## The two atomic GKL24/GCXK25 witness-cover roots (successor tracker to #67)

#67 (ABF26 T5.1 first-moment) is closed — the per-codeword count was sharpened to `b = δ·n + 1` in-tree, and the consumer chain down to `epsMCA` bounds is fully proven. What remains open is exactly the **maximal-domain witness-cover construction** (GKL24 Lemma 1 / GCXK25 Theorem 3 content), tracked by two atomic residual surfaces:

- `ProximityGap.GKL24MaxCorrStrictWitnessCoverResidual` — `ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean` (strict-expansion root: per stack, a close-codeword carrier `T` covering `mcaBad`, `|T| ≤ B_T`, and per `w ∈ T` a maximal correlated-agreement domain strictly expanded by every bad line-agreement set)
- `ProximityGap.Issue67Scratch.GKL24MaxDomainWitnessCoverResidual` — `ArkLib/Data/CodingTheory/Connections/GKL24PetalWitnessCover.lean` (atomic root: adds per-γ codewords `wOf` and the pairwise large-intersection clause — the genuine Lemma 1 certificate)

Everything downstream of these two roots is **proven in-tree**:
- strict root + Johnson params (`2δ ≤ p ≤ 1`) ⟹ max-corr form (`GKL24MaxCorrWitnessCoverResidual_of_strict_cover`, via `lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness`);
- max-corr form ⟹ petal form (`GKL24PetalWitnessCoverResidual_of_maxCorr_cover`, via `linePetal_pairwise_disjoint_of_maxCorrAgreeDomain`);
- atomic root ⟹ petal form (`gkl24PetalWitnessCoverResidual_of_maxDomainWitnessCover`);
- petal form ⟹ first-moment count + `epsMCA` probability front doors.

So the open mathematics is precisely: **construct, per witness codeword, the maximal correlated-agreement domain with the strict-expansion (and, for the atomic form, pairwise-intersection) properties** — the sunflower/maximal-domain argument of the paper. The intermediates (`GKL24MaxCorrWitnessCoverResidual`, `GKL24PetalWitnessCoverResidual`) carry no independent open content and are being renamed out of the strict residual ledger as part of #362 (their reduction theorems remain, unchanged).

Acceptance: prove the two roots axiom-clean (paper-faithful construction), or land the paper's Lemma 1 in a dedicated module with the roots as corollaries. Related: #362 (strict residual burn-down), #67 (closed predecessor, full history), #346 (AGL24 sibling campaign).
