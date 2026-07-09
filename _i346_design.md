# Issue #346 design — discharge `randomRSListDecodingFirstMomentResidual`

## The residual (ArkLib/ToMathlib/AGL24RandomRSProof.lean:78)
`randomRSListDecodingFirstMomentResidual F n k listBound η failure hn : Prop :=`
`  Pr_{L ← uniformSizeSubsetOfLe F n hn}[¬ (Λ(RS[toEmbedding L, k], 1-k/n-η) ≤ listBound)] ≤ failure`

Fully parameterized: providers at honest parameter regimes are genuine discharges of the
Prop *at those parameters* (census: provider = theorem whose result head = the residual,
hypotheses not census residuals).

## Literature map (AGL24 = arXiv 2304.09445 v6)
- Thm 1.1: q ≥ n + k·2^{10L/ε}, radius (L/(L+1))(1-R-ε), average-radius (L+1)-list,
  failure ≤ 2^{-Ln}; probability space = uniform DISTINCT n-tuples (≃ uniform n-subsets).
- Proof: bad ⟹ agreement hypergraph k-weakly-partition-connected (Lem 2.3);
  union over ≈2^{Ln} hypergraph shapes; per-shape Pr[reduced intersection matrix
  rank-deficient] ≤ C(n,r)·2^{tr}·((t-1)k/(q-n))^r via certificates (Lem 3.1/3.8/3.10/3.12);
  symbolic full-rank via GM-MDS + hypergraph-orientation (Thm 2.11, BGM23 lineage).
- In-tree frontier certificate: `ProximityGap.johnson_radius_lt_capacity`
  (RSListDecodingFrontier.lean) — Johnson < capacity strictly; beyond-Johnson needs
  GM-MDS machinery absent from mathlib. Above capacity: refuted
  (`rs_uptoCapacity_false_rate12_n256`, UpToCapacityListDecodingFalse.lean).

## In-tree bricks (all verified present, axiom-clean)
- `ProximityGap.reedSolomon_Lambda_le_johnson` (RSLambdaJohnson.lean): every-domain
  Λ(RS,δ) ≤ ⌊n²/((n-⌊δn⌋)² - n(k-1))⌋ under gap n(k-1) < (n-⌊δn⌋)²; [NeZero k][Nonempty ι].
- `CodingTheory.card_le_one_of_two_mul_radius_lt` (UniqueDecodingPairwise.lean).
- `ReedSolomon.minDist_eq'` (NeZero k, k ≤ card ι): minDist = n-k+1.
- `ArkLib.JohnsonBound.minDist_le_hammingDist`.
- `ListDecodable`: Lambda_le_natCast_of_forall_closeFinset_card_le,
  exists_closeFinset_card_gt_of_not_Lambda_le_natCast, card_closeCodewordsRelFinset_eq_ncard.
- `ArkLib.JohnsonBound.card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset`
  (Family.lean) — close ⟹ agree ≥ n - ⌊δn⌋ (δ ≥ 0).
- GG25 bridge pattern (GG25RandomRSMCAProof.lean): Pr = badCount/C(q,n) proof skeleton
  (Pr_eq_tsum_indicator → tsum_fintype → uniformSizeSubsetOfLe_apply → sum_boole).
- mathlib: PMF.coe_le_one, Fintype.card_coe (instance-poly), Finset.exists_subset_card_eq.

## Deliverables (all in AGL24RandomRSProof.lean, #print axioms each)
A. Counting bridge: badDomainCount def; Pr = count/C(q,n); of_badCount; of_allGood.
B. Event-level every-domain lemmas:
   B1 event_of_radius_neg (1-k/n-η < 0 ⟹ Λ=0 ≤ anything; works for n=0 too)
   B2 event_of_johnson_gap (k≠0, 0<n, gap@n, ⌊n²/Den⌋ ≤ listBound)
   B3 event_of_unique_decoding (k≠0, k≤n, 0<n, 2⌊δn⌋ < n-k+1, 1 ≤ listBound)
C. Residual providers (census-visible, honest parameter-regime hypotheses):
   C1 of_failure_ge_one (Pr ≤ 1)
   C2 of_radius_neg, C3 of_johnson_gap (flagship), C4 of_unique_decoding
D. Honest narrowing of the remaining external core (BKR06 `_of_*` hypothesis pattern):
   D1 witness extraction: bad L ⟹ ∃ f, ∃ T ⊆ closeFinset, |T| = listBound+1
      (+ agreement ≥ n-⌊δn⌋ per member when δ ≥ 0) — AGL24 Lemma 2.3 input shape, PROVEN.
   D2 of_certified_count: bound on #(domains admitting a D1 certificate) ⟹ residual
      (consumes exactly the AGL24 §3 counting output; proven via D1 + filter mono).
E. Module docstring: coverage map; remaining external content = AGL24 §3 counting
   (GM-MDS/hypergraph-orientation lineage); frontier + refutation cross-refs.

## Honesty guards
- No `True`-conversion, no axiom, no restated-conclusion hypothesis except the
  documented GG25-precedented `of_badCount`/`of_prob_bound` reduction API.
- Beyond-Johnson coverage is NOT claimed; frontier strictness cited; refutation cited.
- Regime providers state exact coverage in docstrings.

## Census effect
Row `CodingTheory.randomRSListDecodingFirstMomentResidual` open → discharged
(concrete providers C1–C4). No new census rows (D-hypotheses are theorem hypotheses,
BKR06-style). Open count 42 → 41.

## Remaining external core: 3 reasonable + 3 novel routes (for issue comment)
R1. Formalize GZ23 (2304.01403, quadratic field) instead of AGL24: same front door,
    simpler counting (no orientation thm); still needs GM-MDS.
R2. Formalize the FOLKLORE exponential-field bound (q ≥ 2^{Θ(n/η)}): pure
    interpolation+union bound, no GM-MDS; gives nontrivial beyond-Johnson regime at
    huge q. Most tractable full proof.
R3. Port GM-MDS via the Lovett/Yildiz-Hassibi simple proof (symbolic determinant
    non-vanishing, polynomial method) + AGL24 App A orientation argument.
N1. Average-radius potential-function argument à la CZ25 FPRUNE shell
    (FirstMomentListBound.lean): re-derive AGL24 Lem 2.3 certificates as weighted
    samples of the in-tree `card_le_of_weight_bounds` shell, bypassing hypergraphs.
N2. Two-prime/derandomized domains: prove the bound for STRUCTURED domains
    (multiplicative cosets) via in-tree subspace-poly machinery — sidestep uniform
    sampling by transport from a measure-preserving domain family.
N3. Entropy-compression: encode a bad domain by its certificate (D1) + repair data;
    in-tree EntropyVolume bricks give the counting; turns AGL24 §3 into an
    incompressibility statement (no GM-MDS, but needs new encoding lemmas).
