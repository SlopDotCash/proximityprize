## Discharged: every-domain regime providers + AGL24 brick 0 (Lemma 2.4) + the faithful §3 interface

**What landed** (commit <SHA>, all axiom-clean `[propext, Classical.choice, Quot.sound]`, `#print axioms` in-file):

### 1. Genuine unconditional providers (the "connect the existing development" criterion)

The residual is parameterized over `(n, k, listBound, η, failure)`; in real parameter regimes the AGL24 statement holds for **every** size-`n` domain, so `Pr[bad] = 0 ≤ failure` outright. New providers in `ArkLib/ToMathlib/AGL24RandomRSProof.lean`:

- `randomRSListDecodingFirstMomentResidual_of_johnson_gap` — **the substantive one**: under the Johnson gap `n(k−1) < (n−⌊δn⌋)²` (δ = 1−k/n−η) with `listBound` clearing the second-moment Johnson cap `⌊n²/((n−⌊δn⌋)²−n(k−1))⌋`, every domain is good (via `ProximityGap.reedSolomon_Lambda_le_johnson`, the #232 Johnson brick). Front-door corollary `random_rs_list_decoding_of_johnson_gap` included.
- `..._of_unique_decoding_radius` — below half the RS distance (`2⌊δn⌋ < n−k+1`), list size ≤ 1 on every domain (`card_le_one_of_two_mul_radius_lt` + `ReedSolomon.minDist_eq'`); covers `listBound = 1`, sharper than Johnson there.
- `..._of_radius_neg` — degenerate radius `1−k/n−η < 0`: every point list empty, any `listBound` (even 0).
- `..._of_one_le_failure` — probability floor `Pr ≤ 1` (sanity regime).
- `..._of_allGood` — the all-domains-good ⟹ zero-failure reduction feeding the above (GLMRSW22 `PMF.map_const` pattern).

**Honest coverage boundary**: these stop exactly at the Johnson radius. The in-tree frontier certificate `ProximityGap.johnson_radius_lt_capacity` proves the gap to capacity is non-empty, and `rs_uptoCapacity_false_rate12_n256` refutes the bound at capacity for adversarial parameters — beyond Johnson, the *randomness of the domain is essential* and no every-domain argument can exist. Module docs state this explicitly.

### 2. Brick 0 of the genuine AGL24 campaign: Lemma 2.4 PROVEN

New file `ArkLib/Data/CodingTheory/ListDecoding/AGL24WeakPartitionConnectivity.lean` (Mathlib-only, self-contained):

- `WeaklyPartitionConnected` — AGL24 Definition 2.2 over `Finpartition`;
- `edgeWeight_le_partsMet_sub_one_add_sum` — the pointwise weight identity behind eq. (2.4);
- `exists_weaklyPartitionConnected_subset` — **[AGL24] Lemma 2.4 in full**: total weight ≥ k(|V|−1) ⟹ a ≥2-vertex subset whose restricted hypergraph is k-weakly-partition-connected (minimal-cardinality subset + per-part failure + the summed identity).

This is exactly the "brick 0: Lemma 2.4 + self-contained combinatorics first" recommended in the comment above.

### 3. The faithful narrowed interface (the "exact paper lemma that remains external")

- `exists_close_list_of_badDomainEvent` — witness extraction: a bad domain yields `listBound+1` distinct close codewords (Lemma 2.3 input shape), proven.
- `randomRSWeakPartitionWitness` — the AGL24 §2 certificate: ≥2 distinct RS codewords + center whose coordinate agreement hypergraph is `d`-weakly-partition-connected (closeness deliberately dropped — the paper's §3 counts the weaker object, making the interface faithful).
- `randomRSWeakPartitionWitness_of_badDomainEvent` — **Lemma 2.3 + Lemma 2.4 composed, proven in-tree**: in the discrete parameter regime `d·listBound + n ≤ (listBound+1)(n−⌊δn⌋)`, every bad domain admits a `d`-WPC certificate.
- `randomRSListDecodingFirstMomentResidual_of_weakPartitionWitness_count` — the residual now follows from a **count of WPC-certificate domains** — precisely the object AGL24 §2.3–§3 bounds via reduced intersection matrices. Everything else (witness extraction, weight argument, PMF accounting) is in-tree.

### Remaining external core, honestly delineated

The single remaining input is the RIM counting estimate: `#{L : ∃ d-WPC agreement certificate} ≤ B`. Per the scope verdict above, that is the 39-page paper's §2.3–§3 (full-rank of reduced intersection matrices w.h.p., via GM-MDS + hypergraph orientation). Routes, for whoever picks it up:

**Reasonable (known math):**
1. **GZ23 route** (arXiv 2304.01403, quadratic field size): same front door, simpler counting than AGL24's; still needs GM-MDS. Formalize Yildiz–Hassibi/Lovett's GM-MDS proof (symbolic determinant non-vanishing — polynomial method, mathlib-friendly).
2. **Folklore exponential-field route**: for `q ≥ 2^{Θ(n/η)}` a direct interpolation + union bound over agreement patterns works with no GM-MDS; gives a *complete, honest, nontrivial* beyond-Johnson discharge at huge field size. Most tractable full proof; recommended next brick.
3. **AGL24 App. A route**: hypergraph-orientation theorem (Frank–Király–Kriesell lineage) + GM-MDS, then the certificate counting of §3 (Lemmas 3.8/3.10/3.12) — the full linear-field result. Lemma 2.4 (done) was step 0 of exactly this path.

**Novel (new proof tech):**
1. **FPRUNE-shell re-derivation**: re-derive the §3 count as a weighted first-moment via the in-tree `CodingTheory.ListDecoding.card_le_of_weight_bounds` union-bound shell (CZ25 machinery), with WPC certificates as the weighted objects — bypassing intersection matrices.
2. **Structured-domain transport**: prove the count for explicit structured domain families (smooth multiplicative cosets, via the in-tree subspace-polynomial toolkit) and transport to uniform sampling through `UniformPushforward.lean`'s balanced-surjection bridge — a derandomized variant that would also feed the #334 δ* program.
3. **Entropy-compression**: encode a bad domain by its WPC certificate + repair data and use the in-tree entropy-volume bricks (`EntropyVolumeListSize` etc.) for an incompressibility count — no GM-MDS, but needs new encoding lemmas.

Census: `randomRSListDecodingFirstMomentResidual` now has unconditional regime providers (was: only the `_of_badCount` accounting reduction); open count unchanged at the improved baseline, no new census rows added (narrowed obligations are named hypotheses of proven reductions, per the BKR06 `_of_family` convention).
