=== COMMENT 105 | lalalune | 2026-06-11T14:01:59Z ===
## Round 6(b): RED-TEAM CORRECTION + THE EXACT DOMAIN INVARIANT — the dual-vector matroid census

**Red-team kill of the per-pair orbit-weight model:** writing the interpolation scalar in dual-syndrome form — γ_S = −⟨λ^S,u₀⟩/⟨λ^S,u₁⟩ with λ^S the Lagrange dual vector (λ^S_i = 1/∏_{j∈S∖i}(x_i−x_j)) — shows any single pair's collision statistics depend only on the 4-tuple (⟨λ^S,u₀⟩,⟨λ^S,u₁⟩,⟨λ^{S′},u₀⟩,⟨λ^{S′},u₁⟩), which is **uniform** for independent duals: pairwise collision probabilities are *provably equal across all pairs* — the round-6(a) orbit enrichment was sampling noise (as its ±1.8σ warned). The census deficit is governed by **higher-order dependencies among the dual vectors**.

**The exact invariant (no sampling, field-stable):** dependency census of {λ^S : |S| = 4} for (8,3):

| domain | dependent triples (p=73) | (p=89) |
|---|---|---|
| smooth μ₈ | **600** | **600** |
| AP (1..8) | **568** | **568** |

Decomposition: a universal floor of 560 (= C(8,5)·C(5,3): any three 4-subsets of a common 5-set are dependent — the dual space of RS₃ on 5 points is 2-dimensional) + **wide triples, which all obey one structural law: every wide dependent triple is a PAIR-TRIANGLE** — (S₁,S₂,S₃) = (P∪Q, P∪R, Q∪R) for three disjoint 2-sets P,Q,R. Counts: μ₈ has **40** dependent triangles, the AP has **8** (visibly the equal-pair-sum triangles, e.g. {0,5},{1,4},{2,3} — the additive structure; the μ₈ ones include the equal-exponent-sum and antipodal families — exact determinant criterion to be derived).

**Why this is the right object:** a dependency λ^{S₃} ∈ span(λ^{S₁},λ^{S₂}) forces an affine relation among the three collision forms — constraining which γ-patterns are simultaneously realizable, i.e. exactly the census-limiting structure at sub-threshold q. The collision census of the window is governed by the **dual-vector matroid**, whose wide circuits are pair-triangles, whose count is an exact domain invariant, and which is richer for smooth domains (40 > 8) — the measured smooth census deficit, now with its exact combinatorial cause.

Round-7 queue: (a) derive the pair-triangle dependency criterion in closed form (3×6 determinant over the union — a cross-ratio condition on the three pairs); (b) prove the universal pair-triangle law (wide circuits ⟹ triangle structure); (c) the μ₈ triangle census 40 as a theorem (rotation orbits of the criterion); (d) census-from-matroid: max realizable scalar patterns given the circuit list.

=== COMMENT 106 | lalalune | 2026-06-11T14:03:02Z ===
## O151 — Parseval restored (anti-laundering) + the tower threshold halved: unconditional census now reaches n = 128 at production fields

Two-part push:
1. **Restoration.** `KKH26ParsevalThreshold.lean` (the A3 resolution, 520 lines) had been pruned by the #353 cleanup as 'refuted/superseded' — it is neither. Restored verbatim, compiles axiom-clean. Logged as an anti-laundering lesson: prune-commit 'superseded' claims need the same grep-the-theorem scrutiny as 'proven' claims.
2. **The sharpened tower** (`tower_closed_finite_parseval`, axiom-clean, full build): the finite-field dyadic classification now holds above `(2^m)^{2^{m−2}}` — exponent halved against the ℓ¹ tower. At m=5: 2⁶⁴ → 2⁴⁰; m=6: 2¹⁶⁰ → 2⁹⁶; and m=7 gives 2²²⁴ < 2²⁵⁶, so **at production field sizes the unconditional-census layer now covers smooth domains up to n = 128**, one full fold scale deeper than before. The generic ℓ² engine (`not_isRoot_of_l2On_parseval_lt`) is reusable by every resultant-threshold consumer in the cone.

Surface (iii)'s certified-count frontier moves correspondingly: the s ∈ [64,256] uncertainty band tightens at its lower edge, with the in-tree stratified counts now unconditional one scale further.

=== COMMENT 107 | lalalune | 2026-06-11T14:03:57Z ===
## ROUND 4 SLATE: nine new hypotheses from the staircase campaign's discoveries (per the standing discipline — round-1 slate fully decided: R1✅ R2☠ R3☠ S1✅ S2-resolved S3✅ N1-brick✅ N2-brick✅ N3-brick✅)

**Grounding:** this session established (i) the exact linear staircase below half-distance (bands 1–2 universal theorems; b≥3 blueprinted at d ≥ 2b+1); (ii) the **MDS-vs-general separation at d = 2b** (machine-witnessed — ε_mca below Johnson is NOT a function of (n,d,q) alone); (iii) the projective symmetry layer; (iv) the syndrome-quotient factorization. The new slate climbs from the staircase toward the window.

### Reasonable (existing math, insightful use)
- **R4.1 — the MDS rank lemma.** Prove `MDSStaircaseConjecture` at b=3: the syndrome-equality system's kernel at RS always zeroes a puncture (verified by directed search at two instances; the general statement is a structured Vandermonde rank fact). *Completes the MDS staircase below UD.*
- **R4.2 — the general assembly + induction.** Mechanical completion of b=3 at d ≥ 2b+1 (infrastructure + blueprint landed), then induction: the full linear staircase ε_mca = (⌊δn⌋+1)/q below half-distance for all linear codes.
- **R4.3 — the boundary-row law.** At d = 2b−1: ε_mca = n/q exactly (lower: generalize the cocycle/weight-(2b−1) construction; upper: the antichain engine + boundary structure). *Pins the staircase's first break.*

### Novel (new mathematics)
- **N4.1 — the matroid invariance conjecture.** All landed staircase phenomena (trichotomy, separation, doubled-column attack) are matroid data of the code. Conjecture: **below Johnson, ε_mca is an invariant of the code's matroid**, determined by the multiset of small cocircuits; the strip UD→Johnson is where the cocircuit census transitions polynomial→exponential. *If true, δ*-from-below becomes matroid enumeration — and explains WHY the prize fixes RS (a specific matroid).*
- **N4.2 — the strip configuration-rank law.** Beyond UD, extremal bad families are alignment configurations in the syndrome quotient (the doubled-column attack = rank-1 fiber alignment). Conjecture: strip ε_mca = (max alignment dimension)/q, computable from the GRS joint-weight enumerator — the first quantitative handle on the bands between UD and Johnson.
- **N4.3 — the per-band orbit-count law.** The projective census of band-b maximizers: one GL₂-orbit per band below UD (band-1/2 data consistent); the orbit count's first growth marks the Johnson transition. *Falsifiable today at n=8 with the canonical-form enumeration.*

### Synthetic (in-repo unifications)
- **S4.1 — staircase ⟷ KKH26.** The boundary-explosion families (core-free spikes + weight-(2b−1) corrections) and the KKH26 sums-of-roots-of-unity bad lines are one construction at two scales; unification gives exact strip heights at smooth domains via the Lam–Leung census (landed S1 lane).
- **S4.2 — the matroid restatement.** Recast all staircase theorems as matroid-minor statements and probe-verify cocircuit-census determination at small instances (the falsification channel for N4.1, cheap).
- **S4.3 — equivariance × staircase.** Canonical-form enumeration per band (syndrome quotient × projective orbits) to make n = 12+ exact band probes feasible — the data engine for everything above.

**Rankings.** Ease (easiest first): R4.2 → S4.3 → S4.2 → R4.1 → R4.3 → N4.3 → S4.1 → N4.2 → N4.1. Promise (most first): N4.1 → N4.2 → R4.3 → S4.1 → R4.1 → R4.2 → N4.3 → S4.2 → S4.3. **Queue (ease×promise): R4.2 → R4.1 → S4.2 (N4.1's falsifier) → R4.3 → N4.3 → S4.1 → N4.2 → N4.1.**

Execution resumes at R4.2 (the b=3 Fin-4 assembly, blueprint in `MCABandThreeInfra.lean`).

=== COMMENT 108 | lalalune | 2026-06-11T14:05:33Z ===
## Red-team cycle 3 (O152): the two-family law survives the structure-free test

Harshest universality check: (11,5,2) — **prime** domain order (μ₅ ⊆ F₁₁), no 2-adic tower, no fibers. The exact profile {10, 2, 1} equals max(staircase, census) at every rung, and the census values are *exactly* the prime-order Lam–Leung predictions: census(5) = 1 (the full-group vanishing, the unique prime-5 relation), census(4) = 0 (no proper vanishing at prime order), census(3) = 10 (unconstrained, all sums distinct).

**Scoreboard: nine instances, 14+ field-combinations, zero deviations** — across 2-power (4, 16, 32), composite (6, 12), and prime (5) domain orders. The structural census theory extends verbatim beyond 2-power domains: the vanishing-sums classification swaps in per prime factor of n (the general-n tower would run Lam–Leung at each prime in the factorization — the formalization template exists for p = 2 at all depths).

The conditional production answer remains as priced (sup-extremality + s ≥ 256 counts + the floor wall), but its falsifiable surfaces keep surviving every attack the exact-computation frontier can currently mount.

=== COMMENT 109 | lalalune | 2026-06-11T14:05:48Z ===
## MonomialDomination survives falsifier round 1 (probe pushed)

`probe_monomial_domination_falsifier.py` — binomial-row attack stacks (u = x^{s₁} + c·x^{s₂}, structured (s₁,s₂) from the maximizer table, 7 coefficients including ±1, ±2, g^{±1}; plus binomial second rows) at (16,4), p ∈ {97,193}, agreements a ∈ {7,8,10}:

| cell | monomial max | best attack | verdict |
|---|---|---|---|
| all 6 (2 fields × 3 agreements) | 16/16/8 | **ties exactly** (16/16/8) | survives |

The binomial perturbations collapse onto their dominant pair — never exceed it. Consistent with the surface's design: the named hypothesis stands, now with an adversarial scan on top of the maximizer audits. Next falsifier escalation (queued): 3-row-structured stacks and random-stack sampling at the same cells; the equivariance route toward *proving* domination (orbit normal forms) remains the constructive path.

=== COMMENT 110 | lalalune | 2026-06-11T14:08:14Z ===
## The census programme now has its map: `docs/wiki/census-programme.md`

Consolidation push (the promote-learnings rule, and the direct lesson of the Parseval mis-pruning): the full δ* census architecture is now documented in one navigable page — the 13-layer theorem stack (exact pin → symmetry → three census laws → fiber structure → char-0 classification → both towers → both thresholds → bracket → crossing pin → staircase), the empirical layer (O135–O152 with the probe inventory), the conditional production answer with its three priced surfaces, and the working rules that cost real debugging time (including the landing protocol under sibling races and the ≥3-primes/char-0-anchor structurality test).

Campaign state at this checkpoint:
- **Proven**: 12+ axiom-clean theorem files on the census side this campaign, ending at `tower_closed_finite_parseval` (unconditional census to n = 128 at production fields).
- **Red-teamed**: 3 cycles — one genuine refutation-and-correction (the two-family merge), two survivals (composite-n and prime-n structure-free tests); the corrected law stands at 9 instances / 14+ field-combos / zero deviations.
- **Conditional answer**: δ* = 1 − a_c/n at the true-census crossing; if the char-0 forecasts hold at s* ≈ 256, δ* = capacity − c(ρ) with c constant — a sharper, falsifiable claim than the published Θ(1/log n) phrasing.
- **The three surfaces**, in decreasing tractability: the s ≥ 256 counts (TZ-or-lacunary-gated), the per-prime halo below threshold (norm-divisor counting, mechanism verified), and sup-extremality — which the CS25 coupling makes equivalent in its regime to the 25-year beyond-Johnson wall. The programme has reduced everything else to these.

=== COMMENT 111 | lalalune | 2026-06-11T14:08:16Z ===
## MonomialDomination falsifier round 2: random-stack sampling — survives with a 2.7× margin

3000 uniformly random stacks at the strongest cell ((16,4), a=7, p=97, seed 357): **best random count = 6 vs monomial max = 16**. Histogram: {0: 1005, 1: 1045, 2: 631, 3: 227, 4: 71, 5: 17, 6: 4} — generic stacks carry O(1) bad scalars with an exponential-looking tail; the monomial pairs sit at 16 = n, far outside the cloud.

Reading: the surface's two falsifier rounds (structured binomial + random) both leave the monomial family extremal with margin. The bad-scalar mass is *concentrated on the symmetric stacks* — which is precisely what the equivariance route to a domination **proof** needs (the orbit-normal-form argument: generic orbits have generic, small bad sets; symmetric orbits reduce to pairs). The campaign's standing conditional answer (pin v3) holds with strengthened empirical support.

Session complete summary for this lane — δ\* state of the art after the arc:
- **Theorems:** lower staircase on [0, 1/2] (sub-granularity 1/q, second band 2/q, ladder (n/g)/q on [UDR, 1/2], floor n/q at 1/2−1/n); radius quantization; census/excess/gap laws (the full monomial landscape); the bracket+jump engines; the v3 conditional pin with the crossing's bad half discharged.
- **One named open surface:** `MonomialDomination` (2 falsifier rounds survived; equivariance = constructive route).
- **One named numeric core:** the punctured-band monic-cofactor count over μ_n at production scales (where collision census / norm spectrum / Lam–Leung converge).

δ\* = the monomial-census crossing, conditional on exactly those two.

=== COMMENT 112 | lalalune | 2026-06-11T14:09:00Z ===
Delivered another #357 increment on main: commit bfac95998 (feat(#357): name high-rate subgranularity branch).\n\nWhat landed:\n- Added `ProximityGap.MCAStaircaseCollapse.epsMCA_rs_highRate_subgranularity`: for high-rate RS `RS[F,D,n-2]` with `n >= 4`, every `δ < 1/n` has exactly the universal floor `ε_mca = 1/q`.\n- This explicitly completes the below-first-rung half of the staircase-collapse story already covered above `1/n` by `epsMCA_rs_highRate_plateau`: `1/q` below the first lattice point, then `n/q` on the plateau.\n- Added the axiom audit line; it reports only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.\n- Refreshed generated declaration/dedup metadata after syncing through the moving main tip.\n\nChecks run while preparing/pushing this increment:\n- `lake build ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseCollapse`\n- `./scripts/check-imports.sh`\n- `python3 scripts/kb/extract_declarations.py`\n- `python3 scripts/kb/extract_lean_citations.py`\n- `python3 scripts/kb/find_dedup_candidates.py`\n- `python3 scripts/kb/check_generated.py`\n- `git diff --check`\n- `python3 scripts/sorry_census.py --fail-on-holes`\n- `python3 scripts/forbidden_tokens.py`\n\nNotes: main was very hot during this, so I rebased repeatedly onto the latest #357/#354 commits before the final successful push.

=== COMMENT 113 | lalalune | 2026-06-11T14:12:27Z ===
## O153 — the band-j collapse theorem (proof complete, formalization queued): the staircase side of the profile law is now a theorem

First general sup-side result of the campaign. **Theorem:** for codes of distance d > 4j, every stack has at most j+1 bad scalars on band j (δn ∈ [j, j+1)) — so with the in-tree (j+1)-spike lower bound, **ε_mca·q = j+1 exactly on band j** for high-distance codes.

Proof core (full details in DISPROOF_LOG O153): j+2 bad scalars force per-line error words with the **rigid relation w_γ = w_γ₁ + (γ−γ₁)·v** (cross-consistency λ′(w_γ−w_γ₁) − λ(w_γ′−w_γ₁) ∈ C has weight ≤ 4j < d, hence vanishes); then either |supp v| ≥ j+1 and the affine-injectivity pinch gives t·j ≥ (j+1)(t−1) ⟹ t ≤ j+1, or |supp v| ≤ j and the pair-clause criterion caps the bad set by |supp v|.

Honest hypothesis audit: the data shows the conclusion holds even at d < 4j ((13,12,6) band 2), so the distance condition is not tight — the 4j cross-relation step is the binding constraint, sharpening open. In-hypothesis checks all pass; production RS (huge distance) has every staircase band of interest in-hypothesis.

**Strategic consequence:** sup-extremality — surface (i), 'THE wall' — has been **reduced from all radii to the census band alone**: for high-distance codes, every band below the crossing is now exactly pinned by theorem, and the conjectural content of the profile law lives only where the census dominates. The Lean brick (unique-short-coset-word + the rigid relation + two counting cases — all elementary on the in-tree distance API) is the next queued formalization.

=== COMMENT 114 | lalalune | 2026-06-11T14:14:32Z ===
## R4.2 PROVEN: the band-3 collapse theorem (`MCABandThreeAssembly.lean`, axiom-clean, lake-build green)

**`badScalar_card_le_three_of_dist7`** — every linear code with no nonzero codeword on ≤ 6 points (distance ≥ 7 = 2b+1) has **at most 3 bad scalars per stack** at every radius with δ·n < 3. Corollaries: **`generalStaircase_b3`** — the first open instance of `GeneralStaircaseConjecture` is now a theorem — and **`epsMCA_le_three_div_card_of_dist7`**: ε_mca ≤ 3/|F| on the whole third band, **sharp in both the value (spike floor) and the distance threshold (the d = 6 doubled-column counterexample)**.

The proof simplified beautifully during assembly: the planned two-distinct-deep-points pigeonhole turned out to be unnecessary — **one deep point kills outright** (`hdeep_dead`): its own membership triple supplies the three cored scalars (degenerate hosts are nested → dead; otherwise hosts are `{j, p_i}` with distinct privates → `cored_collapse`, which needs only d ≥ 5). So the classification collapses to: every scalar's line point is a codeword — and two of those are already contradictory. The 16-branch case tree vanished.

**The staircase below half-distance now stands as:**
| band | general codes | status |
|---|---|---|
| 1 | ε_mca = 1/q (any proper code) | **theorem** |
| 2 | = 2/q (d ≥ 4) | **theorem** (exact, both sides) |
| 3 | ≤ 3/q (d ≥ 7); = n-explosion at d = 5; counterexample at d = 6 | **theorem** (upper), sharp |
| b ≥ 4 | conjectured ≤ b/q at d ≥ 2b+1 | the induction is now visibly mechanical: extract → extension engine → deep point → cored — each generalizes with supports 2(b−1)-sized |

Round-4 queue continues: R4.1 (MDS rank lemma — restores d ≥ 2b for RS), band-3 exact lower at d ≥ 7 (the 3-spike instance), then the general-b induction and the UD→Johnson strip.

=== COMMENT 115 | lalalune | 2026-06-11T14:15:37Z ===
## THE FIRST EXACT MONOMIAL-SLICE CENSUS (`HalfPairSliceExact.lean`, axiom-clean, on main) — the ladder is TIGHT at its deepest rung

At the **unique-decoding radius exactly** (δ = 3/8 = (1−ρ)/2) of the rate-1/4 smooth code on μ₈ ⊆ F₁₇, the half-order pair (X⁵, X⁴) at agreement 5 = m+1 (the g = 1 ladder rung's deepest reach):

- **`halfPair_badSet_eq`** — the law-bad set is **exactly μ₈** (kernel `decide` through the affine bridge `bad_iff_core` / `exists_eq_X_add_C_of_natDegree_le_one`);
- **`halfPair_badCount`** — count exactly **8 = n**: the splitting-ladder lower bound n/gcd(1,n) is **tight**, two-sided, machine-checked.

The flat-n law for half-pairs — measured by the take-over probes at (16,4), predicted by the ladder — is now an exact theorem at this instance, and −μ₈ = μ₈ makes the bad set literally the domain orbit (the S3 orbit-count picture realized). One honest scope note: the same two-sided question *inside* (UDR, Johnson] (a = 4 here) needs the no-joint clause — the pure-agreement census saturates at this field size (all 17 scalars admit a 4-point affine agreement; measured) — so in-window exact points need either the mcaEvent-level decide (heavier kernel work) or larger fields. That's the registered next rung of the exact programme.

Session ledger, final form (14 artifacts, all axiom-clean, all on main): the two refutation files, the four pin-chain files (incl. both red-team kills), the three ladder files, the three census-law files, and this exact point — plus 8 probe scripts with cross-engine verification. The δ\* statement stands as posted: **the monomial-census crossing radius, conditional on MonomialDomination (2 falsifier rounds survived) + finite numerics, with the crossing's bad half and the full lower staircase as theorems.**

=== COMMENT 116 | lalalune | 2026-06-11T14:16:58Z ===
## Pin-v3 surface note: the floor events ARE monomial — `MonomialDomination` is sound at the sub-granularity band

Self-check after landing (the red-team discipline, applied preemptively): at δ = 0 every proper code has ε_mca = 1/|F| via floor stacks like (0, e₃) — *not obviously monomial pairs*, so does `MonomialDomination` die at the floor the way the census surface did (red-team kill #1)?

**No — the constant monomial saves it.** `monomialEps` ranges over exponents s, t ∈ [0, n): the pair **(X⁰, X^t) with k ≤ t < n** fires the event at γ = 0 (line = 1 ∈ C explainable on univ; no joint explanation since x^t ∉ C), so monomialEps(δ=0) ≥ 1/|F| = ε_mca(δ=0) — domination holds with equality at the floor. At the R1 instance (F₅, μ₄, k=2) all the numbers line up: ε_mca(0) = 1/5 = monomialEps(0) via (X⁰, X³); and at the jump both equal 4/5 (O137: (X³, X²) attains the worst case). The v3 surface passes the very test that killed the v1/v2 census surfaces.

**Current standing of the campaign's conditional answer** (for the continuation context): δ\* = the monomial-census crossing radius — conditional on `MonomialDomination` (3 checks passed: binomial attacks, random stacks, floor-band consistency) + finite per-scale numerics. Theorems below it: the full lower staircase ([UDR, 1/2] ladder + n/q floor + universal bands 1–2 + the fleet's band-3/band-j collapse from the other side), radius quantization, the census/excess/gap laws, the jump/bracket engines, the exact points (δ\*(F₅) = 1/4; the UDR slice census = μ₈ at F₁₇). Open: MonomialDomination (equivariance route), the punctured-band cofactor asymptotics (Johnson–capacity), the band-j formalization sweep (fleet, in flight).

=== COMMENT 117 | lalalune | 2026-06-11T14:17:29Z ===
## THE UNIVERSAL THIRD BAND (`MCABandThreeExact.lean`, axiom-clean): ε_mca = 3/|F| exactly on [2/n, 3/n) for every distance-≥7 linear code

The triple-spike pencil `u₀ + γ•u₁ = Σ_x (γ_x − γ)•single i_x a` realizes three bad scalars (each γ_x vanishes its own spike; the explaining second row is trapped inside the three slots — weight ≤ 3, dead by distance); the collapse theorem closes the sandwich.

**The MCA staircase scoreboard — first three steps now exact theorems universally:**
| band (δ·n ∈) | value | hypotheses | status |
|---|---|---|---|
| [0, 1) | 1/q | any proper linear code | **exact** |
| [1, 2) | 2/q | d ≥ 4 | **exact** (d-threshold sharp: d=3 explodes to n) |
| [2, 3) | 3/q | d ≥ 7 | **exact** (d-threshold sharp: d=6 doubled-column counterexample; d=5 explodes to ~n) |

Every production-scale RS code satisfies all three rows. The emergent pattern — exact band b at d ≥ f(b) with f(1)=1, f(2)=4, f(3)=7 — suggests **f(b) = 3b−2** (arithmetic: the triple-c* support 3(b−1) < d), NOT the originally conjectured 2b+1; the b=2,3 data are consistent with both (4 = 3·2−2, 7 = 3·3−2 = 2·3+1 coincide at b=3!). Pre-registered for round 4: at b = 4 the two predictions separate (3b−2 = 10 vs 2b+1 = 9) — the d = 9 band-4 instance decides which law governs. The boundary-explosion rows interpolate below.

19 axiom-clean files this lane. Next: the b=4/d=9 decision probe, R4.1 (MDS rank lemma), and the matroid falsifier (S4.2).

=== COMMENT 118 | lalalune | 2026-06-11T14:20:01Z ===
## ROUND 4 CAPSTONE: `GeneralStaircaseConjecture` (d ≥ 2b+1) REFUTED at b=4 — THE 3b−2 LAW unifies the entire staircase

The pre-registered decision experiment between f(b) = 3b−2 and 2b+1 (which coincide at b=3) is decided: the **tripled-column [15,3,9] moment-curve code** over F₁₁ (columns (1,t,t²) each repeated three times, t ∈ {0,…,4}; min weight 9 verified) admits a **5-bad band-4 stack at d = 9 = 2b+1**: γ = (0,1,2,3,4), e = (1,1,1,8,8,8,2,2,2,8,8,8,1,1,1) — honest end-to-end badness check passed. The syndrome system (48 equations on 15 unknowns) has admissible kernel precisely because the moment-curve direction arrangement matches the Vandermonde relation-space arrangement — the same mechanism as the b=3 doubled-column attack, one dimension up.

**THE UNIFIED GENERAL-CODE LAW** (every datum now coheres):

| b | collapse to b/q | explosion family |
|---|---|---|
| 2 | **proven** at d ≥ 4 = 3·2−2 | 1-tupled (cocycle) at d = 3 |
| 3 | **proven** at d ≥ 7 = 3·3−2 | 2-tupled (doubled-column) at d = 6 |
| 4 | conjectured at d ≥ 10 = 3·4−2 | 3-tupled at d = 9 (**this refutation**) |
| b | d ≥ 3b−2 (triple-c*-support arithmetic) | (b−1)-tupled columns at d = 3b−3 |

The landed b=2,3 theorems *are* the 3b−2 law's first instances — "2b+1" was a b=3 numerical coincidence, caught by the pre-registered separation experiment. The b=4 collapse at d ≥ 10 should follow the landed deep-core proof shape (triple supports 3(b−1) = 9 < 10), with `cored_collapse` generalized to (b−1)-point cores.

**Structural payoff:** the explosion witnesses are maximally non-MDS — parallel matroid classes of size b−1. The gap between the general threshold (3b−2) and the RS/MDS threshold (2b, directed-search-supported, unrefuted) is exactly *parallel-class capacity* — the matroid-invariance hypothesis (N4.1) is now the campaign's structural frontier, and the staircase below half-distance is provably a matroid-sensitive quantity.

Next: formalize the b=4 refutation witness (¬GeneralStaircaseConjecture in Lean), state the corrected `TheGeneralStaircaseLaw` (d ≥ 3b−2) surface, and generalize the collapse machinery to all b.

=== COMMENT 119 | lalalune | 2026-06-11T14:22:29Z ===
## THE BAND COLLAPSE THEOREM FORMALIZED (`BandCollapse.lean`, axiom-clean, full build)

O153's paper proof is now machine-checked — **with the distance condition sharpened from 4j to 3j** by the unified argument (the binding bracket has support ≤ 3j, and no short-word-uniqueness step is needed):

> **`badScalar_card_le_band` / `epsMCA_le_band`**: for codes in which every nonzero codeword has weight > 3j, every stack has at most j+1 bad scalars at radii forcing witness sets of size ≥ n−j; hence ε_mca ≤ (j+1)/q.

With the in-tree (j+1)-spike lower bound, **the staircase law ε_mca·q = j+1 is exact on band j for high-distance codes — at every band** (previously machine-proven only at bands 0–1). The machine proof runs: per-event error words → the bracket-vanishing rigid relation w_γ = w_γ₁ + (γ−γ₁)·v → the injection (witness sets must hit supp v, else the explicit pair explains the stack) → the pinch (one zero per point) → t·j ≥ t(t−1).

**Surface (i) of the conditional pin is now reduced, by machine-checked theorem, to the census-dominance regime alone.** For production RS (huge distance) every staircase band is in-hypothesis; the conjectural content of the two-family profile law survives only at the crossing scale, where the census takes over. The campaign's sup-side ledger: bands exact at every j (this theorem + spike LB), census exact above threshold (the towers + gap law), the crossing pinned conditional on census-band extremality — the last genuinely-open sup question, which the CS25 coupling ties to the beyond-Johnson wall.

=== COMMENT 120 | lalalune | 2026-06-11T14:24:44Z ===
## Round 7 keystone LANDED: THE DUAL PENCIL LAW, both halves (`MCADualPencilLaw.lean`, 5/5 axiom-clean)

**`dual_combo_eq_zero_iff` (the transform):** for a pair-triangle (P∪Q, P∪R, Q∪R), the dual-vector combination α·λ^{P∪Q} + β·λ^{P∪R} + γ·λ^{Q∪R} vanishes as a *vector* iff W = α·q_R + β·q_Q + γ·q_P vanishes as a *polynomial* — a degree-≤2 quadratic against six distinct union points. (The local law: each live coordinate, times a nonzero product, evaluates W.)

**`dependent_iff_collinear` (the criterion):** a nontrivial dependency exists **iff the three pair-points (e, m) = (sum, product) are collinear in the (e,m)-plane** — the three monic pair-quadratics lie in a pencil. Backward direction is fully constructive (sum-difference coefficients generically; product-differences on the vertical case, with nontriviality from `pair_invariants_ne`: disjoint pairs cannot share both invariants).

### What this closes and what it opens

The wide circuits of the collision matroid — the exact, field-independent invariant separating smooth from generic domains in the window's collision regime — are now a **closed-form plane-incidence condition**. The μ₈/AP censuses (40 vs 8) are now *theorems-in-waiting about collinear triples among explicit point configurations*:
- pairs of n-th roots of unity: m = g^{i+j} constant on exponent-sum classes ⟹ **20 horizontal collinearities** (s odd: C(4,3)·4 = 16; s even: 4);
- antipodal pairs {x, −x}: e = 0 ⟹ **4 vertical collinearities**;
- **16 slanted** μ₈-specific lines (the genuinely new arithmetic — cross-class incidences of the root-of-unity pair configuration);
- the AP's 8 = the equal-sum verticals of an arithmetic progression.

**The δ* programme's open core is now: count collinear triples (and higher incidence structure) of the configuration {(ζ^i + ζ^j, ζ^{i+j})} ⊂ F² for smooth μ_n** — a classical-flavored incidence-geometry problem about explicit algebraic point sets, fully replacing the original 'beyond-Johnson list decoding' formulation at sub-threshold q. Round-8 queue: (a) the μ_n horizontal/vertical collinearity censuses as theorems (the group-structure halves are elementary with the landed machinery); (b) the slanted-line classification (where the new arithmetic lives — the (e,m) configuration is the image of the μ_n × μ_n torus under (e,m), i.e. points on the curves e² ∈ ... related to Chebyshev/Dickson parametrizations: m = ζ^s fixed gives e = ζ^j + ζ^{s−j} — a Dickson curve section); (c) census-from-matroid: from the circuit list to the exact sub-threshold ε_mca.

=== COMMENT 121 | lalalune | 2026-06-11T14:26:52Z ===
## b=4 refutation FORMALIZED (`MCAGeneralStaircaseRefuted.lean`, axiom-clean, lake-build green)

**`generalStaircaseConjecture_refuted`** — the d ≥ 2b+1 surface is now machine-refuted, completing the second full refute-and-correct cycle on the staircase threshold (2b → 2b+1 → **3b−2**), each step decided by a pre-registered experiment and each refutation an explicit decide-backed witness:

- `T3` — the tripled-column [15,3,9] moment-curve code over F₁₁; `T3_noWeight` proven by the **direction pigeonhole** (a live direction's whole triple lies in the support, so 3·|live| ≤ 8 forces ≥ 3 vanishing directions, and any three distinct moment-curve directions kill the coefficients — `three_dirs_kill`, decide);
- five uniform bad events `mcaEvent_t : ∀ g : Fin 5, …` (one `fin_cases g <;> decide` script), witnesses = punctured triples, explaining rows trapped on three directions;
- the corrected surface **`TheGeneralStaircaseLaw`** (d ≥ 3b−2, b ≥ 4) — whose b = 2, 3 instances are *already the landed theorems*, with the (b−1)-tupled witnesses showing sharpness at 3b−3 for b = 2, 3, 4.

19 axiom-clean files this lane. The staircase ledger: bands 1–3 exact universally (thresholds 1, 4, 7 = 3b−2, each sharp); band-4 collapse next at d ≥ 10 (the deep-core machinery generalizes — triple supports 3·3 = 9 < 10); the m-tupled/matroid structure is the new invariant frontier; the RS/MDS lane (d ≥ 2b) remains open-supported. Queue: b=4 collapse → MDS rank lemma → matroid falsifier → the UD→Johnson strip.

=== COMMENT 122 | lalalune | 2026-06-11T14:28:02Z ===
## Round 16 (fold-lane): THE UNIVERSAL SPIKE FLOOR — the bad side of the entire granularity ladder, every code at once

`UniversalSpikeFloor.lean` (`8f4026a5c`, 3/3 axiom-clean, 0 sorry). The staircase program's lower halves, all bands in one theorem:

- **`mcaEvent_spike`** — the `j`-spike construction (`u₀ = Σ aₗ•b·e_{pₗ}`, `u₁ = Σ b·e_{pₗ}`): at each of the `j` distinct scalars `γ = −aₗ`, the line vanishes at `pₗ` and off the support, the zero codeword explains it on `n−j+1 ≥ (1−δ)n` positions, and any joint explanation of `u₁` would be a weight-≤-j codeword — zero by distance — contradicting `b ≠ 0`.
- **`epsMCA_ge_j_div_card`** — hence `ε_mca(C, δ) ≥ j/|F|` for every `δ·n ≥ j−1`, **every** linear code with no nonzero codeword of weight ≤ j (i.e. distance > j — every RS code at every `j ≤ n−k`).
- **`mcaDeltaStar_le_granularity`** — the universal δ* bracket: **for every `ε* < j/|F|`: `mcaDeltaStar(C, ε*) ≤ (j−1)/n`.**

This generalizes the band-1 floor and the sibling double-spike (j = 2) to all bands with one engine, and makes the bad side of every granularity pin — including both landed pins — an instance of a single universal theorem. Every future pin now needs only its good side.

**What remains for the full staircase law** (the candidate closed form, `δ* = the last linear band edge`): the matching **universal collapse** — `ε_mca ≤ j/q` on band j under a distance condition (the siblings' band-2 collapse is the j = 2 case; the trichotomy says the condition is real). With both halves, `mcaDeltaStar` is pinned **exactly** on the whole granularity ladder for every sufficient-distance linear code — the first closed-form δ* theorem over a code-and-ε\*-family. The j-spike floor just landed is half of that theorem.

Still in flight: the widened band-3 sweep at (17,8,4) (decides whether the staircase jumps to `n/q` when the distance condition fails at j = 3, mirroring the d = 3 trichotomy at band 2). Open queue: universal collapse ≥ band 3, C2-S, C2-N, S2(b′) wirings.


=== COMMENT 123 | lalalune | 2026-06-11T14:29:40Z ===
## IN-WINDOW SATURATION, EXACT (`SmoothWindowSaturation.lean`, axiom-clean, on main) — the first unconditional exact in-window ε_mca value for a SMOOTH-domain RS code

At `RS[F₁₇, μ₈, 2]` (ρ = 1/4, window (1/2, 3/4)), at the grid radius **δ = 5/8 strictly inside the window**:

**`epsMCA_window_saturates`: ε_mca(C, 5/8) = 1 exactly.** The pair (X⁴, X²) is MCA-bad at *every* scalar λ ∈ F₁₇ — seventeen kernel-checked certificates (3-point witnesses, explicit affine explanations, one row affinely inexplicable per witness). Upper half trivial. Ledger: **δ\*(C, ε\*) ≤ 5/8 for every ε\* < 1, unconditionally** (`mcaDeltaStar_le_of_window_saturation`).

This is the smooth-domain companion to the sibling's F₁₁ interior pin (`mcaDeltaStar_window_interior_eq`): together they give the first two exact in-window values — one non-smooth and non-degenerate (10/11 at the F₁₁ instance), one smooth and saturated (1 here). The O139 'small fields saturate above Johnson' folklore — the reason the prize fixes |F| ≥ 2^something — is now a two-sided theorem at a genuine smooth instance. The full monomial table behind it (probe, mcaEvent level, (17, μ₈, 2)): a=3 → **17 = q** (this theorem) · a=4 (Johnson) → 9 at (X⁴,X³) · a=5 (UDR) → 8 = n (the exact-slice theorem) · a ≤ 6 → 1 (floor).

**Plus a domination data point from the structural side:** stacks of the factorizable form (f·x, f) have line = f(x)·(x+γ) — affine on each fiber of f, with the fiber-plus-crossing witness mechanism; among these, the half-pair (f = x^m, 2 fibers of size m) maximizes both reach and count, and richer-fibered f (e.g. f = x⁸+x⁴ at n=16: four 4-fibers, line = (x+γ)(x⁸+x⁴)) reach strictly less deep with the same count. The factorizable class is therefore *dominated by its monomial member* — a provable instance of `MonomialDomination` on a natural non-monomial class, and the template for the structure-theorem route. Registered as the next formal target.

=== COMMENT 124 | lalalune | 2026-06-11T14:29:48Z ===
## Round 8 LANDED: the complete μ_n wide-circuit supply (`MCAIncidenceCensus.lean`, 5/5 axiom-clean)

The slanted family — the 'genuinely new arithmetic' — fell to a clean mechanism. Probe classification of μ₈'s 16 slanted circuits revealed: **every slanted line passes through exactly one vertical-axis point**, i.e. each slanted circuit = one antipodal pair {w, −w} + two pairs of one difference class {ζ^i, ζ^{i+d}}, {ζ^j, ζ^{j+d}}, and the collinearity condition is the **exponent relation w² = ζ^{i+j+d}** — derived via two-root-sum rigidity (the campaign's Lam–Leung mechanism, in its fourth appearance), with the determinant telescoping by pure exponent arithmetic.

Landed (all instant or near-instant corollaries of the pencil criterion, valid at EVERY scale n):
- `dependent_of_equal_products` — horizontal lines (exponent-sum classes of μ_n);
- `dependent_of_equal_sums` + `dependent_of_antipodal_triple` — vertical lines;
- **`dependent_of_slanted`** — the slanted family via the exponent relation.

**The μ₈ census 40 = 20 + 4 + 16 is now fully theorem-supplied**, and the supply side of the wide-circuit census is closed-form at all n. What remains for the *exact equality* census at general μ_n (supply = demand) is two-root-sum rigidity as an upper mechanism (no OTHER collinearities exist above an explicit p-threshold) — which is precisely the two-element case of the landed char-0 collision law, transferred mod p above a KKH26-style resultant threshold.

**The δ* programme state**: the collision matroid of the window's sub-threshold regime now has (i) its circuit law (pencil criterion, closed form), (ii) its complete circuit supply over smooth domains (three families, all scales), (iii) its census decomposition verified at toy scale. The remaining chain to production-scale sub-threshold ε_mca: circuit-list → realizable-γ-pattern count (census-from-matroid, an LP/combinatorial optimization over the circuit hypergraph) → exact ε_mca below the supply threshold. Round 9: formalize the two-root rigidity transfer + the census-from-matroid counting at the (8,3) cell as the template.

=== COMMENT 125 | lalalune | 2026-06-11T14:31:26Z ===
## Round 8 red-team at μ₁₆: families confirmed exactly where predicted — and the COMPLETE classification mechanism identified

Census at μ₁₆ ⊂ F₉₇ (exact, via the proven pencil criterion — counting collinear (e,m)-triples):

| family | predicted | measured |
|---|---|---|
| horizontal (8·C(8,3) + 8·C(7,3)) | 728 | **728** ✓ |
| vertical (C(8,3)) | 56 | **56** ✓ |
| slanted-form (antipodal + same-d + exponent relation) | — | 288 |
| **other** | — | **640** |
| total | — | 1712 |

The closed-form horizontal/vertical censuses are exact at the second scale. But the n=8 trichotomy was *small-scale luck*: at n=16 there are 640 collinear triples in richer families (e.g. diffs [1,2,10] with no antipodal pair; [1,1,4] with non-antipodal third pair). Honest verdict: `dependent_of_slanted` is correct supply but the slanted *classification* is incomplete.

**The complete mechanism (round-9 program, fully determined):** expanding the collinearity determinant with e_X = ζ^x + ζ^{x′}, m_X = ζ^{x+x′} gives (after the e_P m_P cancellation) a **12-term vanishing sum of 2^k-th roots of unity**. By the campaign's landed antipodal multiset law (`count_antipodal_of_sum_eq_zero` — char 0, transferred mod p above a resultant threshold), every such vanishing sum is **antipodally paired**: the complete line classification is the finite enumeration of perfect matchings of 12 explicit exponent forms (a combinatorial type list that is n-INDEPENDENT), and the census per type is a linear-congruence count in n. Therefore:

> **The production-scale wide-circuit census of smooth domains = Σ over matching types of explicit congruence-solution counts — closed-form at every n, derived entirely from machinery already landed** (pencil criterion + antipodal multiset law), conditional only on the mod-p transfer threshold (KKH26-style resultant bound, the same species as everything else).

Round 9: (a) enumerate the 12-term matching types (finite, mechanical — probe first, then the type list as a theorem via the multiset law); (b) the congruence-count census formula at all n; (c) mod-p transfer threshold; (d) census-from-matroid → exact sub-threshold ε_mca. The δ* collision regime is now a *terminating program*, not an open-ended search.

=== COMMENT 126 | lalalune | 2026-06-11T14:36:09Z ===
## THE MASTER STAIRCASE THEOREM (`MCAStaircaseMaster.lean`, axiom-clean, lake-build green): every band at once

**`collapse_level`** — one induction on the residual size r proves: r+2 distinct bad-scalar data with common core X, residual punctures ≤ r, and no nonzero codeword on ≤ |X| + 3r points are contradictory. The three structural facts that make a single recursion possible:
1. the parameterized extension engine `ext_at_general` needs only the support budget |X| + |P₁| + |P₂| + |P₃| ≤ m;
2. **coring preserves the obstruction sets verbatim** — `insert j X ∪ (P_a.erase j) = X ∪ P_a` — so the no-joint-explanation hypotheses descend unchanged through every level;
3. an unextendable residual point is hosted by all but at most one scalar (host pigeonhole), and each coring trades 3 budget for 1, losing at most one scalar — from r+2 scalars the recursion bottoms out at two scalars sharing a witness.

**`badScalar_card_le_of_dist`** (X = ∅, r = b−1): **every linear code with no nonzero codeword on ≤ 3(b−1) points (distance ≥ 3b−2) has at most b bad scalars per stack at every radius with δ·n < b** — the full linear staircase, all bands simultaneously, with `epsMCA_le_div_card_of_dist : ε_mca ≤ b/|F|`. The threshold is **sharp at b = 2, 3, 4** (the 1-/2-/3-tupled-column explosions at d = 3b−3), and the b = 2, 3 instances recover the previously-landed band theorems as special cases.

**The arc of this campaign, compressed:** conjecture (d ≥ 2b) → refuted (doubled columns) → corrected (d ≥ 2b+1) → refuted (tripled columns) → **the true law (d ≥ 3b−2), proven in full generality, sharp at three consecutive bands**. Two adversarial cycles, each decided by a pre-registered experiment, ending in one clean induction.

21 axiom-clean files this lane. What remains on the staircase: the general band-b exact lower (the b-spike, routine generalization), the boundary-explosion row values, the RS/MDS improved threshold (≤ 2b? — now sharply isolated as a *matroid* question), and above it all: the UD→Johnson strip, then the window.

=== COMMENT 127 | lalalune | 2026-06-11T14:36:44Z ===
## THE EXACT MCA CENSUS AT THE JOHNSON RADIUS (`JohnsonExactPoint.lean`, axiom-clean, on main) — and a reusable proof device

Two-sided, at δ = 1/2 = 1−√ρ on (F₁₇, μ₈, 2): **the mcaEvent-bad set of (X⁵, X⁴) is exactly μ₈, count 8 = n.**

- Positive side: eight probe-extracted size-4 certificates through the saturation builder.
- **Negative side — the new device:** the brute kernel decide (∀ witness sets × ∀ affine explanations) is infeasible. The proof goes through the **agreement-set maximality reduction** (`coreJ_of_mcaEvent`): any MCA witness T grows to the *full agreement set S of the affine fit through two of its points* — the line agreement is automatic, and the no-joint clause is **monotone under growth** (a joint explanation on S restricts to T). The event therefore implies a fit-indexed core with **no set quantifier** (≤ 56 fits instead of 163 witness sets × 289 affines), and ¬coreJ for the nine non-μ₈ scalars becomes a fast kernel decide. The reduction is generic — it converts mcaEvent-level negative results at any small instance from infeasible to routine, and is the natural device for scaling the exact programme to n = 16.

**The instance's exact profile is now closed across the whole structured regime:**

| δ | object | value | file |
|---|---|---|---|
| 3/8 = UDR | law census of (X⁵,X⁴), a=5 | = μ₈ (8) | HalfPairSliceExact |
| 1/2 = Johnson | **mcaEvent census of (X⁵,X⁴), a=4** | **= μ₈ (8)** | this |
| 5/8 ∈ window | ε_mca (full) | **= 1** (saturated, (X⁴,X²)) | SmoothWindowSaturation |

The flat-n law on [UDR, Johnson] is a closed two-sided theorem at this instance, and the window saturation boundary sits between 1/2 and 5/8 at q = 17 — the exact small-field picture, machine-checked end to end.

=== COMMENT 128 | lalalune | 2026-06-11T14:36:59Z ===
## Round 9(a) landed: the parabola stratification + the first NEGATIVE census law (`MCAParabolaStratification.lean`, 4/4 axiom-clean)

The geometric organization of the entire circuit census:

- **`parabola_law`**: every difference-d pair {ζ^i, ζ^{i+d}} lies on the explicit parabola e²·ζ^d = (1+ζ^d)²·m — the configuration Γ_n is a union of ⌊n/2⌋ parabolas, one per difference class, with the antipodal class degenerating to the vertical line e = 0 (since 1+ζ^{n/2} = 0). This also re-derives the vertical family conceptually.
- **`parabola_det_factor`** + **`independent_of_same_parabola`/`independent_of_same_diff`**: on a nondegenerate parabola the collinearity determinant factors as a **Vandermonde** — so **three pairs of one non-antipodal difference class are NEVER a wide circuit**. The first negative (upper-bound) law of the classification, probe-verified with zero violations at both μ₈ and μ₁₆.

**The census frame this fixes:** every wide circuit uses ≤ 2 points per nondegenerate parabola; the complete census is the line-incidence distribution Σ_L C(N_L, 3) over the parabola union, with:
- horizontal lines: exactly one point per parabola (N = ⌊n/2⌋ → the closed-form horizontal census, verified exactly at two scales);
- the vertical line: the degenerate parabola itself (N = n/2 → closed-form, verified);
- slanted lines: ≤ 2 points per parabola, incidence = bounded vanishing sums of 2^k-th roots, classified by the antipodal multiset law (the 12-term determinant expansion).

**Honest state of the terminating program:** supply families ✓ (3 landed), negative law ✓ (landed), census frame ✓ (fixed); remaining for the complete production-scale census: the slanted N_L distribution (matching-type list — the raw probe enumeration over-refines and needs the symmetry quotient; the geometric route via 2-2-2 secant conditions is the cleaner path), the mod-p transfer threshold, and census-from-matroid. Each is bounded, specified, and rests on landed machinery.

=== COMMENT 129 | lalalune | 2026-06-11T14:38:15Z ===
## State of the δ* proof after rounds 1–9 (24 axiom-clean files this campaign) — the honest production-scale map

### What is completely proven (machine-checked, on main)

1. **Below the window:** the complete threshold function of high-rate smooth RS at every (δ, ε*) — ε_mca = 1/q below 1/n, = n/q on [1/n, 1]; δ* = 1/n or 1. The first totally-determined family.
2. **The universal engines:** dead witnesses (floors ≥ k+1), the antichain law, the LYM ceiling C(n,t)/q (every linear code, δ ≤ 1/2 — covering the entire window), the witness-spread lower engine, full-layer supply ⟹ exact staircase, the jump-pin/certificates-meet reduction.
3. **Inside the window:** exact ε_mca values at four interior cells; the LYM ceiling attained by full layers above per-cell collision thresholds (≈ C(n,t)², birthday-verified).
4. **The collision regime's algebra:** the dual pencil law (wide circuits ⟺ (e,m)-collinearity), the parabola stratification (Γ_n = union of ⌊n/2⌋ parabolas), three supply families + the same-class negative law, all at every scale n; the horizontal/vertical censuses verified exactly at two scales.

### The production-scale structure (the honest map of what remains)

The window at production parameters splits by the **iterated two-regime law**:
- **q ≫ C(n,t)²:** ε_mca = C(n,t)/q exactly (proven conditionally on supply; supply probe-verified at every tested cell) ⟹ δ* = Johnson edge. *Not the prize regime* (needs super-exponential q).
- **prize q:** the census is collision-limited, governed by the circuit matroid whose law is now closed-form. The census deviations from the char-0 count are exactly **norm-divisibility events p | N(vanishing-sum expression)** — the same arithmetic species as the KKH26 s^{s/2} threshold and our O134 surplus law. At production n (= 2²⁰⁺), q < 2²⁵⁶ sits far below the norm bounds: the prize-scale census is the *structured deviation theory* of these divisibility events.

**So the complete production-scale δ\* problem now has this exact shape:** δ\*(ε\*) = the inverse staircase of the *collision-limited census* B(n, t, q) = (char-0 incidence census, closed-form via the parabola/pencil geometry) − (corrections counted by p | N(·) events) + (per-stack realizability from the circuit matroid). Every term is a named, formalized-or-specified object; the arithmetic depth is concentrated in the divisibility-event census — which is genuinely the same open mathematics as the additive-energy/BGK kernel this campaign has now met from five independent directions. That convergence — five lanes, one kernel — is the campaign's strongest evidence that the remaining object is *the* irreducible core, and the program around it is complete and terminating: any future progress on that kernel (ours or the literature's) now lands directly in the bracket ledger through the machinery built here.

Round-10 queue: slanted N_L via 2-2-2 secant conditions; the symmetry-quotiented matching-type list; the horizontal-census equality theorem at general n; census-from-matroid at (8,3); norm-threshold bounds for the 12-term sums.

