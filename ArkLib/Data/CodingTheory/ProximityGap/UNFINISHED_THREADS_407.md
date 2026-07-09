# UNFINISHED THREADS — Proximity Prize δ* master census (#407 ← #389/#400/#371/#357/#334/#232)

> **Status: research ledger, not a closure.** The $1M prize core is OPEN. This file consolidates
> 141 archivist-mined threads from issues #407 #389 #400 #371 #357 #334 #232 into a single thematic
> map: which sub-problems are genuinely attackable, which are dead, and which carry the most
> under-pursued insight. It is cross-checked against the current in-tree state
> (`docs/kb/deltastar-SESSION-MASTER-MAP-2026-06-13.md`, `RESEARCH_SYNTHESIS_407.md`,
> `DISPROOF_LOG.md`, `docs/kb/deltastar-100-routes.md`, `residual-census.md`, the `Frontier/` dir).
>
> **Honesty contract (absolute):** never fabricate a closure. Threads are marked
> `closed-proven / refuted / partial / open`. A "landed brick" is distinguished from "open math".
> **Checkout caveat (load-bearing):** several bricks the threads call "landed" (`HeightGateNormBound`,
> `ConstantIndexGaussSumBound`, `SuperCodeListBridge`, `ActionOrbitFRI`/`_BadPrimeBoundCore`,
> `shaw_offdiag_moment_le`/`shawOp_eigen`, `FarThresholdMaximality`, `CumulantDyadicDescent`) are
> **NOT present in this checkout** — they lived on parallel worktrees that never merged to `fork/main`
> here. They are flagged `[NOT-IN-TREE]` and are therefore *genuinely actionable to re-land*.

---

## (a) Executive summary — the open core and the frontier

### The reduction (machine-checked, do not re-derive)
The entire prize provably reduces to **one analytic input with four equivalent forms**, all open,
all empirically supported. For `C = RS[F_q, μ_n, k]`, `n = 2^μ`, `p ~ n·2^128`, `q < 2^256`,
`ρ ∈ {½,¼,⅛,1/16}`, `ε* = 2^-128`, index `m = (p−1)/n = 2^128` (the invariant), `|μ_n| = n ≪ p^{1/4}`:

| form | statement | cleanest attack | in-tree anchor |
|------|-----------|-----------------|----------------|
| **B-form** | worst Gauss period `B(μ_n)=max_{b≠0}\|Σ_{x∈μ_n}e_p(bx)\| ≤ C√(n·log(q/n))` | `= max over m=(p−1)/n periods` = generalized-Paley eigenvalue of `Cay(F_q,μ_n)`; `≤2√n ⟺ Ramanujan` (Paley Graph Conjecture) | `GaussPeriodCosetReduction`, `WorstPeriodLowerBound`, `PaleySpectralFloor` |
| **energy-form** | `E_r(μ_n) = (2r−1)!!·n^r·(1+o(1))` for `r ≤ r_max = Θ(log(p/n))` | **the cleanest attackable form**; `Σ_b\|η_b\|^{2r}=q·E_r` + Markov ⟹ B-form | `EnergyCharacterTransport`, `DyadicEnergyK1`, `CharSumMomentDeepWall`, `AdditiveEnergyBridge` |
| **halo-form** | high-order spurious vanishing sums of `μ_n` mod `p` don't concentrate a period (`SubsetSumHaloEnergy`) | char-0 vs char-p **mod-q defect** `E_r − E_r^{(0)} ≥ 0` is the whole wall | `CyclotomicNormDefectThreshold` |
| **list-form** | explicit smooth-RS beyond-Johnson worst-case list stays `≤ poly` below `δ*` | super-code list size = LD grand challenge | `Connections/ListDecodingAndCA`, `JohnsonListBound` |

**Candidate closed formula** (admissible, NOT proven): `δ* = 1 − ρ − 2/s*`,
`s* = min{ s : C(s, ⌊ρs⌋+2) ≥ ε*·q }`. Upper bracket `δ* ≤ 1−ρ−2/s*` **PROVEN** (Kambiré).
Lower bracket past Johnson = the open input above. Also stated as
`δ* = H_q^{-1}((1−ρ) − log_q(1/ε*)/n)` (curve shape validated up to Johnson).

### Why the wall is irreducible (structural evidence, not a theorem)
Three independent novel routes (Frankl–Wilson/RCW, ℤ/n free-orbit, m-interleaved) and ~108 catalogued
routes (`deltastar-100-routes.md`) ALL collapse to one of: (i) Johnson/UDR, (ii) a triviality,
(iii) the BGK/additive-energy/Gauss-period core, or (iv) a different recognized open problem.
The proven walls every new idea must beat: **W1** per-witness counting caps at `C(w−1,d+1)`;
**W2** additive energy carries a fatal `√n` loss (Johnson-strength only); **W3** confluent-Stepanov
stalls at `n^{2/3}`; **W4** the moment method provably stops `√(log)` short of the sup-norm.
The KU/Wasserstein SOTA (2505.22059) is `~2^27` too weak in subgroup size (`KowalskiUntrauBarrier`).

### The most promising surviving attack surfaces (ranked, see §(d) and the actionables)
1. **Cyclotomic norm-defect threshold past n=32** (T407-T01) — elementary, decidable, push the
   `(2r)^{φ(n)} < p` clean range structure-aware.
2. **char-p autocorrelation recursion `E_{r+1}=n·E_r+cross_r`** (T389/407-T28) — proves `DM_r` free for
   `r≳1.36n`; close the band `[β log n, 1.36n]`.
3. **cosh-MGF root-free form at the saddle** (T407-T15) — tightest known dress of the open input.
4. **thinness-essential constraint / B_∞←B_{log n} Sidon bootstrap** (T407-T18) — a necessary
   condition that excludes all thickness-monotone methods.
5. **Katz sheaf-trace × generic-chaining** and **ε-biased/Delsarte-LP operator** (routes 56/57/103,
   93/104) — the only never-tried families that could give worst-case `√`-cancellation without BGK/GRH.

---

## (b) Thematic clusters of unfinished threads

Status legend: `open` (genuinely open math, never executed) · `partial` (proven in a sub-regime,
prize regime open) · `landed` (axiom-clean brick exists in *this* tree) · `[NOT-IN-TREE]` (brick
claimed landed on a parallel worktree, absent here → re-landable) · `refuted` / `dead` (see §(c)).
Regime: `yes` (prize regime) · `partial` · `re-aimable` · `no` (wrong regime).

### Cluster 1 — Gaussian-period / B-form / Paley spectral (the analytic heart)

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T03 | Effective Gauss-sum independence at fixed index (effective Rojas-León) | 407 | open | re-aimable | 8 | 3 | qualitatively proven q→∞ (Katz monodromy = GL(1)^f); prize = effectivity gap. cancellation in WEIGHTS not conductor |
| 407-T07 | Constant-index √-cancellation `‖η_b‖≤√m·√n` | 407 | landed?[NOT-IN-TREE] | no | 4 | 8 | solved for fixed/polylog index; vacuous at prize m=2^128. `ConstantIndexGaussSumBound` absent here → re-land as a clean unconditional sub-√q result |
| 407-T15 | cosh-MGF root-free reduction: `G(y*)≤I₀(2y*)^{n/2}` at saddle | 407 | open | yes | 6 | 3 | tightest root-free form (no √p, no max, no 2r-th root); empirically tighter than moments |
| 407-T16 | HD reduces Gauss-phase DOF to exactly n/4 (Katz floor) | 407 | reopened-insight | yes | 4 | 5 | exact-relation hunt EXHAUSTED at Katz floor; needs non-relation concentration |
| 407-T17 | Periods are i.i.d.-Gumbel (white-noise), NOT log-correlated; C→√2 | 407 | reopened-insight | yes | 5 | 4 | kills FHK/BRW/GMC crown; bulk Gaussianity ≠ tail (the gap IS the wall) |
| 407-T18 | Thinness-essential: optimal bound FALSE in thick window β≈2.3–3.2 | 407 | open | yes | 8 | 3 | **necessary condition**: excludes ALL thickness-monotone methods; B_∞←B_{log n} Sidon bootstrap must break at β<4 |
| 357-T01 | Beat √q per-frequency on smooth subgroups (isolated kernel) | 357 | open | yes | 10 | 3 | the B-form, sixth independent appearance; `SubgroupGaussSumWorstCase` pins √q only |
| 357-T18 | Effective Jacobi/Gauss-period equidistribution (tangent-sum core) | 357 | open | yes | 9 | 3 | `A_h=m·conj(τ_h)·T_h`: house = multiplicative tangent sum off BGK wall |
| 232-T01 | Subgroup-restricted partial quadratic/mixed Gauss sum (Weil-on-curves) | 232 | open | yes | 9 | 2 | full-field = √q proven; subgroup per-frequency = open; no-go: Weil alone reaches Johnson only |
| 232-T08 | Worst-period EVT scaling `B≈√(n log m)` as max-of-m sub-Gaussians | 232 | reopened-insight | yes | 8 | 2 | reframing explains log(q/n); moment ceiling = n^{3/4} provably |
| 232-T20 | exact constant C ≈ 1.33 (gated on deep-moment/BGK wall) | 232 | reopened-insight | yes | 5 | 2 | bare-Gaussian C→1 is a fixed-n CLT artifact; plateau ≈1.33 |
| 334-T13 | M3 t₂ spectral-gap theorem (Weil on (1,1)-curves) | 334 | open | partial | 5 | 5 | torus-normalizer spike law `{x↦c/x}∪{x↦−x}`; non-normalizer t₂=O(n²/q+1) Weil-provable |

### Cluster 2 — Additive-energy / E_r / moment ladder (cleanest attackable form)

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 389-T01 | Deep-moment validity / √-cancellation at r≍log q (master open input) | 389 | open | yes | 10 | 2 | proven anchor r=2 only; depth needed exceeds r_max≈2log_n p by ≈a/2 |
| 407-T02 | Non-moment additive-combinatorial bound on r-fold cross-surplus (BGK char-p) | 407 | open | yes | 9 | 3 | named "best lever" = Shkredov higher-energy; moment route PROVEN can't supply it |
| 407-T24 | p-independence of `E_r/(r!·n^r)` → p-uniform concentration bound | 407 | open | yes | 5 | 3 | moment ladder factors through a p-FREE invariant of complex roots; p-uniform-from-p-free never built |
| 407-T28 | char-p autocorrelation recursion `E_{r+1}=n·E_r+cross_r` | 407 | open | yes | 6 | 3 | trivial `C_r≤E_r` gives DM_r free for r≳1.36n; close band `[β log n, 1.36n]` via non-trivial cross_r |
| 407-T09 | char-0→char-p transfer of deep E_r at band (r_max, ½ln q] + ideal-SVP | 407 | open | yes | 6 | 2 | threshold law `r*=½λ₁^{L1,even}(P)` verified 10/10; fully-split N(𝔮)=q = Pan-Xu open gap; cross-parity leak A≡−g·B mod q (96-100% of defects) unexploited |
| 232-T02 | Additive energy `E(G)/E_r` of the smooth 2^k-subgroup over F_q | 232 | open | yes | 9 | 3 | E=168 q-independent at order-8 (F_257/F_65537); crossover law = HBK sum-product territory |
| 389-T15 | Bessel even-moment law + geometric-moment-growth escape | 389 | reopened-insight | yes | 4 | 3 | `E_r^∞=(2r)![x^{2r}]I₀(2x)^{n/2}` proven; geometric-growth `E_r≤C^r·Gaussian` is the reopenable conditional |
| 389-T08 | Additive-energy route REFUTED as δ*-relevant (√n deficit) | 389 | refuted | no | 3 | 7 | `list≥√(n·E)≥n^{3/2}` always; energy reaches Johnson only — see §(c) |
| 400-T03 | Θ(n²) distinct-e_1 count IS the additive-energy rigidity (re-aim to E_r) | 400 | reopened-insight | yes | 6 | 4 | `#distinct e_1≈0.18n²` measured over both F_q and char-0 → intrinsic combinatorial |
| 400-T05 | q-dependence of count at fixed n = mod-q defect probe | 400 | open | yes | 7 | 5 | per-q spread (160/192/224 at n=32) is a direct, unrecognized measurement of the k_D defect |

### Cluster 3 — List / orbit / combinatorial extremality (the count side)

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 389-T02 | Worst-case far-line incidence I(δ) for adversarial words | 389 | open | yes | 10 | 2 | hill-climb beats power-words 2.3× above Johnson; super-code bridge recasts as worst (k+1)-dim list |
| 407-T11 | Super-code list-size bridge: one bound closes BOTH challenges | 407 | landed?[NOT-IN-TREE] | yes | 7 | 3 | `SuperCodeListBridge` absent here; δ*_LD<δ*_MCA gap >24×; re-land bridge then attack super-code list |
| 371-T01 | CensusDomination — the single named open Prop the pin rests on | 371 | open | yes | 10 | 2 | both-sided pin conditional on ONE Prop; audited airtight (NubsCarson O165) |
| 371-T02 | Shaw-operator unification → `B(μ_n)≤√2·√n` | 371 | landed?[NOT-IN-TREE] | yes | 10 | 2 | `shaw_offdiag_moment_le`/`shawOp_eigen` absent here; collapses all moments to spectral gap via Hölder |
| 371-T03 | ExplainableCoreSupply / sub-Johnson list-count wall | 371 | open | yes | 10 | 2 | uncoupled set-system method INTRINSICALLY capped at Johnson (`block_mass_le`); needs word-coupled algebra |
| 389-T06 | Sub-Johnson list = max subset-sum fibre N_fib; word-domination half | 389 | partial | partial | 7 | 3 | `polyEval_supply_choose_le` removes whole poly-word family unconditionally; only arbitrary unstructured words open |
| 232-T04 | Upper-half list bound `ℓ(θ)≤2^{O(H/η)}` past Johnson (list-form core) | 232 | open | yes | 10 | 2 | sharp budget = `2^{Θ(H/η)}` not poly; conditional formula `δ*=1−ρ−Θ(H/(log q−128−log n))` |
| 232-T12 | Forward equivalence: prize ⟺ RS list-decoding to 1−ρ−η q-independent | 232 | open | yes | 8 | 2 | machine-checked both directions; classical open problem since GS 1999 |
| 407-T05 | Realizability / Hankel-rank lever for R-thin curve-decodability | 407 | open | yes | 6 | 4 | all moment/spectral levers proven EMPTY; the shared-single-c Toeplitz realizability is the one untried lever |
| 407-T10 | General-pencil extremality (R1 refuted: monomials NOT extremal) | 407 | reopened-insight | yes | 5 | 3 | general cofactor line doubles bad count 8→16; clean general-pencil worst-case is open |
| 400-T01 | Window-interior worst direction dir(a,b), b−a>1 | 400 | open | yes | 8 | 3 | refutation conflated overall-worst (super-linear) with window-interior-worst (δ*-pinning); never enumerated for b−a>1 |
| 400-T09 | Higher symmetric-function constraints (e_3=0, e_j=0) generalize e_2=0 | 400 | missed | yes | 7 | 4 | the concrete missing link between refuted e_2=0 family and open window-interior target; never derived |
| 357-T03 | CensusUpperExtremal/HybridDomination conditional pin | 357 | open | yes | 10 | 2 | full conditional pin EXCEPT one extremality surface; ≡ beyond-Johnson LD of explicit RS |
| 357-T02 | Discharge InteriorCeiling at k≥2 (k=1 done) | 357 | open | yes | 9 | 5 | r=3/k=2 slice is first decisive test: probe k=2 bad-count vs `2^3·C(4,3)=32`; never run |
| 389-T22 | t=3 factorial-moment gate (sub-Poisson at small scale) | 389 | open | partial | 5 | 4 | t=3 first order seeing μ_n structure; the decisive n-scaling experiment never built |
| 371-T11 | Spectrum-collapse law: j-fold-deficient root spectrum O(n·poly(j)) | 371 | open | partial | 6 | 4 | consumer landed; the orbit-count bound (spectrum collapses, not supply) NOT proven |
| 232-T05 | Multi-symmetric zero-fiber / PTE count at deep interior t=Θ(n) | 232 | open | yes | 9 | 4 | full_tower char-0 = coset-unions PROVEN; effective height threshold + all-words quantifier open |
| 389-T04 | Per-fiber quadratic-Vinogradov/PTE for deep-band r≥5 | 389 | open | partial | 6 | 4 | r=3,4 PROVEN; Mansfield–Mudgal energy→support conversion via incidence is the new-math step |
| 389-T20 | General-k orchard/zero-sum (k+1)-subset count = deepest-band supply | 389 | partial | partial | 5 | 4 | `general_orchard_card` landed (here, `CosetUnionGrowth.lean`); worst-case Conway–Jones classification open |

### Cluster 4 — Algebraic-geometry / curve / NVM / higher-order-MDS

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T04 | Specific-subgroup NVM at large index (R3/GM-MDS, index>3) | 407 | open | yes | 6 | 3 | dyadic NVM **decidably false** (x↦x^d collapses columns ⟹ det≡0, power-of-2 is WORST index) |
| 407-T08 | char-p deep-moment via Garcia-Lorenz-Todd Fermat point-counting | 407 | wrong-regime | partial | 4 | 2 | r=2 citable theorem in-regime; GLT/Betti no-go caps AG route at r=2 asymptotically |
| 389-T05 | Higher-order-MDS (GM-MDS) order ≥3 for explicit μ_n | 389 | partial | partial | 7 | 3 | order-3 FAILS unconditionally for negation-closed μ_n (antipodal sum-zero); affinely-dependent case open |
| 389-T09 | Stepanov confluent auxiliary for `r(c)≤4n^{2/3}` (GVRepBound) | 389 | partial | partial | 3 | 3 | Johnson-strength only (honest caveat); inert n\|p+1 solved, split n\|p−1 open |
| 357-T06 | Heath-Brown–Konyagin `E(G)≪\|G\|^{5/2}` via Stepanov | 357 | partial | partial | 4 | 6 | `monomial_lemma` landed (`ToMathlib/MonomialShiftDivisibility.lean`); average-side only, not prize-closing |
| 357-T07 | M3 pencil noise band ≡ #232 BGK additive-energy kernel | 357 | open | partial | 6 | 3 | additive-pencil Weil noise band = `\|μ_n∩(c−μ_n)\|` = BGK core; same open math two lanes |
| 334-T19 | Curve/pencil k=3 fibre structure (x↦x−γ/x on subgroup) | 334 | reopened-insight | partial | 6 | 4 | first nontrivial smooth-domain regime; matches #389 nodal-cubic extremizer |
| 232-T18 | Higher-order MDS genericity (MDS(ℓ)) of smooth domains | 232 | missed | yes | 6 | 5 | **explicitly-claimed lane that never reported back**; MDS(3) probe of μ_{2^k} decidable at small n |
| 232-T06 | Derandomize random/folded-RS capacity to explicit smooth | 232 | wrong-regime | re-aimable | 7 | 3 | M1/M2 domain-independent (proven); difference lives at 3rd agreement moment |
| 357-T10 | Derandomization of random-RS capacity (highest-leverage untried) | 357 | missed | yes | 9 | 2 | the structure/randomness wall IS the entire smooth-vs-random difference; never seriously attempted |

### Cluster 5 — Lattice / ideal-SVP / cyclotomic-norm / Mersenne

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T01 | Structure-aware norm bound on `Σ_{i∈S}ζ^i` (§5.0 at n≥112) | 407 | landed?[NOT-IN-TREE]+open | yes | 10 | 4 | `HeightGateNormBound` absent here; house bound proves n≤32, ~2^61 gap on n=128 witness; **most tractable single inequality** |
| 407-T14 | Half-Sum Lemma uniform-in-n (char-p coincidences across split primes) | 407 | partial | yes | 5 | 3 | proven n=8..64; naive uniform-in-n DEAD (ledger saturates); refined incidence-coupled form open |
| 389-T17 | BCHKS25 Conj 1.12 (subgroup-sumset, Mersenne wall) | 389 | partial | yes | 5 | 2 | reduced to "largest prime factor of 2^p−1 ≥ 2^{p/5} i.o." (weaker than ∞ Mersenne, still open NT) |
| 389-T10 | Small-subgroup cyclotomic-resultant lift: closed for n<log₂p | 389 | partial | partial | 5 | 6 | end-to-end proven n<log₂p; coprimality FAILS past n=64 (gcds ~2^{0.29n}); the in-tree `CyclotomicNormDefectThreshold` IS this |
| 232-T09 | Effective char-0→F_p transfer with POLYNOMIAL height threshold | 232 | open | partial | 6 | 3 | exponential threshold proven; class-group localization (h=359057 at ζ_128) is the disproof breathing room |
| 334-T11 | mod-p surplus α-spectrum (char-0→mod-p transfer defect) | 334 | open | partial | 6 | 5 | +11/+54 spurious configs at n=64 measured exactly; classify the bad lattice vectors α with p\|N(α) |
| 334-T24 | A3-incidence: bad-prime certificate norms have class-field structure | 334 | reopened-insight | partial | 5 | 4 | c=11.0918 exact Galois; residue-degree splitting law (0/1142 violations); = #407 cyclotomic-norm line |

### Cluster 6 — Dyadic-tower / fold-transport / 2-adic descent

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T13 | Dyadic-deviation-decay δᵢ=O(1/i) for the 2-adic cocycle | 407 | open | yes | 5 | 3 | constant excess → power n^{c(δ)} (proven fatal); need the O(1/i) rate; TOWER-2 decoupling REFUTED |
| 407-T19 | Gowers/higher-order-Fourier collapse to linear via gcd | 407 | wrong-regime | no | 3 | 2 | `Σe_p(b·x^d)=gcd(d,n)·η_b` exact; GTZ has NO nonlinear content on μ_n — see §(c) |
| 389-T03 | Tower-recursive phase alignment of worst-frequency half-coset sums | 389 | open | yes | 8 | 4 | cos=1.0000 EXACT tower-recursive (not asymptotic); the one mechanism distinguishing worst from average |
| 389-T16 | Fold-transport of explicit capacity results | 389 | open | yes | 4 | 5 | naive refuted (L*=1+√ρ); surviving condition = MCA-bad error co-location under tower; co-location probe never run |
| 334-T02 | K1 fold-transport of KKH26 ceiling down the smooth tower | 334 | missed | yes | 6 | 6 | falsifiable in-tree: check fold-invariance of KKH26 witness; mutually-falsifying with K4 |
| 232-T19 | Dihedral/reflection + dyadic 2-adic Gauss tower descent | 232 | wrong-regime | yes | 4 | 2 | squaring halving proven; `M(2n)²≤2M(n)²` REFUTED (ratios to 3.86) — see §(c) |

### Cluster 7 — Probabilistic / negative-association / concentration

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T22 | Negatively-associated line-incidence ⟹ Shao convex-transfer | 407 | open | partial | 4 | 3 | non-moment, would reach budget n worst-case IF NA holds; Dubhashi-Ranjan cert never applied to line-membership |
| 389-T07 | Second-moment pair-sum certificate — REFUTED as cert, localizes object | 389 | refuted | yes | 4 | 7 | gate Θ(E²) not o(E²); typical cert never sees worst line — see §(c) |
| 389-T13 | RS Johnson-lift floor → single residual hBadCount (GKL24) | 389 | partial | partial | 4 | 5 | rate-limited (johnsonLift maps 1−√ρ to MCA floor 1−ρ^{1/4}); prize needs capacity-radius |
| 389-T14 | Deep-band saturation/failure side (complete) | 389 | landed | yes | 5 | 9 | `deep_band_saturation` landed here (`DeepBandSaturationDischarge.lean`); structurally capped at capacity−Θ(1/log n) |
| 371-T05 | Poisson ceiling law → census-free bad side (polynomial threshold) | 371 | partial | partial | 6 | 6 | threshold drops exponential→polynomial p>C(n,d+2)+1; n=128 census-free pin NEVER followed up |
| 232-T08b | (see Cluster 1, 232-T08 EVT scaling) | — | — | — | — | — | — |

### Cluster 8 — Syndrome / coding-theory lens / inverse theorems

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T23 | Sparse-support cyclic-code list-size lens (BCH/HT/Roos toolbox) | 407 | open | yes | 4 | 3 | `BCHVarietyRigidity` landed here; δ* = beyond-Johnson list growth of explicit sparse cyclic code |
| 407-T26 | Okamoto syndrome-space lens (2025/1712) | 407 | missed | partial | 3 | 3 | unconditional stops at δ<(1−ρ)/3; syndrome change-of-basis for window-interior never mined |
| 357-T11 | Syndrome-space lens (Yuan-Zhu) as proof device for smooth RS | 357 | missed | yes | 7 | 3 | dual GRS joint weight enumerator = explicit never-exploited object; flat-numerator = MacWilliams identity? |
| 357-T12 | Additive-combinatorial inverse theorems (Bogolyubov-Ruzsa/Sanders) | 357 | missed | yes | 8 | 2 | **the unification bet**: if every bad family is structured, δ* becomes finite enumeration; refutation as hard as progress |
| 334-T07 | A3-inverse (inverse theorem for window bad sets) | 334 | missed | yes | 8 | 2 | duplicate of 357-T12; highest-leverage idea in #334 |
| 334-T05 | A1 — pencil census IS the δ* obstruction (domain-separating) | 334 | open | partial | 6 | 4 | M3 separates smooth/random at k=3; k=4 census probe (the falsifier) never run |
| 334-T23 | G4/G5 incidence-lattice list bounds (Fisher/Plotkin + Bonferroni-2) | 334 | open | no | 4 | 5 | only path toward beating the union bound via exact inclusion-exclusion; fully specified, never run |

### Cluster 9 — Literature acquisition / equidistribution SOTA

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 357-T13 | Lacunary cyclotomic resultant maxima (Myerson/Lehmer) for s=128 | 357 | open | yes | 6 | 3 | sharp ±1-poly cyclotomic norms at s∈[128,256] would open s=128 WITHOUT Thorner-Zaman; thin literature |
| 334-T15 | Parseval threshold residual: s=128 still needs Thorner-Zaman | 334 | partial | yes | 5 | 5 | Parseval halved exponent (opened s=64 uncond.); s=128 needs TZ effective-PNT-in-APs (not in Mathlib) |
| 357-T05 | Lam-Leung positivity W(pqr) at 3+ primes | 357 | open | no | 3 | 5 | first open case n=105=3·5·7; off-regime (prize fixes 2-power) but generalizes census-transfer |
| 232-T07 | Lam-Leung ℕ-span positivity at 3+ primes (M31/Circle-STARK) | 232 | partial | partial | 5 | 5 | two-prime complete; n=105/154 need Conway-Jones weight-4/5; **active mathlib race (dennj PRs)** |
| 334-T10 | Odd-r exclusion / stratum turn-on theorem | 334 | open | no | 4 | 4 | r_max=2j−5 extrapolated not derived; reproduce calibration {0 at s=32, 1.59e9 at s=64} |

### Cluster 10 — Action-orbit / non-BGK lanes

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 407-T06 | Action-Orbit Q2 (Chai-Fan Conj 7.1) + Q3 universal-k lift | 407 | partial[NOT-IN-TREE] | partial | 5 | 3 | Q1 closed via elementary p≤n²/4; `ActionOrbitFRI`/`_BadPrimeBoundCore` absent here → re-land Q1 |
| 407-T20 | Existence-form floor via pigeonhole — REFUTED (∀-field-universal) | 407 | reopened-insight | partial | 5 | 4 | fixed-field surface IS provable; mcaConjecture binds constants BEFORE ∀q — see §(c) |
| 407-T21 | Ring-hom merge-only monotonicity N(char-p)≤N(char-0) | 407 | reopened-insight | yes | 5 | 3 | proven for count N but WRONG object: line-incidence I SATURATES (char-p > char-0) — see §(c) |
| 407-T25 | Char-p excess confined to deep bands (cliff-confinement) | 407 | partial | partial | 5 | 3 | verified n≤32 char-invariant; knife-edge zero margin; constant-rate large-n = same wall |
| 407-T27 | Cyclic-sieving/hook-content Schur-vanishing faithfulness | 407 | open | yes | 3 | 2 | binding-band Schur factor degenerates to trivial single-box e_1 → CSP gives no boost |

### Cluster 11 — Protocol-side / interleaving / infrastructure (mostly off-core)

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 357-T16 | Run LD⇔MCA dictionary BACKWARD (exact MCA ⟹ new LD lower bounds) | 357 | open | re-aimable | 5 | 6 | `exists_interleavedList_card_gt_of_epsMCA_gt` proven; feed in-window exact MCA values backward for new LD data |
| 334-T08 | A4 conditional LD⇒MCA collapse (q/(q−1) loss) | 334 | partial | partial | 7 | 6 | all 3 ingredients landed; forward conditional theorem is pure assembly, never reported landed |
| 334-T18 | Cor 5.9/5.10 [GG25] instance-dependent transfer | 334 | partial | partial | 5 | 5 | transfer machinery fully built; bottleneck = one concrete subspace-design decodability instance |
| 334-T12 | K2-strictness converse to Jo26 Thm 4.2 | 334 | open | no | 3 | 3 | blocked on same A3 MCA-instance (proportionality trap) |
| 334-T14 | A1-dichotomy hollowness (>q joint-agreement subspaces?) | 334 | open | no | 3 | 6 | exhaustive search at n−k≥2 never run; if hollow, m-interleaved route collapses |
| 334-T22 | A4 wire-model bridge (MCA-as-one-round-protocol) | 334 | missed | no | 2 | 5 | cross-subtree unification; one ENNReal/ℝ≥0 probe file, never run |
| 371-T16 | Master modular reduction (distinct modular-Wronskian ratios) | 371 | partial | partial | 7 | 4 | far-class = strict extremizer (#bad=C(n,k+1)); collision census for non-ladder stacks open |
| 371-T10 | WB-to-esymm compiler (split-locator → esymm fibre → RS list) | 371 | partial | yes | 8 | 3 | bridge staged/proven; explicit smooth fibre count of e_1..e_{m+1} on μ_n is the residual |
| 232-T16 | Push proven Johnson MCA (BCIKS20 §5.2.7) past dependency-island | 232 | partial | no | 3 | 4 | known math; 5-9 person-months; needs `Hab25JohnsonAlgebraicData.ofMonicHenselFactors` wiring |
| 357-T08 | CellPackageSupply (Johnson-floor discharge) | 357 | partial | partial | 5 | 4 | regime I-II only (Johnson floor, NOT the window wall); Finding-14 βHensel recursion mismatch |
| 389-T12 | BCIKS20 A.4 Johnson lane re-target to field-level Λ(α_t)=1 | 389 | reopened-insight | no | 2 | 4 | NOT blocked on hard lemma — blocked on wrong (false-as-stated) target; needs honest AddValuation |

### Cluster 12 — Census/structure bookkeeping (toy-scale, low δ*-relevance)

| id | title | src | status | regime | rel | feas | note |
|----|-------|-----|--------|--------|----:|----:|------|
| 400-T04 | Exact w=4 closed form `#orbits = n/4 − 1` | 400 | open | partial | 5 | 6 | clean exact cyclotomic char-0 statement, landable Lean brick; never proven |
| 400-T07 | Orbit-count growth profile by w (n=32: w9→23 max) | 400 | open | yes | 6 | 3 | bimodal profile, argmax w*~n/4; only 3 data points |
| 400-T08 | Exact ℤ[ζ_n] enumerator as reusable substrate | 400 | missed | partial | 3 | 8 | char-0 exact tooling described but never attached; reusable for ALL roots-of-unity vanishing-sum experiments |
| 400-T12 | Excluded e_1=0 cases = exactly μ_4-cosets | 400 | open | partial | 3 | 6 | small self-contained cyclotomic lemma; connects to X^{n/2}=±1 brick |
| 371-T04 | SPECTRUM = −μ_n law (monomial adversary completeness) | 371 | partial | partial | 6 | 5 | closure half proven; completeness via Newton identities open (single-coset form refuted → tower-graded) |
| 371-T06 | Landau ℓ² resultant sharpening (opens μ=6 pins) | 371 | landed | partial | 4 | 6 | landed; μ=7 needs TZ or Poisson; production-silent (r≲√n) |
| 371-T07 | WindowReconstructionPencil branch (ii) closure | 371 | partial | no | 3 | 7 | below-UDR (production-silent); DeepDegenerate/HasBlindPoint empty in probes, unproven |
| 371-T08 | Graded pencil ladder WB-6 (twin-freeness) | 371 | partial | no | 4 | 5 | per-grade residual converges to census torus-normalizer; Desnanot-Jacobi landed |
| 371-T09 | Below-saturation strengthened window-localization (N3 sunflower) | 371 | open | re-aimable | 6 | 4 | needs q≫n·(1/ρ)^k instances at (8..16,2..3); queued, never run |
| 371-T12 | ClassPackingBound dom4134 (first beyond-Johnson in-window pin) | 371 | partial | no | 4 | 5 | toy-scale p=12289; coupling mechanism explicit miniature of production core |
| 371-T13 | Overlapping-bisimplex grand packing envelope | 371 | partial | no | 3 | 6 | interaction law closes ratio-pigeonhole on 5t≥3n+3d strip; production-silent |
| 371-T14 | Constant-6 Möbius coincidence law ≤6 (Beukers-Smyth) | 371 | open | no | 3 | 4 | publishable off-δ*; char-0 layer bounded, char-p = growing 4\|G\|^{2/3} |
| 371-T15 | Production-regime MCA failure ε_mca≈q at boundary band | 371 | partial | partial | 5 | 4 | upper side of δ* in production proven; deeper-band m≥1 = ExplainableCoreSupply |
| 357-T04 | MDS rank lemma / strip UD→(1−ρ)/2 lift (Padé/bordered-det) | 357 | partial | partial | 5 | 5 | below Johnson (sharpens floor not window); bordered-determinant certificate |
| 357-T09 | a≥9 growing primitive census hierarchy | 357 | open | re-aimable | 6 | 4 | growth laws orbit-count(a,n) = where δ*-asymptotics live; never computed |
| 357-T14 | Slanted-stratum exactness converse (collision-branch Lean) | 357 | partial | no | 2 | 7 | bounded certificate-driven Lean emission, no new math; census bookkeeping |
| 357-T15 | Threshold-halving fixpoint iteration | 357 | refuted | no | 2 | 6 | REFUTED (halving exits window); salvage (protocol-side constraint) never explored — see §(c) |
| 357-T17 | General 3∤n boundary-defect arc-tiling certificate | 357 | partial | no | 2 | 6 | 2-power domains permanently in defect case (n−1 not n); sub-Johnson |
| 232-T03 | BGK kernel `M=\|μ_n∩−(1+μ_n)\|` char-0/Fermat/parity structure | 232 | open | yes | 8 | 3 | M=0 char-0; M odd ⟺ char\|2^n−1; 6\|M generically (S3); magnitude = open BGK core |
| 232-T10 | Cross-level locus incidence down 2-adic tower (Conjecture D) | 232 | open | yes | 7 | 4 | n=16/32 list anatomy (19=3+16, 35=C(7,4), 1344) novel; beating union bound = loc-divisibility geometry |
| 232-T11 | Conjecture 41 (c≥3 Open-Set Rank Lemma) escape-clause survives | 232 | open | yes | 7 | 3 | printed M_true form REFUTED; (ii)≡(iii) weld via class syndromes = same wall as PTE count |
| 232-T13 | Syndrome-space lens adapted to MCA + exact ε* (Okamoto/B-S-C) | 232 | wrong-regime | re-aimable | 5 | 3 | capacity-vacuity result citable as "why open"; unconditional reach (1−ρ)/3 |
| 232-T14 | Candidate formula δ*=1−ρ−2/s* + m-interpolation 1−ρ^{m/(m+1)} | 232 | open | yes | 7 | 3 | upper bracket proven; m=2 explains the 1−ρ^{2/3} sweep landing; admissible not correct |
| 232-T15 | Near-direction branch of collision-lemma dichotomy | 232 | open | yes | 6 | 3 | cyclic-automorphism near-branch: how many codewords can a coset family be near under P(x)↦P(ωx)? |
| 232-T17 | Large-sieve/average-over-q and Burgess (off-regime, flagged) | 232 | wrong-regime | no | 2 | 2 | Burgess gate a>42.67 NEVER met at prize a∈[25,40] — see §(c) |

---

## (c) DEAD / DO-NOT-REDO appendix (closed, refuted, or proven-vacuous)

Do not spend cycles re-attempting these. Each has a machine-checked countermodel, a proven no-go,
or a decisive regime/method exclusion. Citations to `DISPROOF_LOG.md` / KB notes / threads.

### Refuted shortcuts / mechanisms
- **Additive-energy route as a δ*-floor** (389-T08, W2): `list ≥ √(n·E) ≥ n^{3/2} > n` *always*
  (diagonal alone gives E≥n²). Reaches Johnson only, by an unconditional `√n` deficit. No E_r bound
  of any order proves the floor (r=2 short by √n; r≥3 fails F_p transport).
- **Second-moment pair-sum as a worst-case certificate** (389-T07, DISPROOF O173): gate is Θ(E²) not
  o(E²) across the whole window; a Chebyshev/whp certificate is exponentially blind to the structured
  worst line. The no-overlap sub-window lies entirely *below* Johnson.
- **Moment-arrow closure at constant index / flat-plateau constant / universal √2 house constant**
  (DISPROOF 2026-06-14): the moment method provably stops `√(log)` short (W4); `B/√(n log(p/n))→1`
  is a fixed-n CLT artifact (true plateau ≈1.33); v2(m)-dependence is the #400 Fermat near-threshold trap.
- **Log-correlated / FHK / BRW / GMC / Coulomb-gas crown** (407-T17): periods have *distance-independent*
  autocovariance (exchangeable white-noise), NOT log-correlated — directly measured. FHK/BRW machinery
  does not apply.
- **Ladder-only floor** (407 `LadderFloorRefutation.lean`, landed here): floor = `max(N_fib, L_nodal)`,
  the nodal product-supply `C(n,r)/n` strictly exceeds the ladder fibre at all tower heights incl. n=2^32.
- **Phase-alignment tower recursion as a descent lemma** (DISPROOF O-2026-06-13(2)): the aligned path
  exists but its base is tiny; circular. (NB: the *exact* alignment fact 389-T03 is still a live
  structural input — only its use as a self-contained descent was refuted.)
- **Ring-hom monotonicity removes the char-p wall** (407-T21): proven for the count N, but δ* is governed
  by line-incidence I, which SATURATES mod q (char-p > char-0); excess-prime exponent n^{3.25}→n^{5.99}.
- **Existence-form floor via pigeonhole** (407-T20, retracted fb7943197): `mcaConjecture` binds constants
  BEFORE the ∀q quantifier — the prize is ∀-field-universal; "some good prime exists" is a non-sequitur
  against Kambiré's ceiling. The fixed-field surface is already a theorem.
- **Threshold-halving fixpoint bands** (357-T15, `HalvingWindowExit.lean`): `(1−ρ)/2 ≤ 1−√ρ`, first
  iterate exits below Johnson, never returns. 858 sidesteps ε_mca, doesn't bound it.
- **Odd-order / radix-3 domain to remove negation** (407-T12): REFUTED — `−1∈μ_n` HELPS the floor
  (negation cancels subset-sums, reducing distinct-sum count); odd order is strictly worse.

### Proven dead routes / wrong regime
- **Gowers / higher-order-Fourier (GTZ/nilsequence) on μ_n** (407-T19): `Σe_p(b·x^d)=gcd(d,n)·η_b`
  exact — all higher-order phases collapse to linear Gauss periods. No nonlinear content. 8-lens exotic
  sweep (incl. Pila-Wilkie, ergodic, free-prob) ALL reduce-to-wall.
- **Garcia-Lorenz-Todd AG point-counting past r=2** (407-T08): Betti `B_prim=((d−1)^{2r}+(d−1))/d` is
  exponential in r; Deligne error beats main term at `r*=log p/(2 log(d−1))=3` at prize index. AG caps at r=2.
- **dyadic tower multiplicativity `M(2n)²≤2M(n)²`** (232-T19, 407 NVM-tower): FALSE (ratios to 3.86);
  NVM dyadic tower descent fails; power-of-2 is the WORST index.
- **Large-sieve / average-over-q** (232-T17, DISPROOF 2026-06-13): explicit-code prize lets you choose q,
  but first-moment covering reaches r≈½log_n Q, 4× WORSE than per-q norm reach; averaging strictly weaker.
- **Burgess / Sato-Tate / positive-proportion equidistribution** (232-T17, `RegimePin.lean`): Burgess gate
  a>128/3≈42.67 NEVER met at realizable a∈[25,40]; β=1+128/a∈[4.2,6.1] so positive-proportion is a vacuous
  n→∞ asymptotic.
- **Kowalski–Untrau / Wasserstein SOTA** (407-T03, `KowalskiUntrauBarrier.lean`): decay exponent `1/(d−1)`
  puts d in the denominator; at d=2^32 the bound is vacuous (`~2^76` vs support `2^16`), `~2^27` too weak.
- **Effective-Katz at fixed index** (407-T03, `EffKatzConductorBarrier.lean`): mean discrepancy ~1/log q≈2^-8,
  need <1/m=2^-128; 2^120 gap. Rojas-León 1010.0120 needs extensions large vs conductor — fails over prime field.
- **Croot-Lev-Pach / slice rank on multiplicative subgroups** (232-T05, route 17/18): proven dead (gives o(q)).
- **RCW / Frankl-Wilson, naive ℤ/n free-orbit count, m-interleaved curve-degree** (novel-route-ledger):
  RCW→triviality C(n,k−1); free-orbit factor-n closed but #orbits IS the core /n; interleaving = GG25
  curve-degree (open for plain RS). All three converge to the same core.
- **Height obstruction (unifying no-go)** (`RESEARCH_SYNTHESIS_407.md` §4, DISPROOF 2026-06-14): EVERY
  char-0 algebraic floor-certificate (energy, BGM higher-order-MDS det, esymm) has norm-height ≥2^{φ(n)}≫p,
  so it can vanish mod p. The floor has no char-0-transferable certificate at prize scale; proof needs analysis.
- **NVM for dyadic μ_n** (407-T04): decidably FALSE — `x↦x^d` collapses columns ⟹ generalized-Vandermonde
  det ≡ 0; power-of-2 is the worst index, R3 for dyadic is *blocked*, not merely walled.
- **HD-like exact-relation hunt** (407-T16): EXHAUSTED at the Katz floor n/4; HD+reflection are the complete
  archimedean relation set; 10 reductions all dofcut=0. Needs non-relation concentration input.
- **~108 catalogued routes** (`deltastar-100-routes.md`): the ✗J / ✗W2/W3/W4 / ✗triv / ✗inc / ~sm tally.
  The only ★ live shortlist: 11 (bilinear), 30 (Croot-Sisask), 34 (phased MacWilliams), 36 (deep-hole
  concentration), 48/50 (Krawtchouk restriction), 53/54 (generic chaining on RS-structured u₀),
  56/57/103 (Katz sheaf-trace), 84/85 (Delsarte-LP/Terwilliger), 93/104 (ε-biased restatement).

### #400 specific
- **dir(k+1,k+2) / e_2=0 near-capacity direction** (400 headline): REFUTED as δ* path — count is Θ(n²),
  sits at δ=1−ρ−2/n ABOVE the window. The n=8/16 "O(1) orbit" data was a μ_16=F_17* full-group degeneracy
  + w-parity artifact. NB the *literal* rho=1/4 point is w≡2 mod 4 = vacuous (400-T02), undetermined.

---

## (d) NOVEL / UNDEREXPLORED INSIGHTS (the most interesting under-pursued observations)

Ranked by "genuinely new + actionable + not yet executed." These are where a fresh agent should look.

1. **Thinness-is-essential as a logical necessary condition** (407-T18). The target inequality
   `B ≤ √(2n log p)` is *FALSE* in the intermediate-thick window β≈2.3–3.2 (measured at Fermat p=65537).
   This EXCLUDES every thickness-monotone method (di Benedetto, generic sum-product) as a matter of logic,
   not difficulty. The precise object a correct proof must exploit-and-break is the `B_∞ ← B_{log n}`
   Sidon-depth bootstrap. **No thinness-essential argument has been attempted.** This is the sharpest
   constraint-on-the-solution the whole campaign produced.

2. **The cosh-MGF root-free form** (407-T15). Two exact cancellations strip the √p and the max:
   `Σ_b cosh(|η_b|y) = p·I₀(2y)^{n/2}` ⟹ `B ≤ min_y (1/y)arccosh(p·I₀(2y)^{n/2})`, the open input with
   NO 2r-th root, NO max — empirically *tighter* than the moment method (8.56 vs 9.99). The saddle
   `y*=√(2 log p/n)` automatically locates the open deep moments. Whether the MGF-at-saddle admits a
   non-moment attack the raw moments don't is **unexplored**.

3. **char-p autocorrelation recursion** (407-T28/389). Exact: `E_{r+1}=n·E_r+cross_r`,
   `cross_r=Σ_{s≠t}C_r(s−t)` the autocorrelation of `1_{μ_n}^{*r}`. The *trivial* `C_r≤E_r` already
   proves `DM_r` UNCONDITIONALLY for `r≳1.36n`. A non-trivial decay of `cross_r` in the band
   `[β log n, 1.36n]` closes `DM_r` at prize depth. Concrete, formalizable, **never attempted**.

4. **The p-free invariant `c_r = E_r^∞/(r!·n^r)`** (407-T24). The entire moment ladder factors through a
   p-INDEPENDENT additive-structure invariant of the *complex* n-th roots (verified identical at p=337,3209).
   A concentration bound proven on this single p-free object would be automatically p-uniform, dodging the
   per-prime structured-prime explosion. The p-uniform-from-p-free argument was **named, never built**.

5. **The cross-parity leak A ≡ −g·B mod q** (407-T09). 96–100% of all mod-q defects obey this single
   structured relation, and the threshold law `r* = ½λ₁^{L1,even}(P)` (half the shortest even-L1 vector of
   the prime ideal P|p) was verified 10/10. The fully-split `N(𝔮)=q` case is EXACTLY the Pan-Xu ideal-SVP
   open gap. The leak structure was **never turned into a bound**.

6. **HD cuts the Gauss-phase DOF by exactly ×4 to the Katz floor n/4** (407-T16). An integer-pinned theorem
   that proves the exact-relation hunt is doomed and quantifies precisely how much structure HD removes.
   Redirects to non-relation concentration — a clean meta-result that should stop wasted relation-hunting.

7. **Structure-aware cyclotomic norm bound, ~2^61 slack** (407-T01). At n=128 the house bound predicts
   norm ~2^192 but a measured witness realizes only ~2^131 — a concrete, exploitable 2^61 structural slack.
   The §5.0 inequality `|N(Σ_{i∈S}ζ^i)| ≥ p` for non-antipodal S is the most elementary, decidable,
   formalizable single statement bracketing the prize (closed n≤32, open n≥112).

8. **Inverse-theorem unification bet** (357-T12 / 334-T07). Every known counterexample family (CS25, KK25,
   prime-field, KKH26) lives on coset/orbit structure. If any ε*-bad family is poly(1/ε)-covered by
   affine-subgroup-structured families, δ* stops being analytic and becomes a *finite enumeration*. The
   self-consistency check (a "random sparse" killer would itself be an unstructured large list config) makes
   this a well-posed structure conjecture. Bogolyubov-Ruzsa/Sanders **never imported** into proximity gaps.

9. **The Θ(n²) e_2=0 count IS the mod-q defect, measurable cheaply at tiny n** (400-T05/T06). The per-q
   spread at fixed n (160/192/224 at n=32) is an *unrecognized direct measurement* of the k_D mod-q defect
   that the frontier calls the whole wall. And n=16,w=6 over C gives 0 solutions but F_q gives a w-stable set
   — the cleanest small witness of the halo-form spurious-vanishing phenomenon, at enumerable scale.

10. **Tower-recursive phase alignment is EXACT (cos=1.0000), not asymptotic** (389-T03). At the worst
    frequency the two half-coset sums are exactly phase-aligned and the alignment persists one 2-adic level
    down, in both p~n² and prize p~n⁴ regimes. This is the one identified mechanism distinguishing the worst
    case from the average — the moment hierarchy provably cannot see it. Never formalized as a named lemma.

11. **Katz sheaf-trace × generic-chaining** and **ε-biased/Delsarte-LP** (routes 103/104). The only two
    never-tried families that could give worst-case `√`-cancellation WITHOUT assuming BGK/GRH, because they
    bound `sup_{u₀}|𝒮|` by an algebraic conductor or an LP dual certificate rather than by moments (which
    provably stop `√(log)` short). First step for 103: write `𝒮(u₀)=Σ_{ξ∈D}(trace fn)(ξ)e(ξu₀)` and compute
    the sheaf conductor. First step for 104: set up the Delsarte LP for D at radius w.

---

*End of census. For the ranked actionable attack list, see the StructuredOutput returned by the synthesis
agent. Cross-references: `docs/kb/deltastar-SESSION-MASTER-MAP-2026-06-13.md`,
`RESEARCH_SYNTHESIS_407.md`, `DISPROOF_LOG.md`, `docs/kb/deltastar-100-routes.md`, `Frontier/README.md`.*
