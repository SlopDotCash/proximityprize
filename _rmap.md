# δ* Research Map — Literature Inventory and Adjacent-Mathematics Survey

**Scope.** This page is the standing research map for the δ* program: pinning the
mutual-correlated-agreement threshold

```
δ*(C, ε*) = sup { δ : ε_mca(C, δ) ≤ ε* }
```

for explicit smooth-domain Reed–Solomon codes (ABF26 Definition 4.3 of mutual correlated
agreement; `C = RS[F, L, k]` with `L` a multiplicative subgroup of size `n = 2^μ`, rate
`ρ = k/n`, `|F| < 2^256`, `ε* = 2^{-128}`). It inventories the papers already wired into the
in-tree formalization, states the four equivalent faces of the open core with their current
best bounds, surveys adjacent mathematics not yet used in this domain, and ranks the most
promising never-tried attack vectors.

Companion ledgers: `docs/wiki/deltastar-357-nine-hypotheses-2026-06-11.md` (hypothesis queue),
`docs/wiki/open-math-hypotheses-334-deltastar-2026-06.md` (K/A wave),
`docs/wiki/residual-census.md` (whole-project residual map),
`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md` (build and honesty rules).

---

## 1. The four faces of the open core

The open core — determine δ* in the window between the Johnson radius and capacity — has four
equivalent (inter-reducible) faces. Progress on any one moves all four.

| Face | Statement | In-tree anchor |
|---|---|---|
| (i) List decoding | Beyond-Johnson list decoding of *explicit* smooth-domain RS: a poly(n) list bound `Λ(RS, δ)` for some δ > 1−√ρ | `RSListDecodingFrontier.lean`, `Connections/ListDecodingAndCA.lean`, `MCADictionaryBracket.lean` |
| (ii) Character sums | Per-frequency sub-√q bounds for incomplete character sums over smooth multiplicative subgroups (size ~n in fields of size up to 2^256) | `AdditiveEnergy*.lean` family, `AddEnergy*.lean`, BCHKS25 §7 mirror (`AttackLoop46.lean`, `ProximityGapLoop49.lean`) |
| (iii) Bad-side families | Constructing stacks with more than `q·2^{-128}` bad scalars at radius δ (the bad-family/census face) | `KKH26WitnessSpread.lean`, `MCAWitnessSpread.lean`, census/probe programme (`A4CensusValue.lean`, `A5CensusValue.lean`, second-layer converse) |
| (iv) Line–ball incidence | Maximum incidence of an affine line (with far-coset direction) against the weight-⌊δn⌋ syndrome ball in `F_q^{n−k}` | `FarCosetExplosion.lean` (`epsMCA_ge_far_incidence`), `BadGammaAffineCount.lean`, `TopDirectionLineCount.lean` |

Face (iv) is new from this campaign: for linear `C`, the bad-scalar count of a stack
`(u₀, u₁)` is exactly the number of points of the affine line
`γ ↦ syn(u₀) + γ·syn(u₁)` inside the weight-`⌊δn⌋` ball of the syndrome space; pinning δ* from
above is the construction of high-incidence lines with far directions, and pinning from below
is bounding the maximum such incidence (`epsMCA_ge_far_incidence`, axiom-clean).

### Current best bounds

- **Floor (Johnson).** `δ* ≥ 1 − √ρ` (up to the η-slack of the Johnson-regime statements):
  full MCA at the Johnson radius via the BCIKS20/Hab25 lane, in-tree conditional on **one
  named residual** (the Hab25 lane's algebraic discharge; see `Hab25Johnson.lean`,
  `Hab25JohnsonDischarge.lean`, `Hab25LaneBridge.lean`). Everything else in the chain is
  proven and axiom-clean.
- **Ceiling (capacity, strict).** `δ* < 1 − ρ`, and quantitatively
  `δ* ≤ 1 − ρ − Θ_ρ(1/log n)` in the deployed regime: the capacity edge is destroyed by the
  CS25/KK25 covering constructions and the near-capacity strip is excluded by the KKH26
  family (`kkh26_mcaDeltaStar_le` in `KKH26DeltaStarReduction.lean`, unconditional, in-tree).
- **Exact points (toy scale).** `mcaDeltaStar(RS[F₅,4,2], 2/5) = 1/4` — the first exact MCA
  threshold for any code anywhere (in-tree, axiom-clean), plus the consolidated exact-staircase
  results page (three-regime law). These calibrate the window but do not move the asymptotic
  brackets.
- **The window.** `δ* ∈ (1−√ρ, 1−ρ−Θ_ρ(1/log n))` is open. The lower-bracket side is at
  least as hard as ~25-year-open beyond-Johnson list decoding of explicit RS (the coupling
  wall, machine-mirrored in-tree); the three structural walls (coupling, average→worst-case,
  structure/randomness) are formalized as no-go lemmas
  (`JohnsonSecondMomentFrontier.lean`, `JohnsonFourthMomentNoGo.lean`,
  `FisherPastJohnsonCap.lean`).

---

## 2. Paper inventory — literature already wired into the program

One line per paper: what it contributes, and a representative in-tree consumer. (Citation
counts are large — 681 `.lean` files in `ProximityGap/` cite at least one of these; only
representative consumers are listed.)

| Key | Reference | Contribution | Representative in-tree consumers |
|---|---|---|---|
| BCIKS20 | ePrint 2020/654 (Ben-Sasson–Carmon–Ishai–Kopparty–Saraf) | Proximity gaps for RS up to Johnson; correlated agreement for lines and curves; Appendix A rational-function/Hensel layer | `BCIKS20.lean` + `BCIKS20/` cone, `Hab25Johnson.lean`, `DeepQuotientTransfer.lean`, `GWInterpolation.lean`; page `docs/kb/papers/BCIKS20.md` |
| ABF26 | *Open Problems in List Decoding and Correlated Agreement* (Arnon–Boneh–Fenzi, 2026/680, Apr 8 2026) | Survey of record; Definition 4.3 (MCA); grand-challenge statements; §4.2–4.3 capacity-regime ε_ca/ε_mca bounds; §5 collapse question | `RSListDecodingFrontier.lean`, `CapacityBounds.lean`, `LDThreshold.lean`, `GrandChallenges.lean`; audit `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md` |
| KKH26 | ePrint 2026/782 | Near-capacity strip exclusion: bad lines near capacity force `mcaDeltaStar ≤ 1 − r/2^μ` for explicit smooth evaluation codes — the unconditional upper bracket | `KKH26DeltaStarReduction.lean` (capstone), `KKH26WitnessSpread.lean`, `KKH26EntropyForm.lean`, `KKH26CharZeroCollisionLaw.lean` |
| Jo26 | ePrint 2026/891 | Curve decodability ⇒ non-covering (Lemma 5.4); deviation-kernel obstruction analysis | `GG25NonCovering.lean`, `Jo26FullyCloseAssembly.lean`, `InterleavingStabilityMCAP.lean`, `SubspaceAvoidance.lean` |
| CS25 | Covering-construction paper (with KK25, the "MCA fails at capacity" pair) | Covered, non-jointly-close stacks from count budgets: ε_mca ≥ 1 at capacity radius — destroys the capacity edge | `CS25CoveringExistence.lean`, `CS25CoveredFractionEntropy.lean`, `CS25BallInterShell.lean`, `CoveringFromFarCount.lean` |
| BCHKS25 | ECCC 2025/169 | The barrier paper: gaps stop at Johnson; MCA-past-Johnson ⟹ beyond-Johnson list decoding (the coupling wall); §7 multiplicative-subgroup sumset attack | `KKH26DeltaStarReduction.lean`, `Hab25AlgebraicBridge.lean`, `MCAWitnessSpread.lean`, `ProximityGapLoop49.lean`, `AttackLoop46.lean` |
| GG25 | ePrint 2025/2054 | Random punctured RS at capacity over small alphabets; Definition 3.1 curve decodability — the ensemble-side capacity result the smooth domain must be measured against | `GG25NonCovering.lean`, `GG25ExactPreservation.lean`, `DerandomizationFrontier.lean`, `LineDecodingT421Faithful.lean` |
| GZ23 | Guo–Zhang (arXiv 2304.01403, FOCS'23 line) | Randomly punctured RS achieve list-decoding capacity over poly-size alphabets (n²); with AGL24 down to O(n) | `DerandomizationFrontier.lean`, `LDThreshold.lean` |
| CZ25 | Chen–Zhang (STOC 2025) | Explicit folded RS achieve capacity with optimal list size O(1/ε) — closes Guruswami–Rudra for folded codes | `GWInterpolation.lean`, `ReedSolomonUniqueDecode.lean`, `CapacityBounds.lean`, `GWKernelReduction.lean` |
| JLR26 | arXiv 2601.10047 | Folded-RS/subspace-design capacity line (with ECCC TR26-057/058/074 the nearest active derandomization thread) | docs-side only so far: `docs/wiki/open-math-hypotheses-334-deltastar-2026-06.md`, `docs/wiki/deltastar-357-nine-hypotheses-2026-06-11.md` — **no .lean consumer yet** |
| Hab25 | Haböck 2025 | The streamlined Johnson-radius MCA lane (the floor); in-tree conditional on one named algebraic residual | `Hab25Johnson.lean`, `Hab25Core.lean`, `Hab25CellTailFree.lean`, `Hab25CurveCellProduction.lean`, `Hab25LaneBridge.lean` |
| CF26a "858" | IACR ePrint 2026/858 (Chai–Fan) | Threshold-halving: unconditional protocol-level result; Thm 5 = RVW13-style half-threshold uniqueness | `ProofLoop42.lean`, `CAPairExtractionEngine.lean`, `TopDirectionLineCount.lean`, `C2CoreEliminationBound.lean` |
| CF26b "861" | IACR ePrint 2026/861 (Chai–Fan) | Action-orbit core; sound conditional on two named hypotheses (Q1/Q2); protocol-level, sidesteps ε_mca | `BridgeLoop41.lean`, `BridgeLoop43.lean`, `BridgeLoop44.lean`, `Conjecture41CliqueKernelStructure.lean` |
| GS | Guruswami–Sudan 1999 | Algebraic list decoding to the Johnson radius — the engine behind every in-tree poly list bound | `MCAGSUniqueDecodingGap.lean`, `GSKernelAffineDescent.lean`, `Hab25Johnson.lean`, `MCAConjectureProgress.lean` |
| RVW13 | Rothblum–Vadhan–Wigderson 2013 | Half-threshold uniqueness for pair extraction (the `J/2`-agreement uniqueness used by 858 Thm 5) | `CAPairExtractionEngine.lean` (`bad_card_le_one`), `MCADictionaryBracket.lean` |
| GKL24 | (with BGKS20) 1.5-Johnson regime | The `1 − (1−δ)^{1/3}`-type intermediate-regime bounds between Johnson and capacity | `OnePointFiveJohnsonGeometry.lean`, `CapacityBounds.lean`, `GrandChallenges.lean`, `Hab25Core.lean` |
| DP24 | Diamond–Posen 2024 | Binary-tower / packed multilinear setting; the DG25 contrapositive chain consumes it | `DG25/Contrapositive.lean`; page `docs/kb/papers/DP24.md` |

Gap worth noting: **JLR26 is cited in the dossiers but has no formal consumer** — mirroring its
subspace-design statement as a named Prop (the way GG25 Def 3.1 was mirrored) is an easy
inventory-completion task.

---

## 3. Adjacent mathematics not yet used — survey and assessment

Each direction below is scored against the four faces: which face it attacks, what the
obstruction is, and a first concrete Lean-able or probe-able step.

### (a) Lines in Hamming balls; covering codes and deep holes — attacks face (iv)

**What exists.** The basic combinatorial fact is classical: a line (1-dimensional affine
subspace) meets a Hamming ball of radius `(k/(k+1))·Δ` around a distance-Δ linear code in at
most `k` points (folklore, surfaced in list-decoding lecture notes and in
[Bishnoi's survey of subspace-meeting sets](https://anuragbishnoi.wordpress.com/2023/03/15/sets-of-points-meeting-each-subspace-in-a-few-points/));
at half the distance the count is 1 (= RVW13 half-threshold, already in-tree as
`bad_card_le_one`). Beyond that, the question "how many points of a line lie in a *fixed-radius
weight ball* of `F_q^m`" is essentially the Littlewood–Offord problem in `F_q` (see (a′)
below) and the *covering codes / deep holes* literature
([deep holes of RS and projective RS codes](https://arxiv.org/pdf/1612.05447),
[explicit deep holes](https://arxiv.org/pdf/1711.02292),
[twisted-RS deep holes, ISIT 2024](https://arxiv.org/html/2403.11436v2)) characterizes the
*far directions*: `u₁` is a far direction exactly when its syndrome is far from the syndrome
image, and deep-hole classifications for RS (covering radius `d−1`, deep holes ↔ specific
rational-function classes, Cheng–Murray/Wan-style reductions) give *explicit* candidate far
directions for the smooth domain that nobody has fed into the incidence question.

**Assessment.** Direct hit on face (iv): `epsMCA_ge_far_incidence` says the bad-side family
question *is* a max-line-ball-incidence question, and the deep-hole literature is the only
body of work that explicitly constructs the far directions the theorem needs. The obstruction
is that deep-hole results classify *maximum-distance* cosets, while face (iv) needs incidence
at *intermediate* radius ⌊δn⌋ with δ in the open window — an unexplored regime in that
literature. A first step that is purely finite: for the in-tree exact instance
`RS[F₅,4,2]` and its staircase relatives, compute (probe lab) the full line–ball incidence
spectrum over all (syndrome, direction) pairs and compare the maximizers against deep-hole-type
directions; then state the observed maximum as a `decide`-certified lemma. A second Lean-able
step: mirror the "affine RS covering radius = d−1" fact and the deep-hole ⇒ far-direction
implication as named lemmas feeding `FarFromCode` hypotheses.

### (a′) Anti-concentration / Littlewood–Offord in `F_q` — attacks faces (iii) and (iv)

**What exists.** The incidence of the line `γ ↦ s₀ + γs₁` with the weight-w ball is
`#{γ : wt(s₀ + γs₁) ≤ w}` — a *one-dimensional anti-concentration* question for the random
variable `wt(s₀ + γs₁)` with γ uniform. The Littlewood–Offord school
([Erdős–LO with arbitrary probabilities](https://dl.acm.org/doi/10.1016/j.disc.2022.113005),
[polynomial LO and its algebraic aspects, 2025](https://arxiv.org/pdf/2505.23335),
[algebraic inverse theorems for quadratic LO](https://arxiv.org/pdf/1909.02089)) provides both
concentration bounds and — crucially — *inverse theorems*: if a linear/low-degree form
concentrates anomalously, the coefficient vector is highly structured (arithmetically
degenerate). Coding-side, the closest existing result is the
[weight distribution of random cosets vs. binomial under dual-distance hypotheses](https://arxiv.org/pdf/1408.5681)
(L∞-closeness decaying in the dual minimum distance) — for face (iv) the relevant code is the
*dual of smooth RS, which is again generalized RS*, so its (dual) distance is known exactly.

**Assessment.** This is the most direct never-tried handle on the bad-side census: an inverse
LO theorem over `F_q` saying "if many γ give low weight, then the coordinate pair
`(s₀ᵢ, s₁ᵢ)` family is structured (mostly proportional / few directions)" would convert the
incidence face into the coset/orbit structure that all known bad families (CS25, KK25, KKH26)
already exhibit — i.e., it would be the missing *inverse/structure theorem* for bad families.
Obstruction: LO theory is developed over ℤ/ℝ and for Bernoulli signs; the `F_q`-coefficient,
uniform-γ version is genuinely different (each coordinate contributes `1 − 1_{γ = −s₀ᵢ/s₁ᵢ}`,
so weight along the line is `n − (multiplicity of the most popular ratio …)` — in fact
exactly controlled by the *ratio multiset* `{−s₀ᵢ/s₁ᵢ}`). First step (cheap, Lean-able now):
prove the exact identity `wt(s₀ + γs₁) = m − #{i : s₁ᵢ ≠ 0 ∧ γ = −s₀ᵢ/s₁ᵢ} + #{i : s₁ᵢ = 0 ∧ s₀ᵢ ≠ 0}`
— this reduces face (iv) entirely to the *multiplicity profile of a ratio sequence of two GRS
syndromes*, a new, clean combinatorial object (the "ratio census") that the probe lab can
enumerate at toy scale and that connects directly to the in-tree pencil census.

### (b) Sub-Weil bounds for character sums over multiplicative subgroups — attacks face (ii)

**What exists.**
- [Bourgain–Glibichuk–Konyagin](https://arxiv.org/pdf/0705.4573) (BGK): for any γ > 0 there is
  ν(γ) > 0 with `|Σ_{x∈H} e_p(ax)| ≤ |H| p^{−ν}` for all subgroups `H ≤ F_p^×` with
  `|H| ≥ p^γ` — nontrivial cancellation for *very small* subgroups, far below the √q Weil
  range. Modern expositions: [Kowalski 2024](https://arxiv.org/abs/2401.04756),
  [Shakan's notes](https://blog.georgeshakan.com/exponential-sums-over-small-subgroups/).
- [Heath-Brown–Konyagin] (Stepanov method): `|Σ_{x∈H} e_p(x)| ≪ p^{1/4}|H|^{3/8}`-type bounds
  for medium subgroups (also [Konyagin's lecture notes](https://mathtube.org/sites/default/files/lecture-notes/Konyagin_Lectures.pdf),
  [medium-size refinements](https://www.sciencedirect.com/science/article/pii/S1071579714000847),
  [2020 improvements](https://arxiv.org/pdf/2003.06165)).
- [Ostafe–Shparlinski–Voloch, *Weil sums over small subgroups*](https://arxiv.org/pdf/2211.07739):
  bounds for `Σ_{x∈H} χ(f(x))e_p(g(x))` that remain nontrivial where classical Weil is already
  trivial — algebraic geometry blended with additive combinatorics; exactly the shape of sum
  face (ii) needs (polynomial arguments, not just linear).
- [Shkredov's subgroup energy program](https://arxiv.org/pdf/1504.04522): `E^+(Γ) ≪ |Γ|^{32/13}`-type
  additive-energy bounds for `|Γ| ≲ p^{2/3}`, `|3Γ| ≫ |Γ|²/log|Γ|`, non-sumset structure of
  small subgroups ([additive decompositions](https://www.researchgate.net/profile/Chi-Hoi-Yip/publication/370338879)),
  shifted-subgroup multiplicative energy ([trinomial sums application](https://arxiv.org/pdf/1701.06192)).
- [Chang–Shparlinski double sums over subgroups and intervals](https://arxiv.org/pdf/1401.6611),
  [Kerr–Macourt-style double/multilinear sums](https://arxiv.org/pdf/1901.00975) and
  [Kloosterman sums over small subgroups](https://arxiv.org/pdf/1903.10070): sub-√q savings
  from *bilinear* structure, below the Burgess range.

**Assessment.** Face (ii) needs: for `H` smooth of size n ~ 2^μ in `F_q` with q up to 2^256
(so `|H| ~ q^γ` with γ as small as ~1/8 in deployed parameters), per-frequency bounds
`|Σ_{x∈H} χ(x)ψ(ax)| ≤ |H|^{1−c}` or `≤ √q / q^ν`. BGK *qualitatively* delivers exactly this
(any fixed γ > 0), and this appears never to have been cited anywhere in the proximity-gap
literature — the BCHKS25 §7 attack and the in-tree additive-energy cone use only elementary
energy counts. Two obstructions: (1) BGK's ν(γ) is effective but astronomically small
(triple-log savings in the worst case) — fine for "nontrivial", useless for the 2^{-128}
budget without a quantitative overhaul; (2) the smooth domain is in `F_q^×` for *prime-power*
q (binary-field deployments), while BGK's strongest forms are prime-field; the `Z_q^*`
extensions ([Bourgain, arbitrary q](https://math.ucr.edu/~mcc/paper/122%20NewExp.pdf)) lose
more. First step: mirror BGK as a named Prop (`BGKSubgroupCancellation`) with the exact
quantifier shape face (ii) needs, then prove in Lean the *reduction* "BGK with explicit
ν ≥ ν₀(γ) ⟹ bad-scalar count ≤ q^{1−ν₀}" through the in-tree Fourier bridge
(`AddEnergyMathlibBridge.lean`) — this isolates exactly how large a ν the program needs and
turns "is BGK strong enough?" into a checkable inequality. In parallel, probe Heath-Brown–
Konyagin/OSV numerically at toy q to see whether the *smooth* (2-power-order) structure of H
gives better-than-generic cancellation per frequency.

### (c) Vanishing sums of roots of unity and the subgroup-sumset census — attacks face (iii)

**What exists.** The census face's `e_j`-systems over roots of unity (the in-tree second-layer
converse, the balanced-law files `BalancedFourLaw.lean`/`BalancedFiveLaw.lean`, the 4-adic
recursion) live exactly in the classical theory of vanishing sums of roots of unity:
[Conway–Jones 1976](https://www.semanticscholar.org/paper/d9a98c092f1dadfbeae274d46d88a743fe35fb85)
(minimal vanishing sums of weight ≤ 9, trigonometric diophantine equations),
[Lam–Leung 1995](https://arxiv.org/abs/math/9511209) (`n` m-th roots sum to zero iff
`n ∈ ℕp₁ + … + ℕp_r`), [Lam–Leung in characteristic p](https://arxiv.org/pdf/math/9605216),
and the recent [classification of minimal vanishing sums up to weight 21](https://arxiv.org/pdf/2008.11268).
There is even a proof-complexity angle:
[vanishing sums of roots of unity in Polynomial Calculus and SOS](https://drops.dagstuhl.de/storage/00lipics/lipics-vol241-mfcs2022/LIPIcs.MFCS.2022.23/LIPIcs.MFCS.2022.23.pdf),
directly relevant to certifying census kills.

**Assessment.** For 2-power-order smooth domains the relevant root-of-unity order is `2^μ`
(single prime divisor!), where Lam–Leung is at its strongest: every vanishing sum of `2^μ`-th
roots of unity has even weight and decomposes into antipodal pairs `ζ + (−ζ)`. This is a
*structure theorem for the census's collision systems* that the in-tree machine-generated
branch trees currently re-derive case-by-case (10395 pairings → 8 survivors); Lam–Leung +
Conway–Jones would replace per-weight enumeration with a uniform decomposition law and likely
collapse the second-layer seed systems a priori. Obstruction: the census systems are not bare
vanishing sums — they are *systems* of power sums (`e_j`/`p_j` constraints) with multiplicity
and balance conditions, so the classical results apply to each equation separately but the
interaction is new. First step (very concrete): prove in Lean the 2-power Lam–Leung
specialization "every vanishing sum of `2^μ`-th roots of unity in characteristic 0 is a
ℕ-combination of antipodal pairs" (an induction on μ via the unique index-2 subgroup — clean,
self-contained), then re-derive the existing `secondLayer_of_no_antipodal` survivors from it
and measure the compression; if it collapses the tree, the same law scales the census to
depths the certificate generator cannot reach.

### (d) Croot–Lev–Pach / slice rank for line–ball incidence — attacks face (iv) lower bounds

**What exists.** The slice-rank polynomial method
([Croot–Lev–Pach](https://quomodocumque.wordpress.com/2016/05/12/croot-lev-pach-on-ap-free-sets-in-z4zn/),
[Tao's symmetrization](https://terrytao.wordpress.com/2016/08/24/notes-on-the-slice-rank-of-tensors/),
[survey 2024](https://www.cambridge.org/core/books/abs/surveys-in-combinatorics-2024/slice-rank-polynomial-method-a-survey-a-few-years-later/43C03D3CC747E32C976EBB29C3B22233))
bounds sets avoiding/realizing linear patterns in `F_q^n` by the rank of an indicator tensor;
the key enabling fact is that *Hamming-ball indicators have low-degree polynomial
representations* (the CLP lemma is literally "functions on `{0,1}^n` supported on a ball have
low slice rank"). Applications so far are to caps, sunflowers, tri-colored sum-free sets —
not to coding-theoretic line–ball incidence.

**Assessment.** Face (iv) asks: max over lines of |line ∩ B_w| where `B_w ⊂ F_q^m` is a weight
ball. A line is the ultimate "linear pattern", and `1_{B_w}` has exact polynomial degree
`≤ w(q−1)` (weight is a sum of `1 − x_i^{q−1}` terms) — so the CLP mechanism applies in
principle: if a line had many points in `B_w`, the restriction of `1_{B_w}` to the line is a
univariate polynomial of degree ≤ w(q−1) with many roots of `1 − f`, giving the trivial bound;
the interesting question is whether tensor/slice-rank versions beat the trivial
degree-counting when the *direction* is constrained to be far (the far-coset condition is a
strong restriction CLP-type arguments have never been asked to exploit). Obstruction: for the
deployed regime `q ≫ m`, polynomial-method bounds in the q-direction tend to be weak (CLP
shines when q is small and the dimension is large — here `m = n−k` is large but the line lives
in the q-direction); a genuinely new hybrid (polynomial in the m coordinates, algebraic in γ)
would be needed. First step: probe at toy scale whether `max_line |line ∩ B_w|` for far
directions is attained by ratio-degenerate directions (connecting to (a′)); then attempt the
trivial-but-new lemma "incidence ≤ 1 + (number of distinct ratios −s₀ᵢ/s₁ᵢ achieving
multiplicity ≥ n−w)" in Lean — it is the exact-identity route from (a′) restated in CLP
language, and it already gives a nontrivial far-direction bound.

### (e) Beyond-Johnson for structured codes: folded/multiplicity capacity results — calibrates face (i)

**What exists.**
- Random side: [GZ23](https://arxiv.org/abs/2304.01403) (punctured RS at capacity, q = O(n²)),
  [AGL24](https://arxiv.org/abs/2304.09445) (linear-size alphabets, optimal),
  building on Brakensiek–Gopi–Makam (higher-order MDS / generalized Singleton).
- Explicit side: [folded RS / multiplicity codes achieve relaxed generalized Singleton bounds](https://arxiv.org/abs/2408.15925)
  (STOC'25), [Srivastava SODA'25](https://arxiv.org/pdf/2502.14358) (list size O(1/ε²)),
  Chen–Zhang STOC'25 (optimal O(1/ε)); [near-linear-time decoders](https://arxiv.org/pdf/2603.03841);
  [deterministic list decoding of RS, ECCC 2025/170](https://eccc.weizmann.ac.il/report/2025/170/).
- Why they fail for plain smooth RS, precisely: every capacity proof either (1) consumes
  *domain randomness* — GZ23/AGL24 union-bound over evaluation-point choices, and the smooth
  domain is a single fixed orbit with zero entropy; or (2) consumes *folding/derivative side
  information* — the FRS/multiplicity decoders solve for the message from `s` correlated
  symbols per position, which plain RS does not provide; or (3) consumes *subspace-design
  structure* (CZ25/JLR26) imposed at encoding time. The in-tree
  `DerandomizationFrontier.lean` and the M3 probe campaign (third agreement moment, pencil
  census) show the smooth domain is *measurably different* from the random ensemble — so
  transfer is not merely unproven, it is plausibly false in one direction.

**Assessment.** This face is where the program's coupling wall lives, so the realistic use of
this literature is *transport*, not transfer: the smooth domain of size `2^μ` is an iterated
2-to-1 quotient tower, and folding plain RS along that tower *is* an FRS-like code over the
subfield orbit — the never-tried question is whether the Chen–Zhang/Srivastava list bound for
the *folded* smooth code, combined with the in-tree fold fixed-point/kill-challenge transport
(the `β = −w` lane) and the KKH26 ceiling transport, yields any δ > 1−√ρ statement for an
*explicitly derived* (not plain) smooth code that still feeds the MCA dictionary
(`MCADictionaryBracket.lean` consumes interleaved list bounds at radius 2δ, code-agnostic).
Obstruction: unfolding a list bound back to the plain code multiplies the radius loss by the
fold arity, and naive unfolding lands back below Johnson — the question is whether the smooth
tower's *kissing structure* (probe-measurable) beats the naive loss. First step: state the
folded-smooth-RS code as an in-tree object (the fold infrastructure exists), instantiate the
CZ25 bound as a named Prop for it, and compute at toy scale the exact unfolding loss against
the exact-staircase δ* values — a pure probe-lab experiment with a decisive numeric answer.

---

## 4. Ranked attack vectors — five never-tried directions

Ranked by (expected information per unit work) × (directness of the face attacked).

1. **The ratio-census identity (LO-in-`F_q` route, (a′)+(d)).** Prove the exact identity
   reducing line–ball incidence to the multiplicity profile of the ratio sequence
   `{−s₀ᵢ/s₁ᵢ}` of two GRS syndromes; enumerate the profile at toy scale; then attack the
   profile with the GRS structure (a GRS syndrome ratio sequence is a rational function
   evaluated on the smooth domain — its level sets are root sets, so multiplicities are
   degree-bounded). This is face (iv) made fully concrete, it is entirely elementary to state,
   it subsumes the trivial CLP bound, and the rational-function level-set bound is a genuinely
   plausible new theorem: *incidence ≤ 1 + deg-bound on how often a fixed rational function
   repeats a value on a subgroup orbit*. First step: the identity lemma + a probe sweep of
   ratio profiles on the exact-staircase instances.
2. **BGK quantified through the Fourier bridge ((b)).** Mirror Bourgain–Glibichuk–Konyagin as
   a named Prop with explicit ν, and prove the in-tree reduction "per-frequency cancellation
   `q^{−ν}` over the smooth subgroup ⟹ bad-scalar budget `q^{1−ν}`" via
   `AddEnergyMathlibBridge.lean`. This imports the only known sub-√q technology for
   subgroups of size `q^γ`, never cited in this domain, and converts the vague hope into one
   checkable inequality ("is ν₀(γ) ≥ 128/256 achievable for smooth H?"). Even a negative
   answer (BGK's ν is structurally too small) is a publishable wall-statement matching the
   moment no-gos. First step: the Prop statement + the reduction lemma + an Ostafe–Shparlinski–
   Voloch toy-q numeric probe for smooth-vs-generic H.
3. **2-power Lam–Leung for the census ((c)).** Prove "every vanishing sum of `2^μ`-th roots of
   unity decomposes into antipodal pairs" (induction on the index-2 subgroup tower), then
   re-derive the machine-generated second-layer survivors from it. Bounded risk, clean
   self-contained Lean target, and if it compresses the 82-node branch tree it scales the
   census programme — the program's only domain-separating invariant — beyond
   certificate-generator depth. First step: the μ-induction lemma (estimated one file).
4. **Deep-hole-fed far directions ((a)).** Use the RS deep-hole classification literature to
   construct explicit `FarFromCode` directions for `epsMCA_ge_far_incidence` at intermediate
   radius, and probe their incidence spectra; the deep-hole community has never been asked
   about intermediate-radius cosets, and the smooth domain's deep holes (rational functions on
   a subgroup) are exactly the objects in vector 1. First step: mirror "affine RS covering
   radius = d−1" + a deep-hole ⇒ far-direction lemma, then probe.
5. **Fold-transport of explicit capacity ((e)).** Instantiate the Chen–Zhang folded-RS bound
   for the smooth tower's folded code as a named Prop, and measure the exact unfolding loss
   against the exact-staircase values. Highest ceiling (it is the only vector that could move
   face (i) directly past Johnson for a smooth-derived code), but gated on the known naive
   loss; the probe decides cheaply whether the tower's structure beats it. First step: the
   folded-smooth object + toy-scale unfolding-loss table.

Cross-cutting quick win: add the missing **JLR26 named-Prop mirror** (§2 gap) while touching
the frontier files.

---

## 5. Method notes

- All five vectors follow the program discipline: probes precede formalization; refutations
  land as sorry-free lemmas in `DISPROOF_LOG.md`; open cores stay named Props; δ* claims must
  arrive as bracket pairs (`le_mcaDeltaStar_of_good` / `mcaDeltaStar_le_of_bad`) that meet.
- Web-survey sources beyond those hyperlinked above: BGK original (C. R. Acad. Sci. 342,
  2006), [Chang–Shparlinski double sums](https://arxiv.org/pdf/1401.6611),
  [Shparlinski–Macourt-school multilinear sums](https://arxiv.org/pdf/1901.00975),
  [random-coset weight distributions](https://arxiv.org/pdf/1408.5681),
  [minimal vanishing sums weight ≤ 21](https://arxiv.org/pdf/2008.11268),
  [FRS list-size exposition](https://arxiv.org/pdf/2502.14358),
  [list-decodability of RS with large radius](https://arxiv.org/pdf/2012.10584).
- The four faces are equivalent only up to the in-tree reductions; when writing new results,
  cite the face actually proven and let `Connections/` carry the transfer.
