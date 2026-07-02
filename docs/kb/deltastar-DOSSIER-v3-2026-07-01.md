# Prove δ\* — the complete research dossier (v3)

> **🔁 This dossier supersedes v2 (issue #464, 179 comments) and #444 (1,190 comments).**
> Canonical in-tree copy: `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`. The Lean-side single-file
> workspace is [`ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean).
> Consolidated 2026-07-01 from: proximityprize.org + ABF26 (ePrint 2026/680); the FULL #464 thread
> (dossier v2 + all 179 comments, independently re-digested); the #444 record; the in-tree substrate
> (~1,611 `Frontier/` files, 59-entry `DISPROOF_LOG.md`, ~150 `deltastar-464-*` KB notes); and the
> recovered unpushed #444 workstation branch (see §12 — the "phantom bricks" are resolved).
>
> **Mission.** Pin **δ\*** — the mutual-correlated-agreement (= list-decoding) threshold — for
> *explicit* smooth-domain Reed–Solomon codes in the **window interior `(1−√ρ, 1−ρ−Θ(1/log n))`**,
> worst-case, with a *closed* proof (reducing only to known-proven mathematics). This resolves
> **both** grand challenges (Grand-MCA and Grand-LD — one threshold).
>
> **Honesty contract (non-negotiable).** Be **bold in exploration, strict in proof-claims**. A claim
> is "proven" only with an axiom-clean Lean declaration (`#print axioms ⊆ {propext, Classical.choice,
> Quot.sound}`, 0 `sorryAx`); everything else is a `conjecture` / probe / KB note. Refutations with
> machine countermodels are *wins*. Never fabricate closure. The open core is a recognized open
> problem in analytic number theory; carrying it as a named `Prop` is modularity, not incompleteness.

---

## 0. TL;DR — where the prize stands (2026-07-01)

1. **The prize is ONE inequality, now with an exact-rational target form.** Both grand challenges,
   all ~20 analytic faces, and every proven reduction funnel to:
   > **(CORE)** `M(μ_n) := max_{b ≢ 0 (mod p)} |Σ_{x∈μ_n} e_p(b·x)| ≤ C·√(n·log(p/n))`, `C = O(1)`
   > (conjecturally `C = √2`), for the dyadic subgroup `μ_n ⊂ F_p^×`, `n = 2^μ ≈ 2^30`, at the
   > Burgess barrier `p ≈ n^β`, `β ≈ 4`, uniformly to moment depth `r ≈ ln q ≈ 83–89`.

   New in #464: the **master-gap identity** pins `δ* = (1−ρ) − m*/n` — an exact rational with
   denominator `n`, where `m*` is the minimal degree-excess of a bad far line, bracketed
   `m* ∈ [m_floor, m_KKH26]` with the ceiling `m_KKH26 = Θ(n/log n)` **proven**
   (`kkh26_mcaDeltaStar_le_of_TZ`). Pinning δ\* ≡ computing the integer `m*` ≡ the wall.

2. **The wall is two-sided, necessary, and now exhaustively mapped.** `ERM-at-r ⟺ M ≤ √((2r+1)n)`
   (floor and ceiling are the same object); every second-order / energy / spectral / LP method
   provably caps at Johnson / √p (the Meta-Theorem); no fifth structural door exists (the
   Tetrachotomy); the #464 campaign additionally closed the **entire door-(iv) gap-combinatorial
   face**, all **graph-relation reformulations**, **six non-period angles**, **three
   √-cancellation-breaking templates**, and **five beat-SOTA exponent mechanisms** (0 survivors,
   double-refereed). Twelve independent technologies re-derive `M(μ_n)` at their quantitative step:
   **plain-RS δ\* in the window IS the Paley/BGK object, provably**.

3. **The char-0 half is fully closed; the fixed-depth char-p side is closed too.** `E_r ≤ (2r−1)‼·n^r`
   is proven for all r in char 0 (Lam–Leung; Bessel; exact ladder E₂…E₃₃). New in #464: **every
   fixed-r face closes unconditionally off-BGK** (no finite-r cutoff — canonical width-four/resultant
   ladder discharged concretely at n = 16…32768). The entire residual is the **joint limit**
   `r ≈ ln q`, `n = 2^30`: the char-p wraparound transfer at logarithmic depth.

4. **The off-BGK floor route is RESOLVED — as obstruction-removal, not a bypass.** Floor-bad(16) =
   {17} and floor-bad(32) = {97} (exact validated scanners); the Thorner–Zaman sub-quartic
   least-prime exponent **12/5 is CONFIRMED unconditional** for dyadic moduli (2026-06-27, from the
   verbatim TZ paper: Siegel zero eliminated since the squarefree part d = 2 is fixed) — so the
   binder-family obstruction is removed **unconditionally** at every prize scale. But the meta-verdict
   stands: **δ\*-pin ⟹ floor-good, never conversely** — floor-goodness is necessary-not-sufficient;
   the window-interior δ\* remains gated on the wall.

5. **A genuinely new production interface exists: the line-list counting stack** (on main, verified:
   `LineListReduction` → zero-agreement strata → coordinate fibers → MDS uniqueness for `#S ≥ k` →
   singleton-defect → support-ratio covers), which discharges everything except **low-profile
   (`t < k`) fibers on large-zero-safe lines** — with exact failure scanners at every layer; the raw
   envelopes are all formally refuted. ✅ **UPDATE 2026-07-01: its prize-facing weld is RE-LANDED
   and referee-verified** (`LineListMCAWeld.lean`, `mcaDeltaStar_ge_of_farLineListBudgeted`, now
   with a proven coset dichotomy localizing the near branch to large-zero directions — see §12);
   the open production obligations are the far-line list budget `Λ ≤ L ≲ ρ·n` and the
   large-zero-direction budget (`hlow`).

6. **The evidence stays mildly favorable to the floor being TRUE** (δ\* strictly inside the window):
   `C ∈ [1.07, 1.49]` hugging √2 across eight octaves with no upward drift (~900 primes, to n=1024);
   the {log|η_b|} field is measured independent-Gaussian (NOT log-correlated — FHK killed by
   experiment); the GPU worst-case list is bounded deep in the interior. And it is **proven that
   numerics cannot decide it** (the deciding regimes are compute-infeasible).

7. **What survives as attack surface** (§6): the **windowed SumsetExtremal** crux; the **line-list
   low-profile obligations** (mixed-profile fits / second-witness multiplicity /
   `CandidateListExactSuccessor`); the **Hankel-positivity / Lax-pair spectral-shift** seam on the
   Jacobi turnover (the one non-magnitude door left ajar); the **uniform-in-μ floor-bad
   characterization**; ~~the di Benedetto effective-1/2 push~~ (**CLOSED 2026-07-01** —
   quantified-dead, double-refereed; the whole exponent-pushing axis is δ*-irrelevant by
   `deltaStar_determination_all_or_nothing`, see §6 item 5); plus a short
   list of unrun probes and bankable off-core wins (folded-RS pin, Binius domain dissolution,
   deployment-prime certificates).

8. **Bottom line: the prize is OPEN and ON-BGK.** The campaign's cumulative achievement is a
   complete, machine-checked cartography: a two-sided reduction to one open inequality, route
   elimination *as theorems*, a production-grade counting interface wired to the prize object, and an
   honest record (including recovering and resolving its own phantom-brick flags, §12).

---

## 1. The problem — exact target, formal objects, governing law

### 1.1 The prize (proximityprize.org + ABF26)

The Ethereum Foundation offers **$1,000,000** for two "grand challenges" on the Reed–Solomon codes
underpinning FRI/STIR/WHIR. Both fix `C := RS[F, L, k]` with **smooth** (dyadic FFT subgroup)
evaluation domain `L`, **constant rate** `ρ = k/|L| ∈ {1/2, 1/4, 1/8, 1/16}`, `|F|` large, and target
error `ε* = 2^−128`:

- **Challenge 1 (Grand MCA).** Determine the largest `δ*` with `ε_mca(C, δ*) ≤ ε*`.
- **Challenge 2 (Grand LD).** Determine the largest `δ*` with `|Λ(C^{≡m}, δ*)| ≤ ε*·|F|`.

The two thresholds coincide on the relevant window — **one δ\***.

### 1.2 The formal objects (in-tree, machine-checked)

- **`mcaEvent`** (ABF26 Def 4.3, `Errors.lean:216`); **`epsMCA`** (`Errors.lean:231`):
  `ε_mca(C,δ) := ⨆_{u} Pr_{γ←$F}[mcaEvent C δ (u 0) (u 1) γ]` — a **sup over ALL word stacks**.
- **`mcaDeltaStar`** (`MCAThresholdLedger.lean:86`): `δ*(C,ε*) := sSup {δ ≤ 1 : ε_mca(C,δ) ≤ ε*}`,
  with proven brackets `le_mcaDeltaStar_of_good` / `mcaDeltaStar_le_of_bad`.
- **Degeneracy guards (machine countermodels):** `candidate_floor_is_exact_REFUTED`,
  `candidate_uptocapacity_REFUTED`. The non-degenerate target is `mcaConjecture` /
  `mcaConjectureBound` (`GrandChallenges.lean:650/623`) — **not** the radius-one `grandMCAChallenge`.
- **NEW (#464): the windowed-guard discipline.** The in-tree `SumsetExtremal` predicate as literally
  written (all δ, no field-size guard) is **FALSE** (`not_sumsetExtremal`, countermodel at
  `RS[F₁₇, μ₈, k=2]`, δ=1/8: a 2-spike pencil beats every monomial stack). Any extremality/dominance
  hypothesis must carry the explicit prize-window guard `δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))`, `q` large
  (`SumsetExtremalityGuard.lean`). Below-window countermodels kill degenerate Props, not the prize.

### 1.3 The prize regime (the constants that make it hard)

- Domain: dyadic `μ_n`, `n = 2^μ ≈ 2^30`, a **proper** subgroup (`n ∣ q−1`), index
  `m = (q−1)/n = 2^128`; `q ≈ n·2^128` (equivalently `p ≈ n^β`, `β ≈ 4–5` on the analytic diagonal).
- `ε* = 2^−128` ⟹ **budget `q·ε* ≈ n`**. **THIN:** `n ≈ q^{1/4..1/5} ≪ √q`.
- Window `(1−√ρ, 1−ρ−Θ(1/log n))`: Johnson `1−√ρ` achievable (ACFY24/Hab25, vacuous AT Johnson);
  capacity `1−ρ` proven impossible (Crites–Stewart 2025/2046, Diamond–Gruen, Kambiré).
- ⚠️ Never validate on the full group `n = q−1` (the #400 trap); always proper subgroups, large
  primes, multiple primes; exclude correlated directions `X^{n/2} = ±1`.

### 1.4 The governing law and the master-gap identity

> `δ* = sup{δ : I(δ) ≤ q·ε*}`, `I(δ) = max_{u₀,u₁} #{γ : u₀+γu₁ is δ-close to RS[k]}`
> (`badScalars_eq_explainable` + `FarCosetExplosion.mcaEvent_iff_line_explainable`).

Extremal lines are monomial directions (dilation equivariance). **NEW (#464), the master-gap form:**

> **`δ*(C) = (1−ρ) − m*/n`** — exact rational, denominator `n`, `m*` = minimal degree-excess of a
> bad far line; `m* ∈ [m_floor, m_KKH26]`, ceiling `m_KKH26 = Θ(n/log n)` **proven**
> (`kkh26_mcaDeltaStar_le_of_TZ`); `m* = m_KKH26 ⟺ M(μ_n,p) ≤ M_KKH26` via
> `_EnergyRatioMonotoneReduction`. **Pinning δ\* ≡ computing the integer `m*` ≡ the wall.**

---

## 2. The single open core — one object, all faces

> **CORE.** `M(n,p) = max_{b≠0} |η_b| ≤ C·√(n·log(p/n))`, `η_b = Σ_{x∈μ_n} e_p(bx)`, at `p ≈ n^4`,
> `n = 2^30` — equivalently the DC-subtracted char-p energy `A_r ≤ K^r·(2r−1)‼·n^r` at `r ≈ ln q`.

### 2.1 The Paley-graph dictionary

Liu–Zhou (Thm 115/116) / Podestá–Videla: the `η_b` are exactly the non-principal eigenvalues of the
generalized Paley graph `Cay(F_q, μ_n)`; `M ≤ 2√n ⟺ Ramanujan` = the Paley Graph Conjecture
(Kim–Yip–Yoo Conj 2.12, open). `M` is totally real (`−1 ∈ μ_n`); Parseval floor `M ≥ ≈√n`
unconditional (`GaussPeriodParsevalFloor`). The prize graph is NOT strongly Ramanujan
(`M/(2√n) = 1.34…2.43`); the target is the order `√(n log m)`.

### 2.2 Master reduction chain (axiom-clean)

`Σ_b η_b^r = q·N₀(G,r)`; DC-subtracted Parseval `Σ_{b≠0}|η_b|^{2r} = q·E_r − n^{2r}`
(`DCSubtractedMoment.sum_nonzero_moment`); moment method at `r ≈ ln q` gives `M ≤ √(2e)·√(n ln q)`
*conditional on the Wick bound at that depth*.

### 2.3 ⚠️ MANDATORY FORM — DC-subtracted energy `A_r`

Raw `E_r ≤ (2r−1)‼·n^r` is **FALSE at the prize** (DC term `n^{2r}/q` dominates for `n ≥ 64, r ≥ 8`;
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`). Only `A_r = E_r − n^{2r}/q ≤ Wick` is
non-vacuous (`DCEnergyCorrection.DCEnergyBound`). The honest target is `E_r ≤ K^r·(2r−1)‼·n^r`,
`K = O(1)`, uniformly to `r ≈ ln q` — NOT `W_r = 0` (false; onset `r₀ = 5`).

### 2.4 The four canonical equivalent forms (state the core to an analyst in any of these)

- **(A) Wick moments at log depth:** `A_r ≤ K^r(2r−1)‼·n^r` to `r ≈ ln p ≈ 89`. Char-0 analogue is a
  theorem for all r. Residual = char-p wraparound: do short (`≤ 2 ln p`-term) ±1-relations of
  `2^μ`-th roots of unity vanish mod p more often than the Wick rate?
- **(B) Effective worst-case vertical Sato–Tate:** make Katz equidistribution of `{η_b}` effective,
  worst-case, sup-norm at conductor `m = 2^128`. (Effective-Katz is PROVEN VACUOUS in the thin regime
  — `effectiveKatz_vacuous_in_thin_regime` — so this form needs genuinely new machinery.)
- **(C) Wraparound Variance Law (arithmetic CLT):** `W_r = A_r − E_r^∞` concentrates at its DC mean
  `n^{2r}/p` with √-fluctuations, uniformly to `r ≈ log p`.
- **(D) Early Jacobi turnover:** the recurrence coefficients `b_k` of the empirical spectral measure
  follow Hermite (`b_k² = nk`) up to a turnover `k*`; `M = 2·max_k b_k`; core ⟺ `k* = O(log p)`.
  (The Toda/isospectral route is proven gauge — `todaTurnover_not_determined_by_invariants` — but the
  Hankel-*positivity* seam is open, §6.)

**The sharpest #464 localization (the independence form):** the measured `{log|η_b|}` field on the
`m` cosets is independent-complex-Gaussian — NOT log-correlated (killed FHK by experiment: measured
log-autocovariance ≈ 0.008/−0.085/0.02 vs log-correlated prediction 0.88/0.75/0.62). The prize =
**certifying the independence**: a centered sub-Gaussian tail `P(|η_b| > tn) ≤ exp(−ct²n)` to depth
`r ≈ log p`, equivalently `E_r^+(μ_n) − n^{2r}/p ≤ C^r·r!·n^r` at logarithmic depth. The difficulty
is certification, not distribution shape.

### 2.5 The prize-facing faces (all propositionally linked, in-tree)

| Face | In-tree name | One line |
|---|---|---|
| Far-line incidence | `OpenCoreConditionalPin.WorstCaseIncidenceBounded` | floor ⟸ incidence bound |
| Orbit-count | `OrbitCountPinNecessity`, `unionGrowth_iff_orbitGrowth` | combinatorial conversion |
| Char-sum | `WorstCaseIncompleteSumBound` | `∀b≠0, ‖η_b‖² ≤ M` |
| Energy | `DCEnergyBound` | DC-subtracted Wick at depth r |
| Signed-deep | `CrossFormBridge.dcEnergyBound_iff_signedDeepCancellation` | sign ⟺ orbit-count rate |
| Line-list (⚠️ weld not on main, §12) | `LineListReduction` stack; weld `mcaDeltaStar_ge_of_farLineListBudgeted` claimed, to re-land | floor ⟸ `Λ ≤ L ≲ ρn` on far lines |
| **Field closure (NEW)** | `floorClosureBudgetedMaxAtField_univ_iff_floorGood_and_worstCaseIncidenceBounded` | all-stack closure ≡ floor-good ∧ WCI |
| Stack domination (NEW) | `StackMaximizerDomination` | bounded dominating stack ⟺ WCI |
| Target | `mcaConjecture` (`GrandChallenges.lean:650`) | the prize predicate |

**The L²→L∞ verdict stands:** every proven input is L²/aggregate; the offset-magnitude set equals
the global spectrum (`lineEta_image_eq_globalImage`), `#dev = q−1`; bounding the worst offset IS
bounding M. **Moment-exponent quantification:** the pure 2r-th-moment route yields exponent
`θ(r,β) = (β+r−1)/(2r) > 1/2` always; non-triviality (`r > β−1`) coincides with the DC crossover
(`r > β`) where char-p Wick is already refuted; the prize `θ = 1/2` is the unattained `r → ∞`
limit. **The moment route is the route to Paley.** (⚠️ the Lean brick claimed for this,
`MomentExponentThreshold.lean`, is NOT on main — §12; the arithmetic is elementary and worth
re-landing.)

---

## 3. SOTA and the external literature — why the wall stands

Object: `M(n) = max_a |Σ_{x∈H} e_p(ax)|`, `H = μ_n`, `n = p^γ`, `γ = 1/4`. At the prize point the
only proven bound is BGK `n^{1−o(1)}` — off the `√n` target by a half-power.

| Result | Bound | Status at β=4 |
|---|---|---|
| Weil / RH-curves | `(n−1)√p` | vacuous (0-dimensional `μ_n`) |
| Heath-Brown–Konyagin (Stepanov) | needs `n ≫ p^{1/3}` | vacuous |
| Shkredov energy | needs `n ≫ p^{1/3}` | vacuous + √-lossy |
| di Benedetto et al. 2003.06165 | `n^{1−31/2880}·(p^{1/72})` | boundary-vacuous (saving→0 at `n ↓ p^{1/4}`) |
| **BGK** | **`n^{1−o(1)}`** | only survivor; `o(1)` ineffective (BKT+BSG, non-constructive) |
| Paley Graph Conjecture | `≈√n` | OPEN everywhere |

- **Why di Benedetto dies at β=4:** the trilinear `p^{1/4}` prefactor eats the `191/2880` saving to
  `31/2880`; worse than trivial for `β > 191/40 = 4.775`. Campaign specialization with exact Sidon
  energies `T₂ = 3n²−3n`, `T₃ = 15n³−45n²+40n` (`_AvL_T3ClosedForm`, axiom-clean) reaches exponent
  `0.9583` at β=4 (≈3.9× the generic saving) — **SOTA-closeness, not closure**.
- **Unconditional plateau:** `M ≤ n^{1+2.25/r}` = Johnson at `r = log n`; the effective sum-product
  method is structurally dead at/below `p^{1/4}`.
- **#464 literature gates (each formalized as the precise missing transfer, in `Frontier/_D*.lean`):**
  D0 EVW homological vanishing — **airtight-killed for F_p** (Jacobi self-braiding non-torsion ⟹
  infinite Nichols algebra; function-field side untouched); D1 convolution-squaring bootstrap —
  consumer of the Paley start value, not a bootstrap; D2 Rogers–Siegel variance — gated on a
  pointwise prime-to-lattice coupling (would DECIDE the lower-tail sliver, §6); D3 Tsang high
  moments — range-gated (`2r ≤ β`, constant depth only); D4 MacMahon margins / permutation-insdel
  rank — no bad-mass bound / generic-locus gap (worst far config is non-generic: twisted `x^a(x+1)`
  gives 27 vs monomial 9 bad scalars at n=16); D5 ℓ-adic monodromy families — doubly blocked
  (`weil_exceeds_prize_by_2pow60`). Sawin–Shusterman short-sum sheaves stop exactly at the flatness
  wall (interval structure required, multiplicative subgroups excluded verbatim). Anti-resonance
  (Chapman–Mudgal 2605.15434) and non-backtracking Ihara–Bass (2606.27075) are **unrun probes** (§6).
- **No 2024–2026 paper crosses `n^{0.989} → n^{1/2}`** at β=4 for thin 2-power subgroups (multiple
  sweeps incl. a 67-paper harvest + three #464 sweeps of 29+26+35 papers against the foreclosure
  ledger). The missing analytic input does not exist in the literature.

---

## 4. Why every elementary route is dead — the theorem-level no-go landscape

### 4.1 The Meta-Theorem (second-order no-go)
Every second-order method (energy of any order, L²/Parseval, spectral λ₂, SDP/Delsarte-LP,
cumulants, the Shaw operator) provably caps at Johnson/√p (`MetaTheoremSecondOrderCap`,
`_MomentLadderExceedsPrize`). A winning method must be simultaneously **b-sensitive**,
**deterministic-archimedean**, and **genuinely L∞** — the probabilistic-EVT crown is killed
(periods are exchangeable, covariance distance-independent).

### 4.2 The Tetrachotomy (no fifth door)
(i) Algebraic geometry — CLOSED (0-dimensional; disc CFT-fixed ⟹ wall is archimedean);
(ii) additive combinatorics — engages the object but saturates at `n^{1−o(1)}`;
(iii) harmonic analysis — CLOSED (needs curvature; `μ_n` is flat);
(iv) probability/moments — works only at `r* ≈ ln p` where it IS the wall. 250+ generated
conjectures collapse into these four. **No fifth branch** (14 distant fields tested, zero survivors).

### 4.3 The Arithmetic Uncertainty Principle
`(knowable by magnitude)·(needed from phase) ≥ √m`: magnitude methods resolve to `√p` or Johnson;
the truth `√n` needs phase information provably absent. To violate it is to cross the Burgess
barrier. (Explains the wall's existence; not a key.)

### 4.4 #464 additions — the door-(iv) face and the bounded-complexity principle
- **Worst-b structure (all axiom-clean):** the worst frequency phase-aligns its coset halves
  (ρ(b\*) = 1.00000 exactly at every n) but is strictly imbalanced (median r(b\*) ≈ 0.83, a
  stationary O(1) band — an earlier "divergence" claim was corrected as a 3-point artifact);
  measured per-level tower growth `M(μ_n)/M(μ_{n/2}) = 1.74/1.54/1.46 > √2` kills recursive
  √2-descent (`no_sqrt_two_perLevel_thinning`); greedy heavier-half descent is exact but inert
  (`G/√n` grows); partition-depth invariance at every dyadic refinement.
- **The gap-combinatorial face is CLOSED:** gap values ≤ n/2+1, curvature = n, gap-DFT rank = n−1,
  longest run O(1) — all dilation-invariant or wrong-direction (`_DoorIVGap*`,
  `_DoorIVPhaseCurvatureGeneric`). The only remaining door-(iv) hope lives in the multiplicative
  `{b·x^m}` phase arithmetic that gap geometry coarsens away.
- **Graph-relation reformulations are tautological:** clique-cover, color, endpoint-second-witness,
  coordinate-overlap budgets each collapse to the original singleton cap
  (`relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden` etc.).
- **The bounded-complexity principle** (unifying cause, 6-framework assault, winsCount = 0 twice
  refereed): every √-cancellation-breaking method needs bounded complexity; the thin 2-power
  subgroup forces unbounded complexity (degree-`n/2` cyclotomic field, degree-`2^128` monomial lift,
  `(2w)^{n/4}` norm height — the improved bound, still exponential — flat geometry).
- **Symmetry-reduction trap:** orbit-summing any LP/SDP/eigenvalue program under μ_n's automorphisms
  regenerates `Σ e_p(bx)` verbatim — keep programs unsymmetrized. **AG point-counting trap:**
  incidence cohomology factors through the rank-~n character sheaf ⟹ Deligne vacuous.

### 4.5 The structured-prime lever is quantified-dead
Depth-R Stickelberger/prime-splitting ceiling `p ≤ w^{n/(4R)}` is non-vacuous only at `R ≈ n/8`,
super-polynomial at prize depth `R ≈ β ln n` (`_wf5M2_stickelberger_depth`). High-`v₂(p−1)` primes
are worst at β=3 but benign at β=4.

---

## 5. Discoveries and firsts (machinery and cartography — not a closure)

**Structural reductions / equivalences:**
- Two-sided prize ⟺ char-sum (`_EnergyRatioMonotoneReduction`: `ERM-at-r ⟺ max‖η_c‖² ≤ (2r+1)n`).
- The Meta-Theorem + Tetrachotomy + AUP (route-elimination as theorems).
- Mandatory DC-subtraction (`DCEnergyEssential`) — invalidated a whole class of naive moment attacks.
- The Paley dictionary formalized (`GeneralizedPaleyRamanujan`, `GaussPeriodMomentBound`).
- I031 ⟷ #407 unification; I031 chaining entropy reduction proven **cosmetic**
  (`i031_chaining_cosmetic`: the `log(p/n)` collapse cancels under the outer 2r-th root).
- **NEW: the line-list counting stack** (verified on main) — and the claimed weld
  `mcaDeltaStar_ge_of_farLineListBudgeted` (first slack-free connection of list-counting to the
  actual `epsMCA`/`mcaDeltaStar` objects, with `aligned_line_lambda_ge_q` forcing the
  far-restriction). ⚠️ The weld file itself is a §12 phantom — re-land it before consuming.
- **NEW: the field-closure trichotomy** — all-stack sharp closure at a field ≡
  `¬FloorBad ∧ WorstCaseIncidenceBounded`; supply arguments (Linnik/TZ) can only discharge the
  floor-good half.

**Exact closed forms / identities:**
- Char-0 energy ladder E₂…E₃₃ (leading coeffs `(2r−1)‼` through E₁₃ = 25‼); char-0 cumulants; CGF
  `½ log I₀(2t)`; MGF = lattice theta (rank n, covolume p, `λ₁² = 2`, kissing number n).
- Over-determined incidence `2m³−2m²+1 = Θ(n³)` (Johnson cap); crossing law `D = z + S·O`.
- **NEW: exact per-line high-multiplicity identity**
  `(weight(e₁) + #{i: e₁ᵢ=0 ∧ e₀ᵢ≠0} − w)·#{γ: weight(e₀+γe₁) ≤ w} ≤ weight(e₁)` and the
  ratio-degree local gate: bad set empty-or-singleton `{−c}` classified exactly by `P = cQ`
  (`RatioMultiplicityBridge`, hypothesis-minimal).
- **NEW: MDS coordinate-fiber endpoint** `coordinateAgreementFiber_card_le_one_of_k_le` (`#S ≥ k ⟹`
  fiber ≤ 1) — the high-profile discharge that localizes everything to `t < k`.
- **NEW: the canonical width-four lane, closed at every fixed scale:** `canonicalRatioPoly n =
  (X⁴+1)^n − (X²+1)^n`; exact bad-prime sets n=16 → {17}, n=32 primitive → {97,641,673,1153}
  (Bezout certificates); resultant height gates (crude `2^{n+1}`-totient and sharp Landau/Mahler);
  concrete witness ladder n = 16, 32, 64, 128, 256, 512, 1024 … 32768
  (`CanonicalWidthFourConcreteTZ*.lean`); norm-height halving `|N(β)| ≤ (2w)^{n/4}` (verified n≤256).
- **NEW: moment-exponent threshold** `θ(r,β) = (β+r−1)/(2r)` (machine-checked: `θ > 1/2` always;
  non-triviality ⟺ DC-crossover).

**Invented instruments:** the Jacobi/recurrence-coefficient tool (form D); the Shaw value
`Sh(n) = limsup M/√(n log(p/n))`; the Wraparound Variance Law; the modular lower floor
`M ≥ √3·√n` (`_AvFloor_MomentRatioLowerBound`); the iid-Gumbel backward derivation (upper half
formalized: `prize_scale_bound_at_saddle` conditional on `DCEnergyBound`; inverted K ≈ 0.21 stable).

**The floor resolution (#464):** exact validated scanners (`floor_scan_exact.c`, reproduces n=16
ground truth exactly); floor-bad(16) = {17} (15.4M patterns), floor-bad(32) = {97} (15,366,400
patterns full-scan; 193/257/353/449/577/673 all GOOD); TZ sub-quartic 12/5 confirmed unconditional
for dyadic moduli; the Linnik rung instances + TZ arrow formalized
(`_FloorLinnikRungInstances`, `_FloorLinnikThornerZamanArrow`, `tzSupplyOne_gives_prime_below_prize`);
the guard lemma `canonicalN32PrimitiveBadPrimes_ne_singleton97` (width-four-bad ≠ floor-bad —
landed specifically to forbid a tempting conflation).

**Corrections to the record:** BCHKS-1.12 vacuity caught; master-gap off-by-one fixed; the proxy
artifact traced; phantom bricks recovered and resolved (§12); numerics-cannot-decide proven.

---

## 6. The live frontier — ranked open avenues (what a next agent should actually do)

### Tier 1 — the sharpest open surfaces

1. ~~**The windowed SumsetExtremal crux.**~~ **REFUTED AT SCALE 2026-07-01 (round 1, replicated):**
   at n=16, k=4, in-window a=7, a 2-Fourier-component direction (`x^4+c*x^14` shape) strictly beats
   every monomial (13-14 vs 9) at THREE primes across two v2 classes (65537/65617/65633),
   brute-verified witnesses; a = k+1 is direction-blind (`FirstInteriorLevelDirectionBlind`), so
   only a >= k+2 discriminates — and there spread wins. The monomial-extremality ansatz is FALSE
   in-window; the guard-cell catalogue route as designed is dead. See
   `deltastar-466-p5-replication-2026-07-01.md`, DISPROOF `466-r1-windowed-extremal-spread-beats`,
   commit `fe272cc43`. **Survivor (round-2 lane W1): the bounded spread-excess law**
   `worst_spread <= C*worst_mono` (measured C <= 1.56, conjectured C <= 2) — a weaker per-cell
   input that still feeds the weld's far-line budget; the excess is constant-factor, so all proven
   brackets are unaffected. Original statement (record): prove (or refute *in the window*): a ≥2-Fourier-component
   spread direction cannot beat every pure monomial component, for
   `δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))`, `q` large. This = min-weight dual-RS hyperplane capture = the
   Paley eigenvalue in extremality clothing. Sockets built: `SumsetExtremalityGuard.lean`,
   `mcaDeltaStar_pin_of_finsetGuardCover(_orOutside)` (instantiate a real guard-cell catalogue and
   prove the outside-branch budget).
2. **Line-list production obligations** (the counting surface closest to the prize object):
   - ~~first, re-land the weld~~ **DONE 2026-07-01 (round 1, referee-verified, commits
     `537959141`/`bd546962c`)**: `mcaDeltaStar_ge_of_farLineListBudgeted` is a THEOREM (root
     `LineListMCAWeld.lean`), with a strengthened derivation: witness-farness is FREE from the
     `¬pairJointAgreesOn` clause (aligned directions carry ZERO bad scalars); direction-coset
     invariance makes the residual branch exactly the large-zero stratum; the far-restriction is
     proven both NECESSARY (`aligned_line_lambda_ge_q`, `not_uniform_lineListBudgeted_of_lt_card`,
     `not_forall_nonvanishing_lineListBudgeted_of_lt_field`) and SATISFIABLE. Historical round-1
     form at `Frontier/LineListMCAWeldRound1.lean` (nonvanishing-only consumer carries a vacuity
     warning). Its open inputs are the next bullets. Original task (record): re-derive from the chain
     (`badScalars_eq_explainable` → `explainableFilter_subset_lineBadScalars` →
     `lineBadScalars_card_le_lineAppearingCodewords_card_mul`); the substrate names all exist;
   - the **low-profile theorem**: bound exact-appearance fibers `D(t)` for `t < k` on large-zero-safe
     lines with combined fit `puncturedWeight + Σ_{t<a} choose(#zeroSet(u₁),t)·D(t) ≤ 2B`;
   - the **mixed-profile top-fit arithmetic**: prove/refute `Low/FullMixedChooseProfileTopSumsFit`,
     `FieldPow*TopFit` (contracted to the single endpoint `z = n` — "the next step is arithmetic,
     not API plumbing");
   - the **second-witness / multiplicity floor**: prove `NoUniqueBadScalarWitness` on hard lines, or
     exhibit a unique-witness bad scalar; the pairwise-interpolation relation (two singleton scalars
     force a second witness / an RS dependence / a small classified pencil) is the one graph-route
     shape not yet exhausted;
   - **`CandidateListExactSuccessor`**: the successor/renormalization law for the floor predicate
     (or its adjacent-rung counterexample `R(a) ∧ ¬R(a+1)`) — with prefix+successor+budgeted-max the
     in-tree `deltaStar_pin_of_*` consumers fire.
3. ~~**Hankel-positivity / Lax-pair spectral-shift on the Jacobi turnover**~~ **BOUNDED WINDOWS
   REFUTED 2026-07-01 (round 1):** the early recurrence window is ensemble-deterministic
   (`1−q_j = c_j(n)/p` — reads p, not the instance; countermodel pair 65617/65633: identical
   4-window to 7ppm, k\* differs 21%), so no O(1)-window Jacobi functional pins `k*` per-prime
   (DISPROOF `466-r1-hankel-bounded-window-refuted`). The seam survives ONLY as global variance
   certification = the independence form (§2.4). Kept diagnostics: the Hankel double-ratio Fermat
   anomaly detector (~52× at moment order 6, deployment-screening candidate); the spacing law
   `b_j² − b_{j−1}² ≤ (1+ε)n` (all instances); the exact j=1 ramp law (round-2 lane: j=2,3 proof).
   Original text (for the record): the Toda invariants provably don't determine `k*`; the
   spectral-shift inequality hope was — "the one surviving non-magnitude seam."
4. **Uniform-in-μ floor-bad characterization** ("floor-bad = {smallest prime ≡ 1 mod n}"): verified
   a = 4, 5; prove it uniform (the scanner + successor contracts are in place) — the only route
   terminating at a known theorem (least-prime-in-AP, now unconditional at 12/5). Remember the
   meta-verdict: this closes an obstruction, not the prize; the floor→δ\* arrow is a separate gap.
5. ~~**Bold attack #5: di Benedetto pushed to an effective 1/2 exponent at β=4.**~~ **CLOSED
   2026-07-01 (refutation-with-exact-constants, double-refereed by two independent sessions):**
   `Frontier/_BGKEffectiveHalfPlateau.lean` (commit `537959141`) + `probe_466_dibenedetto_push.py`.
   The sharpest explicit iterated-BGK (Shkredov 1705.09703 Cor. 16, per Kowalski 2401.04756
   Rem. 1.2(3)) gives n-saving exactly `1/16384` at β=4 (k = 12 squarings; clean applicability
   floor `2^768` ≫ prize `2^30`); the trilinear ceiling `1/24` (in-tree) dominates it 682×;
   saving 1/2 is unreachable at any depth (`1/2^{k+2} < 1/2` structurally, Shkredov Rem. 17);
   the multilinear chain with perfect energies IS the moment ladder (`θ(s,β)` dictionary,
   probe-verified). With `deltaStar_determination_all_or_nothing`, ANY fixed θ > 1/2 is
   δ*-irrelevant — the whole exponent-pushing axis is dead for the prize. See
   `deltastar-466-bgk-effective-half-plateau-2026-07-01.md` +
   `deltastar-466-exchange-rate-essay-2026-07-01.md` (the tariff-table re-ranking of this list
   toward the exact/counting surfaces: items 1, 2, and the integer form of 3).

### Tier 2 — decisive probes not yet run

- **Anti-resonance dichotomy** (Chapman–Mudgal): is the worst `b` anti-resonant? (empirical gate).
- **Non-backtracking / Ihara–Bass** `b_m = q^{m/2}·T_m(A/2√q)` on `Cay(F_q,μ_n)` — "the only sliver
  that could beat √q"; probe not run.
- **D2 Rogers–Siegel decision**: concentration ⟹ final no-go brick; heavy lower-tail ⟹ the
  "prize prime as large-deviation anomaly" sliver genuinely reopens. Gated on a pointwise
  prime-to-lattice coupling.
- **Tsang level-splitting probe**; **Kravchuk moment-interlacing** numerical check (`SCL_ρ` vs
  `1−√ρ`; risk: re-derives Johnson); **I031 Lamzouri-type union bound** over the collapsed index set
  (is the entropy reduction exploitable at the *tail* rather than the moment?).

### Tier 3 — bankable wins off the core (real value, no wall contact)

- **Folded-RS / subspace-design capacity pin** (JLR 2601.10047 Lemma 5.12 + GG25): MCA to capacity
  with zero character sums for folded RS — FRI/STIR/WHIR already fold. Lean-actionable via
  `curveDecodable_of_structured_close_set_budget`. (The naive fold→plain transfer is formally
  refuted — `FoldingTransferNoGo` — the folded pin itself is live.)
- **Additive/Binius domain dissolution**: for an F₂-subspace S the far-direction eigenvalue is 0 or
  |S| by orthogonality — the Johnson→capacity gap is a multiplicative-domain artifact; clean finite
  formalization (caveat: hardness may relocate to `S^⊥`-cosets).
- **Explicit ε\* certificates at deployment primes**: M = spectral radius of an f×f period matrix;
  Arb-computable for BabyBear (f=15) / KoalaBear (f=127); not Goldilocks.
- **ThornerZamanPNT discharge** (the B3 ceiling's named analytic input, "largely dischargeable");
  **landable bricks** flagged in-thread: `widthFourGood_of_resultantHeight`,
  `deployerFloor_iff_R1_and_R2`, compile `_AvDeployerFloorSeparation.lean` (currently a NON-COMPILED
  scaffold with explicit sorries), per-octave `resultantHeight_R32_le`/`_R64_le`, the
  `e2BadScalarSet` orbit census, pin `D_3`/`height(R_3)` exactly.
- **Function-field model theorem** (the F_p no-gos don't cover `F_q[t]` smooth domains; EVW is
  killed for F_p only).
- **B2 curve-decodability bricks**; **B4** (Crites–Stewart: "CA ⟹ MCA, unknown even for lines") —
  named exact open problem.

### The tool-shape principle (from the #464 killing fields)
Any future survivor must be an **L∞/sup-control method fed by computable second-order data** —
Talagrand γ₂/generic chaining is the canonical candidate shape (L∞-native; needs sub-Gaussian
increments under SOME metric — the needed increment sub-Gaussianity is currently exactly the open
Wick atom, but the Jacobi cocycle could conceivably supply a different metric).

---

## 7. The synthesis essays (conceptual scaffolding)

- **Shaw value & the four doors** (`shaw-value-missing-mathematics-2026-06-18`) — prize ⟺
  `Sh(n) = O(1)`; 14 distant fields, zero survivors.
- **Arithmetic Uncertainty Principle** (`arithmetic-uncertainty-principle-essay-2026-06-19`).
- **Wraparound Variance Law** (`the-wraparound-variance-law-essay-2026-06-21`) — "nothing left to peel."
- **The expert-facing open problem** (`proximity-prize-open-problem-for-number-theorists-2026-06-21`)
  — forms (A)–(D) with the β=4 evidence table; any proof must use thinness load-bearingly.
- **iid-Gumbel backward derivation** (`backward-derivation-from-empirics-Mn-is-iid-Gumbel-2026-06-17`).
- **#464 essays:** the ∃/∀ deployer-vs-analyst separation (Claim 1 proven; R1 width-four closes
  unconditionally via crude Mahler; R2 corrected ON-BGK the same day); the outright-attack ledger
  (`deltastar-464-outright-attack-ledger-2026-06-27.md`) — four attacks written as proofs then
  refuted, residues = Tier-1 items 3 and 4 above; the independence localization (§2.4).

---

## 8. Dead / refuted ledger — do NOT re-attempt

> Full catalogue: `DISPROOF_LOG.md` (1.66MB, 59 tagged entries, current through 2026-06-27) +
> `docs/kb/deltastar-464-*.md` (~150 notes). Check both before trying anything.

**⛔ Reduces to the wall (proven):** line-decoding/collinearity; BCHKS-1.12-as-budget (vacuous);
crossCell tower iteration; even-moment face; restriction/extension; Gross–Koblitz/p-adic;
theta/AFE + de Finetti; circle method; Elekes–Szabó; polynomial method/slice-rank; hyper-Kloosterman;
random-RS transfer; cosh-MGF/Bessel saddle; per-coset descent; bilinear/cube/free-prob/RMT;
tropical/BKK; Carlitz/FF-RH; LP/SDP third route; theta/ideal-lattice; Delsarte/Beurling–Selberg;
Stepanov (fully closed); antipodal-tower descent; completion sums; OSV short-Weil; band dichotomy;
10 "new-math" relocations (Terwilliger, Bourgain–Gamburd, Amice/Iwasawa, Kelley–Meka/PFR, chaining
metric-blind, …); 50-/72-/100-/140-/250-conjecture sweeps (0 survivors); **#464:** six non-period
angles (bandlimited rigidity, syzygy rank, Hasse multiplicity, agreement-set energy, dyadic coset
rigidity, line-Johnson — all = the 2-power uncertainty failure, Loukaki); three √-breaking templates
(Weil lift `m = 2^128` vacuous; curvature methods flat; Bombieri–Vinogradov length ≫ Q²);
concentration/arc framing (3 routes); D0–D5 paper gates; FHK log-correlated (killed by experiment);
EVW (killed for F_p); first-moment good-prime averaging (`E_p[W_r] ≫ Wick` — the average prime is
bad); `_RatioIncrementWickLadder` (margin decay 22→11→2.7%); I031 chaining (cosmetic); Bilu/Arakelov
& adelic & Bogolyubov (wrong direction / phase-blind / size-only); Weil explicit formula;
large-sieve positive-proportion (still deep-r energy at r ≈ 128).

**⛔ Johnson-locked:** over-determined far-line count Θ(n³); Hab25 (nothing past Johnson);
plateau-dichotomy proxy; complete-homogeneous floor; unconditional `n^{1+2.25/r}`.

**❌ REFUTED-FALSE (machine countermodels):** raw `GaussianEnergyBound` past DC crossover;
`W_{r*} = 0`; guard-free `SumsetExtremal`; support-eligible line-list capstone
(`aligned_line_lambda_ge_q`); raw field-power fiber envelope (any `B < |F|^k`); raw singleton
field-power (any `2B < |F|^k`); ambient support-ratio below `|F|·choose(n,a)`; graph-relation
budgets (tautological); raw width-four `Cd₀NonCollision` (antipodal collision; repaired mod-sign);
"ramified ⟹ floor-bad" (97 unramified yet bad); floor-bad(32) = {257} and = {97,193,257,1153}
readings (exact scanner: {97}); Gumbel-fixed-K; small-ball/Halász; bad-set Sidon; √q-completion
resonator; per-frequency localization (thickness-invariant); odd/signed thin-cancellation; additive
large sieve; fewnomial; reverse LD⟹MCA; per-codeword heavy-scalar domination (spread factor
`(n−z)/(a−z) > n/a` favors the adversary); five beat-SOTA mechanisms (multilinear k-fold,
multiplicative-energy lever, shifted-Burgess r=4 [conditional on open E₄], 2-power-Stepanov tower,
free best-effort saturating 0.9583).

**⚠️ Artifacts:** thin-Sidon r_min advantage (decays); balance-enrichment (sampling artifact —
full scans show imbalance band); worst-b "divergence" (3-point artifact; median flat); "K_eff creep"
(saturates at n=256); "m\* ~ log n" (engine direction-cap artifact; far-line m\* is LINEAR n/4−1).

**🚫 Larp / vacuous:** DFT-uncertainty at 2-powers (Loukaki proves it CANNOT hold — why the prize
fixes 2^μ); `_AntipodalPlotkinHalfCap`; `_Close27_*` tautologies; FLOOR_A2 transitivity shell;
WraparoundVariance abstract-ring restatement; N9 codim-2; toy `deltaStar_pin_mu6_dim4`.

---

## 9. The off-BGK floor — RESOLVED as obstruction-removal (the #464 verdict)

- **The object:** floor-bad(n) = primes where some adjacent 7th-type pattern is realizable
  (`rank[M_A] = rank[M_A|b_A]`); binder family `w_g = x^{3n/4} + g·x^{n/2}`. 0-dimensional /
  divisibility question, genuinely not a character sum (defect count flat in p).
- **Resolved:** floor-bad(16) = {17}, floor-bad(32) = {97} (exact validated scanners, full pattern
  enumerations); the smallest-prime characterization holds at a = 4, 5. TZ sub-quartic **12/5
  unconditional** for dyadic moduli (Siegel zero eliminated, d = 2 fixed) ⟹ every prize prime
  (`p ≈ n^4`) is floor-good, **unconditionally** — the binder obstruction is gone at every scale.
- **The meta-verdict (§16 of v2, stands):** `ε_mca` is a sup over ALL stacks; the floor object is a
  lower bound for ONE direction; **δ\*-pin ⟹ floor-good, never conversely.** The floor was the
  campaign's one "different" route; it removes an obstruction and is provably incapable of
  supplying the prize.
- **Still open here:** the uniform-in-μ characterization (Tier-1 item 4); the floor→δ\* arrow;
  and the guard fact width-four-bad ≠ floor-bad (`ne_singleton97`) — two different finite objects.
- **The conjugate-count no-go guards the whole lane:** `|N(β)| ≤ (2r)^{n/2}` (improved: `(2w)^{n/4}`)
  is exponential regardless of sparsity — only inter-conjugate phase cancellation (= BGK) beats it;
  divisibility/existence questions survive, cancellation questions don't.

---

## 10. Numerical evidence (and the proof that numerics cannot decide it)

- **Wall constant** `C = M/√(n log(p/n))` at β=4: `1.07, 1.21, 1.31, 1.49, 1.42, 1.39, 1.28, 1.33`
  (n = 8…1024 single-prime column), mean ≈ 1.285, hugging √2, **no upward drift** (~900 primes).
  Worst `M/√(2n log p)` = 0.655…0.837 (β=4) and 0.79–0.82 (β=3 high-v₂, n=512/1024) — all < 1.
- **K_eff** (DC-subtracted): peak ≈ 0.60–0.67, flat n=32→256, saturating (the early "creep" resolved).
- **GPU worst-case list** (n=64, ρ=1/8): L=0 across δ∈[0.64,0.80]; explodes only within ~0.03 of
  capacity — floor-structure supported at that octave.
- **iid-Gumbel ratio** `M/(√n·a_m)`: 0.916…1.018 (n=8…256), centered on 1.0.
- **Independence experiment (#464):** log-field autocovariance ≈ 0 at all lags (kills FHK);
  `M/√(n log m)` decreasing 1.28 → 1.12.
- **Per-level tower band:** growth 1.74/1.54/1.46 (n=16/32/64) — above √2 at small n; its asymptotic
  fate is exactly the tower form of the core.
- **Why numerics cannot decide:** the wall lives at `r ≈ 89`, `n = 2^30`; exact probing caps at
  `r ≤ 6`, `n ≤ 1024`; the distinct-γ growth law is provably undecidable below n ≥ 256; the data is
  consistent with both prize-true and BGK-tight.

---

## 11. The substrate and how to continue (everything a fresh agent needs)

### 11.1 Start here (in order)
1. **This dossier** (`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`).
2. **`ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`** — the compiling
   single-file Lean workspace: exact target, regime, `#check`-verified substrate, walls, closure
   contract, `▼ YOUR CONJECTURE HERE ▼` slot, and the 2026-07-01 state-of-play section.
3. **`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`** (auto-loaded; `AGENTS.md` is a copy) —
   build recipe, ledger, pitfalls.
4. **`DISPROOF_LOG.md`** + `docs/kb/deltastar-464-*.md` — check before re-trying ANYTHING.
5. `docs/wiki/residual-census.md` — named-residual conventions.

### 11.2 Build (mandatory — or you clog the 16-core box)
- The cone is 1,600+ files; `lake build` traces a 3,000+-job graph and takes the build lock.
  **Never bare `lake build`.** Warm once: `scripts/pg-warm.sh`. Iterate: `scripts/pg-iterate.sh
  <file>` (~30–75s, no lock, parallel). One real `./scripts/lake-locked.sh build <module>` before
  landing (autoImplicit differs between the fast path and the real build — declare every binder).
- CI gate: `scripts/forbidden_tokens.py` (catches bodyless `opaque` and `: True` laundering) — run
  it plus the KB pipeline (`check_generated.py`, `kb/lint.py`) per batch.
- Locate declarations by THEOREM name (`grep -rln 'theorem <name>'`), never by path. Keep a /tmp
  copy of in-flight files. Probe scripts go in `scripts/probes/`; a theorem must MATCH a probe
  before you trust it.

### 11.3 The core substrate API (import, don't re-derive)
- **Bracket engine:** `mcaDeltaStar`, `le_mcaDeltaStar_of_good`, `mcaDeltaStar_le_of_bad`,
  `unique_bad_gamma_common_witness`, `JohnsonListBound`, `epsMCA_interleaved_eq`.
- **Incidence/floor:** `OpenCoreConditionalPin.WorstCaseIncidenceBounded` + `worstCaseIncidence_pin`;
  `FarCosetExplosion.epsMCA_ge_far_incidence`; `GaussPeriodParsevalFloor`;
  `_PrizeFloorOfBGK.prizeFloor_window_of_BGK_and_incidence` (incidence ⟹ δ\*-window, airtight).
- **Line-list stack (NEW #464):** `LineListReduction`, `LineListAppearanceFiber*`,
  `LineListSupportRatio*`, `LineListIncidenceMultiplicity`, `LineListSingletonDefect*`,
  `LineListCodewordSingleton*` — with exact failure scanners at every layer; the residual is
  localized to low-t fibers. (⚠️ the prize-facing weld `LineListMCAWeld` is a §12 phantom —
  re-land first.)
- **Floor machinery (NEW #464):** `FloorNecessaryNotSufficient`, `FloorClosureSuccessorScanner`,
  `FloorClosurePrefixConsumer`, `FloorFiniteRungUniformityBarrier`, `FloorLevelDepthPrimeScaleGate`,
  `_FloorClosureContract`, `StackMaximizerDomination`, `_FloorLinnikRungInstances`,
  `_FloorLinnikThornerZamanArrow`.
- **Canonical width-four lane (NEW #464):** `E2W4CyclotomicNonCollision`,
  `CanonicalWidthFourBadPrimeSet`, `CanonicalWidthFourConcreteTZ{64…32768}`, `SharpResultantBound`.
- **Energy + DC trio:** `_AvL2_E*ClosedForm` (E₂…E₃₃), `_CharZeroWickEnergy` /
  `DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic`, `MetaTheoremSecondOrderCap`,
  `DCEnergyBound`, `DCSubtractedMoment`, `DCEnergyEssential`.
- **Gauss/Paley:** `SubgroupGaussSum*`, `GeneralizedPaleyRamanujan`, `GaussPeriodMomentBound`.
- **KKH26/TZ ceiling:** `kkh26_mcaDeltaStar_le(_of_not_dvd, _of_TZ)`, `KKH26ThornerZaman.TZPrimeSupply`,
  `tzPrimeSupply_{8..64}_*`, `_KKH26s128ThornerZamanBridge`.
- **Ratio-degree gate:** `RatioMultiplicityBridge` (`badWeight_empty_of_degree_exact` +
  empty-or-singleton dichotomy), `RatioProfileDegreeObstruction`, `HighMultiplicityBadCount`.
- **Guard rails:** `SumsetExtremalityGuard`, `_FixedParameterLimitTransferGate`,
  `_PolynomialThresholdDiagonalGate`, `_SubgroupExpSumPSavingGate` (ν ≥ 1/8 at β=4),
  `_BurgessShiftHolderExponentGate`, `FoldingTransferNoGo`, `DelsarteLPNoGo`.

### 11.4 File-naming conventions (`Frontier/`)
`_` prefix = scratch/in-flight until promoted. `_Av*` = avenue attacks; `_wf*` = workflow lanes;
`_DoorIV*` = door-(iv) bricks; `_AssaultV2_*` = the 2026-06-22 assault bank; `_D0…_D5*` = paper
gates; `LineList*` = the production counting stack; `*NoGo/*REFUTED/*Vacuous` = certified dead;
`Sweep_A##`, `O###` = DISPROOF_LOG IDs; `KKH26*/GG25*/Jo26*/Hab25*/ABF26*` = per-paper groups.

### 11.5 References
| tag | id | what |
|---|---|---|
| [ABF26] | 2026/680 | the prize paper; §4.5 `mcaConjecture`, §5 LD⇒MCA |
| [KKH26] | 2026/782 | explicit bad-line ceiling |
| [Jo26] | 2026/891 | general-generator factor; curve-decodability half |
| [GG25] | 2025/2054 | curve decodability (B2) |
| Chai–Fan | 2026/858, 2026/861 | FRI above Johnson via threshold-halving (protocol side, NOT δ\*); Conjecture 7.1 |
| ceilings | 2025/2046, 2025/2010 | up-to-capacity disproofs |
| [TZ24] | arXiv:2108.10878 | Thorner–Zaman; §3 powerful-modulus, θ = 12/5 for 2^a (CONFIRMED) |
| JLR | 2601.10047 | subspace-design capacity pin (folded) |
| NT core | BGK CRMA 2006; 2003.06165; 2309.09124 (PGC); 1809.09829; 2310.15378; 2505.22059; 1303.2729 | in `docs/references/proximity-gap-paley-spectrum/` |
| #464 gates | 2606.26440 (EVW), 2512.24080, 2606.24471, 2606.27020, 2606.10242, 2606.27323, 2606.22344, 2605.15434, 2606.27075, 2606.19075 | each with a formal `_D*`/gate verdict |

### 11.6 The split goal (don't conflate)
**(A) Protocol soundness above Johnson = RESOLVED** (Chai–Fan threshold-halving, ~2× query cost —
explicitly "does not claim the zero-loss proximity gap"). **(B) δ\*/zero-loss MCA = OPEN = this
dossier's mission.** Conflating them is the standing larp hazard.

---

## 12. Honesty audit — corrections, phantom-brick resolution, what not to cite

- **✅ The 2026-07-01 phantom flags are DISCHARGED (same day): `LineListMCAWeld.lean` and
  `MomentExponentThreshold.lean` re-derived and RE-LANDED** (commits `537959141` + umbrella
  `d6dcc2cfd`), **referee-verified by a second independent session** (independent real build,
  3541 jobs, all `#print axioms` = `[propext, Classical.choice, Quot.sound]`, 0 `sorry`). The
  re-landed weld is *stronger* than the #464 claim: `mcaDeltaStar_ge_of_farLineListBudgeted` now
  carries a **proven coset dichotomy** (`mcaEvent_direction_sub_codeword_iff` +
  `farFromCode_of_forall_coset_supportEligible`: every stack either shifts to a large-zero
  direction or is genuinely far), so the near branch is localized to large-zero directions
  (`hlow`) instead of a blanket hypothesis; the far restriction is proven FORCED
  (`aligned_line_lambda_ge_q` + `not_uniform_lineListBudgeted_of_lt_card` — a mid-flight
  first draft whose floor consumer quantified over all nonvanishing directions was caught by the
  referee session as vacuous-at-prize by its own refuter, and fixed before landing; kept as
  `Frontier/LineListMCAWeldRound1.lean`). Historical record of the original flags: both were
  claimed in the #464 thread (2026-06-26) but existed in no commit — the round-4
  ephemeral-worktree failure mode. Everything else headline-claimed in the thread verifies on
  main (spot-checked: the coordinate-fiber MDS endpoint, the field-closure trichotomy,
  `not_sumsetExtremal`, `ne_singleton97`, the TZ arrow, the door-IV bricks, the singleton-defect
  layer).
- **Phantom bricks (v2 §12): RESOLVED 2026-07-01.** Dossier v2 flagged `_DstarGrowthLaw`, `_OPSingleOrbit`,
  `_DyadicRecursionDstar`, `PrizeEquivalencePin`, `FloorResonanceEnergyBridge` (+ `_S2NonSymTower`)
  as "cited as landed but absent on every branch." The files were **recovered from an unpushed
  workstation branch** (now archived at `archive/444-charzero-dyadic-rigidity`, with ~83 committed +
  ~150 uncommitted #444-era files) and **all six compile axiom-clean against 2026-07-01 main**
  (`pg-iterate` + real build; `dStar3_gt_budget`, `OP_single_orbit_refuted`,
  `symmetric_dyadic_halving`, `no_second_order_route` etc. all `[propext, Classical.choice,
  Quot.sound]`) — landed with the recovery commit, so every previously-phantom citation now
  resolves. The #444 conclusions never depended on them (they were re-founded on
  `_MomentLadderExceedsPrize` / `_EnergyRatioMonotoneReduction` / `KambireDeepBandFloor` /
  `OverdetIncidenceMaxClosedForm`), and their contents are consistent with the settled verdicts
  (off-BGK routes dead; `O_P = n/8−1`; recursion refuted). The honesty lesson is operational:
  **push before the session ends; a cited brick must be verifiable on `main` at cite time.**
- **#464-era corrections (all caught in-thread, same-day):** guard-free `SumsetExtremal` false as
  written (fixed with window guards); the support-eligible line-list capstone vacuous
  (`aligned_line_lambda_ge_q`, replaced by the far-restricted form); R2 "off-BGK" retracted
  (Johnson ∨ wall); the r≤3 ladder-cutoff retracted (no finite-r cutoff); the width-four "Theorem 2"
  self-refuted pre-landing (`ne_singleton97` guard); the worst-b divergence corrected (median flat);
  balance-enrichment was a sampling artifact; CI was silently red until `3c6918435` (bodyless
  `opaque` + `: True` laundering — the binding gate is `forbidden_tokens.py`); round-4 lanes lost a
  genuine reduction to an ephemeral worktree (keep files, not just narratives); AssaultV3/V4 banked
  ~nothing new (redundancy — the wall is mapped); `_AvDeployerFloorSeparation.lean` is a NON-COMPILED
  scaffold (honestly labeled).
- **Standing retractions from v2 (still binding):** "δ\* climbs to capacity" (artifact);
  "prize ⟺ BCHKS-1.12 tight" (vacuous); `LamLeungUnconditionalQ` proves the foundation not the Wick
  bound; the S6 Betti/Deligne brick refuted on the math; `MomentRatioPeakAtTwo` self-refuted;
  "W₄ = 0 at Fermat 65537" false (W₄ = +4480).
- **The one forbidden move:** claiming `δ* = …` is a theorem with the open input silently
  discharged. A refutation is a win; never call the core closed.

---

## 13. Bottom line

δ\* for explicit smooth-domain RS in the window interior has been reduced — two-sidedly,
axiom-cleanly, and now with an exact rational target `δ* = (1−ρ) − m*/n` — to a single open
inequality: thin-subgroup BGK/Paley √-cancellation `M(μ_n) ≤ C√(n·log(p/n))` at β ≈ 4, `n = 2^30`,
depth `r ≈ ln q`. Every elementary, second-order, off-BGK, graph-theoretic, and literature-2026
route has been eliminated **as a theorem or a formal gate**; the fixed-depth side closes
unconditionally at every scale; the off-BGK floor is resolved as unconditional obstruction-removal;
and the one counting surface wired end-to-end to the prize (the line-list weld) has its residual
localized to a concrete low-profile fiber theorem. The evidence mildly favors the floor being true.
What remains is genuinely new mathematics: the windowed extremality crux, the low-profile counting
theorem, the Hankel/Lax-pair seam, the uniform floor characterization, and the un-run di Benedetto
push — plus a proof that must use thinness load-bearingly.

**The prize is OPEN and ON-BGK. Continue here.**

---

## 14. Round log — Round 1 (#466, 2026-07-01): plan → essay → 8-lane assault, double-refereed

Plan: `deltastar-466-research-plan-round1-2026-07-01.md`. Essay (5 new machineries, each
developed to its gap or death): `deltastar-466-essay-novel-mathematics-2026-07-01.md`.
Assault: 8 lanes + 8 independent skeptics (16 agents); all verdicts CONFIRMED (severities
minor/none). DISPROOF_LOG tags `466-r1-*`.

**(A) The §12 new-phantom flags are RESOLVED.** `LineListMCAWeld` re-derived and landed —
`Frontier/LineListMCAWeldRound1.lean` (8 thms; the weld is TRUE: `explainableScalars ⊆
lineBadScalars` holds; the far-free counting bound is genuine) **plus** the refined cone-level
`LineListMCAWeld.lean` supplying the REAL floor consumer `mcaDeltaStar_ge_of_farLineListBudgeted`
and `not_uniform_lineListBudgeted_of_lt_card`, which machine-confirms the skeptic's finding that
the non-far-restricted consumer is vacuous-in-practice (aligned directions force `Λ ≥ q` — the
same vacuity mode #464 once retracted; far-restriction is necessary AND sufficient).
`MomentExponentThreshold.lean` re-derived (ℚ-valued, sharper hypotheses, r=89 anchor). Both on
main (commit `537959141`).

**(B) Three Tier-2 probes RUN and CLOSED (never run before):** anti-resonance is **b-blind**
(dilation invariance washes out every residue-class statistic; future dichotomies must classify
coset-SETS); non-backtracking/Ihara–Bass is a **deterministic monotone relabeling** (the whole
spectral-preprocessing family closes; upgrades I037); Kravchuk moment-interlacing is **weaker
than Johnson** (semicircle `1/2+√(ρ(1−ρ)) > √ρ`; moments bound max agreement from BELOW only —
countermodel; joins the second-order cap).

**(C) The Hankel/Jacobi seam (Tier-1 #3) is REFUTED-for-bounded-windows** — countermodel pair
(65617/65633: identical 4-window, 21% different k*) + the mechanism: the early window is
ensemble-deterministic, `1−q_j = c_j(n)/p` (reads p, not the instance). Kept wins: the Hankel
double-ratio anomaly detector (Fermat at moment-order 6, ~52× amplification — deployment-prime
screening candidate); the pre-turnover bulge as a structured-prime signature; the exact j=1 ramp
law. The seam survives only as global variance certification = the independence form (no shortcut).

**(D) Windowed SumsetExtremal (Tier-1 #1) — crux RELOCATED:** at n=8 the first interior level
`a = k+1` is **direction-blind** (per-direction ceiling `C(n,k+1)` with generic saturation — an
identity in ALL n, so the discrimination question only has content at depth `a ≥ k+2`); at the
boundary a=4 all 340 directions tie at 9 (search-bounded, honest). n=16 interior (a=6,7 — the
first genuinely discriminating levels) launched.

**(E) Attack #5 (Tier-1 #5) EXECUTED AND CLOSED as a route to 1/2:** infimum exponent
`θ_min(β) = 1 − 1/(2β)` (7/8 at β=4) over the whole method family; binding = CS mass floor
`T_k ≥ n^{2k}/p` at depth `k=β`; unlimited-depth ladder reproduces the prize target (circularity
exact). Iterated-BGK quantified-dead (`_BGKEffectiveHalfPlateau.lean`: saving misses by 8192×;
Cor-16 floor `2^768` vs prize `2^30`). **SIDE-DISCOVERY (live):** bilinear (3,3) + √p-DFT
finisher ⟹ `M ≤ n^{8/9+o(1)}` at β=4 — beats the campaign's 0.9583 with one FEWER external
input (good-prime conditional, dies at β=6); independently re-derived by the skeptic; round-2
formalization lane.

**(F) Essay outcomes (machine-checked where claimed):** γ₂-chaining provably degenerates to the
union bound on flat-covariance exchangeable families (`_GammaTwoDegenerationGate.lean`,
axiom-clean) — chaining is the wall, not a route around it; vertical-MSS dead at both ends
(`_VerticalMSSGate.lean`, axiom-clean: min≤average + bad mean ⟹ vacuous); the typical-prime
sieve boundary `r_cross = β` confirmed (`probe_466_tps_boundary.py`) — three independent methods
(DC-crossover, moment-exponent θ, TPS) now agree the unconditional boundary is `r ≈ β`. Open
essay proposals CMK (Christoffel edge-crowding) and SST (sparse-section transference,
dilation-on-supports) went to round 2 with explicit lone-spike / section-statistics attacks.

**Net:** two phantom flags resolved, three Tier-2 slivers closed, two Tier-1 items closed
(one relocated, one executed-dead), one SOTA-adjacent discovery (n^{8/9}) pending
formalization, three new provable targets spun off (ramp law j=2,3; first-interior-level brick;
D4 scanner). **CORE unchanged: OPEN, ON-BGK.**

<sub>🤖 Consolidated 2026-07-01 by Claude (Fable 5) from the full #464 record (dossier v2 + 179
comments, three independent digests), the in-tree substrate, the recovered #444 workstation branch,
and independent re-verification. No fabricated closure; the core is carried as a named open
`Prop`.</sub>
