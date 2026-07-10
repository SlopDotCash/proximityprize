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

> **2026-07-10 rate-quarter correction.**  The exact first-prime prize instance is not confined
> to the above-Johnson window asserted by the July 1 snapshot.  The axiom-clean modules
> `_P1RateQuarterScaleConstruction.lean`, `_P1RateQuarterScaleBadCount.lean`, and
> `_P1RateQuarterScaleFinalConsumer.lean` construct `N+2` literal bad scalars and prove
> `mcaDeltaStar <= 23/48-2/(3N) < 1/2` for `N=2^30`, rate `1/4`, and error `2^-128`.
> `_P1RateQuarterOperationalBracket.lean` applies the full unique-decoding MCA bound at the
> exact rate-quarter radius `3/8`, proving the unconditional two-sided interval
> `3/8 <= mcaDeltaStar <= 23/48-2/(3N)` on that same concrete code and error target.
> A degree-saturated common-factor construction gives the stronger executable candidate
> `43/96+1/(3N)`, whose operational Lean assembly is still in progress.  These are upper
> and lower bounds, not an exact pin; closing the interval and the separate asymptotic BGK wall
> remain open.  See `deltastar-466-rate-quarter-thickened-isolated-upper-2026-07-10.md` and
> `deltastar-466-rate-quarter-common-factor-amplifier-2026-07-10.md`.

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

2. **The wall is two-sided, necessary, and now exhaustively mapped.** The machine-checked two-sidedness
   is `ε_mca(C,δ) ≤ E/q ⟺ WorstCaseIncidenceBounded C δ E` (round 14, `_TwoSidedCapstone.lean`, both
   directions axiom-clean). [⚠️ **Corrected 2026-07-04, round 14:** the older phrasing `ERM-at-r ⟺
   M ≤ √((2r+1)n)`, "floor and ceiling are the same object", is *prose* — only the forward direction
   `ERM ⟹ bound` is formalized (`gaussianEnergyBound_of_ERM`), and raw ERM/`GaussianEnergyBound` is
   itself DC-crossover-refuted (§2.3); the sup-norm `M` is a *strictly lossy* projection of the moment
   tower `WallHolds` (`_R14SupNormWeakerThanWall.lean`), so `M` and the Wick tower are **not** the same
   object. Use the DC-subtracted `WallHolds`, and the outer iff above, as the machine-checked forms.]
   Every second-order / energy / spectral / LP method
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
| Line-list | `LineListReduction` stack; weld `mcaDeltaStar_ge_of_farLineListBudgeted` re-landed in `LineListMCAWeld.lean` | floor ⟸ `Λ ≤ L ≲ ρn` on far lines |
| **Field closure (NEW)** | `floorClosureBudgetedMaxAtField_univ_iff_floorGood_and_worstCaseIncidenceBounded` | all-stack closure ≡ floor-good ∧ WCI |
| Stack domination (NEW) | `StackMaximizerDomination` | bounded dominating stack ⟺ WCI |
| Target | `mcaConjecture` (`GrandChallenges.lean:650`) | the prize predicate |

**The L²→L∞ verdict stands:** every proven input is L²/aggregate; the offset-magnitude set equals
the global spectrum (`lineEta_image_eq_globalImage`), `#dev = q−1`; bounding the worst offset IS
bounding M. **Moment-exponent quantification:** the pure 2r-th-moment route yields exponent
`θ(r,β) = (β+r−1)/(2r) > 1/2` always; non-triviality (`r > β−1`) coincides with the DC crossover
(`r > β`) where char-p Wick is already refuted; the prize `θ = 1/2` is the unattained `r → ∞`
limit. **The moment route is the route to Paley.** (`MomentExponentThreshold.lean` is re-landed;
see §12.)

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
- Two-sided prize ⟺ char-sum: the machine-checked form is the OUTER iff `ε_mca(C,δ) ≤ E/q ⟺
  WorstCaseIncidenceBounded` (`_TwoSidedCapstone.lean`, round 14, both directions axiom-clean). [The
  `_EnergyRatioMonotoneReduction` "`ERM-at-r ⟺ max‖η_c‖² ≤ (2r+1)n`" is forward-only in-tree
  (`gaussianEnergyBound_of_ERM`); the ⟺ is prose — the sup-norm is a lossy projection of the moment
  tower, round 14.]
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
   - ~~the **second-witness / multiplicity floor**~~ **REFUTED-WITH-MECHANISM 2026-07-02 (round 4,
     lane L2)**: unique-witness bad scalars exist on EVERY hard line tested; the extremal lines are
     ALL-singleton (`{1w:56}` at n=8 a=3 saturation, both primes; n=16 a=7 `{1w:8,2w:1}`, both
     primes) — and this is a THEOREM: the incidence cap `Σ_γ #fiber(γ) ≤ C(n,a)` on far-direction
     lines makes the floor and near-extremality mutually exclusive (`NoUniqueBadScalarWitness ⟹
     #bad ≤ C(n,a)/2`), and ceiling saturation forces every fiber singleton. The
     pairwise-interpolation relation is dead (the extremal object is a PERFECT MATCHING bad scalar ↔
     private `a`-subset). KEPT: the incidence cap (strict strengthening of the direction-blind
     scalar ceiling to Σ-multiplicities, all levels `a ≥ k`, production vocabulary).
     `Frontier/_SecondWitnessFloor.lean` (compile VERIFIED 2026-07-02: pg-iterate ✅ 330s, all 11
     `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no sorryAx; a=4 boundary row now
     2-prime replicated via `_out_466_second_witness_n8_q8273_a4.txt`),
     DISPROOF `466-r4-second-witness-floor-refuted`,
     kb `deltastar-466-second-witness-floor-refuted-2026-07-02.md`;
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

### Tier 2 — decisive probes: ALL RUN, ALL DECIDED (rounds 1+4; section retained as record)

- **Anti-resonance dichotomy** (Chapman–Mudgal) — **KILLED r1**, `466-r1-antiresonance-bblind`
  (b-blind on μ_n).
- **Non-backtracking / Ihara–Bass** — **KILLED r1**, `466-r1-nonbacktracking-relabeling`
  (deterministic monotone relabeling on `Cay(F_p, μ_n)`; no sliver past √q).
- **D2 Rogers–Siegel decision** — **DECIDED r4: CONCENTRATION**,
  `466-r4-d2-lowertail-concentration` (all 2038 primes at n=16: x = M/√(n log(p/n)) ∈
  [1.104, 1.218], lower tail thinner than Gumbel; the ∃-form/anomaly sliver is closed; gate
  brick `_D2LowerTailConcentrationGate.lean`).
- **Tsang level-splitting** — **KILLED r4, vacuous**, `466-r4-tsang-levels-vacuous` (exact
  level decomposition `E_r = Σ_k e_k`: generic-prime wraparound `N_k ≡ 0` through r=6 (n=8) /
  r=4 (n=16); level 0 carries 100.1–104.2% of `E_r` in every cell; nonzero levels sub-smooth —
  nothing to split past the closed diagonal `2r ≤ β`;
  `deltastar-466-tsang-levels-vacuous-2026-07-01.md`).
- **Kravchuk moment-interlacing** — **KILLED r1**, `466-r1-kravchuk-weaker-than-johnson`
  (no in-window content; re-derives ≤ Johnson).
- **I031 Lamzouri-type union bound** — **KILLED r4, cosmetic at the tail too**,
  `466-r4-i031-tail-cosmetic` (exact identity: union-with-Markov-tail at depth r ≡ the
  quotient moment bound `(m·μ_{2r})^{1/2r}`; with `i031_chaining_cosmetic` the entropy
  reduction is cosmetic at BOTH recognized inputs — I031 fully closed;
  `deltastar-466-i031-tail-cosmetic-2026-07-01.md`).

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

### §6 addendum — 2026-07-10 evening (#506 refresh; landings after `fe7d48c6c`)

All items below are axiom-clean and in-tree on `research/proximity-prize`; none closes CORE.
The production δ* conjecture remains **open**.

- **Line-list lane (item 2) — within-Johnson side DISCHARGED.**
  `Frontier/_S2PuncturedJohnsonDischarge.lean` (commit `981b38e62`) proves
  `puncturedListBudget_of_johnson`: the `hlow`/low-profile obligation holds unconditionally
  whenever the punctured parameters sit inside the squared Johnson region (essentially
  `(a−s)² ≳ z(k−1)` up to `1/q` terms). The window probe
  `scripts/probes/probe_s2_punctured_johnson_window.py` (commit `dcf7ca728`, kb
  `deltastar-466-s2-johnson-window-probe-2026-07-10.md`) quantifies the discharged region at
  prize shapes: the surviving open region is a single beyond-Johnson `z`-band per line
  family. The open part of this lane is therefore pinned to exactly beyond-Johnson
  (Johnson-equivalent-hard per the hlow map); do not re-attack the within-Johnson side.
- **CORE lane — G75→G78→G81 localization; the open rung window is now FINITE in depth.**
  Shallow rungs were already sealed (r=2 unconditional via the Stepanov weld, §29/§41);
  `Frontier/_G81DeepRungDCRecovery.lean` (commit `2ee6e69f7`) seals the deep end
  unconditionally: `DCEnergyBound G r` holds outright once `(2r−1)!! ≥ |G|^r` (the crude
  ceiling `E_r ≤ |G|^{2r}` sits inside the Wick budget). Honest scope: prize depth
  `r ≈ log p ≪ n` remains far inside the still-open middle window — no prize contact.
  Along the way: G77+G78 (commits `e78e41383`, `1c7b20205`, `dc39c89e3`) close the signed
  `relationAnomaly` route as a Fourier gauge, and prove the #505 single-embedding qualifier
  has zero slack (`_G78WeightedRelationEmbeddingRigidity.lean`: the weighted signed
  structure is invariant under every primitive embedding `g ↦ g^a`, gcd(a,n)=1); the
  Kelley–Meka spread walk is loss-class-compatible but rank-one circular
  (`_G78KMSpreadCircularity.lean`). Synthesis:
  `deltastar-466-tool-shape-doctrine-v2-2026-07-10.md` (the single missing certificate is
  NON-Fourier anti-concentration) and workbench §5.9 doctrine addendum (commit `a87271b8b`).
- **Factorial padding repair arc (G79S/G80R → G81C → G83M/G84S/G84A/G85/G86).**
  `_G80RPrimitivePaddingEnvelopeRefuted.lean` (commit `c2cf969b2`) refutes the naive padding
  envelope exactly; the corrected reconstruction code and its exact cardinality
  `|Core|·(r desc s)²·(r−s)!·|A|^(r−s)` land in `_G81CRelativePaddingOrderCeiling.lean`,
  with saddle localization `_G79SPrimitivePaddingSaddleLocalization.lean` (landed in commit
  `b849784ce`) and the decoder chain completed through slot partition and endpoint
  assembly (`_G84SCorePaddingSlotPartition.lean`, `_G84AEndpointAssembly.lean`,
  `_G85EndpointAssemblyEquiv.lean` commits `cfa506a38`/`65893d439`,
  `_G86CoreOccurrenceEmbedding.lean` commit `03e7e895a`).
- **G80 arc-model arc.** `_G80SignedL1CertificatePinnedToWall.lean` (commit `4fc4db2e6`):
  the signed ℓ¹ certificate is pinned to the wall M (r-uniform, last-door closure).
  `_G80ArcOscillationWeld.lean` (commit `227597af5`) pays G78's owed arc model;
  `_G80ZArcArithmeticInstantiation.lean` (commit `f8323ecb4`) instantiates it end-to-end on
  `ZMod p`; converse direction `_G80YArcEquivalenceConverse.lean` (commit `486790cb6`);
  decoupling parallel-cap collapse `_G80DDecouplingParallelCapCollapse.lean` (`84aa3e0fc`).
- **G82/#507 production gate — CONDITIONAL pin, one hypothesis deep.** Audit note
  `deltastar-466-g82-production-gate-audit-2026-07-10.md` (commit `203395261`): the
  end-to-end gate already exists in `Frontier/_PrizeShapeRateHalfBracket.lean` —
  `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` gives
  `mcaDeltaStar = 31/64` EXACTLY at production parameters (n = 2^30, rate 1/2,
  ε* = 2^-128) from ONE open hypothesis (the n-scalar bad-count cap at radius
  `31/64 − 2^-30`), with the unconditional bracket `178956971/2^30 ≤ δ* ≤ 31/64` around it.
  This is a conditional reduction, NOT a closure. G82 also lands the depth-two/three
  core-universe absorption + CRT transversality threshold
  (`_G82DepthTwoEnergySaddleBridge.lean`, `_G82TransversalityCRTThreshold.lean`, commits
  `74d694d8e`/`fc5989b0c`/`e80dabc8f`/`59b59f5d9`/`2cdde513a`/`cdca83b80`), and G83 the
  determinant coverage fence + free-orbit energy bridge
  (`_G83DeterminantCoverageFence.lean`, `_G83FreeOrbitEnergyBridge.lean`, commit
  `a0b363326`; maximal common cancellation `_G83MMaximalCommonCancellation.lean`).
- **Lane B2 re-pointed.** Literature sweep 2026-07-10 (commits `ddeed917f`/`9936ff7bb`, kb
  `deltastar-466-litsweep-2026-07-10.md`): analytic core unchanged; B2 curve-decodability
  now pointed at the GGSW 2607.08516 row-span LCL formulation; JLR withdrawal flagged.
- **OC tail ceilings.** Cross-prime stacking-census tail ceiling (commit `82637b6dd`) and
  cross-scale super-additivity no-go (commit `a7c580b97`).

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
  localized to low-t fibers. The prize-facing weld `LineListMCAWeld` is re-landed; remaining
  obligations are the low-profile/list-budget inputs.
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

## 15. Round log — Round 2 (#466, 2026-07-01): the refute pass + the seven spun threads

7 lanes + skeptics (two skeptics lost to a rate limit; their lanes re-verified by the
orchestrator: compile ✅, anchors independently reproduced by two other lanes' verifiers).
Concurrently, a second session ran a round-2B (floorbad64, h-low map, P5 referee, CMK
depth gate) — merged here. DISPROOF tags `466-r2-*`.

**(A) CMK is REFUTED — and the essay's one new closure shape dies.** The lone-spike
countermodel (certified brackets, q = 2^40…2^120): the abstract equal-atom moment problem's
sharp answer IS the raw moment bound, `C(K) = 2K(1+o(1))`; positivity + equal masses + full
moment sequences add nothing; the essay's Hermite–Christoffel constant was a computational
error; **CMK ∘ TPS dies** (the spike realizes the slack). Standing filter: any future
"positivity upgrades a lossy moment input" proposal must first beat this countermodel.
Companion gate `_R2B_CMKDepthIrreducibility.lean` (depth cannot be traded for slack).

**(B) SST is structurally clarified — no new leverage.** Orbit-constancy is PROVABLE (shift =
unit multiple ⟹ isometry): the dilation-on-supports compression is exact factor-n bookkeeping
(the SST analogue of the I031 cosmetic collapse); the essay's bare statement is FALSE at 2-power
n without the antipodal `3^k−1` correction (dyadic Lam–Leung); measured genuine char-p defect =
**identically 0** across all sections at n=16 (exhaustive, r=2,3) and n=32 (full r=2 census) —
zero events, consistent with fixed-depth cleanliness. Surviving residue (named, open): the
multiplier action `S → kS` (not an isometry) cross-orbit correlation.

**(C) The n^{8/9} discovery is FORMALIZED** — `_BilinearDFTBeat.lean` (18 declarations,
axiom-clean): the bilinear (3,3) + √p-DFT chain survives a second full adversarial re-derivation
(exhaustive b-scan verification at p=4129; the splice direction, Parseval completion with no DC
leak, and T3-squared bookkeeping all check); exponent law `θ(β) = (12+β)/18`, saving `(6−β)/18`,
dominates the landed 23/24 for β < 17/3. Named hypotheses `Leg1PopularSumset` /
`Leg2DFTFinisher`; good-prime-conditional; `isPrizeClosure := false`;
`deltaStar_determination_all_or_nothing` keeps it honest (a fixed power saving cannot move δ\*).

**(D) The Jacobi ramp law is EXACT and formalized** — `_JacobiRampDefectLaw.lean` (6 theorems):
j=1 unconditional (`1−q₁ = (n−1)/(p−1) + n/(p−1)²` — the measured law is exactly the variance),
j=2 conditional on clean `E₂`/`T₃` with the structural payoff: the j=1 defect reads p only,
while j=2 carries an n-only char-0 Bessel floor `3/(2n)`. Ensemble MEAN only; instance turnover
and j≥3 (where the char-p defect enters) stay open.

**(E) First-interior brick landed; the discriminating depth at n=16 is k+3, not k+2.**
`FirstInteriorLevelDirectionBlind.lean` (axiom-clean): a = k+1 is direction-blind with ceiling
`C(n,k+1)` (thin corollary of `KKH26CeilingMarch.scalar_eq_of_shared_tuple`). n=16 completed
runs: a=6 (depth 2) is an exact p-INDEPENDENT tie at 89 across all three primes; a=7 (depth 3)
is where spread wins. **The P5 referee audit (466b) STRENGTHENED the refutation: spread worst
≥ 21 vs monomial 9 (ratio ≥ 2.33)** — so the bounded spread-excess law at C=2 is already dead;
**C=3 is the live constant** (`_SpreadExcessLaw.lean` carries the parameterized Prop + refuter
record). Depth-separation appears driven by near-degenerate directions (self-agreement a−1).

**(F) The 2-adic/Fermat family is an ARTIFACT — the real mechanism is generalized-Fermat.**
v₂-saturation exonerated (2/34 vs 0/34 controls; C-ratio 1.0145); the true resonant family is
`p = b^(2^s)+1` with `μ_n = ±⟨B⟩` a geometric progression: **η₁ = n − c_B exactly** (7/7
verified; c₂ = 6.789). Only B=2 beats the C plateau (≈1.70 asymptotic; ONE in-window witness at
β=3.2), and the B=2 supply ENDS at F₄ = 65537 (F₅ composite). Deployment avoid-list narrowed to
generalized-Fermat B ≤ 4; BabyBear-class exonerated. Ceiling-side tool; touches no floor.

**(G) D4 scanner: the depth-4 face mirrors D3.** Anchor `W₄(65537, n=16) = +4480` reproduced
exactly (by three independent implementations across lanes); NEW unconditional fact: `D4(n)` is
FINITE for every n (norm-height `8^{n/2}`), and the n=8 window is PROVABLY D4-clean
(`8^4 = n^4`); n=16: threshold-bad empty, exactly-bad ≈ {65537}; n=32 exhaustive scan (18,452
primes) confirms the pattern (see `_out_466_d4_scanner.txt` for the exact set). The
D4-conditional `n^{7/8}` has plausible good-prime supply, but the in-tree counting comparator
is vacuous at depth 4 — formal closure needs a structure theorem for depth-4 norm divisors.

**(H) Round-2B (concurrent session):** floor-bad(32) = {97} re-verified through p = 1217 with
the NEW exact count (32 realizable patterns = ONE translation orbit); **floor-bad(64) is
UNDECIDED at feasible compute** (pattern space 2.2·10¹⁵ ≈ 10⁷ CPU-hours) — Tier-1 item 4 is now
formally in the "numerics cannot decide" regime and needs the successor THEOREM
(`CandidateListExactSuccessor`) or nothing; the h-low map + `_R2B_LargeZeroWitnessSplit.lean`
advance the weld's near-branch; the referee vacuity theorem
(`not_uniform_lineListBudgeted_of_lt_card` consumer shape) landed.

**Survivor list after round 2 (the §6 re-rank):** ① line-list low-profile obligations
(`_LowProfileFiberBound` + `LargeZeroWitnessSplit` narrow them; the weld consumer is real) —
now clearly the primary open surface; ② the **bounded spread-excess law at C=3**
(`_SpreadExcessLaw.SpreadExcessLaw`, parameterized, refutable — the replacement for the dead
windowed SumsetExtremal); ③ uniform-in-μ floor-bad = the successor-theorem-or-nothing regime;
④ the SST multiplier-action residue; ⑤ the D4 structure theorem (payoff 7/8); ⑥ ramp law j=3
(first mean-ramp p-vs-n crossover); ⑦ the GF-ceiling brick (elementary, bankable). Dead this
round: CMK, CMK∘TPS, 2-adic-family, naive SST. **CORE unchanged: OPEN, ON-BGK.**

## 16. Round log — Rounds 4–6 (#466, 2026-07-01/02): the open-angle sweep, the deployment certificates, and the novel-mathematics round

Multi-agent workflows (Fable + Opus, ~90 agents), each verdict double-refereed. DISPROOF tags
`466-r4-*`/`466-r5-*`/`466-r6-*`.

**(A) Every remaining Tier-2/Tier-3 avenue DECIDED.** D2 Rogers–Siegel lower tail = **CONCENTRATION**
(`_D2LowerTailConcentrationGate.lean`; x ∈ [1.10,1.22]/[1.13,1.39] over ALL window primes at
n=16/32, strictly tighter than iid Gumbel; no anomaly class — the ∃-form lever is dead). Tsang
level-splitting = nothing to split (all excess is level-0/archimedean; generic wraparound
identically zero to r≤6/4). I031 tail = cosmetic (union-over-cosets ≡ the quotient moment bound
exactly, 9e-16 — the entropy reduction cancels at BOTH inputs; I031 fully closed). Mixed-topfit =
UNSAT at every prize shape (`MixedTopFitBudgetIncompatibility.lean`, 420/420, refereed — the
low-profile split is MANDATORY). Second-witness/multiplicity floor = REFUTED (`_SecondWitnessFloor.lean`
— extremal far lines force ALL bad scalars to be unique-witness singletons). Function-field model =
null (Carlitz analogue ~ random subspaces; Weil vacuous at q=2 the same way — F_q[t] is 0-dimensional too).

**(B) Deployment certificates — the wall at PRODUCTION scale.** BabyBear (`p = 15·2^27+1`, n=2²⁷,
f=15): exact-integer period-matrix certificate gives **M/√(n log(p/n)) = 1.304**, INSIDE the
measured [1.07,1.49] band, two octaves beyond all prior data (n≤1024); Parseval anchor
|S₂/(p−n)−1| = 2e-16. No-divergence confirmed at 2²⁷. (`deltastar-466-deployment-certificates.md`.)

**(C) D4 depth-4 face DIVERGES from D3** (exhaustive n=32, 13,319 primes; anchor W₄(65537,16)=+4480
reproduced): n=8 provably D4-clean (norm-height 8⁴=n⁴), n=16 0 K-bad, **n=32 92 K-bad in-window**
(max W₄/K-margin ratio 2.14). The bilinear n^{7/8} route's T4=O(n⁴) good-prime supply is NOT free
at n=32 — it needs a genuine depth-4 divisor structure theorem excluding the structured K-bad set;
the n^{8/9} (T3) route is unaffected. New exact value E₄⁰(32)=90,889,120.

**(D) The coset-SET language FOUND** (`deltastar-466-w8-*`): coarse arc-concentration functionals
(quarter-arc discrepancy, L2 arc energy) predict |η_b| and near-extremize at the worst coset —
the correct vocabulary for any future dichotomy, upgrading the round-1 residue-blindness kill from
"residues of b don't classify" to "coset-SET arc concentration does."

**(E) The novel-mathematics round — SEVEN out-of-distribution complete-proof attempts, all
developed to exact deaths, each a new standing filter.** Each proposer wrote a complete chain with
prize-point constants; two orthogonal refuters (arithmetic-vacuity + structural-reduction) and a
judge adjudicated. Verdicts:
- **N1 theta/cusp** (REDUCES_TO_WALL): the wraparound-lattice θ = Eisenstein + cusp, but the
  Eisenstein slot provably holds the VOLUME term (off by 10^{3·10⁹}), the Wick term is a
  weight-n/4 theta invisible to the weight-n/2 main-term slot, and the cusp Deligne transfer costs
  (2r)^{n/4} = the norm-height wall in automorphic clothing. FILTER: any weight-n/2 automorphic
  main-term proposal misfiles the Wick term.
- **N2 Weil-representation** (exact dictionary; the thin orbit stays an incomplete sum),
  **N3 homogeneous dynamics** (three sub-routes die on exact arithmetic — the Hecke union tax
  beats the τ-spectral gap; no dynamics in S at fixed p),
  **N5 SoS duality** (SELF-REFUTATION-WITH-STRUCTURE: the lone-spike measure IS a valid
  pseudo-distribution ⟹ the wall is an SoS lower bound; enumerates which techniques remain
  SoS-unrepresentable — dyadic induction, integrality, entropy compression),
  **N6 Shmerkin/Hochman entropy flattening** (triple relocation onto the wall).
- **N4 Lee–Yang / period-polynomial roots** (REDUCES_TO_WALL, dies TWICE): M = house of the Gauss
  period polynomial P_m; the Fujiwara max-form root bound binds at k=2 → √(2p) (worse than
  Johnson), and shallow-weighted real-rootedness tests are blind to the lone spike (the
  root-location twin of the CMK moment death).
- **N7 free-synthesis / Gauss-sum-phase dual** (REDUCES_TO_WALL, unitarily): the dual η ↔ g map is
  a unitary DFT and |g(χ)| = √p is flat, so M is a functional purely of the phases arg g(χ); the
  one new lever — Stickelberger/Gross–Koblitz p-adic data — is ARCHIMEDEAN-BLIND; the required
  argument-equidistribution is unitarily equivalent to the prize. FILTER: any p-adic/Stickelberger/
  Gross–Koblitz/Jacobi-sum/Iwasawa-only lever is phase-blind and cannot bound the house.

**Net (rounds 4–6):** ~20 axiom-clean bricks + ~18 DISPROOF entries; every Tier-2/Tier-3 avenue and
every OOD complete-proof route is now decided with a countermodel, exact identity, or standing
filter. **CORE unchanged: OPEN, ON-BGK.**

## 17. Round log — Round 7 (#466, 2026-07-02, Opus): the line-list weld CLOSURE ROUTE is closed

11 Opus lanes, double-refereed. DISPROOF tags `466-r7-*`.

**⛔ THE HEADLINE: the pure-coding-theory closure route is EXHAUSTED.** The line-list weld
(`mcaDeltaStar_ge_of_farLineListBudgeted`) reduces the δ\* floor to a far-line list budget; the
budget was to be certified through the fiber-counting stack. Its three successive sub-obligations
are now ALL refuted: mixed-topfit (`466-r2`, UNSAT at every prize shape), second-witness floor
(`466-r4`, all-singleton), and now — the last hope — the **z-COUPLED low-profile sum**
(`466-r7-lowprofile-coupled-carries-q`, `_LowProfileFiberCoupled.lean` axiom-clean countermodel):
it carries a q-power because `choose(z,t)` explodes (coup/true ratio 715× at n=16) **at the t≥k
MDS strata where D=1 is already proven** — so no low-profile fiber theorem can rescue it;
`choose(z,t)` is the killer, not `D(t)`. **Consequence:** the weld stays a valid *reduction*, but
the budget provably cannot be certified through the counting stack — the route that avoided the
analytic wall is closed, pushing everything back onto BGK/Paley.

**The surviving open surface, re-ranked after round 7:**
- **The floor successor as an ARITHMETIC theorem** (`466-r7-floor-successor-is-a-norm`, the round's
  most promising residue): the combinatorial 16→32 lift is REFUTED (orbit count 10→1), but the
  smallest-prime mechanism is DISCOVERED — **bad prime ⟺ p | Norm(β)**, β the fixed obstruction
  algebraic integer, Norm the cyclotomic resultant (char-0, p-independent). The floor successor is
  a resultant-divisibility question — the same 0-dimensional height object as the width-four/D3
  lane — not a pattern map. This *terminates at a theorem*, not the wall.
- **The D4 depth-4 divisor structure theorem** (from §16 C: n=32 has 92 in-window K-bad primes) —
  needed for the n^{7/8} bilinear route; the n^{8/9} route is unaffected.
- **The coset-SET arc-concentration language** (§16 D) — the correct vocabulary, no bound yet.
- **The analytic wall itself** — the DC-subtracted char-p Wick bound at depth r ≈ ln q.

**Also landed (all axiom-clean):** `_JacobiRampDefectLawJ3.lean` (j=3 ramp law — the char-0 floor
`F_3 = (18n−31)/(3n(2n−3)) ≈ 3/n` is DOUBLE the j=2 floor `3/(2n)`: the char-0 floor GROWS with
depth; + the `j*(n,p)` crossover characterization, the first quantitative statement of WHERE the
char-p defect enters the Jacobi window); `_SSTMultiplierAntipode.lean` (SST fully closed — the
multiplier action S→kS is a Galois twist `L_{kS}(h)=L_S(h^k)`, shares sparse-count but NOT the
transference quantity λ₁*); `_SpreadExcessLaw.lean` (the spread "excess" is an
elevated-self-agreement `agreemax=a−1` artifact, not spreadness — monomial baseline robustly 9,
spread 21 at n=16 a=7); `_GFCeilingInstance65537.lean` (|η₁| > 2√n at F₄, out-of-window β=3.2 —
docstring corrected to make NO in-window claim; re-confirms the round-2 GF mechanism); three
Mathlib-API-drift repairs.

**#313 Binius closeout:** math residuals done (4/4), but the cone is BUILD-RED — blocked on a
substrate `iteratedQuotientMap` API migration landed after the audit (all errors are index/API
drift, zero `sorry`). Kept OPEN with the honest status; per-site fix list in
`docs/kb/binius-313-closeout-2026-07-02.md`.

**CORE unchanged: OPEN, ON-BGK. The campaign has now closed every route that terminates anywhere
BUT the wall — except the floor-successor-as-norm, which terminates at a cyclotomic-resultant
divisibility (a genuine, non-wall theorem target).**

## 18. Round log — Round 8 (#466, 2026-07-02, Opus): the floor-successor sharpened; the D4 n^{7/8} route killed

3 lanes, double-refereed (all verifiers severity none). DISPROOF tags `466-r8-*`.

**(A) The floor-successor-as-norm is SHARPENED to a precise uniform conjecture — its shortcut
refuted.** The round-7 mechanism is verified exactly (independent Z[ζ_n] Bareiss recomputation):
floor-bad ⟺ `p | N(A) = Res(V_A, Φ_n)` (char-0, p-independent). n=16: N=2312=2³·17²; n=32: the
three orbit-rep norms have unique ≡1-mod-n factor = p_min(n) (17, 97). Germ landed axiom-clean
(`_FloorSuccessorNorm.lean`: `floorObstructionNorm_forces_pmin_{16,32}` — p prime ∧ p%n=1 ∧ p|R_n
→ p=p_min). **The "one canonical resultant resolves floor-bad(64)" shortcut is REFUTED** — the norm
is genuinely pattern-dependent; at n=64 the ≡1-mod-64 factor sets of the seven canonical
obstruction norms have EMPTY intersection, so no single char-0 resultant collapses the 2.2×10¹⁵
search and floor-bad(64) stays compute-hard. **The surviving non-wall target, now precise: the
uniform conjecture "unique ≡1-mod-n prime factor of R_n = p_min(n)" (verified n=16, 32).**

**(B) The D4 depth-4 n^{7/8} route is DEAD (decisive negative).** Census of all 92 in-window K-bad
primes at n=32 (exhaustive): they are ARITHMETICALLY GENERIC — 0 generalized-Fermat, 0 high-v₂,
47/92 at the minimal v₂=5 with a single-large-prime cofactor, spanning the whole window to
β=4.394. Countermodel: p=1391393=2⁵·43481 (43481 prime — the most generic form for p≡1 mod 32, yet
K-bad). No divisor structure theorem exists at depth 4, so the bilinear n^{7/8} route's T4=O(n⁴)
good-prime supply fails on positive-density generic K-badness. `_D4NormHeightFinite.lean` records
the unconditional finiteness (the `8^{n/2}` norm-height cutoff). **The n^{8/9} (T3) route is
UNAFFECTED** — it remains the best good-prime-conditional SOTA-closeness. (DISPROOF
`466-r8-d4-kbad-generic-no-structure-theorem`.)

**(C) B2 curve-decodability:** `_B2ExplainingCurveList.lean` axiom-clean and landed (a real bug
fixed); the structured/weld pair is code-complete, blocked only on the GG25 dependency build.

**THE STATE after 8 rounds.** Every Tier-1/2/3 avenue, all seven OOD complete-proof chains, and the
entire line-list closure route are decided. Two surviving open surfaces: (1) the uniform
floor-successor resultant conjecture (a *non-wall* target); (2) the analytic BGK/Paley wall.

## 19. Round log — Round 9 (#466, 2026-07-03, Opus): the LAST non-wall target refuted; the campaign converges to ONE open surface

6 lanes (4 floor-successor + 2 wall), double-refereed. DISPROOF `466-fs1/fs2/w1/w2-*`. This round
attacked both surviving targets directly and closed the first outright.

**⛔ (A) THE UNIFORM FLOOR-SUCCESSOR CONJECTURE IS FALSE (FS1, the decisive result).** The
conjecture floor-bad(n) = {p_min(n)} — true at n=16 ({17}) and n=32 ({97}) — is **REFUTED at
n=64: floor-bad(64) does NOT contain p_min = 193.** A COMPLETE scan of the entire adjacent-7th-type
pattern family (the whole ≈2.2×10¹⁵ family up to the exact Z/16 translation symmetry; 2012s/11
cores) found ZERO realizable patterns at p=193. The least-prime law is an n=16/32 **coincidence,
not a theorem**; the off-BGK floor route via a uniform successor law is CLOSED. This was enabled by
a NEW axiom-clean theorem — `_FloorComplementReform.lean` (real lake build): a pattern is
floor-realizable at p IFF its complement polynomial `Q_B` has vanishing coefficients at the middle
degrees `[n/8+1, n/4−1]`, which turns the scanner's degree-`5n/8` remainder test into a 7-coefficient
condition and enables a meet-in-the-middle that replaces the raw scan. **Completeness is PROVABLE**
(the Z/16 rotation-canonicalization is exhaustive, verified two ways + positive/negative controls +
an independent RREF algorithm agreeing on 0 — verifier severity none). floor-bad(64) over the full
window [193, 64⁴] is left open, but if nonempty it is NOT governed by a uniform law. (This does not
change §16 A: the off-BGK floor was already necessary-not-sufficient — δ\*-pin ⟹ floor-good, never
conversely.)

**(B) The floor-successor program, fully mapped.** FS2 (refuted, `_FloorPackingDensityRefuted.lean`):
the packing/density germ is dead — floor-badness is a sharp resultant-divisibility coincidence, not
metric density (min-gap = 1 at both floor-bad and floor-good primes; density inversion
`512/7681 < 256/769`). FS3 (partial): the resultant HEIGHT `2^{O(n log n)}` provably cannot force
the common factor = p_min — the conjecture is irreducible to a height bound; but
`_FloorSuccessorTZBridge.lean` (axiom-clean) wires the confirmed TZ 12/5 result to the floor closure
so the entire off-BGK floor rests on ONE named conjecture (now known to fail the clean form at n=64).
FS4 (partial, `_FloorSuccessorResultantBridge.lean`, axiom-clean): the realizability ⟹
resultant-divisibility bridge is machine-checked (reusing the width-four `CyclotomicResultantBound`
machinery).

**(C) The wall, sharpened to its cleanest form.** W1 (decided, `_WallBetaPlusOneLocalization.lean`,
axiom-clean, non-circular): the first unproven rung r = β+1 is ALREADY the wall. The exact split
`E_r^(p) = E_∞ + W_r` and `A_r ≤ Wick ⟺ WraparoundBelowDC := (W_r ≤ n^{2r}/p)`; the signed-cancellation
idea is REFUTED (`W_r` is a nonnegative count — nothing to cancel; the observed negative excess IS
the unsigned inequality whose proof is the wall). **The wall is now pinned to an exact scalar**: at
the prize (n=2³⁰, β=4, r=5) it demands `W_r` match its DC mean to relative precision `2^{−47}` — a
genuine √-cancellation statement, the sharpest possible localization of the open core. W2 (decided,
`_WallNewEnergyExhaustion.lean`, 19 decls): the exact-μ_n-energy exponent axis is EXHAUSTED — no beat
past `n^{8/9}` good-prime or `n^{1−o(1)}` unconditional (multiplicative energy `n³` enters only via
sum-product to the additive; T₄/T₆ reduce to the swept trilinear; the character 2nd moment is the
Parseval √n floor).

**═══ THE FINAL STATE after 9 rounds ═══**
**The surviving open surface is EXACTLY ONE object: the analytic BGK/Paley wall** — now reduced to
its cleanest form, the exact √-cancellation `W_r ≤ n^{2r}/p` of the wraparound below its DC mean at
r = β+1 (equivalently the DC-subtracted char-p Wick bound `A_r ≤ K^r(2r−1)‼·n^r` at depth
`r ≈ ln q`), the recognized ≈25-year-open thin-2-power square-root-cancellation problem. **Every
other route** — every Tier-1/2/3 lever, all seven OOD complete-proof chains, the entire line-list
closure route, and the floor-successor — **is decided, each with a countermodel, exact identity, or
standing filter.** The prize is a single, precisely-stated open inequality with a completely mapped
no-go landscape. **CORE OPEN, ON-BGK. No fabricated closure.**

<sub>🤖 Consolidated 2026-07-01 by Claude (Fable 5) from the full #464 record (dossier v2 + 179
comments, three independent digests), the in-tree substrate, the recovered #444 workstation branch,
and independent re-verification. No fabricated closure; the core is carried as a named open
`Prop`.</sub>

---

## 20. Round log — Round 10 (#466, 2026-07-04, Fable): two genuinely-new wall angles + a fresh literature sweep — all confirm the surface is exactly one object

Plan: `deltastar-466-research-plan-round10-2026-07-04.md`. Essay:
`deltastar-466-essay-round10-2026-07-04.md`. 3 lanes + 3 adversarial skeptics (7 agents), all verdicts
CONFIRMED (severity minor). DISPROOF tags `466-r10-*`. This round attacked the LAST surface (the wall
`W_r ≤ n^{2r}/p` at `r = β+1`) from two machineries checked absent from the 18k-line dead ledger, plus a
2024–2026 sweep. **All three confirm: the wall stands, one object.**

**(A) Automatic-sequence / substitutive Fourier analysis — REFUTED, but with a NEW observation.** The
dyadic-root phase sequence `k ↦ e_p(b·ζ^k)` (2-adic digits of `k ∈ Z/2^μ`; Allouche–Shallit /
Byszewski–Konieczny–Müllner Gowers-norm machinery). **New, previously-unrecorded fact:** the wraparound
solution set IS genuinely 2-adic-digit **structured** (pairwise-valuation `v₂(kᵢ−kⱼ)` deviates from the
digit-uniform null with χ²/dof in the hundreds–thousands; single-exponent popcount *exactly* uniform ⟹
structure is JOINT not marginal) and is **not dilation-closed** (only `u=1` fixes the wrap set) — so it
is NOT b-blind in the naive C1 sense. It dies three machine-checked ways anyway: (i) **count-neutral /
b-summed** — the wrap set is the equal-sum locus, on which the character weight `χ_b(0)=1` for every `b`,
so the structure is a property of the b-summed moment `E_r` and `W_r` already sits at/below its
digit-uniform DC mean (`W_r/DC ∈ [0.13, 0.98]`), no total to save; (ii) **sign-unstable in p** (the
deviation flips direction across primes, no fixed Gowers bias); (iii) **no μ-uniform automaton** (the
2-kernel base `ζ^{2^i}` has multiplicative order `n/2^i` shrinking to 1, so automatic-sequence
asymptotics do not apply — reconfirms [wf-NC/NC1]). Brick `_LaneAAutomaticBBlind.lean` (axiom-clean:
`char_weight_trivial_on_solset`, `solset_count_is_b_summed`). Probe `probe_466r10_automatic.py` (exact
enumeration, tuple-validated; skeptic re-derived every number via a disjoint char-0 convention).

**(B) Transfer-operator / dynamical-zeta spectral gap — REFUTED as GAUGE.** The doubling-map `x↦x²`
transfer operator on the dyadic tower, designed to beat the refuted naive √2-descent via a spectral gap.
Every operator invariant factors through the coset-invariant magnitude multiset `{‖η_b‖}`, whose
invariants are its power sums = the raw energy/moment ladder — so the spectrum is a reparameterization of
the moments (the `todaTurnover_not_determined_by_invariants` gauge shape), and its leading eigenvalue is a
bounded transient → the √2 mean-field rate forced by `M ~ √(n log m)` at fixed `log m` (regime-mute,
cannot separate prize-true from BGK-tight). Gauge test passed (same low moments ⟹ same spectrum). Brick
`_B_TransferOperatorGauge.lean` (4 axiom-clean thms). KB `deltastar-466-r10-laneB-*`.

**(C) Literature 2024–2026 — CLEAR (zero survivors).** Every genuinely-new √-cancellation result lives on
a structure the prize object lacks (Burgess intervals, function fields `F_q[t]`, the `p^{1/3}` energy
floor, non-abelian Bourgain–Gamburd); the closest hit (Kunisky) is index-2 and conjectural. The
BGK-only-survivor foreclosure ledger is unbroken through 2026-07. KB `deltastar-466-r10-laneC-*`.

**═══ STATE after 10 rounds ═══** Unchanged and reconfirmed from a new direction: **the surviving open
surface is EXACTLY ONE object, the wall `W_r ≤ n^{2r}/p` at `r = β+1`.** Both new machineries collapse to
the *same* cause the Meta-Theorem names (b-summed / gauge second-order data). **The one honest Round-11
candidate** is a genuine sub-question of the wall, not a new route: `JointPhaseFieldStructure` — does the
**joint** `(η_b, η_{ζb})` phase field carry b-sensitive information at deep `r` that is invisible to every
marginal-magnitude / moment functional? Round-10 lanes found the adjacent-coset joint *marginal-determined
at r=2*; a round is warranted only if a deep-`r` joint statistic can be exhibited that is (a) not a
function of the moment ladder and (b) b-sensitive. If it too collapses, that is another clean refutation —
the expected outcome for this wall. **CORE OPEN, ON-BGK. No fabricated closure.**

---

## 21. Round log — Round 11 (#466, 2026-07-04, Fable): the last sub-thread closed; the no-go cartography is COMPLETE

Plan: attack the ONE sub-thread round 10 declined to foreclose (`JointPhaseFieldStructure`) + a
completeness scout stress-testing the Tetrachotomy. Essay: `deltastar-466-essay-round11-2026-07-04.md`.
2 lanes + 2 adversarial skeptics (5 agents), both verdicts CONFIRMED (severity minor). DISPROOF `466-r11-*`.

**(A) JointPhaseFieldStructure — REFUTED, COLLAPSES at ALL depths (the last sub-thread closed).** The joint
two-frequency tower field `(η_b, η_{ζb})` — the two tower half-periods `A_b = η_b(μ_{n/2})`,
`B_b = η_{ζb}(μ_{n/2})`, `A_b + B_b = η_b(μ_n)` — is **exactly collinear** for every coset
(`max_b |sin(arg B_b − arg A_b)| < 3·10⁻¹¹`, n=8/16/32, ≥2 primes, full coset scan), because the index sets
are negation-closed for `4|n` (periods real up to a global phase — the logged `eta_real_of_neg_closed` /
[door-iv-common-ray-coherence] fact, here upgraded from the worst `b*` to ALL `b` and from `r=2` to ALL `r`).
Collinearity ⟹ the joint is 1-real-dimensional per coset; its only phase content is a sign bit
`s_b = (|η_b|²−|A_b|²−|B_b|²)/(2|A_b||B_b|)` **algebraic in the three magnitudes** (0 mismatches over
500–33 000 cosets/prime), so the joint reconstructs from `(|η_b|,|A_b|,|B_b|)` and every joint moment is a
symmetric function of the magnitude multiset = the moment ladder (**gauge**). The apparent "joint-vs-marginal
gap grows with r" is the trivial `||a|±|b|| vs √(a²+b²)` magnitude arithmetic with `s` fixed algebraically —
zero residual phase at any depth. This upgrades `[doorIV-joint-field-white]` from `r=2` to all `r`: per coset
the problem is 1-real-dimensional, so no depth admits a second-order-transcendent phase invariant. Brick
`_JointPhaseCollinearGauge.lean` (5 axiom-clean thms; real build 3311 jobs). Skeptic re-ran the probe
(0/33 000 mismatches), pg-iterated the brick, and independently confirmed `A_b` real to `1e-15` — a robust
rediscovery of a logged reality fact, not a delicate signal.

**(B) Completeness scout — the TETRACHOTOMY HOLDS (no fifth door).** Systematic stress-test of the "no fifth
door" claim across model-theoretic/o-minimal, condensed/perfectoid/prismatic/p-adic-Hodge, motivic/
determinantal, operator-algebraic/free-probability, random-matrix-universality-beyond-moments,
information-theoretic. Zero survivors — the campaign had already run a T01–T25 sweep (24 escape-theorems in 5
clusters) + 84 prior escapes, all dead. **Unifying category obstruction** (the deep reason): every p-adic /
cohomological / model-theoretic / spectral-invariant functor lands in a target with NO archimedean place (or
a signed/mean-zero object), whereas `W_r` is an **unsigned archimedean modulus** — so each candidate
sign-reverses, rank-collapses to the rank-`n` second moment, or needs an even moment, landing back in doors
(i)/(iii)/(iv). The naive third-order avatar `T3 = η_b²·conj(η_{ζb})` collapses even more cleanly:
`|T3| = |η_b|²·|η_{ζb}|` identically (magnitude = marginal product), only a mean-zero sign that cancels under
the coset sum.

**═══ THE CARTOGRAPHY IS COMPLETE (state after 11 rounds) ═══** With `JointPhaseFieldStructure` closed on
both its magnitude and phase faces, **no live sub-thread remains.** The surviving open surface is still
EXACTLY ONE object — the wall `W_r ≤ n^{2r}/p` at `r = β+1` — now the **sole irreducible open core**, with
every other approach (every Tier-1/2/3 lever, all seven OOD complete-proof chains, the line-list closure
route, the floor-successor, both round-10 machineries, and now the joint-phase sub-thread + the entire
fifth-door class) **decided, each with a countermodel, exact identity, or standing filter.** The final
refutable residue `UnsignedJointInvariant` ("there exists a b-sensitive UNSIGNED joint functional at prize
depth not a function of the `|η_b|`-multiset") is stated as the negation of the last conceivable escape;
round-11 data supports the standing conjecture that no such object exists (a "universal b-summed collapse").
**CORE OPEN, ON-BGK. No fabricated closure.** The campaign's product is a complete, machine-checked
cartography reducing a $1M grand challenge to one precisely-stated ≈25-year-open analytic inequality, with
route-elimination as theorems and every conceivable escape decided.

---

## 22. Round log — Round 12 (#466, 2026-07-04, Fable): the frontal assault ON the wall + the machine-checked CAPSTONE

After 11 rounds the cartography was complete (every escape decided). Round 12 does the two things the
elimination campaign never did: a **frontal attempt ON the wall itself** (not an escape route) and the
**machine-checked capstone** localizing the prize to one named Prop. Essay:
`deltastar-466-essay-round12-2026-07-04.md`. 2 lanes + 2 adversarial skeptics (5 agents); Lane F severity
**none**, Lane K severity minor. DISPROOF `466-r12-*`. Neither closes the wall — honestly.

**(F) Frontal norm/conjugate-count assault — REDUCES-TO-WALL, at an exact-finite step.** `W_r` is exactly the
count of sparse ±1 sums `α = Σεᵢhᵢ` of `2r` n-th roots with `p | N(α)`, `α ≠ 0` (identity: `p` splits
completely, so `α ≡ 0 mod 𝔭` with `α ≠ 0 ⟺ p | N(α)`; probe-validated exact at n=8). The one unconditional
magnitude tool — `|N(α)| ≤ (2r)^{n/2}` (in-tree `abs_norm_sum_rootsOfUnity_le`) — proves `W_r = 0` exactly
where `(2r)^{n/2} < p` (the conjugate gate `no_wraparound_at_depth`). **New landed content**
(`_FrontalConjugateGateCollapse.lean`, 4 axiom-clean thms, real build): at the prize `p = n^4` the gate is
**vacuous** — `gate_vacuous_at_prize` proves `(2r)^{n/2} ≥ p` for every `r ≥ 1` once `n ≥ 64` (since
`n^4 < 2^{n/2}`, even crossover at n=44; dyadic fails at 32, holds at 64), so the sole unconditional tool
certifies `W_r = 0` at NO rung on `[1, β+1]`. This sharpens the prior asymptotic `threshold_lt_saddle` to an
exact finite prize-point boundary. The residual is precisely the un-gated `WraparoundBelowDC` (the wall,
unchanged); a magnitude-only argument cannot enter it because `|N| = ∏|σ|` can exceed `p` with every
`|σ(α)| ≤ 2r` small — bounding the count of large-norm p-divisible sparse sums needs inter-conjugate PHASE
cancellation = BGK. Empirically the wall HOLDS at every measured post-onset rung (`W_r/(n^{2r}/p) ∈
[0.007, 0.615] < 1`, n=8/16/32, ≥2 primes, β=4).

**(K) The machine-checked capstone — CAPSTONE-PARTIAL.** `_WallCapstone.lean` (3 axiom-clean thms; skeptic
independently pg-iterated and verified every cited link is a real in-tree theorem faithfully applied — no
laundering) states the wall as ONE named Prop `WallHolds G := ∀ r, DCEnergyBound G r` (the ∀-r closure of
W1's `WraparoundBelowDC`, the wall verbatim) and proves: `charSum_of_wallHolds` (WallHolds ⟹ the
per-frequency sup-norm bound — the wall's whole analytic payload, DERIVED); `deltaStar_floor_of_charSumBound_of_budget`;
and the composite `wall_capstone` (a conjunction, so WallHolds is genuinely load-bearing). **The prize
localizes to `WallHolds ∧ RealizedIncidenceBudget`**, machine-checked, where `RealizedIncidenceBudget` is ONE
explicitly-named glue (the M→δ* far-coset law + naive incidence budget) that the wall does not supply, is
vacuous at the prize budget for nonzero B, and needs the open `√q·B` cancellation (Paley/BCHKS-1.12) — flagged,
NOT discharged; the moment-order optimization is passed as a parameter.

**═══ CARTOGRAPHY CAPSTONED (state after 12 rounds) ═══** The sole open core is a single named `Prop`
(`WallHolds`); the frontal magnitude route is machine-certified to bottom out exactly on it
(`gate_vacuous_at_prize`); and a compiled certificate (`wall_capstone`) localizes the prize onto it modulo one
honestly-named, prize-vacuous glue that is itself the recognized open `√q·B` cancellation. The wall is **not**
claimed closed — it remains genuine ≈25-year-open analytic number theory (square-root cancellation for thin
2-power subgroups; best proven at β=4 is BGK `n^{1−o(1)}`). **CORE OPEN, ON-BGK. No fabricated closure.**

---

## 23. Round log — Round 13 (#466, 2026-07-04, Fable): the capstone tightened — moment-order parameter removed, and the core is TWO distinct inputs (not one)

Round 12 left `CAPSTONE-PARTIAL` with two soft spots: (a) the moment-order optimization was an un-formalized
parameter, and (b) it was open whether the second conjunct is genuinely distinct from the wall. Round 13 settles
both. Essay: `deltastar-466-essay-round13-2026-07-04.md`. 2 lanes + 2 adversarial skeptics (5 agents); both
lanes independently reached **WORLD-II**, skeptics CONFIRMED (severity minor). DISPROOF `466-r13-*`.

**(M) The moment-order optimization is now AXIOM-CLEAN — caveat (a) discharged.** `_MomentOptimizedSupNorm.lean`
(real build 3320 jobs, 9 axiom-clean thms) proves `WallHolds G ∧ q≥e ⟹ ∀ b≠0, ‖η_b‖ ≤ √(2e·n·(ln q+1))`
directly from the DC-subtracted wall — the new Stirling-free arithmetic `(2r−1)‼ ≤ (2r)^r` (for Mathlib's
`Nat.doubleFactorial`) + the saddle `q^{1/r} ≤ e` at `r=⌈ln q⌉`. `_MomentWallWiringCheck.lean`'s
`wall_capstone_moment_closed` machine-verifies it composes into `wall_capstone`'s `B` slot (the two `WallHolds`
defs are definitionally equal — no glue lemma), so **the wall now supplies its own optimized sup-norm `B`, with
no free parameter.** (The crude Lean constant `√(2e)≈2.33` over-estimates the probe-measured sharp `≈1.43`;
non-load-bearing numeric.)

**(R) The core is TWO distinct open inputs, not one — the crux settled WORLD-II.** The wall's entire analytic
payload is the sup-norm `M = max_b ‖η_b‖` (lane M derives it from `WallHolds`). Round 13 proves `M` is
**necessary but not sufficient**: the machine-checked second-moment identity
`∑_{s₀} ‖I_H(s₀)‖² = q·∑_{b∈H} ‖η_b‖²` (`_R13HyperplaneSecondMoment.lean`, axiom-clean, pure additive-character
orthogonality) shows `M` controls only the **s₀-average** of the signed hyperplane incidence
`I_H(s₀) = ∑_{b∈H} conj(η_b)ψ(b·s₀)` (giving `‖I_H‖ ≤ √|H|·M` on average) — while the far-coset adversary picks
the **worst** `s₀` (which reaches the diagonal Gauss-period `|H|·M`-scale), and a **same-moduli two-spectra
witness** (identical `{‖η_b‖}` hence identical `M`, worst-case incidence differing by `√|H|`; probe, rel-diff
`2e-16` on the identity) proves the worst-case `√q·B` cancellation is **provably not a function of `M`**. So the
prize localizes to **`WallHolds ∧ HyperplaneCancellation`** — two genuinely distinct open Props: (1) `WallHolds`,
the moment/energy (Wick) bound = BGK proper, phase-blind; (2) `HyperplaneCancellation`, the worst-case
per-frequency √q·B cancellation = **BCHKS Conjecture 1.12**, a phase-correlation statement. The first does not
imply the second. This makes rigorous and machine-checks the two-input structure already implicit in
`CharSumDeltaStarBridge.lean`'s docstring, and **refines the §0/§2 "one inequality `M`" framing**: `M` (the
moment face) is one of two irreducible inputs.

> **REFINEMENT TO §0/§2 (honest correction, 2026-07-04):** the earlier TL;DR "the prize is ONE inequality
> `M ≤ C√(n log)`" is the *moment face* only. Round 13 machine-checks that `M` bounds just the **average**
> hyperplane incidence; the δ\*-floor also needs the **worst-case** `√q·B` cancellation (BCHKS-1.12), which is a
> distinct phase-correlation input not implied by any moment/energy bound. The core is **two** inputs: the Wick
> bound `WallHolds` (⟹ `M`) **and** `HyperplaneCancellation`. Both are open; both are ON-BGK (BCHKS-1.12 is the
> `√q`-cancellation form of the Paley-graph problem). Modeling caveat: the in-tree `V=F` syndrome hyperplane is
> degenerate (`{b:b·s₁=0}={0}`), so lane R models `H` as a nontrivial index-`deg` subgroup (the honest
> higher-dim analogue) — the two-input verdict is rigorous in that model and consistent with the in-tree bridge.

**═══ STATE after 13 rounds ═══** The capstone is tightened: `WallHolds` now discharges its full analytic
payload axiom-clean (the sup-norm `M`), and the prize is machine-checked to localize to **two** distinct named
open Props (`WallHolds ∧ HyperplaneCancellation`), the second provably not implied by the first. Both are
recognized open thin-2-power √-cancellation statements (BGK moment bound + BCHKS-1.12 worst-case cancellation).
The no-go cartography remains complete and every escape decided. **CORE OPEN, ON-BGK. No fabricated closure.**

---

## 24. Round log — Round 14 (#466, 2026-07-04, Fable): the two inputs are INDEPENDENT + the real machine-checked two-sided iff + an honesty correction to §0

Round 13 established the core is two distinct inputs; round 14 completes that thread (their relationship + the
two-sided iff) and corrects an over-stated §0 claim. Essay: `deltastar-466-essay-round14-2026-07-04.md`. 2 lanes
+ 2 adversarial skeptics (5 agents); Lane D severity minor, Lane I severity none. DISPROOF `466-r14-*`.

**(D) The two open inputs are INDEPENDENT — neither implies the other.** Round 13 proved `WallHolds ⇏
HyperplaneCancellation` (the wall's sup-norm `M` is phase-blind — controls only the `s₀`-average incidence).
Round 14 proves the REVERSE also fails, `HyperplaneCancellation ⇏ WallHolds`: `HyperplaneCancellation`'s only
spectral input is `M`, and the sole per-rung fact `M ≤ B` supplies is the Hölder projection
`A_r = ∑_{b∈H}‖η_b‖^{2r} ≤ |H|·B^{2r}` — which, with the wall's own `B² = 2e·n·(ln q+1)`, has the WRONG SHAPE
`(2e·n·ln q)^r` vs Wick `(2r−1)‼·n^r` and **strictly exceeds** the Wick RHS at `r=1` (`_R14SupNormWeakerThanWall.lean`,
3 axiom-clean thms: `supBound_sumPow_le`, `wick_lt_supProjection_r1`, `wallConst_sq_ge_n`; probe: overshoot 45–75×
at r=1 growing to `~10¹²` by r=15, at every n, ≥2 primes). So `M` (a single spectral radius) is a strictly lossy
projection of the whole moment tower and cannot recover it. **Verdict: the moment/energy layer (`WallHolds`, ⟹ the
Paley-graph sup-norm, strictly stronger than it) and the phase-correlation layer (`HyperplaneCancellation`,
BCHKS-1.12) are orthogonal — the prize needs BOTH; neither is the sole bottleneck.**

**(I) The real machine-checked two-sidedness: the OUTER iff.** `_TwoSidedCapstone.lean` (6 axiom-clean thms; skeptic
severity none) proves BOTH DIRECTIONS `ε_mca(C,δ) ≤ E/q ⟺ WorstCaseIncidenceBounded C δ E` — the NEW reverse
(`worstCaseIncidenceBounded_of_epsMCA_le`) unfolds `epsMCA` as the per-stack sup and cancels `q`. Sufficiency
`WorstCaseIncidenceBounded ⟹ δ ≤ mcaDeltaStar C (E/q)` is fully proven; necessity is proven pointwise with the named
`hGoodAt` (goodness at the non-attained sSup boundary, not laundered). The inner reduction of the incidence Prop to
`WallHolds ∧ HyperplaneCancellation` stays the open glue `IncidenceFromWallGlue` (the in-tree bridge budget is the
naive `⌈|G|+q·B⌉`, vacuous at prize; the non-vacuous form needs the `√q·B` `HyperplaneCancellation`). Verdict
IFF-PARTIAL-NAMED-GLUE.

**(⚠️ Honesty correction to §0/§5, folded above.)** The dossier's `ERM-at-r ⟺ M ≤ √((2r+1)n)`, "floor and ceiling
are the same object", was *prose*: only the forward `ERM ⟹ bound` is formalized (`gaussianEnergyBound_of_ERM`), raw
ERM is DC-crossover-refuted (n=32, r=6), and a whole-cone grep found no formalized ERM iff. The campaign's genuine
machine-checked two-sidedness is round 14's outer `ε_mca ⟺ incidence` iff — NOT an `ERM ⟺ M` iff. The sup-norm `M`
is a strictly lossy projection of the moment tower (Lane D), so `M` and the Wick tower are not the same object.

**═══ STATE after 14 rounds ═══** The reduction is now maximally sharpened and honest: the δ\*-floor is
machine-checked equivalent both ways to `WorstCaseIncidenceBounded` (outer iff); that Prop reduces (one-directional
named glue) to `WallHolds ∧ HyperplaneCancellation`, two **independent** open inputs — the phase-blind Wick moment
bound (BGK proper, ⟹ the Paley-graph sup-norm) and the phase-correlation worst-case `√q·B` cancellation (BCHKS-1.12)
— neither implying the other, both open, both ON-BGK. The no-go cartography is complete, capstoned, two-sided at the
outer layer, and every escape decided. **CORE OPEN, ON-BGK. No fabricated closure.**

## §25. Round 15 (2026-07-07) — the FIRST dedicated Problem-B structural round: the diagonal spike, the corrected off-diagonal B, and the χ/moment decompositions

Three lanes + three adversarial skeptics (all CONFIRMED, severity minor). DISPROOF tag
`466-r15-diagonal-spike-and-offdiag-moment`; bricks `_R15GaussDecompDiagonalSpike.lean`,
`_R15IncidenceMomentInterchange.lean` (both real-build verified, 3315 jobs, axiom-clean).

**Lane B1 (Gauss-sum decomposition).** Exact identity (verified to 1e-10, 33 (n,p,deg) cells):
`I_H(s₀) = (p·1_{s₀∈μ_n} − n)/deg + (1/deg)Σ_{χ≠χ₀} g(χ)·T_χ(s₀)`, `T_χ(s₀)=Σ_{x∈μ_n,x≠s₀}χ̄(s₀−x)`.
Consequences: (i) **Problem B over ALL offsets is FALSE** — the χ₀ term is a structural diagonal
spike `≈ |H|` at every `s₀ ∈ μ_n`; round 13's "worst/(√|H|·M) = 6.1→13.7" is exactly `√|H|/M`,
the trivial diagonal, fully explained — **B must be restated off-diagonal (`s₀ ∉ μ_n`) or
χ₀-subtracted** (a reformulation of the campaign Prop, NOT a refutation of BCHKS 1.12);
(ii) corrected off-diagonal B is empirically Θ(1)-true (ratio 0.61–1.61, no |H| growth over
×1000); (iii) **new unconditional partial bound** `‖I_H(s₀∉μ_n)‖ ≤ n√p` (beats the trivial
`|H|·M` budget by `n^{1.5}/deg` at prize scale); (iv) the corrected B reduces per-χ (√deg loss)
to square-root cancellation of the twisted thin-subgroup sums `T_χ` — the same wall, now a
cleaner scalar family; deg=2 face: `|Σ_{x∈μ_n}(s₀−x|p)| ≤ √2·M` (Legendre over the shifted
subgroup — Karatsuba/Shkredov shifted-subgroup literature is the round-16 lane).

**Lane B2 (s₀-moment tower).** `S_r = Σ_{s₀}‖I_H‖^{2r}` is the η-weighted 2r-energy of H; also
`I_H(s₀) = Σ_{t∈H/μ_n} conj(η_t)·η_{t·s₀}` (coset autocorrelation). Raw Wick-for-incidence is
probe-REFUTED (the same diagonal: `I_H(s₀∈μ_n) = Σ/n` EXACTLY); the **diagonal-subtracted tower
(D = {0}∪μ_n) obeys Wick at every probed scale with ratio < 1 decreasing in r** — the offset-side
mirror of Problem A's mandatory DC subtraction. Conditional interchange landed axiom-clean:
diagonal-subtracted Wick rung at `r=⌈ln q⌉` ⟹ off-diagonal B up to `√(2e·ln q)` (9 audited
declarations). The named open residual `WickForIncidenceAwayAt` reduces to the char-p deep-depth
object **with thick-H averaging in front — the one genuinely new lever**; round-16 target: the
r=2 rung unconditionally via Shkredov thick-subgroup E₄ (probe ratio 0.18–0.58, comfortable room).

**Lane A1 (audit).** The §6 "Hankel/Lax-pair seam" was already dead in-tree
(`_AssaultV2_JacobiToda.lean` isospectral kill + tags r1/r10/r11) — struck above. New loophole
check: interlacing under moment-window growth gives only LOWER bounds on M (Gauss-quadrature
edges converge to M from below at depth ≈ ln p); increments are Θ(√n) not O(1), so the
rank-one-update variant RELOCATES to Problem A verbatim. No A-side residual outside the ledger.

**═══ STATE after 15 rounds ═══** Problem B is now correctly stated (off-diagonal), structurally
decomposed two independent ways (χ-decomposition; s₀-moment tower), carries its first
unconditional nontrivial partial bound (`n√p`), and its moment face acquires the first genuinely
new lever since the two-Prop split (thick-H averaging). **CORE OPEN, ON-BGK. No fabricated
closure.**

> **Numbering note (2026-07-07 hygiene pass, round 24):** sections from here down were written by concurrent sessions and originally carried duplicated numbers (two §26s, two §27s, two §28s, two §30s). They have been renumbered into a single consistent sequence §26–§37; content is unchanged. Older notes citing '§32/§33 (rounds 22/23)' now correspond to §36/§37.

## §26. Round 16 (2026-07-07) — lane B2 first result: away-Wick refuted as universal, the diagonal made exact, and the constant-C corrected tower

DISPROOF tag `466-r16-away-wick-refuted-diag-exact`; brick `_R16DiagonalExactValue.lean`
(axiom-clean, real-build verified). Probes `probe_r16_b2_{quad,spikedom,spikeloc}.py` +
independent float128 recomputation of the decisive cell.

**The r15 named hypothesis is FALSE as stated.** `WickForIncidenceAwayAt` with `D = {0}∪μ_n`
and Wick constant `(2r−1)‼` has machine countermodels: `(p,n,deg) = (7681,64,8)` at β≈2.15
(`S'_2/Wick = 1.0048`, `S'_3/Wick = 1.0364`) and thin-`H` cells at β=4
(`deg≥128` at n=16, ratio up to 2.05). Failing offsets are unstructured (full order, ∉H,
∉μ_n+μ_n), arriving in exact μ_n-orbits — an EVT tail, not a hidden diagonal. In the
prize-shaped bulk (β≈4, deg≤32) all margins are 0.55–0.97: the constant is knife-edge.

**What landed axiom-clean.** (i) `incidenceSum_diag_exact`: for a subgroup `G` stabilizing `H`,
`I_H(s₀∈G) = Σ/|G|` exactly (pure reindexing, no primitivity) — the r15 spike bound upgraded to
an identity; (ii) exact μ_n-orbit invariance of the incidence field; (iii) `diagMass_exact`
closed form; (iv) `I_H(0) = conj(Σ_{b∈H}η_b)`; (v) the corrected named object
`WickAwayAtWithConstant … C` with rungs r=0,1 for all C≥1 and the moment bridge at depth
`⌈log(C·q)⌉` — the `√(2e log)`-loss interchange survives the correction verbatim.

**State.** Problem B's moment face now carries: an exact diagonal (no analytic content), a
refuted knife-edge constant, and a probe-calibrated corrected target (C=4 sufficient at every
probed cell; open at the prize instance). CORE OPEN, ON-BGK.

## §27. Round 16 (2026-07-07) — the round-15 openings cashed in: B's first unconditional theorem, the sound Prop layer, the r=2 lattice, the Legendre face

Four lanes + four skeptics (all CONFIRMED, minor). DISPROOF tag `466-r16-partialB-unconditional-and-r2-lattice`.
Bricks (all real-locked-build, axiom-clean): `_R16UnconditionalIncidenceBound.lean` (the FIRST
unconditional theorem-level partial Problem B: `‖I_H(s₀∉G)‖ ≤ |G|·((m−1)√q+1)/m ≤ n√q`, every thick
index-m subgroup, general m — glued from R15 resummation + #407 ConstantIndexGaussSumBound; deg=2
per-shift bound TIGHT), `_R16OffDiagonalHyperplaneCancellation.lean` (Prop-layer audit: nothing
formal was unsound — HyperplaneCancellation was docstring-only, V=F lineIncidence is offset-blind;
+ the corrected `OffDiagonalHyperplaneCancellation` Prop and its wiring from the R15 Wick tower at
C = √(2e⌈ln q⌉)), `_R16IncidenceR2Rung.lean` (r=2 rung lattice: diagonal quadruples = 2/3·Wick
unconditionally; open content = `StrongR2Rung` signed-quadruple cancellation, empirically true but
margin down to ~4% — a live falsification watch), `_R16LegendreCosetFace.lean` (face coset-invariant
⟹ m DOF; exact ℤ second moment |G|q−|G|²; face statistically INDEPENDENT of M per prime — a
distinct object sharing the value; Weil moments stall at k=2, unconditional max|W| ≲ 1.3·n^{3/2}).

**═══ STATE after 16 rounds ═══** Problem B (corrected, off-diagonal) now has: a formal Prop, a
sound consumer audit, an unconditional n√q theorem, an exact r=2 reduction lattice whose sole open
content is the signed quadruple cancellation (with a thin-margin falsification watch), and a deg=2
scalar face with exact averages over only m cosets. Problem A unchanged. **CORE OPEN, ON-BGK. No
fabricated closure.**

## §28. Round 17 (2026-07-07) — StrongR2Rung refuted in the bulk; r=2 closes modulo Weil; averaging proven Wick-flat

Three lanes + skeptics (all CONFIRMED, minor). DISPROOF tag `466-r17-strongr2rung-bulk-refuted-and-weil-r2`.

1. **Refutation win:** the constant-2 r=2 rung is DEAD in the β=4 bulk for deg ≥ 8 (deg-plateau law
   `S₂^D/Wick ≈ 1 − c/deg` — first campaign violation ABOVE β=4-onset norms); constant-3 survives
   all β ≥ 2.7. The live r=2 object is `WickAwayAtWithConstant` with C ∈ (2, 3].
2. **Conditional-proof win (`_R17QuadrupleWeilRung.lean`):** r=2 rung at explicit K(deg) reduces to
   textbook Weil (+ the R15 duality identity + hSig energy-equidistribution, probe-only) for
   p ≳ n⁴; **r=2 is the LAST Weil-closable rung** (rung r needs n^r ≲ √p). The wall is now the rung
   gap [3, ⌈ln q⌉].
3. **Exact identities (`_R17TchiMomentIdentities.lean`):** cross-χ and cross-offset second moments
   proven exactly Wick-flat (arbitrary G, arbitrary nontrivial MulChar; general two-point
   orthogonality new); fourth moment Wick-true at β=4 but value-useless (n^{3/2}).
4. **Literature (web-verified):** nothing published beats √p at n = p^{1/4} worst-shift
   (Karatsuba ≥ q^{1/2+ε}; bilinear Vinogradov √(q|A||B|)); r16 UNVERIFIED flags resolved.

**═══ STATE after 17 rounds ═══** The r=2 layer of corrected Problem B is fully mapped: constant-2
refuted in-bulk, constant-3 open-but-surviving, constant-K(deg) proven modulo textbook-Weil
formalization inputs in the prize regime. All second-moment averaging directions are exact
identities with zero slack. The open analytic content of the B-moment route is precisely rungs
3..⌈ln q⌉ of the diagonal-subtracted tower — the same deep-depth wall, now with exact rung
bookkeeping. **CORE OPEN, ON-BGK. No fabricated closure.**

## §29. Round 17 (2026-07-07) — the FIRST discharged rung: r=2 away-Wick at deg=2 is Weil-classical, via the exact QR bridge

DISPROOF tag `466-r17-deg2-weil-rung-discharged`; brick `_R17Deg2WeilRung.lean` (axiom-clean,
real-build verified, 10 audited declarations). Probe `probe_r17_deg2_weil_rung.py` (18 cells).

**The discovery.** For `H = QR` the incidence field collapses exactly:
`I_QR(s₀) = (q·1_G(s₀) − n + g·W(s₀))/2` with `W(s₀) = Σ_{y∈μ_n}χ(s₀−y)`, `|g|² = q` — so the
deg-2 face of corrected Problem B IS the shifted-subgroup character sum, and the r=2 rung is
the fourth moment of `W`: paired quadruples give the Wick main term, all-distinct quadruples
are Weil sums. The Weil error `3n⁴√q` is subdominant exactly for `√q ≳ n²` (β > 4) — which
CONTAINS the prize scaling (β ≈ 5.3).

**What landed (all machine-checked).** A self-contained real-quadratic-character calculus
(`IsRealQuadChar`: two-point orthogonality, twisted complete sums, `g·conj g = q` — no Mathlib
Gauss-sum import); the exact bridge; exact `ΣW = 0`, `ΣW² = n(q−n)`; the R-kernel split
`W² = (n−1_G) + R` with `ΣR ≤ 0` and `ΣR² ≤ 2n²q + 3n⁴√q` (quartic Weil, matching-pair count
exact); the third moment via Cauchy–Schwarz (no cubic input); and the theorem
**`wickAwayAt_two_of_weil`**: `√q ≥ 16n²` ⟹ the constant-1 r=2 rung
`WickForIncidenceAwayAt ψ μ_n QR ({0}∪μ_n) 2`, conditional only on the named
`WeilQuarticPairs` (Weil 1948; named-residual convention).

**State after 17 rounds.** Problem B now structurally mirrors Problem A: shallow tower rungs
are closed (r=1 unconditional; r=2 at deg=2 classical), and the genuinely-open content is
localized to deep depth `r ≈ ln q` (the moment-method demand) where Weil's `n^{2r}√q` loses to
the main term. At prize scaling the FIRST open rung at deg=2 is r=3 (needs β > 6; prize is
β ≈ 5.3). Round-18: general-deg `T_χ` version (same skeleton per χ), the r=3 boundary rung,
and the deep-rung wall — which is where BCHKS/Paley genuinely lives. CORE OPEN, ON-BGK; the
open region is now delimited from below by machine-checked classical mathematics.

## §30. Round 18 (2026-07-07) — hSig discharged; the r=2 rung reduced to exactly two formalization gaps; plateau explained; welding refuted

Four lanes + skeptics (all CONFIRMED, minor). DISPROOF tag `466-r18-hsig-discharged-weil-isolated-plateau-explained`.
Bricks: `_R18SigmaEquidistribution.lean` (hSig PROVEN for H=G_χ, q ≥ 16m²n²; sharp n(n−1)√q Gauss-sum
bound, saturated at Fermat cells), `_R18FourthMomentTwist.lean` (Weil input isolated to
`QuarticWeilInput` = Hasse genus ≤ 1, verbatim-absent from Mathlib; E₂-escape refuted),
`_R18PlateauLaw.lean` (plateau = variance depletion, exact S₁^D depletion identity, `DepletedWickR2`
target flat in deg), `_R18RungThreeDecomposition.lean` (sixth-moment master identity via cubeWeight
Parseval; 2/5 pairing law; rung-3 deficit exactly n at β=4; **tower-welding refuted** — the banked
E₃(μ_n) slice is negligible ≤ 1e-4 of Wick; open mass is cross-coset self-referential).

**═══ STATE after 18 rounds ═══** The corrected-B moment tower now has a complete r=2 story:
the rung is machine-checked modulo exactly TWO classical-mathematics formalization gaps
(ChiDecompositionOff, QuarticWeilInput) — everything else (hSig, Gauss-sum modulus, degeneracy
combinatorics, the assembly) is proven axiom-clean. Rungs ≥ 3 are the wall proper: each rung r
needs a factor n^{r−2} beyond square-root cancellation, the banked Problem-A energies live in a
negligible slice, and the dominant mass is self-referential. The two towers (A and B) do NOT weld.
**CORE OPEN, ON-BGK. No fabricated closure.**

## §31. Consolidation after rounds 15–18 (2026-07-07) — the corrected two-problem statement

Rounds 15–18 (two concurrent sessions, ~12 landed commits) materially updated what "Problem B"
is. The definitive statement of §0/round-14 should now be read with these corrections:

**Problem B, corrected statement (supersedes the raw round-13/14 form).** The BCHKS-1.12-shaped
input is the OFF-DIAGONAL incidence field: `D = {0} ∪ μ_n` must be deleted (the diagonal value
is the exact rational `I_H(s₀∈μ_n) = Σ/n` — `incidenceSum_diag_exact`, zero analytic content),
and the Wick tower carries a constant: the raw `(2r−1)‼` form is REFUTED as a universal
statement (float128 countermodels at low β and at thin `H`; tag
`466-r16-away-wick-refuted-diag-exact`), the corrected object is `WickAwayAtWithConstant`
(C = 4 probe-sufficient everywhere; plateau law `1 − c/deg` = exact variance depletion, r18).

**What is now CLOSED under named classical inputs (machine-checked):**
- rungs r = 0, 1 of the corrected tower — unconditional;
- rung r = 2 at deg = 2 — `wickAwayAt_two_of_weil` (+ `quadraticChar` instantiation): constant-1
  Wick for `√q ≥ 16n²`, conditional ONLY on `WeilQuarticPairs` (Weil 1948 — a pure
  Mathlib-formalization gap, not open math; the E2-escape is refuted, r18);
- the r = 2 rung reduction lattice at general deg through `QuarticWeilInput` (r18, peer session);
- the deg-2 face is TWO-SIDEDLY the thin-shifted-Legendre sup problem:
  `g·W = 2·I_QR + n` exactly off-diagonal (`_R18Deg2FaceConverse`) — corrected Problem B at
  deg 2 ⟺ Karatsuba's shifted-thin-subgroup cancellation, explicit constants both ways.

**What is genuinely OPEN (the delimited core, replacing "BCHKS 1.12" tout court):**
1. the r = 3 rung at deg = 2 in the β ∈ (4,6) gap (prize β ≈ 5.3): the sixth moment sits AT
   the Wick main term empirically while per-tuple Weil is vacuous — requires cancellation
   ACROSS the genus-2 Weil sums of the family `{∏(s−yᵢ)}_{y⃗∈μ_n⁶}` (vertical-Sato–Tate
   flavor); rung-3 master identity + tower-welding no-go landed (r18);
2. the deep-depth regime `r ≈ ln q` at every deg — the moment-method demand, where the wall
   (Paley/BGK/BCHKS) genuinely lives;
3. Problem A (`WallHolds`) — unchanged since round 12.

**Net effect on the prize statement.** `prize ⟺ WallHolds ∧ HyperplaneCancellation` stands,
but `HyperplaneCancellation`'s open content is now delimited from below by classical
mathematics: everything up to fourth moments is Weil-classical; the first open object is a
family-cancellation statement for sextic character sums; and its deg-2 face is a NAMED
classical open problem (Karatsuba). CORE OPEN, ON-BGK. No fabricated closure.

## §32. Round 19 (2026-07-07) — the duality debt paid; the tower names its fixed point

Four lanes + skeptics (CHIDECOMP severity NONE, rest minor). DISPROOF tag
`466-r19-chidecomp-discharged-tower-collapses-to-awaysup`. Bricks: `_R19ChiDecomposition.lean`
(ChiDecompositionOff + GaussSumSizeBound PROVEN verbatim in the R17 shapes; **r=2 rung = ONE named
input**), `_R19HasseAudit.lean` (±-paired quartic → Legendre cubic EXACT; residual
`LegendreCubicHasse`; minimal missing Mathlib statement pinned; complete quadratic evaluation −1
proven), `_R19DepletedConstant.lean` (C∞ = 3 exactly, envelope ~n^{−1.2}; DepletedWickR2-3
per-instance false; K m²→m modulo FamilyQuarticCubicBound; |X|²-version probe-refuted =
signed-vs-absolute gap), `_R19RungRecursion.lean` (**the tower collapses**: rung weights =
convolution powers of w, ŵ = I_H; sup-split recursion loss ≤ 2.7 flat; L_r ≤ 1 everywhere;
`AwaySupBound C` + tower_of_awaySupBound = the fixed-point equivalence). Plus concurrent-session
`_R18OrderTwoCharacterBridge.lean` (FourthMomentTwist wired to order-2 double-cover inputs).

**═══ STATE after 19 rounds ═══** The corrected-B tower is now a THEOREM-SHAPED object: rung 2 =
FourthMomentTwistBound alone (whose ±-paired quadratic face = elliptic Hasse, the pinned Mathlib
gap); rungs ≥ 3 ⟺ AwaySupBound (the prize sup itself) up to measured per-rung constant ≤ 3, with
sub-Wick monotonicity (W_{r+1} ≤ W_r) as the new standalone structural conjecture. The wall's
sharpest name: **AwaySupBound C at C = O(polylog q)**. **CORE OPEN, ON-BGK. No fabricated closure.**

## §33. GRAND CONSOLIDATION after rounds 15–27 (2026-07-07, two concurrent sessions) — the ladder normal form: what is closed, what is THE open object

**This section supersedes §0/§6 as the statement of the open core.** Read the machine-checked
chain in this order: `_R19JacobiFourierExpansion` → `_R20JacobiParseval` →
`_R21QuarticConvolutionCollapse` → `_R22SexticConvolutionCollapse` →
`_R23TripleConvEnergyInput` → `_R24InvolutionNoGo` → `_R25DualFamilyInstantiation` →
`_R26DiscreteLogExists` → `_R27FullTowerCollapse` (all axiom-clean, all unconditional after
r26; DISPROOF tags `466-r15-*` … `466-r27-*`).

**THE LADDER (the final normal form of corrected Problem B / HyperplaneCancellation).**
For every finite field F (q = card F), every divisor pair m·n = q−1, χ any nontrivial
multiplicative character, J the Jacobi coefficient sequence of the thin face on ℤ/m:

  `∑_{s≠0} ‖T(s)‖^{2r} = (q−1) · ∑_{c∈ℤ/m} ‖(J^{∗r})(c)‖²`   — EXACT, every r
  (`fullTower_collapse`), with `m·W_χ = χ·(T − 1)` the exact bridge to the face.

Rung status:
- **r = 1: PROVEN** (`jacobi_parseval`, pure orthogonality).
- **r = 2: PROVEN modulo textbook Weil** (`wickAwayAt_two_of_weil` + the r18 reduction
  lattice; the Weil input is a pure Mathlib-formalization gap, not open math).
- **r = 3: THE CALIBRATED OPEN CORE** (`TripleConvEnergyBound`, C = 40 probe-safe, Gaussian
  C = 6; per-tuple Weil provably insufficient for β ∈ (4,6) ∋ prize).
- **r ≈ ln q: the wall** (`IterConvEnergyWick` at deep depth) — the remaining content of
  `HyperplaneCancellation`; `WallHolds` is its A-side twin in the same Gauss-phase class.

**Closed strategy classes (do NOT re-attempt):** per-tuple Weil at r ≥ 3 in the gap (r18);
spike deletion at the Jacobi level — there is no spike (r23); renormalization descent — the
spectrum↦coefficients map is the DFT involution (r24); uniform Wick constant 1 — refuted with
countermodels (r16); constant-2 r=2 — refuted in the bulk (peer r17).

**Live routes:** (i) Katz vertical equidistribution for the Jacobi angle family along linear
conditions in ℤ/m (the literature route; would close r=3 and plausibly the gap window);
(ii) Hasse–Davenport exact angle relations along subgroup cosets of ℤ/m (unexplored exact
structure ON the ladder object); (iii) a genuinely new idea, now checkable directly against
`IterConvEnergyWick`. CORE OPEN, ON-BGK. No fabricated closure.

## §34. Round 20 (2026-07-07) — the Möbius discharge; the Stepanov program opens; the equivalence goes two-sided at depth

Four lanes + skeptics (one MAJOR correction recorded). DISPROOF tag
`466-r20-mobius-discharged-stepanov-scaffold-depth-twosided`. Bricks: `_R20QuadFaceBridge.lean` +
`_R20MobiusDischarge.lean` (cast bridge + the t = d + 1/s discovery: quartic scales by a perfect
square ⟹ NO cross-ratio machinery; **quadratic face of QuarticWeilInput = LegendreCubicHasse
ALONE**, all n⁴ tuples), `_R20StepanovScaffold.lean` (route decided; twist-negation halving:
one-sided `CubicStepanovUpper` suffices; ~1500–2500-line self-contained core, all Mathlib
ingredients present; must reuse in-tree Stepanov engines), `_R20SupSplitReverse.lean` (ρ ≤ N^{1/r}
unconditional ⟹ **tower ⟺ AwaySupBound two-sided with constant 3 at rungs ≥ log₃q**; below that
depth magnitude-only reverse REFUTED — the phase-deep zone), `_R20SubWickInterpolation.lean`
(log-convexity + ratio monotonicity + the depth-independence no-go; ⚠️ the "two-way collapse"
claim was corrected by the skeptic to one-way — sub-Wick monotonicity stays a live independent
conjecture). Plus concurrent `_R19ExplicitCharacterRung.lean`.

**═══ STATE after 20 rounds ═══** The proof-chain to the r=2 rung is now:
`CubicStepanovUpper` (one-sided Stepanov, pure formalization, ~2k lines) ⟹ `LegendreCubicHasse` ⟹
(Möbius, proven) quadratic face ⟹ (+ open higher-d faces) `FourthMomentTwistBound` ⟹ r=2 rung —
and above it, tower ⟺ `AwaySupBound` is a genuine two-sided theorem (constant 3) at all depths
≥ log₃q. The wall's residual: the head rungs r < log₃q (phase-deep, magnitude-only provably
insufficient), the higher-order-χ quartic faces, and AwaySupBound itself. **CORE OPEN, ON-BGK.
No fabricated closure.**

## §35. Round 21 (2026-07-07) — S1 done (core was in-tree); one uniform Hasse family; head rungs settled; expert statement v2

DISPROOF tag `466-r21-s1-done-orderblind-uniform-family-headrung-settled`. Bricks:
`_R21StepanovS1.lean` (cubic independence glue onto the in-tree #232 non-vanishing core;
CubicStepanovUpper = S2 mechanical linear algebra + S3 assembly), `_R21HigherDFaces.lean`
(order-blind substitution ⟹ ALL χ-orders reduce to `TripleLinearHasse`, per-tuple 2√p uniform in d
— the r=2 rung's complete formalization surface is ONE Hasse family), `_R21HeadRungDichotomy.lean`
(sub-Wick: automatic above (Λ−1)/2, phase-deep below — deleted as independent conjecture; exact
free-measure max Λ/(2r+1)), `deltastar-466-expert-statement-v2-2026-07-07.md` (definitive v2;
finding F1: "C∞=3 exactly" was probe-only — corrected).

**═══ STATE after 21 rounds ═══** The B-side is now: r=2 rung ⟸ TripleLinearHasse (one uniform
superelliptic Hasse family; its order-2 member ⟸ CubicStepanovUpper, whose hard core is in-tree
and whose remainder is mechanical); tower ⟺ AwaySupBound two-sided at depth ≥ log₃q; head rungs
= the wall's shadow (phase-deep, proven). **CORE OPEN, ON-BGK. No fabricated closure.**

## §36. Round 22 (2026-07-07) — S2 proven; the pipeline assembled; constants parametric everywhere

DISPROOF tag `466-r22-s2-done-pipeline-assembled-constant-parametric`. Bricks: `_R22StepanovS2.lean`
(S2 DONE — auxiliary-polynomial existence, zero residuals; char-p Hasse-derivative machinery
landed), `_R22StepanovAssembly.lean` (the full S2Output → CubicStepanovUpper → LegendreCubicHasseC
→ QuarticWeilInputC → rung pipeline, 18 theorems; NO consumer needs the sharp Hasse constant —
Cw parametric; S = 2#N⁺+3−q exact), `_R22Order2Link.lean` (d=2 family member welded as a theorem;
honest mass accounting: d=2 is 1/(m−1) of the family), `_R22SuperellipticIndependence.lean`
(d-generalization mapped; Kummer inputs proven; DBlockIndependence named with d=2 instance proven
from the in-tree core).

**═══ STATE after 22 rounds ═══** Remaining for the UNCONDITIONAL r=2 quadratic face: parameter
instantiation (m,J,D as explicit functions of q satisfying the two proven budgets), the Euler
criterion bridge, and small-q — pure arithmetic against proven interfaces. The d ≥ 4 bulk of the
family = the norm-fold construction (new work, mapped lemma-by-lemma). Above the rung: unchanged
(tower ⟺ AwaySupBound at depth; head rungs phase-deep). **CORE OPEN, ON-BGK. No fabricated
closure.**

## §37. Round 23 (2026-07-07) — 🏁 THE STEPANOV MILESTONE: the unconditional Hasse-type theorem lands; the r=2 quadratic face fires

DISPROOF tag `466-r23-MILESTONE-unconditional-stepanov-hasse`. Two independent parameter families
(PARAM K=169/49, MILESTONE K=625), both skeptic-verified at severity NONE:
**`legendreCubicHasseC_unconditional`** (every odd finite field, gap-free, zero named hypotheses,
no Weil input anywhere in the chain — pure Stepanov: S1 independence [in-tree #232 core] + S2
rank-nullity existence [r22] + Euler bridge + explicit ℕ-sqrt parameter arithmetic [this round])
and **`fourthMoment_quadChar_unconditional`** (Cw = 17; tight 11). To our knowledge the first
machine-checked elementary Weil/Hasse-type character-sum bound in any proof assistant.

**═══ STATE after 23 rounds ═══** The corrected-B r=2 rung: quadratic face UNCONDITIONAL;
remaining faces = the superelliptic d ≥ 4 family (norm-fold, mapped in r22). Above the rung:
tower ⟺ AwaySupBound (two-sided at depth), head rungs phase-deep. Problem A unchanged. The
campaign's first unconditional wall-adjacent THEOREM. **CORE OPEN, ON-BGK. No fabricated
closure.**

## §38. Round 24 (2026-07-07) — d=4 independence proven (new descent technique); the full-rung pipeline; the gate audit

DISPROOF tag `466-r24-dblock-d4-proven-supers2-fullrung-gate-audit`. Bricks:
`_R24DBlockIndependence.lean` (d=4 PROVEN — alternating-conjugate fold + extension-free quartic
descent, a genuinely new formalization technique; d=2^k iterates mechanically),
`_R24SuperellipticS2.lean` (d-block S2 chain conditional on DBlockIndependence alone),
`_R24FullRungAssembly.lean` (pipeline + `fullFamily_gate_impossible`: the full-family normalized
gate was NEVER live, even for sharp Weil — the live route is subfamily-Y), UPSTREAM hygiene
(EulerBridge import fix; dossier renumbered — rounds 22/23 logs now §36/§37; Mathlib PR plan).

**═══ STATE after 24 rounds ═══** r=2 rung: d=2 face UNCONDITIONAL (§37 milestone); d=4
independence PROVEN, its S2 machinery in place (parameter instantiation owed); d=8+ mechanical
descent iterations; full-family gate dead by theorem, subfamily-Y the live consumer. Above the
rung unchanged (AwaySupBound; head rungs phase-deep; Problem A). **CORE OPEN, ON-BGK. No
fabricated closure.**

## §39. Round 25 (2026-07-08) — d=8 proven (tower pattern found); non-squarefree kernel resolved; the subfamily gate honestly pinned

DISPROOF tag `466-r25-d8-proven-nonsquarefree-resolved-suby-not-free`. Bricks:
`_R25D8Descent.lean` (dBlockIndependence_eight; 2^k recursion: next descent = same descent over
K(√c), hypotheses stable — d=16 mechanical), `_R25D4Instantiate.lean` (s²·r radical fold; first
non-squarefree instance; quintic_kernel_fiber_bound = the pipeline's count supply, asymptotic
regime flagged), `_R25SubfamilyGate.lean` (subfamily-Y NOT free; original-H gate ⟺
HyperplaneTransferOff, refuted as exact identity; bounded-residual variant is the real target).
MATHLIB-drafts lane failed (nothing produced; redo owed).

**═══ STATE after 25 rounds ═══** The superelliptic Stepanov program: independence proven at
d ∈ {2,4,8} including the true non-squarefree kernels; the 2-power tower is a mechanical
recursion; fiber counts supplied to the pipeline. The rung's live consumer needs the
bounded-residual subfamily gate (cross-character cancellation — a genuinely analytic question).
**CORE OPEN, ON-BGK. No fabricated closure.**

## §40. Round 26 (2026-07-08) — the second face falls; the tower capstone; the mixed-moment pin

DISPROOF tag `466-r26-d4-face-unconditional-d16-tower-mixedmoment-pinned`. Bricks: `_R26D4Mirror.lean`
(**tripleLinearHasseC_d4_unconditional**, K=45, zero named hypotheses — the SECOND unconditional
face), `_R26D16.lean` (d=16 + the uniform `dBlockIndependence_two_pow` capstone, k ≤ 4),
`_R26ResidualL2CrossIdentity.lean` (new exact cross-χ identity with Jacobi modulus √q; per-part
splits provably overspend — the subfamily gate's open content = **Main–Res mixed-moment
cancellation**). MATHLIB debt now 2 rounds (owed).

**═══ STATE after 26 rounds ═══** The r=2 rung: two unconditional faces (d=2, d=4); independence
closed through d=16 with a uniform capstone; the one remaining analytic input for the live gate is
the Main–Res mixed moment. Above the rung unchanged. **CORE OPEN, ON-BGK. No fabricated closure.**

## §41. Round 27 (2026-07-08, Opus) — the mixed moment goes real; the rung fires at κ=1/2

DISPROOF tag `466-r27-mixed-moment-real-rung-fires-at-half`. Bricks: `_R27FMixedMoment.lean`
(+`_R28FMixedMomentGuards.lean`): M' and Res proven pointwise real in the rung regime ⟹ mixed
moment = real ∑(A+B)⁴; `_R27GMixedAudit.lean` (`mixed_rung_fires_at_half`): the composed RHS at
κ=1/2 is 0.919·budget < budget — **the subfamily rung is machine-checked to FIRE once
`MixedMainResHalfCS(½)` is supplied** (the cross-block 4-character decoupling object, exactly
pinned). `_R27GD8D16Mirrors.lean` (d=8/16 parameter backbone; blocked on non-squarefree
`dBlockIndependence_{eight,sixteen}_sqmul`); `_R27GGenericDescent.lean` (quadAdjoin extracted
generic; k=5 pattern confirmed; general-k induction still open).

**═══ STATE after 27 rounds ═══** The r=2 rung subfamily gate is reduced to a single precise
open object (`MixedMainResHalfCS(½)`, a Y×complement decoupling), and the rung is PROVEN to fire
once it lands (6.5% slack, machine-checked). Two unconditional faces (d=2,4); independence d ≤ 16;
mirror arithmetic + general-k skeleton in place. Above the rung unchanged. **CORE OPEN, ON-BGK.
No fabricated closure.**
