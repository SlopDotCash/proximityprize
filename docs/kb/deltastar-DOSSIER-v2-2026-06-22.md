# Prove δ\* — the complete research dossier (v2)

> **The canonical, self-contained account of the Ethereum RS Proximity Prize as a formalization target.**
> Consolidated 2026-06-22 from: [proximityprize.org](https://proximityprize.org/); the companion paper *Open Problems in List Decoding and Correlated Agreement* (Arnon–Boneh–Fenzi 2026, ePrint 2026/680, **"ABF26"**); the full #444 thread (1,190 comments) and its predecessors (#407/#389/#371/#357/#334/#232); the in-tree substrate (~1,667 ProximityGap files, ~1,544 in `Frontier/`); the KB dossiers; the external number-theory PDFs; and independent re-verification. **This issue is the working successor to #444 — start here.**
>
> **Mission.** Pin **δ\*** — the mutual-correlated-agreement (= list-decoding) threshold — for *explicit* smooth-domain Reed–Solomon codes in the **window interior `(1−√ρ, 1−ρ−Θ(1/log n))`**, worst-case, with a *closed* proof (reducing only to known-proven mathematics). This solves **both** grand challenges (Grand-MCA and Grand-list-decoding — one threshold).
>
> **Honesty contract (non-negotiable).** Be **bold in exploration, strict in proof-claims.** A claim is "proven" only with an axiom-clean Lean declaration (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`); everything else is `conjecture` / probe / `docs/kb` note. Refutations (machine countermodels) are *wins*. Never fabricate closure. **The core is a recognized open problem in analytic number theory** — naming it as an open `Prop` and building around it is the project's modularity convention, not incompleteness.

---

## 0. TL;DR — where the prize actually stands

After a multi-month, multi-agent campaign (≈1,700 comments across #407+#444, ~50 independent confirmations, a full axiom-clean substrate, and an exhaustive propose→refute discipline), the situation is **decisive in structure and open at the core**:

1. **The prize is ONE inequality.** Both Grand Challenges, all ~20 analytic "faces," and every proven reduction funnel to a single statement:
   > **(CORE)** `M(μ_n) := max_{b ≢ 0 (mod p)} |Σ_{x∈μ_n} e_p(b·x)| ≤ C·√(n·log(p/n))`, `C = O(1)`,
   > for the dyadic subgroup `μ_n ⊂ F_p^×`, `n = 2^μ`, at the **Burgess barrier** `p ≈ n^β`, `β ≈ 4`, `n ~ 2^30`.

   This is the **thin-subgroup BGK / Paley √-cancellation wall** = the non-principal eigenvalue of the generalized Paley graph `Cay(F_p, μ_n)` = the worst-case cyclotomic Gauss period = the house of a degree-`m` algebraic integer = the DFT sup-norm of the Gauss-sum vector. **It is a recognized ~25-year-open problem in analytic number theory.**

2. **The wall is two-sided and necessary.** It is proven (axiom-clean) that the floor lower-bound direction and the moment upper-bound direction are the *same* object (`ERM-at-r ⟺ M ≤ √((2r+1)·n)`), and that **every second-order / energy / spectral / SDP method provably caps at Johnson / √p** (the Meta-Theorem). There is **no elementary route** and **no off-BGK escape** that reaches the window interior — every such route is proven to collapse to Johnson or to equal the wall.

3. **The char-0 half is fully closed.** `E_r(μ_n) ≤ (2r−1)‼·n^r` is proven for *all* r in characteristic 0 (Lam–Leung antipodal pairing; Bessel `I₀(2y)^m ≤ exp(m y²)`; exact energy ladder E₂…E₃₃). The **entire residual is the characteristic-p transfer at depth `r ≈ ln q ≈ 89`** — i.e. whether short (`≤ 2 ln q`-term) `±1`-relations of `2^μ`-th roots of unity vanish modulo the prize prime more often than at the Wick (Gaussian) rate.

4. **What is genuinely new and rare here** is *not* a solution but a **complete cartography**: the problem has been reduced, two-sidedly and axiom-cleanly, to exactly the open analytic wall; every classical and many non-classical attack routes have been *eliminated as theorems* (not just "tried"); the wall has been re-expressed in ≥6 kernel-equivalent forms (energy / Paley-eigenvalue / wraparound-variance / Jacobi-turnover / orbit-count / signed-deep-cancellation); and it has been *proven that numerics cannot decide it*.

5. **The evidence is mildly favorable to the floor being TRUE** (so δ\* sits strictly inside the window): the normalized constant `C = M/√(n·log(p/n))` is non-divergent in `[1.07, 1.49]` (hugging `√2`) across eight octaves `n = 8…1024`; the char-0 anchor `K_eff → 1` strictly from below; and the GPU-measured worst-case list is bounded deep in the window interior. **But "mildly favorable" is not a proof, and a proof needs external analytic NT that does not yet exist in the literature.**

6. **There is exactly one genuinely off-BGK obstruction-removal lever still standing** (§9): the **bad-prime localization / least-prime-in-AP** route for the explicit binder-family floor obstruction. It is a 0-dimensional cyclotomic-resultant question, *not* a character sum. The exact closure premise is: if "floor-bad primes = the single smallest prime ≡ 1 mod n" holds uniformly in `μ`, and that least prime is below prize scale `n^4`, then every prize-scale prime is good for this modeled binder predicate. Classical exponent-5 Linnik does **not** by itself imply the below-`n^4` premise, but the Thorner--Zaman powerful-modulus refinement now supplies an unconditional sub-quartic dyadic least-prime exponent `12/5+ε` (§16C; `deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md`). Proven at `n = 16` and `n = 32` for the modeled floor predicate. This is still a useful arithmetic check, but §16 is the governing correction: binder-family floor-goodness is necessary, not sufficient, for the δ\* lower pin.

**Bottom line.** The prize is **OPEN and ON-BGK.** The campaign's achievement is to have turned a vague $1M challenge into a single, precisely-stated, two-sidedly-reduced open inequality with a fully mapped no-go landscape — and to have done so honestly, with the open core carried as a named `Prop` and never larped as closed.

---

## 1. The problem — exact target, formal objects, and governing law

### 1.1 The prize (verbatim from proximityprize.org + ABF26)

The Ethereum Foundation offers **$1,000,000** for resolving two "grand challenges" about Reed–Solomon codes underpinning SNARKs (FRI/STIR/WHIR). Both fix:

- A Reed–Solomon code `C := RS[F, L, k]`, evaluation domain `L ⊆ F` **smooth** (a dyadic FFT subgroup), **constant rate** `ρ(C) := k/|L| ∈ {1/2, 1/4, 1/8, 1/16}`, `|F|` sufficiently large.
- The target error `ε* = 2^−128`.

**Challenge 1 — Grand MCA.** *Determine the largest `δ*_C ∈ [0,1]` such that `ε_mca(C, δ*_C) ≤ ε*`.*

**Challenge 2 — Grand List Decoding.** *Determine the largest `δ*_C ∈ [0,1]` such that `|Λ(C^{≡m}, δ*_C)| ≤ ε*·|F|`* (the interleaved list at radius `δ`, constant `m`).

The two thresholds coincide on the relevant window — **one δ\***. The companion ABF26 frames `ε_mca` (mutual correlated agreement) as the strengthening of correlated agreement (CA) in which a *single* witness set must simultaneously certify closeness and non-agreement.

### 1.2 The formal objects (in-tree, machine-checked — `ArkLib/Data/CodingTheory/ProximityGap/`)

- **`mcaEvent`** (ABF26 Def 4.3, `Errors.lean:216`): for a code `C`, radius `δ`, words `u₀ u₁`, scalar `γ`:
  `∃ S, |S| ≥ (1−δ)·|ι| ∧ (∃ w∈C, ∀ i∈S, w i = u₀ i + γ·u₁ i) ∧ ¬ pairJointAgreesOn C S u₀ u₁`.
- **`epsMCA`** (ABF26 Def 4.3, `Errors.lean:231`): `ε_mca(C,δ) := ⨆_{u : WordStack} Pr_{γ ← $F}[mcaEvent C δ (u 0) (u 1) γ]`.
- **`mcaDeltaStar`** (`MCAThresholdLedger.lean:86`): `δ*(C, ε*) := sSup {δ ≤ 1 : ε_mca(C,δ) ≤ ε*}`.
- **Brackets** (proven, unconditional): `le_mcaDeltaStar_of_good` (a good radius lower-bounds δ\*), `mcaDeltaStar_le_of_bad` (a bad witness upper-bounds δ\*). `δ*` is pinned by sandwiching these.
- **Degeneracy guards (REFUTED, machine countermodels):** `candidate_floor_is_exact_REFUTED` (ε_mca is *not* pinned to its `1/|F|` floor) and `candidate_uptocapacity_REFUTED` (the "up-to-capacity" form is false for small fields — the prize *must* fix `|F|` large). Read these before proposing any closed-form δ\*.
- **The non-degenerate prize target** is `mcaConjecture` / `mcaConjectureBound` (`GrandChallenges.lean:650/623`) and the workbench object `mcaDeltaStar` — **not** the radius-one-degenerate `grandMCAChallenge`.

### 1.3 The prize regime (the constants that make it hard)

- Domain: dyadic FFT subgroup `μ_n`, `n = 2^μ`, a **proper** multiplicative subgroup `μ_n ⊊ F_q^×` (`n ∣ q−1`).
- `q = n^β` prime, `β ≈ 4–5`, `ε* = 2^−128`, so `q ≈ n·2^128 ≫ n³`, **budget `q·ε* ≈ n`**, fixed index `m = (q−1)/n = 2^128`.
- **THIN:** `n = q^{1/4..1/5}`, `n ≪ √q`, prize `n ~ 2^30`.
- Window `(1−√ρ, 1−ρ−Θ(1/log n))`, strictly between **Johnson** `1−√ρ` (achievable) and **capacity** `1−ρ` (proven impossible with poly soundness).
- ⚠️ **NEVER validate on the full group `n = q−1`** (special additive structure → false positives, the #400 trap). Always proper subgroups, large prime, multiple primes; exclude correlated directions `X^{n/2} = ±1`.

### 1.4 The governing law (exact identity, in-tree)

> `δ* = sup{ δ : I(δ) ≤ q·ε* }`, where `I(δ) = max_{u₀,u₁} #{ γ : u₀+γ u₁ is δ-close to RS[k] }` is the maximum far-line incidence.

This is `badScalars_eq_explainable` + `epsMCA = ⨆_u Pr_γ[mcaEvent] = max(#bad)/q` (`FarCosetExplosion.lean:87`, `mcaEvent_iff_line_explainable`). Extremal lines are **monomial directions** `(X^a, X^b)` (the `Z/n` dilation symmetry; `_wf3D4` proves monomial is the unique dilation-eigenvector far direction). The status of the endpoints:
- **Johnson `1−√ρ`** achievable (ACFY24/Hab25 prove RS-MCA exactly *up to* Johnson; **vacuous AT Johnson**, `ℓ→∞` there — not a bypass).
- **Capacity `1−ρ`** proven impossible (Crites–Stewart 2025/2046, Diamond–Gruen, Kambiré 2604.09724).
- **The CEILING** `δ* ≤ (1−ρ) − Θ(1/log n)` is proven via the KKH26/Kambiré bad family (one explicit bad line, rate-locked at `r = k+1`) — confirming the window *location* but not the floor.
- **The FLOOR** (worst-case list small for ALL words, so δ\* enters the interior) is the open direction.

---

## 2. The single open core — one object, ~20 equivalent faces

> **CORE.** `M(n) = max_{b≢0(p)} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m)`, `C = O(1)`, at `p ~ 2^160`, `m = 2^128`, for the binding **low-exponent** direction. The prize is proven **two-sided** onto exactly this BGK char-sum; equivalently the char-p energy `E_r(μ_n) ≤ (2r−1)‼·n^r` at `r ≈ ln q`.

### 2.1 The Paley-graph dictionary (the one rigorous structural gain)

By Liu–Zhou (*Eigenvalues of Cayley graphs*, Thm 115/116) and Podestá–Videla (Thm 2.1): the generalized Paley graph `Γ((q−1)/n, q) = Cay(F_q, μ_n)` has non-principal eigenvalues exactly the cyclotomic Gauss periods `η_b = Σ_{x∈μ_n} ζ_p^{Tr(bx)}`, with `Σ_b η_b = −1`. So:
> **`M(n) = max_{b≠0}|η_b| =` the non-principal spectral radius of `Cay(F_q, μ_n)`,** and the prize per-frequency bound **`M ≤ 2√n ⟺ the graph is RAMANUJAN`** (`2√(n−1)` = the Alon–Boppana optimum). In-tree: `GeneralizedPaleyRamanujan.lean` (`‖η_b‖≤2√n ⟹ WorstCaseIncompleteSumBound`).

`M(n)` is **totally real** (`n` even ⟹ `−1 ∈ μ_n` ⟹ undirected graph / real periods). The **Parseval floor** is unconditional: `Σ_{b≠0}|η_b|² = n(q−n)` ⟹ `M ≥ √(n(q−n)/(q−1)) ≈ √n` (`GaussPeriodParsevalFloor.lean`). The prize graph is **NOT** Ramanujan in the strong sense — fresh data gives `M/(2√n) = 1.34…2.43`, well above 1 — but the *order* `√(n log m)` is the open target.

### 2.2 Master reduction chain (axiom-clean)

- `Σ_b η_b^r = q·N₀(G,r)` (the r-th moment is `q ×` the count of r-fold vanishing sums).
- Parseval DC-subtracted identity: `Σ_{b≠0}|η_b|^{2r} = q·E_r − n^{2r}` (verified through `r=6`; `DCSubtractedMoment.sum_nonzero_moment`).
- Dyadic split `N₀(G,r) = 2·N₀(H,r) + crossCell(H,ζ,r)`, exact `crossCell(n,4) = 3n²/2`.
- Moment method: `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r}`, optimized at `r ≈ ln q` gives `M ≤ √(2e)·√(n ln q)` *conditional on the Wick bound at that depth*.

### 2.3 ⚠️ MANDATORY FORM — the DC-subtracted energy `A_r`

Raw `E_r ≤ Wick = (2r−1)‼·n^r` is **FALSE at the prize** (the DC term `n^{2r}/q` dominates for `n ≥ 64`, `r ≥ 8`): `DCEnergyEssential.not_gaussianEnergyBound_of_deep`. **Only the DC-subtracted `A_r = E_r − n^{2r}/q ≤ Wick` is non-vacuous** (`DCEnergyCorrection.DCEnergyBound`). `A_r ≤ Wick` is proven char-0 for *all* r (Lam–Leung structural); the wall is **char-p validity at depth `r ≈ ln q ≈ 89`**. The relaxed honest target is **not** `W_r = 0` (false: onset r₀=5, `W_8 ≈ 1.4×10^17` at the saddle r*=11 for n=16) but `W_r ≤ slack_r`, i.e. `E_r ≤ K^r·(2r−1)‼·n^r` for some **constant K = O(1)** uniformly to `r ≈ ln q`.

### 2.4 The faces (all proven propositionally linked; only the single Prop is open)

| Face | In-tree name | One line |
|---|---|---|
| **F1 Far-line incidence** | `OpenCoreConditionalPin.WorstCaseIncidenceBounded` (= BCHKS Conj 1.12) | floor ⟸ incidence bound + the BGK sup-bound |
| **F2 Orbit-count ≤ d** | `OrbitCountPinNecessity` | converts the analytic floor to a combinatorial orbit-count |
| **F3 Union-growth law** | `unionGrowth_iff_orbitGrowth` | distinct-γ union floor ≡ orbit-count growth (orbit size divided out) |
| **F4 EVT concentration** | `_EVTFloorRoute.prizeFloor_of_EVTConcentration` | de-Finetti substrate proven; residual = `‖η_b‖ ≤ C√(n log(q/n))` |
| **Char-sum form** | `WorstCaseIncompleteSumBound` (`InteriorWorstCaseIncompleteSum.lean:59`) | `∀ b≠0, ‖η_b‖² ≤ M` |
| **Energy form** | `DCEnergyBound` (`DCEnergyCorrection.lean:38`) | DC-subtracted Wick bound at depth `r` |
| **Distributional** | `EtaSubGaussianTail` | sub-Gaussian period tail to depth `ln q` |
| **Conjecture target** | `mcaConjecture` (`GrandChallenges.lean:650`) | the prize predicate itself |

**The decisive L²→L∞ verdict (the freshest localization).** The operative input (F1) is PROVEN in **L²-mean over the offset** (`IncidenceDevL2Offset`: `∑_{s₀}‖D(s₀)‖² = q·∑_{b∈dev}‖η_b‖²`). The remaining gap is L²→L∞, and it is **provably the wall, not a free lever**: `TwoDAnnihilatorLineParseval.lineEta_image_eq_globalImage` proves the offset-magnitude SET `{‖D(s₀)‖}` *equals* the global set `{‖η_b‖}`, so `max_{s₀}‖D(s₀)‖ = M` exactly; and `sum_reindex_mul_unit` forces `#dev = q−1` (the WHOLE nonzero spectrum) — the hoped-for `#dev = O(log)` is structurally impossible. **Bounding the worst offset literally is bounding M.** Every proven input is L²/aggregate; the floor needs the L∞ max; the L²→L∞ collapse at the binding rung `r ~ log n` IS the wall.

---

## 3. SOTA and the external literature — exactly how far, and why the wall stands

The object is `M(n) = max_a |S_a(H)|`, `S_a(H) = Σ_{x∈H} e_p(ax)`, `H = μ_n`, `|H| = n = p^γ`, `γ = 1/β ≈ 1/4`. The literature verdict is **unambiguous**: at the prize point (`γ = 1/4`, 2-power order) **the only proven bound is BGK's `n^{1−o(1)}`, off the `√n` target by a full half-power, and the single best effective bound vanishes exactly there.**

| Result | Best bound on `M(n)` | Status at `β = 4` (`H ~ p^{1/4}`) |
|---|---|---|
| Weil / RH-for-curves | `(n−1)√p` | **vacuous** (`√p ≫ √n`; `μ_n` is 0-dimensional) |
| Heath-Brown–Konyagin (Stepanov) | non-trivial only for index `k ≪ p^{2/3}` ⟺ `n ≫ p^{1/3}` | **vacuous** (`n ~ p^{1/4} < p^{1/3}`) |
| Shkredov additive energy `E(H) ≪ n^{5/2}` | `Φ_A ≪ p^{1/8}n^{5/8}`, needs `n ≫ p^{1/3}` | **vacuous + √-lossy** |
| di Benedetto et al. (2003.06165, sum-product) | `n^{1−31/2880} ≈ n^{0.989}`, **needs `H > p^{1/4}`** | **boundary-vacuous** (saving → 0 as `H ↓ p^{1/4}`) |
| **BGK (Bourgain–Glibichuk–Konyagin)** | **`n·p^{−ν(γ)} = n^{1−o(1)}`** | **the only survivor; `ν` tiny & ineffective** |
| Ramanujan / Paley Graph Conjecture | `√n / 2√n` (= the prize) | **OPEN everywhere** |

**Why BGK is `n^{1−o(1)}` and non-effective.** Its engine is the sum-product / Balog–Szemerédi–Gowers pipeline (Bourgain–Katz–Tao sum-product gives `max(|A+A|,|A·A|) ≫ |A|^{1+δ}` with `δ = δ(γ) > 0` produced *non-constructively*; BSG bleeds polynomial factors `2^14 α^6`). Each alternation loses an unquantified amount, so `ν` inherits a tower of "there exists δ > 0" with no numerics. The bottleneck is precisely the **ineffective sum-product exponent passed through lossy energy refinement**.

**Why di Benedetto's `31/2880` vanishes at `β = 4`.** The proof is an explicit Bourgain-style dyadic descent feeding the trilinear Petridis–Shparlinski bound (`p^{1/4}` prefactor) with the Murphy–Rudnev–Shkredov energy counts `T₂ ≪ H^{49/20}`, `T₃ ≪ H⁴ log H`. Tracking exponents gives `M ≤ H^{2689/2880}·p^{1/72}`. At `H = p^{1/4}`: `p^{1/72} = H^{160/2880}`, so the genuine saving `191/2880` is *eaten* by the `p^{1/72}` loss, leaving only `31/2880 = 191/2880 − 160/2880`. For `β > 4` (`H < p^{1/4}`) the loss exceeds the saving and the bound goes worse than trivial. **The effective sum-product method is structurally dead at and below the prize point.**

**The named open lever = the Paley Graph Conjecture** (Kim–Yip–Yoo Conj 2.12): `|Σ_{a∈A,b∈B} χ(a+b)| ≤ p^{−δ}|A||B|` for `|A|,|B| > p^ε`. It applies at `n = p^{0.19}` (needs only `n > p^ε`) and would close the per-frequency core — but it is exactly the unproven Bourgain/sum-product content. The semiprimitive shortcut (the only sub-`√q` Gauss-period mechanism) is **arithmetically dead** at the prize point: `q = 2^158 ⟹ r/2 = 79` prime ⟹ `t = 1` ⟹ `p^t+1 = 3 ∤ k ≈ 2^128`.

**Campaign SOTA contribution (honest scope).** Specializing di Benedetto Thm 3.1 to `μ_n` with the exact Sidon-floor energies `T₂ = 3n²−3n`, `T₃ = 15n³−45n²+40n` gives `M ≪ |H|^{1−1/24} p^{1/72}`, **β=4 exponent `0.9583`** — beating the generic `0.9892` (≈3.9× the saving) and nontrivial where the generic bound vanishes; β=5 gives `H^{35/36}`. The T₃ char-0 input is now an **unconditional theorem** (`_AvL_T3ClosedForm.rEnergy_mu_three_eq`, axiom-clean). **But** the beat (a) dies at `β = 191/40 = 4.775`, (b) realizes the `1/24` saving only asymptotically (finite-n exponent strictly larger), and (c) stays good-prime-restricted at char-p. **It is SOTA-closeness, not closure** — reaching `1/2` = beating the `p^{1/4}` prefactor = the wall.

**No 2024–2026 paper crosses `n^{0.989} → n^{1/2}` at β=4 for thin 2-power subgroups.** Confirmed by 5+ literature sweeps including a 67-paper arXiv harvest (2026-06-21, the productive search terms are *generalized Paley graph eigenvalue / incomplete Gauss sums over subgroups / Burgess bound subgroups / additive energy of multiplicative subgroups / BGK* — **not** Jacobi/Bessel/graph-theory, which collide on keywords). The missing analytic input **does not exist in the literature.**

---

## 4. The Meta-Theorem, the Tetrachotomy, and the Arithmetic Uncertainty Principle — *why* every elementary route is dead

This section is the campaign's most reusable output: route-elimination *as theorems*, not as "we tried it."

### 4.1 The Meta-Theorem (second-order no-go)

> For the deterministic period family `{η_i}` with `Σ η_i² = p−n`, bounding `max|η_i|` below `√Σ` admits exactly **two equivalent routes** — (a) high moments `Σ η_i^{2r}` to depth `r ≍ log m`, (b) a uniform individual tail ≡ (a). **There is no third route.**

`_MomentMethodNoGo` / `MetaTheoremSecondOrderCap` (axiom-clean): every second-order method caps at Johnson / √p via `(q·E_r)^{1/2r} ≥ n`. Eliminated *as a theorem*: additive energy (any order), L²/Parseval, spectral `λ₂`, SDP/Delsarte-LP (phase-blind ⟹ L¹ triangle = trivial `n`; `DelsarteLPNoGo`), cumulant-2, the Shaw operator. Method-necessity is `_MomentLadderExceedsPrize.moment_ladder_exceeds_prize` (no second-order route at *any* depth). **The 3-property necessary condition on any winning method:** simultaneously (a) **b-sensitive**, (b) **deterministic-archimedean** (not probabilistic-EVT), (c) **genuinely L∞** (sup, not RMS). The probabilistic-EVT crown is killed: periods are exchangeable white-noise (`Cov(η_a,η_b) = −Var/(m−1)`, distance-independent) → kills FHK / GMC / BRW / Coulomb-gas.

### 4.2 The Tetrachotomy (no fifth door)

Any bound on `max_b|η_b|` for the flat 0-dimensional `μ_n` is necessarily one of four branches; doors (i)–(iii) are dead and (iv) closes for the dyadic object:

- **(i) Algebraic geometry (Weil/Deligne)** — CLOSED. Via `y↦y^m` the period is a complete monomial sum but Weil gives `(m−1)√p ≈ p^{5/4} ≫ p`, vacuous, because `μ_n` is **0-dimensional** (Lang–Weil/Deligne give nothing at `d=0`). Any symmetric/discriminant constraint gives only a *lower* bound on `M` (`discnogo`: `disc(Ψ) = p^{m−1}·f²` is class-field-theory-fixed ⟹ **the wall is provably archimedean**).
- **(ii) Additive combinatorics (Burgess/sum–product)** — the only door that engages the real object, but **saturates** at `n^{1−o(1)}`; the trilinear `p^{1/4}` prefactor eats the saving exactly at `|H| = p^{1/4}`. The `o(1)` provably cannot be promoted to a power by current technique.
- **(iii) Harmonic analysis (decoupling/restriction/Vinogradov-MVT)** — CLOSED. All require **curvature**; `μ_n` is **flat** (0-dim, an AP of phases). Decoupling constant trivial; restriction vacuous.
- **(iv) Probability/moments (energy ladder)** — `M^{2r} ≤ Σ|η_b|^{2r} = A_r`; works only at depth `r* ≈ ln p`, where `A_{r*} ≤ K·Wick` **is the wall in moment clothing.** The genuine non-reducing object — *a new evaluation of `η_b`* — is the open problem itself. Motivic/Tannakian relations express `η_b` via Galois conjugates (= symmetric = (i)); the one escape (a conductor factorization) is unavailable since `n = 2^a` has an irreducible 2-power conductor; Bost–Connes/KMS is circular; p-adic↔archimedean transfer is impossible because the period is a *partial* subgroup sum (its two places are independent). **There is no fifth branch.** This is *why* 250+ generated conjectures collapse.

### 4.3 The Arithmetic Uncertainty Principle (the sharpest description of *why*)

For any *magnitude* observable `Mag` (norm / moment / trace / Schatten / Weil — sees only `|u_t|`) and *phase coherence* `Pha`: `(knowable by Mag)·(needed from Pha) ≥ √p/√n = √m`. Magnitude methods resolve the spectrum only to `√p` (incoherent) or `≥ n` (Johnson floor); the truth `√n` needs phase information `√m` finer, **provably absent** (phases structureless). These are Fourier-conjugate (the period is the DFT of the phases), so a magnitude method is maximally delocalized in phase — exactly Fourier uncertainty, with the "Planck constant" pinned at `√m`. **To violate it is to prove the phases equidistributed = cross the Burgess barrier.** This is the cleanest explanation of the wall's *existence*, not a key to it.

### 4.4 The structured-prime lever is quantified-dead

Since `n = 2^30 ∣ p−1`, every prize prime has `v₂(p−1) ≥ 30` — the prize lives *inside* the "structured / 2-power" regime that is empirically worst-case (lowest onset `r₀`, explicit Fermat `W₄` defect). A dedicated round attacked exactly there, where 2-adic / Stickelberger / complete-splitting machinery is strongest. Result (axiom-clean, `_wf5M2_stickelberger_depth.lean`): the depth-`R` Stickelberger / prime-splitting ceiling is `p ≤ w^{n/(4R)}` — **non-vacuous only at `R ≈ n/8` (the full window), and super-polynomial (zero constraint on `p = n^β`) at prize deep-moment depth `R ≈ β·ln n ≪ n/8`.** So the maximal-structure 2-adic lever is an *exact route-refutation*, not an escape.

---

## 5. Discoveries and firsts — what this campaign did that had not been done

These are the genuinely novel, verified contributions (axiom-clean unless noted). They are *machinery and cartography*, not a prize closure.

**Reductions / equivalences (the structural firsts):**
- **Two-sided reduction of the prize onto a single char-sum.** `_EnergyRatioMonotoneReduction` proves `ERM-at-r ⟺ max_c‖η_c‖² ≤ (2r+1)·n`: the floor lower-bound and the moment upper-bound are *literally the same object*. No prior treatment had shown the proximity-gap floor and the BGK sup-norm to be propositionally equal.
- **The Meta-Theorem + Tetrachotomy + AUP** (§4): a *proof* that no second-order method and no fifth structural door exists for this object — route-elimination as theorems.
- **The mandatory DC-subtraction** (`DCEnergyEssential`): the discovery that the raw energy/Gaussian hypothesis is *false* at prize depth and must be DC-corrected — a correction that invalidated a large class of naive "moment" attacks (including the campaign's own earlier ones).
- **I031 ↔ #407 unification** (`i031_M_le_logTarget_of_constantIndexConjecture`, sorry=0): two independently-named open objects (the I031 union-bound and the #407 pointwise period bound) proven to deliver the *same* prize target through one chain.
- **The Paley-graph dictionary formalized** (`GeneralizedPaleyRamanujan`, `GaussPeriodMomentBound`): `M = λ₂(Cay(F_q,μ_n))`, prize ⟺ Ramanujan, with two axiom-clean conditional bridges.

**Exact closed forms / identities (never tabulated before for `μ_{2^μ}`):**
- **Char-0 energy ladder** `E₂ = 3n²−3n`, `E₃ = 15n³−45n²+40n`, … `E₉ = 34459425 n⁹`, extended to **E₃₃**, each leading `(2r−1)‼`, kernel-proven via Lam–Leung antipodal balance (`_AvL2_E*ClosedForm`, `_CharZeroWickEnergy.gaussianEnergyBound_dyadic` for *all* r).
- **Char-0 cumulants** `κ_{2r} = c_r·n` (κ₂=1, κ₄=−3, κ₆=40, κ₈=−1155, κ₁₀=57456), CGF `g(t) = ½ log I₀(2t)`; the char-0 period is the `n/2`-fold arcsine convolution ⟹ exact `Sh_char0 = √2`.
- **MGF = lattice theta** (verified to 1e−11): `Φ(s) = (p/(p−1))Θ_{L_p}(s) − e^{ns}/(p−1)`, `L_p = ker(ℤ^n → F_p)` rank-n covolume-p; `λ₁(L_p)² = 2`, kissing number `= n`.
- **Subgroup-sum spectrum structure**: `|μ_n| ∣ |spectrum_r \ {0}|`, peak `(3^m+1)/2` at center, total mass `3^{m−1}(m+3)`, even nonzero card at `r=n/2`.
- **Over-determined far-line incidence** `OverdetIncidenceMaxClosedForm = 2m³−2m²+1 = Θ(n³)` (p-independent census), and the crossing law `D = z + S·O` (`OrbitCountCrossingLaw`).
- **Tower RG exact rate** `Q₂(N) = 1 + 1/(2(N−1))`; free-probability constant; entire-type / crest-factor face `M = type(Φ) = (1/m)‖DFT(G)‖_∞`.

**The invented "no-name" tools (genuinely new instruments):**
- **The Jacobi / recurrence-coefficient tool (form D).** `M = top eigenvalue of the Jacobi matrix J of the empirical spectral measure μ_η`, **exactly** (closes the moment→sup conversion with no `L^{2r}` overshoot — the half-power loss). The recurrence coeffs follow `b_k² = nk` (Hermite) to a turnover depth `k*`, then fall; `M = 2 max_k b_k = √(2n k*)(1+o(1))`. **Wall ⟺ `k* = O(log p)`.** The `b_k` are a *bounded, sharper* invariant than `E_r` and they **discriminate the bad primes** that the bulk moments average out. (Honest caveat: Hankel/Toda routes `k*` back to depth-`2k* ≈ log p` moments — it *relocates*, does not escape.)
- **The Shaw-value reframe** `Sh(n) := limsup_{p>n^4} M(μ_n,p)/√(n log(p/n))`; the entire prize ⟺ `Sh(n) = O(1)`, bracket `[√n, n]` raw / `[1.07, 1.49]` normalized.
- **The Wraparound Variance Law** (§7.3): the prize as an *arithmetic CLT* — three orthogonal routes (moment-at-log-depth / Gauss-phase-DFT / algebraic-norm-divisibility) collapse to one variance crux.
- **The modular lower floor `M ≥ √3·√n`** (`_AvFloor_MomentRatioLowerBound`, axiom-clean): `M²·A_r ≥ A_{r+1}` ∀r ⟹ `M ≥ √(2r+1)·√n` (saturates at the DC-crossover `r₀ ≈ 5`). A genuine new *lower* bound beyond the √n Parseval floor.

**Corrections to the record (honesty firsts):** the BCHKS-1.12 mis-statement caught and retracted (`|Σ_r|` grows ≫ budget ⟹ the old "prize ⟺ Conj 1.12 tight" was vacuous); the master-gap off-by-one fixed (`capacity − δ* = m*/n`); the "δ\* climbs to capacity" artifact traced to a `b<s` engine direction-cap; **a proof that numerics cannot decide the prize.**

---

## 6. Open angles, open directions, and unexplored mathematics (the live frontier)

> Everything below either (i) is the char-0 *face* of the wall (closed — do not re-grind), (ii) the genuine open wall (char-p transfer — the single core), or (iii) a reframing/lever shown to reduce to it. The one genuine off-BGK lever (§9) is listed separately. **The honest stance: closure needs external analytic NT.**

### 6.1 The single core (the wall) — char-p `A_r ≤ (2r−1)‼·n^r` at `r ≈ ln q`
Char-0 = closed for all r. The residual is the char-p excess `W_r ≤ slack_r` at deep r, with **no in-tree handle** — it *is* the BGK/Paley wall. In-tree forward motions: characterize the onset-threshold growth law; extend the E_r ladder (mechanical, char-0, prize-inert). A complete proof needs a genuinely new sum-product / effective-equidistribution / monodromy input.

### 6.2 The five kernel-equivalent incarnations (pick an attack surface)
1. **Bare BGK/Paley** `M ≤ C√(n log m)` — the only unprovable in-tree predicate.
2. **The √2-gate** — per-level `LevelRatioBound … √2` down the dyadic tower ⟹ prize; clean single-variable reduction; empirically false at large n (ratio→1 at upper levels) but kernel-exact as a reduction.
3. **Orbit-count wall** — `n·orbitCount(r) ≤ Wick(r)` uniformly over the worst prime at the saddle `r* ≈ log p`; dichotomy `OnsetSavesSaddle ∨ OrbitCountWall`; onset provably fails at prize scale ⟹ routed entirely through the orbit-wall.
4. **Turnover depth** — `k* ≤ log p` under the Jacobi-edge model `M² = 2nk*`; free ceiling only `k* ≤ (9/2)n`; gap `O(n) → O(log p)`.
5. **Signed deep cancellation** — `|Σ_{b≠0} η_b^{2k+1}|` controlled at depth `r ≈ log p`; thinness-essential `|·|`-leak but no quantitative route.

### 6.3 I031 dilation-quotient chaining (the strongest empirical non-BGK lead)
`M(n) ≤ C·E[sup|G_b|]` over the `(p−1)/n` dilation-orbit representatives — chaining on `F_p^×/μ_n` collapses metric entropy `log p → log(p/n)`. The orbit-reduction substrate is fully axiom-clean (`I031DilationOrbitReduction`). The DECIDER probe shows `M/√(n·log(p/n))` stable in `[1.15, 1.40]` and *slightly decreasing* at β=4 with no upward trend to n=256 — **the campaign's strongest single signal for a bounded constant.** *Next (concrete, under-explored):* attempt a Lamzouri-type union bound at depth over the collapsed `(p−1)/n` index set, and verify whether `log(p/n)` vs `log p` actually changes the achievable constant (i.e. is the entropy reduction *exploitable*, or only cosmetic?).

### 6.4 Conjecture 41 / determinantal Open-Set-Rank route (genuine non-BGK, refuted as a payoff)
Chai–Fan 2026/858 §7 publishes the dossier's determinantal lever: the worst-case list `M_true` has a codimension phase diagram (`c=1` saturating; **`c=2` exponential** `~0.66·1.36^n`, proven; `c≥3` deployment regime conjecturally **linear** `≤ ⌊(2D−1)/c⌋` — Conjecture 41). The reduction is to **full rank** of `A = [N_{E_i} | γ_i N_{E_i}]`; the only obstruction is the `(w+1)-clique` row-dependency. **Verdict (verified by exact-ℚ rank computation):** the clique dependency is **identically zero over every field** (rank `= D+c−1`, not a mod-p coincidence) — so there is **no `p₀`** and the "poly `p₀` ⟹ prize" narrative is a category error (conflates polynomial *degree* with integer *height*). The prize relocates to two orthogonal exponentially-resistant layers: (i) prove every persistent rank-deficient syndrome is *degenerate*, and/or (ii) bound the log-**height** of the all-nonzero-realizability resultant by poly(n) — where every proven in-tree height is exponential (`4^{φ(n)} = 2^n`). This is the **E2W4 residual replicated at codim c≥3, not discharged.** Substrate: `Conjecture41CliqueKernelStructure`, `_CoreA6deep`. *Bankable Lean target:* weld the char-0 "rank = D+c−1 over any field" fact to a headline to permanently kill the prize-favorable reading.

### 6.5 Effective-Chebotarev / Linnik good-prime count (`_AvW2`)
Prove a good prime exists where r-sums are distinct mod p (poly-many distinct λ); bad primes divide `Res(Φ_s, ΣX^i − ΣX^j)` (≤ `log₄ s` per pair). Weight-4 spurious collisions exist only at `p=17` (m=4) and Fermat `641` (m=5) — bad primes finite & small. Reduces to quantitative Linnik / effective Chebotarev (Lagarias–Odlyzko; the surviving `p≡1 mod 8` density-¼ class is the prize-prime class). **This is the same machinery as the §9 floor route and is the most concretely actionable.**

### 6.6 Distinct-γ union-count growth law (the reframed combinatorial core)
A generating-function / polynomial-method bound on the p-independent distinct-γ count `|⋃_R {γ_R}|`. Shallow-rung growth is super-linear (`oc₃ ~ n²/32`, `oc₄ ~ n³/512`); `deg(#bad_r) < r` for general r would give the decay. **The plateau-width law `w(n)` of the worst-direction cascade is the single most decision-relevant computation** (bounded `w` ⟹ `m* = O(log n)`), but it is **provably undecidable below n ≥ 256** (numerics cannot separate bounded-`m*` from `log₂n`). The `n=64` GPU `min_m D*(m)` via the orbit-count recursion is the decisive test (brute is GPU-infeasible).

### 6.7 Out-of-regime candidates worth a prize-regime re-test (§7 of the prior dossier)
Not refuted; hit a compute/scale ceiling or validated only out of regime. Re-test at thin prize `n=2^30`, `q=n^β`, multi-prime:
- Murphy–Rudnev–Shkredov `49/20` energy (1712.00410); OSV short-Weil curve-blend (2211.07739; floor `p^{3/7}`, but the *blend* untested); Liu–Zhou subgroup-restriction eigenvalue recursion up the dyadic tower; theta-FE for `x↦x²` (metaplectic self-similarity); FKMS bilinear-below-PV.
- **Wasserstein / Kowalski–Untrau (KU25, 2505.22059) effective equidistribution** — the W₁ extreme-value upgrade of the Gauss-period family law, untested in the thin regime (necessary not sufficient; the additive floor blocks the union over `m = 2^128`).
- **Thin-Sidon depth → sup-norm bootstrap** — every conversion gate ratio `M_thin/M_random` stays flat ~0.93–0.96 (β-invariant); a valid bootstrap must explain why MORE depth buys NO sup-norm saving.
- **Bilinear/dispersion `n^{2/3}` & `n^{3/4}` towers** — the only lane yielding a non-trivial unconditional exponent from a self-contained subgroup identity with no external sum-product input; stalls (per-level multiplicative loss).

### 6.8 Genuinely unexplored mathematics (no serious attempt yet)
- **Effective vertical Sato–Tate / Katz monodromy with a worst-case (not distributional) conclusion** — Katz gives qualitative equidistribution of Gauss-period families; the prize needs a *finite, effective, worst-case-uniform* version `max_k |û(k)| ≤ C√(m log m)`. No one has tried to make Katz's equidistribution effective *and* sup-norm at this conductor.
- **The Jacobi-matrix / discrete-Toda integrable-systems framing (form D)** as a genuine PDE/ODE attack on `k* = O(log p)` — treat the recurrence coefficients `b_k` as a Toda flow and bound the turnover via a Lax-pair / spectral-shift argument. The `b_k` discriminate bad primes; no integrable-systems machinery has been brought to bear.
- **The bad-prime resultant height as an Arakelov / equidistribution-of-small-points question** — bounding `log-height(Res)` by poly(n) is a height question; Bilu/Bombieri–Zannier equidistribution of conjugates is the natural-but-untried tool (current in-tree heights are all the crude `2^n`).
- **A direct attack on the off-BGK binder-floor obstruction (§9) via the least-prime-in-AP literature** (Xylouris' Linnik constant `≤ 5`, Heath-Brown) — this route can close a modeled floor-bad predicate only with a sub-prize least-prime input; exponent-5 Linnik is not enough, and the result would still need a universal stack-domination bridge to prove δ\*.

---

## 7. The synthesis essays (the conceptual scaffolding for a continuing agent)

### 7.1 The Shaw value & the four doors (`shaw-value-missing-mathematics-2026-06-18`)
Prize ⟺ `Sh(n) = O(1)`. Tested against 14 distant fields (prismatic cohomology, condensed math, free probability, o-minimality, Tannakian Galois …) — **zero survivors, no fifth door** (this is the Tetrachotomy of §4.2). The doors collapse: (i)/(ii)/(iv) are the *same* problem (symmetric-function = BGK; or √q-completion too big; or extreme-value = BGK), and the only genuinely non-reducing object is "a new evaluation of the monomial sum" = the open problem.

### 7.2 The Arithmetic Uncertainty Principle essay (`arithmetic-uncertainty-principle-essay-2026-06-19`)
A *true, new, illuminating* description of the wall's existence (§4.3), **not** a solution. "The sharpest possible explanation of why the wall is there."

### 7.3 The Wraparound Variance Law (`the-wraparound-variance-law-essay-2026-06-21`)
Split additive energy `E_r = E_r^∞ + W_r` (char-0 no-wraparound + genuinely-F_p coincidences). Then **prize ⟺ `W_r − E[W_r] = O^r((2r−1)‼·n^r)` uniformly to depth `r ≈ log p`** — an arithmetic CLT: the wraparound count concentrates at its DC mean `E[W_r] = n^{2r}/p (1+o(1))` with √-fluctuations. Three orthogonal routes (analytic moment-at-log-depth `_AvW0_BesselWickDomination` / harmonic Gauss-phase DFT / algebraic norm-divisibility) collapse to this one variance crux. The derived value is `Sh = √((1+K)e)`. **The cleanest possible statement of the wall — "there is nothing left to peel."**

### 7.4 The expert-facing open problem (`proximity-prize-open-problem-for-number-theorists-2026-06-21`)
The four equivalent forms: **(A)** Wick moment bound at log depth; **(B)** square-root cancellation of the Gauss-sum-phase DFT (effective worst-case vertical Sato–Tate); **(C)** the Wraparound Variance Law; **(D)** early turnover of the Jacobi-matrix recurrence (`k* = O(log p)`). The β=4 evidence: `Sh` over ~190 thin primes ∈ `[1.07, 1.49]`, plateaus at `√2`; worst-case (highest `v₂(p−1)`) at β=4 gives `Sh = 1.199, 1.214, 1.336, 1.389` (n=16,32,64,128) — all below √2, approaching from below; `Sh > √2` occurs only *below* β=4 (Fermat 65537 gives 1.614 at β=3.2 but 1.199 at β=4) ⟹ **any proof must use thinness `n ≤ p^{1/4}` load-bearingly.**

### 7.5 The iid-Gumbel backward derivation (`backward-derivation-from-empirics-Mn-is-iid-Gumbel-2026-06-17`)
`M(n)` tracks **the Gumbel max of `m = (q−1)/n` iid `N(0,n)` variables**: `M = √(2n·ln(q/n))(1+o(1))`, `C = √2`. The decisive ratio `M/(√n·a_m)` (exact Gumbel location `a_m`): `0.916, 0.986, 1.009, 1.073, 0.991, 1.018` for n=8…256 — within `[0.92,1.07]`, centered on 1.0, **no upward drift** (a half-power violation would blow this up). Steps 1 (Plancherel `E‖η‖²=n`), 3 (near-independence: flat covariance, Poisson level-spacing), 4 (Gaussian EVT) all proven; the **only missing step is the char-p per-period sub-Gaussian tail at the saddle** = the wall. Upper half formalized (`_BackwardDerivationPrizeBound`, axiom-clean): `prize_scale_bound_at_saddle` gives `M ≤ √(2e·|G|·⌈log q⌉)` conditional on the single Prop `DCEnergyBound`. Inverting measured M gives **K ≈ 0.21, STABLE across doublings** — char-0 is Gaussian to 3×10⁻⁶ at the prize saddle; the entire difficulty is the char-p wraparound transfer.

---

## 8. Dead / refuted ledger — do NOT re-attempt (grouped by *where* it failed)

> Full catalogue: `DISPROOF_LOG.md` (~1.6MB, technique clusters H1–L5 → fences F0–F12, conjecture corpus C05–C51, O### entries). Check it before re-trying anything.

**⛔ Reduces to the BGK/Paley sup-norm wall (real machinery, NOT a bypass):** Line-decoding / collinearity (ABF26 Thm 4.21) — same far-line incidence; BCHKS-1.12 `|Σ_r|≤budget` as the prize object (`|Σ_r|` grows ≫ budget, vacuous); crossCell dyadic-tower iteration (floors at `log₂M ~ log₂n` ⟹ trivial); even-moment/additive-energy face (thin `A_r` = neg-closed-random `A_r` exactly; thin LARGER); restriction/extension (Mockenhaupt–Tao); Gross–Koblitz / p-adic Γ_p / Newton-polygon (b-invariant unit phases); theta/AFE + de Finetti; circle method (minor arcs → L²); Elekes–Szabó / sum-product (√-lossy); polynomial method / slice-rank (`n^{0.92}`); hyper-Kloosterman/FKM (conductor `~n` too large); HOMDS/Schur-at-roots; random-RS capacity transfer (Schwartz–Zippel unavailable for explicit points); cosh-MGF/Bessel-saddle (caps `~1.03×` floor); per-coset descent (`−1∈μ_n` forces real = a SIGN not a phase); bilinear/cube/free-prob/RMT; tropical/BKK/Croot–Sisask/Rankin–Selberg; Carlitz/FF-RH/quantum-group; LP/SDP "third route"; **50-/72-/100-/140-/250-conjecture sweeps (0 survivors)**; theta/ideal-lattice (rank `φ(n)=n/2` ⟹ `exp(Θ(n/2))` weight count = the √n-deficit in lattice clothing); Delsarte/LP/Beurling–Selberg (`delsartelpnogo`, phase-blind ⟹ trivial); Stepanov **fully closed** (`61187fbe0`: `μ_n` is 0-dim univariate, Frobenius fixes `μ_n`, multiplicity saturates at `n`; Weil `√q ≥ n` at β≥2); even/odd & antipodal-tower descent (saving-neutral, telescopes to `μ_2`); completion-sum `Σ_j G_j` (= the open BGK content, phase-blind); OSV short-Weil (`p^{3/7} ≫ p^{1/4}`); band dichotomy (consecutive lacunary is *benign*, the witness must be GAPPED); 10 "new-math" relocations (Terwilliger op-norm `=M`, Bourgain–Gamburd amenable, Amice/Iwasawa b-independent, Kelley–Meka/PFR wrong direction, chaining metric-blind, …) ⟹ **`M(μ_n)` is INTRINSIC (framing-independent).**

**⛔ Reduces to Johnson / Plotkin proxy:** even/over-det far-line construction (`δ*_farline = ½+1/n → ½`, `m* = n/4−1` LINEAR; the over-det count is `Θ(n³) ≫ budget` and collapses to Johnson); Hab25 as a published bypass (reaches NOTHING past Johnson); antipodal-domination (RETRACTED, saturates AT Johnson); r=2 (L4) rung (`A₂` L4 ceiling `~n^{1.5}` overshoots); the "m\* sub-linear (3,5,8,12)" plateau dichotomy (real but the PROXY face, recursion-extrapolated not measured); complete-homogeneous floor (super-poly `multichoose s s ≥ 2^{s−1}` ⟹ Johnson-side crossing).

**❌ REFUTED-FALSE (machine countermodel):** odd/signed-moment thin-cancellation (`A_r = −32^r` through r=7); additive large sieve (RHS = 2× Parseval, wrong side); fewnomial/Khovanskii/Descartes on `I(n)`; reverse LD⟹MCA (thickness-invariant); "worst-case window list constant L=2" (that's the dilation-invariant-word list only); char-0 `δ* = (1−ρ)−log₂n/n` (true law `s*−k = n/4`); base-case+monotonicity proof of `A_r≤Wick` (n=64 KILLS it); CensusDomination via `K`; wf-D3 pinch (constant Θ(1) gap); shallow-band `#bad/census ~0.26` (budget-conflation); v₂(p−1)-gated 2-adic law; **`W_{r*}=0` target** (onset r₀=5, `W_8≈1.4e17`; right target `W_r ≤ slack_r`); raw `E_r ≤ (2r·n)^r` (false past DC crossover); martingale QV (Freedman/Azuma circular); Gumbel/EVT with a *fixed* K (tail unboundedly heavier than Rayleigh, 576× overshoot at n=64); small-ball/Littlewood–Offord/Halász (frequency-blind, `S_b=b·μ_n` dilation-invariant); bad-set Sidon lever (bad set = union of negation-closed cosets ⟹ has antipodal quad ⟹ non-Sidon); √q-completion resonator (`(m−1)²≤m ⟹ m≤2.62 < 4`, non-realizable); per-frequency localization (coherence ρ, half-mass H — both **thickness-invariant** ⟹ prize content is collective-only).

**⚠️ Finite-size artifact (decays in n):** thin Sidon `r_min` advantage (drops 11→8 at n=64); decoupling crossing-depth `c*` (O(1) constant in rate); deep-hole sup (saturates p-independent).

**🚫 Larp / vacuous:** classical DFT-uncertainty (Donoho–Stark `0.8n` above Johnson; Tao strong-UP needs n PRIME — Loukaki 2412.08600 *proves* it CANNOT hold at n=2^μ, explaining why the prize fixes 2^μ); N9 codim-2 cohomology (`|V_4|=48` p-independent constant); `_AntipodalPlotkinHalfCap`; the `_Close27_*` tautologies; `deltaStar_pin_mu6_dim4` (toy n=6).

---

## 9. The one genuinely off-BGK obstruction check — bad-prime localization

This is the **only** arithmetic obstruction-removal route the campaign found that does *not* itself ask for a thin-subgroup character-sum estimate (`bad-prime-localization-theorem-2026-06-19`, 15 sections, heavily revised — note its §7 Fermat mechanism is itself REFUTED). It does **not** by itself prove the prize: it controls one binder-family predicate, while the δ\* lower pin consumes the universal `WorstCaseIncidenceBounded` input over all stacks.

**Why it is genuinely off-BGK for the binder predicate.** Bad primes are divisors of a **FIXED, p-independent cyclotomic resultant** `N(Δ_A)` — a 0-dimensional / height question, **not** a √p character sum. The defect count is **flat in p** (392 at n=16 across a 704× range; 42632 at n=32), confirming 0-dimensionality. The polarity matters: this can remove a known lower-bound obstruction, but it is not an upper bound on the worst stack.

**The floor/ceiling split (the re-grounded characterization):**
- **FLOOR-bad = the single smallest prime ≡ 1 mod n.** n=16 → {17} (exhaustive Rust, 15.4M patterns: 193, 257, …, 929 all FALSE); n=32 adjacent → {97}. Mechanism: only at the tightest/smallest prime does `μ_n` pack densely enough to force the forbidden "7th-type" adjacent-agreement profile; for larger p, `μ_n` is sparse and the 6-type freeze holds. {97,193,257} are the least primes ≡ 1 mod 32/64/128 (Linnik P(2^μ)); at them `M/√(n log p)` is BENIGN (~0.51) ⟹ floor-bad, not ceiling-bad.
- **CEILING-bad = high-`v₂(p−1)` / Fermat primes** `2^{2^k}+1` — extreme `Sh`, but only 5 Fermat primes exist (finite, can't settle asymptotics).
- The n=32 defect core is a **fixed integer polynomial** `R^(32)(g) = g^16 − 196g^12 + 4486g^8 − 21700g^4 + 1 = S(g⁴)`, identical to the n=8 excess polynomial, disc `= 2^41·17²·257²`; root-count drops exactly at {17,257}.

**The cleanest possible binder-predicate closure (the actionable target).** *If* "floor-bad = {smallest prime ≡ 1 mod n}," and if the least prime `≡ 1 mod n` is below `n^4`, then every prize prime (`p ≈ n^4`) is GOOD for this explicit floor-bad predicate without a BGK character-sum estimate. The second input must be stated carefully: ordinary Linnik with exponent `5` is an `O(n^5)` theorem and does **not** imply `O(n^4)`. The usable in-tree arrow is the Thorner--Zaman supply interface: a prime in `[n^β,2n^β]` with `β ≤ 3` is below prize scale, and the analytic supply is carried as `TZPrimeSupply` / `ThornerZamanPNT`, not as a proved Lean theorem. **Proven at n=16 (exhaustive).** Remaining open: keep the n=32 floor-bad predicate reproducible and prove the characterization **uniform in `μ`**. The missing consumer is a new domination theorem from this binder predicate to `WorstCaseIncidenceBounded`; absent that, §16 says the prize core remains on the BGK/Paley wall.

**The obstruction to be careful of (the conjugate-count no-go).** Bad prime ⟺ `p ∣ N(β) = ∏_σ σ(β)`, a product over `φ(n) = n/2` Galois conjugates. Support `C` bounds terms *inside* each factor but **not the number of factors** ⟹ `|N(β)| ≤ (2r)^{n/2}`, exponential in n, **independent of support/sparsity**. So no support / sparsity / height / Newton-polygon / decoupling argument can close the char-sum transfer — only inter-conjugate *phase* cancellation (= BGK). The floor route survives this only because it asks a *divisibility/existence* question (is there a small good prime?), not a *cancellation* question.

---

## 10. Numerical evidence (and the proof that numerics cannot decide it)

**The wall constant `C = M/√(n·log(p/n))` at β=4** (worst-case across primes; `M(n)=max_{b≠0}‖η_b‖`, smallest `p≡1 mod n`, `p≥n⁴`):

| n | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 |
|---|---|---|---|---|---|---|---|---|
| C (worst) | 1.07 | 1.21 | 1.31 | **1.49** | 1.42 | 1.39 | — | — |
| C (single-prime) | 1.07 | 1.20 | 1.26 | 1.36 | 1.28 | 1.32 | 1.28 | 1.33 |

Non-monotonic, mean ≈ 1.285, **no upward drift across eight octaves**, hugging `√2 ≈ 1.414`; `M < √(2n ln q)` throughout; doubling ratio decays toward `√2`. **Mildly favorable to a bounded `C` (floor TRUE)** — but oscillating points cannot rule out an `n^{−o(1)}`-slow divergence.

**`K_eff = (E_r/Wick)^{1/r}`** (DC-subtracted, at optimal depth, β=4): peak ≈ 0.60–0.67, **flat** across n=32→256; structured (hi-v₂) primes **not worse**; `K_eff^{NP} ≤ 1` to n=1024; `K_inf` fitted to 1. (The full-energy K diverges — that's the DC-crossover, why DC-subtraction is mandatory.) The LIVE tension: one early measurement found `K_eff` *creeping* `0.608→0.625→0.675` (n=32→128), prize-threatening if it crosses; the n=256 measurement found it *saturating* ≈ 0.67. **This is the decisive compute-bound question** and it sits exactly at feasibility's edge (n=256).

**GPU worst-case list** (n=64, ρ=1/8; Johnson δ=0.646, capacity δ=0.875): **L=0 across the window interior δ∈[0.64,0.80]; L≤35 (bounded) at δ=0.81–0.83; explodes 6459→6643 only within ~0.03 of capacity (δ≥0.844).** ⟹ **floor SUPPORTED at the n=64 octave** — worst-case list bounded deep in the window interior, exploding only near capacity, exactly the floor structure. (1×H200 ran it; ρ=1/4 and n=128 need 8-GPU parallelism, infeasible on 1 GPU — not reported, no fabricated data.)

**iid-Gumbel ratio** `M/(√n·a_m)`: `0.916, 0.986, 1.009, 1.073, 0.991, 1.018` (n=8…256), centered on 1.0, no drift (§7.5).

**Why numerics cannot decide it.** The wall lives at depth `r ≈ log m ≈ 89` and prize scale `n = 2^30`; all exact probing is confined to `r ≤ 6` at sub-prize primes and `n ≤ 256`. The distinct-γ growth law is **provably undecidable below n ≥ 256** (bounded-`m*` and `log₂n` are numerically indistinguishable there). The data is consistent with **both** prize-true and BGK-tight. **A closure needs a proof, and the proof needs external analytic NT.**

---

## 11. The substrate and how to continue (everything a fresh agent needs)

### 11.1 Start here
- **`PROXIMITY_PRIZE_WORKBENCH.lean`** — the single self-contained "write your solution here" file: the exact non-degenerate target, the prize regime, the imported+`#check`-verified proven substrate, the proven walls, the closure contract, and a `▼ YOUR CONJECTURE HERE ▼` slot.
- **`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`** (auto-loaded in that cone; `AGENTS.md` is a copy) — the build recipe, the #334 ledger, the four faces, references, the honesty contract, pitfalls.
- **`docs/wiki/residual-census.md`** — the named-residual census (read before treating any `*Residual` as proof debt; the `(P2-Slack)` residual is the genuine BGK char-p wall).

### 11.2 Build (mandatory — or you clog the 16-core box)
- The cone is **808+ files**; `lake build` traces a 3000+-job graph (~2–3 min even no-op) and takes the build lock (serializes all agents). **NEVER bare `lake build`.**
- Warm once: `scripts/pg-warm.sh` (pre-builds the substrate oleans).
- Iterate per-attempt: `scripts/pg-iterate.sh <file>` (= `lake env lean`, ~30–75s, **no lock → parallel**). It treats `sorry` as a WARNING and runs an axiom audit (bails on `sorryAx`) — **always read `#print axioms` for the specific declaration.**
- ⚠️ **`lake env lean` runs `autoImplicit=true`; the project build is `autoImplicit=false`.** Declare every binder explicitly; do one real `./scripts/lake-locked.sh build <module>` before landing.
- Push to remote `fork`, branch `main` (origin is 403). Race-deletions are real — keep a `/tmp` copy, locate declarations by **theorem name** (`grep -rln 'theorem <name>'`), never assume a path is stable.

### 11.3 The actionable open targets (Frontier scaffolds)
- **B3 — s=128 Thorner–Zaman ceiling** (largely dischargeable). Named hypothesis `KKH26ThornerZaman.TZPrimeSupply` (counting half proven); consumer `kkh26_mcaDeltaStar_le_of_TZ` proven; concrete per-modulus discharges `tzPrimeSupply_{8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768}_*` landed axiom-clean in `ThornerZamanInstance.lean`. Remaining open: the general [TZ24] effective density (analytic NT only), carried as `ThornerZamanPNT`.
- **B2 — curve decodability** ([GG25] Def 3.1 → [Jo26] half). Scaffold `CurveDecodability.lean`; real bricks `GG25Curve*`, `Hab25Curve*`, `Jo26Curve*`. Read the #334 thread before duplicating.
- **A5 — equivariance pin** (DISCHARGED). Engine `MCAEquivariance.lean` + the stronger diagonal-twisted `MCAMonomialEquivariance.lean`.
- **Best fresh entry points:** s=128 TZ general bound · B2 curve bricks · sharpening any A3/KKH26 threshold constant. The δ\* core and B4 (LD⇒MCA collapse) are **blocked-on-literature** — touch only when a new paper moves a side of the window.

### 11.4 The core substrate API (import; do NOT re-derive)
- **Bracket engine:** `mcaDeltaStar`, `le_mcaDeltaStar_of_good`, `mcaDeltaStar_le_of_bad`, `unique_bad_gamma_common_witness` (the structural obstruction any lower bound must respect), `JohnsonListBound` (the only unconditional regime), `epsMCA_interleaved_eq` (interleaved transfer, B1).
- **Incidence / floor:** `OpenCoreConditionalPin.WorstCaseIncidenceBounded` + `worstCaseIncidence_pin`; `epsMCA_ge_far_incidence` (`FarCosetExplosion`); `GaussPeriodParsevalFloor` / `ParsevalFloorSqrtN` (the √n floor).
- **Energy ladder + DC trio:** the `E2..E33` closed forms (`_AvL2_E*ClosedForm`), `_CharZeroWickEnergy.gaussianEnergyBound_dyadic` (all-r char-0 Wick), `MetaTheoremSecondOrderCap` (the second-order cap), `DCEnergyBound` / `DCSubtractedMoment.sum_nonzero_moment` / `DCEnergyEssential.not_gaussianEnergyBound_of_deep`.
- **Char-0 / Lam–Leung:** `ConverseLamLeung2Power` (antipodal-vanishing law), `LamLeungTwoPower`, `_AvL_T3ClosedForm`.
- **Gauss sums / Paley:** `SubgroupGaussSum{SecondMoment,WorstCase,MomentBound}`, `GeneralizedPaleyRamanujan`, `GaussPeriodMomentBound`.
- **KKH26 ceiling + over-det:** `kkh26_mcaDeltaStar_le(_of_not_dvd)`, `kkh26_mcaDeltaStar_le_of_TZ`, `card_bigPrimeFactors_le`, `OverdetIncidenceMaxClosedForm`, `OrbitCountCrossingLaw`.
- **Reduction skeletons:** `_BchksF3_RetargetedReduction` (`prize_reduces_to_SumsetExtremality`), `_BchksF6_ExplicitDeltaStarLower`, `_MomentLadderExceedsPrize`, `_EnergyRatioMonotoneReduction`, `I031DilationOrbitReduction`, `_EVTFloorRoute`, `_BackwardDerivationPrizeBound`.

### 11.5 File-naming convention (Frontier/)
`_` prefix = scratch/in-flight (gitignored until promoted). `_Av*` = "Avenue" attack routes (second token = math-domain cluster letter: A analytic/algebraic, C count/orbit, L2 energy-ladder, W, …). `_wf*` = "workflow" lane outputs (trailing token cross-refs a face). `_A##` / `A##*` = Class-A δ\* sub-targets (#334 ledger). `B#` = Class-B known-result residuals. `_Attack*` = adversarial probes (often end `NoGo`). `Sweep_A4#_*` = systematic sweep series. `*NoGo` / `*Refutation` / `*REFUTED` / `*Vacuous` = certified dead routes (do not redo). `O###` = DISPROOF_LOG entry IDs (not filenames). Cone-level: `KKH26*`/`GG25*`/`Jo26*`/`Hab25*`/`BCIKS20/*`/`ABF26*` group by source paper; `MCA*` = the core.

### 11.6 References
| tag | ePrint | what |
|-----|--------|------|
| [ABF26] | 2026/680 | the Proximity Prize paper; §4.5 `mcaConjecture`, §5 LD⇒MCA, Thm 4.17 |
| [KKH26] | 2026/782 | the explicit bad-line ceiling; prime threshold, η=Θ(1/log n) |
| [Jo26]  | 2026/891 | Thm 4.2 general-generator factor; curve-decodability half |
| [GG25]  | 2025/2054 | Def 3.1 curve decodability (B2 from scratch) |
| Chai–Fan | 2026/858 | FRI soundness above Johnson via threshold-halving (resolves *protocol* soundness at 2× query, **sidesteps δ\***); §7 = Conjecture 41 |
| | 2025/2046, 2025/2010 | up-to-capacity disproof (the ceiling) |
| External NT | — | BGK (CRMA 2006), di Benedetto et al. (2003.06165), Kowalski (2401.04756), Heath-Brown–Konyagin, Shkredov/Hart (1303.2729), Liu–Zhou (1809.09829), Podestá–Videla (2310.15378), Kim–Yip–Yoo (2309.09124, Paley Graph Conj 2.12), Kunisky (2303.16475) — all in `docs/references/proximity-gap-paley-spectrum/` |

### 11.7 The split goal (don't conflate)
- **(A) Protocol soundness above Johnson = RESOLVED unconditionally** (Chai–Fan 2026/858, threshold-halving, ~2× query cost; analyzes at δ/2 below Johnson where BCIKS 2025 proves the gap unconditionally). It explicitly **"does not claim the original zero-loss proximity gap."**
- **(B) δ\* / the zero-loss correlated-agreement / MCA proximity gap = STILL OPEN = this dossier's mission = the BGK/Paley wall.** A "prize pinned unconditionally" reading of 2026/858 conflates (A) with (B).

---

## 12. Honesty audit — phantom bricks, retractions, what NOT to cite

The campaign maintained a strict honesty contract; the following were caught and must not be consumed as landed (all verified absent / corrected):

**Phantom bricks (cited as landed axiom-clean but ABSENT on every branch):** `_DstarGrowthLaw` (`dStar3_gt_budget`), `_OPSingleOrbit`, `_DyadicRecursionDstar`, `PrizeEquivalencePin`, `FloorResonanceEnergyBridge` (the ON-BGK verdict's brick names — the *conclusion* stands on the VERIFIED bricks `_MomentLadderExceedsPrize`/`_EnergyRatioMonotoneReduction`/`KambireDeepBandFloor`/`OverdetIncidenceMaxClosedForm` + standing numerics, but these specific names were not landed); `prize_of_transfer_slack`, `CharPEnergyTransferWithSlack`, `_wfS1_transfer_slack_prize`, and the **S6 bounded-Betti Deligne brick** (the latter **refuted on the math**: the `μ_n`-subgroup trap makes `V_r` 0-dimensional / the bridge to the energy is the `m`-character sum = the wall); `_DefectOnsetOvershoot`, `SubsetSumThreePowExact` (re-created honestly as `_AttackDefectOnset_EnergySandwich` / `_AttackThreePow_SubsetSumExact` — the latter proves `3^{n/2}` is an UPPER bound, not exact); `EffectiveTZLowerBound`/`effectiveTZ_to_supply` (the real artifacts are `KKH26ThornerZaman.TZPrimeSupply` + `kkh26_mcaDeltaStar_le_of_TZ`).

**Retractions:** "δ\* climbs to capacity / m\*~log n" (engine `b<s` direction-cap artifact; far-line δ\* is Johnson-locked, `m*=n/4−1` LINEAR); "prize ⟺ BCHKS-1.12 (tight)" (vacuous, `|Σ_r|` grows ≫ budget); `_AntipodalPlotkinHalfCap` ("δ*≥½ cap" larp); the quadratic "plateau-floor failure mechanism"; "M→δ\* exponent-transfer bridge axiom-clean" (does not compile).

**Overclaims softened:** `LamLeungUnconditionalQ` proves the *structural foundation* (`linearIndependent_pow_le`), **not** the full Wick bound; `_Close27_*` "decides opposite horns" = `omega`/`decide` tautologies (prose-only); A6 "Lang–Weil tractability" → the valid object is a Bézout/degree ROOT-count (`V_r` is 0-dim ⟹ Lang–Weil VACUOUS — the bound stands, the point-count framing is the trap); `MomentRatioPeakAtTwo` self-refuted (peak at r=1); "W₄=0 at Fermat 65537" refuted (`E₄ = 4654160 ≠ generic 4649680 ⟹ W₄ = +4480`).

**The one forbidden move:** claiming `δ* = …` is *a theorem* with the open input silently discharged. The open core may live as a named `Prop` indefinitely; that is modularity, not incompleteness. **A refutation is a win; never call the core closed.**

---

## 13. Bottom line

The Ethereum RS Proximity Prize — pin δ\* in the window interior — has been reduced, **two-sidedly and axiom-cleanly, to a single open inequality**: the thin-subgroup BGK / Paley √-cancellation bound `M(μ_n) ≤ C·√(n·log(p/n))` at the Burgess barrier `β ≈ 4`, `n = 2^30`. This is a recognized ~25-year-open problem in analytic number theory; **no published technique crosses `n^{0.989} → n^{1/2}` for thin 2-power subgroups at β=4, and the campaign confirmed the missing analytic input does not exist in the literature.**

What the campaign achieved is decisive and rare: it **eliminated every elementary / second-order / off-BGK route as a theorem** (the Meta-Theorem, the Tetrachotomy, the Arithmetic Uncertainty Principle); built the full axiom-clean substrate (energy ladder to E₃₃, the Bessel char-0 face, the spectrum-structure / minor-degree / orbit bricks, the necessary-condition theorem, the tight two-sided reduction, the iid-Gumbel and Wraparound-Variance reframings, the invented Jacobi-turnover and Shaw-value instruments); corrected the record (BCHKS-vacuous; `capacity−δ*=m*/n`; the proxy artifact; the phantom bricks); and **proved that numerics cannot settle it.**

The evidence is **mildly favorable to the floor being TRUE** — `C ≈ 1.25` non-divergent across eight octaves, `K_eff → 1` from below, the GPU list bounded deep in the interior — so the most likely truth is that δ\* sits strictly inside the window. But "mildly favorable" is not a proof.

The single most useful under-explored arithmetic obstruction check is the **off-BGK binder floor via bad-prime localization** (§9): it can terminate at a least-prime-in-an-AP input rather than at a character-sum estimate, it is proven at n=16, and its closure hinges on a clean, checkable characterization ("floor-bad = the smallest prime ≡ 1 mod n," uniform in μ). It no longer counts as a prize route by itself: §16 corrects the polarity error. To prove δ\*, one still needs effective worst-case vertical Sato–Tate / BGK-Paley cancellation, a domination theorem from all stacks to the binder predicate, or another genuinely universal incidence mechanism.

**The prize is OPEN and ON-BGK.** Continue here.

---

## 14. Round log — AssaultV2 (2026-06-22, 12-lever multi-agent assault)

A maximal multi-agent assault (12 attack lanes, one per open lever; each adversarially verified by 2 independent skeptics; 37 agents) ran against every open lever. **Outcome: the wall was not cracked** (expected); **8 axiom-clean structural bricks banked** (real `lake build`, 3381 jobs, `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`), all `advancesPrize=false`; **4 lanes excluded** (vacuous/redundant/tautological). The off-BGK floor's advertised `n=32 = {97}` characterization was **not reproduced** in round 2 (a non-faithful reconstruction returned `∅`, and the *superseded* disc-polynomial object localizes to `{257}`) — **now RESOLVED in §15: the faithful exact §1 test confirms `n=32` floor-bad `= {97}`.** Banked bricks (all in `Frontier/_AssaultV2_*.lean`):
- `I031Chaining.i031_chaining_cosmetic` + `energy_eq_n_mul_transversal` — exact `Σ_{b≠0}‖η_b‖^{2r} = n·Σ_rep‖η_rep‖^{2r}`: the §6.3 dilation-quotient entropy reduction is **cosmetic** at the moment input (the `1/n` cancels under the outer `2r`-th root). Pins the strongest empirical non-BGK lead as a structure theorem.
- `Conj41Height.conj41_no_good_prime` + `degeneracy_escape_clause_false` — retires two prize-favorable Conjecture-41 readings (rank-over-ℚ good-prime existence; the degeneracy escape) over every field; the sole surviving lever is the exponential realizability **height** (§6.4).
- `JacobiToda.todaTurnover_not_determined_by_invariants` + `no_invariant_functional_for_edge` — cospectral toy `(5,0)/(3,4)`: identical Toda invariants `tr(J^k)`, different `max b_k` ⟹ **no isospectral functional recovers the turnover `k*`** (the form-D integrable-systems door is gauge, not a handle). μ_n-flow claim is numerics-only.
- `EffectiveSatoTate.effectiveKatz_vacuous_in_thin_regime` — proves `f ≥ √q ⟹ discrepancy D_f = f/√q ≥ 1` throughout the thin prize regime: **effective Katz/vertical-Sato–Tate is vacuous at β=4** (upgrades refuted conjecture C13 to a compiled vacuity). Monodromy dim is an asserted input, not derived from AG.
- `FloorResultantHeight.oddBad_iff_dvd_discS` + `discS_height_exceeds_64bits` — the §9 floor's 0-dim core: `disc(S) = 2^41·17²·257²` exact, root-count drop at the ramified `{17,257}`, height exponential (confirms the crude `2^n` is the obstruction).
- `FloorLocalizationN32.floor_localization_capstone` — n=16 binder-floor predicate closes (`floorBad16 = {17}`, `17 < 16^4`, by `decide`); the uniform-in-μ characterization carried as a named open Prop.
- `OnsetGrowthLaw.onset_growth_polynomial` + `charZeroEnergyLeadingCoeff_ten = 654729075` — the char-p onset threshold `(2r)^{n/2}` is polynomial-in-`r` of degree `φ(n)`; energy ladder leading coeff extended to E₁₀ (`= 19‼`).
- `CrossFormBridge.dcEnergyBound_iff_signedDeepCancellation` — new in-tree `↔` between the DC-subtracted energy form and the signed-deep-cancellation form (sharing the exact constant `q·Wick`).

**Excluded (not banked):** `FloorLeastPrimeAP` (the GRH/TZ reduction compiles but is a label-laundered transitivity shell with **zero** prize-object content — the §9 characterization that carries it is absent from the Lean); `WraparoundVariance` (trivial abstract-real `ring` restatement); `DisproofHunt` (the lower-bound rung is a redundant `r=4` specialization of the in-tree `energy_moment_floor_general`; its value is the *numeric* finding — **no C-divergence across ~900 primes to n=256**, positive floor evidence); `NewTool` (the dilation dynamical-zeta is b-blind / tautological headline — the only b-sensitive zeta is the moment ladder = door iv). **The core remains OPEN and ON-BGK.** Full per-lever verdicts: the assault comment on this issue.

## 15. Round log — AssaultV3 + the n=32 floor RESOLUTION (2026-06-22)

**(A) The n=32 floor contradiction is RESOLVED (the §9 / §14 open question).** I re-derived the *exact* §1 realizability test — `p ∈ B(n)` iff some adjacent 7th-type pattern `A` is realizable over `F_p`, i.e. `rank[M_A] = rank[M_A | b_A]`, `M_A = [x^0..x^{n/2-1} | −x^{n/2}]_{x∈A}`, `b_A = x^{3n/4}`, `A` ranging over the adjacent agreement profile (for n=32: `28·28·70·70·4 = 15,366,400` patterns, matching the KB's "15.4M Rust scan") — and implemented it exactly (`scripts/probes/floor_scan_exact.c`, validated: it reproduces the n=16 ground truth **exactly**, `p=17 → 160/2304 BAD`, `{97,113,193,241,257,3889} → 0/2304 good`). Running it at **n=32**:
- **`p = 97` → BAD** (smallest prime ≡ 1 mod 32; ≥1 adjacent pattern realizable).
- **`p = 193` → GOOD**, **`p = 257` → GOOD** (each: 0 of 15,366,400 patterns realizable, *fully scanned*).

⟹ **n=32 floor-bad = `{97}`** — exactly the smallest prime ≡ 1 mod 32, matching the n=16 pattern (`{17}`). This **confirms the §12 `{97}` characterization** and **refutes** both the round-2 `{257}` reading (that was the *superseded §11 disc-polynomial* object — `257` is "ramified" there but **good** for the actual adjacent-realizability floor object) and the §9-L102 `{97,193,257,1153}` claim (`193`, `257` are good). The smallest-prime-≡1-mod-n characterization (`FloorLocalizationUniform`) now holds at **both** verified rungs `a = 4, 5`. The off-BGK floor's conditional closure (`smallest prime ≡ 1 mod n < n^4 ⟹ every prize prime good`) thus rests on: (1) the characterization uniform in `a` (verified `a=4,5`); (2) least-prime-≡1-mod-`2^a` `< (2^a)^4` — **unconditional via Linnik/Xylouris is only `n^{5.2}` (insufficient worst-case), GRH gives `n^{2+ε}` (sufficient), and the Thorner--Zaman powerful-modulus refinement was later confirmed at exponent `12/5+ε` (§16C), sufficient unconditionally for dyadic moduli**; (3) the floor-good ⟹ δ\*-interior arrow (still open and governed by the necessary-not-sufficient correction).

**(B) AssaultV3 (8 sharpened lanes, adversarially verified) banked nothing new and clean** — diminishing returns confirming the wall is thoroughly mapped. The verifiers (correctly, per the honesty contract) rejected every lane: 2 were **phantom** (files never written: `FloorClosureReal`, `BiluArakelov`), the rest **redundant** with already-banked round-1/2 content or carried **no prize-object substrate** (a tautological Conj-41 height headline; the adelic and Bogolyubov "fresh tools" both reduce to door (i)/(ii) and duplicate `_DoorIVGeomMeanBelowMax` / `WorstPeriodMomentAvgLower`; the cross-bridge and energy-ladder lanes were mostly verbatim dups, only E₁₁–E₁₃ leading-coeff rows `21‼/23‼/25‼` and a Paley↔worst-case ↔ being arguably new but not cleanly separable). **Fresh-tool verdicts (all REDUCES_TO_WALL):** Bilu/Arakelov & Schinzel–Zassenhaus give only a *lower* house bound (wrong direction, joins `discnogo`); the adelic product formula pins only the Norm `∏|η_c|` (symmetric/phase-blind, door i); quantitative Bogolyubov/Chang give only *size* bounds on the large spectrum (yield an M *lower* bound, door ii). **(C) Disproof extended to n=1024:** exact Gauss-period enumeration, worst `M/√(2n log p) = 0.655…0.837` (β=4, n=8…256) and `0.79–0.82` (β=3, n=512/1024, high-`v₂`) — **all < 1, no upward drift** (positive floor evidence, not a proof). High-`v₂` primes are worst at β=3 but benign at β=4.

**Net:** the genuinely-new outcome of this round is the **n=32 floor resolution** (the validated exact scanner + the `{97}` confirmation) and the extended no-divergence evidence; the Lean-brick lanes hit redundancy. **The core remains OPEN and ON-BGK.**

## 16. Round log — AssaultV4 + the decisive floor meta-verdict (2026-06-22)

**(A) ⚠️ KEY CORRECTION to §9 — the off-BGK floor is NECESSARY-NOT-SUFFICIENT, *not* a BGK bypass.** The dossier §9 framed the off-BGK floor as a route that "closes by a known theorem, genuinely off the BGK wall." A focused meta-analysis (resolving the long-standing §0/§2-vs-§9 tension) shows this is **over-optimistic**: closing the off-BGK floor removes only the *one binder-word family*, it does **not** pin δ\* in the window interior. The mechanism is a clean logical fact about the governing law:
- `ε_mca(C,δ) = ⨆_{u : stack} Pr_γ[mcaEvent…]` is a **supremum over all word stacks / all far directions** (`Errors.lean:231`).
- The δ\* lower pin (`OpenCoreConditionalPin.worstCaseIncidence_pin`) consumes `WorstCaseIncidenceBounded C δ B = ∀ u, #{γ : mcaEvent…} ≤ B` — an **upper bound on the worst stack** (`:100`).
- The off-BGK floor object (`FarCosetExplosion.epsMCA_ge_far_incidence`, `:87`) is only a **lower bound** (`≤ ε_mca`) for a **single** supplied far direction — the binder family `w_g = x^{3n/4} + g·x^{n/2}` (the monomial pair `(b=3n/4, b=n/2)`).

A lower bound on **one** summand of a sup can never upper-bound the sup. So the provable implication runs strictly **`δ*-pin ⟹ floor-good`** (if all directions are bounded, the binder direction is too), **never the reverse**. Floor-goodness is therefore a logical *consequence* of the prize bound — hence necessary, hence **provably incapable of supplying it on its own**. The missing quantity is named exactly: the worst-case far-line incidence over **all** monomial directions `(a,b)` = `M(μ_n) = max_{b≠0}‖Σ_{y∈μ_n}ψ(by)‖` = the open BGK/Paley sup-norm. **⟹ The off-BGK floor (§9) is a genuine *obstruction-removal* (it kills the binder family unconditionally under Linnik/GRH) but is NOT a path to the prize; the window-interior δ\* remains gated on the BGK wall.** (The Lean lanes for this were tautological packaging — recorded as a verdict, not committed bricks.)

**(B) n=32 floor resolution — COMPLETE.** The exact validated scanner (§15) finished: at n=32, **`97` BAD** and **six** primes GOOD by full 15,366,400-pattern scan (`193, 257, 353, 449, 577, 673`, each 0 realizable). So **floor-bad(32) = {97}** (the unique smallest prime ≡ 1 mod 32) is firmly established — the smallest-prime characterization holds at `a=4,5`.

**(C) The Thorner–Zaman exponent ladder — RESOLVED 2026-06-27 (sub-quartic CONFIRMED, exponent 12/5).** The off-BGK floor's conditional closure needs least prime `≡ 1 mod 2^a` `< (2^a)^4`. **GRH** gives `q^{2+ε}` ✓; unconditional Xylouris `q^{5.18}` and TZ **Cor 1.4** `q^{11.1}` (verbatim threshold, rounded `q^12`) both exceed 4. **The TZ §3 Iwaniec powerful-modulus refinement supplies the unconditional sub-quartic exponent** — flagged UNCONFIRMED, now confirmed from the verbatim paper (see `deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md`): Thm 1.1 has `θ = 7/12` when no Siegel zero `β₁` exists, and eq (1.8)'s coefficient `3/2 → 1` in that case, so with `h=x` the asymptotic PNT-in-AP count is valid for `x ≥ q^{12/5}`. For `q = 2^a` the squarefree part `d = 2` is **fixed**, so `β₁` is eliminated for all large `a` (§3.1 eq 3.1 + [15, Lem 6.2]) ⟹ **least prime `≡ 1 (mod 2^a) ≪_ε (2^a)^{12/5+ε} = (2^a)^{2.4+ε}`, unconditional and effective, no GRH.** `2.4 < 4` with margin ⟹ the off-BGK binder-floor obstruction-removal is now **unconditional** (was GRH-conditional). This does NOT change §16(A): floor-goodness is necessary-not-sufficient; the window-interior δ\* stays gated on the BGK wall.

**(D) Two untried analytic angles — both doors closed.** *Weil explicit formula:* controls one Dirichlet `L(s,χ)`'s zeros ⟹ only the per-character `√p` scale (vacuous on thin `μ_n`, since `√(p/n) ≫ 1`); the prize `√n` is the *cross-family* `√N` cancellation = the wall. *Large-sieve positive-proportion:* the average/positive-proportion relaxation (only `≤ q·ε*` bad `b`, not worst-case) **does lower the required moment depth** but still forces `E_r ≤ Wick` at depth `r ≈ log(1/ε*) = 128` — i.e. the same DC-subtracted energy bound at deep `r` = the wall. Neither escapes.

**Net (rounds 3–4):** the analytic wall and its tetrachotomy are **exhausted** — fresh lanes now yield findings/no-gos, not bricks (round-3: 0 clean; round-4: 0 to disk). The genuine outputs are the **n=32 floor resolution** and the **floor-is-necessary-not-sufficient meta-verdict** (which corrects §9). **The core `M(μ_n) ≤ C√(n·log(p/n))` at β≈4 remains OPEN and ON-BGK**, and the off-BGK floor — the campaign's one "different" route — is now understood to remove a single obstruction rather than bypass the wall.

<sub>🤖 Consolidated 2026-06-22 by Claude (Opus 4.8, 1M ctx) from proximityprize.org + ABF26 (ePrint 2026/680) + the full #444 thread (1,190 comments) and predecessors + the in-tree substrate + the external NT PDFs + the KB dossiers, with independent re-verification (definitions checked on disk, phantoms verified absent, results tagged by status). No fabricated closure; the core is carried as a named open `Prop`.</sub>
