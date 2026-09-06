# Prize "25 new theorems" fence-threading sweep — full catalog (2026-06-17)

**Lane:** synthesis (opus-4-8). **Issue:** lalalune/ArkLib#444 (Ethereum Proximity Prize; ePrint 2026/680).
**Object:** `M(n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n` the order-`n=2^μ` subgroup of `F_p^*`.
**Prize regime:** `n ~ 2^30`, `p = n^β ~ 2^120` (`β=4`), `p ≡ 1 mod n`. **Prize bound:** `M(n) ≤ C√(n log(p/n))`.

## Headline

A fresh batch of candidate ANT theorems was generated to *thread* the proven fence map **F0–F11** (each
candidate engineered so that exactly one fence has bite and the dodge is explicit), then each was attacked and
adversarially re-verified.

- **Generated/attacked: 24** (IDs `T01–T05`, `TT06–TT10`, `T11–T16`, `T18–T25`). **`T17` was never generated**
  — the G4 cluster list jumps from T16 to T18 — so the "25" framing is nominal; 24 real candidates exist on disk
  as `Frontier/_wfT*.lean`.
- **SURVIVORS: 0.**
- **REFUTED: 5** (`TT06`, `TT08`, `TT10`, `T22`, `T25`) — internally false at prize scale.
- **REDUCES-TO-WALL: 19** (the rest).

**Verdict: the conservation-law / no-escape terminal is REINFORCED, not cracked.** Running tally across this
batch plus the prior 84+ invented escapes: **0 survivors.**

## The fence map (kill mechanisms referenced below)

- **F0** Conservation law: any estimate whose only input is `μ_n`'s first/second-order arithmetic caps at
  Johnson `√n`; the `√log` excess is a rare-event/tail phenomenon invisible to 2nd moments.
- **F1** Moment/energy/cumulant conjugacy (incl. Legendre/Cramér duals).
- **F2** Weil/Deligne on the obvious config varieties (Betti vs `p^{r-1}` error).
- **F3** p-adic / valuation is archimedean-blind.
- **F5** Spectral gap / Bourgain–Gamburd: abelian torus ⇒ zero gap.
- **F6** Almost-periodicity / strong-`L^q` Croot–Sisask vacuous below `L²` at `β=4`.
- **F7** Rényi-2 entropy = additive energy.
- **F9** Supply-side counting (Chebotarev / per-prime norm certificate).
- **F10** Sheaf/FKM conductor floor (`cond ≥ rank = 2nd moment`).
- **F11** Object-change synonyms: every exact `δ*` quantity = the BGK conjugate-norm divisibility count.

## Design clusters

- **G1** parameter-space / sheaf-in-a-family / Deligne (where `n<√q` is irrelevant): `T01–T05`.
- **G2** adelic / joint archimedean × non-archimedean / heights / equidistribution-of-conjugates: `TT06–TT10`.
- **G3** information functionals OTHER than Rényi-2 (min-entropy, rate function, Rényi-α, Kolmogorov/MDL,
  conditional entropy): `T11–T15`.
- **G4** post-2020 additive combinatorics STRUCTURE/COVERING (Chang/Sanders/bilinear-Bogolyubov/PFR): `T16,T18–T20`.
- **G5** dynamical / operator-algebraic / determinantal / motivic-higher: `T21–T25`.

---

## Per-candidate catalog

Each row: title · cluster · final verdict · fence (or refutation reason) · Lean file.

### G1 — sheaf-in-a-family / Deligne

**T01 — Drop-locus partial-signal sub-sheaf (polylog-conductor object carrying only the worst-`b` excess).**
REDUCES-TO-WALL **F10** (via F0). Splitting the rank-`n` period sheaf into `F_avg ⊕ F_exc` is geometrically void
(Deligne purity ⇒ trivial weight filtration; tame ⇒ trivial break filtration) and arithmetically blocked: any
direct-sum split has `cond(F_exc) ≥ M2(t_exc)`, and Parseval pins `M2(η)=n`, so forcing polylog conductor starves
the excess. Worst-fiber excess `≈ 2^30·90` dwarfs any polylog budget. The sup is read off a rank-`n` (cond=`n`)
object. *File:* `_wfT01_drop_locus_subsheaf_conductor.lean` (axiom-clean).

**T02 — Drinfeld two-variable partial-Frobenius decoupling.** REDUCES-TO-WALL **F10** (sec. F2; meta F0). The
manufactured 2-variable family `T(b,t)=Σ ψ(bx+t·x^g)` has both partial-Frobenius factors on the SAME `n`-element
domain; the fiber product `{x=y ∧ x^g=y^g}` collapses to the `n`-point diagonal for ANY `φ`, so the 2-D rank = `n`
= the 1-D rank. Drinfeld decoupling buys exactly zero. Probe (β=4): avg`|T|²`=`n` exactly, no off-diagonal
shrinkage. *File:* `_wfT02_drinfeld_twovar_diagonal_collapse.lean` (axiom-clean).

**T03 — Gauss–Manin / Picard–Fuchs ODE-rigidity sup bound.** REDUCES-TO-WALL **F3** (sec. F0/F10). The only novel
size-source ("`log(p/n)` via the Dwork/Frobenius slope") is a p-adic Newton-polygon datum, archimedean-blind
(=A08/A09). The oscillation/Sturm count uses local exponents = `1/n`-spaced roots of unity (F0 domain arithmetic)
and `N=n+2` singular points (= rank+2 = conductor F10); the ceiling is `Θ(n)`, vacuous (bigger than even the
trivial `M≤n`). *File:* `_wfT03_gauss_manin_ode_rigidity.lean` (axiom-clean).

**T04 — Leptokurtic-corrected vertical Sato–Tate EVT + bounded exceptional fibers.** REDUCES-TO-WALL **F1**
(lever (ii) F2/F10). Strict refinement of the already-mapped C5/C13 monodromy-EVT route (NOT novel). Lever (i): the
moments of the exact limiting law `L_n` ARE the energy sequence `E_r`; EVT depth at the GROWING prize depth `~√(2
ln q)` is governed by the far-tail exponent `α≥2`, which IS verbatim the open `CumulantEnergyBound`; the
in-tree-proven kurtosis-3 leptokurtic shoulder forces `α<2`, making leptokurtic EVT strictly WORSE. Lever (ii):
`O(1)` Larsen exceptional-fiber count needs effective equidistribution to order `r~ln q`, where the convolution
sheaf conductor `~n^{2r-1}` makes Weil-II lossy by `n^{r-1/2}` = BGK wall. *File:*
`_wfT04_leptokurtic_evt_reduces.lean` (axiom-clean; novelty=false, absence=false).

**T05 — Primitive-cohomology sub-bound on the Veronese moment-curve dilation family.** REDUCES-TO-WALL **F2** (sec.
F1). The "primitive dimension" `dim_prim := C(2r,r) − (2r-1)‼` is MALFORMED at prize depth (`(2r-1)‼ > C(2r,r)`
for `r≥4`, so `dim_prim < 0` ⇒ truncates to 0; the prize needs `r~ln q≈83`). The Veronese moment curve FOLDS UP
over `μ_n` (`x↦x^j` sends `μ_n→μ_{n/gcd(j,n)}`), supplying no transversality / no per-class `p^{-1/2}` weight drop.
Probe (β=4): energy excess `W_r` is NEGATIVE and scales like `Θ(n^{r-1})`, not the claimed `O_r(1)`. *File:*
`_wfT05_veronese_primitive_reduction.lean` (axiom-clean).

### G2 — adelic / heights / equidistribution

**TT06 — Coupled product-formula House bound.** **REFUTED** (sign-reversed) + REDUCES-TO-WALL F3 (sec. F9/F11). For
the algebraic-integer lifted period `θ_b`, the product formula forces `Σ_{arch} log|wθ_b| = φ(n)·D(b) =
log|N(θ_b)| ≥ 0`: non-arch content `D(b)` and arch log-mass are EQUAL and move TOGETHER, so `D(b)>0` ⇒ `logHouse ≥
D(b)` (a LOWER lever), the OPPOSITE of the claimed budget decrease. Exact counterexample `θ=1+ζ_8`: `House=√(2+√2)
≈1.848 > exp(2D)=√2≈1.414`. *File:* `_wfTT06_coupled_productformula_house.lean` (axiom-clean).

**TT07 — Adelic capacity / transfinite-diameter ceiling on the conjugate set.** REDUCES-TO-WALL **F1** (sign-reversal
+ F3/F11). Transfinite diameter `cap(E_b) = |disc(Ψ_b)|^{1/d(d-1)}`; Fekete gives `House ≥ capacity` (LOWER bound,
reversed). `disc(Ψ_b)=p^{m-1}·f²` is class-field-FIXED (conductor-discriminant, verified exactly across 14
prize-type cases), so `cap` log-content `=(log p)/m → 0` at prize `m~2^90` (vacuous), the ceiling collapses to the
Parseval floor `√n`. *File:* `_wfTT07_adelic_capacity_house_ceiling.lean` (axiom-clean).

**TT08 — Arithmetic self-intersection (Arakelov) lower bound.** **REFUTED** + REDUCES-TO-WALL F3 (sec. F9/F11). The
Arakelov self-pairing `=0` IS the product formula; for the principal period section arch log-mass EQUALS non-arch
content (move together), so `logHouse ≥ content` — the candidate has `content` in the exponent with a MINUS sign.
β=4 counterexamples (n=8..128): true House `~5√n` ≫ ceiling `√n·exp(−content)~1.88` (shrinks); violation grows to
`~86000×` extrapolated at `n=2^30`. *File:* `_wfTT08_arakelov_self_intersection.lean` (axiom-clean).

**TT09 — Quantitative Bilu equidistribution + non-arch local-mass correction.** REDUCES-TO-WALL **F0** (sec. F1/F3).
A `W_p` equidistribution rate on the conjugate cloud CANNOT bound `House = max conjugate modulus`, because
sup-of-support is `W_p`-discontinuous: moving one atom of mass `1/φ` to radius `R` raises House by `R−R₀` but
contributes only `(R−R₀)·φ^{-1/2}` to `W₂`. The only route to a bound (`R_eq=√(log(p/n))`) is circular
(=the prize). Probe (β=4): House`/√n` grows 3.46→4.28 while bulk spread stays `O(1)`, tail mass `O(1)/φ ≪
W₂`-floor. *File:* `_wfTT09_adelic_equidist_house_nogo.lean` (axiom-clean).

**TT10 — Mahler/Lehmer lower bound UPPER-bounds the arch root.** **REFUTED** + REDUCES-TO-WALL F0/F1. Step (S1)
`House ≤ Mahler(Ψ_b)^{1/k_b}` is AM-GM REVERSED: `Mahler^{1/k_b}` = geometric mean of the `k_b` large conjugates
`≤ max = House` (lower bound only). β=4 probe: House 7.30/13.84/22.98 vs geom-mean 2.62/3.27/4.24 at `n=8/16/32`
(gap grows). *File:* `_wfTT10_mahler_lehmer_house_kb.lean` (axiom-clean).

### G3 — information functionals other than Rényi-2

**T11 — Level-set min-entropy (spectral `H_∞`) transfer.** REDUCES-TO-WALL **F7/F1** (+ F0 escape-clause). NOT novel /
NOT absent: the hypothesis `MinEntropyLevelSetDecay` is bit-for-bit the in-tree open `SubGaussianTailBound`; the
forward implication is the textbook sub-Gaussian-max union bound already in
`I031SubGaussianMaxBridge.subgaussian_max_le`. Uniform sub-Gaussian level-set decay to depth `√(2 log m)` is the
Legendre dual of `E_r≤(2r-1)‼ n^r` at `r~log m` = BGK wall. *File:* `_wfT11_min_entropy_levelset.lean`
(axiom-clean; novelty=false, absence=false).

**T12 — Spectral large-deviation rate function (strictly-convex Cramér rate).** REDUCES-TO-WALL **F0** (mech. F1/F10).
The rate `I(λ)=−log S(λ)/log m` is the convex Legendre conjugate of the CGF (= generating function of the
cumulants/energy). A rate LOWER bound `I(λ)≥aλ²` is IDENTICALLY the C5/T04 far-tail Weibull exponent `α≥2`
(machine-checked biconditional); the saddle threshold grows (`a·λ*²=β/(β-1)`), forcing rate-control at growing
depth `~log q` = deep-cumulant control = BGK. *File:* `_wfT12_spectral_rate_function_reduces.lean` (axiom-clean;
absence=false).

**T13 — Rényi-α smoothing / flatness factor at `α*=2+c/log m`.** REDUCES-TO-WALL **F7** (mech. F1). The spectral
flatness is `n·ε_α=(E_{α-1})^{1/(2(α-1))}` = the deep-moment ladder at depth `r=α-1`; at `α=2` it is literally the
additive energy. The super-critical offset `c/log m → 0` at prize scale (`m≈n³→∞` at β=4), so `α*→2` collapses onto
the F7 energy order. The interpolation `ε_∞≤ε_{α*}^θ` is a tautology (`θ` is a function of the unknown answer).
*File:* `_wfT13_renyi_flatness_reduces.lean` (axiom-clean; absence=false).

**T14 — Kolmogorov/MDL incompressibility of the worst-frequency witness (Kraft).** REDUCES-TO-WALL **F0** (≡F1). The
"engineered" count `#{b:‖η_b‖>λ√n} ≤ (p−1)/λ²` is bit-for-bit the Markov bound on the Parseval 2nd moment. Both
load-bearing premises are FALSE: (i) `‖η_b‖` is constant on `μ_n`-cosets ⇒ every level set is a coset union of size
a multiple of `n`, so the alignment map is `≥n`-to-1, never injective; (ii) the worst `b*` is named by its coset
rep (or as "the maximizer") in `O(log)` bits, the LEAST incompressible. Matches in-tree DISPROOF_LOG D9. *File:*
`_wfT14_kraft_mdl_witness.lean` (axiom-clean).

**T15 — Conditional-entropy chain rule along the 2-adic dilation tower.** REDUCES-TO-WALL **F0** (via F7). Three kills:
(a) Pinsker/Fano maps entropy gaps to average/TV quantities, never to a max over `m` points — bridging average→max
costs the union bound `log₂ m = √(log m)` the candidate set out to remove (its own conclusion still contains
`√(log m)`); (b) rare-event invisibility: the near-max set carrying `M` is `7/2e6` cosets, deleting it perturbs
Shannon entropy by `3.8e-5` bits; (c) per-step mutual information flat `~0.15` bits (levels nearly independent), so
the chain rule re-sums marginal entropies (F1/F7) and the doubling increment is phase-coherent (`cos~+1`, the BGK
cocycle). *File:* `_wfT15_tower_conditional_entropy.lean` (axiom-clean).

### G4 — post-2020 additive combinatorics structure/covering

**T16 — Frobenius-refined Chang cover of the `H`-invariant large spectrum.** REDUCES-TO-WALL **F1** (sec. F0). Chang's
dissociated-dimension bound `D0=C0 α^{-2} log(p/n)` = Rudin's inequality = a corollary of Khintchine = even-moment
object (F1); the candidate ADMITS `D0` recovers the BGK wall. The only novel lever (`1/μ` Frobenius collapse) is
empirically FALSE: `b↦b²` does NOT preserve `|η|` (`|η_{b*²}|/M→~0.05`), no Galois invariance to collapse
`{-1,0,1}`-relations. The balancing arithmetic is REVERSED: cardinality + Parseval gives `M² ≥ (p−n)/D ≥ n`
(Johnson RMS lower bound, GROWING as the cover shrinks). *File:* `_wfT16_chang_frobenius_cover.lean` (axiom-clean).

**T18 — Bilinear Bogolyubov codimension cover of the difference incidence.** REDUCES-TO-WALL **F0** (mech. F6/A12,
F1). (A) Structural non-applicability: bilinear Bogolyubov needs large ambient `F_p`-dimension; the prize ambient
`(F_p)²` over a PRIME field has dim fixed at 2, less than the demanded codim `O(log n)`. (B) Mass-vacuity: granting
the chain, surviving mass `p·n^{-c}` is empty at prize scale (`ln n·(4−ln n)<0` for `n>e^4`), the same `p·e^{-cL}<1`
floor as A12. Also flagged by the pre-existing DISPROOF_LOG "Bloom-Sisask/Bogolyubov-Ruzsa DEAD" (wrong direction:
`μ_n` is small-energy/large-doubling, the opposite of the Bogolyubov trigger regime). *File:*
`_wfT18_bilinear_bogolyubov_codim.lean` (axiom-clean).

**T19 — Additive-dimension / spectrum duality (Schoen–Shkredov anti-structure ⇒ sparse spectrum).**
REDUCES-TO-WALL **F1** (terminal F0). The dualization is forced through a Parseval/2nd-moment spectrum-COUNT
(`|Spec_α| ≤ p/α²`), which is `dim⁺`-FREE; a count bound cannot bound a sup (F0). The duality inequality is
QUANTITATIVELY FALSE at β=4: claimed RHS `~1.0–1.6` vs measured `|Spec_1.5|/n = 8.5,33,137,551` (off 1–2 orders,
growing like `Θ(p/n)`); `M/√n` GROWS (2.58→4.24) precisely WHILE `dim⁺=n/2` grows linearly. *File:*
`_wfT19_dim_spectrum_duality.lean` (axiom-clean).

**T20 — Galois-equivariant covering: `(μ_n ⋊ Frobenius)`-orbit count with 2-power floor.** REDUCES-TO-WALL **F0**
(terminal; sec. F11) + REFUTED-AT-MECHANISM. The advertised p-sensitive 2-power floor `2^{ν(p)}` with
`ν(p)=v₂(ord(p mod n))` is IDENTICALLY 1 in the prize regime: `μ_n ⊂ F_p^*` of order `n` forces `p≡1 mod n` ⇒
`ord(p mod n)=1` ⇒ `ν(p)=0`; `p` splits completely in `Q(ζ_n)`, decomposition group trivial, "Frobenius" on the
spectrum is the IDENTITY (`b^p=b`). The threshold `ν(p)≥log₂log(p/n)≈6` defines the EMPTY prime set. The genuine
W_r-orbit-parity lives on the relation tower, not the spectrum. *File:* `_wfT20_galois_spectrum_cover.lean`
(axiom-clean).

### G5 — dynamical / operator-algebraic / determinantal / motivic

**T21 — Reduced-crossed-product norm of the affine orbit-averaging projection.** REDUCES-TO-WALL **F5** (sec. F1/F11).
The only super-`√n` lever is `n·(1−1/Λ_cb^θ)^{1/2}`, positive iff `Λ_cb^θ>1`. But `μ_n=Z/n` is cyclic ⇒
`H²(Z/n,T)=0` ⇒ every 2-cocycle is a coboundary ⇒ the metaplectic cover splits, the finite-dim (nuclear) twisted
crossed product has `Λ_cb=1` (cb-norm=op-norm). Plugging `Λ_cb^θ=1` gives `M≤√n`, FALSE in regime (probe: `M/√n`
grows 2.58→5.09). *File:* `_wfT21_crossed_product_cb_collapse.lean` (axiom-clean).

**T22 — Determinantal repulsion of the Paley-eigenvalue process (hole-probability on the count).** **REFUTED** (at
spectrum level); surviving sup-deduction half REDUCES-TO-WALL F1. `Cay(F_p,μ_n)=Γ(k,p)` has `k=(p−1)/n` DISTINCT
periods EACH of multiplicity exactly `n` (Liu–Zhou Thm 115; Podestá–Videla 2604.06513), so `N(t)` is always a
multiple of `n`, `n`-fold atomic = maximally NON-simple — but a CD PROJECTION-kernel DPP is a.s. SIMPLE
(Hough–Krishnapur–Peres–Virág). The determinantal/log-rigidity hypothesis is FALSE by the algebraic spectrum. *File:*
`_wfT22_determinantal_count_rigidity.lean` (axiom-clean).

**T23 — Beilinson-regulator (dilogarithm) spacing of cyclotomic periods.** REDUCES-TO-WALL **F0** + load-bearing step
REFUTED. There are `m=(p−1)/n ~ n³ ~ 2^90` DISTINCT periods; Parseval crams them into an `O(√n)` window, so
pigeonhole FORCES a pair within `~O(n^{-5/2})~1.5e-22` at `n=2^30`, BELOW the claimed separation floor
`1/(√n·polylog)` by `~n²`. `n³` periods cannot all be `n^{-1/2}`-separated when their 2nd moment confines them. The
regulator→spacing bridge is the same reversed-covolume trap as TT10/S8 (`geomMean ≤ max`). *File:*
`_wfT23_beilinson_regulator_spacing.lean` (axiom-clean).

**T24 — Sarnak–Xue DENSITY (multiplicity-counting) of the affine Koopman operator.** REDUCES-TO-WALL **F1** (terminal
F0; F5/F11 via real spectrum). The affine Koopman matrix coefficient `⟨U_b ξ,ξ⟩=η_b` literally (periods real,
`max|Im η_b|≈1e-15`), so the "non-abelian principal series" supplies no eigenvalue not already in `{η_b}`. The
non-tempered count's only handle is the Markov level-set inequality `N(s)·n^{(1+2s)r} ≤ Σ|η_b|^{2r}=(p−1)n^r E_r` =
F1; the sharp closing form `N_t≤m·e^{-t²}` is REFUTED at β=4 (empirical tail constant `c_eff≈0.65–0.73<1`,
heavier-than-Gaussian = BGK content; `t_max=M/√n` VIOLATES `√(log m)`). *File:*
`_wfT24_affine_koopman_density_reduces.lean` (axiom-clean).

**T25 — Absolutely-continuous (Rajchman) spectral measure of the dilation Koopman flow.** **REFUTED** (root: finite-dim
⇒ pure-point ⇒ a.c. density vacuous); only well-posed surrogate REDUCES-TO-WALL F1. `ℓ²(F_p)` is finite-dim ⇒ the
Koopman unitary is diagonalizable with eigenvalues on the unit circle ⇒ spectral measure is a finite sum of Dirac
atoms, NO absolutely-continuous part — `ρ_max` does not exist. On `H_η` the coefficients `μ̂_V(k)≡1` ⇒ `δ_1`, the
MOST non-Rajchman measure. The Wiener `|μ̂|²` surrogate = Parseval energy `Σ|η_b|^{2r}` = F1. *File:*
`_wfT25_rajchman_density_pure_point.lean` (axiom-clean).

---

## Fence-threading map: which clusters got closest, which fences proved most absorptive

**Most-absorptive fences (primary attributions among the 19 reductions):**

| Fence | Primary count | Representative candidates |
|-------|---------------|---------------------------|
| F0 (conservation law) | 4 primary (+ meta under 6 more) | T09, T14, T18, T23 |
| F1 (moment/energy/cumulant) | 7 | T04, T07, T12, T13, T16, T19, T24 |
| F3 (p-adic blind) | 2 | T03, TT07 |
| F7 (Rényi-2 = energy) | 2 | T11, T13 |
| F10 (FKM conductor floor) | 2 | T01, T02 |
| F5 (abelian gap) | 2 | T20, T21 |

**F0 + F1 (and their faces F7/F10) together absorb the overwhelming majority.** This is structural, not
accidental: F1/F7/F10 are the *energy/conductor faces of F0*. The single most common terminal is the
char-`p` energy transfer `E_r ≤ (2r-1)‼·n^r` at depth `r ~ ln q` (char-0 PROVEN, char-`p` OPEN = the BGK/Paley
conjugate-norm wall, F11). Every Legendre-dual recoordinatization of the tail (rate function ↔ EVT depth ↔
min-entropy ↔ Rényi-α flatness ↔ moment ladder) lands there.

**Recurring kill mechanisms (cross-cluster):**

1. **Sign reversal of "ceiling → lower bound"** via the product formula on algebraic-integer periods:
   TT06 (product formula), TT08 (Arakelov), TT10 (Mahler/AM-GM), TT07 (Fekete/disc), T23 (regulator covolume) all
   share this. Heights/capacities/Mahler measures of an algebraic integer LOWER-bound the House; they cannot
   upper-bound the single largest conjugate (which carries `M`). G2 was the *least* productive cluster — 3 of its 5
   are outright REFUTED by this one mechanism.
2. **Diagonal / rank collapse** of every manufactured higher-dimensional family back onto the rank-`n` 2nd moment:
   T01 (sub-sheaf), T02 (Drinfeld 2-var), T05 (Veronese), T22 (determinantal). The "second variable" / "primitive
   part" / "drop-locus" contributes nothing to the rank.
3. **Legendre-dual recoordinatization of the tail** all carrying the SAME open char-`p` energy transfer:
   T04, T11, T12, T13, T15, T24 (G3 + EVT). The information-theoretic relabel is cosmetic.
4. **`p≡1 mod n` forces trivial decomposition-group Frobenius**, killing every "p-sensitive Galois/Frobenius
   2-power" lever: T20 (and reinforces the F5 collapse in T21).

**Closest any cluster got:** none crossed. G1/G5 produced the most *genuinely novel* objects (sub-sheaf split,
Drinfeld 2-var, crossed-product cb-norm, determinantal kernel, Rajchman measure) — all absent from literature and
codebase — but each collapses to a rank-`n`/2nd-moment object or is structurally false (finite-dim ⇒ pure-point;
cyclic ⇒ trivial Schur multiplier; `Γ(k,p)` spectrum ⇒ `n`-fold degenerate). The novelty is real; the
non-reduction is not.

## No-escape terminal: REINFORCED

Across this batch of 24 + the prior 84+ invented escapes the running tally is **0 survivors**. Every framing
attempted reads the prize sup `M(n)` as one of:
- (a) a rank-`n` / 2nd-moment object capped at Johnson `√n` (F0/F1/F10),
- (b) a p-blind valuation datum (F3),
- (c) a vacuous abelian/finite-group gap (F5),
- (d) an internally sign-reversed or structurally false construction (the 5 REFUTED).

The only honest residual *everywhere* is the char-`p` energy transfer at depth `r~ln q` = the irreducible 25-year
BGK/Paley conjugate-norm wall (F11). **No `#334`/`#444` closure; no crack.**

## Formal-cone state

- 24 axiom-clean `Frontier/_wfT*.lean` files (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`,
  no `sorryAx`), each recording its reduction/refutation as machine-checked lemmas.
- `ArkLib.lean` umbrella regenerated to import all 24 (plus merged sibling-lane files; +258 / +1 imports, 0 lost).
- Research/ProximityPrize/DISPROOF_LOG.md: consolidated `[T01-T25 ANT fence-threading sweep]` entry appended (union-merge).
- No claim of a proven `M(n) ≤ C√(n log)` at `n=2^30`. The char-0 case remains PROVEN; the char-`p` transfer
  remains OPEN.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>
