# N7-free: the Gauss-sum-phase / Stickelberger DUAL of M(μ_n) — complete chain, explicit death (#466, 2026-07-02)

> **Lane:** N7-free (free-synthesis novel-math round). **Seed:** free choice — I picked the
> route no prior lane (N1 theta, N2 Weil-rep, N3 homogeneous, N5 SoS, N6 arith-dynamics) touched:
> the **dual** side. Instead of bounding the periods `η_b` directly (lattice / dynamics / moment
> side), pass to the `m = (p−1)/n` **Gauss sums** `g(χ)`, `χ ∈ H` (the order-`m` group of
> characters trivial on `μ_n`), via the exact finite-Fourier identity, and bring in the one
> genuinely new arithmetic lever the dual offers — **Stickelberger / Gross–Koblitz p-adic exact
> data** — as the structure that might beat the period-side moment wall.
>
> **Verdict up front (honest): SELF-REFUTED — REDUCES_TO_WALL, unitarily.** The chain is
> COMPLETE and dies at a single, precisely located step: the map `η ↔ g` is a **unitary DFT** on
> `Z/m`, `|g(χ)| = √p` is **flat**, so the entire content of `M(μ_n)` lives in the **arguments**
> `arg g(χ)`; the target is EVT-sharp square-root cancellation of the argument vector; and the
> only new lever the dual supplies over the period-side moments — the p-adic (Stickelberger)
> valuations of `g(χ)` — is **archimedean-phase-blind**. It fixes the magnitude at `√p` and gives
> the exact valuations, but says **nothing** about the complex argument, which is exactly the
> `√m` of phase information the AUP (dossier C6) says is missing. Controlling it is **unitarily
> equivalent to the original prize**. This is a genuinely NEW statement of the SAME hardness
> ("argument-of-Gauss-sum equidistribution over `H` at EVT strength") and a new standing filter.
>
> Probe: `scripts/probes/probe_466_novel_gauss_phase_dual.py` — identity + flat-magnitude verified
> to `1e−13`; random-phase model pins the load-bearing constant. Everything marked **[classical]**
> cites a proven theorem with hypotheses checked here; **[probe]** is machine-verified.

---

## 0. The objects (all verified)

Fix `n = 2^μ`, `p ≡ 1 (mod n)`, `μ_n ⊂ F_p^×` cyclic of order `n`, `m := (p−1)/n`, `e_p(t) =
e^{2πit/p}`. Target: `M(n,p) := max_{b≠0} |η_b| ≤ C·√(n·log(p/n))`, `η_b := Σ_{x∈μ_n} e_p(bx)`.

- **H** := characters `χ` of `F_p^×` with `χ|_{μ_n} = 1`. As the dual of `F_p^×/μ_n`, `|H| = m`
  and `H ≅ Z/m` cyclic. Orthogonality on the quotient: `Σ_{χ∈H} χ(x) = m·[x∈μ_n]`. **[classical]**
- **η_b depends only on the coset `b·μ_n`** ⇒ there are exactly `m` distinct periods.
  This is the PROVEN in-tree brick `GaussPeriodCosetReduction.eta_image_card_mul_le` (`#distinct·
  |μ_n| ≤ q−1`) [memory `arklib-407-gauss-period-house`]. **[probe: `distinct = m` at all cases]**

## 1. The dual identity (the whole lane in one line) [classical, exact]

> **(D)** For `b ≠ 0`:  `η_b = (1/m)·[ −1 + Σ_{χ∈H, χ≠1} \overline{χ}(b)·g(χ) ]`,
> where `g(χ) = Σ_{y∈F_p^×} χ(y) e_p(y)` is the Gauss sum.

*Proof.* `η_b = Σ_{x∈F_p^×}[x∈μ_n]e_p(bx) = (1/m)Σ_{χ∈H}Σ_x χ(x)e_p(bx)`; the inner sum is
`\overline{χ}(b)g(χ)` (substitute `y=bx`), and `g(χ_0)=−1`. ∎

**(D) is a finite Fourier transform on `Z/m ≅ H`:** the length-`m` vector `(η_b)_{cosets}` is the
inverse DFT of `(g(χ))_{χ∈H}` (with `g(χ_0)=−1`). **[probe: reconstruction error `≤ 1.3e−13`
across n=8,16,32.]** This is a **unitary** change of basis — no information is created or lost.

## 2. Flat magnitude (the crux geometry) [classical, exact]

`|g(χ)| = √p` for every `χ ≠ 1`; `g(χ_0) = −1`. **[probe: `max_{χ≠1}||g(χ)|−√p| ≤ 1.1e−12`.]**
So on the dual side the magnitude is **constant** — *all* of `η` is encoded in the **arguments**
`arg g(χ)`. Parseval across the `m` cosets: `Σ_b |η_b|² = (1/m)(1 + (m−1)p) = p − p/m + 1/m ≈ p`,
so `mean|η_b|² ≈ p/m = n·(1+o(1))`, `RMS = √n`. **[probe / classical]**

## 3. Galois: `M(n,p)` is the house of a degree-`m` algebraic integer [classical]

`Gal(Q(ζ_p)/Q) = (Z/p)^×` acts by `η_b ↦ η_{cb}`, transitively on the `m` cosets, so the periods
are one Galois orbit and `M(n,p) = house(η)` for a degree-`m` algebraic integer `η`. Always
`house ≥ RMS = √n`; the target is `house ≤ C√(n log m)`, i.e. house within a `√(log m)` factor of
the RMS floor.

## 4. The target restated on the dual [exact reduction]

Combining (D)+§2, the prize is **EVT-sharp square-root-with-log cancellation of a twisted
Gauss-sum sum**:
`M(n,p) = (1/m)·max_{b≠0} | Σ_{χ≠1} \overline{χ}(b) g(χ) − 1 |`,
with `m−1` summands each of modulus `√p = √(nm)`. Target `M ≈ √(n log m)` ⟺ the twisted sum has
magnitude `≈ m√(n log m)` for **every** `b` — i.e. the phase vector `Θ := (arg g(χ))_{χ≠1}`,
twisted by the root-of-unity characters `\overline{χ}(b)`, exhibits square-root cancellation
uniformly in `b`; `max_b` is then the **extreme value over `m` near-independent partial sums**.

- **Magnitude-only baseline (no phase cancellation):** triangle inequality gives
  `M ≤ (1/m)(1 + (m−1)√p) ≈ √p = n²`. Everything between `n²` and `√(n log m)` is pure phase
  cancellation.

## 5. The new lever the dual offers: Stickelberger / Gross–Koblitz [classical, and its limit]

The one thing the Gauss side has that the period-side moments do NOT is **exact p-adic data**:

- **Stickelberger's theorem:** the ideal `(g(χ))` in `Z[ζ_{p−1}, ζ_p]` factors over primes above
  `p` with valuations given explicitly by the Stickelberger element (Gauss sums of digits /
  fractional-part `L`-function). This determines `g(χ)` **up to a complex unit**.
- **Gross–Koblitz:** `g(χ)` p-adically as a product of `p`-adic Gamma values `Γ_p(·)`.

This is *strictly more* than the period power sums `Tr(η^k)` (= the moments `E_k`, capped at
Johnson by the Meta-Theorem). **But it is archimedean-phase-blind:** it pins the p-adic valuation
and fixes `|g(χ)| = √p` (§2), while the **complex argument** `arg g(χ)` is exactly the classical
*"argument of the Gauss sum"* problem — quadratic case = Gauss's sign (hard already); cubic case =
Kummer's conjecture, equidistribution proven only via Heath-Brown–Patterson **metaplectic / cubic
theta**, for fixed small order. There is no Stickelberger-type formula for `arg g(χ)`. **The p-adic
toolbox controls the magnitude analog and the valuation, never the archimedean phase §4 needs.**

## 6. THE DEATH — unitary equivalence + archimedean-blindness

`η ↔ g` is a unitary DFT (§1). `M(n,p)` is a **nonlinear functional of the phase vector `Θ`**.
Two facts collide:

- **(6a) All magnitude + valuation + moment data is phase-blind.** `|g|=√p` (§2), the
  Stickelberger valuations (§5), and every period power sum `Tr(η^k)` (= moments) are **invariant
  under a huge family of reassignments of `Θ`** — including the *lone-spike alignment* that makes
  one `|η_b| ≈ (m−1)√p/m ≈ √p = n²`. So this data does NOT determine the sup: it leaves a `√m`
  uncertainty. **This is the AUP (C6) made fully explicit on the dual:** the magnitude-only bound
  `√p = n²` and the target `√(n log m)` differ by exactly `√p / √(n log m) = √(m/log m) = √m /
  √(log m)` — the `√m` phase deficit, and it *is* the argument-of-Gauss-sum information.
- **(6b) Reaching the target = proving `Θ` is EVT-pseudorandom.** One must show the arguments of
  the structured family `{g(χ) : χ∈H}`, twisted by `\overline{χ}(b)`, equidistribute with
  discrepancy strong enough that the inverse-DFT sup obeys the extreme-value law. This is (i) NOT
  suppliable by the available structure — Stickelberger is archimedean-blind (6a); any *second-
  order* functional of `Θ` is Meta-Theorem-capped at Johnson/`√p`; asymptotic equidistribution
  (Katz vertical Sato–Tate for Gauss sums, `p→∞`, averaged) controls averages, not the sup — and
  (ii) **unitarily equivalent to the original prize** (the DFT is invertible), hence exactly as
  hard.

**Death located:** the dual relocates the wall to *"argument-of-Gauss-sum equidistribution over
the order-`m` subgroup `H`, at EVT-discrepancy strength."* It is a genuinely different-looking
open problem (multiplicative arguments of a structured Gauss-sum family vs additive cancellation
of periods) but provably the same hardness, and the only new lever (p-adic/Stickelberger) is
constitutionally blind to it. **REDUCES_TO_WALL.**

## 7. Probe — sharpening the load-bearing constant, and confirming no free lunch

**Random-phase model:** replace `arg g(χ)` by iid uniform, keeping `|g|=√p` **and** the exact
conjugate-pairing constraint `g(χ)g(\bar χ) = χ(−1)p` (so §2 and the reality structure hold), then
recompute `max_b|η_b|`. **[probe, 120 trials/case, n=8,16,32, m=3…15]:**

| model | `Mmax/√(n log m)` mean | range |
|---|---|---|
| TRUE periods | **1.21** | [1.04, 1.45] |
| random flat-magnitude phase | **1.22** | [1.07, 1.26] |

Interpretation: **(i)** the constant is `C ≈ 1.2–1.3` *if* the phases are pseudorandom — a sharpened
prediction consistent with the #407 prize-diagonal plateau `C ≈ 1.16–1.33`; the TRUE upper outlier
`1.45` is `p=257` (Fermat prime, `m=8` pure 2-power) = the known **#400 Fermat trap**, not a new
effect. **(ii)** — the death, quantitatively: the random-phase model uses **only** the magnitude
and pairing data (exactly what Stickelberger fixes) and **already sits at the target scale**. So
the true periods are *not distinguished* from generic flat-magnitude phase vectors by any
magnitude/valuation statistic. Only a genuine **phase-equidistribution theorem** separates the
target `√(n log m)` from the lone-spike `√p` — and that theorem is the wall (6b).

## 8. Constants at the prize point (n = 2^30, p = n^4 = 2^120, m = (p−1)/n ≈ 2^90, r* ≈ ln p ≈ 83)

| quantity | value |
|---|---|
| # Gauss sums = # periods = EVT samples `m` | `≈ 2^90` (`= 2^128` on the steeper `p≈n^{4.9}` diagonal) |
| each `|g(χ)|` | `√p = 2^60` (exact) |
| magnitude-only triangle bound | `≈ √p = n² = 2^60` |
| target `√(n·log(p/n))` (nat log, `log m ≈ 62.4`) | `≈ 2^15·7.9 ≈ 2^18.0` |
| **AUP phase deficit** = triangle / target = `√(m/log m)` | `≈ 2^45/2^2.98 = 2^42` |
| measured constant `C` (random-phase EVT) | `1.2–1.3`, `≤1.45` at Fermat traps |
| BGK unconditional, for comparison | `n^{1−δ} ≈ 2^{29} ≫ 2^18` (route does not accidentally reach) |

The AUP deficit `2^42 = √m/√(log m)` **is** the archimedean argument information of the `m`
Gauss sums — the precise `√m` the magnitude/valuation data cannot carry.

## 9. Honest self-assessment

- **Completeness:** every step is exact or classical with hypotheses checked here (orthogonality;
  Gauss `|g|=√p`; Galois transitivity on cosets — the PROVEN coset-count brick; Stickelberger /
  Gross–Koblitz; Parseval). No unproven bridge is load-bearing.
- **Weakest step — stated honestly:** §6b's *unitary equivalence* is airtight (DFT invertible), so
  the dual is **at least** as hard as the prize. The residual honesty question is whether the
  Gauss-argument equidistribution is *strictly* as hard or merely morally so. Answer: it is at
  least as hard, and **no literature theorem reaches it** — Katz's vertical Sato–Tate is
  asymptotic-in-`p` and averaged (not sup, not fixed `p`); Heath-Brown–Patterson is fixed small
  order via metaplectic theta (not a size-`2^90` subgroup family `H`); KU/Wasserstein decays as
  `q^{−1/(m−1)} ≈ 1` at `m=2^90` (vacuous, memory `arklib-407-gauss-period-house`). So the death is
  honest: no partial win, no accidental reach.
- **Filters respected:** b-sensitive (b enters via `\overline{χ}(b)`); genuinely L∞ (max over the
  `m` phase-partial-sums); NOT moments-on-`η` (it is the *dual* of the moments); NOT
  BGK-circular (it does not invoke a sum-product bound); NOT averaged-over-`p` (single fixed `p`);
  does NOT terminate in "moments + positivity" (it terminates by *locating* why positivity/p-adic
  data cannot help — the lone-spike is a valid flat-magnitude phase configuration, §6a). The N1
  weight-`n/2` automorphic filter is not triggered (no main-term proposal).
- **Verdict:** SELF-REFUTED, REDUCES_TO_WALL. CORE stays OPEN, ON-BGK.

## 10. What survives (bankable)

- **(S1) The dual identity (D)** as a clean, unitary DFT statement `η = IDFT_{Z/m}(g)`, with the
  in-tree coset-count brick supplying the `m`-point index set. Reusable framing for the whole
  Gauss-period cone.
- **(S2) The AUP made explicit and quantitative:** on the dual, the C6 `√m` deficit is literally
  `√p / √(n log m) = √(m/log m) = 2^42` at the prize point, and it equals the argument content of
  the `m` Gauss sums. This is the sharpest concrete realization of dossier C6 to date.
- **(S3) NEW standing filter — "the Gauss-sum dual is unitary and archimedean-blind":** *any*
  method whose only lever beyond the period-side moments is p-adic / Stickelberger / Gross–Koblitz
  / Jacobi-sum-integrality / Iwasawa-Stickelberger-ideal data is archimedean-phase-blind and
  cannot bound the house; the `√m` deficit is exactly the argument-of-Gauss-sum information, and
  controlling it is unitarily equivalent to the original sup. Pre-kills that whole family of future
  proposals in one stroke.
- **(S4) Sharpened constant `C ≈ 1.2–1.3`** (random-phase EVT), consistent with the #407
  prize-diagonal plateau; Fermat traps (`m` pure 2-power) push to `≤1.45` — a dual-side
  confirmation of the #400 Fermat-trap phenomenon.

## 11. ADJUDICATION (judge, 2026-07-02)

**Verdict: REDUCES_TO_WALL (unitarily). Dying step: Step 6.** Both refuters returned
`killed=true` at Step 6, mapping REDUCES_TO_WALL; the judge independently re-derived the load-
bearing steps and concurs. No step is CLOSED_FALSE; constants do not decide it (VACUOUS is not the
mechanism — the chain produces *no new bound at all*, it tautologically re-expresses the prize).

**Independent re-derivations (judge, not taken on trust):**
- **(D) from scratch.** `1_{μ_n}(y) = (1/m)Σ_{χ∈H}χ(y)` (`H` = dual of `F_p^×/μ_n`, `|H|=m`);
  `η_b = (1/m)Σ_{χ∈H}χ(b^{-1})g(χ)`, trivial term `−1`. Yields (D) **verbatim**. Exact.
- **Parseval.** `Σ_b|η_b|² = (1/m²)·m·[1+(m−1)p] ≈ p` ⇒ mean `n`, RMS `√n`. Exact.
- **AUP deficit.** `√p/√(n log m) = √(p/(n log m)) = √(m/log m)` since `p=nm`; at the prize point
  `= 2^60/2^18 = 2^42`. Exact.
- **In-tree brick.** `GaussPeriodCosetReduction.eta_mul_left` + `card_mul_eta_pow_le_sum_erase`
  read and confirmed axiom-clean (`#print axioms` in-file): `η` constant on `μ_n`-orbits ⇒ `m`
  distinct periods, one Galois orbit. Step 0 / Step 3 substrate is genuinely proven in-tree.
- **Stickelberger blindness.** Stickelberger pins the ideal `(g(χ))` (valuations) hence `|g|` up
  to a complex unit; `arg g(χ)` is the classical open "argument of the Gauss sum." Confirmed.

**Why REDUCES_TO_WALL and not SURVIVES_ROUND.** The only object that "survives" the chain is the
statement *"`arg g(χ)` over `H` equidistributes at EVT-discrepancy strength."* Because `η↔g` is an
**invertible** DFT, that statement is the prize **verbatim in dual coordinates** — not a new
refutable conjecture, the wall itself. A subtlety worth flagging (it does not rescue the lane):
the sup-norm is **not** unitarily invariant, so "unitary equivalence" is not literally "same
sup." The correct and airtight reading — which the note uses — is: (D) is an *exact identity*,
so `sup_b|η_b|` **is** `(1/m)sup_b|Σ\barχ(b)g(χ)−1|`; it is the same number, computed from the
same data, with the only free parameter the phase vector `Θ=arg g`. The dual therefore supplies
**zero** new constraint on `Θ` unless an external phase theorem is imported, and the only phase-
relevant import beyond period-side moments (Stickelberger/Gross–Koblitz) is archimedean-blind.
Hence: correct chain, lands on the core = REDUCES_TO_WALL. The precise walls hit, all four
correctly self-identified: (i) dossier **C6 / AUP** (`√m` magnitude-vs-phase deficit, here made
quantitative `= 2^42`); (ii) the machine-checked **lone-spike filter** (magnitude+moment+valuation
invariant under the one-spike phase reassignment); (iii) the **Meta-Theorem** cap for any 2nd-order
functional of `Θ`; (iv) the open core itself (`min≤avg` / "average prime is bad" kills the only
equidistribution literature — Katz vertical Sato–Tate is averaged/asymptotic, not the fixed-`p`
sup).

**Scale robustness (header inconsistency resolved).** The task header quotes both `p~n^4` and
`m~2^128`; these are inconsistent (`p=n^4 ⇒ m=(p−1)/n≈2^90`, not `2^128`). The death is robust to
either reading: at `m=2^90` the deficit is `√(m/log m)=2^42`; on the steeper `p≈n^{4.9}` diagonal
(`m=2^128`, `log m≈88.7`) it grows to `≈2^61` while the target stays `2^18` — a *larger* gap, same
kill. Neither refuter's arithmetic depended on the ambiguous value.

**Both refutations (recorded).**
- **REFUTER-A** — killed=true, Step 6, REDUCES_TO_WALL. Constants-lens audit: confirms Step 6 is
  the FIRST death (Steps 0–5 carry zero ineffective/tower/dimension constant); prize-point
  recompute `|g|=√p=2^60`, target `2^18`, deficit `2^42`; the `log m=62.4` factor is the union tax
  baked into the TARGET, not an extra method tax. Diagonal-robust (deficit `2^61` at `m=2^128`).
  Literature vacuity confirmed by constants (KU/Wasserstein `q^{−1/(m−1)}≈1`).
- **REFUTER-B** — killed=true, Step 6, load-bearing lever dead-on-arrival at Step 5. Secret-
  identity map: Step 1 = exchangeability/unitary-invertibility (invertible basis change cannot ease
  a sup); Step 2 = tetrachotomy(iii) flat/curvature-free geometry — *but* it cleverly SIDESTEPS
  tetrachotomy(i) 0-dim AG vacuity (`|g|=√p` is the honest 1-dim Weil bound for a genuine
  additive×multiplicative sum over all of `F_p^×`, not the vacuous `(m−1)√p`); Step 4 = prize
  restated; Step 5 = "size-only in the *non-archimedean* metric" (ord_p is a magnitude orthogonal
  to the archimedean magnitude the target needs) = the bounded-complexity/uncertainty kill in
  p-adic clothing; Step 6a = the lone-spike filter verbatim; Step 6b = Meta-Theorem cap +
  min≤avg for the equidistribution literature.

Judge concurs with both. The sole genuinely clever move (B's observation) — routing through the
**full**-`F_p^×` Gauss sum to escape the 0-dimensional-`μ_n` Weil vacuity — is real and is the
lane's one lasting contribution, but it buys **magnitude only** (`|g|=√p`) and reroutes straight
into the uncertainty kill: it converts the AG-vacuity wall into the AUP wall without lowering it.

**DISPROOF-ready paragraph.** *Claim:* the Gauss-sum / Stickelberger dual bounds
`M(μ_n)=max_{b≠0}|η_b|` by `C√(n log m)`. *Refutation:* the finite-Fourier identity
`η_b=(1/m)[−1+Σ_{χ≠1}\barχ(b)g(χ)]` (proved in §1, matched by the in-tree coset-count brick
`GaussPeriodCosetReduction.eta_mul_left`) is an **exact** transform of the length-`m` Gauss-sum
vector to the period vector; since `|g(χ)|=√p` is flat (Weil, §2), `M` is a function **only** of
the phase vector `Θ=(arg g(χ))`. The magnitude-only triangle bound is `√p=n^2`; the target
`√(n log m)=2^18` demands EVT-sharp cancellation of `Θ`, i.e. `√(m/log m)=2^42` bits of phase
information at the prize point. The one arithmetic lever the dual adds over period-side moments —
Stickelberger/Gross–Koblitz p-adic valuations — fixes the ideal `(g(χ))` and hence `|g|` up to a
unit but is provably blind to `arg g(χ)` (the classical open "argument of the Gauss sum"). All
magnitude+valuation+moment data is invariant under the lone-spike phase reassignment (machine-
checked lone-spike filter), so it cannot separate the target scale from `√p`. Bounding `Θ` at EVT
strength is the prize verbatim in dual coordinates. Therefore the route supplies no new bound:
REDUCES_TO_WALL, unitarily. CORE stays OPEN, ON-BGK.

**Bankable sub-results (judge-confirmed, none load-bearing to a live claim):**
- **(S1)** Dual identity `η = IDFT_{Z/m}(g)` — clean unitary framing, `m`-point index set from the
  in-tree coset brick. Judge re-derived (D) independently; exact.
- **(S2)** Dossier **C6/AUP made quantitative**: on the dual the deficit is literally
  `√p/√(n log m)=√(m/log m)=2^42` at the prize point (`2^61` on the steep diagonal), and it *is*
  the archimedean argument content of the `m` Gauss sums. Sharpest concrete C6 realization to date.
- **(S3)** **NEW standing filter (S3):** any method whose only lever beyond period-side moments is
  p-adic / Stickelberger / Gross–Koblitz / Jacobi-sum-integrality / Iwasawa-Stickelberger-ideal
  data is **archimedean-phase-blind and cannot bound the house**; controlling the `√m` deficit is
  unitarily equivalent to the original sup. Pre-kills that whole family (companion to the N1
  weight-`n/2` automorphic filter).
- **(S4)** Sharpened constant `C≈1.2–1.3` (random-phase EVT), consistent with the #407 prize-
  diagonal plateau; Fermat traps (`m` a pure 2-power, e.g. `p=257`) push to `≤1.45` — dual-side
  confirmation of the #400 Fermat-trap phenomenon.
- **(S5, judge)** `house(η) ≥ RMS = √n` with target `≤ C√(n log m)`: the entire prize is a
  `√(log m)` factor above the trivial RMS *lower* bound, while the trivial *upper* (triangle)
  bound is `√p=n^2` — locating the whole difficulty in the `[√n, √p]` phase-cancellation window.

<sub>🤖 Lane N7-free — proposer + REFUTER-A/B + judge adjudication, 2026-07-02. Probe:
`scripts/probes/probe_466_novel_gauss_phase_dual.py` (identity + flat-magnitude to 1e−13;
random-phase constant, 120 trials/case). Verdict REDUCES_TO_WALL (unitarily), dying at Step 6.
No Lean claims; nothing called "proven" beyond the cited classical theorems, the axiom-clean
in-tree coset brick, and machine-verified probe data. Not committed.</sub>
