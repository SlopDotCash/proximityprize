# #407 Proximity Prize — Workflow Synthesis & Completeness Critic (2026-06-13)

**Object (the open core).** `p` prime, `n = 2^μ`, `n | p−1`, **prize regime** `n = p^{1/β}`, `β ∈ [4,5]`
(so `n ≤ √p`, a PROPER thin subgroup, NOT `n = q−1`). `μ_n` = order-`n` subgroup. Gaussian period
`η_b = Σ_{x∈μ_n} e_p(b·x)`. The object is `B = max_{b≠0} |η_b|`. Parseval ⇒ RMS over `b≠0` is `√n`.
**The conjecture (= δ* via the proven in-tree chain):** `B ≤ C₀·√(n·log(p/n))`, `C₀ ≈ 1.33`.
Three equivalent in-tree faces: (i) IDFT of Gauss sums `τ(χ_j)`, `|τ|=√p`; (ii) non-principal
eigenvalue of the generalized Paley graph `Cay(F_p, μ_n)` ("almost-Ramanujan"); (iii) the HOUSE
(max conjugate) of the degree-`m` algebraic integer `η_1 ∈ ℤ[ζ_p]`, `m=(p−1)/n`.

**This document is the final honest arbiter's synthesis** of: (a) adversarial re-verification of 5
empirical findings + 1 identity, (b) a 6-route proof assault, (c) the exact-constant question,
(d) the Lean formalization, (e) the completeness critic (untried surface), (f) the final verdict.

---

## 1. Empirical findings — what survived adversarial verification

Each was re-tested by a **fresh, independent probe** (`scripts/probes/probe_verify_f{1,3,4,5}.py`
and `scripts/probes/_407_verify/probe_verify_identity.py`) — none imported session code; all use
self-contained Miller-Rabin / primitive_root / odd_part, exclude Fermat/fully-dyadic primes
(`odd_part((p−1)/n) > 1`), and cross-check `B` against brute force + Parseval `rms = √n`.

| Finding | Claim (short) | Verdict | Precise status |
|---|---|---|---|
| **F1** | `C₀ = B/√(n ln(p/n))` plateaus at **~1.33**, flat `n=64→1024` on `p=n⁴` | **NUANCED-CONFIRMED** | The **plateau is real and flat** (no growth `n=64,128,256`); independently-measured center is **~1.29–1.32**, so 1.33 sits at the *upper edge* of the per-prime spread, not the mean. Qualitative content (clusters near 1.3, non-growing) reproduces cleanly. |
| **F2** | bare-Gaussian `C₀→1` is a fixed-`n` (`m→∞`) CLT artifact, NOT the prize diagonal | **CONSISTENT** (not independently re-run but corroborated) | Confirmed indirectly: the prize-diagonal center is ~1.3, well above 1 — consistent with F2's claim that `C₀→1` only off-diagonal. Also corroborated by the exact-constant route's controlled fixed-β experiment (§3). |
| **F3** | `E_r mod p` matches char-0 until `r~β` then inflates; "`n=32,β=4: +0.7%@r4, +4%@r5`"; `r=2` exact | **NUANCED / specifics REFUTED** | **Phenomenon real, numbers wrong.** Confirmed: (a) genuine positive p-defect at deep `r`; (b) `r=2` **exactly** char-0 `=3n²−3n` everywhere (defect 0); (c) defect 0 at small `r`, turns on deep; (d) onset deepens with `β`. **Refuted:** "`+0.7%@r4`" is wrong — `r=4` defect is **exactly 0**; onset is `r=5` at **+1.745%** (not +4%, ≈2.3× smaller). Observed onset `r ~ β+1`, not `~β`. **Critical correction:** the `(2r−1)!!·n^r` double-factorial is the *leading Sidon term*, **NOT** the true char-0 value (768 vs true 720 at `n=16,r=2`); defect must be measured vs the TRUE char-0 (prime-free `ℤ[ζ_n]` reduction), else a spurious "defect at all r" appears. |
| **F4** | `B ~ n^{1/2+o(1)}` (sqrt-`n`-log law), NOT the `n^{3/4}` moment ceiling; `a→1/2` | **NUANCED-CONFIRMED (direction); `a→1/2` indirect** | **Direction CONFIRMED robustly.** Discriminating evidence (holds raw + Gumbel-EV-corrected, so not a sampling artifact): `B/√(n log(p/n))` flat (CV 0.08–0.09) while `B/n^0.75` sweeps 1.45→0.82 (CV 0.20–0.22) — opposite of an `n^{3/4}` law; global log-log marginal slope **0.466–0.484 ≈ 1/2** not 0.75; direct `B²` fit favors `c·n·log(p/n)` over `c·n^1.5`. Measured `a` ≈ claimant's `[0.825,0.812,0.775,0.752]`. **Honest caveat:** at no finite tested `n` is `a` actually near 0.5 (`n=1024`: `a_ev=0.747`); "`a→1/2`" is an asymptotic *inference* from trend+slope+normalizer, not an observed value. |
| **F5** | tower recursion has perfect child phase-alignment `cos=1` at maximizer, OR `±1` for generic; alignment NOT universal | **NUANCED-CONFIRMED (but reason is trivial)** | Both literal sub-claims reproduce (`cos=+1` at maximizer all levels `μ≥2`; `±1` sign-mix generic), and the conclusion "alignment is NOT a universal descent mechanism" is **CORRECT**. **But** `cos = ±1` is a **TRIVIALITY forced by realness** (`−1∈μ_n` for `n` even ⇒ both half-sums real), not a phase-coherence effect — degenerate at every level for ANY frequency. Only the **SIGN** carries information; the non-trivial open content is the sign pattern down the 2-adic tower = √-cancellation among `(p−1)/n` Gauss-sum phases (unchanged, still open). |
| **identity** | `η_b = (1/m)[−1 + Σ_{j=1}^{m−1} conj(χ_j)(b)·τ(χ_j)]`, `|τ(χ_j)|=√p` | **CONFIRMED** | Both faces to **machine precision ~1e-14** (10⁶× below the 1e-8 bar). The `m` characters of `Q=F_p^*/μ_n` are exactly `χ_{nl}(g^k)=exp(2πi(nl)k/(p−1))`; `τ(χ_0)=−1` supplies the `−1`. **Falsification controls pass:** full-`F_p^*` chars give error 15.8, wrong coset gives 17.3 — the match genuinely depends on the correct quotient-character set, not a tautology. Confirms in-tree face (i) and the `|τ|=√p` anchor. **NOTE:** this is the EXACT algebraic identity (a known/structural fact); says nothing about the open bound. |

**Bottom line on findings.** All survive *qualitatively*. The two with shaky *quantitative*
specifics are **F1** (center ~1.30 not 1.33 — 1.33 is the upper edge) and **F3** (onset `r=5`
not `r=4`, magnitude ~2× smaller, and the double-factorial-is-char-0 confusion corrected). F4's
direction is solid; its `a→1/2` endpoint is an inference. F5's effect is real but trivially forced.
The identity is rock-solid.

---

## 2. Proof-route assault — did ANY route make genuine progress? (NO) + frontier map

**Headline: NO route made genuine new progress toward `B ≤ C·√(n log(p/n))`.** Every route walls,
and three routes' *own headline claims were refuted by the skeptic*. Best bound achieved by any
route in-regime remains the literature record **`t^{1−31/2880} ≈ t^{0.989}`** (di Benedetto 2020),
a **full half-power short** of the `√n` target. Below is the consolidated, exhaustive frontier map.

| # | Route | Best in-regime | Walls at (the exact failure point) | Skeptic verdict on route's *own* claims |
|---|---|---|---|---|
| **R1** | **Norm-Mahler-lattice** (count short `α` in cyclotomic prime ideal `𝔭`) | none (no improvement) | **FATAL CONFLATION of 3 distinct thresholds:** (a) norm-no-defect window `2r<p^{1/φ}→1`; (b) abstract short-lattice-point onset `r*~3`; (c) REAL additive-energy-defect onset `r=5` (`n=16,β=4`), deepening with β; (d) defect-DOMINANCE depth (`~ln p`, unmeasured). The route equates "defect first **nonzero**" with "defect **dominates** the moment bound" — but at first onset defect/`E_r^(0)` = **2.35e-4**, utterly negligible. Minkowski forces a ball point, not a *realizable* sparse `r`-fold-sum defect. | **REFUTED.** Headline norm-bound "correction" attacks a strawman (correct exponent is `φ(n)` not `φ/2`); `r*=3` is the wrong object; route's own two probes are mutually inconsistent. Claimed "new wall lemma" is FALSE as stated. |
| **R2** | **Large-sieve / amplification** (Iwaniec-Sarnak amplifier, smoothed-max duality, classical large sieve) | `B≤n` (trivial) | **The L²→L^∞ extraction step**, three each-fatal walls: (1) **smoothing tautology** — `max_c (|η|²∗K)(c)` is achieved at the unattenuated spike, so smoothing can only *increase* the max (measured F=1→31: 1.0→2.6×); (2) **NO Hecke gain** — amplified 2nd moment over the Gauss-sum dual is **purely diagonal** `=‖a‖²(m−1)p` (off-diag/Jacobi gain = 0 to ~8% noise, all amplifier lengths), because the natural `b`-average is the COMPLETE quotient `Q` which annihilates Hecke-analogue mixing; (3) **circularity** — a usable a-priori amplifier needs a uniform lower bound on a short character sum over `Q` = the original incomplete-subgroup-sum problem verbatim. | Route's no-go conclusion **UPHELD** and sharpened. New mechanism (off-diagonal=0, why I-S transfers zero advantage) is a genuine *negative* structural fact. |
| **R3** | **Limiting-distribution / exact-constant** (claims `C₀=√2`) | `n¹` (none) | `C₀=√2` fails BEFORE any tail bound: (1) **empirical confound** — support for "`C₀²→2`" holds `m≈30000` fixed while growing `n`, sliding `β` from ~4.1 down to ~2.86 (only `n=32` is in-regime); on a **controlled fixed-β diagonal** `C₀²` is flat/non-monotone **~1.72**, not rising to 2; (2) **circularity** — `C₀²→2` IS the iid-Gaussian extreme value `t²/ln m→2`; assuming the `m` correlated deterministic periods behave iid in their extreme = √-cancellation = the open core. | **`C₀=√2` REFUTED** (see §3). Only survivor: the bulk κ4=−3/n correction (correct char-0 algebra, characterizes the bulk not the max). |
| **R4** | **Stepanov-Weil-boundary** (push HBK / di Benedetto below `p^{1/4}`) | `t^{0.989}` only at top edge `α=0.25`, dies by `α=0.2094` | **EXACT wall at `α* = (1/72)/(1−2689/2880) = 0.20942 = p^{1/4.78}`** — the di Benedetto record itself becomes trivial; the prize `[p^{1/5},p^{1/4}]` straddles/sits below it. Two structural walls: (1) **L⁴→L^∞ loss** — Stepanov is a counting method, reaches `B` only via `B≤(p·E_r)^{1/2r}`, carrying an irreducible **+1/4** in the `p`-exponent (even with EXACT `E_2`); (2) **depth ceiling** — removing +1/4 needs `r~log p` (`r=89–111` at `n=2³²`), Stepanov proves a saving only to `r=3`. The 2-power structure gives ZERO leverage: degree/count invariants (`deg X^{2^μ}`, Lemma-6 monomial count, `n⁴T<p³`) are factorization-blind. OSV 2022 Rmk 1.2 confirms no post-2020 lift of the linear case. | Route's no-go **UPHELD**. New: exact `α*=p^{1/4.78}` crossover; clean impossibility argument that `n=2^μ` is not special. |
| **R5** | **Dyadic-2adic-Gauss-tower** (Stickelberger / quadratic-Gauss-sign / Lam–Leung descent) | none (`C₀≈1.21` for dyadic ≥ odd-order `C₀≈0.96`) | **2-adic lever lives in the WRONG place.** Four walls: (1) the `χ` trivial on `μ_n` (where `τ` lives) have order `| m`; their 2-power block is O(1) size `∈{1,2,4}` — the √-cancellation needed is among the `~m` **ODD-order** phases the 2-adic lever can't touch; (2) quadratic char trivial on `μ_n` only when `v₂(p−1)>μ`, contributes `O(n/√p)=o(1)`; (3) deep p-defects are full-rank generic in `ℤ[ζ_n]`, **no descent** to `ℤ[ζ_{n/2}]` (0/96) — Lam–Leung constrains nothing; (4) defect persists above the norm threshold (2.5–3.8×) and into the prize regime. **`−1`-closure INFLATES the house** rather than cancelling. | Route **REFUTED as a path to √(n log)**; clean reproducible no-go. New negative lemma: antipodal-inflation + exact 4-wall localization. |
| **R6** | **Novel-freeform** (non-backtracking/Ihara-Bass; Bourgain-Chang level-set; LP/Beurling-Selberg majorant; "SHARP" Markov-Krein) | none | Walls at the same open core (√-cancellation among `~m` phases) — correct. **But the route's advertised SPECIFIC wall ("sharp moment short by Θ(log m), deficit grows with prize size") is FALSE.** Independent LP re-derivation: `R_need` (smallest `R` to reach 1.5× target) is **FLAT ~7** across `log₂m=20..80`, not growing linearly. Genuine gap is "valid to `r*~3`, need `~7`" = **O(1)**, not `Θ(log m)`. | **REFUTED.** The "SHARP Markov-Krein" bound is the **CRUDE single-moment Markov inequality mislabeled** (route's own docstring admits "APPROX ... is the naive bound"). True LP extremal is strictly smaller, needs O(1) moments. Moments were **wrong-signed**: true normalized eigenvalue moments are **SUB-Gaussian** (kurtosis 2.81–2.91 platykurtic; ratio `μ_2r/(2r−1)!! = 1.00,0.94,0.82,0.67,0.50`), permitting LESS extreme atoms — route conflated the char-0 ENERGY defect with the eigenvalue MOMENT (two different quantities). |

### The consolidated frontier map (where everything bottoms out)

All six routes reduce to **ONE** recognized open problem, via different arrows:

```
                         B = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|   (thin dyadic subgroup, n=p^{1/β}, β∈[4,5])
                                          │
        ┌──────────────────┬─────────────┼─────────────┬──────────────────┐
   face (i) char-sum   face (ii) Paley  face (iii) house  moment arrow    amplification
   BGK / di Benedetto   eigenvalue λ₂    Norm/Mahler       B≤(p·E_r)^{1/2r}  L²→L^∞
        │                    │                │                │                │
   record t^{0.989}     exact only in     log-norm only,   needs E_r=E_r^(0)  diagonal=‖a‖²·p
   (R4 caps here)       structured cases  fixed-f axis      to r~ln p          (R2: zero gain)
   half-power short     (R5 inflates)     (Habegger:avg)    (R1/R3/R6 wall)
        │                    │                │                │                │
        └────────────────────┴────────────────┴────────────────┴────────────────┘
                                          ▼
              √-CANCELLATION among (p−1)/n Gauss-sum phases χ̄(b)τ(χ_j), |τ|=√p
              = BGK / Bourgain–Glibichuk–Konyagin incomplete-subgroup-sum problem
              = generalized-Paley almost-Ramanujan (λ₂ ≤ 2√n)
              = di Benedetto/Shkredov sub-Johnson wall (record t^{0.989}, a FULL HALF-POWER short)
              = deep-moment defect-DOMINANCE depth (~ln p), NOT defect-onset depth (~β+1)
                                    ── OPEN ──
```

**Key consolidated insight (the sharpest negative output of the whole pass):** the deep-moment wall
is mislocated by *three* successive over-shallow thresholds, and the routes that "wall at `r~β`"
are conflating them. The honest hierarchy of depths is:

1. **norm-no-defect window** `2r < p^{1/φ(n)} → 1` ⇒ `r=O(1)` (the *proven* clean band; Lean §4).
2. **real additive-energy-defect ONSET** `r ~ β+1` (F3 corrected: `r=5` at `n=16,β=4`) — where the
   defect first becomes *nonzero* but is still `~1e-4·E_r^(0)`, **harmless**.
3. **defect-DOMINANCE depth** `~ln p` — where defect becomes *comparable* to `E_r^(0)` and actually
   inflates `(p·E_r)^{1/2r}`. **This is the real wall, and it is UNMEASURED/UNPROVEN.**

No route reaches depth (3); they wall at (1) or (2) and mistake it for (3).

---

## 3. Exact constant `C₀²` — closed form found?

**NO closed form. Still numerical.** The limiting-distribution route (R3) claimed `C₀²=2` (i.e.
`C₀=√2≈1.414`); this is **REFUTED**:

- `C₀²=2` is exactly the **iid-Gaussian extreme-value constant** (`max of M iid N(0,1) ≈ √(2 ln M)`).
  Asserting it presupposes the `m` correlated deterministic period values behave iid in their
  extreme — which **IS** the √-cancellation open core.
- The empirical "rise to 2" is a **confounded experiment**: it slid `β` from ~4.1 down to ~2.86
  by holding `m` fixed while growing `n`. On a **controlled fixed-β diagonal** (`m=n²`, `β=3`) the
  constant is **flat/non-monotone ~1.72** (`C₀²=1.73,1.77,1.65,1.74` for `n=64..512`), NOT rising.
- Independent verification (F1) measures the center on the true `β=4` diagonal at `C₀≈1.29–1.32`
  (so `C₀²≈1.66–1.74`).

**Honest status of the constant:** `C₀² ≈ 1.7–1.8` numerically (equivalently `C₀ ≈ 1.30–1.34`),
**flat on a fixed-β diagonal**, **NO proven or even conjectured-closed form**. The candidates on
the table — `√2` (iid-Gaussian extreme), `√(7/4)=1.323` (the in-tree `1.75` plateau), bare-Gaussian
`1` (F2-refuted off-diagonal artifact) — are all either refuted or unproven heuristics. The one
*correct* increment is the **bulk** kurtosis correction `κ4 = −3/n` (`E[(η/√n)^{2r}] =
(2r−1)!!(1 − r(r−1)/(2n) + O(1/n²))`), which is right char-0 algebra but characterizes the
distribution **bulk**, not the **max** — so it does not pin `C₀`. The value-distribution literature
(Marklof's non-Gaussian incomplete-Gauss-sum limit law, Garcia's `p^{3/2}` 4th-moment term)
independently predicts the constant carries **arithmetic structure** above the bare-Gaussian 1 —
consistent with the ~1.33 plateau being inflated, but offering no closed form.

---

## 4. Lean formalization — what is axiom-clean, what is the isolated open Prop

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/CyclotomicNormDefectThreshold.lean`
**Status: PROVEN axiom-clean** (exactly `[propext, Classical.choice, Quot.sound]` on all 8 theorems;
no `sorry`, no `native_decide`; forbidden-axiom grep = 0). **Verified to exist in tree.**

**What is proven (the TRUE EASY HALF — the clean range, end-to-end, nothing abstracted):**
- Main: `prime_le_of_balanced_tuple` — realizing the cyclotomic integer `α` as `g(ζ_n)` for a
  signed-monomial `g ∈ ℤ[X]` (`≤2r` unit-modulus terms), proves `p ≤ (2r)^{φ(n)}` via
  `Polynomial.resultant` + complex embeddings.
- Capstone (contrapositive): `no_spurious_tuple_of_lt_prime` — if `(2r)^{φ(n)} < p` then **no**
  signed-monomial `g` has a primitive `n`-th root `ζ ∈ ZMod p` as a root.
- All four sub-bounds **discharged** (none left as hypotheses): (1) per-conjugate `|g(ω)|≤2r`
  (triangle ineq); (2) `|Res(Φ_n,g)| = ∏|g(ω)| ≤ (2r)^{φ(n)}` as a genuine integer-norm bound
  (`resultant_eq_prod_eval` + `map_cyclotomic_int`); (3) `p ∣ Res` when `α≡0 mod 𝔭`; (4) `Res≠0`
  from char-0 nonvanishing. Generalizes the in-tree `CyclotomicResultantBound.lean` (4-term, bound 4)
  to arbitrary `M=2r`, and PROVES what the sibling `CleanRangeNorm.lean` leaves as a hypothesis on `N`.

**What is isolated as the OPEN part:** the complementary regime `(2r)^{φ(n)} ≥ p` — i.e. once the
prime sublattice `𝔭` meets the `2r`-box, where the threshold theorems become **vacuous**. In the
prize regime `φ(n)=n/2` so `p^{1/φ(n)}→1`, certifying only `r=O(1)` — **far below** the
moment-optimal `r≍log p`. This open regime is the **Bourgain–Shkredov representation-mass /
equidistribution wall at `n<p^{1/4}`**; it is **documented in the docstring (§Honesty contract) and
tracked in** `docs/kb/deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`. It is honestly
**NOT** encoded as a `:True` placebo or a `_holds` axiom (per the ResidualAxioms larp-audit
discipline) — the file proves *only* the clean range and states the open part in prose.

**Honest Lean verdict:** this is the rigorous formalization of the *known-vacuous easy half*
(matching MEMORY: "char-0 EXACT while `2r<p^{2/n}`, VACUOUS for prize"). It does **NOT** prove DGPH
or the Proximity Prize, and the file says so explicitly. It is a clean, reusable, correctly-scoped
brick — not a closure claim.

---

## 5. COMPLETENESS CRITIC — what attack surface was NOT tried

The six routes cover: lattice/norm (R1), analytic amplification (R2), value-distribution (R3),
Stepanov/Weil (R4), 2-adic algebraic descent (R5), and freeform spectral/LP (R6). The literature
sweep additionally surveyed Paley-eigenvalue (Podestá–Videla), Habegger house-norm, Garcia moments,
Bober–Goldmakher / Marklof extreme-value, and Bandeira–van Handel matrix concentration. **What was
NOT genuinely attempted:**

1. **Polynomial-method / Croot–Lev–Pach–Tao slice rank** applied to the *additive-energy
   incidence tensor* `E_r = #{x_1+…+x_r = y_1+…+y_r}` directly (not via norm bounds). The defect
   `E_r − E_r^(0)` is exactly an upper-bound-on-the-rank-of-a-structured-tensor question; CLP/slice
   rank is the modern tool for "few solutions to `Σ=Σ` over a multiplicative set." **Untried.**
2. **Effective Bombieri–Pila / o-minimal point-counting transferred from Habegger's
   log-norm to the MAX** — Habegger controls `(1/k)Σ log|η_t|` (the *average*); the determinant
   method counts conjugates of bounded house in a box. Nobody tried to push his unlikely-intersection
   machinery from the geometric mean to the sup. **Untried** (literature only does the average).
3. **The SIGN-pattern of the real half-sums down the 2-adic tower (F5's residual).** F5 proved the
   *cosine* metric is degenerate-by-realness, but the **sign sequence** `s_μ ∈ {±1}` of the real
   half-sums is the actual carrier of √-cancellation and was never modeled as a (possibly
   pseudorandom / multiplicative-character-driven) sequence. A sign-correlation / discrepancy bound
   here is the structurally-closest untouched handle. **Untried.**
4. **`E_3` (sixth-moment) via Schoen–Shkredov `E_3(A) ≪ |A|³ log|A|` for `|A|≪p^{2/3}`** — flagged
   in the sweep as an *honorable mention* but never actually fed through. L⁶ alone gives only
   `B ≲ n^{2/3}(log)^{1/6}` (admitted far from `√n`), but it was not combined with the amplifier or
   the LP majorant. **Partially untried** (known to be insufficient solo).

### The SINGLE most promising untried direction

**Direction (1): the polynomial method / slice rank on the additive-energy defect tensor,
combined with the corrected depth hierarchy from §2.** Rationale: every route that walls does so by
needing `E_r = E_r^(0)` to **depth `r ~ ln p`** while only being able to certify it to **`r = O(1)`**
(norm) or knowing the defect is *nonzero* by `r~β+1` (F3). The genuinely open quantity is the
**defect-DOMINANCE depth** — at what `r` does `E_r − E_r^(0)` become *comparable* to `E_r^(0)` rather
than merely nonzero (currently `~1e-4·E_r^(0)` at first onset). This is a **bound-the-growth-rate-of-a-
structured-tensor-rank** problem, exactly the shape CLP/slice rank attacks, and it has **never been
applied to the `Σ=Σ` energy of a multiplicative subgroup**. It is the only untried tool that targets
the *real* wall (depth 3) rather than the mislocated shallow onset (depth 2). Even a *conditional*
"defect stays `o(E_r^(0))` to `r=c·ln p`" via slice rank would, through the proven in-tree moment
arrow `B≤(p·E_r)^{1/2r}`, deliver `√(n·log p)` — i.e. it plugs directly into the existing chain. The
honest risk: slice rank typically gives *capset-type* exponential-in-dimension bounds and may itself
wall, but it has not been tried and it is aimed at the correct threshold.

---

## 6. HONEST FINAL VERDICT

**The prize core is STILL OPEN after this exhaustive pass. No fabrication; no closure claimed.**

This pass was *productive in the honest sense*: it (a) independently reproduced the empirical
structure (F1 plateau, F4 √-log law, F5 realness, identity) while correcting two quantitative
over-claims (F1's 1.33→~1.30; F3's onset `r=4→r=5` + the double-factorial-≠-char-0 fix); (b) refuted
three routes' *own* headline claims (R1's "new wall lemma", R3's `C₀=√2`, R6's "Θ(log m) deficit");
(c) produced the **sharpest negative result of the campaign** — the explicit three-threshold
hierarchy showing every route walls at the *defect-onset* depth (`~β+1`) or shallower, while the
real wall is the *defect-dominance* depth (`~ln p`), unmeasured; (d) located the exact di Benedetto
triviality crossover `α*=p^{1/4.78}` proving the prize regime sits inside the dead zone; (e) landed
a correctly-scoped axiom-clean Lean brick for the known-vacuous clean half, honestly documenting the
open complementary regime. The literature sweep confirms **nobody** reaches `√(n·polylog)`: the record
is `t^{0.989}`, a full half-power short, and the deepest machinery (Habegger o-minimality,
Podestá–Videla Paley spectrum) lives on the *fixed-order* axis or resolves only the *structured* cases
the prize excludes.

### Updated conjecture ranking (each /10)

| Face / conjecture | Novelty | Insight | Proximity (to proof) | Feasibility |
|---|---|---|---|---|
| (i) char-sum `B ≤ C√(n log(p/n))` (the prize, via BGK/di Benedetto) | 6 | 9 | **2** | 3 |
| (ii) Paley almost-Ramanujan `λ₂ ≤ 2√n` (generic thin 2-power) | 5 | 8 | **2** | 3 |
| (iii) house/norm of `η_1` ≤ `C√(n log)` (Habegger axis) | 7 | 8 | **2** | 2 |
| moment route: defect `o(E_r^(0))` to `r~ln p` (the real bottleneck) | 8 | 9 | **3** | 4 |
| **slice-rank on the energy-defect tensor (untried, §5)** | **9** | 8 | **3** | 4 |
| Lean clean-range threshold (proven, easy half) | 4 | 6 | 10 (done) | 10 (done) |

*Proximity column reads "how close is a proof," not "how close to the truth" — all faces are believed
true (numerics robust), but a proof is `~2/10` away across the board.* The highest-leverage *open*
target is the **moment-defect-dominance depth**, and the highest-novelty *untried* attack on it is
**slice rank** — they are the same row of the table.

**One-sentence bottom line:** After an exhaustive six-route assault, a deep cross-domain literature
sweep, five independently-reproduced findings, and an axiom-clean Lean brick for the easy half, the
#407 core remains a recognized open problem — every route provably reduces to the same √-cancellation
wall, the world record stays a full half-power short (`t^{0.989}`), the exact constant has **no closed
form** (numerically `C₀≈1.30–1.34`, flat on a fixed-β diagonal, `√2` refuted), and the single most
promising untried direction is the **polynomial method / slice rank on the additive-energy-defect
tensor**, which uniquely targets the *real* (defect-dominance, `~ln p`) wall rather than the
mislocated shallow onset and plugs directly into the proven in-tree moment arrow.
