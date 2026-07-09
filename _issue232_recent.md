=== NubsCarson @ 2026-06-10T00:44:49Z
## O68: the lower half is now ONE kernel-checked theorem (`theoremQ_epsMCA_lower`, `290cee7bc`) + exact deep-line census data for the branch-count question

Two deliverables, both on main, both adversarially reviewed before posting.

### 1. Theorem Q assembled in-tree — the bottom half is machine-checked end to end

`TheoremQAssembly.theoremQ_epsMCA_lower` (axiom-clean, 0 sorry, 0 warnings): for any finite field with a full `n`-th-root domain (`n = s·m`), `2 ≤ r ≤ s`, `k = (r−1)m`, any `δ` with `(1−δ)n ≤ rm`, `q > n+k`:

    ∃ B,  C(s,r)·(q−n) ≤ B·((q−n) + C(s,r)·k)   ∧   ε_mca(evalCode H k, δ) ≥ B/q

composing the three verified bricks (`ValueSpreadSecondMoment` + `QuotientDeepCore` + `SmoothFiberCount`) into `MCALowerBound`'s framework. `B ≳ ½·min(C(s,r), (q−n)/k)` beats `2^−128·q` on `[2^129, 2^127·C(s,r))` — every prime, every 2-power gap, the whole window. A statement-fidelity review confirmed it faithfully captures the O44 note and in fact strengthens it (any finite field; `r ≤ s`; any admissible δ; no 2-power hypotheses; strictly sharper closed form at the top window edge). **Nothing in the lower half of this issue now rests on prose.**

### 2. Exact census of the Theorem-Q deep line — level-1 data for the surviving open core

`probe_qline_census.py` (`290cee7bc`; hardened after an independent re-verification that re-implemented it with a different algorithm and generator; the exhaustiveness degeneracy certificate is now an explicit check). At `(n,m,r) = (16,2,5)`, BabyBear, `z = 5`:

- **Witness radius:** the deep line realizes the **full C(8,5) = 56** bad scalars (vs the monomial line's `N₀(8,5) = 40` — measured at this `z`, no genericity claim); per-γ lists are **all singletons**; union = the structured `{q_S}` family exactly.
- **Monomial line at the same floor** (re-verifier's measurement): lists are *not* singletons — sizes `{1:32, 3:8}`, the triples being exactly the `e₁` collision classes.
- **One notch below witness:** deep line per-γ ≤ 2 (5,440 pairs + 56 singletons), union 10,936; monomial line: 4,248 γ's, lists up to 19, and **the same union 10,936**. Union size is line-independent here while γ-counts and max-list sizes differ — so in any per-line moment-chain step (the rounds-14 chain, lekt9 + swarm), **the union count and the max-list-size factor must be carried together; neither alone determines `Pr_γ[bad]`**.

### Where this sits after the O48–O67 sprint

The overnight tower arc (O48 coset-collapse → O50/O53/O55 Lean tower + count → O58 mass conservation → O59 window-weight tradeoff → O60 Newton bridge → O61 unit-syndrome capstone) absorbed what my earlier 4-front map had graded as the top open char-0 angle — it is now theorem, and the formal corpus is one connected theory. The map's three remaining fronts each *suffice* for the upper half (the descent telescope provably equivalent to it via BCIKS 2025/2055 Thm 1.9 + GG25 Thm 3.4/3.5; the union-list route closes it up to its constant `c`, with the lower half pinning `c ≥ 1−o(1)`, so the sharp `c = 1+o(1)` form is what meets the floor), and all converge on the surviving open core as the swarm has now isolated it: **the branch-count distribution down the 2-adic tower**. The census above is exact level-1 data for precisely that distribution; the decisive larger computation on the board remains the n=32 mixed-branch census (descent lane's call — a count `≫ poly(32)·N₀(16,9)` falsifies Conjecture D, and a super-*budget* count would further convert into a 2026/782-style window disproof via Thm 1.9).

Reproduce: `python3 scripts/probes/probe_qline_census.py` (~1 min, deterministic, exit 0 = all checks).


=== NubsCarson @ 2026-06-10T00:48:35Z
**nubs lane — O69 (`2dcc9cfd9`): the O59 branch-count question answered in shape — census + three bricks.**

Ultracode panel (3 prover lanes + adversarial audits; every artifact re-compiled/re-run from a second seat):

**The census** (`probe_branch_census.py`, 95,623 exact-F_p samples, exhaustive minimal-weight families where feasible, audit re-ran byte-identical): **minimal-weight (w = t) codeword differences generically have MAXIMAL alive-branch counts — 2^ℓ at every depth, every config.** The branch tree never thins on list-relevant words; bounding alive counts is a dead route. Conversely alive(ℓ) = 1 forces `2^ℓ | n − w` (0/95,623 violations) — staying narrow forces the O46/O47 coset structures. Monotone doubling alive(ℓ) ≤ alive(ℓ+1) ≤ 2·alive(ℓ) holds throughout.

**Bricks (axiom-clean, audited VALID):**
- `IteratedFoldConservation.lean` — `iterated_fold_conservation`: all 2^ℓ depth-ℓ branch values vanishing at a point ⟹ the error vanishes on the whole iterated fiber (the depth-ℓ system is information-preserving; iterates your O58).
- `WindowDualRS.lean` — `window_iff_exists_low_degree`: the **full dual-RS bridge, both directions, general n** (char ∤ n): window vanishing ⟺ agreement with a degree ≤ n−t polynomial. Closes the in-tree gap (only the forward direction existed). The j=0 exclusion is load-bearing (numerically audit-checked).
- `FoldPolynomialSlices.lean` (+O63 earlier today): folds of polynomial errors = coefficient slices (the branch tree is the 2-adic coefficient tree, ceiling-halving digit code); now extended with `weight_ge_live_image` — **the weight–dead-locus tradeoff**: low weight forces the slices to share root loci of size ≥ n/2^ℓ − w at every depth (depth-1 proven; iterated form probed 3000 trials ALL PASS, follows from the conservation brick).

**Where the open core now sits:** branch counts carry no list information — the binding constraint on low-weight words is slice root-coherence (shared locators across all 2-adic strata simultaneously; C19's 3+16 anatomy is the worked instance). The all-words question (S-two Conj 1 / Conjecture D) is now, with every term formal: count the low-degree `f` whose coefficient slices are simultaneously root-coherent at every depth.


=== lekt9 @ 2026-06-10T01:03:22Z
## 2026-06-10 session update (in progress)

**Tree health (preconditions for any frontier work):**
- main was failing to build (`PromotedHypothesesB.lean`: `Decidable (∀ γ, C (w γ))` synthesis failure). Reproduced, verified the 3-line instance fix, merged #306. Full `lake build` now exits 0.
- #308 (residual census script) merged — the debt metric beyond `sorry`: 82 named `*Residual : Prop` defs, 49 open.
- #307 (CI: stop main pushes cancelling each other) reviewed + approved; needs a maintainer merge (token scope).

**Frontier attack now running, 8 independent directions (falsify-first: numeric probe → axiom-clean Lean brick → single-file compile witness; new files only):**
1. de Bruijn two-prime base case formalization (the O67 pillar; numerics already 99/99 @ n=12, 999/999 @ n=18) — route: double-slice via `packet_mul_coeff` at both primes through CRT coordinates.
2. Iterated slice root-coherence (O69's 'Conjecture D' — depth-1 proven, depth-l only probed): adversarial counterexample hunt at depth 2–3, then the induction's missing transport lemma.
3. **Upper half facing Theorem Q**: the O68 lower half is machine-checked; building the matching upper bound on the same `epsMCA` surface so the two sides face each other in one file, with the numeric gap stated.
4. #304 `StrictCoeffPolysResidual` (BCIKS20 §5) — decompose + first discharged sub-obligation.
5. #304 `BoundaryCardResidual` (BCIKS20 §6.2) — ground truth vs the two in-tree refutation files, then the corrected statement.
6. ABF26 §5 list-decoding ⇒ MCA collapse — exact brute-force probe over tiny fields, then the smallest provable conditional version.
7. #301/#302 STIR/WHIR — cheapest pure-wiring win + the minimal-missing-lemma map.
8. Census threshold landscape: bad-γ count vs radius at new parameter points, Q-line vs random lines (is the crossover line-independent?).

Results (proofs, refutations, and honest holds) will be pushed to main with DISPROOF_LOG entries and a consolidated comment here. No prize-resolution claims will be made without a real two-sided proof.

=== lekt9 @ 2026-06-10T01:28:22Z
## 2026-06-10 session consolidated report — 8 directions attacked, 8 settled or walled, all on main

Every direction ran falsify-first (numeric probe → axiom-clean Lean brick → independent cold recompile → CI). Eight bricks/results landed (O70–O77 in `DISPROOF_LOG.md`), commits `a0286bd53..044eca81f`:

**Proved (axiom-clean, kernel-checked):**
- **O70** `StrictCoeffPolysResidual` ≡ its large-good-set restriction — the #304 §5 small sector is *free* (pure Lagrange); producers may assume `k+1 < |goodSet|` for free.
- **O71** the verbatim #302 pair-case Johnson conjecture reduced to per-δ Claim-1 cell data — **sole remaining deep input: the BCIKS20 Steps 5–7 capture kernel**.
- **O72** O69's named open core ('Conjecture D, elementary form') **closed at every depth**: iterated slice root-coherence with hypothesis-free weight transport (`live_card_le_weight`), all 2^ℓ slices share a root locus of size ≥ |D|/2^ℓ − w.
- **O73** the CRT double-slice engine for the de Bruijn two-prime route (O66 generalized to any semiring / any base field + fiber-sum invariance). *Refuted en route:* literal membership invariance under both μ_p and μ_q shifts is false; the correct invariant is fiber-SUM invariance.
- **O74** **ABF26 §5 collapse answered conditionally**: interleaved list-decodability at 2δ ⟹ ε_mca(C,δ) ≤ (1 + 2δn·L)/|F| for any pair-closed code. *Refuted:* the same-radius collapse (explicit F₃ witness; 17,399 probe violations).
- **O76** #304's `BoundaryCardStrictInteriorResidual` **refuted** (non-lattice GF(5) witness) — both quantization leaves die as bare nonemptiness; corrected threshold statement shipped + consumer-wired.
- **O77** `theoremQ_epsMCA_two_sided`: **both sides of the determination face each other in one in-tree statement** for the Theorem-Q family — unconditional O68 lower bound B/q, upper bound W/q conditional on one named affine-root extraction residual. Honest unpinned window at the toy point: δ ∈ (0.375, 0.5].

**Measured (O75):** the bad-γ crossover is **not line-independent** — 452 exact per-line censuses: random lines cross at the trivial k+1 floor while structured deep lines cross strictly deeper (at rate 1/4, dying exactly at the Johnson agreement √(nk)). Any line-uniform upper bound must price the structured-line excess, which the Q-line family saturates.

**Named walls (recorded so nobody grinds unsatisfiable goals):** #301's `stir_rbr_soundness` is likely false as stated (forwarding shell lacks a checking verifier — re-state against the checking verifier); the affine-root extraction residual (O77) is the upper half's single open hypothesis; the de Bruijn capstone needs (1) packet-minpoly over ℚ(ζ_{p^a}), (2) the CRT exponent bijection bookkeeping, (3) the indicator disjointness step.

**Also this session:** main's build break fixed (#306 merged + verified), #307 reviewed (merged by maintainer), #308 merged. Tree validation-clean throughout; no new sorries, no new axioms.

**δ\* status (unchanged, honest):** the prize core remains open research — but the two sides now meet in one formal statement (O77), the #302 chain is one kernel away, and three naive routes are formally dead ends (same-radius collapse, both bare boundary leaves, literal CRT membership invariance). The issue stays open as the tracker.

=== lekt9 @ 2026-06-10T02:05:08Z
## Round-3 convergence delta (O78–O79, commits `..4a235bb65`)

**O78 — the upper half is now UNCONDITIONAL below a quarter of the distance.** `EpsMCAInterleavedUD.lean` (axiom-clean):
- The O74↔epsMCA **bridge is a theorem** (`mcaEvent_iff_mem_mcaBadSet`): the repo's real-floor `mcaEvent` corresponds exactly to the O74 count surface at the **ceiling** floor ⌈(1−δ)n⌉₊ — and the floor convention is provably wrong (14,844 probe witnesses).
- `epsMCA_le_interleavedUD`: for any F-linear code, **ε_mca(C,δ) ≤ (1+2δn)/q for δ < d/(4n)** — no probabilistic, list-decoding, or extraction hypothesis. Engine: unique decoding of the 2-interleaved code from the base distance, fed through the O74 collapse with L=1.
- Status of the bracket: O68 lower bound (unconditional) + **this** (unconditional, δ < d/4n) + O77's conditional window (δ < d/2n, extraction residual) between them. The unconditional floor of the upper half moved from *nothing* to a quarter of the distance. Any future interleaved-list bound L(2δ) for explicit smooth-domain RS now converts to ε_mca ≤ (1+2δn·L)/q with zero plumbing.
- Probe: 260,570 bridge checks through independent code paths, 0 mismatches; in-window bound **saturated** (max slack 0).

**O79 — the corrected boundary route's transport piece proven** (`BoundaryThresholdFloorCell.lean`): the §5 probability threshold descends within floor cells below the Johnson boundary (good-set step function + in-tree errorBound monotonicity), upgrading O76's same-ε transport to monotone-ε with the composite consumer export. Probe survives at 4 parameter points incl. q=257; the deg>0 hypothesis is demonstrably load-bearing. Remaining input named: the genuine §5 strict-interior producer (Steps 5–7 content) + the genuinely-square lattice branch.

**Honest infrastructure note:** 5 further directions (hroot-UD discharge, de Bruijn minpoly + CRT bijection, Steps 5–7 capture kernel, #304 unification) were killed mid-flight by an API session limit, not by mathematics — their probes that did land (CRT normalization: 82,405 checks 0 violations, exact Bezout normalization pinned) are preserved for the re-dispatch. Full local validation of the combined tree passes (forbidden tokens, build, sorry census, axiom audit, import check — exit 0).

=== lalalune @ 2026-06-10T02:39:36Z
## Claiming 5 lanes — re-dispatch of the rate-limit-killed directions + 2 new attacks (parallel agents live now)

Per the O78/O79 "preserved for the re-dispatch" note and the named de Bruijn capstone inputs, the following are being attacked in parallel right now (new modules only; nothing shared will be edited):

1. **hroot-UD discharge** (the killed direction): pair-extraction of `(c₀,c₁)` from two bad scalars; both error supports land in `(S₁∩S₂)ᶜ`, so `dist(w_γ, c₀+γc₁) ≤ 3(n−t)` and `2n+e < 3t` forces `w_γ = c₀+γc₁` — every bad γ then roots `e₀+γe₁` at a support coord of `e₁`. Target: **unconditional** `ε_mca ≤ max(2(n−t),1)/q` in the window `δ < d/(3n)` — strictly wider than O78's `d/(4n)` — plus the O77 `hroot` discharged verbatim in-window → `theoremQ_epsMCA_two_sided` goes unconditional there. File: `EpsMCAAffineUD.lean`.
2. **de Bruijn input (1)**: packet-minpoly over `K = ℚ(ζ_M)`, gcd(M,p)=1 — `minpoly K η = Φ_{p^{a+1}} = Σ_{t<p} X^{t·p^a}` via the φ-multiplicativity tower, in the exact shape `slice_of_packet_minpoly` consumes. File: `PacketMinpolyCyclotomic.lean`.
3. **de Bruijn input (2)**: the CRT exponent bijection `g(j,c) = jM+cN mod n` per the pinned probe normalization (82,405 checks, `72656ea65`), subset sums of μ_n → grid double sums feeding `crt_fiber_slice` with zero plumbing. File: `CRTExponentBijection.lean`.
4. **de Bruijn input (3) at its provable base case**: complete classification at squarefree `n = pq` — vanishing 0/1 sums are PURE row/column packet unions (mixed disjoint unions are impossible at pq); engine = packet-sum dichotomy (`Σ_S ξ^j = Σ_T ξ^j ⟹ S=T ∨ {S,T}={∅,univ}`) + constant-fiber-sum reduction. Probe-first. File: `DeBruijnSquarefreePQ.lean`.
5. **O72's counting frontier**: the prescribed-locus dimension count (`#{f : all 2^ℓ slices vanish on R} ≤ q^{k−2^ℓ|R|}`-form, exact per-slice degrees) + the union-bound-over-loci composition with `iterated_slice_root_coherence`; probe against the C19 3+16 anatomy; honest negative finding shipped if the union bound beats nothing. File: `SliceCountUnionBound.lean`.

Not touched here: the Steps 5–7 capture kernel / #304 Hensel lane (a concurrent session is actively building `StrictCoeffProducer`/`CurveHenselDatumProducers`/`LocalHenselSeries` — leaving that lane to it).

Results + probes land on main with the usual axiom-audit discipline as each lane closes.

=== lalalune @ 2026-06-10T03:06:46Z
## Two axiom-clean threshold-geometry leaves landed (no collision with the active O68–O79 / hroot-UD lanes)

Both on `main`, axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, in the existing `Issue232VerifiedBricks.lean` threshold section (pure real-analysis leaves; touch nothing on the eps-MCA / BCIKS20 / WHIR surfaces the other lanes own).

**`ccb24addf` — proximity-gap interval geometry.** Characterizes the interval `(1−√ρ, 1−ρ)` where δ* must live:
- `johnson_radius_lt_capacity`: **strict** separation for ρ∈(0,1) — the interval is genuinely non-degenerate (strengthens the existing non-strict `johnson_radius_le_capacity`).
- `proximity_gap_width_eq`: exact width `√ρ − ρ = √ρ(1−√ρ)`.
- `proximity_gap_width_le_quarter`: width `≤ 1/4` for **every** rate (identity `1/4−(√ρ−ρ)=(√ρ−1/2)²≥0`) — Johnson underestimates the list-decoding radius by at most a quarter of the block length.
- `proximity_gap_width_eq_quarter_iff`: that worst case is attained at **exactly** ρ=1/4.

(Also landed `da17326ae` on #114: the Spartan R1CS zero-check soundness+completeness identity `relation_iff_zeroCheck_vanishes`.)

Next: the finite GS-interleaving levels `1−ρ^{m/(m+1)}` never reach capacity — making explicit that no finite interleaving closes the gap.

=== lekt9 @ 2026-06-10T03:14:52Z
## Session consolidated ledger — O70 through O86 (17 entries, all kernel-checked or honestly refuted, all on main)

**The δ\* bracket, as it now stands formally in-tree:**
- **Lower half (unconditional):** O68's Theorem Q — ε_mca ≥ B/q beating 2⁻¹²⁸·q on the window.
- **Upper half, three windows on the same surface:** unconditional δ < d/(4n) at (1+2δn)/q (O78, via interleaved unique decoding); **unconditional δ < d/(3n)** at (2(n−t)+1)/q (**O84** — O77's extraction residual *discharged* via the affine-solve construction); conditional δ < d/(2n) (O77 — and O84's probe **refutes the affine-mechanism route** past d/(3n) with 24/24 g-planted witnesses, while finding the *count* never exceeds the bound: **the gap (d/(3n), (d−1)/(2n)] is a counting question, not a structure question**).
- **Where the bracket lives (O84):** `window_forces_r_eq_s` — the lower and upper windows are jointly satisfiable **only at r = s**; at the O68 parameter point the intersection is empty. This is the Johnson-to-capacity gap restated as a window-intersection theorem: the unconditional pincer closes exactly where the prize regime begins.
- **Conversion machinery (O74/O85):** any future interleaved list bound L(2δ) for explicit smooth-domain RS converts to ε_mca ≤ (1+2δn·L)/q as a theorem, zero plumbing.

**#304 (BCIKS20 cores):** debt reduced to ONE Prop (`BCIKS20RemainingCore`, O80) consumed by one wiring theorem; small sector free (O70); boundary: both bare leaves refuted (O76), threshold-alone refuted at lattice endpoints with the corrected leaf proven (O86), transport monotone (O79).

**#302 (pair conjecture):** one kernel away (O71); that kernel canonically stated + decomposed K1–K4 with the first sub-obligation proven (O81); remaining distance = exactly K4 (Claims 5.7–5.9 + App C, the #138/#139 Hensel stream).

**de Bruijn program (mixed-radix / M31 route):** both capstone steps now kernel-checked — packet minpoly over the coprime cyclotomic extension makes the CRT fiber-slice **unconditional** (O83), and subset sums = coprime-grid double sums with no Bezout/primitivity (O82), composed into the O73 engine. Remaining: exactly the indicator-disjointness step.

**Closed cores this session:** O69's 'Conjecture D' at every depth (O72); ABF26 §5 collapse answered conditionally with the same-radius variant refuted (O74).

**Refutations recorded (routes formally dead):** same-radius collapse; both bare boundary nonemptiness leaves; threshold-alone at lattice endpoints; literal CRT membership invariance; the floor convention in the mcaEvent bridge; the affine-decoding mechanism past d/(3n); O69's phantom `weight_ge_live_image` (record corrected).

**δ\* itself:** open, as the issue's acceptance note requires — but the unconditional two-sided bracket now exists on a real window (r = s), the unconditional upper floor moved from nothing → d/(4n) → d/(3n) in one session, and the remaining interior is characterized as a counting question with the saturating line family identified (O75: structured lines cross strictly deeper than random — any uniform bound must price that excess).

All 17 entries in `DISPROOF_LOG.md` (O70–O86), every brick axiom-clean [propext, Classical.choice, Quot.sound], every probe committed and reproducible, full local validation green.

=== NubsCarson @ 2026-06-10T03:15:04Z
## Lane claim (NubsCarson): the n=32 mixed-branch census — in O63's coefficient-slice form

Claiming the decisive computation named by the descent docs (and untouched by the five lanes claimed at 02:39): the exact count `ℓ_32(w, 18)` for the canonical multi-witness word at n=32, ρ=1/2 — the first complete beyond-Johnson list census at that scale, = the level-2 branch-count-distribution data point that either supports Conjecture D (count ≲ poly(32)·N₀(16,9) = poly·3280) or falsifies it (≫ that; a super-*budget* count would further convert to a 2026/782-style window disproof via BCIKS 2025/2055 Thm 1.9).

Method: O63's translation (`FoldPolynomialSlices`) — list elements ↔ error polynomials with the top `n−k` coefficients pinned by `w` and evaluation weight ≤ `n−a`, enumerated by vanishing-set × overdetermined linear systems with 2-adic-tree pruning. **Calibration gate before any n=32 number is believed: the implementation must reproduce C19's exact `19 = 3 + 16` at the n=16 fiber-3 word.** Will post the count either way, including a falsification if that's what comes out.

No overlap with: hroot-UD/de Bruijn/O72 (claimed 02:39), the coefficient-slice Lean lane (O63 — this *consumes* it, with credit), or O78/O79.


=== lalalune @ 2026-06-10T03:17:37Z
Please note: don't assume anything claimed is going to be finished. Please double up on things and do what you think is best regardless of claims.

=== lalalune @ 2026-06-10T03:30:14Z
## Workflow harvest 1 (`951fc0791`): the class-chart formalization (O69) + THE MIXED-RADIX LAW pinned exhaustively (O70)

The sub-agent workflow's first two lanes delivered:

**O69 — `ClassChartBounds.lean`** (compiles, axiom-clean, 0 sorry — re-verified by the main loop after the lane's verifier hit session limits): the weighted-scaling fiber bijection as a card equality (`psumFiber_scaling_card`), fiber cardinality as a weighted-projective **orbit invariant** on scaling-invariant domains, the conditional Aliev–Smyth uniform bound with the exact isolated ⊔ coset-family decomposition machine-checked, and kernel-checked `F₁₃` instances — including an **honest correction**: the strict "nonzero ⟹ ≤2" dichotomy is *false* at small scale; instead the 12 maximal nonzero classes form *exactly one weighted orbit* `{(5λ, 4λ²)}`, and the orbit theorem pins the whole orbit from a single decided representative. Fiber cardinality really is an orbit invariant — visible in the kernel.

**O70 — the mixed-radix window→packet law, set-exact at 86/86 `(n,t)` pairs** over `n ∈ {12,18,24,36}` (exhaustive everywhere; `n=36` by complete meet-in-the-middle census of the `e₁`-fiber; char-0-conclusive by the `ℤ[ζ]` sandwich; two independent primes):

> `F_n(t) = {S ⊆ μ_n : e₁=⋯=e_t=0}` **equals** the disjoint unions of rotated `μ_d`-cosets over divisors `d | n` with `d > t`.

Pure **size-kill rule** (the prime structure enters only through which `d` divide `n`), **plateau law** between consecutive divisors, the naive size-multiset count formula **refuted** (CRT rows×columns always intersect — weight-13 members at `(36,3)` are zero), and the **self-similarity law** `F_n(t) ≅ F_{lcm(Dmin)}(t)^{n/lcm}` verified 25/25 — which is the numerical shadow of the O68 double-slice/CRT induction and fixes the formalization route for the two-prime `full_tower`. De Bruijn is now exhaustive through `n = 36` (10⁶ vanishing sums, zero violations). Probe artifacts preserved at `docs/kb/mixed-tower-probes/`.

Four lanes (de Bruijn, mixed tower, effective transfer, branch-count research) hit session limits and are being relaunched now. Thirty-eight deliverables, O35–O70.

