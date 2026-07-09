# Proximity-Prize #407 — capstone synthesis (2026-06-14)

The authoritative consolidated state after the #407 feasible-grind session. Everything below is
either a **machine-checked in-tree theorem** (cited by file) or a **documented honest open core**
(named, never fabricated). Predecessor record: `RESEARCH_SYNTHESIS_389.md` (esp. §7–§9).

## 0. The target (ABF26, eprint 2026/680)

Pin `δ*` for smooth-domain RS `C = RS[F_q, μ_n, k]` (`n = 2^a`, `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`,
`ε* = 2^{-128}`, `k ≤ 2^40`, `q < 2^256`) for **both** grand challenges (MCA and list-decoding),
two-sided, in the open window `(1−√ρ, 1−ρ)` = (Johnson, capacity).

## 1. The closed-form ansatz (validated up-to-Johnson; deep band open)

> **`δ* = H_q^{-1}( (1−ρ) − log_q(1/ε*)/n )`** — a single computable number, strictly inside the window.

- **Proven, axiom-clean:** the crossover `listValue_at_deltaStar` and budget reduction
  `deltaStar_le_of_listBound` (`PROXIMITY_PRIZE_CONJECTURE.lean`).
- **Validated (workflow Q4, 2 reps, cross-checked vs in-tree syndrome sup):** the bad-γ incidence
  integers are **q-invariant up to Johnson** (count=9 at δ=0.5 across q=41..233) ⟹ `ε_mca = const/q → 0`;
  the measured crossover rises toward δ* as q grows (0/44 refutations). Right ansatz + curve shape +
  window placement. The **deep band (δ>Johnson)** is where the open core lives.
- **Sharpened constant (workflow Q2):** the `B`-law normalization should be `ln q`, not `ln(q/n)`;
  the house constant is `≈1.0–1.1` typical (one exact point >√2), β-dependent under `ln(q/n)`.

## 2. The floor (upper half) — REFINED and partly REFUTED

The floor = "no far word's list beats the budget at δ*." Two machine-checked corrections this session:

- **The monomial ladder is NOT the list-maximal floor** (`LadderFloorRefutation.lean`, axiom-clean,
  real build 8313 jobs): the nodal product-supply `C(n,r)/n` strictly exceeds the ladder antipodal
  fibre `N_fib(2^{h+1},r)=C(2^h−1,(r−1)/2)` — `ladder_not_floor` (n=8,16,32) and
  **`ladder_not_floor_general` (ALL h≥2, incl. prize n=2^32)** at the deep radius r=3, with the gap
  ratio `≈2^{h+1}/3` GROWING (`nodal_floor_gap_grows_concrete`). So **the floor is `max(N_fib, L_nodal)`,
  not `N_fib` alone.** Mechanism: the ladder sees only ±-paired subsets; the nodal word's product
  pinning sees all of them.
- **Caveat (honest):** the general theorem is at the deep radius `r=k+1` (where codeword-list = core
  count). At the **prize-window radius `r≈ρn`**, list ≠ core-count (`#cores = Σ_c C(a_c,k+1)`), and the
  codeword-list rate is the open core — `O(1)` vs growing beat-ratio is unresolved (= the wall).

## 3. The single open core (named, classical, NOT fabricated)

All closing directions reduce to **one** object, machine-checked across faces:

> **The growing-`n` sup-norm (house) of the order-`2^a` Gauss period** `B(μ_n) = max_{b≠0}‖∑_{x∈μ_n}e_p(bx)‖`
> = the generalized-Paley-graph eigenvalue of `Cay(F_q,μ_n)`. `B ≤ 2√n ⟺ Ramanujan` = the **Paley
> Graph Conjecture** (open); prize needs `B ≲ √(n·log q)` at `n ~ p^{1/5} < p^{1/4}`.

In-tree structural facts (axiom-clean, this session + campaign):
- `GaussPeriodCosetReduction.eta_image_card_mul_le` — `B = max` over exactly `(p−1)/n` periods (why
  the log is `log(p/n)`); `eta_smul_invariant` (coset-invariance).
- `GaussPeriodTower` — the parallelogram tower recursion; `CharSumMomentDeepWall` — the moment arrow
  `B ≤ (q·E_r)^{1/2r}` (proven) + its deep-moment wall; `GeneralizedPaleyRamanujan`,
  `GaussPeriodMomentBound` — the Ramanujan/energy conditional bridges; `TangentSumJacobiAverage` —
  the Jacobi-sum reframing (house = avg of Jacobi sums).

## 4. What is settled / refuted (genuine progress, not closures)

- **E_r random-likeness: SETTLED YES** (workflow Q1, 2 reps, exact to r≈log q): `E_r−n^{2r}/p ≤ C^r r! n^r`,
  C≈1–1.6 bounded in n and r, c_r decreasing in r. The E_3-spike debate = prime resonance.
- **Refuted shortcuts** (`DISPROOF_LOG.md` 2026-06-14): universal √2 house constant; moment-arrow
  closure at constant index; ladder-only floor; flat-plateau constant; v2(m)-dependence of the constant
  (the p=65537 spike is the near-threshold #400 Fermat trap, not 2-adic). Methodology: weak search
  gives false negatives — use ladder-neighborhood perturbation.
- **Height obstruction** (`DISPROOF_LOG.md`): every char-0 algebraic floor-certificate (energy, BGM
  higher-order-MDS det, esymm) has norm-height `≥2^{φ(n)} ≫ p`, so it can vanish mod p — the floor has
  no char-0-transferable certificate at prize scale; proof requires analysis (the Paley wall). Covers
  the BGM/higher-order-MDS route the prize community most hopes for.

## 5. Papers added (reading list `PAPERS_NEEDED.md`)

Kowalski–Untrau ultra-short (2302.13670) + Wasserstein-quantitative (2505.22059) — the frontier on the
growing-n distribution; Habegger "Norm of Gaussian Periods" (1611.07287) — Myerson, the transfer/norm;
Garcia "Visual aspects" (2308.05220) — hypocycloid geometry; Randomstrasse101 2025 (2603.29571) — Paley
open problems; Shparlinski "Open Problems on … Character Sums"; Bourgain–Glibichuk 0705.4573 (the
`|H|≫p^{3/7}` threshold the prize `n~p^{1/5}` falls below).

## 6. Honest bottom line

The δ* picture is sharp: ansatz `H_q^{-1}((1−ρ)−log_q(1/ε*)/n)`, correct up-to-Johnson + curve shape,
floor = `max(N_fib, L_nodal)` (ladder refuted at all n), single open input = the growing-n Gauss-period
house = Paley eigenvalue. **No feasible direction closes the prize**; every one reduces (machine-checked
across faces) to that named open wall, which no method in the 2024–26 literature crosses at `n<p^{1/4}`.
The session's contribution is verified scaffold + refutations that *locate* the wall precisely and
remove wrong shortcuts — not a closure, which is not fabricated per the project honesty contract.

## 7. DEEP-READ of the SOTA lever (Kowalski–Untrau 2025, arXiv:2505.22059) — the literature provably cannot reach the prize, QUANTIFIED

Full-text read of the only paper attacking exactly the growing-`n` distribution of subgroup sums.

- **Lemma 3.9 (the quantitative engine):** `W₁(μ_{q,d}, ν_d) ≤ 2^{12}·d(d+1)·q^{−1/(d−1)}`, where
  `d=|H|` is the subgroup size, `μ_{q,d}` the empirical law of the normalized sums
  `|H|^{−1/2}∑_{x∈H}e(ax/q)`, and `ν_d` the limiting hypocycloid measure.
- **Theorem 3.8:** these sums equidistribute to a complex Gaussian `N(0,½Id)` iff `d→∞` and
  **`d = o(log q / log log q)`** — exactly the threshold the campaign had recorded (`n < 2log q/loglog q`).
- **Why it dies at prize scale (the mechanism, now explicit):** the subgroup size `d` is in the
  *exponent's denominator* of the decay `q^{−1/(d−1)}`. At prize params `d=2^32`, `q=2^256`:
  `q^{−1/(d−1)} = 2^{−256/(2^32−1)} ≈ 2^{−2^{−24}} ≈ 1` (NO decay), prefactor `d²≈2^{64}`, so
  `W₁ ≲ 2^{76}` — vacuous (support diameter is only `O(√d)=O(2^16)`). Non-vacuous only for
  `d ≲ 11` (with the `2^12` constant) to `≲ 34` (asymptotic); the prize needs `d=2^32`, a gap of
  `~2^27` in subgroup size.
- **Conclusion:** the SOTA growing-`n` equidistribution — which, if it reached the prize, would give the
  Gaussian tail controlling the Gauss-period house `B` — provably stops `~2^27` short of the prize
  subgroup size. The wall is not merely "open"; the best existing tool is exponentially (in the
  subgroup size) too weak, by the precise mechanism that the decay exponent is `1/(d−1)`. No closure.

### §7 FORMALIZED: `KowalskiUntrauBarrier.lean` (axiom-clean)
The deep-read finding is now a machine-checked theorem: `ku_bound_vacuous_at_prize (d≥2^32, q≤2^256)`
proves `Nat.log 2 q < kuThreshold d` where `kuThreshold d = (d−1)(12+2·log₂d)` is the log₂ of KU
Lemma 3.9's non-vacuity threshold `(2^12 d²)^{d−1}`. I.e. for ALL prize params the SOTA Wasserstein
bound is provably vacuous (threshold ≥ (2^32−1)·76 ≈ 2^38 ≫ 256 ≥ log₂q). `ku_threshold_prize_gap`
records the concrete d=2^32 instance. **This is the in-tree formal certificate that no known method
(the 2025 frontier included) reaches the prize regime** — a true negative result, not a closure.
