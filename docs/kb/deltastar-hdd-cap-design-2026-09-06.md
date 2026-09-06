# δ* — the hidden-derivative hierarchy at every order: Lean core, cap-design instruments, TR26-164 rev. 1 (2026-09-06)

Standalone issue #1, code-theoretic (BGK-free) lane; successor to
`deltastar-hd1-hidden-derivative-interpolation-2026-09-05.md`.  Classification (dossier v4 §6
vocabulary): **two new axiom-clean Lean theorems**, **three validated exact/sound instruments**,
**reproducible computational measurements** (counting-bound interpolation thresholds), one
**documented false-feasibility failure mode**, and **literature intelligence with exact
quantification**.  Production δ* remains **OPEN**; nothing here touches the character-sum CORE.

## 1. Lean: the interpolation core is now order-uniform (axiom-clean)

* `Frontier/_HDdContactVanishing.lean` — `contact_vanishing_d`: TR26-164 Lemma 3.1 at every
  derivative order `d`.  The truncated Möbius inversion `X^{d+1} | f − f(0) − Σ_{j<d} (−1)^j
  X^{j+1} f^{[j+1]}` is proved coefficientwise from the alternating binomial sum
  (`X_pow_dvd_mobius_tail`), and Hasse derivatives commute with the Taylor shift
  (`shift_hasseDeriv`).  Normalization: the node substitution uses the block `T^d · E` (the
  formal `E` absorbs one power of `T`, exactly as in the `d = 1` file), under which the
  constraint "every monomial has `T`-degree + `E`-degree ≥ m" has the SAME constraint set as
  TR26-164 (25) (bijection `t = t′ + e` on support monomials); it also matches rev. 1's
  eq. (4) (`Y₀ = y + Σ (−1)^{j+1} T^j Y_j + T·E` with `T^d | E`).
* `Frontier/_HDdInterpolationCore.lean` — `exists_interpolant_d`: TR26-164 Proposition 3.13 at
  every order, with the node-rank sum left explicit: if
  `Σ_{α∈S} rank(nodeMapD_α|Qs) < dim Qs` and `D ≤ A·m`, a nonzero `Q ∈ Qs` satisfies
  `Q(X, P, P^{[1]}, …, P^{[d]}) = 0` for every `deg ≤ w` polynomial with `≥ A` agreements.
  Supporting: `wdegD` (weights `(1, w, w−1, …, w−d)`), `natDegree_specializeD_lt`,
  `specializeD_eq_zero_of_agreement` (coprime `(X−α)^m` product), `nodeMapD_eq_zero_iff`.
  Axioms of all headline theorems: `propext, Classical.choice, Quot.sound` only
  (`scripts/pg-iterate.sh`, 2026-09-06).

Consequence: at EVERY `d`, theorem + a rank computation = the full interpolation step.  The
probes below compute (exactly) or soundly bound that rank sum.

Late-session completions (same day, all axiom-clean): `_HDdCountingBound.lean`
(`finrank_span_range_le_sum_min`, `finrank_span_range_eq_restrict`),
`_HDdNodeTranslation.lean` (`contactSubstD_translate`), `_HDdOriginGrading.lean` (the
`(g₁,g₂)` bigrading through `weightedDegree_of_mem_support_contactSubstD`),
`_HDdNodeRankAssembly.lean` (`originNodeFamily_rank_le_blockCount`), and
`_HDdTranslateStability.lean` (`support_translateD_monomial`,
`translateD_monomial_mem_span` — downward-closed monomial spans are translation-stable,
reducing every node to the origin block count).  Eleven theorems total; the chain from an
audited integer certificate to `exists_interpolant_d`'s hypothesis is formal at every named
step, with only per-instance finite bookkeeping (kernel-infeasible at scale, audited by
`hdd_certificates.py`) remaining.

## 2. Instruments (all selftested against the existing exact probes)

1. **`hdinf_cap_search.py`** — the counting rank bound `Σ_blocks min(#rows, #cols)` evaluated
   in `O(|cap| + grid)` per candidate: per-`bs` column RECTANGLES in block coordinates
   `(g₁, g₂) = (b₀ + Σb_j, a − Σ j·b_j)` via 2-D difference arrays (each `bs` contributes ≤ 2
   rectangles when `m ≤ w`), plus a cap-independent row-count DP.  On top: local search over
   arbitrary DOWNSETS of `ℕ^d` — the true design space; boxes/simplices/ω-caps are only warm
   starts.  Selftest: exact agreement with `hd_fast_bound.rank_bound(exact_rows=False)` and
   `dim_space` on the reference grid; sound (≥ exact `node_rank`) everywhere tested.
2. **`hdinf_continuum_lp.py`** — the exact `m → ∞` limit as a 2-D occupancy problem: every
   functional depends on a cap point `c` only through `(S, J) = (Σc_j, Σ j·c_j)`, so the cap
   design space collapses to `0 ≤ o(S,J) ≤ ν_d(S,J)` with `ν_d` and the row density computed
   by ray-convolution DPs LINEAR in `d`.  `ρ·IQ − IR` is convex in `o` (bang-bang optima),
   solved by iterated marginal pricing; midpoint grids + Richardson `h`-ladder.  Validation:
   reproduces `hd1_continuum_limit.py` to ≤ 4·10⁻⁵ in the ratio at rates 1/2, 1/4, 1/8.
3. **`hdspec_search.py`** — exact-integer SPECTRAL caps: `cap(Ω) = {bs : (Σb, Σjb) ∈ Ω}` for a
   set `Ω` of integer pairs; multiplicities by unbounded-knapsack DP; `W = w·S − J` exactly, so
   the threshold evaluation is exact at ANY `d` in 2-D.  Selftest: spectral wedge ≡ simplex
   cap agrees with the `hd_fast_bound` reference bisection.

## 3. Measurements (rate 1/2, `n = 2¹⁸`, counting bound ⇒ sound interpolation certificates)

* **Free cap shapes beat every previously tried family at every `(d, m)`.**  Downset search
  (counting bound), Johnson `A_J = 185364`: `d=2, m=32`: `A = 180770` — better than the
  EXACT-rank box optimum recorded in the 09-05 note at the same `m` (`182048`); `d=3, m=32`:
  `179807`; `d=3, m=64`: `178609` (`δ = 0.31866`, ratio `0.96357`), already past the `d=1`
  `m→∞` limit `0.3101`.  `d=3` `m=48` best `179548`.  The optimal downsets are neither boxes
  nor ω-simplices (e.g. per-axis maxima `[38, 18, 11]` at `d=3, m=64`).
* **Continuum `d`-sweep** (free occupancy, Richardson): `δ_∞(d)` at rate 1/2 =
  `0.31010 (d=1), 0.31815–0.32038 (d=2), 0.32301 (d=3), 0.32577 (d=4), 0.32834 (d=6)`;
  increments decay roughly geometrically.  `d ≥ 8` values require the seeded optimizer (first
  runs hit initialization failure); sweep in progress.  The naive extrapolation lands near
  **1/3** — numerically close to the SYZ conditional strip bracket `δ* ≈ 1/3` at rate 1/2
  (`_SYZ46CensusBridge`), which would be a structural rhyme between the BGK-free interpolation
  face and the strip/MCA face; NOT established, recorded as a target.
* **False-feasibility failure mode (documented, fixed).**  The unconstrained occupancy LP can
  return `β < 1` (beyond capacity) via mass at the `J`-grid boundary whose column windows fall
  off-grid (rank cost silently dropped, margin ~10⁻³³ on mass ~10⁻²⁸).  Fixes: occupancy
  masked to fully-on-grid windows, and a margin tolerance.  Post-fix validation unchanged.
  Discrete cross-check: single-`(S,J)`-group caps at `d=4, m=12` are exactly evaluated and NOT
  feasible below Johnson (`dim ≪ n·rank`, exact = bound there).  Lesson recorded: the
  interpolation-step threshold measured here is a NECESSARY face of the method; decoding
  claims also need the root-finding/list side (mild for plain LD — see §4 — but binding at the
  prize's `ε* = 2⁻¹²⁸` budget).

## 4. TR26-164 revision 1 (2026-09-05): all constant rates, and what it costs

* **Corollary 1.2/5.1 (new in rev. 1, reduction credited to Alrabiah–Goyal–Guruswami):** every
  RS code of rate ≤ R over a prime field `q ≥ C(R,δ)·n`, ARBITRARY distinct evaluation points,
  is efficiently list decoded from a `1 − R − δ` fraction of errors, list `n^{O_{R,δ}(1)}`.
  The reduction is PADDING: extend the evaluation set to `N = Θ(k/η)` points, pad the received
  word, decode at low rate `k/N ≤ (1−θ)η` by Theorem 4.1, prune.  So the 09-05 note's line
  "TR26-164 asymptotics need low rate" is now historical: capacity holds at ALL constant
  rates, and the LOW-RATE EXCESS is the universal currency: excess `ε(ρ′) := A*/k − 1` at low
  rate `ρ′` transfers to rate `R` as radius `≈ (1−R) − R·ε` at field cost `q ≳ k/ρ′`.
* **Cost through the paper's constants:** Theorem 4.1 needs `k/n ≤ (1−θ)ε`,
  `ε < (θ³(1−θ)^{1−θ}/768)^{(5+θ)/θ}`, `q ≥ max(n, 4ε^{1−9/θ}n/k)`, `d = ε^{−3/θ}`, `m = d³`;
  the first Johnson-beating δ at rate 1/2 (needs `δ < √R − R ≈ 0.207`, so `θ ≤ 0.143`) costs
  `η ≲ 2^{−655}`, i.e. `q ≳ n·2^{655}` — the campaign's production shape `|F| ≈ n·2^{138}` is
  out of reach of the BLACK-BOX constants by ~2^{500}.  (This sharpens, with numbers, the LIT
  note §5 item 1 prediction.)  The constants are analysis artifacts; the instruments of §2
  measure the method's true thresholds instead (already `δ = 0.3187` at `d=3, m=64`, and §3's
  continuum trend, at ANY prime `q ≥ k` for plain LD — see next).
* **Kopparty side conditions are mild (Theorem 2.1 = [Kop15] Thm 4.3):** `q ≥ k > d` prime,
  `deg_{Y_i} Q < q`, weighted degree `< q²` ⇒ all roots found in `q^{O(d+1)}` time, list
  `≤ q^{4d+6}`.  Composition: counting-feasibility certificate at `(n,k,A,m,d,cap)` (§2/§3) +
  `exists_interpolant_d` (§1) + Kopparty ⇒ RS list decoding at rate 1/2 beyond Johnson
  (`δ ≈ 0.319` measured; continuum face → ≈ 1/3) for ANY prime `q ≥ k`, list `q^{O(d)}`.  This
  does NOT resolve any prize box: the Grand LD budget is `Λ ≤ 2^{−128}·q`, far below
  `q^{4d+6}`; prize-budget lists need PR #122-style tight ledgers (open for `d ≥ 2`, = open
  item (ii) of the 09-05 note).

## 3.5 Certified thresholds (spectral paramscan + refinement; bignum-verified records)

All values: counting bound ⇒ sound interpolation certificates, field-uniform, `n = 2¹⁸`;
`verify_exact_int` re-checks the records with Python bignums end-to-end (no floats).

| rate | Johnson δ | best certified δ | at (d, m) | capacity | record verification |
|---|---|---|---|---|---|
| 1/2 | 0.29289 | **0.33791** (wedge) / 0.338+ refining | (12, 128) | 0.5 | `dim = 173575795916105963870 > n·rb = 173574747307010686976` at `A = 173563`, infeasible at `A−1` |
| 1/8 | 0.64645 | **0.72008** | (8, 96) | 0.875 | refined Ω (saved) |
| 1/16 | 0.75 | **0.80927** | (6, 128) | 0.9375 | wedge value `A = 50264` (δ = 0.80826) bignum-verified; refined 49998 |

Calibration: on OPTIMIZED caps the counting bound is nearly exact — `d=2, m=32` downset
winner: counting `A = 180770` vs exact-rank `A = 180738` (gap 0.018%; boxes showed 2.4%),
and `d=6, m=8` truncated wedge: 0.12%.  The certified face is essentially the true
exact-rank face on the searched family.  Padding vacuity (measured): the rate-1/16 face
(ratio 0.763; capacity regime would be 0.25) is far from the `A ≈ k` regime, so the AGG
padding composition is strictly worse than the direct face at every measured parameter —
padding becomes relevant only if a low-rate face ever approaches capacity.

`(d, m)`-matrix at rate 1/2 (δ, refined): d=6: .31921/.32410/.32663/.32939/.33064 at
m=32/48/64/96/128; d=8: .32603/.32888/.33241/.33417 at m=48/64/96/128; d=12:
.33196/.33624/.33791+ at m=64/96/128.  Monotone in both parameters; `c/m` fits give
`δ_∞(d) ≈ 0.3344 (d=6), 0.3395 (d=8), 0.3429 (d=12)`, still rising in `d` with a
decelerating tail suggesting a counting-face limit ≈ 0.345–0.35 at rate 1/2 — but the
counting-vs-exact gap also grows with `d` (composition-superset rows), so the TRUE
exact-rank face sits above the counting face at large `d`.  Granularity warning: the
continuum solver needs `m ≫ d` (cap entries `~ m/d` must be large); at `d ≥ 12` trust the
discrete spectral instrument only.

## 3.6 The window-fraction law, and the death of two scaling hypotheses

Two clean negative findings pin the method's practical shape:

1. **`m = d³` does NOT unlock capacity at prize rates.**  At rate 1/2, `(d, m) = (8, 512 = d³)`
   gives `δ = 0.33675` — barely above `(8, 128)` (0.33417) and BELOW `(24, 128)` (0.34321,
   scan continuing); at rate 1/16, `(8, 512)` gives `δ = 0.82105` vs capacity 0.9375.  The
   `m`-direction saturates fast (beyond `m ≈ 16d` gains are ~0.003 per doubling); the
   `d`-direction grows the face only ~0.005 per doubling at `m = 128`.  Within the whole
   parameter space reachable at `n = 2¹⁸` (`d ≤ m ≤ w`), the counting face at rate 1/2
   cannot exceed ≈ 0.40, and realistically plateaus ≈ 0.35.
2. **TR26-164's capacity regime is purely asymptotic.**  Constraint (26) caps the usable
   radius parameter at `ε < (θ³(1−θ)^{1−θ}/768)^{(5+θ)/θ} ≲ 10⁻⁴³` even at `θ = 1/2` — the
   paper's capacity phenomenon lives at rates below `~10⁻⁴³`, twenty-plus orders below any
   prize rate.  At the four prize rates the method's TRUE quantitative content is exactly
   what the instruments measure.

**The `d`-hierarchy SATURATES (answer to the 09-05 note's open item (i)).**  At `m = 128`,
rate 1/2: `δ(d) = 0.33417 (8), 0.33791 (12), 0.34321 (24), 0.34605 (32), 0.34819 (64),
0.34827 (96), 0.34822 (127)` — the face converges at `d ≈ 64` (the winning wedge
`(smax, jcap) = (173, 538)` is IDENTICAL for `d = 64, 96, 127`: derivative orders beyond
the `J`-budget are simply unused).  The remaining axis is `m`: at `d = 32`,
`m = 128 → 256` gains `0.34605 → 0.35175` (bignum-verified, tight).  Extrapolating the
`m`-doublings, the full `(d, m) → ∞` counting face at rate 1/2 is
**`δ_∞ ≈ 0.357 ± 0.004`** — 22 % beyond Johnson in absolute radius, ~31 % of the
Johnson→capacity window, and decisively NOT capacity.

**Window-fraction law (measured, `n = 2¹⁸`, best certified):** the face crosses a bounded,
slowly-growing fraction of the Johnson→capacity window at every prize rate —

| rate | Johnson | face (best) | capacity | window fraction (lower bound) |
|---|---|---|---|---|
| 1/2 | 0.29289 | **0.35498** (d=32, m=384; bignum-verified, tight) | 0.5 | 30 % (near-converged; limit ≈ 31–32 %) |
| 1/4 | 0.5 | **0.57140** (d=8, m=192; bignum-verified, tight) | 0.75 | 29 % (unconverged in (d,m)) |
| 1/8 | 0.64645 | **0.72106** (d=8, m=128 refined; wedge 0.72004 verified) | 0.875 | 33 % (unconverged) |
| 1/16 | 0.75 | **0.84377** (d=32, m=256; bignum-verified, tight) | 0.9375 | 50 % (still growing) |

The fractions are LOWER BOUNDS increasing along the (d,m) frontier, and they grow as the
rate falls — the finite-parameter shadow of the ρ→0 capacity phenomenon.  Only rate 1/2 is
near its (d,m)-limit (`δ_∞ ≈ 0.357`, §above).  n-STABILITY: at `(d,m) = (32,128)`, rate 1/2,
`δ = 0.34608 / 0.34605 / 0.34604` at `n = 2^16 / 2^18 / 2^20` — the face is n-independent to
`~10^-5` in the ratio, so these charts describe production `n = 2^30` directly.

The padding composition is strictly dominated by the direct face at all measured parameters
(§ above), so this law is currently the quantitative frontier of the entire hidden-derivative
approach at prize shape.

## 4.5 The T5.1 √-wall: the LD face cannot reach beyond-Johnson MCA through the known transfer

The in-tree LD⇒MCA chain (`RSLambdaSubJohnsonMCA.lean`, consumer
`linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_witnessCover_hypothesis` = ABF26 T5.1 shape)
converts a list bound at radius `δ` into `ε_mca` at radius `1 − √(1−δ+η)`.  The loss is
structural: LD AT CAPACITY (`δ = 1−ρ`) transfers to MCA radius exactly `1 − √ρ` = Johnson, for
every rate.  Hence NO strength of the interpolation face can cross to beyond-Johnson MCA via
this transfer — with `η → 0` the map `δ ↦ 1 − √(1−δ)` sends `[0, 1−ρ]` into `[0, 1−√ρ]`.
Beyond-Johnson MCA remains exactly the CORE wall; the face measured here is progress on the
GRAND LD box's territory (plain-RS layer; the box itself is `m`-interleaved with budget
`Λ ≤ 2^{−128} q`, which also rules out Kopparty-scale lists).  Recorded so no future lane
re-attempts this composition.

## 5. Open, ordered by leverage

1. Finish the seeded continuum `d`-sweep at rate 1/2 (and low-rate sweeps `ρ′ ≤ 1/16` for the
   padding composition); determine whether the interpolation face converges to `1/3` at rate
   1/2 and to `1 − ρ − ε(ρ)` with polynomial `ε(ρ)` decay at low rate.
2. Spectral-cap trend `hdspec_search.py` at `m = 96, 128` to validate the continuum values
   discretely (exact integers, any `d`).
3. The CONSTRAINED design problem: add the seed/list budget (PR #122 ledger functional,
   heuristically `seeds ≈ n²w^{d+1}·Π caps/gap²`) as a second constraint in the occupancy LP —
   the prize-relevant frontier is the Pareto curve (radius vs budget), not the unconstrained
   face.  Quantified: the box-product shape charges the `d=12` wedge winner ~`2^62` in cap
   product alone (`Π_j min(Smax, Jcap/j)`), putting high-`d` caps hopelessly over any
   `|F| < 2^256` budget under the PR #122 counting SHAPE.  Identified novel tool (untried in
   this campaign): a SPARSE-elimination ledger — BKK/mixed-volume bounds see the cap's Newton
   polytope, exponentially below the box product for wedge caps; reworking the ledger's
   resultant construction sparsely is the gateway to prize-budget `d ≥ 2` claims.
   Measured sparse-vs-box slack on the record caps: `2^25.2 (d=12)`, `2^65.1 (d=24)`,
   `2^105.9 (d=32, m=256)` — but the ledger's `w^{d+1}` degree factor is NOT improvable by
   cap sparsity (each hidden-derivative variable carries weight ~`w` in the elimination),
   and at production scale (`w = 2^29`) it alone exceeds the `2^122` budget from `d = 4` on.
   So the prize-budget MCA lane through this route is confined to `d ≤ 3`; the honest BKK
   target is pushing the `d = 1` certified `δ ≈ 0.3090` (at `|F| ≈ 2^250`) toward
   `≈ 0.31–0.32` with sparse `d = 2, 3` caps — real but bounded.
   MEASURED (exact ranks): the `s₂ ≤ 1` sparse `d = 2` family
   `{(b₁ ≤ s₁, 0)} ∪ {(b₁ ≤ s₁′, 1)}` beats `d = 1` at every ledger-feasible `m`:
   `m = 13`: `A = 183560` vs `184365` (Δratio −0.44 %); `m = 16`: `182941` vs `183734`;
   `m = 20`: `182474` vs `183243`.  Its ledger surcharge is a single `w`-factor (`s₂max = 1`),
   inside the `2^250` budget slack.  Porting the PR #122 geometric ledger to `d = 2`
   (one extra derivative variable) is therefore the single concrete step standing between
   the campaign and an improved prize-scale lower witness `δ ≈ 0.312–0.314` at `|F| ≈ 2^250`.
   In contrast the BOX `d = 2` family only overtakes `d = 1` from `m ≈ 24` (over budget):
   the box scans said `s₂ = 0` at `m ≤ 16`, and only sparsity rescues `d = 2` in-budget.
4. Exact-rank spot checks of the found downsets at `d ∈ {2,3}, m ≤ 48` (counting-vs-exact gap
   on OPTIMIZED caps, not just boxes).
5. Lean: formalize the counting bound itself (`rank ≤ Σ_blocks min(rows, cols)` via the
   block-diagonal invariants) so a certificate becomes a checked theorem end-to-end at a fixed
   instance.

## 5.4 Instrument limitation: the LINE counting bound is structurally loose

`hdspec_search.line_feasible_int` (sound, exact-integer, `l ≤ L` row cap) is ~2× loose in
THRESHOLD at `d = 2`-sparse shapes (e.g. `m = 16`, `s₂ ≤ 1`: line-bound `δ ≈ 0.153` vs
exact-LD `0.302`), unlike the LD counting bound (near-tight on optimized caps).  Mechanism:
the `Z`-expansion's binomial structure makes line blocks heavily rank-deficient — precisely
why PR #122 needed its exact `localContactRank` closed form.  Line-lane design scans must
use exact ranks (`hd_general_rank.node_rank` with `L`) or a ported closed form; counting
scans of the line system are only useful as sanity ceilings.

## 5.5 Started: the d = 2 ledger port

`scripts/probes/hd2_ledger_projection.py` — a HEURISTIC arithmetic extension of the PR #122
ledger to the sparse `s₂ ≤ 1` family (each branch gains one agreement-vector slot; shape
assumption explicit in the docstring), with the radius side EXACT (`node_rank`, `d = 2`,
line setting).  Its output sizes the payoff of the real geometric port (the actual next
step); nothing from it may be reported as a certified witness.

## 6. Reproduction

    python3 scripts/probes/hdinf_cap_search.py selftest      # rectangles vs references
    python3 scripts/probes/hdinf_continuum_lp.py validate    # d=1 continuum reproduction
    python3 scripts/probes/hdspec_search.py selftest         # spectral wedge cross-check
    python3 scripts/probes/hdinf_cap_search.py trend --rate 2
    python3 scripts/probes/hdinf_continuum_lp.py sweep --rho 0.5 --ds 1,2,3,4,6,8,12 --jmax 12
    scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_HDdContactVanishing.lean
    scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_HDdInterpolationCore.lean

## 7. References

* ECCC TR26-164 rev. 1 (2026-09-05): Corollary 1.2/5.1 (AGG padding), eq. (4), Theorem 2.1,
  Theorem 4.1 with (26).
* [Kop15] Theorem 4.3 (univariate multiplicity root finding).
* Campaign: `deltastar-hd1-hidden-derivative-interpolation-2026-09-05.md` (exact `d=1` state),
  `deltastar-sw1-lit-2026-09-05.md` §5 (the "ECCC-quantify" lane brief), dossier v4.
