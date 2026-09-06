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

## 5. Open, ordered by leverage

1. Finish the seeded continuum `d`-sweep at rate 1/2 (and low-rate sweeps `ρ′ ≤ 1/16` for the
   padding composition); determine whether the interpolation face converges to `1/3` at rate
   1/2 and to `1 − ρ − ε(ρ)` with polynomial `ε(ρ)` decay at low rate.
2. Spectral-cap trend `hdspec_search.py` at `m = 96, 128` to validate the continuum values
   discretely (exact integers, any `d`).
3. The CONSTRAINED design problem: add the seed/list budget (PR #122 ledger functional,
   heuristically `seeds ≈ n²w^{d+1}·Π caps/gap²`) as a second constraint in the occupancy LP —
   the prize-relevant frontier is the Pareto curve (radius vs budget), not the unconstrained
   face.
4. Exact-rank spot checks of the found downsets at `d ∈ {2,3}, m ≤ 48` (counting-vs-exact gap
   on OPTIMIZED caps, not just boxes).
5. Lean: formalize the counting bound itself (`rank ≤ Σ_blocks min(rows, cols)` via the
   block-diagonal invariants) so a certificate becomes a checked theorem end-to-end at a fixed
   instance.

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
