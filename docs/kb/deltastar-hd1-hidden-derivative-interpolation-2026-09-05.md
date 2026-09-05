# δ* — the hidden-derivative (contact) interpolation route, exactly quantified (2026-09-05)

Standalone issue #1.  Lane: code-theoretic / list-decoding face (the "Meta-Theorem
prerequisite" of the LIT note `deltastar-sw1-lit-2026-09-05.md` §3.1).  Classification
(dossier v4 §6 vocabulary): **exact reductions + reproducible computational evidence**, one
**conditional prize-scale lower witness**, and one **negative structural result** (no slack in
the TR26-164 constraint system).  Production δ* remains **OPEN**.  Nothing here touches the
character-sum CORE; everything is BGK-free.

Probes (all PASS, exact integer / modular arithmetic, no floating point in any gate):

* `scripts/probes/hd1_interpolation_threshold.py` — d = 1 interpolation space dimension and
  exact per-node constraint rank (block/Pascal formula, cross-checked against brute-force
  modular elimination; semantic multiplicity check on random instances over `F_p`).
* `scripts/probes/hd_general_rank.py` — exact per-node rank for any derivative order `d`
  (invariant-block elimination), cross-checked against d = 1 and against unblocked brute force.
* `scripts/probes/hd_true_rank.py` — the *true* per-node rank (vanishing for every genuine
  polynomial through the node) versus the formal TR26-164 system.
* `scripts/probes/hd1_line_ledger.py` — port of the PR #122 seed-count ledger to general
  parameters, reproduction of every PR constant, and a radius optimiser under a given budget.

## 0. Executive summary

1. **The state of the art is the hidden-derivative interpolant.**  ECCC TR26-164
   (Brakensiek–Chen–Putterman–Zhang–Zheng, 2026-09-04) list-decodes plain RS on *any* evaluation
   set over prime fields up to capacity at low rate by interpolating `Q(X, Y₀, Y₁, …, Y_d)` in
   which `Y_j` stands for the (unknown) `j`-th Hasse derivative of the message polynomial.
   better.codes PR #122 (nasqret, merged 2026-08-27) is the `d = 1` version in the affine-line
   setting `Q(X, Y, R, Z)` (`Z` = the line parameter γ), machine-checked in Lean at the
   koalaIRS12 profile (`n = 2¹⁸`, rate 1/2, `q = p⁶`), 10 positions beyond finite Johnson.
2. **Both constraint accountings are exact and identical.**  The per-node rank used by PR #122
   (`localContactRank = 49960`) equals the exact rank of the constraint map; the TR26-164 kernel
   bound is an over-estimate but the *formal* system it bounds has rank equal to the *true*
   rank (vanishing for every genuine polynomial through the node) in every case tested
   (`d ≤ 2`, `m ≤ 10`, LD and line).  There is **no hidden slack** in the constraint system: the
   Taylor identity is the only relation the method can exploit.
3. **`d = 1` clears Johnson by a constant fraction, and only that.**  At rate 1/2 the exact
   least-agreement threshold converges, as the multiplicity `m → ∞` with derivative cap
   `s ≈ 0.31m`, to `A* = 0.97566·√(n(k−1))` (exact continuum limit), i.e. **δ = 0.3101** against Johnson `0.2929`
   (capacity `0.5`).  At the other prize rates the gain is larger (§3).  The line/MCA setting
   converges to the same threshold as the `Z`-degree cap `L → ∞` (deficit `≈ 1.6·10⁵/L`
   positions at `n = 2¹⁸`).
4. **Prize-scale evaluation.**  Under the PR #122 ledger, ported parametrically, the `d = 1`
   scheme certifies `ε_mca ≤ 2⁻¹²⁸` up to **δ ≈ 0.3090** at rate 1/2 for every `n ∈ [2¹⁸, 2⁴⁰]`
   over a prime field of size `≈ 2²⁵⁰` (seed counts `2⁸²…2¹²⁰`, budget `2¹²²`), and reproduces
   exactly the PR's own optimum (`a = 185354`, `(m,s,L) = (13,3,169)`) under the koalaIRS12
   budget.  It certifies **nothing** at the campaign's production shape `|F| ≈ n·2¹³⁸` (budget
   `≈ n`): the interpolation route consumes the prize's field-size slack; the razor-thin
   budget regime the campaign chose has no slack to spend.
5. **Higher derivative order helps only slowly.**  With box caps, `d = 2` is *worse* than
   `d = 1` at equal `m ≤ 16` and overtakes it from `m ≈ 24` by a few hundred positions at
   `n = 2¹⁸` (§4); the TR26-164 asymptotics need `m = d³` and low rate.  Whether the exact-rank
   `d`-hierarchy approaches capacity at rate 1/2 for feasible `m` is left open here (§6).

## 1. Objects (exact statements)

Fix `n, k`, `w := k − 1`, agreement `A`, multiplicity `m`, `D := mA`.

**LD space.**  `Q = span{X^a Y₀^{b₀} Y₁^{b₁} ⋯ Y_d^{b_d} : b_j ≤ s_j (j ≥ 1), a + w b₀ + (w−1) b₁ + ⋯ + (w−d) b_d < D}`.
For `deg P ≤ w`, `Q(X, P, P^{[1]}, …, P^{[d]})` has degree `< D`.

**Node constraint (TR26-164 (25)).**  At `(α, y)`: with `X = α + T`,
`Y₀ = y + Σ_{j=1}^{d} (−1)^{j+1} T^j Y_j + T^{d+1} E`, every coefficient of `T^i`, `i < m`, of
the substituted `Q` (a polynomial in `E, Y₁, …, Y_d`) vanishes.  Lemma 3.1 there: then
`(X − α)^m ∣ Q(X, P, P^{[1]}, …, P^{[d]})` whenever `P(α) = y`.  Verified semantically here
(`hd1_interpolation_threshold.py` §B, random `P` over `F_p`, `d = 1`).

**Exact rank, `d = 1`, LD** (`hd1_interpolation_threshold.ld_rank_formula`).  By translation
`(α, y) → (0, 0)` the rank is node-independent.  A column `(a, b₀, b₁)` with `a < m` maps to
rows `(i, b, e) = (a + b₀, b, b₀ + b₁ − b)`, `0 ≤ b ≤ b₀`, with coefficient `C(b₀, b)`; columns
with `a ≥ m` vanish.  The matrix is block-diagonal over `(i, j) := (a + b₀, b₀ + b₁)` and each
block is a Pascal matrix `(C(b₀, b))` of full rank, hence

    rank Φ = Σ_{i<m} Σ_{j ≤ i+s} min( min(m−1−i, j) + 1 ,  #{b₀ : max(0, j−s) ≤ b₀ ≤ min(i,j), (i−b₀) + w j < D} ).

Cross-checked against brute-force modular elimination at five parameter sets (probe §A).

**Exact rank, general `d`, LD and line** (`hd_general_rank.node_rank`).  The substitution
preserves `g₁ := b₀ + Σ_j b_j (+ l₀)` and `g₂ := a − Σ_j j·b_j`; ranks are computed by modular
elimination inside each `(g₁, g₂)` block.  Cross-checked against the `d = 1` formula and against
unblocked brute force for `d = 2`.

**Line setting (PR #122).**  Monomials `X^a Y^{b₀} R^{b₁} Z^{l₀}`, `b₀ + l₀ ≤ L`, `b₁ ≤ s`,
`a + w b₀ + (w−1) b₁ < D`; node `x` with `(u₀(x), u₁(x)) → (0, 1)` after translation/scaling,
`Y = Z + T(Y₁ + E)`.  Dimension `Σ_{b₁ ≤ s} Σ_{b₀} (D − w b₀ − (w−1) b₁)(L − b₀ + 1)`
(`= 13 096 794 720` at the PR profile, matching `coefficient_count_exact`); the exact rank at
the PR profile is `49960`, matching `contact_rank_exact`, and the PR's closed form
`localContactRank` is an upper bound of the exact rank on a 210-point grid (equal whenever
`s ≲ m/2`), never an under-estimate.

**True rank** (`hd_true_rank.py`).  Replace the formal `(E, Y_j)` by the Hasse derivatives of a
generic series `f = y + T·U`, `U = Σ u_l T^l`; the node condition becomes a polynomial identity
in the `u_l`.  Result: `true rank = formal rank` in all 24 cases tested (`d = 0` reproduces the
Guruswami–Sudan count `m(m+1)/2`).  **Negative result:** the formal system loses nothing.

## 2. Reproduction of PR #122 and of the koalaIRS12 optimum

| quantity | PR #122 (Lean) | this probe |
|---|---|---|
| `coefficientCount` | 13 096 794 720 | 13 096 794 720 |
| `localContactRank` | 49 960 | 49 960 (exact rank 49 960) |
| `totalNumerator` | 228 788 847 483 348 849 235 588 882 | same |
| `gap²` | 2 946 644 089 | same |
| least `a` at `(13,3,169)` | 185 354 | 185 354 |
| best `a` over `m∈{9..17}, s∈{2,3,4}, L∈{100..260}` under `B = q/2¹²⁹` | 185 354 | 185 354 at `(13,3,169)` |

So the PR's parameters are optimal within this family under its own budget: at
`n = 2¹⁸, q ≈ 2¹⁸⁶` the ledger (`seeds ≈ 12 n² w² (yCap·s·L)/gap²`) binds at `yCap·s·L ≈ 10⁴`,
which is why only 10 positions beyond Johnson are reachable there.

## 3. The `d = 1` threshold: exact scans (`n = 2¹⁸`, LD setting)

Least `A` with `dim Q > n · rank Φ`; `A_J := ⌈√(n(k−1))⌉`.

Rate 1/2 (`A_J = 185364`, `δ_J = 0.29289`), best `s` per `m` (always `s ≈ m/4`):

| m | 12 | 16 | 24 | 32 | 48 | 64 | 96 | 128 | 192 | 256 |
|---|---|---|---|---|---|---|---|---|---|---|
| A | 184628 | 183734 | 182866 | 182421 | 181969 | 181741 | 181510 | 181393 | 181276 | 181217 |
| A/√(n(k−1)) | .99603 | .99121 | .98653 | .98413 | .98169 | .98046 | .97921 | .97858 | .97795 | .97763 |

Fit `r(m) = r_∞ + c/m` through `m = 128, 256` predicts `m = 192` to five digits; `r_∞ ≈ 0.9767`
(refined in §3.1), i.e. `δ_∞ ≈ 0.3094` at rate 1/2.

Other prize rates (`m = 128`, LD): rate 1/4 → `δ = 0.5291` (Johnson 0.5000, capacity 0.75);
rate 1/8 → `δ = 0.6792` (0.6464, 0.875); rate 1/16 → `δ = 0.7793` (0.7500, 0.9375).
(Optimal `s` grows to `≥ m/2` at low rate; see `scan_rates2` numbers in §3.1.)

Line setting, `(m, s) = (12, 3)` (LD threshold 184628): `L = 40, 80, 160, 320, 640` give
`A = 189039, 186664, 185631, 185119, 184871` — deficit to LD halves with `L`; the line setting
converges to the LD threshold, so at prize scale (where `L` can be `≥ 2¹⁶`) the MCA threshold is
the LD threshold.

### 3.1 Asymptotic constant and low-rate refinements

Rate 1/2, `n = 2²⁶` (finer `A`-grid), optimal `s/m ≈ 0.30`: `A/√(n(k−1)) = 0.976719` at
`m = 256` and `0.976205` at `m = 512`; the `c/m` extrapolation gives `r_∞ ≈ 0.9757`, i.e.
**`δ_∞ ≈ 0.3101`** at rate 1/2 for the `d = 1` scheme.

Other prize rates (`n = 2¹⁸`, LD, best `s` with `s ≤ 2m` allowed):

| rate | Johnson δ | `m = 64` | `m = 128` | `m = 256` | capacity |
|---|---|---|---|---|---|
| 1/2 | .29289 | .30671 | .30804 | .30871 | .5 |
| 1/4 | .50000 | .52734 | .52909 | .52997 | .75 |
| 1/8 | .64645 | .67773 | .67918 | .67991 | .875 |
| 1/16 | .75001 | .77945 | .78064 | — | .9375 |

**Exact limit (`scripts/probes/hd1_continuum_limit.py`).**  Passing the block-rank formula and
the dimension count to scaled variables gives the `m → ∞` threshold as the root of
`ρ·∫₀^β min(y,σ)(β−y)dy = ∫₀¹dx∫₀^{min(β,x+σ)} min(min(1−x,y), min(x,y)−max(0,y−σ)) dy`,
minimised over `σ = s/m`:

| rate | σ* | `A/√(nw)` | δ_∞ | Johnson | capacity |
|---|---|---|---|---|---|
| 1/2 | 0.310 | 0.97566 | **0.3101** | 0.2929 | 0.5 |
| 1/4 | 0.455 | 0.93759 | **0.5312** | 0.5000 | 0.75 |
| 1/8 | 0.553 | 0.90244 | **0.6809** | 0.6464 | 0.875 |
| 1/16 | 0.661 | 0.87243 | **0.7819** | 0.7500 | 0.9375 |

These agree with the discrete scans (`0.976205` at `m = 512`, `c/m`-extrapolated `0.9757`).

The optimal derivative cap is `s ≈ m/4` at rate 1/2 and `s ≈ m/2 … 0.6m` at rates ≤ 1/8; the
gain over Johnson grows with decreasing rate, as TR26-164's low-rate framing predicts, but
stays a bounded fraction of the Johnson→capacity window (7 %, 12 %, 15 %, 16 %).

## 4. Higher derivative order (`d = 2, 3`), box caps, exact rank

`n = 2¹⁸`, rate 1/2, best `(s₁, s₂)` on the grid `s₁ ∈ {m/8..m/2}`, `s₂ ∈ {m/16..m/4}`:

| m | d = 1 best A | d = 2 best A (s) |
|---|---|---|
| 8 | 186181 (s=2) | 188546 (2,1) |
| 12 | 184628 (3) | 185321 (3,1) |
| 16 | 183734 (4) | 183820 (4,1) |

| 24 | 182866 (6) | 182603 (6,1) |
| 32 | 182374 (10) | 182048 (8,2) |

So `d = 2` overtakes `d = 1` from `m ≈ 24` on, by a few hundred positions at `n = 2¹⁸`
(`m = 32`: ratio .98212 vs .98387).  The second derivative costs weighted
degree `w − 2 ≈ w` per power exactly like the first, but its `T²` weight in the node
substitution removes fewer constraints per added monomial than the dimension it adds, at these
`m`.  TR26-164's gain from `d` needs `m = d³`, the ω-weighted cap `Σ (j−1)c_j ≤ W ≈ 1.15·dm/log(ed)`,
and the low-rate regime where the `Y`-degree budget `B = mA/(k−1) ≈ m/R` is large; at rate 1/2,
`B ≈ 1.4 m` is the binding resource.

## 5. Prize-scale evaluation under the PR #122 ledger (`hd1_line_ledger.py`, `table_d1.py`)

Ledger (all integer, verbatim structure of `ContactAlignmentParameters.lean`):
`seeds·gap² ≤ regular + gap·singular`, `regular = Σ_v cap(v)·max(cut(v), whole(v))`,
`whole(v) = n(n−w)·mixed(v,E,E) + (e+1)(n−w)·gap·mixed(v,E,Z)`,
`E = (1+2w·yCap, w(2s−1), 2wL+1)`, `gap = a − w`, so `seeds ≈ 12 n² w² yCap s L / gap²`.

Rate 1/2, budget `2¹²²` (`|F| ≈ 2²⁵⁰`, `ε* = 2⁻¹²⁸`), grid `m ≤ 512`, `s = m/4`, `L ≤ 2¹⁸`:

| n | 2¹⁸ | 2²⁰ | 2²⁴ | 2²⁸ | 2³⁰ | 2³² | 2³⁶ | 2⁴⁰ |
|---|---|---|---|---|---|---|---|---|
| certified δ | .30896 | .30896 | .30896 | .30896 | .30896 | .30896 | .30896 | .30805 |
| seeds ≤ | 2^82.5 | 2^86.5 | 2^94.5 | 2^102.5 | 2^106.5 | 2^110.5 | 2^118.5 | 2^119.5 |

Johnson is `0.29289`; the certified gain is `+0.016` in δ, i.e. `1.7·10⁷` positions at `n = 2³⁰`.
At `|F| ≈ n·2¹³⁸` (budget `≈ 2^{log n + 10}`) **no radius is certified** for any `n`.

**Honest classification of row 5.**  The interpolation gate is exact (this note).  The ledger's
geometric inputs (`whole_surface_seed_bound`, the cut and singular branches, the
`(n−w)/(a−w)` incidence factor, the no-large-pencil/strong-alignment bridge, and the
alignment-to-MCA adapter `ε_mca ≤ B/q`) are machine-checked in PR #122 **at its fixed profile**;
their general forms in that development carry parameters `(p, w, a, e, n)` explicitly
(e.g. `ContactSurfaceSeedCount.whole_surface_seed_bound`), but the final assembly
`global_selected_count` is stated with the profile constants.  The prize-scale rows are
therefore **computational evidence under a parametrically-read ledger**, not a Lean theorem of
this repository.  Turning one row into an `MCALowerWitness` requires re-running that
development (226 modules, local Mathlib ports) at the new profile.

## 6. What this changes, and what it does not

* The NEC lane (`deltastar-sw1-nec-2026-09-05.md`) established that "any proof must pass the
  BGK wall" is a meta-claim.  This note exhibits the concrete BGK-free route and its exact reach:
  a constant-relative step beyond Johnson at every prize rate, **only** where the field is
  `≳ 2⁹⁰` times larger than the seed count demands, and with the `d = 1` ceiling `δ ≈ 0.309` at
  rate 1/2.  Jo (ePrint 2026/1432) states that a constant-relative improvement on a prescribed
  smooth subgroup is open; under the PR #122 ledger it is achieved for large fields.
* It does **not** move the campaign's production verdict: at `|F| ≈ n·2¹³⁸` the route is
  empty, and the strip/CORE questions (bad count `≤ n`) are untouched.
* **Lean.**  `Frontier/_HD1ContactVanishing.lean` (Mathlib-only, axioms
  `propext, Classical.choice, Quot.sound`): `contact_vanishing` is TR26-164 Lemma 3.1 at
  `d = 1` and `contact_vanishing_line` its PR #122 line form — the formal contact constraint
  of order `m` at a node forces `(X − C α)^m ∣ Q(X, P, P'[, γ])` for every `P` through the
  node.  This is the semantic half of the interpolation step; the counting half (§1) is
  probe-verified.
* Open (ordered by leverage): (i) does the exact-rank `d`-hierarchy with TR26-164-style
  ω-weighted caps beat `d = 1` at rate 1/2 for feasible `m`, and what is the limiting radius as
  `d → ∞`; (ii) a seed-count ledger for `d ≥ 2` (the PR #122 count is specific to
  `Q(X,Y,R,Z)`; heuristically `seeds ≈ n² w^{d+1} Π caps / gap²`, which at `n = 2¹⁸`, `|F| ≈ 2²⁵⁰`
  leaves room up to `d ≈ 3`); (iii) a Lean port of Lemma 3.1 and of the exact rank formula
  (§1) — both are Mathlib-only statements.

## 7. Reproduction

    python3 scripts/probes/hd1_interpolation_threshold.py --quick   # ~2 min; full ~10 min
    python3 scripts/probes/hd_general_rank.py                        # selftest
    python3 scripts/probes/hd_true_rank.py                           # ~5 min
    python3 scripts/probes/hd1_line_ledger.py                        # ~15 min (exact ranks)

Scan drivers used for the tables are inlined in this note's companion log directory of the
session; every number above is reproducible from the three probe modules' public functions
(`ld_min_agreement`, `line_min_agreement`, `min_agreement`, `ledger`, `local_contact_rank`).

## 8. References

* ECCC TR26-164, Brakensiek–Chen–Putterman–Zhang–Zheng, *Algorithmic List Decoding of
  Reed–Solomon Codes up to Capacity in the Low-Rate Regime*, 2026-09-04 (rev. 1 2026-09-05).
* better.codes PR #122, `proximity-prize/proximity-prize`, head `b3fac81a` (nasqret /
  yukon-autoresearch), merged 2026-08-27; files `ContactAlignmentParameters.lean`,
  `ContactCountingLedger.lean`, `ContactSurfaceSeedCount.lean`, `ContactGlobalSelectedCount.lean`,
  `ContactAlignment6401.lean`.
* ABF26 = ePrint 2026/680 rev. 3 (2026-07-06), §1 (grand challenges), §4.3 (Lemma 4.16), §5.
* Jo, ePrint 2026/1432 (rev. 2026-08-19).
* Campaign: `deltastar-sw1-lit-2026-09-05.md`, `deltastar-sw1-nec-2026-09-05.md`,
  `deltastar-DOSSIER-v4-2026-08-16.md`.
