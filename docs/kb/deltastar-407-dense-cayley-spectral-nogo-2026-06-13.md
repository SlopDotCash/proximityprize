# δ* (#407) — the dense-Cayley-spectral toolbox (Lovász ϑ / Krein / CGW / Hoffman) gives NOTHING new

**Status:** honest negative result; NOT a closure. Assesses the *spectral-graph-theory* version of the
dense-regime hope (distinct from the additive-energy refutation in
`deltastar-407-positive-proportion-premise-refuted-2026-06-13.md`). Author: δ* lane (#407),
dense-cayley-spectral angle, 2026-06-13. Reproducible probes listed at the end.

## The angle

`Cay(F_q, μ_n)` is an `n`-regular graph on `q` vertices whose adjacency eigenvalues are the Gauss
periods `η_b`; `B = max_{b≠0}|η_b|` is the non-trivial eigenvalue. The hope: the *dense* graph spectral
toolbox — **Hoffman ratio bound, Lovász ϑ, Krein/association-scheme positivity, Chung–Graham–Wilson
quasirandomness, the Delsarte LP for the sup eigenvalue** — might pin `B ≤ C√(n log(q/n))` where the
*sparse*-graph Alon–Boppana literature stalls.

## Why it fails — five precise obstructions (each verified)

### 0. The graph is SPARSE, not dense (premise false)
With `m=(q−1)/n ≈ 2^128` held constant, density `= n/q = 1/m = 2^{−128}` and `n = q^{μ/(μ+128)} < q^{1/4}`.
So the "dense, Alon–Boppana-doesn't-apply" premise is arithmetically false (cf. the energy note). The
graph is the *thinnest* Cayley graph in the campaign. Everything below holds even granting the dense
machinery full strength anyway.

### 1. Hoffman / ratio / expander-mixing bound the WRONG functional
Hoffman's ratio bound and expander mixing take `λ` as **input** and bound the independence number /
edge distribution. They never *upper-bound* the second eigenvalue. Wrong direction.

### 2. Lovász ϑ of a normal Cayley graph = a function of the spectrum
For a vertex-/edge-transitive (normal) Cayley graph, `ϑ(G)` equals the Hoffman bound
`N·(−λ_min)/(d−λ_min)` — it is computed *from* the eigenvalues, so it cannot certify a value of `B`
smaller than the truth. The SDP optimum is attained at the actual eigenvectors.

### 3. Krein / association-scheme positivity is a CONSEQUENCE, not a constraint
The μ_n-coset relations form the `m`-class **cyclotomic association scheme** on `F_q`; its eigenmatrix
entries are the Gauss periods and its Krein parameters `q^k_{ij}` are the Bose–Mesner structure
constants — **polynomials in the η themselves**. For the scheme that actually exists they are
automatically `≥0`. So Krein positivity is implied by the true η and places no a-priori ceiling on `B`.
Any η-vector meeting the row/column Parseval **sum rules** + multiplicity integrality is scheme-feasible,
and those sum rules are exactly the **moment constraints** (point 5).

### 4. CGW quasirandomness gives only B = o(n) — the WRONG ORDER
Chung–Graham–Wilson: `λ_2 = o(d) ⟺ quasirandom` (codegree concentration). Here `B/n = √(log m/n) → 0`,
so the graph *is* quasirandom — but that only yields `B = o(n)`, i.e. `B ≤ εn`, which is a factor
`√(n/log m) → ∞` **above** the target `√(n log m)`. Worse, the equivalent combinatorial condition
(codegree concentration) is the **additive energy** `E_2(μ_n)` — the same object the energy route
already controls only to the Parseval RMS `√n`. Circular; no new lever.

### 5. The dense SDP for the SUP eigenvalue = the Markov–Krein moment LP (same wall, located)
The strongest honest formulation: among real symmetric coset-value vectors satisfying the certified
moment constraints, maximize `max_j|v_j|`. For a vertex-transitive graph the SDP/ϑ certifies, **for the
sup eigenvalue**, only the moments it can prove PSD — for free, just the **variance** (Parseval). That
gives Cantelli `B ≤ √q`, whose slack vs the true `B` is

> **slack = √q / B ≍ √(m / (2 log m)) → ∞**, verified to track the prediction across
> `n∈{8,16}`, `m` up to ~6000 (`_407_dense_slack_growth.py`): e.g. n=8 slack rises 1.6 → 26 as
> m: 2 → 6000, while `B/√(n ln m)` stays flat ≈ 0.95. **At prize m=2^128 the slack is ≈ 2^60.**

To reach the target you must inject `R ≈ log m` certified even moments; that is *exactly* the moment
route, and the char-`p` defect caps provable char-0 moments at `R≈3` in the prize regime
(`deltastar-389-deep-moment-wall`). The certified-moment LP table (`_407_delsarte_sup_lp.py`):

| log₂m | R=1 (var only) | R=2 | R=3 | R≈log m (ideal) | target √(2 ln m) |
|---|---|---|---|---|---|
| 30 | 3.3e4 | 238 | 50.2 | 6.50 | 6.45 |
| 60 | 1.1e9 | 4.3e4 | 1608 | 9.16 | 9.12 |
| 128 | 1.8e19 | 5.7e9 | 4.1e6 | 13.35 | 13.32 |

(units of √n.) The variance-only certificate is `2^63` at m=2^128; only `R≈log m` moments reach the
target — and those are the unprovable deep moments.

## Net contribution (vs the additive-energy premise note)

The energy note refuted the *sum-product / large-subgroup* reading. This note refutes the *spectral-graph*
reading independently, and adds a sharp structural statement: **every dense-graph spectral certificate for
the SUP eigenvalue of `Cay(F_q,μ_n)` collapses to the certified-moment LP, which is variance-only (⟹ the
trivial √q, slack `√(m/log m)` that GROWS with the prize index) unless fed the deep moments the p-defect
forbids.** The bulk-wide spectrum (RMS √n, `→N(0,1)·√n`) is *why*: the worst-case `B` is an extreme-value
over `m` near-Gaussian eigenvalues, and no low-moment / vertex-transitive SDP sees the far tail. The
non-backtracking spectrum is likewise bulk-wide (`deltastar-407-markovkrein-and-selfimprove-walls`), so
spectral-gap tools that target an isolated second eigenvalue do not apply. **No closure; nothing fabricated.**

## Cross-path lever (the one thing worth carrying forward)
The reduction "dense-SDP for the sup eigenvalue ≡ certified-moment LP, certified ⟺ char-0 energy provable"
makes the deep-moment wall the *single* bottleneck for the entire spectral family too. Any future result
that certifies even ONE extra even moment `E_r` for `r>3` at prize scale (`p~n^5`) — e.g. via an effective
Jacobi-sum equidistribution at constant index (`RESEARCH_SYNTHESIS_407_TANGENT` §7) — would *simultaneously*
move the moment route, the Markov–Krein extremal, AND this spectral LP. They share one input.

## Reproduce
- `scripts/probes/_407_dense_cayley_krein.py` — cyclotomic scheme eigenmatrix + Krein-as-consequence.
- `scripts/probes/_407_dense_spectral_nogo.py` — Hoffman/ϑ/Cantelli vs true B, slack table.
- `scripts/probes/_407_dense_slack_growth.py` — slack ≍ √(m/2lnm) grows; B/√(n ln m) flat ≈0.95–1.2.
- `scripts/probes/_407_delsarte_sup_lp.py` — certified-moment LP table (R=1,2,3,log m) vs target.
