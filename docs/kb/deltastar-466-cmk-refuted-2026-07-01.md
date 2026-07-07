# #466 Conjecture CMK REFUTED-as-improvement: the abstract moment problem's answer IS the moment bound (lone-spike countermodel)

**Date:** 2026-07-01, round 1, LANE R1.
**Probe:** `scripts/probes/probe_466_cmk_lonespike.py` → `scripts/probes/_out_466_cmk_lonespike.txt`.
**Target:** Conjecture CMK, essay `docs/kb/deltastar-466-essay-novel-mathematics-2026-07-01.md` §2.2 + §3 table + the closing "CMK ∘ TPS" composition.
**Status: numerically decided (certified-bracket countermodel), no Lean claim, no closure of anything arithmetic.**

## The question

CMK claimed: for measures with `q−1` EQUAL atoms (mass exactly `1/(q−1)`), Parseval second
moment (`n(q−n)/(q−1) ≈ n`), and all even moments within `K^r` of Wick–Hermite
(`(2r−1)!! n^r`) to depth `2j = 2⌈ln q⌉`, Christoffel-function / edge-crowding rigidity forces
`M² ≤ C(K)·n·ln q` with `C(K)` **improving** on the raw moment bound. The raw moment bound at
the same data is exactly

```
t_raw(K)² := M²/(n ln q) ≤ min_{r≤j} K·[(q−1)(2r−1)!!]^{1/r}/ln q = 2K·(1+o(1)),
```

optimum at `r ≈ ln q` (interior — deeper moment data is slack). (The folklore `√(2e)` figure is
the un-optimized Stirling variant `[(2r−1)!!]^{1/2r} ~ √(2r)` *without* the `/e`; the exact
optimized constant is `√(2K)`. Both are printed in the probe output.)

## The countermodel (lone spike)

One atom at `M = t·√(n ln q)` + `(q−2)` equal atoms at midpoint-Gaussian-quantile positions
`σ·Φ⁻¹((i−½)/(q−2))`, with `σ` chosen so total second moment equals the Parseval value
**exactly**. Scale-invariant in `n` (only `q = n^4` enters). Computed at `q = 2^40, 2^56, 2^80,
2^120` (i.e. `n = 2^10…2^30`, prize scale included).

**Result (the decisive table, stable across all scales):** with two-sided `K^r`-Wick at the
CMK-stated window `r ≤ L = ⌈ln q⌉`,

| K | t_spike | t_raw | ratio | t_spike²/(2K) |
|---|---|---|---|---|
| 1.05 | 1.452 | 1.452 | 1.0000 | 1.004 |
| 1.20 | 1.552 | 1.552 | 1.0000 | 1.004 |
| 2.00 | 2.004 | 2.004 | 1.0000 | 1.004 |
| 4.00 | 2.834 | 2.834 | 1.0000 | 1.004 |

(numbers for `q = 2^120`; at `q = 2^40` the worst ratio over the K-grid is 0.9979.)
`K_req(t)` behaves exactly as duality predicts: `K_req(t) = max(K_bulk(q), t²/2·(1+o(1)))`,
binding at `r* = L`; `K_bulk(q) = (1/β_L)^{1/L} = 1.034 / 1.024 / 1.017 / 1.011` → 1.

## What this settles

1. **CMK-as-improvement is REFUTED.** For every slack `K` down to the vanishing bulk floor,
   the equal-mass positive measure achieves `t_spike(K) = t_raw(K)·(1−o(1))`. So the abstract
   problem's sharp answer is `C(K) = 2K(1+o(1))` — the moment bound. Positivity + equal masses
   + the full moment sequence add **nothing**. CMK as literally stated ("some C(K)") is
   trivially TRUE via the moment bound, i.e. it collapses to form (A) verbatim — the essay's
   own flagged kill risk ("then CMK = form (A) again"), now determined *as mathematics*.
2. **CMK ∘ TPS dies with it.** The essay's one "genuinely new composition" (a constant-degrading
   `K^r`-Wick input from sieve methods, sharpened to the true edge by moment-problem rigidity)
   is impossible: slack `K` necessarily costs the full factor `K` in `M²`, because the lone
   spike *realizes* the slack. No abstract post-processing of `K^r`-Wick data can beat `√(2K)`.
3. **Depth does not help.** The binding constraint sits at `r ≈ ln q`, interior to the window;
   the countermodel satisfies `K^r`-Wick at ALL depths (window `2L` checked; `r → ∞` slack by
   the same computation). "Go deeper" is not an escape within this abstract format.
4. **Sign/factor question:** improvement factor = 1 exactly. Moreover the essay's proposed
   mechanism, computed correctly, never even threatened an improvement: the exact
   orthonormal-Hermite kernel threshold `t*_H(q) = min{t : K^H_j(t√(ln q)) > q−1}` is
   1.385 / 1.391 / 1.395 / 1.400 at `q = 2^40…2^120`, rising to `√2` FROM BELOW
   (bulk-region asymptotic `K^H_j(x,x) ≍ e^{x²/2}√(2j−x²)` ⟹ `t*_H = √2·(1−O(loglog q/log q))`).
   The Hermite-substituted Christoffel bound *reproduces* the moment bound; the essay's claimed
   constant `t ≈ 1` came from the substitution `He_j(M) ~ M^j`, invalid at `M ≍ √(2j)`
   (needs `M ≫ j`) — a computational error.
5. **Edge crowding never fires.** Small-scale self-consistency demo (`q−1 = 10001` atoms,
   `j = 10`, mpmath Hankel solve): at `t = 1.5 / 1.8` the TRUE Christoffel kernel of the
   countermodel gives `K_j(M,M)/(q−1) = 0.9967 / 1.0000` (bound `mass ≤ 1/K_j` satisfied —
   automatic, since the atom's mass is exactly `1/(q−1)`: the spike deforms its own orthogonal
   polynomials; one atom absorbs one quadrature node), while the Hermite PROXY kernel gives
   `5.8 / 505 × (q−1)` and would "forbid" the atom. The crowding claim (a lonely extreme atom
   needs `Ω(K_j/j)` neighbors) fails: the spike has 0–2 bulk atoms within unit distance vs the
   demanded `~q/log q`.

## The flagged trap, quantified (bulk quantile moment errors)

"Wick to depth `2j`" for the midpoint-quantile atomization of `N(0,n)` means, exactly:
`β_r := m_{2r}^{bulk}/((2r−1)!! n^r) = P(r+½, x_max²/2) + (certified midpoint bracket)`,
`x_max = Φ⁻¹(1−1/(2(q−2))) ≈ 1.36–1.39·√(ln q)` — a tail-truncation **undershoot**:
`β_L ≈ 0.39` (K-cost `2^{1/L} → 1`), `β_{2L} ≈ q^{−c}` (K-cost 1.26–1.31). Brackets: exact
top-2·10⁵ atoms + monotone-integral sandwich via regularized incomplete gamma; validated by
full 16.7M-atom enumeration at `q = 2^24` (containment PASS at documented float tolerance
1e−11; bracket rel width ≤ 6e−7). So the refutation does not leak through edge effects: the
bulk is honestly two-sided `K^r`-Wick with `K → 1` at the CMK window, and the spike constraint
is evaluated with conservative bracket ends.

## What survives

- Form (A) itself (the raw moment bound) — untouched, and now known to be the *exact* answer
  of the abstract equal-mass moment problem.
- The arithmetic question — prove `K^r`-Wick (`E_r ≤ K^r(2r−1)!!n^r`) at depth `r ≈ ln q` for
  the actual `η_b` data — completely untouched. That is still the wall.
- The γ₂-degeneration and vertical-MSS gate bricks (essay §2.1/§2.4) are unaffected; note the
  essay's pattern is now: every "more structure" route (chaining metric, Christoffel
  positivity) computes back to form (A) exactly.

## Watch-fors

- Any future proposal of the shape "positivity/quadrature/log-concavity of the empirical
  spectral measure upgrades a lossy moment input": test it against THIS lone-spike measure
  first — it satisfies equal masses, exact Parseval, all-depth `K^r`-Wick, and saturates the
  moment bound. Only hypotheses that *distinguish* the real `η`-measure from this countermodel
  (i.e. genuinely arithmetic inputs) can beat `√(2K)`.
- `t*_H(q) < √2` at finite `q` does NOT mean the Hermite proxy "improves" anything: the proxy
  substitution is invalid precisely for measures containing the extreme atom (demo item 5).
