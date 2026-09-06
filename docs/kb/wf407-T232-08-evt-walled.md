# wf407 / T232-08-evt — worst-period EVT scaling: VIABLE numerically, WALLED in proof at the bulk-vs-tail gap

**Date:** 2026-06-14 · **Thread:** 232-T08 / 407-T17 · **Verdict:** **walled**
(reduces to the standing sub-Gaussian-MGF / Gauss-sum-equidistribution open core)

## The question

The Gauss-period floor is `B(μ_n) = max_c ‖η_c‖`, the max over the `m = (p−1)/n` distinct periods
`η_c = Σ_{y∈μ_n} ψ(g^c·y)`. The EVT reframing (in-tree `Frontier/SalemZygmundChaining.lean`,
`WorstPeriodLowerBound.lean`) says `B` is the max of `m` quasi-Gaussian frequencies, so
`B ≈ √(n log m)` (NOT `2√n`). The route's PROVEN structural inputs are that the period family is
**exchangeable white-noise**: one linear constraint `Σ_c η_c = −1` (mean `μ=−1/m`), the
second-moment law `Σ_c ‖η_c‖² = p−n` (per-coord var `v≈n/2`), and the covariance fingerprint
`Cov(η_c,η_{c'}) = −Var/(m−1)`.

**Question:** are those three facts SUFFICIENT to PROVE the EVT floor `B ≤ √(2 v log m)(1+o(1))`?
This would BE the prize floor. **Answer: NO — the route is walled at the bulk-vs-tail gap.**

## Numerics (exact, over real prime fields; not sampled)

`scripts/probes/wf407_T232-08-evt_periods.py` (exact complex periods, `n∈{8,16,32,64}`, ~24 primes):

- **Exchangeability EXACTLY confirmed.** Off-diagonal `Cov(Re η_c, Re η_{c'}) / [−Var/(m−1)] =
  1.0000` to 4 decimals at EVERY (n,p). This is an *algebraic identity*, not statistics (see below).
- **Σ-constraint EXACT.** `Σ_c |η_c|² = p − n` holds exactly (sumEcheck True everywhere).
- **Plateau.** `C = B/√(n ln m)` stable in `[1.0, 1.4]`; `R_dir = maxRe/√(n ln m)` hovers ≈ 1
  (i.i.d.-Gumbel prediction). `R_energy = B²/(n ln m)` runs ≈ 1.2–2.0 (above 1; the deep-moment
  inflation, consistent with the `C²≈1.75` plateau elsewhere in the campaign).

`scripts/probes/wf407_T232-08-evt_mgf_tail.py` (worst-direction MGF + tail exponents):

- **The real periods ARE sub-Gaussian.** `ratio_gumbel = B/√(2·Var_dir·ln m) ≤ 1` in essentially
  every case (range 0.73–1.01); empirical sub-Gaussian proxy `σ²/n ∈ [0.92, 1.09]` and FLAT in `m`
  (n=16 plateau: 0.96–1.03 across m=21→63); tail exponents `k(t) ≥ 1` (thinner than Gaussian),
  `k(t)→inf` at t≥2 (no period beyond 2.5 sd). So all three SalemZygmund preconditions hold
  empirically — the route is *numerically viable*.

## The decisive gap test (why it is WALLED in proof)

`scripts/probes/wf407_T232-08-evt_definetti_gap.py` constructs an EXPLICIT adversarial family:
the **position-randomized two-value "spike"** (one coord `a`, the rest `b`). For target
`(mean μ=−1/m, var v=n/2)` it matches:

- mean `= μ` exactly,
- variance `= v` exactly,
- off-diagonal covariance `= −v/(m−1)` exactly (`covMatch=True` at every (n,m)),

yet its **maximum is `|a| ≈ √(v(m−1)) = √(n·m/2)`** — Θ(√m), NOT √(log m). The ratio
`|a|/√(2v ln m) = √((m−1)/(2 ln m))` **blows up unboundedly** (1.65→8.59 as m=16→1024; ≈1.4×10¹⁸
at the prize `m=2^128`).

**Conclusion:** exchangeability + the two proven moments do NOT imply the EVT floor — a family
satisfying all of them can have its max larger by an arbitrarily large factor. The floor needs
strictly more: the **sub-Gaussian MGF**, which constrains ALL higher moments = Gauss-sum joint
equidistribution (Rojas–León 2207.12439) = the BGK/Paley wall = the project's standing open core.

### The sharp structural reason: the covariance fingerprint is VACUOUS

For ANY real sample `Y:Fin m→ℝ` with mean μ, the off-diagonal sum of centered products equals
`−Σ(Yᵢ−μ)²` identically (because `Σ(Yᵢ−μ)=0`, so `(Σ centered)² = 0 =` diagonal + off-diagonal).
Hence `Cov_off = −Var/(m−1)` is an **automatic algebraic identity**, carrying ZERO information
beyond the variance. The "exchangeable white-noise" structure 407-T17 measured (`cov_ratio=1.0000`)
is therefore not extra leverage — it is just a restatement of `Σ|η_c|²=p−n`. This is the precise
sense of "bulk Gaussianity ≠ tail (the gap IS the wall)" from the 407-T17 row.

## Formalization (axiom-clean Lean brick)

`Research/ProximityPrize/Frontier/WF407_T232_08_EVTGap.lean`
(`pg-iterate.sh` ✅ OK; all theorems audit `[propext, Classical.choice, Quot.sound]`):

- `emp_offdiag_sum` — Fact 1: off-diag centered-product sum `= −Σ(Yᵢ−μ)²` for every sample
  (the covariance fingerprint is vacuous).
- `spike_emean`, `spike_evar` — the spike with `spikeVal=μ−√(v(m−1))`, `baseVal=μ+√(v/(m−1))`
  has empirical mean `=μ` and variance `=v` exactly.
- `evt_gap_exceeds_scale` — the spike's centered deviation `√(v(m−1)) ≥ √(2v log m)` whenever
  `2 log m ≤ m−1` (always, for `m≥7`; trivially at `m=2^128`).
- `evt_route_walled` (MAIN) — the assembled countermodel: the spike matches mean, variance, AND
  the exchangeable covariance, yet `|Y(i0)−μ| = √(v(m−1)) ≥ √(2v log m)`.

## Verdict & what remains

**WALLED.** The EVT route is numerically sound (the real periods are genuinely sub-Gaussian) but
its provable inputs (exchangeability + 2 moments) are demonstrably insufficient — a machine-checked
countermodel violates the floor by `√((m−1)/(2 log m))→∞`. The route collapses onto the SAME open
core as faces 3↔4 of the δ* programme and `GaussPeriodMomentBound.lean`/`SalemZygmundChaining.lean`:
the **per-period sub-Gaussian MGF** (`SubGaussianMGF`), i.e. effective Gauss-sum joint
equidistribution / the BGK–Paley √-cancellation wall. No new wall; a precise localization of the
existing one to the bulk-vs-tail boundary.

What would unwall it: an *effective/uniform* MGF bound over the `m−1` index-`m` characters
(currently only the *qualitative* joint independence of Gauss sums is known, Rojas–León). That is
exactly the named open input `SubGaussianMGF` in `SalemZygmundChaining.lean`.

## Artifacts
- `scripts/probes/wf407_T232-08-evt_periods.py`
- `scripts/probes/wf407_T232-08-evt_mgf_tail.py`
- `scripts/probes/wf407_T232-08-evt_definetti_gap.py`
- `Research/ProximityPrize/Frontier/WF407_T232_08_EVTGap.lean`
