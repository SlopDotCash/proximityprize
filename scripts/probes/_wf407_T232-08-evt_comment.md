## wf407 / T232-08-evt — worst-period EVT scaling: numerically VIABLE, but **WALLED** in proof at the bulk-vs-tail gap

**Verdict: walled** (collapses onto the standing sub-Gaussian-MGF / Gauss-sum-equidistribution open core — the BGK/Paley wall).

The EVT reframing `B = max_c‖η_c‖ ≈ √(n log m)` (max of `m=(p−1)/n` quasi-Gaussian periods) is the right *picture*, and I confirmed it holds numerically. But its **provable** structural inputs are not enough to prove the floor, and I have a machine-checked countermodel showing exactly why.

### Numerics (exact, real prime fields, not sampled)
- **Exchangeability fingerprint EXACT:** `Cov(Re η_c, Re η_{c'}) / [−Var/(m−1)] = 1.0000` to 4 dp at every (n,p); `Σ_c|η_c|² = p−n` exact. (`wf407_T232-08-evt_periods.py`)
- **The real periods ARE sub-Gaussian:** worst-direction `B/√(2·Var·ln m) ≤ 1` (range 0.73–1.01), proxy `σ²/n ∈ [0.92,1.09]` FLAT in `m`, tail exponents `k(t) ≥ 1` (thinner than Gaussian). All three SalemZygmund preconditions hold. (`wf407_T232-08-evt_mgf_tail.py`)

### The decisive gap (why proof is walled)
Two algebraic facts, both now axiom-clean in Lean:

1. **The covariance fingerprint is VACUOUS.** For *any* sample, `Σ_{i,j}(Yᵢ−μ)(Yⱼ−μ) − Σ(Yᵢ−μ)² = −Σ(Yᵢ−μ)²` identically (forced by `Σ(Yᵢ−μ)=0`). So `Cov_off = −Var/(m−1)` is an automatic identity carrying **zero** info beyond the variance — the measured "exchangeable white-noise" is just a restatement of the second moment. This is the sharp form of *bulk Gaussianity ≠ tail*.

2. **A spike countermodel matches every proven moment yet has a huge max.** The position-randomized two-value spike (`a = μ−√(v(m−1))`, `b = μ+√(v/(m−1))`) has empirical mean `=μ`, variance `=v`, AND exchangeable covariance `−v/(m−1)` exactly — yet `|a−μ| = √(v(m−1)) = Θ(√(v·m))`, exceeding the EVT scale `√(2v log m)` by `√((m−1)/(2 log m)) → ∞` (≈ **1.4×10¹⁸ at the prize `m=2^128`**). (`wf407_T232-08-evt_definetti_gap.py`, `covMatch=True` at every parameter.)

**⟹ exchangeability + the two proven moments do NOT imply the floor.** Any EVT theorem using only them admits a countermodel violating `max ≤ √(2v log m)` by an unbounded factor. The floor irreducibly needs the **sub-Gaussian MGF** = all higher moments = Gauss-sum joint equidistribution (Rojas–León 2207.12439) = the BGK/Paley √-cancellation wall (the named open input `SubGaussianMGF` in `SalemZygmundChaining.lean`). No new wall; a precise localization of the existing one to the bulk(2-moment)→tail(MGF) boundary, confirming the 407-T17 insight.

### Artifacts
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_T232_08_EVTGap.lean` — `emp_offdiag_sum`, `spike_emean`, `spike_evar`, `evt_gap_exceeds_scale`, `evt_route_walled` (all `[propext, Classical.choice, Quot.sound]`, `pg-iterate` ✅)
- `scripts/probes/wf407_T232-08-evt_{periods,mgf_tail,definetti_gap}.py`
- `docs/kb/wf407-T232-08-evt-walled.md`

🤖 wf407/T232-08-evt · Claude Opus 4.8 · honesty contract held (no fabricated closure)
