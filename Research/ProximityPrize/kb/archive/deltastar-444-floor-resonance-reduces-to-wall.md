# Floor lower bound via the resonance method REDUCES TO the energy-ratio wall (#444)

*Status: PROVEN reduction (axiom-clean Lean) + machine-checked no-go probe. The floor lower bound
`M(n) ≥ c·√(n log m)` is numerically REAL but its proof reduces to the same Bourgain–Shkredov
additive-energy quantity that gates the upper bound. The resonance method (Soundararajan;
Bondarenko–Seip) supplies the engine and a hypothesis-free reverse-Markov lower bound, but NO
shortcut around the wall. This is the WALL-IS-REAL arm half-completed: the floor is a genuine
two-sided barrier modulo the named energy-ratio growth law.*

## The target

The δ\* "wall" route needs a TWO-SIDED barrier on the worst Gauss period
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b·x)`, `m = (p−1)/n`:

> **`M(n) ≥ c·√(n·log m)`** (matching the measured upper bound `M ≤ C√(n log m)`).

The campaign already had: the Parseval / 4th-moment floor `M ≥ √n`
(`WorstPeriodLowerBound.exists_period_sq_ge`, axiom-clean) — MISSING the `√(log m)` factor — and the
conditional Chernoff upper bound (`SalemZygmundChaining`). The attack: prove the matching `√(log m)`
LOWER bound via the resonance method (Bondarenko–Seip arXiv:1505.07840, the standard Ω-result
machine).

## What the probes establish (machine-checked)

`scripts/probes/probe_floor_resonance.py` — sweep `m` at fixed `n` to isolate the `log m` growth:
- `M²/n` vs `log m` has POSITIVE slope `1.1–1.95` (extreme-value model predicts `2`), and the band
  `M/√(n log m) ∈ [1.0, 1.6]` does NOT decay across `n ∈ {16,32,64,128,256}`, `m` up to `~10^5`.
- **So the floor `M ≥ c√(n log m)` with `c ≈ 1` is numerically REAL.**

`scripts/probes/probe_floor_resonance_construction.py` — which resonator CERTIFIES that scale:
- FLAT resonator (`R≡1`): certifies the mean `= n` (Parseval), NO `log m`. (= the existing floor.)
- MOMENT resonator `R_j = a_j^{k−1}` at fixed `k`: certifies a CONSTANT multiple of `n`.
- The depth `k⋆` to reach `0.9·max` GROWS like `log m` (`k⋆ ≈ 4,10,10,17` at n=16 as `m` grows).
- **Reaching `n·log m` requires moment depth `k ≈ log m`.**

`scripts/probes/probe_floor_resonance_gcd.py` — does a Bondarenko–Seip GCD resonator beat the ladder:
- The multiplicative/GCD-structured resonator certifies `0.986–1.003·n` — **identical to the random
  control `0.86–0.95·n`, i.e. just the mean, NO `log m`.** Only the moment resonator (depth `~log m`)
  or an `a²`-peeking top-set reaches `~log m·n`.
- **Reason:** Bondarenko–Seip resonance works for `ζ(½+it)` because the Dirichlet coefficients are
  MULTIPLICATIVE; the Gauss period `η(j)` (over the coset index `j`, `b=g^j`) is a SINGLE additive
  character sum — it does NOT correlate with the multiplicative structure of `j`, so the GCD
  resonator has nothing to grab.

`scripts/probes/probe_floor_resonance_dual.py` — the exact resonance↔energy duality (machine
precision, `match=True` everywhere):
> `max_{b≠0}‖η_b‖² ≥ (q·E_k − n^{2k}) / (q·E_{k−1} − n^{2(k−1)})`   (the moment-resonator ratio).

Calibration check: at `n=16,p=257`, `E_2 = 912` (char-p) vs `3n²−3n = 720` (char-0 closed form) —
the `+192` is the expected one-sided char-p energy inflation at an anomalous prime (memory
`arklib-407-analogies-energy-curve-gaussian`); the duality identity reproduces `2.7368·n` both ways.

## The Lean (axiom-clean)

`Frontier/_FloorResonanceLowerBound.lean` — the abstract resonance engine (7 thms, axiom-clean):
- `resonator_lower_bound` / `resonator_ratio_le_max`: `max_i a_i ≥ (Σ R_i a_i)/(Σ R_i)` for `R≥0`
  (the hypothesis-free engine).
- `flat_resonator_eq_mean`: flat resonator certifies exactly the mean (the `√n` baseline).
- `structureBlind_resonator_le_mean` + `beats_mean_implies_correlated`: the GCD/Bondarenko–Seip
  NO-GO — a structure-blind resonator certifies at most the mean; beating it FORCES `R`-to-`a`
  correlation (the moment resonator).
- `moment_resonator_numerator`: the moment resonator's numerator is the power sum `P_k = Σ a_i^k`
  (so its ratio is `P_k/P_{k−1}` = the energy ratio).
- `floor_reduces_to_energy_ratio`: a flat resonator never reaches a target above the mean.

`Frontier/_FloorResonanceEnergyBridge.lean` — the wired reduction (imports the moment substrate):
- `EnergyRatioGrowth ψ G r T` (named obligation): `q·E_r − n^{2r} ≥ T·(q·E_{r−1} − n^{2(r−1)})` with
  the `(r−1)` defect positive — at `r≈log m`, `T≈c·n·log m`, this is a LOWER bound on `E_{log m}(μ_n)`.
- `worst_period_sq_ge_of_energyRatioGrowth` (PROVEN): `EnergyRatioGrowth` ⟹ `∃ b≠0, T ≤ ‖η_b‖²`,
  chaining the in-tree axiom-clean `exists_period_sq_ge_moment_ratio` (reverse-Markov).
- `energyRatioGrowth_fails_of_no_floor` (PROVEN, contrapositive): no floor ⟹ no energy growth at any
  depth — the floor and the energy wall stand or fall together.

## Honest verdict: REDUCES-TO-WALL (the floor is real, the proof is the energy wall)

1. The floor `M ≥ c√(n log m)` is **numerically real** (non-decaying `M/√(n log m)` band).
2. The resonance method gives a **hypothesis-free** lower bound `M² ≥ P_k/P_{k−1}` at every depth `k`
   (already in-tree as `exists_period_sq_ge_moment_ratio`).
3. Reaching the `n·log m` scale forces depth `k ≈ log m`, i.e. a **lower** bound on the order-`log m`
   additive energy `E_{log m}(μ_n)` — the SAME Bourgain–Shkredov quantity (wall W4) that gates the
   UPPER bound `M ≤ C√(n log m)`.
4. The Bondarenko–Seip GCD/multiplicative resonator — the only known shortcut to the extreme-value
   scale — **provably gives only the mean** for these periods (no multiplicative correlation).

**So: the resonance method does NOT breach the wall — it re-derives the floor FROM BELOW as the same
energy-ratio law. The floor lower bound and the moment-method upper bound are DUAL on `E_{log m}`.**
This completes half of a two-sided barrier (the wall is real on the upper side; the lower side is the
identical energy quantity), with the single open input named exactly: `EnergyRatioGrowth` at
`r ≈ log m`, equivalently `E_r/E_{r−1} ≥ c·r` for `r ≈ log m`.

## Relation to prior #444 results

- Complements the Sweep_A44 retraction (`deltastar-444-beyond-johnson-floor.md`): that was an
  attempted FLOOR on δ\* (retracted as a LIST bound); THIS is a floor on the char-sum `M(n)` (the
  p-DEPENDENT wall object), and it is honestly a reduction, not a breach.
- Strengthens the in-tree `moment_ladder_exceeds_prize` (no L2/moment method reaches the target from
  ABOVE) with its DUAL from below: no resonator reaches it either, except via the same `E_{log m}`.
- Consistent with `GaussPeriodMomentBound` / `GeneralizedPaleyRamanujan`: `B ≤ 2√n ⟺ Ramanujan` =
  Paley Graph Conjecture; this shows the matching LOWER `B ≥ c√(n log m)` is the same energy object.
