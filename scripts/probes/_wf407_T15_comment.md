## wf407/T15-cosh — cosh-MGF root-free saddle inequality: **WALLED to W4** (deep-moment wall)

**Thread:** 407-T15 / A03. **Verdict: WALLED** to the deep-moment / `√(log)`-short wall W4
(`CharSumMomentDeepWall.lean`). Honest — no closure.

The cosh route uses the exact char-0 identity `Σ_{b∈F_p} cosh(‖η_b‖ y) = p·I₀(2y)^{n/2}` for a
root-free one-term bound `B ≤ min_y (1/y) arccosh(p·I₀(2y)^{n/2})`, saddle `y* = √(2 log p / n)`.
I drove it to a definitive verdict via exact numerics (n=8…32, primes p≈n⁴⁻⁵) + an axiom-clean Lean brick.

### The three decisive findings

**Q1 — the identity is CHAR-0, not char-p.** `LHS/RHS = 1.00000` at small `y`, but the ratio
diverges past 1 once `y` crosses the saddle, onset depending on `p/n`. At **n=32, p=1048609**: ratio
`1.00 → 1.50 (y=0.6) → 71.6 (y=1.0) → 3226 (y=1.5)`; b≠0 part already `2.03` at y=0.6. That divergence
*is* the char-p mod-`p` coincidence excess `E_r^{(p)} − E_r^∞ ≥ 0`. So the RHS `p·I₀(2y)^{n/2}` is
**not** an upper bound on the true char-p LHS at the saddle's `y`.

**Q2 — the cosh envelope is a REPACKAGING of the same moments (collapse).** TRUE char-p cosh bound
vs best single moment `mom_p = min_r (Σ_{b≠0}‖η_b‖^{2r})^{1/2r}`: `cosh_p / mom_p ∈ [1.013, 1.043]`
across all (n,p) (n=32: 1.0134, and `cosh/trueB = 1.0355`). `cosh = Σ even moments`, so the MGF
carries exactly the same information — the "root-free, no-max" form is cosmetic, never beats the truth.

**Q3 — the saddle lands `a/2` tower-levels TOO DEEP (the decisive new fact).** After the *proven*
Bessel baseline `E_r ≤ (2r−1)!!·n^r = (2r)! n^r/(2^r r!)` (`RungBesselEnergy.lean`), the `r`-th cosh
weight is `w_r(y) = y^{2r}/(2r)!·E_r ≤ (n y²/2)^r / r!` — a **Poisson profile** with intensity
`λ = n y²/2`. At the saddle `y*² = 2 log p / n` ⟹ `λ = log p` **exactly** ⟹ dominant weight at
`r_peak = ⌊log p⌋` (confirmed numerically to the unit; also `r_peak ≈ r_eff`, the depth the best
single moment uses). But char-0 `E_r` is reliable only for `r ≤ r_max = 2 log_n p = 2β`:

| n | a | r_peak (=log p) | r_max=2β | ratio |
|---|---|---|---|---|
| 32 (β=5) | 5 | 17 | 10 | 1.7 |
| 2^16 (β=5) | 16 | 55 | 10 | 5.5 |
| **2^32 (β=5)** | **32** | **111** | **10** | **11.1** |

`r_peak / r_max = (log n)/2 ≈ 0.347·a` — at the prize **the saddle samples moments 11× deeper than
the reliable cap**, the *same* `a/2`-tower-levels gap W4 already records for the raw moment method.

### Mechanism

The cosh-MGF is literally the exponential generating function of the even moments `E_r`; its saddle is
the Laplace selection of the optimal `r ≍ log p` — exactly the depth the moment method already wants and
already cannot reach. The root-free dressing removes the `2r`-th root and the `max` but moves **none**
of the open content (validity of `E_r` at `r ≍ log p` = the Bourgain/BGK/Paley-graph √-cancellation
core). Q1's measured char-p explosion is that defect, appearing precisely where the saddle puts its mass.
cosh-MGF is thus a 5th member of the moment-method family
(`deltastar-moment-method-convergence-diagnosis`), all sharing the `r < log_n p` threshold.

### Artifacts (axiom-clean Lean: `[propext, Classical.choice, Quot.sound]`)

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_T15Cosh.lean` — 7 thms: Poisson-weight
  concentration (`poissonWeight_succ`/`_le_succ`/`_succ_le`), `saddle_intensity_eq` (`λ=log p`),
  `cosh_mgf_walls_on_W4` (`2 log p/log n < log p`), `not_coshSaddleEscapesW4` (the named Prop
  `CoshSaddleEscapesW4` is FALSE at every prize n), `peak_over_rmax_eq` (gap `= (log n)/2`).
- `scripts/probes/wf407_T15-cosh_saddle_verdict.py` (Q1/Q2), `..._Q3_saddle_weight.py` (Q3),
  `..._Q2_n32_check.py`.
- `docs/kb/wf407-T15-cosh-saddle-walls-on-W4.md`.

**What remains:** a bound on `Σ_{b≠0} cosh(‖η_b‖y)` at `y ≥ y*` that is NOT moment-derived (uses the
actual Gauss-sum phase structure) — the same subgroup-Burgess / effective-equidistribution open
problem, not a new lever. cosh exploits no thinness structure, so it can't beat T18 either.

🤖 wf407/T15-cosh · Claude Opus 4.8 · honesty contract held (no fabricated closure)
