# δ* / #466 — G252: global phase discrepancy does not pin the fixed-row weighted covariance (2026-07-12)

**Lane:** direct Opus 4.8 CORE cron. Branch `research/proximity-prize` only (#499); `main` untouched.

## Context

G251 closed the *aggregate* Cartesian discrepancy route (published Lu–Zheng–Zheng Jacobi
discrepancy, even hypothetically perfect, cannot imply the aggregate weighted covariance) and named
the sole surviving prize face:

```
Re Σ_{χ ≠ 1} What(χ) · conj(Rhat_r(χ)) > threshold,   r = 5, 6,
```

with the explicit demand that any advance needs a **right-object theorem on joint phase-row
placement**, equivalently a fixed-row weighted shifted-subgroup/Jacobi bound.

The natural repair hopes the joint law of the phase axis (`arg What(χ)`) and the rank-weight axis
(`Rhat_r(χ)`) is *rigid* — that the two phases co-rotate as χ varies, so that a
global-discrepancy-admissible rearrangement cannot break the covariance. G252 tests exactly that
hope and refutes it.

## Probe

Three exact sponsor-type sweeps with the true signed CORE incidence weight:

- `scripts/probes/g252_joint_phase_lock_probe.py` (binom-rank surrogate weight; phase-lock scan)
- `scripts/probes/g252_signed_incidence_lock.py` (G245 signed normal form: shift-2 additive
  incidence, DC-subtracted, with a **cosine/Krawtchouk-style surrogate** for the rank-parity sign;
  phase-lock scan)
- `scripts/probes/g252_balanced_split_probe.py` (**the decisive test**: exact minimum real
  covariance restricted to *balanced* histogram-preserving sign vectors, `Σ s = 0`, even-N cells only)

The rank weight in these probes is a structural **surrogate** for the exact rank-r Newton/Krawtchouk
coefficient, not the literal G245 coefficient.  The result tested is structural (phase/row decoupling
under a histogram-preserving move) and is stable across the surrogate; it is not a numerical estimate
of the true covariance value.

### Phase-lock decorrelation

The first two probes measure the magnitude-weighted phase-lock strength
`lock = |Σ|W||R| e^{i(argW−argR)}| / Σ|W||R|`. It collapses toward 0 as `m → ∞`
(`0.36` at m=63, `0.0002` at m=1001): the phases of `What(χ)` and `Rhat_r(χ)` **do not co-rotate**,
and the actual covariance fraction hovers at 0.

> Correction (codex review, 2026-07-12): the first two probes' `zeros` field searched over *all*
> `k`-prefix flips including the degenerate `k=0` (all `+1`) and `k=N` (all `−1`) assignments, which
> makes `min-cov ≤ 0` tautological and does **not** test a histogram-preserving move. That field is
> not evidence. The balanced-split probe below replaces it with the correct, non-tautological test.

### Balanced-split annihilation (the decisive test)

`g252_balanced_split_probe.py` computes the *exact* minimum real covariance over **balanced** sign
vectors (equal `+1`/`−1` counts, `Σ s = 0` — the only move a global phase-discrepancy budget
permits, since it preserves the histogram). With per-index real contribution `c_i = Re(W_i ̅R_i)`,
the balanced minimum forces exactly `⌊N/2⌋` flips and is `Σ c_i − 2·(sum of top ⌊N/2⌋ c_i)`.

A strictly balanced sign vector (`Σ s = 0`) exists only for **even N**, so we report even-N cells
only (odd-N cells are explicitly skipped).  Output (`g252_balanced_split_probe.out`):

```
n=16 p=1009 r=5 m=63   N=62   cov= 5.17e3 bal_min=-2.22e4 bal_frac=-0.5798 bal_zero=True
n=16 p=1009 r=6 m=63   N=62   cov=-3.56e3 bal_min=-2.67e4 bal_frac=-0.7115 bal_zero=True
n=8  p=3001 r=5 m=375  N=374  cov= 4.13e4 bal_min=-4.36e5 bal_frac=-0.6457 bal_zero=True
n=8  p=8009 r=5 m=1001 N=1000 cov= 1.09e3 bal_min=-3.39e6 bal_frac=-0.6559 bal_zero=True
n=8  p=8009 r=6 m=1001 N=1000 cov=-1.85e4 bal_min=-3.24e6 bal_frac=-0.6395 bal_zero=True
```

In every even-N cell the exact balanced minimum is strongly negative, with `bal_frac ≈ −0.58 to −0.71`
**bounded away from 0 and stable in `m`** (and the specific equal-split used in the Lean invariant is
verified genuinely balanced, `lean_balanced=True`). A histogram-preserving move does not merely zero
the fixed-row covariance — it drives it to a large negative fraction of the triangle bound. Global
phase-histogram control therefore cannot lower-bound the fixed-row weighted covariance.

## Formal payload — the freedom invariant

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G252JointPhaseRowFreedom.lean`.

A "global phase discrepancy budget" is, at its strongest, control of the phase *histogram*; the
sharpest such control is a balanced sign vector (equal `+1`/`−1` counts, histogram-sum `0`). For the
extremal decorrelated weight isolated by the probe (`rowWeight k = 1` on `2k` cells):

- `alignedCov k = 2k` and `alignedCov_pos`: the aligned (all-phases-`+1`) fixed-row covariance is
  strictly positive — the fixed-row signal is genuinely nonzero;
- `balancedSign_histogram`: `Σ balancedSign k = 0` — the split is a legitimate
  global-discrepancy-preserving rearrangement;
- `splitCov_eq_zero`: the covariance under that balanced sign vector is exactly `0`;
- `global_phase_control_does_not_pin_covariance` bundles the three: a positive aligned covariance is
  annihilated by an admissible histogram-preserving move;
- `pinning_defect_eq_full`: `alignedCov k − splitCov k = 2k` — histogram-level global phase control
  loses the *entire* fixed-row signal.

Axioms: the arithmetic theorems depend only on `[propext, Classical.choice, Quot.sound]`;
`not_prizeClosure` depends on no axioms; no `sorryAx`.

## Scope

Route no-go, not a Jacobi estimate and not a prize closure. It closes the *joint-phase-lock* repair
that G251 left open: the joint law of `(arg What, arg Rhat_r)` provides no placement rigidity, so no
fixed-row weighted covariance bound can be produced from any global phase-discrepancy input,
however strong. The only remaining admissible route to the r=5/r=6 signed covariance is a genuinely
joint phase-row placement theorem that does **not** factor through a phase-histogram budget —
equivalently a per-row weighted shifted-subgroup/Jacobi bound proved directly against the row label.
CORE remains OPEN / ON-BGK.
