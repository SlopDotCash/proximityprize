# δ* / #466 — G253: the balanced move reverses the fixed-row weighted covariance, not merely annihilates it (2026-07-12)

**Lane:** direct Opus 4.8 formalizer cron. Branch `research/proximity-prize` only (#499); `main` untouched.

## Context

G252 (`_G252JointPhaseRowFreedom.lean`) refuted the "global phase discrepancy pins the fixed-row
weighted covariance" rigidity by exhibiting, on the *uniform* (all-ones) fixed-row weight, a balanced
histogram-preserving sign vector that drops the aligned covariance from `2k > 0` to exactly `0`. That
kill is at the annihilation level and uses a weight with no spread.

The actual CORE object is not uniform:

```
Re Σ_{χ ≠ 1} What(χ) · conj(Rhat_r(χ)) > threshold,   r = 5, 6,
```

where `conj(Rhat_r(χ))` is a **rank-`r` observable that varies across the quotient cells** — a
nonuniform, spread-carrying weight. The Opus-core G252 probes measured, on exact sponsor-type cells
with the true signed incidence weight, that the worst-case balanced split does not stop at `0`; it
drives the real covariance **strictly negative**:

```
n=16 p=1009 r=5 m=63    bal_frac = -0.5798
n=8  p=3001 r=5 m=375   bal_frac = -0.6457
n=8  p=8009 r=5 m=1001  bal_frac = -0.6559
```

`bal_frac ≈ -0.57 … -0.71`, bounded away from `0` uniformly in `m`. G252's uniform weight is
structurally blind to this: `splitCov ≡ 0` there. This file records the exact finite invariant behind
the measured **sign reversal**.

## The invariant

Model the rank observable as the extremal strictly-increasing integer weight

```
rankWeight a k i = a + i        (2k sorted cells, a = DC pedestal, i = rank-sorted spread)
```

and the worst-case balanced move as the **antisorted** sign vector

```
antiSign k i = +1  if i < k   (low-weight half)
             = -1  if i ≥ k   (high-weight half)
```

`antiSign_histogram`: `Σ antiSign = 0` — a legitimate histogram-preserving (global-discrepancy-
admissible) rearrangement. Proved in `ℤ`, in closed form:

- `splitCov_eq_neg_sq`: `splitCov a k = -k²`. The antisorted balanced covariance is exactly the
  negative squared spread, **independent of the DC pedestal `a`**: the pedestal and the linear ramp
  cancel between the two `range k` half-sums by the balanced histogram; what survives is `Σ_{t<k}(-k)`.
- `splitCov_neg`: `splitCov a k < 0` for `k ≥ 1` — the sign reversal, matching the measured `bal_frac < 0`.
- `alignedCov_pos`: `alignedCov a k > 0` for `k ≥ 1`.
- `reversal_defect_eq`: `alignedCov - splitCov = alignedCov + k²`, strictly more than the full aligned
  value. Contrast G252 `pinning_defect_eq_full` (defect equals exactly the aligned value, `splitCov = 0`);
  here the defect strictly exceeds it — the move overshoots into reversal.

## Why new, not a G252 wrapper (and not a fixed-depth island)

G252 proves `splitCov = 0` on the uniform weight. This is a strictly stronger, sign-aware statement on
a strictly larger class of weights (any spread-carrying rank observable); the G252 `= 0` case is exactly
the `k`-independent DC limit `spread → 0`. The `splitCov = -k²` law isolates the reversal magnitude as
the **squared spread of the rank weight**, with the DC pedestal provably inert — a rank-`r` observable
of larger spread yields a proportionally larger reversal. This is r-uniform content (a function of the
weight geometry the rank parameter controls), holding for every `k` and every pedestal `a`, and the
`-k²` closed form is the exact finite fingerprint of the measured `bal_frac`.

## Validation

- `scripts/pg-iterate.sh`: OK (6s); axioms `[propext, Classical.choice, Quot.sound]`; `not_prizeClosure`
  axiom-free; no `sorryAx`.
- `scripts/lake-locked.sh build …_G253AntisortedSignReversal`: success, 3297 jobs.
- `forbidden_tokens.py`, `sorry_census.py --fail-on-holes`, `check-imports.sh`, `kb/lint.py`: clean.
- Codex 5.5 `codex review --uncommitted`: pass.

## Scope

Route no-go, not a Jacobi estimate and not a prize closure. It sharpens G252: not only does global
phase-histogram control fail to *pin* the fixed-row weighted covariance, an admissible histogram-
preserving move *reverses its sign* against any spread-carrying rank weight. No global-phase-discrepancy
input can lower-bound the covariance — the certificate must be a genuinely joint phase-row placement
theorem proved directly against the row label. CORE remains OPEN / ON-BGK.

Formal payload: `Frontier/_G253AntisortedSignReversal.lean`.
