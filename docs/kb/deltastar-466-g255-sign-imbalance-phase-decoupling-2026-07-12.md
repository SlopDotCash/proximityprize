# δ* / #466 — G255: multiplier-sign imbalance does not bound the phase-measure discrepancy (2026-07-12)

**Lane:** direct Opus 4.8 formalizer cron. Branch `research/proximity-prize` only (#499); `main` untouched.

## Context

G252/G253/G254 closed the histogram-budget repairs of the global phase-discrepancy route: a balanced
(`Σ s = 0`), conjugation-preserving sign move annihilates (G252) then reverses (G253/G254) the
fixed-row weighted covariance. The last surviving rescue for a *marginal* Lu–Zheng–Zheng phase input
claimed that such a balanced sign move is nonetheless **admissible** under a marginal-phase budget,
on the ground that its **multiplier-sign histogram** is balanced to at most one atom (`|Σ s| ≤ 1`),
so — the argument went — the actual *complex phase* empirical measure of the rows is perturbed by
only `1/(m-1)`.

The Fable G256 referee probe measured that this identification is false at sponsor scale: on
`(n,p,m,r) = (32,641,20,5)` the claimed one-atom scale is `1/19 = 0.0526` while the circular-interval
distance between the original and moved `What` phase measures is `0.6842`; on `(64,119297,1864,5)`
the one-atom scale is `1/1863 = 0.000537` but the measured phase change is `0.5641` (first Fourier
moment changes by `0.183`). The gap grows to three orders of magnitude by `m = 1864`. G255 formalizes
the exact finite mechanism behind that measurement.

## Mechanism

A sign `s = -1` on a row multiplies its normalized phase `z` by `-1`, i.e. **rotates it by `π`**. A
balanced `Σ s = 0` move multiplies roughly half the rows by `-1`, so it moves that entire half of the
phase atoms by `π`. The multiplier-sign imbalance `Σ s` measures only the balance of the `±1`
histogram; it gives no bound on the discrepancy of the actual phases.

## Formal model (`_G255SignImbalancePhaseDecoupling.lean`)

Index `2k` phase atoms by `Fin (2k)`. Low half `phaseClass = 0`, high half `phaseClass = 1` (the
two-class extremal-decorrelated arrangement of G252). The balanced move `phaseSign` gives `+1` to the
low half, `-1` to the high half. `movedClass` sends a `-1`-signed atom's class `c` to `c + 2` (two
fresh classes `2, 3`, modelling `z ↦ -z`). `phaseChanged` counts the atoms whose class moves.

Theorems, all in `ℤ`/`ℕ`, closed form:

- `signImbalance_eq_zero`: `Σ phaseSign = 0` — the multiplier-sign histogram is *exactly* balanced
  (stronger than the "at most one atom" the rescue is allowed).
- `phaseChanged_card_eq`: `(phaseChanged k).card = k` — exactly `k` of the `2k` atoms change phase,
  the whole high half.
- `phaseChanged_is_half`: `2 · changed = 2k` — the moved fraction is exactly one half, independent of
  the vanishing multiplier-sign imbalance.
- `sign_imbalance_does_not_bound_phase_discrepancy`: the headline decoupling — a move with zero
  multiplier-sign imbalance changes a full half of the phase histogram.
- `phaseDiscrepancy_ge_half`, `phaseDiscrepancy_gt_imbalanceScale`: the phase discrepancy `≥ 1/2` and
  the gap `k` grows without bound — the decoupling is `k`-uniform, not a fixed-`k` island.

Axioms: the arithmetic/Finset declarations carry `[propext, Classical.choice, Quot.sound]`;
`not_prizeClosure` is axiom-free; no `sorryAx`.

## Probe

`scripts/probes/g255_sign_imbalance_phase_decoupling_probe.py` checks the exact finite model
(`sign_imbalance = 0`, `phase_changed = k`, `phase_change_frac = 1/2` for `k ∈ {1,2,5,20,931}`) and
records the corresponding Fable G256 sponsor-scale measurement.

## Scope / honest limits

Route-hygiene no-go, not a Jacobi estimate and not a prize closure. It refutes the "one-atom
phase-histogram" admissibility claim by exhibiting the exact statistic mismatch: a balanced sign move
is **not** admissible under a marginal phase input because it changes the marginal phase measure by a
constant fraction (`1/2`), not by `1/(m-1)`. This closes the last histogram-admissibility rescue of
the marginal phase-discrepancy route. The live prize face is unchanged and must NOT factor through any
marginal phase budget:

```
Re Σ_{χ ≠ 1} What(χ) · conj(Rhat_r(χ)) > threshold,   r = 5, 6,
```

over the full quotient-character family, via a genuinely joint, row-labelled sponsor-prime estimate.
CORE remains OPEN / ON-BGK.
