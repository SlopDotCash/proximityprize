# δ* #466 — R217 normalized-square finite-grid budget

R216 reduced the normalized-square residual to a finite survival-grid budget:

```text
Σ_θ δ(θ) B(θ) ≤ 2 · S.
```

R217 tests the concrete staircase for `exp(X/4)` and the observed half-rate
envelope

```text
B(θ) = 0.6 · S · exp(-θ/2) + 2.
```

The probe distinguishes the carrier issue:

- over quotient cosets, a `+2` reserve means two exceptional cosets;
- over raw nonzero frequencies, the same evidence corresponds to a spike mass
  multiplied by the coset size.

## Artifact

```text
scripts/probes/probe_r217_normalized_sq_grid_budget.py
```

## Prize-index run

```text
python3 scripts/probes/probe_r217_normalized_sq_grid_budget.py \
  --mode prize --ns 64 128 256 512 --samples 20000 \
  --seed 466217 --cutoff 32 --step 0.5 --carrier coset
```

Output summary:

```text
worst_envelope=1.279688 slack=0.720312
worst_empirical=1.544521 slack=0.455479
```

Readout: at `M >= 2^128`, the finite-grid weighted envelope is comfortably
below the target `2`.

## Exact coset run

```text
python3 scripts/probes/probe_r217_normalized_sq_grid_budget.py \
  --mode exact --max-n 256 --max-p 350000000 \
  --cutoff 32 --step 0.5 --carrier coset
```

Output summary:

```text
large rows:
  n=64  envelope=1.3055
  n=128 envelope=1.2829
  n=256 envelope=1.3828

small rows:
  n=32, M=36    envelope=188.9390
  n=32, M=1031  envelope=7.8323
```

Readout: the half-rate finite-grid budget is a large-index tool.  Small-index
rows need the existing direct/small-case branch, not this uniform `+2` coset
spike envelope with a long cutoff.

## Consequence

The next proof target should be the actual large-index survival-count theorem:

```text
#{cosets c : θ ≤ X(c)} ≤ 0.6 · M · exp(-θ/2) + 2
```

for the normalized-square period spectrum.  R216 plus this R217 grid budget
would discharge the normalized-square quarter-MGF residual for the large-index
branch.
