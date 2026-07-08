# δ* #466 — candidate inequalities for tower MGF step (2026-07-08)

## Hypothesis

R179/R180 suggest the R168 MGF is nearly invariant along the dyadic tower.
R181 tests deterministic inequalities for one tower step.  If a parent period
is `a+b` from two child periods, compare the actual parent MGF to envelopes
built from the child magnitudes.

Probe: `scripts/probes/probe_r181_tower_mgf_inequality.py`.

## Result

Shared prime `p=262657`:

```text
n->2n actual   childAvg tri      energy   phase    sigma_parent/child
------------------------------------------------------------------------------------
16 ->32  1.15339  1.15185  1.25915  1.32713  1.15339  1.99988
32 ->64  1.15359  1.15339  1.25990  1.32977  1.15359  1.99976
64 ->128 1.15597  1.15359  1.25747  1.33003  1.15597  1.99951
128->256 1.15475  1.15597  1.26123  1.33669  1.15475  1.99902
256->512 1.15709  1.15475  1.25772  1.33541  1.15709  1.99805
```

Columns:

* `actual`: parent average of `exp(X/8)`.
* `childAvg`: average of the two child `exp(X/8)` values.
* `tri`: bound using `|a+b|² ≤ (|a|+|b|)²`.
* `energy`: bound using `|a+b|² ≤ 2(|a|²+|b|²)`.
* `phase`: actual phase-aware expression.

## Verdict

Normalization is clean:

```text
σ²_parent / σ²_child ≈ 2.
```

The actual parent MGF tracks the child average almost exactly, which is the
desired tower invariant.  However, the crude deterministic triangle/energy
bounds are much looser:

```text
triangle envelope ≈ 1.26
energy envelope   ≈ 1.33
```

Even those loose bounds remain well below the R168 budget `2`, so a crude
tower proof might already suffice for the prize route.  A sharp invariance
proof must use phase cancellation; a merely prize-closing proof may only need
the energy/triangle envelope plus the observed sigma doubling.

Next theorem shape to test in Lean:

```text
If σ²_parent = 2σ²_child and parent periods split as a+b, then
  avg exp(|a+b|²/(8σ²_parent))
is bounded by a child-side exponential budget using |a+b|² ≤ 2(|a|²+|b|²).
```

The constant loss from that inequality appears compatible with R168.
