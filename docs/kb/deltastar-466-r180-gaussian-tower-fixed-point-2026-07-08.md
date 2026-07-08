# δ* #466 — Gaussian fixed point behind the dyadic tower split (2026-07-08)

## Hypothesis

R178 measured the dyadic split

```text
η_{2n}(C) = η_n(C_0) + η_n(C_1)
```

and found two stable statistics:

```text
cancel = |a+b|² / (|a|+|b|)²       ≈ 0.634..0.636
polar  = ||a|²-|b|²| / (|a|²+|b|²) ≈ 0.634..0.636
```

R177 independently found that the normalized period squares follow `χ²_1`.
R180 checks the synthesis: the tower split behaves like adding two independent
real Gaussians.  For `(A,B)` independent real Gaussians, both expectations are
exactly

```text
2 / π = 0.636619772...
```

Probe: `scripts/probes/probe_r180_gaussian_tower_fixed_point.py`.

## Result

```text
2/pi        = 0.636619772368
cancel_quad = 0.636619510569
polar_quad  = 0.636620034167
R178 dyadic measured: cancel≈0.634..0.636, polar≈0.634..0.636
```

The quadrature is deterministic: after polar coordinates, the Gaussian radius
cancels and only a uniform angle remains.  The measured dyadic tower-split
statistics land on the same `2/π` constant.

## Verdict

The tail lane now has a coherent structural conjecture:

```text
Dyadic Gaussian tower fixed point.
At the level of coset periods, the refinement μ_n ⊂ μ_{2n} asymptotically
couples child periods like independent real Gaussian coordinates; hence the
normalized parent period has the same χ²_1 law.
```

This explains, in one mechanism:

* R177's `χ²_1` marginal law;
* R178's stable cancellation and polarization constants;
* R179's near-invariant R168 MGF/bin certificate along the tower.

Proof-facing form:

```text
Show that the empirical angle distribution of child pairs
  (η_n(C_0), η_n(C_1)) / sqrt(η_n(C_0)^2 + η_n(C_1)^2)
is close enough to uniform on the circle to preserve the R168 bin budget.
```

Honest scope: this is still an equidistribution theorem for dyadic Gauss
periods, hence still in the Paley/BGK family.  But it is sharper than a raw
tail estimate: it identifies the specific missing distributional statement
and the constant `2/π` that a proof should produce.
