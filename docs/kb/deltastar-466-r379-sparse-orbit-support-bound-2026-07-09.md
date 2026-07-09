# Issue #466 R379: sparse orbit support bound

Date: 2026-07-09

## Result

For an integer vector `d`, R379 proves

```text
card(support d) <= endpointL1(d).
```

It then proves the covering-family inequality

```text
m <= card(O) * endpointL1(d),
```

whenever the supports of `O` cover all `m` coordinates and every member of `O` has the same
endpoint `L1` mass as `d`. Both results are axiom-clean.

## Significance

R378 proves rotation preserves endpoint mass and the full signed summand. To obtain the predicted
orbit saving, it now remains only to instantiate `O` as the finite negacyclic rotation orbit and
prove its supports cover `Fin m`. The resulting bound is exactly `orbitSize >= m / ||d||_1`, hence
at least `m/(2r)` for a doubled-walk endpoint at depth `r`.
