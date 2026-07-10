# Issue #466 R391: four-fiber toric normalization

Date: 2026-07-09

For a nonzero four-sum fiber of `n`-th roots, divide the first three coordinates by the fourth:

```text
y_i = x_i / x_3.
```

R391 proves that this map is injective on each fixed nonzero fiber and that its image satisfies

```text
y_i^n = 1,
(1 + y_0 + y_1 + y_2)^n = c^n.
```

Thus the finite-characteristic representation problem is a torsion-point count on one explicit
affine hypersurface.  At the prize scale `p ~ n^4`, its generic expected count is `n^4/p ~ 1`;
the observed `O(n)` peaks come from positive-dimensional antipodal components.  The next target is
to factor out those components and bound the remaining zero-dimensional intersection uniformly.
