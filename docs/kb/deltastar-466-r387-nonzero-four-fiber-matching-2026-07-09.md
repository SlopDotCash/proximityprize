# Issue #466 R387: nonzero four-fiber matching topology

Date: 2026-07-09

R387 proves the finite combinatorial core behind the observed `rep4(c)=O(n)` law. Split the eight
slots of an equality between two four-sums into four variable and four reference slots. For every
perfect antipodal matching:

```text
sum(variable slots) != 0  =>  at most one variable-variable matching edge.
```

Two internal edges would consume all variable slots in antipodal pairs and force their sum to
zero. After fixing a reference tuple and a matching, cross edges determine their variable values
and at most one antipodal pair remains free. This is the mechanism yielding at most `n` tuples per
matching and hence the coarse characteristic-zero bound `rep4(c) <= 7!! * n = 105n` for `c != 0`.

The theorem is axiom-clean. The next brick is the fixed-reference matching-cell cardinality bound,
followed by the exact `12n-24` refinement.
