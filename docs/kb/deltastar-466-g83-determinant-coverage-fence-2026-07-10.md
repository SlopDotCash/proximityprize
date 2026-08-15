# Issue #466 G83: determinant coverage fence

Date: 2026-07-10

Lean file:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G83DeterminantCoverageFence.lean`.

G82 reduced the surviving CRT/transversality route to common coverage at distinct degree-one
prime ideals. G83 makes the arithmetic interface behind its documented determinant threshold
kernel-checked.

For rank `d`, prime `p`, coverage count `s`, and determinant magnitude `D`, assume

```text
0 < D,
p^s divides D,
D^2 <= 6^d.
```

Then `p^(2s) <= 6^d` and `s * log p <= (d/2) * log 6`. Coverage above this threshold therefore
rules out such a determinant certificate. All three theorems compile with only `propext`.

This is not the determinant construction. The remaining instantiation must prove, for an actual
full-rank cyclotomic census matrix:

1. its determinant is nonzero;
2. common coverage at `s` distinct prime ideals gives `p^s ∣ D`;
3. support-six row norms give `D^2 ≤ 6^d`.

Until these facts—or a different non-CRT mechanism—are proved, the production delta-star theorem
and the bound on `M` remain open.
