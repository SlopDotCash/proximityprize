# Issue #509 G101: orbit-class variance normal form

Date: 2026-07-10

G101 gives the exact cleared-denominator deviation coordinates requested by #509.

For an exact-order generator `g` of order `n`, the nonzero field values partition into orbit
classes of size exactly `n`. Lean proves

```text
n · #(orbitClassSet F n) = #F - 1.
```

For the class masses `Sγ`, define the pairwise deviation

```text
D = Σγ Σδ (Sγ - Sδ)^2.
```

The general finite variance identity gives

```text
D = 2 · (k · Σγ Sγ^2 - (Σγ Sγ)^2),
k = #(orbitClassSet F n).
```

Using G88's total-mass theorem `ΣγSγ = n^r-S₀`, G101 rewrites the centered shadow mass exactly as
the equidistributed kernel/bulk baseline plus `q·D`, after clearing `2k`. In particular, `D≥0`,
and `D=0` is precisely the uniform class profile.

The headline theorem `dcEnergyBound_iff_kernel_deviation_le` proves that `DCEnergyBound` is
equivalent to the resulting displayed inequality in `(S₀,D)`. Thus the profile formulation has no
remaining hidden freedom: after the kernel mass is fixed, the pairwise deviation is the unique
nonnegative obstruction, with coefficient exactly one. This satisfies #509's honest-closure exit
criterion; it does not prove the production inequality.

`scripts/pg-iterate.sh` passes. Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
