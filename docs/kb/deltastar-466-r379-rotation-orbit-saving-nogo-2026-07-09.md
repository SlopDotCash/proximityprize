# R379: rotation-orbit saving is not automatic

The R378 theorem proves the exact invariance

```text
NR(2m,m,2r,rotZ d) * discrepancy(rotZ d)
  = NR(2m,m,2r,d) * discrepancy(d).
```

This is useful orbit quantization, but it does **not** produce an upper-bound saving by
itself. If an orbit `O` is contained in the summation domain, then invariance gives

```text
∑ d ∈ O, summand d = |O| * summand d₀,
```

not `summand d₀ / |O|`. Thus replacing a sum by orbit representatives merely changes the
weight of each representative. A saving requires an additional mechanism—e.g. a character
twist whose orbit average vanishes, or a signed action that changes the discrepancy
coefficient. R378's discrepancy coefficient is deliberately invariant, so neither mechanism
is present.

This refutes the proposed `m/(2r)` orbit-size improvement as a consequence of R378 alone.
The theorem remains valuable for exact orbit censuses and for locating where a genuinely
non-invariant phase could be inserted, but it does not close `WallHolds` or the R3 Jacobi
convolution bound.
