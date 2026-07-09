# R288: subconvexity lens, lag route refuted as the main bridge

Date: 2026-07-09.

## Claim

The R35 lag-energy bridge is algebraically correct, but it is not the winning
subconvexity bridge at prize scale unless it is strengthened past pair
correlation.  The obstruction is the zero lag.

R35 proves

```text
sum_d |fullConv(J,J)(d)|^2 = sum_t |Corr_J(t)|^2
```

and then feeds this into the R23 self-convolution input.  For the Jacobi
coefficients at `m = (q - 1) / n`, direct probes show

```text
Corr_J(0) = sum_j |J_j|^2 ≈ m q.
```

Therefore the zero lag alone contributes

```text
|Corr_J(0)|^2 ≈ m^2 q^2,
```

whereas the R23 self-convolution input needs

```text
sum_d |selfConv(J,J)(d)|^2 <= C m q^2
```

with `C = O(1)`.  The lag route spends an unavoidable factor `m` before the
third convolution is ever used.

## Numerical check

Fresh direct lag probe:

```text
p      n     m   beta  lag0/(m q)  maxoff/(m sqrt(q))  Eoff/(m^3 q)  E2/(m q^2)  E3/(m^3 q^3)
193    8    24   2.53      0.9171              5.2547         5.8426      37.7723          3.0190
577    8    72   3.06      0.9723              8.2338        18.1038     230.6608         13.9699
1489   8   186   3.51      0.9893              9.5000        14.9468     529.3720         12.8841
1153  16    72   2.54      0.9722              7.5098        16.3917     141.6170          5.1654
4129  16   258   3.00      0.9922             12.7589        31.3987     760.1813         18.9503
5953  32   186   2.51      0.9892             25.9733        55.3636     503.9022         10.9207
```

Here `E2` is the punctured quadratic convolution energy and `E3` is the R23
triple-convolution energy.  The important pattern is:

* `E2/(m q^2)` grows with `m`, so bounding `selfConv` first is too lossy.
* `E3/(m^3 q^3)` remains constant-scale on these cells, so the third
  convolution recovers cancellation that the R35 consumer discards.

## Consequence

The viable subconvex target is not

```text
Pair lag control -> selfConv energy -> triple energy.
```

It is a genuinely cubic estimate:

```text
sum_d |sum_{a+b+c=d, a,b,c != 0} J_a J_b J_c|^2 <= C m^3 q^3.
```

Equivalently, the prize core is a vertical-family subconvexity statement for
the sixth moment of the Jacobi Fourier face.  Pair-Weil and R35 remain useful
diagnostics, but any proof that first compresses the quadratic convolution into
an `L^2` bound loses the zero-lag mass and cannot land the constant-scale R23
input.

## Next target

Attack the cubic estimate directly.  The new hypothesis should be phrased as
one of:

1. a Katz/Sato-Tate equidistribution theorem for the six-character family after
   diagonal deletion;
2. a Hasse-Davenport angle identity that exposes cancellation in
   `selfConv(J,J) * J`;
3. an exact stratification of the sextic expansion into diagonal Wick classes
   plus a square-root-cancelled connected six-point term.

The R35 lag socket should not be extended as the main proof path unless it is
modified to keep the final convolution phase instead of spending absolute
values at the quadratic stage.
