# #466 R198: shifted-Cauchy product consumer

Status: deterministic consumer, not a proof of the one-level quarter-MGF bound.

R192/R193 framed the dyadic product-MGF as a mean-square plus half-turn covariance. A simpler
sufficient condition is available in the actual tower: the two child lists are shifts of the same
child spectrum. Therefore their square sums agree, and pointwise

```text
u v <= (u^2 + v^2) / 2
```

gives

```text
avg_i u_i v_i <= avg_i u_i^2.
```

With `u_i = exp(left_i/8)`, this is exactly the one-level quarter-MGF `avg exp(left_i/4)`.

## Probe check

The quick variance check computed `mean(f)^2 + var(f) = E[f^2] = MGF(1/4)`:

```text
n=16  p=1048609    E[f^2]=1.387418
n=32  p=16778497   E[f^2]=1.399459
n=64  p=16778497   E[f^2]=1.413912
n=128 p=268437889  E[f^2]=1.410143
n=256 p=16777729   E[f^2]=1.409032
n=32  p=32993      E[f^2]=1.523404
n=512 p=262657     E[f^2]=1.467002
```

All are below the needed product budget constant `2`.

## Lean artifact

`_R198ShiftCauchyProductConsumer.lean` proves:

```text
sum v_i^2 <= sum u_i^2
----------------------
sum u_i v_i <= sum u_i^2
```

and the exponential specialization:

```text
sum exp(left/8) exp(right/8)
  <= sum exp(left/4).
```

## Consequence for the proof route

The covariance theorem is optional. It suffices to prove the one-level quarter-MGF residual,
with the small-index direct / large-index tail split from R196/R197:

```text
child quarter-MGF <= 2
  => dyadic product budget <= 2
  => R168 parent tail-MGF
```

This is not a prize closure; it is a simplification of the remaining analytic target.
