# G228 quotient-Jacobi fanout no-go

Date: 2026-07-12.  Lane: direct Opus CORE, issue #466, branch `research/proximity-prize`.

## Question

After G226 closed free Newton packet compression, the live analytic lane asks for an explicit
Gauss/Jacobi instantiation of the signed Mellin covariance

```text
Re sum_{chi != 1, chi|G=1} What(chi) conj(Rhat_r(chi)).
```

A possible thinner route would be: expand the shared factor `What(chi)` into Jacobi sums, keep a
bounded or otherwise small distinguished Jacobi subfamily, and control only that family instead of the
full quotient-character packet.

## Exact identity

Let `G=mu_n <= F_p^*`, `m=(p-1)/n`, and let `H` be the order-`m` quotient-character group trivial on
`G`.  For `chi in H`, put

```text
S_chi = sum_{u in G} conj(chi)(2-u),      What(chi) = n * S_chi.
```

Using

```text
1_G(x) = (1/m) * sum_{lambda in H} lambda(x)       (x != 0)
```

and substituting `u=2x`, one gets the quotient-Jacobi expansion

```text
S_chi = (1/m) * sum_{lambda in H}
          lambda(2) * conj(chi)(2) * J(lambda, conj(chi)),
```

where `J(alpha,beta)=sum_x alpha(x) beta(1-x)` and multiplicative characters are extended by zero at
zero.  Except for the usual at-most-two principal/product-principal exceptions, each Jacobi summand has
magnitude `sqrt(p)`.  Therefore any `K` selected summands, even chosen adaptively, contribute pointwise
at most

```text
|What_K(chi)| <= n * K * sqrt(p) / m.
```

## Parseval fanout lower bound

Let

```text
c_C = #{u in G : 2-u in C},     z = sum_C c_C = #{u in G : 2-u != 0}.
```

for quotient cosets `C in F_p^*/G`.  Parseval on the quotient gives the exact identity

```text
sum_{chi != 1} |S_chi|^2 = m * sum_C c_C^2 - z^2.
```

At both sponsor primes `2 notin G`, so `z=n`.  In the sponsor regime `m >> n`, the `c_C` are
nonnegative integers summing to `n`, so `sum_C c_C^2 >= n` and hence

```text
RMS_{chi != 1} |What(chi)| >= n * sqrt(n*(m-n)/(m-1)).
```

Combining the two displays, one Jacobi summand has RMS fraction at most

```text
sqrt(p) / (m * sqrt(n*(m-n)/(m-1))) = 2^{-64+o(1)}       at P1,
```

and any constant-fraction recovery needs `K = Omega(sqrt(m))` summands.  This is already
`2^64` summands at the first sponsor prime.

## Probe output

Executable artifact: `scripts/probes/oc_g228_jacobi_fanout_no_go.py`.  The script checks the Jacobi
identity directly on small cells and computes the exact Parseval fanout ratios on larger cells.

Selected output:

```text
n=16 p=257   m=16   jacobi_identity_max_err=1.228e-14, K_for_10/50/90=1/3/5
n=16 p=65537 m=4096 mean|S|^2=15.9414, one-term RMS ratio=0.0156538, K_for_10/50/90=7/32/58
n=32 p=65537 m=2048 mean|S|^2=72.5662, one-term RMS ratio=0.0146739, K_for_10/50/90=7/35/62
P1: one_jacobi_RMS_ratio <= 2^-64.000,
    K_for_10/50/90 >= 1844674407370955264 / 9223372036854775808 / 16602069666338596864
P2: one_jacobi_RMS_ratio <= 2^-64.500,
    K_for_10/50/90 >= 2608763565066556416 / 13043817825332781056 / 23478872085599006720
```

## Verdict

The analytic Gauss/Jacobi instantiation is real, but it fans out rather than compresses.  Any bounded
Jacobi subfamily inside `What(chi)` is RMS-negligible at the sponsor primes; a constant-fraction
approximation must retain `Omega(sqrt(m))`, about `2^64` to `2^64.5`, inner Jacobi summands before the
outer Newton packet is even considered.  Thus the next analytic lane cannot honestly replace `What`
by diagonal, low-order, bounded, or hand-picked few Jacobi terms.  It must control the full
quotient-Jacobi average, equivalently the same high-conductor BGK/Paley covariance already isolated by
G216-G227.

Scope: this does not prove the production signed estimate and does not consume the target.  It closes
only the bounded-inner-Jacobi shortcut to the requested analytic instantiation.
