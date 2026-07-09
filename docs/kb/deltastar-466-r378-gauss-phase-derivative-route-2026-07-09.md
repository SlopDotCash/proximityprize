# #466 R378: Gauss-phase derivatives are flat, but the first derivative stops at 3/4

R376 rewrites the prize wall as PAPR of the length-`m=(p-1)/n` Gauss-sum phase
sequence. This round tested whether multiplicative derivatives of that phase sequence have
bounded-conductor Fourier transforms.

For quotient characters `chi, psi`, write `u(chi)=tau(chi)/sqrt(p)`. Away from the trivial
characters, the Gauss/Jacobi identity gives

```text
u(chi psi) conjugate(u(chi)) = tau(psi) J(chi psi, conjugate(chi)) / p.
```

Expanding the Jacobi sum and Fourier transforming in `chi` turns a derivative coefficient
into a character sum over the rational image

```text
h -> h/(b+h),  h in H.
```

Thus derivative flatness is an arithmetic statement about a shifted subgroup, not a generic
CAZAC consequence.

The probe

```text
python3 scripts/probes/probe_r378_gauss_phase_derivatives.py 32 1060513
```

finds, for `m=33141`, first-derivative Fourier maxima between `2.95 sqrt(m)` and
`3.28 sqrt(m)` across the tested shifts. Iterated derivatives along shifts
`1,2,4,...,128` remain between `2.99 sqrt(m)` and `4.74 sqrt(m)` through depth eight.
The original period PAPR is `4.304`.

This supports a constant-conductor hypergeometric-sheaf hypothesis for low derivative depth.
It does **not** close the prize. From `|C_h| <= C sqrt(m)`, the complete van der Corput
identity gives only

```text
|sum_j u_j e(jx/m)|^2 <= C m^(3/2),
```

hence the `m^(3/4)` scale. Fixed-depth Gowers iteration likewise leaves a power loss; reaching
`sqrt(m log m)` requires uniform control at growing depth, where conductor growth is itself
the R376 moment wall. Standard Weil expansion of the rational subgroup sum gives a `sqrt(p)`
bound, losing `sqrt(n)` relative to the observed `sqrt(m)` scale.

Verdict: the derivative phenomenon is genuine and potentially useful if one proves a
growing-depth conductor theorem, but the low-depth version is insufficient and presently
reduces to a shifted-subgroup BGK estimate. No prize closure is claimed.
