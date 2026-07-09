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

Because `psi` is trivial on `H`, this simplifies exactly to

```text
psi(h/(b+h)) = conjugate(psi(b+h)).
```

Keeping the Fourier normalization gives

```text
|Fourier(D_psi u)(b)| / sqrt(m)
  = |sum_(h in H) psi(b+h)| / sqrt(n),                         (1)
```

apart from the explicitly removable trivial-character terms. Thus derivative Fourier
flatness is *exactly* square-root cancellation for a multiplicative character on an additive
translate of `H`, not a generic CAZAC consequence. The measured constants near `3` on the
left of (1) are the same constants near `3` in the normalized shifted-subgroup sum on the
right.

The probe

```text
python3 scripts/probes/probe_r378_gauss_phase_derivatives.py 32 1060513
```

finds, for `m=33141`, first-derivative Fourier maxima between `2.95 sqrt(m)` and
`3.28 sqrt(m)` across the tested shifts. Iterated derivatives along shifts
`1,2,4,...,128` remain between `2.99 sqrt(m)` and `4.74 sqrt(m)` through depth eight.
The original period PAPR is `4.304`.

This supports a square-root shifted-subgroup hypothesis for low derivative depth.
It does **not** close the prize. From `|C_h| <= C sqrt(m)`, the complete van der Corput
identity gives only

```text
|sum_j u_j e(jx/m)|^2 <= C m^(3/2),
```

hence the `m^(3/4)` scale. Fixed-depth Gowers iteration likewise leaves a power loss; reaching
`sqrt(m log m)` requires uniform control at growing depth, where conductor growth is itself
the R376 moment wall. Standard completion gives a `sqrt(p)` bound for the shifted-subgroup
sum, losing `sqrt(m)` relative to the desired `sqrt(n)` scale.

Verdict: the derivative phenomenon is genuine and potentially useful if one proves a
growing-depth conductor theorem, but the low-depth version is insufficient and equation (1)
shows that its key estimate is another exact coordinate system for the shifted-subgroup BGK
wall. No prize closure is claimed.
