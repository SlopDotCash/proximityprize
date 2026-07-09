# δ* #466 — mixed moments of dyadic tower child pairs (2026-07-08)

## Hypothesis

R183/R184 localized the dyadic tower route to child-pair angle
equidistribution.  R185 tests an algebraic equivalent/companion: after RMS
normalization, the two child periods in

```text
η_{2n}(C) = η_n(C_0) + η_n(C_1)
```

behave like independent real Gaussians.

Probe: `scripts/probes/probe_r185_child_pair_mixed_moments.py`.

## Result

Independent real-Gaussian targets:

```text
E[AB]=0, E[A²B²]=1, E[A⁴]=3, E[A⁴B²]=3, E[A⁴B⁴]=9, E[A⁶]=15.
```

Measured:

```text
p          n->2n   pairs    m11      m22      m40      m42      m44      m60
--------------------------------------------------------------------------------------------------------
1048609    16 ->32  32769    -0.00002 0.99984  2.80362  2.82954  7.84904  12.29751
16777601   32 ->64  262150   -0.00000 0.99995  2.90522  2.90162  8.47190  13.55507
268437889  64 ->128 2097171  -0.00000 0.99999  2.95345  2.94991  8.72547  14.31682
```

The quadratic mixed moment is essentially exact:

```text
E[A²B²] = 1 + o(1),
```

and the higher moments approach the independent real-Gaussian constants from
below.

Multi-prime stress for the first five same-regime primes:

```text
n 16 -> 32:
  m22 = 0.99979..0.99984, m42 = 2.79786..2.83500, m44 ≈ 7.848
n 32 -> 64:
  m22 = 0.99994..0.99996, m42 = 2.89842..2.94854, m44 = 8.38390..9.11043
```

The load-bearing low mixed moments are prime-stable; the higher `m44` moment
shows the expected finite high-tail sensitivity.

## Verdict

This is the most algebraic form of the R177-R184 story.  The missing theorem
can be stated as mixed additive-energy control for adjacent dyadic child
cosets:

```text
For child periods A_C = η_n(C_0), B_C = η_n(C_1),
prove Gaussian mixed-moment bounds
  E[A^{2u} B^{2v}] ≤ (2u-1)!! (2v-1)!! σ^{2u+2v}
for the finite set of (u,v) needed by the R168 bin-budget approximation.
```

This avoids division by `sqrt(A²+B²)` and avoids trigonometric angle functions;
it is closer to the existing additive-energy/Weil machinery.  It also explains
the R183 angle uniformity: the low mixed moments already factor as if the two
child coordinates were independent real Gaussians.

Honest scope: this is still a nontrivial mixed-energy theorem.  But it is
strictly more proof-shaped than the earlier global tail envelope: it reduces
the dyadic tower route to finitely many adjacent-child mixed moments.
