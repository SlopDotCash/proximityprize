# δ* #466 — child-pair angle equidistribution in the dyadic tower (2026-07-08)

## Hypothesis

R180 reduced the dyadic tower fixed-point law to a concrete geometric
statement.  If the child period pairs

```text
(η_n(C_0), η_n(C_1)) / sqrt(η_n(C_0)^2 + η_n(C_1)^2)
```

are equidistributed in angle, then the observed `2/π` cancellation and
polarization constants follow from the real-Gaussian fixed point.

R183 measures this directly via low Fourier coefficients and 16-arc
discrepancy.

Probe: `scripts/probes/probe_r183_child_pair_angle_equidistribution.py`.

## Result

```text
p          n->2n   pairs  disc16   maxF1-8  f1      f2      f3      f4
--------------------------------------------------------------------------------------------
1048609    16 ->32  32769  0.00345  0.00966  0.00454 0.00966 0.00019 0.00539
16777601   32 ->64  262150 0.00080  0.00380  0.00094 0.00092 0.00072 0.00380
268437889  64 ->128 2097171 0.00035  0.00226  0.00061 0.00016 0.00013 0.00226
```

The angle distribution is very close to uniform.  The coarse arc discrepancy
falls from `3.45e-3` to `3.5e-4`; the largest low harmonic among `1..8` falls
to `2.26e-3`.

Multi-prime stress (R184, first five primes in each row) did not expose a
prime-specific harmonic obstruction:

```text
n 16 -> 32: maxF1-8 in [0.00653, 0.01059], disc16 ≤ 0.00345
n 32 -> 64: maxF1-8 in [0.00319, 0.00566], disc16 ≤ 0.00117
```

## Verdict

The proof-facing target is now precise:

```text
Dyadic child-angle equidistribution.
For the tower μ_n ⊂ μ_{2n}, the angles of child period pairs have uniformly
small Fourier coefficients:
  |M^{-1} Σ_C exp(iℓ θ_C)| ≤ error(n,p,ℓ)
for the finitely many harmonics needed by the R168/R177 bin budget.
```

This is stronger than a raw survival theorem and more local than the full
Paley sup-norm problem.  It would imply:

1. the `2/π` tower cancellation constants (R180);
2. the `χ²_1` marginal fixed point (R177);
3. preservation of the R168 MGF/bin certificate along the dyadic tower (R179),
   provided the bin functions are approximated by finitely many angular
   harmonics.

Honest scope: proving these Fourier bounds is still an exponential-sum
equidistribution problem.  The win is localization: the missing theorem is no
longer an amorphous `max |η|` bound, but a finite-harmonic angular
equidistribution statement for adjacent dyadic levels.
