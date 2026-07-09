# δ* #466 — real-Gaussian / chi-square law for dyadic period squares (2026-07-08)

## Hypothesis

R173/R176 found that the dyadic normalized coset spectrum is polarized:
extra mass near zero and a heavier high tail than random complex phases.  The
right model is not complex exponential; it is the square of a real Gaussian.
Because `-1 ∈ μ_{2^a}`, every dyadic Gauss period is real after antipodal
pairing, so the natural limiting law for

```text
X_C = |η_C|² / σ²
```

is

```text
χ²_1 = Z²,  Z ~ N(0,1),
P[χ²_1 ≥ T] = erfc(sqrt(T/2)).
```

Probe: `scripts/probes/probe_r177_real_gaussian_chi_square_law.py`.

## Result

```text
chi2_1 survival: T0.25:0.617 T0.5:0.480 T0.75:0.386 T1:0.317 T1.5:0.221 T2:0.157 T3:0.083 T4:0.046
n   p          kind        maxerr  meanerr  comparison
--------------------------------------------------------------------------------------------
32  32993      spike       0.0293  0.0139   T0.5:0.457/0.480 T1:0.298/0.317 T2:0.155/0.157 T4:0.054/0.046 T8:0.009/0.005
64  16778497   spike       0.0024  0.0014   T0.5:0.482/0.480 T1:0.319/0.317 T2:0.159/0.157 T4:0.045/0.046 T8:0.004/0.005
128 268437889  control     0.0012  0.0005   T0.5:0.481/0.480 T1:0.318/0.317 T2:0.158/0.157 T4:0.045/0.046 T8:0.004/0.005
256 16777729   control     0.0016  0.0005   T0.5:0.480/0.480 T1:0.319/0.317 T2:0.158/0.157 T4:0.045/0.046 T8:0.005/0.005
512 262657     high-order  0.0390  0.0137   T0.5:0.519/0.480 T1:0.324/0.317 T2:0.148/0.157 T4:0.035/0.046 T8:0.004/0.005
```

The mature rows (`n=64,128,256`) match `χ²_1` to roughly `10^-3` across the
bulk and moderate tail.  This explains all three R173/R176 observations at
once:

* median near `0.455`, not exponential's `0.693`;
* `P[X≥1]≈0.317`, `P[X≥2]≈0.157`, `P[X≥4]≈0.0455`;
* heavier high tail than complex random phases, but still compatible with the
  conservative R170 `exp(-T/4)` envelope.

## Verdict

The correct distributional target for dyadic periods is **real-Gaussian
coset-period normality**:

```text
|η_C|² / σ²  ≈  χ²_1.
```

This is stronger and cleaner than the R175 random-phase comparison, and it
explains why a global exponential(1) survival theorem is false: `χ²_1` has
tail rate `exp(-T/2)` up to the polynomial `T^{-1/2}` factor, not `exp(-T)`.

Proof target update:

```text
Show the dyadic coset-period empirical CDF is dominated by a modest enlargement
of χ²_1, or prove enough of the χ²_1 moment/tail envelope to feed R168.
```

Honest consequence for the prize: this law is exactly the expected extreme
value scale for real Gaussian samples, namely `max X ≈ 2 log M` for `M`
cosets.  So it supports a sharp `sqrt(2 n log M)`-type Gauss-period constant,
not a `sqrt(n log M)` complex-Gaussian constant.  Any claimed final prize
proof must match the actual constant in the prize statement; the real-Gaussian
law is a promising route if the prize threshold has the real-Gaussian `2`
constant, and a refutation signal if one tries to force the complex-Gaussian
`1` constant.
