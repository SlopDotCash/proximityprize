# δ* #466 — Gaussian fixed point behind the dyadic tower split (2026-07-08)

## Hypothesis

R178 measured the dyadic split

```text
η_{2n}(C) = η_n(C_0) + η_n(C_1)
```

and found two stable statistics:

```text
cancel = |a+b|² / (|a|+|b|)²       ≈ 0.634..0.636
polar  = ||a|²-|b|²| / (|a|²+|b|²) ≈ 0.634..0.636
```

R177 independently found that the normalized period squares follow `χ²_1`.
R180 checks the synthesis: the tower split behaves like adding two independent
real Gaussians.  For `(A,B)` independent, identically distributed, mean-zero real
Gaussians (so that the angle of `(A,B)` is uniform), both expectations are exactly

```text
2 / π = 0.636619772...
```

Probe: `scripts/probes/probe_r180_gaussian_tower_fixed_point.py`.

## Result

```text
2/pi        = 0.636619772368
cancel_quad = 0.636619510569
polar_quad  = 0.636620034167
R178 dyadic measured: cancel≈0.634..0.636, polar≈0.634..0.636
```

The quadrature is deterministic: after polar coordinates, the Gaussian radius
cancels and only a uniform angle remains.  The measured dyadic tower-split
statistics land on the same `2/π` constant.

Scope of this match: `cancel` and `polar` are scale-invariant functions of the
child-pair **angle alone**.  Agreement with `2/π` therefore tests only the angle
law.  It says nothing about the radial law `η_n(C_0)^2 + η_n(C_1)^2`, or about
radius-angle independence.

## Verdict

The tail lane now has a coherent structural conjecture:

```text
Dyadic Gaussian tower fixed point.
At the level of coset periods, the refinement μ_n ⊂ μ_{2n} asymptotically
couples child periods like independent real Gaussian coordinates; hence the
normalized parent period has the same χ²_1 law.
```

If true, this would account for, in one mechanism:

* R177's `χ²_1` marginal law;
* R178's stable cancellation and polarization constants;
* R179's near-invariant R168 MGF/bin certificate along the tower.

Only the second item follows from the measured angle statistics alone.  The
first and third depend on the radial law as well.

Proof-facing form (corrected, audit T160).  An earlier version asked only that

```text
the empirical angle distribution of child pairs
  (η_n(C_0), η_n(C_1)) / sqrt(η_n(C_0)^2 + η_n(C_1)^2)
is close enough to uniform on the circle to preserve the R168 bin budget.
```

**A uniform child-pair angle alone cannot pay a normalized MGF budget.**  The
parent is `η_{2n}(C) = r·(cos θ + sin θ)` with `r^2 = η_n(C_0)^2 + η_n(C_1)^2`.
Hold the angle law exactly uniform and let `r` be arbitrary (heavy-tailed, or
correlated with `θ`).  The parent's normalized MGF is then governed by the law of
`r`, which the angle condition leaves completely free.  So any MGF/bin budget can
be violated with a perfectly uniform angle.  A sufficient proof-facing statement
must also control the radial part, for example:

```text
(i)  the child-pair angle is close to uniform, AND
(ii) the normalized radius r^2 / E[r^2] is close to χ²_2 (or obeys the R168
     MGF bound in its own right), AND
(iii) radius and angle are close to independent,
with all three closenesses quantified strongly enough for the R168 bin budget.
```

Exact (i)-(iii) together characterize i.i.d. centered Gaussian children
(Maxwell/Herschel).  This is the actual Gaussian-fixed-point content, and it is
strictly more than the measured angle statistics test.

Honest scope: this is still an equidistribution theorem for dyadic Gauss
periods, hence still in the Paley/BGK family.  It identifies a specific
distributional statement (angle, radial law and their independence) and the
angle constant `2/π` that a proof should reproduce.  The `2/π` match is evidence
for the angle part only.
