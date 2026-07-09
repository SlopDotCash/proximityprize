# δ* #466 — finite-grid MGF certificate for R168 (2026-07-08)

## Hypothesis

R168 reduced the dyadic tail route to a finite-grid count certificate:

```text
Σ_θ δ(θ) B(θ) ≤ 2 |s|
```

where the staircase increments `δ` dominate `exp(t/8)` and `B(θ)` bounds the
survival counts `#{b : θ ≤ t_b}`.

R169 tests whether such a certificate is numerically realistic on exact dyadic
spectra.

Probe: `scripts/probes/probe_r169_finite_grid_mgf_certificate.py`.

## Construction

Use thresholds spaced by `h ∈ {0.5, 0.25, 0.125}`.  For grid points
`θ_j`, define

```text
δ_j = exp(θ_{j+1}/8) - exp(θ_j/8).
```

Then for `t ∈ [θ_j, θ_{j+1}]`, the staircase reaches
`exp(θ_{j+1}/8)` and dominates `exp(t/8)`.  The R168 weighted-count theorem
can therefore consume the exact survival counts at the grid thresholds.

## Result

Known adversarial and control spectra:

```text
n   p          kind        maxX    mgf       grid0.5   grid0.25  grid0.125
--------------------------------------------------------------------------------------
32  32993      spike       17.636  1.16500   1.21224   1.18666   1.17543
32  1048609    control     16.508  1.15322   1.19765   1.17397   1.16318
64  264769     spike       18.030  1.15422   1.19840   1.17504   1.16417
64  16778497   spike       27.584  1.15414   1.19844   1.17496   1.16413
64  16777601   control     23.195  1.15395   1.19826   1.17478   1.16392
128 2101249    small-spike 18.320  1.15431   1.19878   1.17505   1.16426
128 268437889  control     23.688  1.15432   1.19868   1.17516   1.16431
256 16777729   control     16.587  1.15438   1.19882   1.17524   1.16435
```

Broad stress scan with the coarse `h=0.5` grid:

```text
stress grid0.5
  ratio=1.212239 mgf=1.164998 n=32 p=32993 maxX=17.636
  ratio=1.211553 mgf=1.161369 n=32 p=1217 maxX=6.843
  ratio=1.205870 mgf=1.154468 n=16 p=337 maxX=5.929
  ratio=1.201776 mgf=1.154038 n=32 p=1409 maxX=6.116
  ratio=1.201628 mgf=1.153699 n=64 p=5569 maxX=7.071
  ratio=1.200879 mgf=1.154774 n=64 p=4673 maxX=6.600
  ratio=1.200691 mgf=1.147497 n=16 p=593 maxX=4.569
  ratio=1.199238 mgf=1.155103 n=128 p=17921 maxX=9.465
  ratio=1.199207 mgf=1.151973 n=32 p=2017 maxX=6.613
  ratio=1.198822 mgf=1.154094 n=128 p=18433 maxX=9.311
stress tested=105 violations=0
```

The R168 budget is `≤ 2`; the worst observed finite-grid certificate is
`1.212239`.

## Verdict

The finite-grid R168 contract is numerically very plausible.  Even a coarse
`0.5`-spaced staircase has ample slack on all tested dyadic spectra.

Concrete next proof target:

```text
For the normalized dyadic period spectrum t_b, prove grid survival bounds
  #{b : θ ≤ t_b} ≤ B(θ)
for θ ∈ 0.5·ℕ, with
  Σ_θ (exp((θ+h)/8)-exp(θ/8)) B(θ) ≤ 2M.
```

This is now the sharpest formulation of the concentration route: no moment
monotonicity, no continuous measure layer-cake, and no vague tail prose.  It is
a finite family of survival-count estimates plus one explicit weighted sum.
