# δ* #466 — closed-form tail laws for the finite-grid certificate (2026-07-08)

## Hypothesis

R169 showed the R168 finite-grid MGF certificate works on exact spectra.  R170
asks whether a simple closed-form survival law is enough to imply that
certificate uniformly:

```text
N(T) ≤ C · M · exp(-aT).
```

Probe: `scripts/probes/probe_r170_closed_form_grid_tail.py`.

## Result

Stress set: the same 105 exact dyadic spectra used in R169, thresholds
`T ∈ 0.5·ℕ`, `1 ≤ T ≤ 32`.

```text
C      a       max_tail_ratio  budget_const  verdict
--------------------------------------------------------------------
1      0.25    0.499343        2.057322      FAIL
  worst n=16 p=577 T=1 count=14/36
0.75   0.25    0.665791        1.542991      OK
  worst n=16 p=577 T=1 count=14/36
0.6    0.25    0.832239        1.234393      OK
  worst n=16 p=577 T=1 count=14/36
1      0.3333  0.549574        1.651797      OK
  worst n=16 p=577 T=1.5 count=12/36
0.75   0.3333  0.732765        1.238848      OK
  worst n=16 p=577 T=1.5 count=12/36
1      0.4     1.063660        1.502028      FAIL
  worst n=32 p=32993 T=17.5 count=1/1031
```

`C=1, a=1/4` appears to hold empirically, but its grid-staircase budget is
`2.057322`, just above the R168 target `2`.  The sharper law

```text
N(T) ≤ (3/4) · M · exp(-T/4),        T ≥ 1
```

has both empirical slack and sufficient weighted-sum budget:

```text
max_tail_ratio = 0.665791
budget_const   = 1.542991 < 2
```

## Verdict

The proof target can be sharpened again:

```text
For normalized dyadic periods and all grid thresholds T ∈ 0.5·ℕ, T ≥ 1,
  #{C : |η_C|²/σ² ≥ T} ≤ (3/4) M exp(-T/4).
```

Together with the trivial `N(0)=M` base term and the `h=0.5` staircase
increments for `exp(t/8)`, this closed-form survival bound implies the R168
MGF residual with room to spare.

Two useful lessons:

* The coefficient matters: `exp(-T/4)` alone is too loose for the `≤2` MGF
  budget even though the data satisfy it easily.
* Trying to push the exponent to `0.4` fails at the high-tail singleton
  `(n,p,T)=(32,32993,17.5)`, so high-threshold exceptional cosets impose the
  current rate ceiling.
