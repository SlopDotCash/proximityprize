# δ* #466 — R210 raw dyadic prize-tower step

R210 composes R208 with R209.  It lets the current prize-tower route start from
the raw dyadic triangle inequality

```text
rawParent_i <= rawLeft_i + rawRight_i
```

and a positive child scale `σ`, then uses the normalized spectra

```text
parentN_i = rawParent_i^2 / (2 σ^2)
leftN_i   = rawLeft_i^2   / σ^2
rightN_i  = rawRight_i^2  / σ^2
```

inside the R189/R203/R207/R208 chain.

The theorem is:

```text
prize_sq_of_raw_dyadic_prizeTower_child_normalizedBudgets
```

It lands the same squared prize bound as R208.  This moves the remaining
finite-field input closer to the concrete Gauss-period statement: prove the
raw dilation triangle inequality for the actual parent/children, and prove the
large-index normalized child budgets.
