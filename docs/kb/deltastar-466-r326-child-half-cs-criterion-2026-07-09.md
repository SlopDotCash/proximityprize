# R326 dyadic child half-CS criterion

## Hypothesis

The Main/Residual split in the incidence rung is a Fourier conditional
expectation plus martingale difference.  For one dyadic child split, write

`U = A+B`, `V = A-B`.

Set

```text
A4 = sum (A^4+B^4)
C  = 2 sum A^2 B^2
O  = 4 sum (A^3 B+A B^3).
```

Then exactly

```text
sum U^4     = A4 + 3C + O
sum V^4     = A4 + 3C - O
sum U^2 V^2 = A4 - C.
```

The half-CS estimate follows from the single quartic certificate

```text
O^2 <= (5C-A4)(3A4+C).
```

This implication is proved axiom-clean in
`_R326ChildHalfCSCriterion.lean`.

## Probe

`probe_r326_child_half_cs.py` evaluates complete child-coset families at the
first split prime above the fourth-power diagonal.

| child n | p | kappa | A4/C | normalized O |
|---:|---:|---:|---:|---:|
| 8 | 100049 | 0.289020 | 2.626040 | -4.55e-4 |
| 16 | 1048609 | 0.311880 | 2.812943 | -1.68e-4 |
| 32 | 16777601 | 0.322765 | 2.906366 | -4.13e-5 |
| 64 | 268437889 | 0.328087 | 2.953155 | -1.03e-5 |

The ratios approach the independent-Gaussian value `1/3` from below.  The
certificate has large positive slack in every row.

## Honest scope

This does not yet prove the prize or the full Main/Residual rung. It identifies
a concrete one-split theorem: prove the displayed quartic certificate using a
mixed-energy ratio `A4 <= 5C` and control of the odd moment `O`.

Naive iteration is refuted, including under L2 orthogonality.  For
`A=(2,2,2,2)`, `B1=(2,0,0,0)`, `B2=(0,2,0,0)`, each `(A,Bi)` saturates half-CS and
`B1 dot B2=0`, but `(A,B1+B2)` has ratio `1/sqrt(2) > 1/2`.  The exact squared
countermodel is machine checked by `pairwise_half_cs_composition_countermodel`.

Therefore the surviving route needs a global arithmetic martingale
square-function inequality for all dyadic blocks; per-split half-CS plus
orthogonality is insufficient.
