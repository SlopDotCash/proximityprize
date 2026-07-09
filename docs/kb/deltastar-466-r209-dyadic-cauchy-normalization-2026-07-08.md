# δ* #466 — R209 dyadic Cauchy normalization

R207/R208 use the abstract pointwise hypothesis

```text
parent_i <= left_i + right_i
```

for squared normalized spectra.  The concrete Gauss-period dilation recursion
first gives the raw triangle inequality

```text
‖η_{G∪ζG}(b)‖ <= ‖η_G(b)‖ + ‖η_G(ζb)‖.
```

R209 supplies the variance-normalization arithmetic needed to pass from raw
norms to squared normalized values:

```text
parent^2 / (2 σ^2) <= left^2 / σ^2 + right^2 / σ^2.
```

The Lean file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R209DyadicCauchyNormalization.lean
```

This is not an analytic estimate; it is the deterministic Cauchy step that
connects the concrete dilation triangle inequality to the abstract MGF tower
consumers.
