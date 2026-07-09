# δ* #466 — R210 Gauss-period normalized Cauchy

R209 proves the pure real normalization

```text
parent^2 / (2 σ^2) <= left^2 / σ^2 + right^2 / σ^2
```

from a raw triangle inequality.  R210 composes that arithmetic with the
concrete Gauss-period dilation recursion

```text
‖η_{G∪ζG}(b)‖ <= ‖η_G(b)‖ + ‖η_G(ζb)‖.
```

The new Lean file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R210GaussPeriodNormalizedCauchy.lean
```

It exposes both the one-step dilation statement and the valid-tower step form:

```text
‖η_{towerStep(k+1)}(b)‖^2 / (2 σ^2)
  <= ‖η_{towerStep(k)}(b)‖^2 / σ^2
     + ‖η_{towerStep(k)}(ζ_k b)‖^2 / σ^2.
```

This does not prove the quarter-MGF concentration residual.  It removes a
normalization bookkeeping layer between the exact tower recursion and the
squared-spectrum MGF interface.
