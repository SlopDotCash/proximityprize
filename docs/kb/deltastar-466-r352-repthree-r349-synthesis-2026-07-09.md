# #466 R352 — the L1-six shell is exactly the `RepThree` residual

The repository already contains the precise order-six object needed here:
`GaussianEnergyThreeRepThree.RepThree`.

`RepThree G` asserts that every zero-sum six-tuple from `G` admits an antipodal
perfect matching. Its validated consumer is
`rEnergy_three_le_of_repThree`, which gives

```text
rEnergy G 3 ≤ 15 · |G|^3.
```

The R350/R351 experiments identify the first nontrivial R324 endpoint shell as
L1 six with coefficient pattern `(+1,+1,+1,-1,-1,-1)`. This is precisely a
zero-sum six-term relation after expanding a shadow difference. Therefore the
correct implication is not “Sidon implies no L1-six”; it is:

```text
RepThree(G) ⇒ every realized L1-six relation is antipodal-trivial.
```

R349 then removes the corresponding high-weight depth-four strata. The finite-
field transfer of `RepThree` is already documented in the existing file as the
open order-six core. This synthesis prevents the false B3/Sidon shortcut and
connects the new R324 shell analysis to the project’s canonical residual.
