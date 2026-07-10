# Issue #466 G97: actual depth-four energy weld

Date: 2026-07-10

G97 removes the last type-level gap between the corrected mapped decoder and the production moment
object. It constructs explicit finite equivalences proving

```text
#EqualSumCorePair({x // x∈G}, F, Subtype.val, s)
  = Finset.addREnergy s G
  = SubgroupGaussSumMoment.rEnergy G s.
```

The equivalence is occurrence-preserving: words over the subgroup subtype correspond to ambient
field-valued words belonging to `Fintype.piFinset G`, and the equal-sum subtype corresponds to the
filtered product used by `addREnergy`.

Two applications of the existing axiom-clean convolution recurrence give

```text
rEnergy G 4 ≤ #G^4 · rEnergy G 2.
```

Combining this with G96 yields the actual subgroup-facing production theorem

```text
#G = 2^30
(rEnergy G 2)^2 ≤ 128 · (2^30)^5
------------------------------------------------
#depthFourCollisionSector(G,110) ≤ 219!! · (2^30)^110.
```

Thus depth four is reduced end-to-end to one explicit fixed-depth second-energy estimate, with no
alphabet-closure fiction and no free-orbit undercount.

## Honest residual

The explicit HBK/Shkredov second-energy inequality is not proved here. G97 establishes its exact
consumer and the convolution transport. The all-depth centered anomaly wall from the sibling G96
depth–moment weld remains open.

During validation, G95 was also found to lack the direct import providing `Finset.addREnergy`.
Adding `ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy` restores standalone frontier
validation and removes the resulting `sorryAx` fallout.

`scripts/pg-iterate.sh` passes; standard axioms only.
