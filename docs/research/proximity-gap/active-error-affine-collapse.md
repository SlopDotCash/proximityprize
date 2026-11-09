# Affine collapse of active errors

[`Frontier/_ActiveErrorAffineCollapse.lean`](../../../ArkLib/Research/ProximityGap/Frontier/_ActiveErrorAffineCollapse.lean)
connects the relation-support result in [PR #262](https://github.com/SlopDotCash/proximityprize/pull/262)
to the decoded-head collapse result in [PR #239](https://github.com/SlopDotCash/proximityprize/pull/239).
It addresses the multi-line error-relation route recorded in
[issue #164](https://github.com/SlopDotCash/proximityprize/issues/164).

For code heads `w_i` and received words `u_0 + gamma_i u_1`, write
`e_i = u_0 + gamma_i u_1 - w_i`. An index is active if some linear relation among
all the `e_i` has a nonzero coefficient at that index. Let `A` contain exactly
those active indices.

The new declarations in namespace `ProximityGap.ActiveErrorAffineCollapse` prove:

- `relation_sum_restrict`: removing inactive indices preserves any relation.
- `full_support_relation_on_active`: if `|A| < |F|`, there is one relation on `A`
  with every coefficient nonzero.
- `affine_heads_of_active_errors`: if `|A| * t < 2D`, all active heads have the
  form `U + gamma_i V`, with both `U` and `V` in the code.

The last theorem requires two active indices with distinct scalar parameters.
Each active head must belong to the code and agree with its received word
outside a set of at most `t` coordinates. The distance hypothesis says that a
codeword supported on fewer than `D` coordinates is zero. Both the coordinate
set and index set are finite, and the field is finite.

These bounds use `|A|`, so the full family may contain additional inactive errors.
The theorem makes no assertion about the heads at those inactive indices. It does
not prove that the canonical bad-witness family is active, bound that family's
size, or change the production threshold. The prize problem remains open.

## Verification

The dependency heads used for the composition are
`03d03bf16e70e9284b73064cfea3db0aed6d76e4` (#239) and
`b5089f1eafdfd7e6010aeb6e010a85e43fb7af62` (#262).

```bash
./scripts/lake-locked.sh build ArkLib.Research.ProximityGap.Frontier._IncidenceDependencyArithmetic ArkLib.Research.ProximityGap.Frontier._SixErrorRankSupportMultiplicity
./scripts/pg-iterate.sh ArkLib/Research/ProximityGap/Frontier/_ActiveErrorAffineCollapse.lean
./scripts/lake-locked.sh build ArkLib.Research.ProximityGap.Frontier._ActiveErrorAffineCollapse
./scripts/validate.sh
```

The new module prints the axioms of all three declarations. The permitted set is
`propext`, `Classical.choice`, and `Quot.sound`.
