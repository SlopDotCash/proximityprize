# Issue #466 G88/G89: equal-sum decoder and production depth-three discharge

Date: 2026-07-10

G88 refines G87's corrected maximal-cancellation decoder for additive collision pairs. The finite
alphabet `A` is mapped injectively into an ambient additive cancellation monoid `B`; this is the
correct model for a multiplicative subgroup alphabet `A = G` embedded in its field `B = F`.
Since the
same padding multiset is inserted on both sides, equality of endpoint sums forces equality of the
two residual core sums. The corrected code therefore uses the subtype

```text
EqualSumCorePair(A,B,ι,s)
  = {(leftCore,rightCore) : A^s × A^s | Σι(leftCore) = Σι(rightCore)}.
```

Lean proves the elementary fiber theorem directly: retain the entire left core and the first
`s-1` right entries; equality of mapped sums forces the final mapped value, and injectivity of `ι`
forces the final alphabet symbol. Thus

```text
#EqualSumCorePair(A,s) ≤ #A^(2s-1).
```

Choosing reconstructing codes gives an injection from the genuine equal-sum maximal-depth
collision sector into the corrected padding code. Hence

```text
#collisionSector(r,s)
  ≤ n^(2s-1) · (r descFactorial s)^2 · (r-s)! · n^(r-s).
```

G89 specializes this theorem to `(n,r,s)=(2^30,110,3)` and composes it with G82's exact arithmetic
comparison. The resulting kernel-checked theorem is

```text
#MaxCancellationCollisionSector(A,110,3)
  ≤ 219!! · (2^30)^110
```

whenever `#A = 2^30`, for every injective alphabet embedding `ι : A → B`.

This is an unconditional end-to-end discharge of primitive depth three: canonical maximal
cancellation, repeated-occurrence embeddings, relative padding order, the missing `(r-s)!`, the
equal-sum factor saving, and the production Wick comparison are all included.

## Honest residual

Depth four is the first point where the elementary `n^(2s-1)` bound exceeds the production Wick
budget. The prize remains open on controlling primitive depths `s ≥ 4` collectively or obtaining
additional orbit savings, followed by the all-depth `DCEnergyBound` assembly.

Both files pass `scripts/pg-iterate.sh`; axiom audits contain only standard axioms.
