# G94: arbitrary core embeddings factor through canonical slots

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G94CanonicalCoreSlotFactorization.lean`.

After the G83 orbit-quotient retraction, G84's honest saving comes from canonical increasing core
positions, not from quotienting endpoint scale. G94 proves the key transport statement:

```text
e = canonicalEmbedding(e.range) ∘ σ
```

for a permutation `σ : Perm (Fin s)`. More generally, the theorem accepts any stored `s`-element
slot subset whose elements are exactly the range of `e`.

The permutation is explicit: an original core index is sent to the rank of its endpoint position
in the sorted slot subset. Finite injectivity proves it is bijective. Thus arbitrary occurrence
embeddings carry no positional information beyond:

- the underlying `s`-subset of endpoint slots; and
- a permutation that can be absorbed by reordering the stored core word.

This is the principal finite transport lemma needed to replace G87's two arbitrary embeddings by
G84's two canonical slot subsets in the actual maximal-cancellation decoder. The final decoder weld
must still transport both core words and prove the complementary padding permutation statement.

`scripts/pg-iterate.sh` passes. Both declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`.
