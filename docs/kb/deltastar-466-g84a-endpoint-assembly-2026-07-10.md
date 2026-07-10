# Issue #466 G84A: endpoint assembly

Date: 2026-07-10

G84A defines the ordered endpoint assembled from G84S's slot equivalence:

```text
assemble e core pad = Sum.elim core pad ∘ (slotEquiv e).symm.
```

Lean proves exact restriction laws on core slots and canonical padding slots.  Consequently, for a
fixed core-position embedding, assembly is injective in the pair `(core,pad)`.  The file passes
`pg-iterate`; all declarations report only `[propext]`.

The forward decoder is now concrete.  To prove full surjectivity, the remaining inverse construction
must use G83M reconstruction and `List.Perm.idxBij` to extract the core-position embeddings from the
original endpoints, then use G81D to match the two complementary padding orders.  This is a finite
combinatorial task; after it lands, G81C gives the corrected sector count and G81/G82 consume it.

Production delta-star remains open because growing-depth primitive-core counts and the ultimate
DC-energy inequality are not yet controlled.
