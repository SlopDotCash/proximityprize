# Issue #466 G84I: endpoint split equivalence

Date: 2026-07-10

For a fixed core-position embedding `e : Fin s ↪ Fin r`, G84I defines restriction of an endpoint
word to its core slots and to G84S's canonical complementary padding slots.  It proves these
restrictions are exact inverses to G84A assembly:

```text
(Fin r → A) ≃ (Fin s → A) × (Fin (r-s) → A).
```

Both inverse laws and the resulting equivalence pass `pg-iterate` with only `[propext]` reported.
Thus all positional reconstruction is complete once the two core embeddings are known.

The remaining full-decoder task is occurrence matching: use G83M's residual core multisets and
`List.Perm.idxBij` to choose embeddings whose restricted words enumerate those cores.  Their
complement restrictions then enumerate the common padding multiset; G81D supplies the relative
padding permutation.  Decoder surjectivity and the G81C cardinal bound follow from those facts.

Production delta-star remains open after this finite-combinatorics bridge because the growing-depth
primitive-core mass still requires an analytic bound.
