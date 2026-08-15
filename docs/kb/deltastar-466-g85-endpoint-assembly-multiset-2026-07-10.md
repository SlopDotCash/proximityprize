# Issue #466 G85: endpoint assembly and complement multiset

Date: 2026-07-10

G85 connects the ordered endpoint assembly of G84A to the multiset cancellation of G83M.  For an
embedding `e : Fin s ↪ Fin r`, Lean proves that assembling a core word and a word on the canonical
complementary slots has value multiset

```text
valueMultiset core + valueMultiset pad.
```

It also proves the fixed-embedding inverse: restricting an endpoint to `e` and to its canonical
complement, then assembling those restrictions, recovers the endpoint exactly.

The decoder-facing cancellation theorem is:

```text
coreBag + padBag = valueMultiset word
valueMultiset (coreAt e word) = coreBag
-------------------------------------------------
valueMultiset (padAt hsr e word) = padBag
```

Thus G85E's occurrence-correct core embedding, combined with the G83M maximal-cancellation split,
forces the complementary restriction to have exactly the common padding bag.  Applying the result
to both endpoints gives equal padding bags, after which G81D supplies the relative position
equivalence used by the factorial-corrected decoder.

The file passes `pg-iterate` with only `[propext]` reported.  It does not by itself extract the core
embedding from G83M or finish G81C decoder surjectivity; those are the remaining finite composition
steps.  The production delta-star theorem also remains open at the separate growing-depth
primitive-core mass estimate.
