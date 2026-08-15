# Issue #466 G85: endpoint assembly equivalence

Date: 2026-07-10

G85 discharges the tuple-position reconstruction part of the factorial-corrected padding decoder.
For `s ≤ r` and a core-slot embedding `e : Fin s ↪ Fin r`, G84S gives a canonical increasing
enumeration of the complementary `r-s` padding slots. G85 defines

```text
assemble e core padding : Fin r → A
coreAt e word           : Fin s → A
paddingAt e word        : Fin (r-s) → A
```

and proves both inverse laws. In particular, `endpointEquiv` is the explicit equivalence

```text
((Fin s → A) × (Fin (r-s) → A)) ≃ (Fin r → A).
```

This proves that an ordered core, an ordered padding word, and its core-slot embedding reconstruct
one endpoint with no missing positional data. Applying it independently to the two endpoints and
using G81D's relative permutation accounts for exactly the coordinates counted by G81C's
factorial-corrected `PaddingCode`.

## Honest residual

The full decoder still needs one finite-combinatorics extraction theorem: starting from G83M's
canonical core and common-padding *multisets*, choose compatible ordered representatives and the
two core-slot embeddings, then use G81D to relate the two padding orders. G85 proves the subsequent
assembly is lossless; it does not assert this extraction or decoder surjectivity.

Production delta-star remains open. Depths two and three fit the corrected Wick envelope once this
decoder is connected; depths four and above still require additional orbit savings or collective
cancellation.

## Verification

`scripts/pg-iterate.sh` passes. The declarations report only the standard `propext`,
`Classical.choice`, and `Quot.sound` axioms inherited from finite equivalences.
