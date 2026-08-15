# Issue #466 G86: maximal-split occurrence extraction

Date: 2026-07-10

G86 closes the occurrence-and-cast boundary between the G83M multiset decomposition and G85's
ordered endpoint assembly.

From

```text
coreBag + padBag = valueMultiset word
coreBag.card = s
```

it constructs an embedding `Fin s ↪ Fin r` whose endpoint restriction has value multiset
`coreBag`.  G85 cancellation then shows that the restriction to the canonical complementary slots
has value multiset `padBag`.  The construction uses G85E's `List.Perm.idxBij`, so repeated values
are matched by occurrence and do not require a uniqueness assumption.

Applied simultaneously to two length-`r` endpoints and their G83M maximal cancellation, Lean
constructs left and right core embeddings whose restrictions realize `leftCore` and `rightCore`,
while both canonical-complement restrictions realize the same `commonPart`.  The theorem states
`s ≤ r` explicitly.

The file passes `pg-iterate`; its audited declarations report only the standard quotient/extensional
axioms used by multisets (`propext`, `Classical.choice`, and `Quot.sound`).  The next finite step is
to turn the equal padding value multisets into G81D's relative position permutation and combine the
two G85 inverse laws into one existential decoder representation.  Counted-decoder packaging and
the separate growing-depth analytic primitive-core bound remain open.
