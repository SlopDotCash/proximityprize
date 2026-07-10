# Issue #466 G85: endpoint assembly and multiset cancellation

Date: 2026-07-10

Lean file:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G85EndpointAssemblyMultiset.lean`.

G85 connects G83M's multiset cancellation with G84A's ordered endpoint assembly. It proves:

- value multisets are invariant under finite equivalence reindexing;
- an assembled endpoint has multiset `coreBag + padBag`;
- restricting an arbitrary endpoint to fixed core slots and their canonical complement, then
  assembling, recovers the endpoint exactly;
- if the selected core slots realize a prescribed core bag, multiset cancellation forces the
  complementary slots to realize the prescribed padding bag.

All declarations compile with only `propext`.

The remaining finite inverse bridge is precise: given G83M's residual core multiset, select an
embedding of its occurrences into the original endpoint positions. Once that selection is proved,
G81D supplies the relative padding permutation and the corrected decoder can be made surjective.
Growing-depth primitive-core control and the production delta-star bound remain open.
