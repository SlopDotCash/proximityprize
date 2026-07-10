# Issue #466 G85E: occurrence embeddings

Date: 2026-07-10

G85E turns a permutation

```text
(core ++ padding).Perm endpoint
```

into embeddings of the ordered core prefix and padding suffix into endpoint positions.  It uses
`List.Perm.idxBij`, so repeated values are matched by occurrence rather than by value alone.

Lean proves:

- every embedded core occurrence has the corresponding core value;
- every embedded padding occurrence has the corresponding padding value;
- the core and padding occurrence ranges are disjoint.

The file passes `pg-iterate` with only `[propext]` reported.  This is exactly the occurrence-level
choice needed for the inverse factorial-corrected decoder.  Combining G83M reconstruction with
`Multiset.toList` produces the required list permutation; G85E supplies the core embedding, G84I
then reconstructs the endpoint and identifies its complementary padding word, and G81D relates the
two endpoint padding orders.

The remaining proof is now a composition/cast weld rather than a new counting idea.  Production
delta-star remains open beyond this decoder because growing-depth primitive-core mass still needs
analytic control.
