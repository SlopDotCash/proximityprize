# Issue #466 G88: corrected decoder sector bound

Date: 2026-07-10

G88 packages G87's existential representation into a counted encoding.  It defines the oriented
primitive-core coordinate as a pair of depth-`s` words whose value multisets are disjoint, and the
sector as endpoint pairs whose maximal left residual has card `s`.

For every sector element, G87 supplies a corrected padding code consisting of the primitive core
pair, two core-slot embeddings, one padding word, and one relative padding permutation.  Choosing
one such code for each endpoint pair gives an injective encoder because G84A assembly decodes it
back to the original pair.

Consequently Lean proves the concrete bound

```text
|CancellationSector A r s|
  ≤ |PrimitiveCorePair A s| * (r descFactorial s)^2
      * (r - s)! * |A|^(r - s).
```

This is the intended G81C consumer with decoder representation and injectivity proved rather than
hypothesized.  Repeated endpoint values are covered by G85E/G86 occurrence matching.  An independent
`pg-iterate` check passes; the audited declarations report only the standard multiset
quotient/extensional principles.

The theorem does not bound `|PrimitiveCorePair A s|` uniformly across growing depths. That is the
explicit remaining decoder-side production residual; the independent non-Fourier arc-uniformity
or single-embedding discrepancy bound controlling `M` also remains open. The finite decoder
correction itself is closed.
