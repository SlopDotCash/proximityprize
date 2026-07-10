# Issue #466 G81C: relative padding-order ceiling

Date: 2026-07-10

G80R showed that maximal cancellation leaves a common padding multiset whose two endpoint orders
are independent.  The corrected reconstruction code therefore consists of:

```text
primitive core
× left core-slot embedding
× right core-slot embedding
× first padding word
× relative padding permutation.
```

G81C proves its exact cardinality:

```text
|Core| * (r descFactorial s)^2 * (r-s)! * |A|^(r-s).
```

It also proves the generic consumer: any collision sector admitting a surjective decoder from this
code satisfies the factorial-corrected G80R envelope.  A concrete swapped two-slot padding witness
shows the relative-permutation coordinate is genuinely used.

The result is axiom-clean (`[propext]`).  It does not claim decoder surjectivity for the actual
collision sector.  The exact next bridge is:

1. equal tuple multisets imply the two words differ by a permutation of `Fin (r-s)`;
2. maximal componentwise-min cancellation produces disjoint ordered primitive cores;
3. reconstruct the original endpoint pair from those cores, two embeddings, and the relative
   padding data.

Once that bridge lands, G81's full-Wick arithmetic theorem consumes the corrected envelope under
the same primitive-sector condition `J_s*r^s <= n^s`.  Production delta-star remains open.
