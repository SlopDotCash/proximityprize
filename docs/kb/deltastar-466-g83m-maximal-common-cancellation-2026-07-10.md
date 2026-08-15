# Issue #466 G83M: maximal common cancellation

Date: 2026-07-10

G83M formalizes the canonical multiset decomposition needed by the factorial-corrected padding
route.  For endpoint profiles `left` and `right`, define

```text
common    = left ∩ right
leftCore  = left  - common
rightCore = right - common.
```

Lean proves, axiom-clean:

- `leftCore + common = left` and `rightCore + common = right`;
- `leftCore` and `rightCore` are disjoint;
- equal-cardinality endpoints leave equal-cardinality cores;
- every multiset contained in both endpoints is contained in `common` (maximality);
- equality of endpoint sums descends to equality of primitive-core sums in an additive
  cancellation monoid.

This removes ambiguity about “maximal cancellation”: it is unique at the multiplicity-profile
level and produces the exact disjoint primitive relation required by the corrected sector count.

Combined with the landed chain:

1. G81D: equal padding multisets admit a value-preserving position equivalence;
2. G81C: corrected reconstruction-code cardinality includes `(r-s)!`;
3. G81: the lower odd Wick factors pay that factorial;

the only missing combinatorial brick is tuple-position reconstruction: extract the two core-slot
embeddings and padding words from the original ordered endpoints, then prove the decoder is
surjective.  After that, the remaining analytic input is the collective primitive-core count
`J_s`, especially for depth growing with the saddle.  Production delta-star remains open.
