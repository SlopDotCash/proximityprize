# Issue #466 G87: maximal-cancellation assembly representation

Date: 2026-07-10

G87 completes the finite positional representation behind the factorial-corrected padding decoder.
It first wraps G81D at the `Fin`-function level:

```text
valueMultiset left = valueMultiset right
  -> exists sigma : Equiv.Perm (Fin n), right = left ∘ sigma.
```

Combining this adapter with G86 and G85, Lean proves that any pair of length-`r` endpoint words
whose left maximal residual has card `s` admits:

- ordered left and right core words on `Fin s`;
- a core-slot embedding for each endpoint;
- one padding word on `Fin (r - s)`;
- one relative permutation of the padding positions;
- exact value-multiset identities with G83M's `leftCore`, `rightCore`, and `commonPart`; and
- exact G84A assembly equations reconstructing both original endpoints.

The theorem assumes `s ≤ r` explicitly.  Repeated values are supported: occurrence selection comes
from G85E, while G81D supplies a relative permutation between padding occurrences.

The file passes `pg-iterate`; the audited declarations report only the standard multiset
quotient/extensional principles (`propext`, `Classical.choice`, and `Quot.sound`).  This closes the
finite occurrence/position reconstruction.  Remaining work for the G81C cardinality bound is to
choose and count the oriented primitive-core coordinate type, define the decoder, and prove sector
membership/surjectivity.  The growing-depth analytic primitive-core mass bound remains a separate
production delta-star residual.
