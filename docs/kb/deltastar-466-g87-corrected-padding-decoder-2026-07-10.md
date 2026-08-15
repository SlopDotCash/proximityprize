# Issue #466 G87: corrected maximal-cancellation decoder

Date: 2026-07-10

G87 discharges the combinatorial decoder residual left by G80R/G81C. For a pair of ordered
length-`r` endpoints, cancel their canonical maximal common multiset (G83M) and suppose the residual
depth is `s`. G87 constructs the full corrected code:

```text
(ordered left/right cores,
 left/right core-slot embeddings,
 one ordered common-padding word,
 one relative padding permutation).
```

The proof uses `Multiset.toList` only to choose representatives. G86's `List.Perm.idxBij` matches
occurrences, so repeated values are handled correctly. The complementary padding restrictions are
shown to have the same canonical common multiset by cancellation against the reconstructed core
bags; G86 then supplies their relative permutation.

The main reconstruction theorem is:

```text
exists_code_of_maximalDepth:
  card(leftCore (bag left) (bag right)) = s
  → ∃ code, decode code = (left,right).
```

Choosing one such code yields an injection from the genuine `MaxCancellationSector A r s` into
G81C's `PaddingCode`. Consequently Lean proves the unconditional sector bound

```text
#sector ≤ #CorePair(A,s) · (r descFactorial s)^2 · (r-s)! · #A^(r-s).
```

This is the factorial-corrected envelope with decoder surjectivity fully discharged, rather than
assumed as an interface.

## Consequence and remaining analytic residual

Combined with G82, the full maximal-cancellation sectors at primitive depths two and three fit in
the nominal production Wick budget under the corresponding unrestricted/equal-sum core counts.
The earlier decoder residual is closed.

This is not yet the delta-star prize theorem: primitive depths four and above still need orbit
savings or collective cancellation, and the resulting all-depth energy estimate must still be
wired into `DCEnergyBound` and the production connective tissue.

## Verification

`scripts/pg-iterate.sh` passes. The axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`.
