# Issue #464: abstract canonical height no-go

Status: **checked guardrail**, not a delta-star proof.

The concrete `n = 128` height refutation is proof-engineering heavy because it must certify a large
prime and a finite-field collision.  The logical consumer is now factored into:

```lean
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_CanonicalHeightNoGoAbstract.lean
```

The checked predicate is:

```lean
CanonicalBadPrimeAt n p
```

and the consumers are:

```lean
not_forall_canonicalBadPrimeAt_le_n4_of_exists_gt
not_forall_canonicalBadPrimeAt_lt_n4_of_exists_gt
smallest_bad_prime_control_not_height_bound
```

Thus the concrete witness file only has to prove:

```lean
exists p, CanonicalBadPrimeAt 128 p /\ 128^4 < p
```

Once that is supplied, the polynomial-height shortcut is dead: one bad prime above `n^4` refutes
any claim that all canonical bad primes are below `n^4`.

This is a guardrail for the off-BGK floor route.  Least-prime-in-AP controls the smallest relevant
prime; it does not bound the maximum canonical bad prime.  The floor route must not replace the
smallest-prime statement with a global polynomial-height statement.
