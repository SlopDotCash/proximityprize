# Issue #466 R392: pair multiplicity is necessary for four-step switching

Date: 2026-07-09

R392 proves the injection

```text
G x pairFiber(G,c) -> fourFiber(G,c),
(x,(u,v)) |-> (x,-x,u,v).
```

Hence

```text
|G| * rep2(c) <= rep4(c),
```

and, for nonempty `G`, any `rep4(c) <= C|G|` theorem forces `rep2(c) <= C`.

This is a necessary-input theorem, not a prize closure.  It shows that finite-characteristic
four-step switching must jointly control:

1. pair-sum multiplicity (the antipodal component); and
2. the primitive four-tuples with no antipodal pair.

An exhaustive prime sweep found that the naive quartic Sidon guard is false: for `n=64`, the five
primes `17318209, 19718977, 26034433, 39451393, 65456257` in `[n^4,4n^4]` have nonzero pair
multiplicity `4` rather than `2`.  No larger multiplicity occurred in 89,855 admissible primes in
that interval.  Thus a constant-multiplicity theorem remains plausible, but exact Sidon transfer
does not.
