# Rate-half predecessor: multi-overlap-only proofs are insufficient

At the exact rate-half predecessor, the proposed boundary has agreement fraction approximately
`33/64` and code dimension `k=n/2`. For three distinct bad scalars with decoding polynomials
`q_i`, eliminating the two received-word rows produces a polynomial of degree `<k` which vanishes
on the triple intersection of their agreement sets. Unless the three polynomials are globally
affinely dependent, this proves only

```text
|S_i intersect S_j intersect S_l| < k.
```

That condition cannot imply the required family-size cap `L<=n`. The executable probe
`scripts/probes/probe_rate_half_triple_overlap_nogo.py` supplies a deterministic counterfamily:

```text
universe length             64
number of distinct sets     65 = n+1
size of every set           33
maximum triple intersection 17 < 32 = k.
maximum pair intersection   24 < 32 = k.
```

All pairs and all `C(65,3)=43680` triples are checked exactly using 64-bit masks. Since every
intersection of at least two members is contained in a pair intersection, every such intersection
has size `<k`. Thus the same family defeats any argument whose only combinatorial conclusion is
that a nonzero degree-`<k` polynomial vanishes on an intersection of two or more agreement sets.
The large triple gap is expected from `(33/64)^3 < 1/2`.

Consequently, a proof of the `31/64` predecessor count must use structure absent from arbitrary
agreement sets: the locator divisibility `Lambda_T | (Z^n-1)`, the `m+1` syndrome recurrence
equations, or compatibility of projective labels across supports. Third-moment/MDS root counting
alone, even with arbitrary fixed overlap order, cannot close the one-rung residual.
