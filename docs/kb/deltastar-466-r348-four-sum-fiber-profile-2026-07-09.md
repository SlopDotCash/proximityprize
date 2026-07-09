# #466 R348 — higher-order fiber profile at the n=64 bad endpoint

At `p = 16,778,497`, write `A₂(s)` for the number of ordered pairs
`(x,y) ∈ μ₆₄²` with `x+y=s`, and `A₄=A₂*A₂`. Exact enumeration gives

```text
support(A₄) = 639,489
max A₄      = 12,096
E₄         = ||A₄||₂² = 1,713,759,040.
```

For neighboring primes in the same window, `max A₄` is also `12,096`, while
the K-bad excess comes from a broad change in the multiplicity histogram:
the bad prime has 256 fibers of multiplicity 792 and 448 fibers of
multiplicity 768, whereas the neighboring good primes do not. Hence a bound
on the maximum four-sum fiber is insufficient; the relevant invariant is the
weighted distribution of all higher-order fibers.

This is exactly the quantity exposed by R324:

```text
shadowCollisionMass ≤ (2r)! · Σ_s |Stratum_s| m^s.
```

The next viable theorem must control the entire stratum generating function
`Σ_s |Stratum_s| m^s`, likely via a hypergraph/container or entropy argument,
not via a single recurrence or a maximum-fiber estimate.
