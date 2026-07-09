# R317 Heavy-Resonance Inverse Hypothesis

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Candidate mechanism

The `c=3` web suggests an inverse theorem rather than a vanishing theorem.
At depth `r`, call `a/b` a small rational resonance when

```text
1 <= a,b <= r, gcd(a,b)=1, and (a/b)^n = 1 mod p.
```

Equivalently, `a/b` belongs to the dyadic subgroup `mu_n`.  The proposed
heavy-collision inverse says that collision mass substantially above the Wick
scale forces a positive-density translation stabilizer in the shadow collision
hypergraph, and that stabilizer forces a small rational resonance.

This is deliberately stronger than the already-false claim that every
wraparound relation is binomial.  Sparse non-binomial relations exist.  The
claim concerns only a relation *web carrying super-Wick weighted mass*.

## First attempted refutation

`probe_r317_heavy_resonance_inverse.py` checks the complete R305 `n=32`
depth-3 census.  Restricting to `p > n^4`, exactly one prime violates the exact
Wick headroom:

```text
p = 21523361, excess = 58560 > 44800.
```

It has precisely the reduced small resonances `3/1` and `1/3`; this is the
R307--R316 `c=3` relation web.  Thus there are no unexplained high-beta heavy
primes in the complete census.

This is evidence, not a proof.  The next falsification targets are complete
`n=16` and larger sampled `n=64` censuses, followed by depth four, where the
generic bad-prime phenomenon is already known to be much denser.

## Prize-facing form

The useful general statement cannot demand exact Wick.  Rational resonance
webs really exist, so they must be absorbed into the allowed exponential loss:

```text
collisionMass_r(mu_n)
  <= K^r * (2r-1)!! * n^r + resonanceMass_r(mu_n),
resonanceMass_r(mu_n)
  <= K_res^r * (2r-1)!! * n^r.
```

The intended proof architecture is:

1. weighted Balog--Szemeredi on the shadow collision graph;
2. translation stabilizer extraction for a super-Wick component;
3. sparse signed-basis rigidity, turning the stabilizer into `a*zeta^h=b`;
4. a transfer-matrix or hypercontractive bound for each rational-resonance web;
5. sum over reduced pairs `a,b <= r`, only `O(r^2)` possibilities.

At prize depth `r = O(log p)`, the polynomial `O(r^2)` family count is harmless
inside `K^r`.  The two genuinely new obligations are steps 2--4.  Proving them
would control logarithmic depth without asserting the refuted exact-Wick law.

## Status

Conjecture-grade.  The complete `n=32`, depth-3 high-beta census passes the
first adversarial test.  No prize closure is claimed.
