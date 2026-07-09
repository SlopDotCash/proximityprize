# #466 R327: endpoint fibers refute the raw relation-count route

Date: 2026-07-09

## Question attacked

R326 proves

```text
shadowCollisionMass
  <= card(shadowKernelRelations) * shadowEnergy.
```

The remaining advertised endpoint was therefore to bound
`card(shadowKernelRelations)` by a quantity exponential only in the moment depth `r`.
R315/R320/R323 suggested that short primitive recurrences and their finite dyadic
recurrence-lattice quotients might provide such a count.

This note records a decisive obstruction: the raw relation set is necessarily enormous at
the logarithmic prize depth, before any exceptional recurrence is considered.

## Exact theorem

`Frontier/_R327RelationCountFiberLowerBound.lean` proves, axiom-clean, that for every finite
field `F`, every `g : F`, and all `n,m,r`,

```text
card(keysR n m r)
  <= card(F) * (card(shadowKernelRelations g n m r) + 1).
```

The proof is elementary and lossless.  In one evaluation fiber, choose a basepoint `v`.
The map

```text
w |-> w-v
```

injects all other fiber points into `shadowKernelRelations`: it is a nonzero realized
difference and its evaluation vanishes.  Summing the fiber bound over `F` gives the theorem.

The file then constructs `m.choose r` pairwise distinct shadow keys explicitly.  For each
cardinality-`r` subset `S` of the positive coordinate half, enumerate every element once;
its shadow endpoint is the indicator vector `1_S`.  Therefore

```text
m.choose r <= card(keysR (2*m) m r),

m.choose r
  <= card(F) * (card(shadowKernelRelations g (2*m) m r) + 1).
```

It also exports the direct falsifier

```text
card(F) * (D+1) < m.choose r
  -> not (card(shadowKernelRelations) <= D).
```

No order assumption on `g`, no probabilistic heuristic, and no sampled computation enters
these statements.

## Prize-scale size

`scripts/probes/probe_r327_relation_count_fiber_lower_bound.py` evaluates the exact integer
consequence

```text
D >= ceil(m.choose r / q) - 1.
```

For the largest prize length `n=2^30`, hence `m=2^29`, with the standard proxy
`q=n*2^128=2^158`, the saddle is `r=ceil(ln q)=110`.  Exact integer arithmetic gives

```text
log2(m.choose r)             = 2598.029349...
log2(forced relation count)  = 2440.029349...
effective base per rung      = 2^22.182085... ~= 4.76 * 10^6.
```

Even using the global field-cardinality cap `q<2^256` and its corresponding saddle
`r=178`, the forced count has `log2 > 3827` and effective base `2^21.50` per rung.

Asymptotically, with `q=Theta(m)` and `r=Theta(log m)`, the standard binomial lower bound
gives

```text
log(card(shadowKernelRelations)+1)
  >= r log(m/r) - log q
  = Theta((log m)^2)
  = Theta(r^2).
```

Thus no uniform `C^r` upper bound with fixed `C` can hold for the raw cardinality.

## Why recurrence saturation does not repair this

R323 identifies a principal recurrence-lattice index with the cyclotomic resultant, and
R321 shows that a dyadic quotient kills relation classes after dyadic scaling.  Those are
correct structural statements, but they do not reduce the number of short lattice points.
The evaluation kernel is a high-dimensional lattice cut out by one finite-field equation;
the squarefree positive endpoints alone force huge fibers, and each fiber forces distinct
short differences.  A primitive generator may organize those points into recurrence
classes, but it cannot compress their raw cardinality to `exp(O(r))`.

This obstruction is independent of the already-refuted local `F_2` hypercontractivity
idea: it uses only fiber entropy and injective subtraction.

## Corrected live target

The R326 pointwise replacement

```text
NR(2m,m,2r,d) <= NR(2m,m,2r,0)
```

is too lossy when summed over all relations.  Any recurrence attack must keep the weights:

```text
sum_d NR(2m,m,2r,d),
```

or prove a bound on the **total mass of each recurrence class**, together with a bound on
the number of heavy classes.  Most of the forced relations must be allowed to have tiny
mass.  Replacing every relation by the zero-mode maximum and then counting is now refuted.

This does not prove the DC-subtracted Wick bound or close the prize; it removes the raw
cardinality endpoint and sharpens the surviving recurrence-class programme to a weighted
one.

## Validation

```text
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R327RelationCountFiberLowerBound.lean

python3 scripts/probes/probe_r327_relation_count_fiber_lower_bound.py
```

Both passed on 2026-07-09.  The Lean axiom audit contains no `sorryAx`.
