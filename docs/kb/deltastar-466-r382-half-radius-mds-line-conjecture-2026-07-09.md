# R382: half-radius MDS line conjecture (2026-07-09)

## Direct target

Let `H` be a parity-check matrix of an `[n,k]` MDS code.  Write

```text
B_e = union_{|T|<=e} span(H_T).
```

The tight-budget prize-shaped examples reduce to the following finite-geometric claim.

> **Half-radius MDS line conjecture.** If `2e<n` and `e+k+1<=n`, then every
> projective syndrome line `P` not contained in one support span has at most `n`
> points in `B_e`.

At `e=n/2-1`, this is exactly the numerator bound needed to make the lattice
predecessor of `1/2` good when `floor(p/2^128)=n`.  Together with the already-proven
overlap-packing bad point at `1/2`, it would pin `mcaDeltaStar=1/2` for rates
`1/4`, `1/8`, and `1/16` in the certified prize-shaped field.

This conjecture is stronger than a dyadic-only statement.  Current evidence has not
found a need for multiplicative-subgroup structure, although R380 shows that odd torsion
changes the equality mechanisms.

## Falsification status

The sharper proposed bound `2e+1` is false.  R380 certifies an `[6,2]` MDS syndrome
line over `F_7` with six proper weight-two points, while `2e+1=5`.  Its mechanism is
cubic torsion; R381 proves that exact resonance cannot occur in a two-power subgroup.
The weaker `n` bound is saturated, not refuted.

Small exact and sampled results:

```text
[4,1], e=1, F_5:  exhaustive maximum 2 <= 4
[5,1], e=2, F_7:  exhaustive maximum 4 <= 5
[6,2], e=2, F_7:  exhaustive maximum 6 = n
[8,2], e=3, F_17 dyadic: 500,000 sampled lines, maximum 8 = n
[8,1], e=3, F_17 dyadic: 500,000 sampled lines, maximum 4
[16,4], e=7, F_97 dyadic: 10,000 sampled sparse-point lines, maximum 8
```

The `[8,2]` equality supports are the four facets of each side of a partition into
two four-sets.  This generalizes: for a partition `A union B` into two `(e+1)`-sets,
the intersection `span(H_A) intersect span(H_B)` has dimension `k`; a projective line
inside it meets every facet hyperplane, producing up to `n` low-weight points.

## Exact n=16 annihilator search

`scripts/probes/probe_r382_dyadic_half_n16.py` represents each seven-support span by
the five locator annihilators

```text
X^j Z_T(X),  0<=j<5,  Z_T(X)=prod_{x in T}(X-x).
```

Thus a line `b+gamma*d` meets `span(H_T)` exactly when the two five-vectors
`A_T b` and `A_T d` are proportional.  All `C(16,7)=11440` supports are tested in
one batched exact calculation modulo `97`.

The probe also enumerates all `C(16,8)=12870` candidate third half-spans against the
canonical partition intersection.  No third half-span contains a two-dimensional
pencil.  The partition construction attains exactly sixteen distinct proper points;
no structured counterexample above sixteen was found.

## Why the obvious proofs fail

1. The ordinary secant variety is useless here.  At `e=n/2-1` and `D=n-k`, its
   Zariski closure fills the ambient space whenever `2e>=D`.
2. Unique sparse representation only covers `k<=2` at this radius.  It fails at the
   first production-rate case `[16,4]`.
3. Constant Johnson list size at rates `1/8` and `1/16` does not directly bound a
   line of received words.  The standard MCA collapse pays for the joint list at
   overlap `2(n-e)-n=2`, where no useful list bound is available.
4. The generic quotient interpolation spread lies near capacity: its agreement
   fraction essentially equals its code rate.  It does not specialize to the
   half-radius predecessor at rates below `1/2`.

## Promising proof shape

The statement is a line-versus-secant-subspace theorem for an MDS arc, or equivalently
a worst-case two-dimensional coset-leader theorem.  A proof must retain the finite
support arrangement rather than its secant-variety closure.  The partition equality
case suggests a higher-order-MDS/subspace-design argument: more than `n` proper points
should force one pencil into three or more half-support spans, after which an MDS(3)
intersection inequality gives a contradiction.  The missing implication is precisely
the combinatorial extraction from many distinct `e`-supports to those half-spans.

This is now the shortest direct route to an exact operational pin on the tight-budget
branch.  It remains a conjecture, not a proven prize closure.
