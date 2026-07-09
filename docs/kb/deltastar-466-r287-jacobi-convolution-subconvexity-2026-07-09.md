# #466 R287: Jacobi-convolution subconvexity target

Date: 2026-07-09

## Subconvexity normal form

R286 reframed the prize as a two-input subconvexity package:

```text
WallHolds ∧ HyperplaneCancellation.
```

The dossier's rounds 15-27 make the second input precise.  After deleting the
diagonal `D = {0} ∪ μ_n`, the corrected hyperplane problem is exactly a
Jacobi-convolution growth problem.

The key theorem is:

```text
R27FullTowerCollapse.fullTower_collapse
```

For the Jacobi coefficient sequence `J : ZMod m -> C`,

```text
Σ_{s≠0} |T(s)|^(2r)
  = (q - 1) * Σ_c |J^{*r}(c)|^2.
```

Thus the prize-facing hyperplane subconvexity input is:

```text
IterConvEnergyWick J q r C:
  Σ_c |J^{*r}(c)|^2 <= C^r * r! * (m q)^r.
```

This is the exact `L^{2r}` subconvexity statement.  The deep wall is the same
bound at `r ≈ log q`.

## Rung status

From the dossier:

```text
r = 1:
  closed by Parseval / orthogonality.

r = 2:
  closed modulo textbook Weil formalization.

r = 3:
  first calibrated open core.
  Gaussian constant is C = 6.
  Probe-safe constant recorded in the dossier is C = 40.

r ≈ log q:
  the full prize wall, equivalent to HyperplaneCancellation/AwaySupBound.
```

## The subconvexity hypothesis to attack

The clean current target is:

```text
JacobiConvolutionSubconvex(C0):
  for every prize-regime dyadic subgroup and every relevant nontrivial χ,
  for all 3 <= r <= ceil(log q),
    IterConvEnergyWick J q r C0.
```

The plausible first theorem is the rung-3 statement:

```text
TripleConvEnergyBound J q C3
```

with any absolute `C3` small enough to feed the ladder constant.  R27 already
proves:

```text
TripleConvEnergyBound J q C
  and C <= 6*K^3
  => IterConvEnergyWick J q 3 K.
```

So a proof of rung 3 by vertical equidistribution of the sextic/Genus-2 family
is not just local progress: it is the first non-Weil rung of the exact
subconvexity ladder.

## Lean socket added

The lane
`Frontier/_R287JacobiConvolutionSubconvexitySocket.lean` now includes the
end-to-end theorem:

```text
prizeFloor_of_rungThree_upgrade
```

It packages the route:

```text
RungThreeSubconvex
  -> DeepJacobiSubconvex
  -> HyperplaneSubconvex
  -> PrizeFloor.
```

Thus the remaining proof obligations are exposed without extra bookkeeping:
prove the rung-3 subconvexity input and supply the concrete Jacobi-to-hyperplane
and hyperplane-to-floor consumers.

It also imports the concrete R66/R27 tower interface and exposes the actual
names:

```text
ConcreteRungThreeSubconvex J q B
  := TripleConvEnergyBound J q B

ConcreteDeepJacobiSubconvexUpTo J q R C
  := forall 3 <= r <= R, IterConvEnergyWick J q r C

ConcreteDeepJacobiCeilSubconvex J q C
  := IterConvEnergyWick J q ceil(log q) C

ConcreteDepthThreeToCeilUpgrade J q C
  := IterConvEnergyWick J q 3 C -> ConcreteDeepJacobiCeilSubconvex J q C
```

The theorem

```text
iterConvEnergyWick_three_of_concreteRungThree
```

uses the calibrated normalization

```text
B <= C^3 * 3!
```

to turn a concrete R23 `TripleConvEnergyBound` into the R27 depth-3 Wick
rung.  The theorem

```text
concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_upgrade
```

then packages the finite-depth ladder: a depth-3-to-`R` upgrade plus the R23
certificate gives `IterConvEnergyWick` for every `3 <= r <= R`.

Finally,

```text
concreteDeepJacobiCeilSubconvex_of_upTo
```

extracts the log-depth endpoint from the up-to-ceiling ladder.  The direct
`pureFace` pointwise consumer remains the existing R27 theorem
`sup_pureFace_of_iterConvEnergyWick`; R287 keeps the log-depth socket at the
`IterConvEnergyWick` layer to avoid dragging stale older tower declarations into
this lightweight endpoint.

The composed endpoint theorem

```text
concreteDeepJacobiCeilSubconvex_of_concreteRungThree_upgrade
concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade
concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade_le_const
```

now turns a calibrated R23 rung-3 certificate plus a depth-3-to-ceiling upgrade
directly into the log-depth `ConcreteDeepJacobiCeilSubconvex` endpoint.  The
`_le_const` variant lets the rung-3 certificate be calibrated at a sharper
constant `C` while the named ceiling-depth upgrade is published at any larger
campaign constant `C'`.

The concrete endpoint can now feed the abstract prize-floor route via:

```text
prizeFloor_of_concreteDeepJacobiCeilSubconvex
prizeFloor_of_concreteRungThree_upgrade
prizeFloor_of_concreteRungThree_endpoint_upgrade
prizeFloor_of_concreteRungThree_endpoint_upgrade_le_const
```

The caller still must supply the concrete-to-abstract interpretation
`ConcreteDeepJacobiCeilSubconvex -> DeepJacobiSubconvex`, the
Jacobi-to-hyperplane consumer, and the hyperplane-to-floor consumer.  The second
theorem composes those consumers with the calibrated R23 rung-3 certificate and
the depth-3-to-ceiling upgrade; the endpoint-upgrade variant uses the named
`ConcreteDepthThreeToCeilUpgrade` prop directly.  The `_le_const` prize-floor
variant is the same end-to-end route with the explicit constant relaxation
`0 <= C`, `C <= C'`, and `B <= C^3 * 3!`.

For comparison, R287 also exposes the recurrence-only R95/R96 route:

```text
concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_left_budget
concreteDeepJacobiCeilSubconvex_of_concreteRungThree_left_budget
prizeFloor_of_concreteRungThree_left_budget
```

These propagate a calibrated rung-3 certificate to all depths, and then to
`ceil(log q)` and the abstract floor socket, under the explicit head budget:

```text
m <= 4*C.
```

This is useful as a checked baseline and for diagnosing constants, but it is
not the desired subconvexity upgrade: for an absolute Wick constant, the budget
is linear in the Jacobi modulus `m`.

The obstruction is now named in the R287 socket:

```text
left_budget_forces_const_ge
left_budget_iff_const_ge
not_left_budget_of_const_lt
```

So any recurrence-only attempt with a published bound `C <= K` and `4K < m`
is rejected before it can be mistaken for the prize-scale upgrade.

The concrete predicates also have the expected adapters:

```text
ConcreteRungThreeSubconvex.mono_const
ConcreteDeepJacobiSubconvexUpTo.mono_depth
ConcreteDeepJacobiSubconvexUpTo.mono_const
ConcreteDeepJacobiCeilSubconvex.mono_const
```

These let a sharp rung-3 or ladder certificate publish at a larger campaign
constant, and let an all-depth certificate restrict to the log-depth endpoint
without unfolding the R23/R27 definitions.

## Why this is genuinely subconvexity

The convexity estimate sees only coefficient mass and gives a pointwise or
Chebyshev loss.  In R19 language, the exact recursion is:

```text
S_{r+1}^D <= M_away^2 * S_r^D.
```

That recursion is tight, but it is self-referential: `M_away` is the prize sup.
The available magnitude/Chebyshev input loses about `sqrt(q)`.

The needed theorem is therefore a subconvex bound for the convolution powers
themselves, i.e. cancellation across the Jacobi phases:

```text
||J^{*r}||_2^2  <<  convexity/Chebyshev scale.
```

At `r = 3`, per-tuple Weil is already insufficient in the prize beta gap, so the
needed saving is vertical family cancellation across the sextic character sums,
not termwise square-root cancellation.

## Next attack directions

1. **Rung-3 vertical Sato-Tate/Katz route.**
   Prove cancellation across the family of sextic curves arising in
   `TripleConvEnergyBound`.  This is the most honest subconvexity theorem to
   try first.

2. **Hasse-Davenport exact angle route.**
   Search for dyadic/coset relations among the Jacobi coefficients that force
   cancellation in `J^{*3}` and then propagate through the convolution ladder.

3. **Direct finite-to-asymptotic bridge.**
   Continue finite certificates only as guardrails.  They should not replace
   the analytic target; they are evidence for where the subconvex asymptotic
   becomes clean.

## Current correction to the finite lane

The finite micro-band branch is useful evidence, but R287 supersedes using it
as the main strategy.  The current finite state remains:

```text
finite certified: M < 25000
remaining micro-band theorem: M >= 25000 => S(0.75) <= 0.404
```

The subconvexity route asks for a theorem explaining that tail, rather than
certifying it indefinitely.
