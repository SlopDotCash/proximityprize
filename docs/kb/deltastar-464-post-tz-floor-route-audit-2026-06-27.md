# Issue #464: post-TZ floor route audit

Date: 2026-06-27.

Status: **critical essay and attack plan**, not a delta-star proof.

## What changed

The Thorner-Zaman powerful-modulus input is no longer the uncertain part of the off-BGK
floor-localization lane.  The note

```text
docs/kb/deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md
```

checks the paper's §3 powerful-modulus refinement and pins the dyadic least-prime exponent at
`12/5+epsilon`, below the prize exponent `4`.  The in-tree arithmetic scaffolds already had the
right shape:

```text
_PowerfulTZThetaGate.lean
_FloorLinnikThornerZamanArrow.lean
_ThornerZamanPNTStatement.lean
FloorClosurePrefixConsumer.lean
```

So the honest post-TZ route is not "prove a better least-prime theorem."  That leg is now
mathematically supplied, modulo formalizing the analytic-number-theory paper itself.  The remaining
load is coding-theoretic:

```text
verified prefix
+ CandidateListExactSuccessor
+ TZPrimeSupply at beta < 4
+ FamilyContainsBudgetedGlobalMax
+ scaled budget
=> WorstCaseIncidenceBounded
=> delta-star lower pin.
```

The last non-arithmetic premise is the sharp one:

```lean
FamilyContainsBudgetedGlobalMax F C delta R B
```

from `_FloorClosureContract.lean`.  It means the proposed floor/profile family `R` contains one
actual global maximizer of the real `StackBadCount`, and that maximizer is within budget.

## New tool proposal A: successor-renormalization

The finite-rung floor evidence is now clean:

```text
a = 4: floor-bad(16) = {17}
a = 5: floor-bad(32) = {97}
```

The positive theorem the route wants is:

```lean
CandidateListExactSuccessor FloorBad
```

or semantically:

```text
CandidateListExactAt a -> CandidateListExactAt (a+1).
```

The natural new tool is a dyadic successor-renormalization operator.  It should compare the
adjacent-realizability scheme over `mu_{2^a}` and `mu_{2^(a+1)}` by splitting the larger domain
into the two fibers over the squaring map

```text
mu_{2^(a+1)} -> mu_{2^a},  z |-> z^2.
```

A proof would try to show that a non-least split prime at rung `a+1` descends to a non-least split
prime or a contradiction at rung `a`, while the least split prime is allowed to be bad because the
domain is densest there.

### Backwards attack on A

This is not formal functoriality.  The prime fields are different at adjacent rungs, and the least
prime `1 mod 2^(a+1)` is not a lift inside the same field as the least prime `1 mod 2^a`.
The scanner predicate is arithmetic over `F_p`, not only a characteristic-zero cyclotomic scheme.
Thus a successor theorem cannot be a purely group-theoretic squaring argument; it needs to track
how realizability changes with both the subgroup and the field prime.

The exact failure surface is already in `FloorClosureSuccessorScanner.lean`:

```text
CandidateListExactAt a and not CandidateListExactAt (a+1)
```

So the first attack on successor-renormalization should be a scanner looking for an adjacent
exact-then-failing pair, not another isolated rung.

Verdict: **promising but unproved**.  The tool to invent is not a recurrence for polynomials alone;
it is a field-sensitive descent theorem for the adjacent-realizability predicate.

## New tool proposal B: maximizer-carrying floor family

The old phrasing "family dominates all stacks" is equivalent to the sharper statement that the
family contains a global maximizer:

```lean
familyDominates_iff_containsGlobalMax
```

So a compressed floor proof does not have to budget every member of a large family.  It only has to
show:

```text
some r in R is a true global maximizer,
and StackBadCount(r) <= B.
```

This suggests a new proof tool: a **maximizer-carrying invariant**.  Instead of classifying every
stack, define a profile invariant `P(u)` and prove that every global maximizer can be moved, without
decreasing bad-scalar count, into one of the floor/profile representatives.

The desired theorem shape is:

```text
for every u, exists r in R, StackBadCount(u) <= StackBadCount(r)
```

but the proof should be by monotone improvement:

```text
u -> normalize(u) -> compress(u) -> r
```

where each step preserves or increases `StackBadCount`.

This is now a checked proof socket in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MaximizerCarryingReduction.lean`.  The Lean theorem

```lean
deltaStar_pin_of_someMaximizerReachesFamily
```

turns three inputs into the delta-star consumer:

1. each primitive stack move is count-nondecreasing;
2. some actual global maximizer reaches the chosen finite family by a finite improvement chain;
3. the reached family is within the bad-scalar budget.

This does not prove the missing monotone-normalization theorem, but it removes the need to prove an
all-stack domination theorem when the attack can instead identify the maximizer locus.

### Backwards attack on B

Finite-action and literal quotient versions are already blocked:

```text
_StackRepresentativeCoverCardinality.lean
```

proves that small symmetry covers cannot literally cover the stack universe.  Ratio-profile
degree obstruction adds another warning: arbitrary sparse ratio profiles require high numerator
degree unless their support is large.  Thus a maximizer-carrying theorem cannot be a simple
low-degree normal form for arbitrary stacks.

The only surviving version is an extremal theorem:

```text
bad scalar maximizers have extra structure not shared by arbitrary stacks.
```

That is a plausible theorem, but it must be proven at the level of maximizers.  A normal form for
all stacks is too strong and already runs into cardinality/degree barriers.

Verdict: **best current coding-theory target**.  It is exactly what the floor lane needs after TZ.

## New tool proposal C: universal obstruction compression

The finite-obstruction selector is now available:

```text
Frontier/FiniteObstructionGoodPrime.lean
```

A stronger, prize-facing version would compress the failure of the universal incidence bound into
one integer obstruction:

```text
exists D != 0,
  forall split p in the prize window,
    (not WorstCaseIncidenceBounded over F_p) -> p | D.
```

Then a TZ window with more primes than `omega(D)` would contain a universally good prime.

### Backwards attack on C

The current finite-obstruction successes are local: canonical width-four or binder predicates.
The universal failure predicate quantifies over all stacks.  A naive product over all stack
resultants is exponentially large, and its number of prime factors can exceed any available
window count.  Worse, an existential good prime in a window is weaker than a theorem for a
specified field unless the prize construction is allowed to choose that field.

Verdict: **a sharp off-BGK dream, not currently a proof route**.  To make it real, one needs a
single small obstruction for universal incidence failure, not a product over local certificates.

## Post-TZ proof/refutation loop

The route now splits into three independent gates:

1. **Uniform floor predicate:** prove `CandidateListExactSuccessor`, or find an adjacent
   exact-then-failing rung.
2. **Budgeted maximizer:** prove the floor/profile family contains a true budgeted global maximizer,
   or beat every family member with scanner witnesses.
3. **Universal obstruction compression:** prove one small obstruction for failure of
   `WorstCaseIncidenceBounded`, or show the obstruction count necessarily grows too fast.

Only gate 2 feeds delta-star without returning to analytic number theory.  Gate 1 merely makes the
modeled floor predicate uniform.  Gate 3 would be a genuinely new arithmetic bypass, but it must be
universal, not local.

## What this criticizes in the previous loop

The previous "finite obstruction plus TZ" idea was too optimistic when read as a prize proof.  TZ
does close the least-prime arithmetic leg for the modeled floor predicate, but the floor predicate
is still only a statement about a selected obstruction family.  The `mcaDeltaStar` consumer never
asks whether the selected obstruction is gone; it asks whether every stack is under budget.

So the next proof attempt should not spend its main effort on least-prime supply.  It should try to
prove an extremal classification:

```text
every global maximizer of StackBadCount is represented by the floor/profile family.
```

or return a counterexample stack.  This is the post-TZ core of the off-BGK route.

## Immediate next experiments

- Implement a scanner that, for a proposed family `R`, tries to satisfy
  `not_familyContainsBudgetedGlobalMax_iff_each_member_above_budget_or_beaten`.
- Search adjacent rungs for the exact-then-failing successor certificate instead of accumulating
  isolated exact rungs.
- Try a maximizer-only profile theorem: prove structural properties under the assumption
  `StackBadCount u` is maximal, rather than trying to normal-form arbitrary stacks.
- If a universal obstruction theorem is attempted, first bound `omega(D)` symbolically.  A proof
  that produces an exponential product obstruction is not usable with the TZ selector.

Bottom line: **TZ moved the floor lane forward, but it also exposed the real remaining theorem.**
The floor route now lives or dies on extremal stack classification / budgeted global maximizer
containment.
