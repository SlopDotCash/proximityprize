# Issue #464: outright delta-star attack ledger

Date: 2026-06-27.

Status: **no delta-star proof**. This note records the direct proof/refutation loop after
re-reading the v2 dossier, the ProximityGap workbench, the local domination notes, and the
repo-local Paley/BGK PDF packet. The purpose is to keep the next agents on prize-facing
targets rather than on local obstruction checks that cannot feed `mcaDeltaStar`.

## Prize-facing target

The proof object that would actually pin the floor is still:

```text
OpenCoreConditionalPin.WorstCaseIncidenceBounded C delta B
```

or an equivalent closed theorem giving a universal upper bound on the bad-scalar count:

```text
forall u, StackBadCount F C delta u <= B.
```

A single binder/floor family, a single canonical width-four refuter, or a good-prime statement
for one modeled predicate has the wrong polarity unless it is paired with domination:

```text
forall u, StackBadCount F C delta u
  <= StackBadCount F C delta uStar + slack(profile u).
```

The existing consumers in `_FloorDominationInterface.lean` and
`_ProfileFiberSlackDominance.lean` are exactly the right API. A winning proof should land one of
their certificates, not another local stack budget alone.

## Attempt 1: direct BGK / Paley / moment closure

The local PDFs confirm the dossier's map.

- BGK/Kowalski gives a nontrivial small-subgroup exponential-sum bound
  `|sum_{x in H} e_p(ax)| <= |H| p^{-nu(gamma)}`, with `nu` ineffective and far from the
  `sqrt(|H|)` scale needed here.
- HBK/Stepanov and di Benedetto-style improvements are useful around the `p^(1/4)` boundary or
  above, but they remain power-exponent improvements, not a saddle-depth Wick theorem.
- Liu-Zhou and Podesta-Videla identify the relevant spectrum with generalized Paley graph
  eigenvalues / Gauss periods, but their explicit classifications are small-index or
  semiprimitive; the prize dyadic thin subgroup is not in the semiprimitive escape.
- Kim-Yip-Yoo names the Paley graph conjectural cancellation surface; it is an open input, not
  a proof.

Backwards refutation: any direct moment proof still has to prove the DC-subtracted Wick bound at
depth `r ~= log q`. Low moments, mean-square offset identities, and scalar period magnitudes all
hit the L2-to-Linfty wall already recorded in the dossier.

Verdict: **real target, not currently provable from the local literature**.

## Attempt 2: orbit quotient / Lamzouri-type union bound

The best empirical non-BGK signal remains quotienting frequencies by `mu_n`, reducing the entropy
from `log p` to `log(p/n)`. A Lamzouri-style proof would try to combine:

```text
subGaussian tail for each quotient-period value
+ union bound over (p - 1) / n orbit representatives
=> M(mu_n) <= C sqrt(n log(p/n)).
```

Backwards refutation: the union-bound step is not the hard part. The hard part is the
subGaussian tail at the prize saddle, which is precisely the DC-subtracted high-moment theorem.
Without that tail, the quotient only changes bookkeeping; with that tail, the prize is already
essentially solved.

Verdict: **useful lens, not an escape unless the tail theorem is new**.

## Attempt 3: sparse dominance / profile-fiber slack

This is the strongest non-TZ, non-character-sum-looking attack surface. Chai-Fan/action-orbit
machinery gives real control on sparse/two-monomial inputs, and the workbench localizes the open
gate to domination of unrestricted stacks by sparse representatives.

The exact theorem shape should be one of:

```text
ProfileFiberSlackCertificate F C delta profile rep slack B
```

or the sharper zero-slack/classification version:

```text
forall u, StackBadCount F C delta u
  <= StackBadCount F C delta (rep (profile u)) + slack (profile u)
```

with all used representatives budgeted by `B`.

Backwards refutation: small finite symmetry covers are cardinality-blocked by
`_StackRepresentativeCoverCardinality.lean`. So the theorem cannot be "every stack is in the
orbit of a binder stack" unless the action family is enormous on the nose. The only surviving
form is **true domination without equivalence**: a structural reason every dense/general stack
has no more bad scalars than a sparse representative.

Verdict: **best currently-defined non-wall route**. It is hard, but it feeds the prize API
directly and does not rely on a single modeled floor stack.

## Attempt 4: universal finite-obstruction compression

This is the most promising "crazy idea" if the goal is to bypass analytic cancellation. The
new selector in

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/FiniteObstructionGoodPrime.lean
```

proves the reusable finite step:

```text
if every bad candidate prime divides D != 0
and #candidate_primes > omega(D),
then some candidate prime is good.
```

An outright delta-star version would need a much stronger upstream theorem:

```text
UniversalSingleObstruction:
  exists D != 0,
    forall p in prize_window,
      (exists u, StackBadCount F_p C_p delta u > B) -> p divides D
```

plus a prime-window supply with more candidates than `D.primeFactors.card`. Then the selector
would produce a prime in the window where the **universal** bad-stack event is absent, and the
existing `mcaDeltaStar` consumer could run.

Backwards refutation:

- Current finite-obstruction results control canonical or binder-local predicates, not the
  universal stack supremum.
- If `D` is a product over exponentially many stack/configuration resultants, then
  `omega(D)` can be too large for the prime-window pigeonhole.
- Even a good existential prime does not prove a statement for a prescribed prize field.
- A local "bad prime" predicate must be exactly the failure of `WorstCaseIncidenceBounded`; otherwise
  it removes an obstruction but does not prove the floor.

Verdict: **not a proof, but a precise off-BGK theorem to try**. The missing theorem is not the
selector; it is universal single-obstruction compression with a small prime-factor count.

### Attempt 4b: local-obstruction universalization tax

The finite selector now has a checked multi-obstruction form:

```text
bad_filter_card_le_sum_primeFactors_card_of_local_obstructions
exists_not_bad_of_local_obstructions_sum_lt
```

These theorems prove the exact arithmetic price of trying to universalize a binder-local
bad-prime argument without true compression. If every bad candidate prime divides one of many
local obstruction integers `D_i`, then the number of bad candidates is bounded by

```text
sum_i omega(D_i),
```

not by `omega(product_i D_i)` as a useful black box and not by any single small obstruction.
Consequently, a local-resultant approach can still prove a good prime if the prime window beats
this summed count, but it cannot be sold as a universal floor proof until the index set of local
obstructions and their prime-factor budgets are both controlled.

Backwards refutation: the naive product-over-all-stacks approach is exactly the wrong scale. It
is formally valid, but it replaces the needed `omega(D)` by a sum over all profiles/configurations.
If that sum is exponential or even too large polynomially, TZ/Linnik prime supply cannot clear it.

Verdict: **formal progress, negative pressure on naive universalization**. The off-BGK route now
has a precise subgoal: compress the universal bad-stack predicate to a small obstruction family,
or prove a domination theorem that reduces the family to a sparse/profile representative set.

## Attempt 5: vector hyperplane cancellation

The workbench warns that a bare pointwise Gauss-period bound pays the naive `q * B` conversion and
is insufficient. The operative incidence input needs `sqrt(q) * B`-scale cancellation over the
annihilator hyperplane.

A direct proof should therefore target an operator-valued statement:

```text
for every far stack direction,
the incidence deviation over the annihilator hyperplane is subGaussian
with variance controlled by the mu_n period variance.
```

Backwards refutation: scalar gauges, half-mass splits, local dyadic descents, and average L2
identities have already been shown to relocate the same wall. A vector theorem only helps if it
proves cancellation for the actual hyperplane sum and does not first pass through a pointwise
period maximum.

Verdict: **a real prize-facing route, but it is the analytic wall in incidence form**.

## Assignable next targets

1. `SparseDominanceForWorstStack`: prove a `ProfileFiberSlackCertificate` for a concrete sparse
   profile scheme, or produce a larger-stack counterexample.
2. `UniversalSingleObstruction`: define the universal bad-stack failure predicate and prove it
   divides one integer obstruction `D`, or a local obstruction family with
   `sum_i omega(D_i)` below a TZ/Linnik prime-window count.
3. `HyperplaneIncidenceSubGaussian`: bypass scalar `M(mu_n)` and prove the BCHKS-style
   annihilator-hyperplane cancellation consumed by `WorstCaseIncidenceBounded`.
4. `LamzouriQuotientTail`: turn the quotient entropy reduction into a theorem only if it includes
   the per-orbit subGaussian tail at depth `log q`.
5. `AllMonomialCosetRigidity`: extend finite cyclotomic/symmetric-function rigidity from binder and
   width-four lanes to every monomial direction that can maximize `StackBadCount`.

## Do not spend more cycles on these as prize proofs

- Height-only conditions like `|Res| < p`; the right finite object is the prime-factor set.
- Binder/floor goodness without stack domination.
- Symmetry-cover reductions by small automorphism groups.
- Raw `E_r <= Wick` including the DC term.
- Scalar potential/gauge descents comparable to the true period magnitude.

## Bottom line

The direct proof did not close. The cleanest way forward is to attack the universal stack
supremum, not the local floor obstruction. The finite-obstruction selector is useful only if
upgraded from "this modeled predicate has a good prime" to "failure of the universal incidence
bound has a small single obstruction." Sparse/profile domination is the other realistic
non-literature gate because it already feeds `WorstCaseIncidenceBounded` once proved.
