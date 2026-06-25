# Issue #464: random-domain transfer gate

Date: 2026-06-25

Status: axiom-clean Lean gate; does not solve the floor.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RandomDomainTransferGate.lean`

## Inputs checked

- Live issue #464 still asks for the explicit smooth-domain RS delta-star floor, not a random
  evaluation-domain theorem.
- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md` records random RS and
  random-domain MCA statements as external probability-space results.
- `docs/kb/deltastar-research-map.md` separates domain-random capacity evidence from the fixed
  smooth-domain target.
- `docs/kb/derand-subspace-route-DEAD-caps-at-johnson.md` explains why the subspace-design
  derandomization route is domain-blind for plain RS and therefore cannot by itself use smoothness.

## Claim tested

Random-RS, folded-RS, and subspace-design proximity/list-decoding theorems are valuable nearby
positive results, but they do not automatically prove the explicit smooth-domain RS floor.  Their
quantifier is different.

The prize target fixes the smooth subgroup domain.  A theorem of the form

```text
there exists a good evaluation domain
```

or

```text
all but a small exceptional set of domains are good
```

does not imply

```text
the designated smooth subgroup domain is good
```

unless one proves a fixed-domain certificate such as `Good smoothDomain`, proves zero exceptions
such as `badDomainCount Good = 0`, or proves that the smooth domain is outside the exceptional set.

## Lean result

The file abstracts the issue to a finite domain family `Omega` and a predicate `Good : Omega -> Prop`.

- `ExistsGoodDomain Good`: at least one domain is good.
- `AllDomainsGood Good`: every domain is good.
- `FixedDomainGood Good omega0`: the designated domain is good.
- `badDomainCount Good`: the number of bad domains.
- `fixedDomainGood_of_allDomainsGood`: the valid transfer direction.
- `fixedDomainGood_of_no_bad_domains`: zero exceptions certify the fixed domain.
- `existsGoodDomain_not_force_fixedDomainGood`: Boolean countermodel; `true` is good but the fixed
  domain `false` is bad.
- `one_exception_can_be_the_fixed_domain`: even one exceptional domain can be exactly the smooth
  domain.
- `averageDomainBound_not_force_fixedDomainBound`: average-domain score bounds do not bound the
  fixed domain; a one-domain spike hides in the average.  A usable average-domain theorem would need
  concentration below a one-domain atom or an explicit exclusion of the smooth domain from the bad
  set.

## Consequence for #464

This is the derandomization analogue of the prime and tail atom gates already in the frontier.
The missing bridge from GG25/random-RS-style results to #464 must be one of:

1. a theorem that every relevant smooth subgroup domain is good;
2. a theorem that the smooth subgroup domain is not exceptional for the random-domain theorem;
3. a structural domination theorem transferring the random/subspace-design code-family property to
   the explicit smooth subgroup.

Without such a bridge, random-domain capacity is evidence and context, not a proof of the smooth
plain-RS delta-star floor.

## Effect on the floor problem

This does not solve the floor.  It rules out a recurring shortcut:

```text
random RS / subspace-design reaches capacity, therefore smooth plain RS reaches the prize floor.
```

The exact missing theorem is a derandomization/smooth-domain transfer.  In the current map, that
transfer appears to run into the same Paley/BGK worst-case incidence wall in another language.

## What new math would look like

Any successful import from the random-domain literature must prove one of the following fixed-domain
bridges:

- a uniform theorem: every domain in the relevant family is good;
- a smooth-domain theorem: the specific subgroup/coset domain used by the prize is good;
- a zero-exception theorem: the bad-domain count is zero;
- a non-exception theorem: the random-domain exceptional set is proved not to contain the smooth
  domain;
- a domination theorem: the smooth-domain incidence/list-decoding profile is bounded by a proved
  good random/subspace-design profile.

Without one of these bridges, random-domain capacity is evidence and context, not a proof of the
smooth plain-RS delta-star floor.
