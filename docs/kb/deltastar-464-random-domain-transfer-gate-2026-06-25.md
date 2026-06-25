# Issue #464: random-domain transfer gate

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RandomDomainTransferGate.lean`

## Claim

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

unless one proves that the smooth domain is outside the exceptional set.

## Lean contents

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
  fixed domain; a one-domain spike hides in the average.

## Interpretation

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

The exact missing theorem is a derandomization/smooth-domain transfer.  Existing evidence says that
transfer is essentially the same Paley/BGK worst-case incidence wall in another language.
