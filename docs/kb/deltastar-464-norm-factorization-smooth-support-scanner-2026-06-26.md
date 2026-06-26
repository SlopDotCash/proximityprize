# Issue #464: norm-factorization smooth-support scanner

Date: 2026-06-26.

Status: **scanner-interface progress**, not a delta-star proof.

## Thesis

The norm-factorization route tries to make the off-diagonal wraparound mechanism concrete: relation
norms should not share large prime factors in a way that creates clustered bad-prime behavior.  The
existing file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_NextNormFactorizationClustering.lean
```

already defines the relation support map `Fac`, the shared-prime `ClusterRate`, and the Poisson
comparison.  The new scanner layer makes the smooth-support residual exact.

## Lean Additions

The added declarations are:

```lean
not_SmoothNormPersistence_iff_exists_large_prime
SmoothNormPersistence_iff_threshold_supports_empty
thresholdSupports_disjoint_of_smooth
clusterRate_threshold_eq_zero_of_smooth
not_thresholdSupports_disjoint_iff_exists_pair_large_common_prime
```

So the residual is no longer phrased as a vague "norms stay smooth" hope.  It has two direct
failure predicates:

```text
some relation has a prime factor p > B,
or two distinct relations share a prime factor p > B.
```

And the positive side is equally explicit:

```text
SmoothNormPersistence Rel Fac B
=> every above-B support is empty
=> above-B supports are pairwise disjoint
=> thresholded ClusterRate is zero.
```

## Consequence

This does not prove the prize.  It isolates the exact finite scanner certificate that a norm route
must produce at growing dyadic rungs: either all relevant relation norms are `B`-smooth at the
threshold, or every claimed smoothness statement must return a concrete large prime witness.

This is complementary to the floor max-containment contract.  The floor route asks whether a
candidate family contains a global worst stack; the norm route asks whether the bad-prime arithmetic
for relation carriers has any above-threshold shared large-prime support left.
