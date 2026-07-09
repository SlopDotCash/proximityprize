# Issue #466 R322: signed-walk endpoint envelope

Date: 2026-07-09

## Proven bound

For a depth-`2r` signed-basis walk ending at `d`, let

```text
ell = sum_j |d_j|,   s = (2r - ell) / 2.
```

Every multiplicity profile has unique nonnegative cancellation counts `c_j` with

```text
positive_j = c_j + max(d_j, 0),
negative_j = c_j + max(-d_j, 0),
sum_j c_j = s.
```

The resulting endpoint count obeys

```text
NR(2m,m,2r,d) * s! * product_j |d_j|! <= (2r)! * m^s.       (E)
```

Indeed, the multinomial contribution of a fixed `c` is

```text
(2r)! / product_j ((c_j+d_j^+)! (c_j+d_j^-)!).
```

Using `(c+a)! >= c! a!` and discarding one of the two remaining `c_j!` factors bounds
this by

```text
((2r)! / (s! product_j |d_j|!)) * multinomial(s; c_0,...,c_{m-1}).
```

Summing uses the exact multinomial identity

```text
sum_{sum c_j=s} multinomial(s;c) = m^s.
```

An exhaustive independent check verified (E) for every endpoint with `m,r <= 4`, including
all `8^8 = 16,777,216` depth-eight words at `m=4`.

## Lean status

`_R322SignedWalkEndpointEnvelope.lean` proves, axiom-clean:

* `countPerms_eq_sum_erase`: the value-erasure recurrence for `countPerms`, generalized
  from natural-valued multisets to arbitrary decidable alphabets;
* `tupleMultiset_fiber_card_eq_countPerms`: over any finite alphabet, the number of tuples
  with a prescribed multiplicity multiset is exactly its multinomial `countPerms`;
* `sum_multinomial_piAntidiag`: the exact multinomial mass identity above;
* `sum_composition_weight_le`: a pointwise `C * multinomial` profile bound sums to
  `C * m^s` with no loss.
* `multinomial_signedProfile_envelope`: the denominator-cleared termwise endpoint bound
  for multiplicities `(c+a,c+b)`.
* `tupleVec_encodeSignedTuple_eq_counts`: the ArkLib shadow endpoint is exactly positive
  multiplicity minus negative multiplicity.
* `tupleMultiset_eq_profile_of_endpoint`: for the disjoint positive/negative decomposition
  of an endpoint, every tuple has the unique profile `c_j = min(P_j,N_j)`.
* `tupleCancellationProfile_eq_of_profile`: the converse recovers the same `c`, making the
  cancellation-profile partition fiberwise exact.

The weld is complete.  The file additionally proves:

* `card_canonicalEndpointTuples_eq_sum_multinomial`: the exact endpoint fiber is the sum
  of profile multinomials over cancellation vectors;
* `card_canonicalEndpointTuples_factorial_envelope`: summing the termwise bounds gives the
  canonical endpoint envelope;
* `NR_eq_card_canonicalEndpointTuples`: `signedIndexEquiv` transports that count exactly
  to ArkLib's `NR`;
* `NR_factorial_envelope`: the headline bound (E) for arbitrary integer endpoints, using
  the canonical positive/negative decomposition of every coefficient.
* `shadowRelationMass_factorial_envelope`: via R321, every realized finite-field kernel
  relation inherits the same factorial suppression on its exact collision mass.

Thus (E) is an axiom-clean Lean theorem, not a conjecture or probe.

## Prize relevance

R321 rewrites each realized relation mass as `NR(2m,m,2r,d)`.  Bound (E) then penalizes a
relation of `L1` length `ell` by approximately `m^{-ell/2}` relative to the central Wick
fiber.  This makes a length-stratified resultant or recurrence-lattice census materially
stronger than the existing uniform autocorrelation cap.
