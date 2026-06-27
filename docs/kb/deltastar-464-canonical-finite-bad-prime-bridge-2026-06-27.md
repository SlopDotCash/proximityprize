# Delta-star #464: canonical finite bad-prime bridge

This iteration turns the width-four canonical resultant lane into a finite bad-prime API.
It is a real improvement over the previous "if `p` exceeds the resultant" theorem, but it is
not a delta-star floor proof.

## Tool

For the denominator-cleared canonical obstruction

```text
canonicalRatioPoly n = (X^4 + 1)^n - (X^2 + 1)^n,
```

define the integer carrier

```text
canonicalRatioResultant n =
  Res_Z(Phi_n, canonicalRatioPoly n).
```

The new Frontier file
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/CanonicalWidthFourBadPrimeSet.lean`
defines

```text
canonicalRatioBadPrimes n =
  primeFactors(|canonicalRatioResultant n|).
```

The theorem `mem_canonicalRatioBadPrimes` identifies membership with prime divisibility of the
nonzero resultant.  This is the correct finite obstruction set for the canonical fixed-witness
lane: any finite-field collision in that lane must reduce the characteristic-zero nonzero
algebraic integer to zero modulo a prime above `p`, hence must divide the resultant.

## What landed

The scanner-facing statement is
`not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes`:
if `p` carries a primitive `n`-th root and

```text
p notin canonicalRatioBadPrimes n,
```

then the canonical width-four lane refutes the literal budget

```text
#(e2BadScalarSet(mu_n, 4)) <= n.
```

The proof is deliberately short: a surviving budget already implies
`prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod`; rewriting that
divisibility as membership in the finite prime-factor set gives the contradiction.

Two count bounds were packaged:

* `canonicalRatioBadPrimes_card_le_crude`:
  `#bad <= phi(n) * (n + 1)`, from the crude root-evaluation envelope
  `|Res| <= (2^(n+1))^phi(n)`.
* `canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp`:
  for `n = 2^m`, `#bad <= log_2(canonicalRatioPolySharpBound m)`, from the
  Landau/Mahler squared resultant bound.

Finally, `CanonicalWidthFourGoodPrimeSupply m` names the honest remaining input:
there exists a prime carrying a primitive `2^m`-th root and avoiding
`canonicalRatioBadPrimes (2^m)`.  The theorem
`refuter_of_canonicalWidthFourGoodPrimeSupply` consumes exactly that input and returns a
literal width-four budget refuter for one supplied prime.

Follow-up: the prime-window pigeonhole is now wired too.  The theorem
`exists_tzWindow_notMem_canonicalRatioBadPrimes` says that a Thorner-Zaman window with more
primes than the finite canonical bad-prime set contains a prime outside that set.  The wrappers
`canonicalWidthFourGoodPrimeSupply_of_TZ`,
`canonicalWidthFourGoodPrimeSupply_of_TZ_crude`, and
`canonicalWidthFourGoodPrimeSupply_of_TZ_sharp` turn the raw, crude-count, and sharp-count
versions of that comparison into `CanonicalWidthFourGoodPrimeSupply`.  The direct wrappers
`refuter_of_TZ_canonicalBadPrimeCount`, `refuter_of_TZ_canonicalCrudeBadPrimeCount`, and
`refuter_of_TZ_canonicalSharpBadPrimeCount` compose that supply with the scanner refuter.

Worked finite-exception example: the same principle now has a fully explicit `n = 32` refinement
in `E2W4CyclotomicNonCollision.lean`.  The reduced Bezout constant factors as

```text
430704758627551 = 79 * 97 * 113 * 641 * 673 * 1153.
```

The threshold theorem `polynomial_ne_zmod32_of_prime_gt1153` was already enough to refute all
primes above the largest factor.  The sharper theorem
`prime_eq_97_or_641_or_673_or_1153_of_polynomial_eq_zmod32` uses the primitive-root condition
`32 | p - 1` to eliminate `79` and `113`, and uses the same condition to make the content factor
`272` nonzero.  Thus the canonical `n = 32` denominator-cleared collision can occur only at
`97, 641, 673, 1153` inside the primitive-root lane.  The scanner wrapper
`not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_not_97_641_673_1153` is the corresponding
finite-exclusion good-prime form.
The list is also sharp: `exists_primitive_polynomial_eq_zmod32_badPrimes` packages concrete
primitive-root collapses at all four remaining characteristics, witnessed by
`28 : ZMod 97`, `25 : ZMod 641`, `149 : ZMod 673`, and `439 : ZMod 1153`.

The concrete TZ ladder now feeds this exact row directly at two closed finite-field witnesses:
`exists_mu32_width4_refuter_zmod1217` uses the small `β = 2` row and
`exists_mu32_width4_refuter_zmod1048609` uses the `β = 4` row.  In both cases Lean supplies an
explicit primitive 32nd root and uses `p > 1153` to refute the literal width-four `<= 32` budget.
These close concrete canonical `n = 32` witnesses without asserting a general prime-supply theorem.

The same exact four-prime exception list is now also composed with the concrete TZ-window supply
rows in `Frontier/CanonicalWidthFourConcreteTZ.lean`.  The generic theorem
`exists_tzWindow_mu32_width4_refuter_of_TZ` says any `TZPrimeSupply 32 β supply` with
`4 < supply` contains a window prime outside `{97, 641, 673, 1153}` and therefore refutes the
literal width-four `<= 32` budget.  The concrete wrappers
`exists_tzWindow_mu32_width4_refuter_beta2`, `_beta3`, and `_beta4` instantiate this for the
existing `tzPrimeSupply_32_two`, `tzPrimeSupply_32_three`, and `tzPrimeSupply_32_four` rows.

## Why this does not close the prize

The new theorem changes the shape of the residual from a size inequality to a finite-set
avoidance problem.  That matters, but it does not solve the arithmetic.

The previous sufficient condition was too strong:

```text
|Res| < p.
```

The finite-set version only needs:

```text
p does not divide Res.
```

This is strictly better for existential good-prime arguments, because a large resultant may have
few prime factors and many primes in a Thorner-Zaman or Linnik window can avoid them.  However, it
does not prove that a specified prize prime avoids the set.  A single large prime divisor of the
resultant could still be the prize prime.

It also remains a canonical local lane.  Even if every prize-scale prime were good for this
fixed width-four pair, the delta-star floor still needs a universal domination theorem from all
dangerous stacks to such canonical witnesses, or a separate BGK/Paley cancellation mechanism.
The bridge is therefore useful substrate, not the floor.

## Critical takeaway

The height-only attack was the wrong stopping criterion.  The right arithmetic object is the
prime-factor set of the obstruction resultant.  The next useful theorem was not to shrink
`|Res|` below `p`, but to combine a prime-window supply with a bad-set cardinality bound:

```text
# primes in window and congruence class > # canonicalRatioBadPrimes (2^m)
```

The new TZ wrappers prove exactly this existential canonical good-prime step.  This is the same
shape as the KKH26/BCHKS good-prime residual, but now attached directly to the width-four
canonical resultant lane.

The hard open question is whether this existential canonical refuter can be upgraded to the
specific field used by the prize, or to a universal stack-domination theorem.  Without one of
those upgrades, the result is a clean arithmetic reduction rather than a delta-star pin.
