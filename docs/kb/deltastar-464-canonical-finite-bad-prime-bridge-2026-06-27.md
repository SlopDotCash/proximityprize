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
prime-factor set of the obstruction resultant.  The next useful theorem should not try to shrink
`|Res|` below `p`; it should combine a prime-window supply with a bad-set cardinality bound:

```text
# primes in window and congruence class > # canonicalRatioBadPrimes (2^m)
```

would give an existential canonical good prime in that window.  This is the same shape as the
KKH26/BCHKS good-prime residual, but now attached directly to the width-four canonical
resultant lane.

The hard open question is whether this existential canonical refuter can be upgraded to the
specific field used by the prize, or to a universal stack-domination theorem.  Without one of
those upgrades, the result is a clean arithmetic reduction rather than a delta-star pin.
