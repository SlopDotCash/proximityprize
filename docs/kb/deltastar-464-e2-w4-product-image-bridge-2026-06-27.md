# Issue #464: width-4 product witnesses land in the e2 bad-scalar image

Date: 2026-06-27.

Status: **source bridge for the orbit scanner**, not a delta-star proof.

## What Was Formalized

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/E2W4CyclotomicNonCollision.lean
```

now connects the width-4 product-form parametrization directly to the concrete image used by
`E2DilationDirectCount.e2BadScalarSet`.

New theorem surface:

```lean
quadT_card
quadT_subset_of_mem
neg_one_mem_nthRootsFinset_of_even
quadT_subset_nthRootsFinset_of_even
p2_quadT
p2_quadT_eq_e1_sq
e2_quadT_zero
badScalar_quadT_mem_e2BadScalarSet
badScalar_quadT_mem_e2BadScalarSet_of_mem
not_cd0NonCollision_iff_exists_collision
not_cd0NonCollision_of_collision
cd0NonCollision_of_no_collision
Cd₀NonCollisionModSign
cd0NonCollisionModSign_of_cd0NonCollision
not_cd0NonCollisionModSign_iff_exists_collision
not_cd0NonCollisionModSign_of_collision
cd0NonCollisionModSign_of_no_collision
invariant_neg_eq_neg_invariant
invariant_ne_neg_of_two_ne_zero
not_cd0NonCollision_of_antipodal_collision
not_cd0NonCollision_of_neg_mem
not_cd0NonCollision_nthRootsFinset_of_even
not_cd0NonCollision_nthRootsFinset_of_even_charZero
orbits_distinct_of_nonCollisionModSign
badScalar_orbits_distinct_of_nonCollisionModSign
group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision
group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision
group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_nonCollision
group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_modSignNonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_modSignNonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_nonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_nonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_modSignNonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision
n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_nonCollision
not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_modSignNonCollision
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_pairNonCollision
invariantRatio
invariantPairNonCollision_iff_ratio_notMem
not_invariantPairNonCollision_iff_ratio_mem
invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one
not_invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_eq_one
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_ratioPowNeOne
canonicalRatioPoly
canonicalRatioPoly_eval_map
canonicalRatioPoly_monic
canonicalRatioPoly_natDegree_map_zmod
canonicalRatioPoly_eval_zmod_eq_zero_of_polynomial_eq
invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq
invariantRatio_zeta_sq_pow_ne_one_iff_polynomial_ne
invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
polynomial_eq_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
complex_root_of_unity_real_eq_one_or_neg_one
complex_root_add_inv_im_eq_zero
invariantPairNonCollision_complex_primitive_zeta_sq
invariantRatio_pow_ne_one_complex_primitive_zeta_sq
polynomial_ne_complex_primitive_zeta_sq
resultant_canonicalRatioPoly_ne_zero
prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
prime_le_natAbs_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
canonicalRatioPoly_eval_nnnorm_le_two_pow_succ
natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient
polynomial_ne_zmod_of_resultant_natAbs_lt_prime
polynomial_ne_zmod_of_two_pow_succ_totient_lt_prime
not_e2BadScalarSet_mu_card_le_n_zmod_of_two_pow_succ_totient_lt_prime
canonicalRatioPolySharpBound
natAbs_resultant_canonicalRatioPoly_comm
natAbs_resultant_canonicalRatioPoly_twoPow_sq_le
prime_sq_le_canonicalRatioPolySharpBound_of_e2BadScalarSet_mu_card_le_twoPow_zmod
not_e2BadScalarSet_mu_card_le_twoPow_zmod_of_canonicalRatioPolySharpBound_lt_prime_sq
canonicalRatioResultant
canonicalRatioBadPrimes
mem_canonicalRatioBadPrimes
canonicalRatioBadPrimes_card_le_natLog
canonicalRatioBadPrimes_card_le_crude
mem_canonicalRatioBadPrimes_of_e2BadScalarSet_mu_card_le_n_zmod
not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes
canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp
CanonicalWidthFourGoodPrimeSupply
refuter_of_canonicalWidthFourGoodPrimeSupply
canonicalRatioPoly16_reduction_zmod
canonicalRatioPoly16_bezout
polynomial_ne_zmod16_of_prime_gt17
prime_eq_seventeen_of_polynomial_eq_zmod16
polynomial_ne_zmod16_of_prime_ne17
not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_gt17
not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_ne17
canonicalRatioPoly32ReducedPrimitive
canonicalRatioPoly32_reduction
canonicalRatioPoly32_bezout
prime_not_dvd_canonicalRatioPoly32_bezout_const
polynomial_ne_zmod32_of_prime_gt1153
not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_gt1153
n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even
not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even
orderOf_4134_ratio
isPrimitiveRoot_4134_16_ratio
polynomial_4134_sq_pow16_ne
invariantRatio_4134_sq_pow16_ne_one
sixteen_lt_e2BadScalarSet_mu16_card_zmod12289_width4
not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4
orderOf_19_ratio_zmod97
isPrimitiveRoot_19_32_ratio_zmod97
polynomial_19_sq_pow32_ne_zmod97
invariantRatio_19_sq_pow32_ne_one_zmod97
thirtytwo_lt_e2BadScalarSet_mu32_card_zmod97_width4
not_e2BadScalarSet_mu32_card_le_32_zmod97_width4
orderOf_3_ratio_zmod17
isPrimitiveRoot_3_16_ratio_zmod17
invariantRatio_3_sq_pow16_eq_one_zmod17
polynomial_eq_3_sq_pow16_zmod17
invariant_collision_scalar_5_zmod17
exists_invariant_collision_mu16_zmod17_3
not_invariantPairNonCollision_mu16_zmod17_3
not_forall_primitive_pairNonCollision_zmod17_mu16
seventeen_dvd_resultant_canonicalRatioPoly_16
seventeen_le_natAbs_resultant_canonicalRatioPoly_16
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
exists_invariant_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
not_e2BadScalarSet_mu_card_le_n_zmod_of_resultant_natAbs_lt_prime
not_cd0NonCollisionModSign_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
exists_cd0ModSign_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
```

## The Bridge

For a product-form quadruple

```text
quadT x t = {x, -x, x * t, x * t^-1}
```

with the expected six distinctness hypotheses, Lean proves:

```text
(quadT x t).card = 4
p2(quadT x t) = e1(quadT x t)^2
e2(quadT x t) = 0
```

If `quadT x t` is contained in an ambient subgroup `G`, `t != 0`, and `t + t^-1 != 0`, then its
bad scalar

```text
x^-1 * (-(t + t^-1)^-1)
```

belongs to:

```lean
e2BadScalarSet G 4
```

## Why This Matters

The orbit-budget scanner says the literal `n` budget fails once the concrete `e2 = 0` image contains
two full `mu_n` bad-scalar orbits.  This bridge gives a verified source of elements in that image
from the width-4 product parametrization.

It still does not bound the number of image orbits.  It removes one plumbing gap: product-form
width-4 witnesses are now available to the exact direct-count image, so any future non-collision or
collision argument can feed the orbit scanner without restating the symmetric-function membership
proof.

The theorem `group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision` packages the negative
scanner direction: two product-form witnesses with distinct non-colliding invariants force two
bad-scalar orbits in the image, hence the subgroup-size budget already fails.

Follow-up: the same refuter is now specialized to the actual smooth-domain subgroup
`mu_n = nthRootsFinset n 1`.  The theorem
`n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision` removes the final abstract subgroup-card
rewrite, using `IsPrimitiveRoot.card_nthRootsFinset` to state the conclusion as

```lean
n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card
```

and `not_e2BadScalarSet_mu_card_le_n_of_two_quadT_nonCollision` packages the corresponding literal
budget failure.

The follow-up `*_of_mem` / `*_mem_nonCollision` wrappers remove the manual subset argument.  Given
`-1 ∈ G` and `x,t ∈ G`, `quadT_subset_of_mem` proves `quadT x t ⊆ G`; the concrete `mu_n`
wrappers take `-1 ∈ nthRootsFinset n 1` as an explicit reusable hypothesis.  For even/dyadic
domains, `neg_one_mem_nthRootsFinset_of_even` and `quadT_subset_nthRootsFinset_of_even` discharge
that containment bridge directly.  The final even wrappers
`n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision` and
`not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_nonCollision` consume only `2 ∣ n` and
membership of `x,x',t,t'` in `mu_n`.

Follow-up: `E2DilationDirectCount.ne_zero_of_mem_finSubgroup` packages the reusable fact that
members of a finite multiplicative subgroup are nonzero.  The `*_of_mem`, `*_mem_nonCollision`,
and `*_even_nonCollision` product wrappers now derive `t != 0` and `t' != 0` from membership, so
callers no longer pass those nonzero side conditions separately.

The non-collision residual itself now has an exact scanner-facing failure form.  The theorem
`not_cd0NonCollision_iff_exists_collision` says that `Cd₀NonCollision G` fails exactly when there
are `t,t',u ∈ G` with nonzero distinct invariants `t + t^-1`, `t' + t'^-1` and
`t' + t'^-1 = u * (t + t^-1)`.  The companion wrappers
`not_cd0NonCollision_of_collision` and `cd0NonCollision_of_no_collision` expose the two one-way
forms for callers that have either a concrete collision witness or a no-collision scanner
certificate.

Critical correction: the quotient-free `Cd₀NonCollision` residual is false on the even smooth
domains used by the prize.  If `-1 ∈ G` and `2 != 0`, the antipodal pair `t` and `-t` has
invariants related by multiplication by `-1`.  Lean now proves this as
`not_cd0NonCollision_of_antipodal_collision`, with the concrete smooth-domain wrappers
`not_cd0NonCollision_nthRootsFinset_of_even` and
`not_cd0NonCollision_nthRootsFinset_of_even_charZero`.  The correct future bridge must quotient the
antipodal sign class before asserting non-collision.  This is a refutation of an over-strong
scanner hypothesis, not a delta-star floor proof.

Follow-up: the repaired residual is now named `Cd₀NonCollisionModSign`.  It permits the trivial
equality and antipodal sign classes, and only forbids collisions when `c != c'` and `c != -c'`.
Lean exposes the exact failure scanner
`not_cd0NonCollisionModSign_iff_exists_collision`, the scanner-positive wrapper
`cd0NonCollisionModSign_of_no_collision`, and the usable orbit bridges
`orbits_distinct_of_nonCollisionModSign` /
`badScalar_orbits_distinct_of_nonCollisionModSign`.  This restores the width-4 bridge in the
correct sign-quotiented form; it still leaves the sign-quotiented non-collision proof as the real
finite/primality residual.

The repaired bridge also has budget-consumer wrappers.  The group-level
`group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision` and membership-only
`group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_modSignNonCollision` feed the existing
two-orbit image-budget refuter.  The concrete smooth-domain wrappers
`n_lt_e2BadScalarSet_mu_card_of_two_quadT_modSignNonCollision` and
`n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision` state the conclusion directly
as `n < #(e2BadScalarSet mu_n 4)` under sign-distinct invariants.
The matching `not_e2BadScalarSet_mu_card_le_n_*_modSignNonCollision` wrappers package the literal
budget failure, and the even-`mu_n` wrappers discharge `-1 ∈ mu_n` from `2 ∣ n`.

Final specialization: for even `n > 8`, the canonical witnesses `quadT 1 ζ` and `quadT 1 ζ^2`
discharge the membership, nonzero, distinctness, and sign-separation side conditions from primitive
root facts.  The wrappers
`n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision` and
`not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision` reduce the concrete
width-4 scanner failure to the repaired residual `Cd₀NonCollisionModSign mu_n` alone.

Sharper local specialization: the global repaired residual is stronger than the fixed canonical
pair actually needs.  The pointwise residual `InvariantPairNonCollision G t t'` says only that the
second invariant is not in the first invariant's `G`-orbit.  Lean now identifies this with a single
ratio-membership test:

```lean
InvariantPairNonCollision G t t' ↔ invariantRatio t t' ∉ G
```

assuming `t + t^-1 != 0`, where

```lean
invariantRatio t t' = (t' + t'^-1) * (t + t^-1)^-1.
```

For `G = mu_n`, this becomes the algebraic root test

```lean
InvariantPairNonCollision mu_n t t' ↔ invariantRatio t t' ^ n != 1.
```

The canonical wrappers
`n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne` and
`not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_ratioPowNeOne` reduce the fixed
`quadT 1 ζ`, `quadT 1 ζ^2` scanner failure to proving
`invariantRatio ζ (ζ^2) ^ n != 1`.  This is a narrower polynomial/norm-style residual, not a
delta-star proof.

The same residual now has a denominator-cleared polynomial form.  For primitive `ζ` with `8 < n`,
Lean proves that

```lean
invariantRatio ζ (ζ^2)^n != 1
  ↔ (ζ^4 + 1)^n != (ζ^2 + 1)^n
```

after clearing the nonzero denominator `ζ^2 + 1`.  The wrappers
`n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe` and
`not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe` expose this
denominator-free polynomial nonvanishing statement as the scanner-facing target.  Conversely,
`polynomial_eq_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even` says any successful literal
`n` budget in the canonical lane forces the polynomial equality
`(ζ^4 + 1)^n = (ζ^2 + 1)^n`.

The denominator-cleared obstruction is also packaged as the integer polynomial
`canonicalRatioPoly n = (X^4 + 1)^n - (X^2 + 1)^n`.  Lean records its evaluation formula over any
commutative ring, proves it is monic for `0 < n`, proves mapping to `ZMod p` preserves its degree,
and exposes `canonicalRatioPoly_eval_zmod_eq_zero_of_polynomial_eq` as the bridge from the
finite-field polynomial equality back to a root of the integer carrier.

Over `ℂ`, this fixed canonical ratio residual is now discharged unconditionally for primitive
`ζ` with `8 < n`.  The theorem `invariantPairNonCollision_complex_primitive_zeta_sq` proves that
any collision scalar would be real, hence `±1`, using
`complex_root_of_unity_real_eq_one_or_neg_one` and `complex_root_add_inv_im_eq_zero`; the existing
primitive-root separation lemmas rule out both signs.  The wrappers
`invariantRatio_pow_ne_one_complex_primitive_zeta_sq`,
`polynomial_ne_complex_primitive_zeta_sq`,
`n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even`, and
`not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even` expose the corresponding
ratio, denominator-cleared polynomial, and image-budget conclusions over `ℂ`.  The polynomial
nonvanishing theorem is the exact nonzero input for a cyclotomic-resultant bad-prime argument.
This is characteristic-zero evidence for the local lane, not a finite-field discharge for the prize
prime.

That bad-prime route is now formalized for the canonical polynomial carrier.  Lean proves the
integer resultant of `cyclotomic n` and `canonicalRatioPoly n` is nonzero, then shows a finite-field
vanishing of the denominator-cleared obstruction forces `p` to divide that resultant and hence
`p <= |resultant|`.  The contrapositive theorem
`polynomial_ne_zmod_of_resultant_natAbs_lt_prime` turns an explicit resultant bound into the
polynomial nonvanishing needed by the scanner lane.  The shared resultant helper in
`CyclotomicResultantBound.lean` now also has the generic forms
`nnnorm_prod_eval_cyclotomic_roots_le_of_bound` and
`natAbs_resultant_cyclotomic_le_of_bound`, so future canonical-polynomial height estimates can
plug in an arbitrary per-root bound `B` instead of the original four-term constant `4`.
The first plugged-in canonical estimate is intentionally crude:
`canonicalRatioPoly_eval_nnnorm_le_two_pow_succ` bounds each root evaluation by `2^(n+1)`,
`natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient` turns this into
`|resultant| <= (2^(n+1))^phi(n)`, and
`polynomial_ne_zmod_of_two_pow_succ_totient_lt_prime` packages the resulting good-prime
contrapositive.  The direct scanner wrapper is
`not_e2BadScalarSet_mu_card_le_n_zmod_of_two_pow_succ_totient_lt_prime`.

For two-power domains there is also a sharper coefficient-side Landau/Mahler gate.  The explicit
quantity `canonicalRatioPolySharpBound m` is
`4^deg(canonicalRatioPoly (2^m)) * (sum_i |coeff_i|^2)^(2^(m-1))`.  Lean proves
`natAbs_resultant_canonicalRatioPoly_twoPow_sq_le`, so a surviving literal budget over `ZMod p`
forces `p^2 <= canonicalRatioPolySharpBound m`; the scanner-facing contrapositive is
`not_e2BadScalarSet_mu_card_le_twoPow_zmod_of_canonicalRatioPolySharpBound_lt_prime_sq`.  This is
the current explicit finite arithmetic target for this width-four resultant lane.

`Frontier/CanonicalWidthFourBadPrimeSet.lean` packages the same resultant obstruction as an
actual finite set.  `canonicalRatioBadPrimes n` is the prime-factor set of
`canonicalRatioResultant n`, and
`mem_canonicalRatioBadPrimes_of_e2BadScalarSet_mu_card_le_n_zmod` proves that any surviving
canonical literal budget over `ZMod p` puts `p` in that set.  The contrapositive
`not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes` is the finite-set
scanner form, while `canonicalRatioBadPrimes_card_le_crude` and
`canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp` give crude and sharp divisor-count bounds.
The named hypothesis `CanonicalWidthFourGoodPrimeSupply` isolates the remaining arithmetic input:
produce a primitive-root prime outside this finite set in the desired range.

The `n = 16` canonical obstruction also has an exact good-prime certificate.  The theorem
`canonicalRatioPoly16_reduction_zmod` reduces the denominator-free obstruction modulo
`ζ^8 = -1` to an explicit `17 * 48` multiple of a cubic in `ζ^2`, and
`canonicalRatioPoly16_bezout` gives a Bezout identity showing that this cubic is incompatible with
`(ζ^2)^4 + 1 = 0` unless `7 = 0`.  Lean packages the consequence as
`polynomial_ne_zmod16_of_prime_gt17` and the scanner-facing budget refuter
`not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_gt17`: for every prime `p > 17`, the canonical
primitive-root width-4 lane cannot satisfy the literal `<= 16` image budget.
The follow-up theorem `prime_eq_seventeen_of_polynomial_eq_zmod16` removes the external lower
bound: a primitive 16-th-root denominator-free collision forces `p = 17`.  Equivalently,
`polynomial_ne_zmod16_of_prime_ne17` and
`not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_ne17` refute the same canonical lane for every
prime `p != 17`.

The local obstruction is not merely abstract: `ZMod 12289` already supplies a finite checked
witness at `n = 16`.  Lean proves `4134` has order `16`, checks the denominator-free
`polynomial_4134_sq_pow16_ne`, derives `invariantRatio 4134 (4134^2)^16 != 1`, and derives
`16 < #(e2BadScalarSet (Polynomial.nthRootsFinset 16 (1 : ZMod 12289)) 4)`.  The declaration
`not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4` is the corresponding literal budget refuter
for that concrete subgroup.

The same concrete finite-field lane now has a smaller `n = 32` check.  In `ZMod 97`, Lean proves
that `19` has order `32`, checks
`((19 : ZMod 97)^4 + 1)^32 != ((19 : ZMod 97)^2 + 1)^32`, and derives
`32 < #(e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod 97)) 4)`.  The packaged literal
budget refuter is `not_e2BadScalarSet_mu32_card_le_32_zmod97_width4`.

The `n = 32` canonical obstruction now also has an exact generic good-prime certificate above a
finite threshold.  With `y = ζ^2`, Lean reduces
`(ζ^4 + 1)^32 - (ζ^2 + 1)^32` modulo `y^8 + 1` to
`272 * canonicalRatioPoly32ReducedPrimitive y`, then uses `canonicalRatioPoly32_bezout` to show
that a primitive reduced collision forces `430704758627551 = 0`.  Since this Bezout constant has
prime factors only `79, 97, 113, 641, 673, 1153`, the theorem
`polynomial_ne_zmod32_of_prime_gt1153` refutes the denominator-cleared collision for every prime
`p > 1153`, and `not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_gt1153` packages the literal
width-4 scanner refuter.

There is also a deliberately recorded bad-prime collapse.  In `ZMod 17`, `3` is a primitive
16-th root, but `invariantRatio 3 (3^2)^16 = 1` and the denominator-cleared polynomial equality
holds.  The theorem `invariant_collision_scalar_5_zmod17` checks the scalar `5` directly,
`exists_invariant_collision_mu16_zmod17_3` packages it as a root-of-unity collision, and
`not_forall_primitive_pairNonCollision_zmod17_mu16` refutes any uniform finite-field version of the
canonical pairwise residual without excluding bad primes.  The follow-up declarations
`seventeen_dvd_resultant_canonicalRatioPoly_16` and
`seventeen_le_natAbs_resultant_canonicalRatioPoly_16` route this same bad prime through the
canonical integer resultant, confirming that the abstract bad-prime certificate detects the first
measured collapse and matching the exact `p > 17` good-prime certificate above.

The backwards direction is now explicit too.  If the literal budget
`#(e2BadScalarSet mu_n 4) <= n` holds in the canonical fixed-witness lane, Lean derives both the
pointwise collision
`exists_invariant_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even` and the
ratio obstruction
`invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even`.  The global
residual converse
`not_cd0NonCollisionModSign_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even` and exact
failure extractor
`exists_cd0ModSign_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even` package the
same outcome against `Cd₀NonCollisionModSign mu_n`: a successful literal `n` budget now forces an
explicit nonzero, sign-distinct invariant collision.

For `ZMod p`, this converse also has a resultant form.  The theorems
`prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod` and
`prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod` state that a
surviving literal budget forces `p` to divide, hence be bounded by, the same nonzero resultant.
The contrapositive
`not_e2BadScalarSet_mu_card_le_n_zmod_of_resultant_natAbs_lt_prime` is the scanner-facing finite
field certificate once an explicit resultant bound is available.

The resultant lane now also has a finite bad-prime API in
`Frontier/CanonicalWidthFourBadPrimeSet.lean` and the companion KB note
`deltastar-464-canonical-finite-bad-prime-bridge-2026-06-27.md`.  The definitions
`canonicalRatioResultant n` and `canonicalRatioBadPrimes n` package the prime factors of
`Res_Z(Phi_n, canonicalRatioPoly n)`.  The key scanner-facing theorem is
`not_e2BadScalarSet_mu_card_le_n_zmod_of_not_mem_canonicalRatioBadPrimes`: a prime carrying a
primitive `n`-th root and lying outside this finite factor set refutes the literal width-4
`<= n` budget.  The count bounds `canonicalRatioBadPrimes_card_le_crude` and
`canonicalRatioBadPrimes_twoPow_card_le_natLog_sharp` convert the crude and sharp resultant
envelopes into bad-prime cardinality bounds.  This improves the arithmetic residual from
`|resultant| < p` to prime-factor avoidance, but it remains a canonical local lane rather than a
delta-star floor proof.
