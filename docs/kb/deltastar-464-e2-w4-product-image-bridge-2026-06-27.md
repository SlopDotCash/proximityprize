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
invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq
invariantRatio_zeta_sq_pow_ne_one_iff_polynomial_ne
invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
complex_root_of_unity_real_eq_one_or_neg_one
complex_root_add_inv_im_eq_zero
invariantPairNonCollision_complex_primitive_zeta_sq
invariantRatio_pow_ne_one_complex_primitive_zeta_sq
n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even
not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even
orderOf_4134_ratio
isPrimitiveRoot_4134_16_ratio
invariantRatio_4134_sq_pow16_ne_one
sixteen_lt_e2BadScalarSet_mu16_card_zmod12289_width4
not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
exists_invariant_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
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
denominator-free polynomial nonvanishing statement as the scanner-facing target.

Over `ℂ`, this fixed canonical ratio residual is now discharged unconditionally for primitive
`ζ` with `8 < n`.  The theorem `invariantPairNonCollision_complex_primitive_zeta_sq` proves that
any collision scalar would be real, hence `±1`, using
`complex_root_of_unity_real_eq_one_or_neg_one` and `complex_root_add_inv_im_eq_zero`; the existing
primitive-root separation lemmas rule out both signs.  The wrappers
`invariantRatio_pow_ne_one_complex_primitive_zeta_sq`,
`n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even`, and
`not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even` expose the corresponding
ratio and image-budget conclusions over `ℂ`.  This is characteristic-zero evidence for the local
lane, not a finite-field discharge for the prize prime.

The local obstruction is not merely abstract: `ZMod 12289` already supplies a finite checked
witness at `n = 16`.  Lean proves `4134` has order `16`, checks
`invariantRatio 4134 (4134^2)^16 != 1`, and derives
`16 < #(e2BadScalarSet (Polynomial.nthRootsFinset 16 (1 : ZMod 12289)) 4)`.  The declaration
`not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4` is the corresponding literal budget refuter
for that concrete subgroup.

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
