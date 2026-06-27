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
n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
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
