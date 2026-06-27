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
p2_quadT
p2_quadT_eq_e1_sq
e2_quadT_zero
badScalar_quadT_mem_e2BadScalarSet
group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision
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
