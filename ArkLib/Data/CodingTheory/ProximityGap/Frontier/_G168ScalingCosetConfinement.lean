/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# G168: a scaling of order `d` that fixes a minimal zero-sum support confines it to one coset

The G165 scaling-ladder arc (Shaw's #466 comment `ac6b62994`, Klein-orbit normalization
`4 ∣ genericPrimitiveCorePairs`) reduces the primitive census residue mod `2^k` to the action of the
cyclic `2`-Sylow `H ≤ F_p^*` by scaling on the *minimal zero-sum supports* `minimalZeroSumSupports`.
The Fable referee (2026-07-11 06:35 UTC) refereed the full ladder and *explicitly ranked the
coset-stabilizer lemma as the single decisive next proof for the formalizer*, with a finite
group-theory mechanism:

> If `g` has multiplicative order `d > 1` and `g · S = S`, then `S` is a union of the multiplicative
> cosets `x⟨g⟩`.  The sum of any nontrivial finite subgroup of `F_p^*` is `0`, so each coset
> `x⟨g⟩` is itself a zero-sum subset.  Minimality then forbids a proper zero-sum subset, so `S` must
> be a **single** coset: `S.card = d`, and the stabilizer is exactly `⟨g⟩`.

The companion file `_G167NegationStabilizerCollapse.lean` (opus-core, landed `e3f9843b1`) handles only
the *negation* special case `d = 2` (`g = -1`), giving `S.card = 2`.  This file proves the **general
order-`d` ladder statement**, of which G167 is the `d = 2` instance:

```text
  g^d = 1,  g ≠ 1  (order exactly d),  x ≠ 0,  {x·gⁱ : i < d} = S,  and S is a minimal
  zero-sum support   ⟹   S.card = d.
```

The core new arithmetic content beyond G167 is the **coset geometric-sum vanishing**
`∑_{i<d} x·gⁱ = 0` for `g^d = 1, g ≠ 1` (Mathlib `geom_sum_mul`, factoring `gᵈ - 1 = 0`), and the
**distinct-powers** count `card {x·gⁱ : i < d} = d` when `g` has order `d`.  Together with minimality
this pins the support to one coset of exactly `d` elements, so the accident sector of the ladder is
exactly the power-of-the-order sizes `s = d`, and every size not equal to any fixing order is a free
`H`-orbit.

## Honest scope

This is a structural finite-field group-action theorem.  It exactly identifies the fixed sector of a
single order-`d` scaling on minimal zero-sum supports and forces the support size to be that order.
It is a **congruence / classification, not a magnitude bound**: it does not bound the census count
`N_s` in size, and it does not touch the BGK/Paley barrier that binds the free-orbit magnitudes at
production depth.  **CORE remains open.**  Issue #466 (G168).

No `axiom`, no `sorry`, no `native_decide`; over an arbitrary field.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G168ScalingCosetConfinement

open Finset

variable {K : Type*} [Field K] [DecidableEq K]

/-- A finite set `S` of field elements is a **zero-sum support** if it is nonempty, avoids `0`, and
its elements sum to `0`. -/
structure IsZeroSumSupport (S : Finset K) : Prop where
  nonempty : S.Nonempty
  zero_not_mem : (0 : K) ∉ S
  sum_zero : ∑ x ∈ S, x = 0

/-- A zero-sum support is **minimal** if every nonempty `T ⊆ S` with `∑ T = 0` is all of `S`. -/
structure IsMinimalZeroSumSupport (S : Finset K) : Prop extends IsZeroSumSupport S where
  minimal : ∀ T : Finset K, T ⊆ S → T.Nonempty → (∑ x ∈ T, x = 0) → T = S

/-- The **cyclic scaling orbit** of `x` under `g`: the image `{x·gⁱ : i < d}`. -/
def scalingOrbit (x g : K) (d : ℕ) : Finset K :=
  (Finset.range d).image (fun i => x * g ^ i)

section GeomSum

/-- **Geometric-sum vanishing.**  If `g ^ d = 1` and `g ≠ 1` (so `g` is a nontrivial `d`-th root of
unity), the geometric sum `∑_{i<d} gⁱ` vanishes in the field.  This is the finite-subgroup
sum-is-zero fact in geometric-series form. -/
theorem geom_sum_eq_zero_of_pow_eq_one {g : K} {d : ℕ} (hpow : g ^ d = 1) (hg : g ≠ 1) :
    ∑ i ∈ Finset.range d, g ^ i = 0 := by
  have hmul : (∑ i ∈ Finset.range d, g ^ i) * (g - 1) = g ^ d - 1 := geom_sum_mul g d
  rw [hpow, sub_self] at hmul
  have hne : g - 1 ≠ 0 := sub_ne_zero.mpr hg
  exact (mul_eq_zero.mp hmul).resolve_right hne

/-- **A scaling orbit is zero-sum.**  For a nontrivial `d`-th root of unity `g` and any `x`, the
orbit `{x·gⁱ : i < d}` sums to `x · (∑_{i<d} gⁱ) = 0`.  Distinctness of the powers is *not* needed
for the sum: we sum the underlying function over `range d` and use `Finset.sum_image` only in the
distinct case; here we go through the multiset directly. -/
theorem sum_scalingOrbit_eq_zero {x g : K} {d : ℕ}
    (hinj : Set.InjOn (fun i => x * g ^ i) (Finset.range d))
    (hpow : g ^ d = 1) (hg : g ≠ 1) :
    ∑ y ∈ scalingOrbit x g d, y = 0 := by
  unfold scalingOrbit
  rw [Finset.sum_image (by intro a ha b hb hab; exact hinj ha hb hab)]
  have : ∑ i ∈ Finset.range d, x * g ^ i = x * ∑ i ∈ Finset.range d, g ^ i := by
    rw [Finset.mul_sum]
  rw [this, geom_sum_eq_zero_of_pow_eq_one hpow hg, mul_zero]

end GeomSum

section Confinement

/-- **Cardinality of a distinct scaling orbit.**  When the map `i ↦ x·gⁱ` is injective on
`range d`, the orbit has exactly `d` elements. -/
theorem card_scalingOrbit {x g : K} {d : ℕ}
    (hinj : Set.InjOn (fun i => x * g ^ i) (Finset.range d)) :
    (scalingOrbit x g d).card = d := by
  unfold scalingOrbit
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **The scaling coset-confinement theorem (G168).**

Let `K` be a field, `g : K` a nontrivial `d`-th root of unity (`g ^ d = 1`, `g ≠ 1`) whose scaling
orbit of `x` is genuinely `d`-element (injective, `x ≠ 0` and the powers distinct).  If the orbit
`{x·gⁱ : i < d}` is contained in a minimal zero-sum support `S` (e.g. because `S` is invariant under
scaling by `g` and `x ∈ S`), then `S` equals that orbit and hence

```text
  S.card = d.
```

This is the general order-`d` ladder statement.  For `d = 2`, `g = -1`, it specialises to G167's
negation collapse `S.card = 2`. -/
theorem card_eq_order_of_scaling_fixes
    {S : Finset K} (hS : IsMinimalZeroSumSupport S)
    {x g : K} {d : ℕ}
    (hinj : Set.InjOn (fun i => x * g ^ i) (Finset.range d))
    (hpow : g ^ d = 1) (hg : g ≠ 1)
    (hsub : scalingOrbit x g d ⊆ S)
    (hne : (scalingOrbit x g d).Nonempty) :
    S.card = d := by
  have hsum : ∑ y ∈ scalingOrbit x g d, y = 0 := sum_scalingOrbit_eq_zero hinj hpow hg
  have heq : scalingOrbit x g d = S := hS.minimal _ hsub hne hsum
  rw [← heq, card_scalingOrbit hinj]

/-- **Nonemptiness of a positive-length orbit.** -/
theorem scalingOrbit_nonempty {x g : K} {d : ℕ} (hd : 0 < d) :
    (scalingOrbit x g d).Nonempty := by
  unfold scalingOrbit
  exact (Finset.nonempty_range_iff.mpr hd.ne').image _

/-- **Ladder consequence (free-orbit form).**  If a minimal zero-sum support `S` admits a fixing
order-`d` scaling with a distinct `d`-element orbit inside it, then `S.card = d`; contrapositively,
for any size `s` that is *not* the order of a fixing scaling, no such orbit sits inside `S`, so the
size-`s` supports carry no order-`d` accident and the group acts freely there. -/
theorem no_scaling_fix_of_card_ne
    {S : Finset K} (hS : IsMinimalZeroSumSupport S)
    {x g : K} {d : ℕ}
    (hinj : Set.InjOn (fun i => x * g ^ i) (Finset.range d))
    (hpow : g ^ d = 1) (hg : g ≠ 1)
    (hsub : scalingOrbit x g d ⊆ S)
    (hne : (scalingOrbit x g d).Nonempty)
    (hcard : S.card ≠ d) : False :=
  hcard (card_eq_order_of_scaling_fixes hS hinj hpow hg hsub hne)

/-- **G167 as the `d = 2` instance.**  With `d = 2`, `g = -1` (`(-1)² = 1`, and `-1 ≠ 1` in
characteristic `≠ 2`), the orbit `{x, x·(-1)} = {x, -x}` recovers the negation pair.  We supply the
nontrivial `d = 2` root of unity and the `d`-element orbit hypothesis abstractly, so the confinement
theorem gives `S.card = 2` — exactly G167's `card_eq_two_of_neg_invariant`, now as an instance of the
general order-`d` ladder. -/
theorem card_eq_two_of_neg_scaling
    {S : Finset K} (hS : IsMinimalZeroSumSupport S)
    {x : K}
    (hg : (-1 : K) ≠ 1)
    (hinj : Set.InjOn (fun i => x * (-1 : K) ^ i) (Finset.range 2))
    (hsub : scalingOrbit x (-1) 2 ⊆ S) :
    S.card = 2 := by
  have hpow : (-1 : K) ^ 2 = 1 := by ring
  have hne : (scalingOrbit x (-1) 2).Nonempty := scalingOrbit_nonempty (by norm_num)
  exact card_eq_order_of_scaling_fixes hS hinj hpow hg hsub hne

end Confinement

/-! ## Axiom audit -/
#print axioms geom_sum_eq_zero_of_pow_eq_one
#print axioms sum_scalingOrbit_eq_zero
#print axioms card_scalingOrbit
#print axioms card_eq_order_of_scaling_fixes
#print axioms no_scaling_fix_of_card_ne
#print axioms card_eq_two_of_neg_scaling

end ArkLib.ProximityGap.Frontier.G168ScalingCosetConfinement
