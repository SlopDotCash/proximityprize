/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Power-map fiber card identities

Issue #464 frontier brick.  The bounded-complexity critique of the Deligne/complete-sum route
uses the elementary fact that a power map with constant fibers turns a sum over the source into
the common fiber size times the image sum.  For multiplicative subgroups this is the mechanism
behind the lift

```text
sum_{t in F*} psi (b * t^m) = m * sum_{x in (F*)^m} psi (b * x),
```

but the theorem below is deliberately stated as a finite-set lemma.  It records the exact
combinatorial obstruction: after the lift, the resulting complete sum has the complexity of the
power map, so any square-root estimate must pay for that high-degree map rather than for the small
subgroup alone.
-/

open Finset

namespace ProximityGap.Frontier.PowMapFiberCard

variable {α β R : Type*} [DecidableEq β] [AddCommMonoid R]

/--
Constant-fiber regrouping over finite sets.

If `f` maps `s` into `t`, every fiber over `t` has cardinality `m`, and `g` is a weight on `t`,
then summing `g ∘ f` over the source is exactly `m` copies of the sum of `g` over the target.
This is the finite-set core of the complete power-map lift used in the Gauss-period no-go route.
-/
theorem sum_comp_eq_nsmul_sum_of_fiber_card_eq
    (s : Finset α) (t : Finset β) (f : α → β) (g : β → R) (m : ℕ)
    (hmaps : (s : Set α).MapsTo f t)
    (hfiber : ∀ y ∈ t, (s.filter fun x => f x = y).card = m) :
    ∑ x ∈ s, g (f x) = m • ∑ y ∈ t, g y := by
  calc
    ∑ x ∈ s, g (f x)
        = ∑ y ∈ t, ∑ x ∈ s.filter (fun x => f x = y), g (f x) := by
          exact (Finset.sum_fiberwise_of_maps_to hmaps (fun x => g (f x))).symm
    _ = ∑ y ∈ t, ∑ x ∈ s.filter (fun x => f x = y), g y := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ y ∈ t, (s.filter fun x => f x = y).card • g y := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.sum_const]
    _ = ∑ y ∈ t, m • g y := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [hfiber y hy]
    _ = m • ∑ y ∈ t, g y := by
          rw [Finset.sum_nsmul]

variable {G R' : Type*} [Group G] [Fintype G] [DecidableEq G] [AddCommMonoid R']

/--
Power-map lift with an explicitly supplied image and constant fiber size.

For a finite group `G`, a chosen image set `image`, and a proof that every point of `image` has
exactly `m` preimages under `x ↦ x ^ e`, the complete source sum of `g (x^e)` is `m` times the
sum over the image.  The later analytic obstruction is that, in the multiplicative-field case,
this complete source sum is a high-degree power sum.
-/
theorem sum_pow_eq_nsmul_sum_image_of_fiber_card_eq
    (e m : ℕ) (image : Finset G) (g : G → R')
    (hmaps : ((Finset.univ : Finset G) : Set G).MapsTo (fun x : G => x ^ e) image)
    (hfiber : ∀ y ∈ image, ((univ : Finset G).filter fun x => x ^ e = y).card = m) :
    ∑ x : G, g (x ^ e) = m • ∑ y ∈ image, g y := by
  simpa using
    sum_comp_eq_nsmul_sum_of_fiber_card_eq
      (s := (univ : Finset G)) (t := image) (f := fun x : G => x ^ e) (g := g) (m := m)
      hmaps hfiber

variable {H S : Type*} [CommGroup H] [Fintype H] [DecidableEq H] [AddCommMonoid S]

/--
Every nonempty fiber of the finite-group power map has the same cardinality as the kernel fiber.
This is the group-theoretic reason a complete power-map lift counts each image point with a
uniform multiplicity.
-/
theorem pow_fiber_card_eq_kernel_card (e : ℕ) {y : H}
    (hy : y ∈ Set.range (powMonoidHom e : H →* H)) :
    ((univ : Finset H).filter fun x => x ^ e = y).card =
      ((univ : Finset H).filter fun x => x ^ e = 1).card := by
  have h1 : (1 : H) ∈ Set.range (powMonoidHom e : H →* H) := ⟨1, by simp⟩
  simpa [powMonoidHom_apply] using
    MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom e : H →* H) hy h1

/--
Complete power-map lift over a finite commutative group, with no supplied fiber hypothesis.

The source sum over `x ↦ x^e` is exactly the kernel-fiber cardinality times the sum over the
range of the power map.  In `F_p^*`, this is the formal finite-group core behind
`Σ_t ψ(b t^m) = #ker(·^m) · Σ_{x in (F_p^*)^m} ψ(bx)`.
-/
theorem sum_pow_eq_kernelCard_nsmul_sum_range
    (e : ℕ) (g : H → S) :
    ∑ x : H, g (x ^ e) =
      ((univ : Finset H).filter fun x => x ^ e = 1).card •
        ∑ y ∈ (univ.filter fun y : H => y ∈ Set.range (powMonoidHom e : H →* H)), g y := by
  refine
    sum_pow_eq_nsmul_sum_image_of_fiber_card_eq
      (G := H) (R' := S) e ((univ : Finset H).filter fun x => x ^ e = 1).card
      ((univ : Finset H).filter fun y : H => y ∈ Set.range (powMonoidHom e : H →* H))
      g ?_ ?_
  · intro x _hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, by simp [powMonoidHom_apply]⟩⟩
  · intro y hy
    exact pow_fiber_card_eq_kernel_card (H := H) e (Finset.mem_filter.mp hy).2

/-- In a finite cyclic commutative group, the kernel fiber of `x ↦ x^e` has size `gcd(#H,e)`. -/
theorem pow_kernel_fiber_card_eq_gcd [IsCyclic H] (e : ℕ) :
    ((univ : Finset H).filter fun x => x ^ e = 1).card = (Nat.card H).gcd e := by
  rw [← Fintype.card_subtype (fun x : H => x ^ e = 1)]
  rw [← IsCyclic.card_powMonoidHom_ker (G := H) e, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight (fun x => ?_)
  rw [MonoidHom.mem_ker, powMonoidHom_apply]

/--
Cyclic specialization of the complete power-map lift.

For a finite cyclic commutative group, `Σ_x g(x^e)` is `gcd(#H,e)` copies of the sum over the
range of `x ↦ x^e`.  When `e ∣ #H`, the multiplicity is `e`, matching the prize case
`e = (p-1)/n` on `F_p^*`.
-/
theorem sum_pow_eq_gcd_nsmul_sum_range_of_isCyclic [IsCyclic H]
    (e : ℕ) (g : H → S) :
    ∑ x : H, g (x ^ e) =
      (Nat.card H).gcd e •
        ∑ y ∈ (univ.filter fun y : H => y ∈ Set.range (powMonoidHom e : H →* H)), g y := by
  rw [sum_pow_eq_kernelCard_nsmul_sum_range (H := H) (S := S) e g,
    pow_kernel_fiber_card_eq_gcd (H := H) e]

section SourceAudit

#print axioms sum_comp_eq_nsmul_sum_of_fiber_card_eq
#print axioms sum_pow_eq_nsmul_sum_image_of_fiber_card_eq
#print axioms pow_fiber_card_eq_kernel_card
#print axioms sum_pow_eq_kernelCard_nsmul_sum_range
#print axioms pow_kernel_fiber_card_eq_gcd
#print axioms sum_pow_eq_gcd_nsmul_sum_range_of_isCyclic

end SourceAudit

end ProximityGap.Frontier.PowMapFiberCard
