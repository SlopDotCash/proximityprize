/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset

/-!
# The involution-closed subset count: `#{ι-closed 2i-subsets} = C(|T|, i)` (#407)

The exact combinatorial engine behind the all-antipodal `e₂=0` diagonal of the K(n) census. For a
fixed-point-free involution `ι` on a finite type with transversal `T` (one representative per orbit:
`Disjoint T (ι T)`, `T ∪ ι T = univ`), the subsets stable under `ι` of cardinality `2i` are in
bijection with the `i`-subsets of `T` (via `U ↦ U ∪ ι U`, inverse `S ↦ S ∩ T`), so there are exactly
`C(|T|, i)` of them.

Application (#407): with `ι = negation` on dyadic `μ_{2^k}`, the negation-closed subsets are exactly the
zero-sum subsets (Lam–Leung, `LamLeungTwoPow.vanishing_sum_antipodal`), so the dyadic zero-sum `2i`-subset
count is `C(2^{k-1}, i)`; via the squaring map this gives the all-antipodal `e₂=0` count
`#{S = ∪ j antipodal pairs : e₂(S)=0} = C(n/4, j/2)` (verified probe across n=8..64). An exact closed
form for the entire all-antipodal diagonal — char-0, no character sums, no √ wall.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
open Finset

namespace ArkLib.ProximityGap.InvolutionClosedCount
variable {α : Type*} [Fintype α] [DecidableEq α]

def IsClosed (ι : α → α) (S : Finset α) : Prop := ∀ x ∈ S, ι x ∈ S

instance (ι : α → α) (S : Finset α) : Decidable (IsClosed ι S) := by
  unfold IsClosed; infer_instance

theorem isClosed_union_image {ι : α → α} (hinv : Function.Involutive ι) (U : Finset α) :
    IsClosed ι (U ∪ U.image ι) := by
  intro x hx
  rw [Finset.mem_union] at hx ⊢
  rcases hx with h | h
  · right; exact Finset.mem_image_of_mem ι h
  · left; rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h; rwa [hinv y]

/-- **The exact count of `ι`-closed `2i`-subsets = `C(|T|, i)`.** `ι` a fixed-point-free involution,
`T` a transversal of the `ι`-orbits (`Disjoint T (ι T)` and `T ∪ ι T = univ`). The bijection is
`U ↦ U ∪ ι U` (an `i`-subset of `T` ↦ an `ι`-closed `2i`-set), inverse `S ↦ S ∩ T`. -/
theorem isClosed_card_eq_choose
    {ι : α → α} (hinv : Function.Involutive ι) (hfpf : ∀ x, ι x ≠ x)
    (T : Finset α) (hdisj : Disjoint T (T.image ι)) (hcov : T ∪ T.image ι = Finset.univ)
    (i : ℕ) :
    (Finset.univ.powerset.filter (fun S => IsClosed ι S ∧ S.card = 2 * i)).card
      = Nat.choose T.card i := by
  classical
  rw [← Finset.card_powersetCard i T]
  refine Finset.card_nbij' (fun S => S ∩ T) (fun U => U ∪ U.image ι) ?_ ?_ ?_ ?_
  · -- S ↦ S ∩ T lands in powersetCard i T
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨_, hClosed, hcard⟩ := hS
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.inter_subset_right, ?_⟩
    show (S ∩ T).card = i
    -- |S ∩ T| = i because S = (S∩T) ⊔ ι(S∩T), card 2i
    have hsplit : S = (S ∩ T) ∪ (S ∩ T).image ι := by
      apply Finset.Subset.antisymm
      · intro x hx
        have : x ∈ T ∪ T.image ι := hcov ▸ Finset.mem_univ x
        rw [Finset.mem_union] at this
        rcases this with hT | hiT
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
        · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
          exact Finset.mem_inter.mpr ⟨by have := hClosed (ι y) hx; rwa [hinv] at this, hy⟩
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with h | h
        · exact (Finset.mem_inter.mp h).1
        · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
          exact hClosed y (Finset.mem_inter.mp hy).1
    have hdisj' : Disjoint (S ∩ T) ((S ∩ T).image ι) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right (Finset.image_subset_image Finset.inter_subset_right) hdisj)
    have hc : S.card = 2 * (S ∩ T).card := by
      conv_lhs => rw [hsplit]
      rw [Finset.card_union_of_disjoint hdisj',
        Finset.card_image_of_injective _ hinv.injective]; ring
    omega
  · -- U ↦ U ∪ ι U lands in the filter
    intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, hUcard⟩ := hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, isClosed_union_image hinv U, ?_⟩
    have hd : Disjoint U (U.image ι) :=
      Finset.disjoint_of_subset_left hUT
        (Finset.disjoint_of_subset_right (Finset.image_subset_image hUT) hdisj)
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinv.injective, hUcard]; ring
  · -- left inverse: (S ∩ T) ↦ recovers S
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨_, hClosed, _⟩ := hS
    show (S ∩ T) ∪ (S ∩ T).image ι = S
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact (Finset.mem_inter.mp h).1
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hClosed y (Finset.mem_inter.mp hy).1
    · intro x hx
      have : x ∈ T ∪ T.image ι := hcov ▸ Finset.mem_univ x
      rw [Finset.mem_union] at this
      rcases this with hT | hiT
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
      · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
        exact Finset.mem_inter.mpr ⟨by have := hClosed (ι y) hx; rwa [hinv] at this, hy⟩
  · -- right inverse: (U ∪ ι U) ∩ T = U
    intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, _⟩ := hU
    show (U ∪ U.image ι) ∩ T = U
    rw [Finset.union_inter_distrib_right]
    have h1 : U ∩ T = U := Finset.inter_eq_left.mpr hUT
    have h2 : U.image ι ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hUT) hdisj.symm
    rw [h1, h2, Finset.union_empty]

end ArkLib.ProximityGap.InvolutionClosedCount
#print axioms ArkLib.ProximityGap.InvolutionClosedCount.isClosed_card_eq_choose
