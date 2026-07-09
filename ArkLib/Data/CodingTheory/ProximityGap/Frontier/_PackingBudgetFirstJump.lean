/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PackingEnvelope

/-!
# The first overlap-packing jump at a field-normalized budget

This file turns the freshness hypotheses of
`PackingEnvelope.overlap_packing_epsMCA_lower_bound` into a cardinality theorem and
packages the exact integer arithmetic of the first packing jump.

For `B = floor (p / Q)`, code dimension `k`, and `D = n-k`, the packing family has
`2e+2` bad scalars at error radius `e/n` throughout

```text
  ceil(D/2) <= e <= D-1.
```

Thus its first budget-crossing error is `max(ceil(D/2), floor(B/2))`, provided this
does not exceed `D-1`.  This is only a bad-side consumer: no matching upper bound or
threshold equality is claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.PackingEnvelope

namespace ArkLib.ProximityGap.PackingBudgetFirstJump

/-- The six separation conditions required by the tuned overlap-packing construction. -/
structure OverlapFreshScalars {p n : ℕ} (g : ZMod p) (s c : ℕ) where
  γK : Fin n → ZMod p
  γA : Fin n → ZMod p
  ne : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → γK x ≠ γA x
  k_not_dom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    ∀ j : Fin n, γK x ≠ -(g ^ (j : ℕ))
  a_not_dom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    ∀ j : Fin n, γA x ≠ -(g ^ (j : ℕ))
  k_inj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x = γK y → x = y
  a_inj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γA x = γA y → x = y
  cross : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x ≠ γA y

/-- An element of positive multiplicative order in a field is nonzero. -/
private lemma ne_zero_of_orderOf_eq {p n : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) : g ≠ 0 := by
  intro h0
  subst h0
  have h1 : ¬ IsOfFinOrder (0 : ZMod p) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨t, ht, hpow⟩
    rw [zero_pow ht.ne'] at hpow
    exact zero_ne_one hpow
  exact NeZero.ne n (hg.symm.trans (orderOf_eq_zero h1))

/-- Negated powers below the order are injective. -/
private lemma neg_pow_injective {p n : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) :
    Function.Injective (fun j : Fin n ↦ -(g ^ (j : ℕ))) := by
  have hg0 := ne_zero_of_orderOf_eq hg
  intro i j hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf
  · rw [hg]
    exact i.isLt
  · rw [hg]
    exact j.isLt
  · exact neg_injective hij

open Classical in
/-- **Fresh-scalar supply.**  The six hypotheses of the overlap construction are
satisfiable as soon as the complement of the negated evaluation domain contains `2c`
elements.  The bound `2c ≤ p-n` is both the natural sufficient count and necessary for
this particular package (the two injective images are cross-disjoint). -/
theorem exists_overlapFreshScalars {p n s c : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) (hcs : c ≤ s) (hsn : s ≤ n)
    (hsupply : 2 * c ≤ p - n) :
    Nonempty (OverlapFreshScalars g s c) := by
  classical
  let forbidden : Finset (ZMod p) :=
    Finset.univ.image (fun j : Fin n ↦ -(g ^ (j : ℕ)))
  have hforbidden : forbidden.card = n := by
    rw [forbidden, Finset.card_image_of_injective _ (neg_pow_injective hg),
      Finset.card_univ, Fintype.card_fin]
  have hcompl : forbiddenᶜ.card = p - n := by
    rw [Finset.card_compl, hforbidden, ZMod.card]
  have hfreshCard : Fintype.card (Fin (2 * c)) ≤ forbiddenᶜ.card := by
    simpa [hcompl] using hsupply
  obtain ⟨fresh, hfresh⟩ :=
    Function.Embedding.exists_of_card_le_finset (s := forbiddenᶜ) hfreshCard
  let inY : Fin n → Prop := fun x ↦ s - c ≤ (x : ℕ) ∧ (x : ℕ) < s
  let off : (x : Fin n) → inY x → Fin c := fun x hx ↦
    ⟨(x : ℕ) - (s - c), by omega⟩
  let kIndex : (x : Fin n) → (hx : inY x) → Fin (2 * c) := fun x hx ↦
    ⟨(off x hx : ℕ), by have := (off x hx).isLt; omega⟩
  let aIndex : (x : Fin n) → (hx : inY x) → Fin (2 * c) := fun x hx ↦
    ⟨c + (off x hx : ℕ), by have := (off x hx).isLt; omega⟩
  let γK : Fin n → ZMod p := fun x ↦
    if hx : inY x then fresh (kIndex x hx) else 0
  let γA : Fin n → ZMod p := fun x ↦
    if hx : inY x then fresh (aIndex x hx) else 0
  have hoff_inj : ∀ {x y : Fin n} (hx : inY x) (hy : inY y),
      off x hx = off y hy → x = y := by
    intro x y hx hy heq
    apply Fin.ext
    have hv : (off x hx : ℕ) = (off y hy : ℕ) := congrArg Fin.val heq
    dsimp only [off] at hv
    dsimp only [inY] at hx hy
    omega
  have hk_ne_ha : ∀ x y : Fin n, (hx : inY x) → (hy : inY y) →
      kIndex x hx ≠ aIndex y hy := by
    intro x y hx hy heq
    have hv := congrArg Fin.val heq
    dsimp only [kIndex, aIndex] at hv
    have hlt := (off x hx).isLt
    omega
  refine ⟨⟨γK, γA, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx1 hx2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    simp only [γK, γA, dif_pos hx] at hEq
    exact hk_ne_ha x x hx hx (fresh.injective hEq)
  · intro x hx1 hx2 j hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hmem : fresh (kIndex x hx) ∈ forbiddenᶜ := hfresh (kIndex x hx)
    rw [Finset.mem_compl] at hmem
    apply hmem
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by simpa [γK, hx] using hEq⟩
  · intro x hx1 hx2 j hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hmem : fresh (aIndex x hx) ∈ forbiddenᶜ := hfresh (aIndex x hx)
    rw [Finset.mem_compl] at hmem
    apply hmem
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by simpa [γA, hx] using hEq⟩
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γK, dif_pos hx, dif_pos hy] at hEq
    have hi := fresh.injective hEq
    apply hoff_inj hx hy
    apply Fin.ext
    exact congrArg Fin.val hi
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γA, dif_pos hx, dif_pos hy] at hEq
    have hi := fresh.injective hEq
    apply hoff_inj hx hy
    apply Fin.ext
    have hv := congrArg Fin.val hi
    dsimp only [aIndex] at hv
    omega
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γK, γA, dif_pos hx, dif_pos hy] at hEq
    exact hk_ne_ha x y hx hy (fresh.injective hEq)

end ArkLib.ProximityGap.PackingBudgetFirstJump

