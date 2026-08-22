/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AllWitnessFloorGeneric

/-!
# A field-sized locator list below the Johnson radius

The shared-base analysis reduces the two-rider layer to Reed--Solomon codewords agreeing with a
received direction on only `111848108 < k` carrier coordinates.  At any agreement size below
`k`, a direction-only list cap is impossible: scalar multiples of the locator polynomial of the
agreement set are distinct codewords and all agree with zero on that set.

This is a no-go theorem, not a prize closure.  Any successful treatment of the two-rider layer
must retain extra rider/vote coupling that the punctured direction list forgets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open _root_.ProximityGap.SpikeFloor

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterBelowJohnsonLocatorListRefuted

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} [NeZero n]

/-- The literal P1 two-rider agreement floor is strictly below the code dimension. -/
theorem twoRiderAlignment_lt_k : 111848108 < 268435456 := by norm_num

/-- Locator polynomial of a coordinate set. -/
noncomputable def locator (dom : Fin n ↪ F) (A : Finset (Fin n)) : F[X] :=
  ∏ x ∈ A, (X - C (dom x))

/-- The scalar-multiple evaluation word belonging to a locator. -/
noncomputable def locatorWord (dom : Fin n ↪ F) (A : Finset (Fin n)) (c : F) : Fin n → F :=
  fun x => (c • locator dom A).eval (dom x)

theorem locator_monic (dom : Fin n ↪ F) (A : Finset (Fin n)) :
    (locator dom A).Monic := by
  rw [locator]
  exact monic_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)

theorem locator_natDegree (dom : Fin n ↪ F) (A : Finset (Fin n)) :
    (locator dom A).natDegree = A.card := by
  rw [locator, natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)]
  simp

theorem locator_eval_eq_zero_of_mem (dom : Fin n ↪ F) (A : Finset (Fin n))
    {x : Fin n} (hx : x ∈ A) :
    (locator dom A).eval (dom x) = 0 := by
  rw [locator, eval_prod]
  apply Finset.prod_eq_zero hx
  simp

theorem locator_eval_ne_zero_of_not_mem (dom : Fin n ↪ F) (A : Finset (Fin n))
    {x : Fin n} (hx : x ∉ A) :
    (locator dom A).eval (dom x) ≠ 0 := by
  rw [locator, eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro y hy
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr fun h => hx (dom.injective h.symm ▸ hy)

/-- Every locator multiple agrees with the zero received word throughout `A`. -/
theorem locatorWord_eq_zero_of_mem (dom : Fin n ↪ F) (A : Finset (Fin n)) (c : F)
    {x : Fin n} (hx : x ∈ A) :
    locatorWord dom A c x = 0 := by
  simp [locatorWord, locator_eval_eq_zero_of_mem dom A hx]

/-- If `|A| < k`, every locator multiple is a dimension-`k` RS codeword. -/
theorem locatorWord_mem_rsCode (dom : Fin n ↪ F) (A : Finset (Fin n)) (c : F)
    (hAk : A.card < k) :
    locatorWord dom A c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  by_cases hc : c = 0
  · subst c
    have hz : locatorWord dom A 0 = (0 : Fin n → F) := by
      funext x
      simp [locatorWord]
    rw [hz]
    exact (rsCode dom k).zero_mem
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply ProximityGap.Ownership.polyEval_mem_rsCode
  rw [natDegree_smul _ hc, locator_natDegree]
  omega

/-- Outside `A`, evaluation at one coordinate recovers the scalar, so the list is injective. -/
theorem locatorWord_injective (dom : Fin n ↪ F) (A : Finset (Fin n))
    (hA : A ≠ Finset.univ) : Function.Injective (locatorWord dom A) := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ A := by
    by_contra h
    push_neg at h
    exact hA (Finset.eq_univ_of_forall h)
  intro c d hcd
  have heval := congrFun hcd x
  have hn := locator_eval_ne_zero_of_not_mem dom A hx
  simp only [locatorWord, eval_smul, smul_eq_mul] at heval
  exact (mul_right_cancel₀ hn heval)

/-- **Field-sized below-`k` list.**  The image of all scalar locator multiples has exactly
`|F|` distinct RS codewords, and every member agrees with zero on every coordinate of `A`. -/
theorem fieldSized_locatorList (dom : Fin n ↪ F) (A : Finset (Fin n))
    (hAk : A.card < k) (hA : A ≠ Finset.univ) :
    ∃ L : Finset (Fin n → F),
      L.card = Fintype.card F ∧
      (∀ w ∈ L, w ∈ (rsCode dom k : Submodule F (Fin n → F))) ∧
      ∀ w ∈ L, ∀ x ∈ A, w x = 0 := by
  classical
  refine ⟨Finset.univ.image (locatorWord dom A), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (locatorWord_injective dom A hA),
      Finset.card_univ]
  · intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨c, -, rfl⟩ := hw
    exact locatorWord_mem_rsCode dom A c hAk
  · intro w hw x hx
    rw [Finset.mem_image] at hw
    obtain ⟨c, -, rfl⟩ := hw
    exact locatorWord_eq_zero_of_mem dom A c hx

end ArkLib.ProximityGap.Frontier.P1RateQuarterBelowJohnsonLocatorListRefuted

open ArkLib.ProximityGap.Frontier.P1RateQuarterBelowJohnsonLocatorListRefuted

#print axioms fieldSized_locatorList
