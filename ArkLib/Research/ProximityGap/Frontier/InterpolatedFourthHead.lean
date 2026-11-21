/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import Mathlib.LinearAlgebra.Lagrange

/-! # A fourth head interpolating assigned sites

Outside a prescribed agreement set, a free locator coefficient makes the fourth
second row distinct from the three existing entries. The baseline first row
recovers every fresh site's evaluation point.
-/

open Finset Polynomial Code ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.InterpolatedFourthHead

variable {F I S : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]
variable [DecidableEq I] [Fintype S]

omit [Nonempty I] in
/-- Match prescribed second-row values and differ from all three old heads at every
unassigned point. One degree remains available for multiplication by `X`. -/
theorem exists_fourth (dom : I ↪ F) (V : Finset I) (prescribed : I → F) (old : Fin 3 → I → F)
    (k : ℕ) (hdegree : V.card + 2 ≤ k) (hq : 3 * Fintype.card I < Fintype.card F) :
    ∃ B : F[X], B.natDegree + 1 < k ∧ (∀ x ∈ V, B.eval (dom x) = prescribed x) ∧
      ∀ x ∉ V, ∀ j, B.eval (dom x) ≠ old j x := by
  classical
  let L := Lagrange.nodal V (fun x => dom x)
  let B₀ := Lagrange.interpolate V (fun x => dom x) prescribed
  let forbidden (z : Fin 3 × I) := (old z.1 z.2 - B₀.eval (dom z.2)) / L.eval (dom z.2)
  have hsmall : (univ.image forbidden).card < (univ : Finset F).card := by
    apply card_image_le.trans_lt
    simpa using hq
  obtain ⟨b, _, hb⟩ := exists_mem_notMem_of_card_lt_card hsmall
  refine ⟨B₀ + C b * L, ?_, ?_, ?_⟩
  · have hB : B₀.natDegree ≤ V.card := by
      by_cases hz : B₀ = 0
      · simp [hz]
      · have hle := (Lagrange.degree_interpolate_lt prescribed dom.injective.injOn
          (s := V)).le
        rw [show Lagrange.interpolate V (fun x => dom x) prescribed = B₀ by rfl,
          degree_eq_natDegree hz] at hle
        exact_mod_cast hle
    have hL : L.natDegree = V.card := Lagrange.natDegree_nodal
    have hC : (C b * L).natDegree ≤ V.card := by
      simpa [hL] using natDegree_mul_le (p := C b) (q := L)
    have hd := natDegree_add_le (p := B₀) (q := C b * L)
    omega
  · intro x hx
    have hz : L.eval (dom x) = 0 := Lagrange.eval_nodal_at_node hx
    have hval : B₀.eval (dom x) = prescribed x :=
      Lagrange.eval_interpolate_at_node prescribed dom.injective.injOn hx
    simp [hz, hval]
  · intro x hx j he
    have hn : L.eval (dom x) ≠ 0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro y hy heq
      exact hx (dom.injective heq ▸ hy)
    have hf : b = forbidden (j, x) := by
      apply (eq_div_iff hn).2
      simp only [eval_add, eval_mul, eval_C] at he
      linear_combination he
    exact hb (hf ▸ mem_image_of_mem forbidden (mem_univ (j, x)))

/-- When the baseline first row is the evaluation point times the second row, every
normalized label has first coordinate `-dom x`. Separation of the remaining scalar
is therefore required only for labels at the same site. -/
theorem mass (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (core : S → Finset I) (site : S → I)
    (r a : S → F[X]) (w b : I → F) (slope : S → F)
    (hr : ∀ i, (r i).natDegree + 1 < k) (ha : ∀ i, (a i).degree < (k : WithBot ℕ))
    (hcore : ∀ i x, x ∈ core i → (r i).eval (dom x) = w x ∧ (a i).eval (dom x) = b x)
    (hcard : ∀ i, k ≤ (core i).card)
    (hsize : ∀ i, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (((core i).card + 1 : ℕ) : ℝ≥0))
    (hmismatch : ∀ i, (r i).eval (dom (site i)) ≠ w (site i))
    (hslope : ∀ i, slope i * ((r i).eval (dom (site i)) - w (site i)) =
      b (site i) - (a i).eval (dom (site i)))
    (hlocal : ∀ i j, site i = site j → slope i = slope j → i = j)
    (hfield : (Fintype.card S).choose 2 ≤ Nat.card F) :
    (Fintype.card S : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let key (i : S) : Fin 2 → F := ![-dom (site i), slope i]
  have hdeg (i : S) : (X * r i).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have h := natDegree_mul_le (p := (X : F[X])) (q := r i)
    rw [natDegree_X] at h
    have := hr i
    exact_mod_cast (by omega : (X * r i).natDegree < k)
  exact LinearPencilFreshLabels.mass_of_distinct_fresh_labels dom k δ core site
    (fun i => X * r i) a r (fun x => dom x * w x) b w key hdeg ha
    (fun i => degree_le_natDegree.trans_lt (by exact_mod_cast (by have := hr i; omega :
      (r i).natDegree < k)))
    (by
      intro i x hx
      obtain ⟨h₁, h₂⟩ := hcore i x hx
      simp [h₁, h₂])
    hcard hsize hmismatch
    (by
      intro i
      refine ⟨?_, hslope i⟩
      simp only [key, Matrix.cons_val_zero, eval_mul, eval_X]
      ring)
    (by
      intro i j he
      exact hlocal i j (dom.injective (neg_inj.mp (congrFun he 0))) (congrFun he 1))
    hfield

end ArkLib.ProximityGap.Frontier.InterpolatedFourthHead

#print axioms ArkLib.ProximityGap.Frontier.InterpolatedFourthHead.exists_fourth
#print axioms ArkLib.ProximityGap.Frontier.InterpolatedFourthHead.mass
