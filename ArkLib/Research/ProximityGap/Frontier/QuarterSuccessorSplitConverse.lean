/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveFactorRecursion

/-! # Three saturated pair intersections force a split polynomial pencil -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitConverse

open Polynomial Finset HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterPrimitiveDirection HalfPredecessorRateQuarterPrimitiveFactorRecursion

variable {F I : Type} [Field F] [Finite F] [DecidableEq F] [Fintype I] [DecidableEq I]

omit [Finite F] [DecidableEq F] in
private theorem drop_degree {Z P V : F[X]} {d : ℕ} (hZ : Z.natDegree ≠ 0)
    (hv : V = Z * P) (hd : V.natDegree ≤ d + 1) : P.natDegree ≤ d := by
  by_cases hP : P = 0
  · simp [hP]
  have nz : Z ≠ 0 := fun hz => hZ (by simp [hz])
  rw [hv, natDegree_mul nz hP] at hd
  omega

/-- Three distinct collinear polynomial heads of degree at most `d + 1` whose
three pairwise joint cores have `d` sites and whose triple core is empty
give three disjoint, completely split fibers of degree `d`, provided their
primitive polynomial direction has a nonconstant component. -/
theorem split_of_saturated_cores (dom : I ↪ F) (u v : I → F) {d : ℕ}
    (a b c : PolynomialLine F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (det : lineDeterminant a b c = 0)
    (degree : ∀ h ∈ ({a,b,c} : Finset _), h.1.natDegree ≤ d + 1 ∧ h.2.natDegree ≤ d + 1)
    (dir : (primitiveIntercept a b).natDegree ≠ 0 ∨ (primitiveSlope a b).natDegree ≠ 0)
    (cores : let D (h : PolynomialLine F) := jointCore dom u v h.1 h.2
      (D a ∩ D b).card = d ∧ (D a ∩ D c).card = d ∧ (D b ∩ D c).card = d ∧
        (D a ∩ D b ∩ D c).card = 0) :
    ∃ P Q : F[X], P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧
      (univ.filter fun i => P.eval (dom i) = 0).card = d ∧
      (univ.filter fun i => Q.eval (dom i) = 0).card = d ∧
      (univ.filter fun i => P.eval (dom i) = Q.eval (dom i)).card = d ∧
      ∀ i, P.eval (dom i) = 0 → Q.eval (dom i) ≠ 0 := by
  classical
  let _ := Fintype.ofFinite F
  let D (h : PolynomialLine F) := jointCore dom u v h.1 h.2
  obtain ⟨hAB,hAC,hBC,empty⟩ := cores
  obtain ⟨P, p₁, p₂⟩ := exists_polynomial_factor_of_lineDeterminant_eq_zero a b b hab
    (by simp [lineDeterminant])
  obtain ⟨Q, q₁, q₂⟩ := exists_polynomial_factor_of_lineDeterminant_eq_zero a b c hab det
  have dim (h : PolynomialLine F) (mem : h ∈ ({a,b,c} : Finset _)) {f : F[X]}
      (eq₁ : h.1 - a.1 = primitiveIntercept a b * f)
      (eq₂ : h.2 - a.2 = primitiveSlope a b * f) : f.natDegree ≤ d := by
    obtain ⟨a₁,a₂⟩ := degree a (by simp)
    obtain ⟨h₁,h₂⟩ := degree h mem
    rcases dir with z | z
    · exact drop_degree z eq₁ ((natDegree_sub_le ..).trans (max_le h₁ a₁))
    · exact drop_degree z eq₂ ((natDegree_sub_le ..).trans (max_le h₂ a₂))
  have hp := dim b (by simp) p₁ p₂
  have hq := dim c (by simp) q₁ q₂
  have pp : P ≠ 0 := by
    intro eq
    exact hab.symm (Prod.ext (sub_eq_zero.mp (by simpa [eq] using p₁))
      (sub_eq_zero.mp (by simpa [eq] using p₂)))
  have qq : Q ≠ 0 := by
    intro eq
    exact hac.symm (Prod.ext (sub_eq_zero.mp (by simpa [eq] using q₁))
      (sub_eq_zero.mp (by simpa [eq] using q₂)))
  have pq : P ≠ Q := by
    rintro rfl
    exact hbc (Prod.ext (sub_left_inj.mp (p₁.trans q₁.symm)) (sub_left_inj.mp (p₂.trans q₂.symm)))
  let roots (f : F[X]) := univ.filter fun i => f.eval (dom i) = 0
  have sat {S : Finset I} {f : F[X]} (sc : S.card = d) (hf : f ≠ 0)
      (fd : f.natDegree ≤ d) (sub : S ⊆ roots f) : S = roots f :=
    eq_of_subset_of_card_le sub
      ((ArkLib.CS25.card_domain_roots_le dom f hf).trans (fd.trans_eq sc.symm))
  have ab : D a ∩ D b = roots P := by
    apply sat hAB pp hp
    simpa [D,roots,inter_comm] using
      core_intersection_subset_factor_sub_roots dom u v a b b a P 0 hab p₁ p₂ (by simp) (by simp)
  have ac : D a ∩ D c = roots Q := by
    apply sat hAC qq hq
    simpa [D,roots,inter_comm] using
      core_intersection_subset_factor_sub_roots dom u v a b c a Q 0 hab q₁ q₂ (by simp) (by simp)
  have bc : D b ∩ D c = roots (P - Q) := by
    apply sat hBC (sub_ne_zero.mpr pq) ((natDegree_sub_le ..).trans (max_le hp hq))
    exact core_intersection_subset_factor_sub_roots dom u v a b b c P Q hab p₁ p₂ q₁ q₂
  refine ⟨P,Q,hp,hq,(congrArg Finset.card ab).symm.trans hAB,
    (congrArg Finset.card ac).symm.trans hAC,?_,?_⟩
  · simpa only [roots, eval_sub, sub_eq_zero] using (bc ▸ hBC : (roots (P - Q)).card = d)
  · intro i hp₀ hq₀
    have memP : i ∈ D a ∩ D b := ab ▸ mem_filter.mpr ⟨mem_univ _,hp₀⟩
    have memQ : i ∈ D a ∩ D c := ac ▸ mem_filter.mpr ⟨mem_univ _,hq₀⟩
    have non := card_pos.mpr (show (D a ∩ D b ∩ D c).Nonempty from
      ⟨i, mem_inter.mpr ⟨memP, (mem_inter.mp memQ).2⟩⟩)
    exact (Nat.ne_of_gt non) empty

end ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitConverse
