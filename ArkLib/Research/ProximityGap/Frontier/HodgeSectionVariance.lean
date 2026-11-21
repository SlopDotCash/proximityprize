/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import Mathlib.Tactic

/-! # Agreement variance on the normalized interpolation surface

The Hodge and ramification estimates remain geometric inputs. The scalar clamp,
orthogonal section costs, comparison with cubic agreement moments and weighted
surface construction below are checked independently of those inputs.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.HodgeSectionVariance

/-- Clamped slopes have squared difference at most their mixed energy. -/
theorem clamp_energy (a b : ℝ) :
    (min 1 (max 0 a) - min 1 (max 0 b))^2 ≤
      (a-b)*(min 1 (max 0 a) - min 1 (max 0 b)) := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    nlinarith only [h]
  let g := fun x : ℝ => min 1 (max 0 x)
  have h₁ : g a ≤ g b := min_le_min_left _ (max_le_max_left _ hab)
  have h₂ : g b-g a ≤ b-a := by
    simp only [g, min_def, max_def]
    split_ifs <;> linarith
  change (g a-g b)^2 ≤ (a-b)*(g a-g b)
  nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

/-- Summing orthogonal fibre classes with their own deviations as coefficients. -/
theorem orthogonal_cost {ι : Type*} (S : Finset ι) (v a : ι → ℝ) {c K : ℝ}
    (hc : 0 ≤ c) (hK : 0 ≤ K) (ha : ∀ i ∈ S, a i ≤ K)
    (h : (∑ i ∈ S, (v i)^2)^2 ≤ c * ∑ i ∈ S, (v i)^2*a i) :
    ∑ i ∈ S, (v i)^2 ≤ K*c := by
  have hp := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (ha i hi) (sq_nonneg (v i))
  rw [← sum_mul] at hp
  have hq := h.trans (mul_le_mul_of_nonneg_left hp hc)
  have hn : 0 ≤ ∑ i ∈ S, (v i)^2 := sum_nonneg fun i _ => sq_nonneg (v i)
  by_cases hz : ∑ i ∈ S, (v i)^2 = 0
  · rw [hz]
    exact mul_nonneg hK hc
  · apply (mul_le_mul_iff_of_pos_left (lt_of_le_of_ne hn (Ne.symm hz))).mp
    nlinarith only [hq]

/-- Agreements take values zero and one, so the empirical mean minimizes the
sum of squared deviations from an arbitrary divisor degree. -/
theorem indicator_variance {ι : Type*} (S : Finset ι) (I : ι → ℝ) {θ z : ℝ}
    (hi : ∀ i ∈ S, I i ^ 2 = I i) (hθ : ∑ i ∈ S, I i = (S.card : ℝ)*θ) :
    (S.card : ℝ)*θ*(1-θ) ≤ ∑ i ∈ S, (I i-z)^2 := by
  have he : ∑ i ∈ S, (I i-z)^2 =
      (S.card : ℝ)*θ*(1-θ)+(S.card : ℝ)*(θ-z)^2 := by
    calc
      _ = ∑ i ∈ S, (I i - 2*z*I i + z^2) := by
        apply sum_congr rfl
        intro i h
        nlinarith only [hi i h]
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hθ]
        simp
        ring
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Three sections outside an affine line over the rational function field have
at most the code degree in common received-line agreements. -/
theorem triple_common {F : Type*} [Field F] (z₀ z₁ z₂ : F) (p q r : F[X])
    (u v : F → F) (S : Finset F) {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hr : r.natDegree ≤ d)
    (hn : C (z₁-z₀)*(r-p) - C (z₂-z₀)*(q-p) ≠ 0)
    (h : ∀ x ∈ S, p.eval x = u x+z₀*v x ∧ q.eval x = u x+z₁*v x ∧
      r.eval x = u x+z₂*v x) : S.card ≤ d := by
  classical
  let f := C (z₁-z₀)*(r-p) - C (z₂-z₀)*(q-p)
  have hs : S ⊆ f.roots.toFinset := by
    intro x hx
    obtain ⟨a,b,c⟩ := h x hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hn).mpr
    change f.eval x = 0
    simp only [f, eval_sub, eval_mul, eval_C, a, b, c]
    ring
  calc
    S.card ≤ f.roots.toFinset.card := card_le_card hs
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le ..).trans (max_le
      ((natDegree_C_mul_le ..).trans ((natDegree_sub_le ..).trans (max_le hr hp)))
      ((natDegree_C_mul_le ..).trans ((natDegree_sub_le ..).trans (max_le hq hp))))

/-- The lower estimate from the triple determinant and the upper Hodge estimate
give the population inequality, allowing exceptional pairs and discarded scalars. -/
theorem population {ι : Type*} (S : Finset ι) (θ : ι → ℝ) {n d t N m b X Z : ℝ}
    (hN : 0 ≤ N) (hθ : ∀ i ∈ S, 0 ≤ θ i)
    (ht : N*t ≤ N*∑ i ∈ S, θ i)
    (hdet : N*(∑ i ∈ S, (θ i)^3) ≤ N*d+(n-d)*(m+1))
    (hgeo : N*(∑ i ∈ S, θ i*(1-θ i)) ≤ 4*m*b*X*Z+m*n+X*Z) :
    N*(t-d) ≤ (8*m*b+2)*X*Z+2*m*n+(n-d)*(m+1) := by
  have hm := sum_le_sum fun i hi => show θ i-(θ i)^3 ≤ 2*(θ i*(1-θ i)) by
    nlinarith only [mul_nonneg (hθ i hi) (sq_nonneg (1-θ i))]
  rw [sum_sub_distrib, ← mul_sum] at hm
  have hq := mul_le_mul_of_nonneg_left hm hN
  nlinarith only [ht, hdet, hgeo, hq]

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- The two actual production surfaces, with the same prescribed bad sections. -/
theorem production_surfaces {F : Type} [Field F] {ι : Type*} [Fintype ι]
    (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824)
    {r a s : ℕ} (hshape : (r,a,s) = (6,8,32521) ∨ (r,a,s) = (12,17,98)) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i k, ((Q.coeff j).coeff i).coeff k ≠ 0 →
        j ≤ a ∧ i+j ≤ s ∧ k+j*536870911 < r*775491824) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ 536870911 → ∀ B : Finset ι, 775491824 ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z*v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  have hr : 0 < r := by rcases hshape with h | h <;> cases h <;> decide
  have hs : r ≤ s+1 := by rcases hshape with h | h <;> cases h <;> decide
  have hcount : Fintype.card ι * Fintype.card (JetRows s r) <
      Fintype.card (Monomials s a 536870911 (r*775491824)) := by
    rcases hshape with h | h <;> cases h <;> rw [hn] <;>
      simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] <;>
      norm_num [Fin.sum_univ_succ]
  obtain ⟨c,hc,_,hf⟩ := exists_surface dom u v hr (by decide : 0 < 775491824) hs hcount
  refine ⟨surface c,surface_ne_zero hc,fun _ _ _ h => surface_support c h,?_⟩
  intro z q hq B hB hg
  rw [surface_eval]
  exact hf z q hq B hB hg

#print axioms clamp_energy
#print axioms orthogonal_cost
#print axioms indicator_variance
#print axioms triple_common
#print axioms population
#print axioms production_surfaces

end ArkLib.ProximityGap.Frontier.HodgeSectionVariance
