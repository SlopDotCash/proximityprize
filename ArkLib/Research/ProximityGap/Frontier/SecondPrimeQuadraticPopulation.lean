/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticScalarClass
import ArkLib.Research.ProximityGap.Frontier.DiscriminantSquareClass
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSylvesterFiberMass

/-! # Exclusion of the second-prime quadratic population alternative -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeQuadraticPopulation

open Finset Polynomial SecondPrimeActualPopulations SecondPrimeQuadraticScalarClass
open scoped NNReal

variable {K : Type} [Field K]

private theorem degree_discriminant (a b c : Polynomial K[X]) {D : ℕ}
    (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D) (hc : c.natDegree ≤ D) :
    (b ^ 2 - 4 * a * c).natDegree ≤ 2 * D := by
  have h4 : (4 : Polynomial K[X]).natDegree = 0 := natDegree_ofNat 4
  have h4a : (4 * a).natDegree ≤ D := natDegree_mul_le.trans (by omega)
  apply (natDegree_sub_le ..).trans
  apply max_le
  · exact natDegree_pow_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)

private theorem disc_degrees (f Q : K[X][X][X]) (hf : f ≠ 0) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (shape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) :
    (disc f).natDegree ≤ 68 ∧ (Bivariate.swap (disc f)).natDegree ≤ 715827884 := by
  have tri := SecondPrimeSectionResultant.factor_triangle hQ hdiv
    (fun j i a h => (shape j i a h).2.1)
  have hs (j) : (f.coeff j).natDegree ≤ 34 := by
    by_cases hz : f.coeff j = 0
    · simp [hz]
    · have := tri j hz
      omega
  refine ⟨degree_discriminant _ _ _ (hs 2) (hs 1) (hs 0), ?_⟩
  obtain ⟨g, hfg⟩ := hdiv
  have hg : g ≠ 0 := fun hg => hQ (by simp [hfg, hg])
  have hweight := SecondPrimeCoordinateWeight.weight_le_of_coeff 67108863 Q (W := 357913942)
    (fun j i a h => Nat.le_of_lt_succ (shape j i a h).2.2)
  rw [hfg, SecondPrimeCoordinateWeight.weight_mul _ _ _ hf hg] at hweight
  have hc (j) : (Bivariate.swap (f.coeff j)).natDegree ≤ 357913942 := by
    change Bivariate.natDegreeY (Bivariate.swap (f.coeff j)) ≤ _
    rw [Bivariate.natDegreeY_swap]
    apply Finset.sup_le
    intro i hi
    have hn := SecondPrimeCoordinateWeight.coeff_weight_le 67108863 f
      (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
    omega
  simp only [disc, map_sub, map_pow, map_mul, map_ofNat]
  exact degree_discriminant _ _ _ (hc 2) (hc 1) (hc 0)

private theorem section_square (f : K[X][X][X]) (hd : f.natDegree = 2)
    (z : K) (w : K[X]) (h : f.eval₂ (evalRingHom (C z)) w = 0) :
    IsSquare ((disc f).eval (C z)) := by
  let a := (f.coeff 2).eval (C z)
  let b := (f.coeff 1).eval (C z)
  let c := (f.coeff 0).eval (C z)
  have hex : f = C (f.coeff 0) + C (f.coeff 1) * X + C (f.coeff 2) * X ^ 2 := by
    simpa [sum_range_succ] using (f.as_sum_range_C_mul_X_pow' (n := 3) (by omega))
  have hr : c + b * w + a * w ^ 2 = 0 := by
    conv at h => lhs; arg 3; rw [hex]
    simpa only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_evalRingHom] using h
  refine (isSquare_iff_exists_sq _).mpr ⟨2 * a * w + b, ?_⟩
  simp only [disc, eval_sub, eval_pow, eval_mul, eval_ofNat]
  change b ^ 2 - 4 * a * c = (2 * a * w + b) ^ 2
  linear_combination -4 * a * hr

variable {I F : Type} [Field F] [DecidableEq F] [Fintype I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- Every actual value-degree-two factor over the algebraic closure has at most 2047
selected labels. The characteristic bound is on the genuine coordinate degree of its
discriminant. In particular the 4129-label alternative is impossible. -/
theorem population_le [Finite F] [IsAlgClosed K]
    (fam : Family dom δ u) (σ : F →+* K) (f Q : K[X][X][X])
    (hi : Irreducible f) (hd : f.natDegree = 2) (hQ : Q ≠ 0) (hf : f ∣ Q)
    (shape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (h2 : (2 : K) ≠ 0) (hp : 715827884 < ringChar K ∨ ringChar K = 0) :
    (population fam σ f).card ≤ 2047 := by
  classical
  by_cases h0 : disc f = 0
  · exact SecondPrimeQuadraticScalarClass.population_le fam σ f Q hi hd hQ hf shape hn ht h2
      0 0 (by simp [h0])
  obtain ⟨hZ, hX⟩ := disc_degrees f Q hi.ne_zero hQ hf shape
  obtain ⟨s, V, H, hs, hv, _, he, hsz, hvz, hhz, _, hS | ⟨hr, hsep⟩⟩ :=
    _root_.ProximityGap.DiscriminantSquareClass.normalize (disc f) h0
      (hp.imp (hX.trans_lt ·) id)
  · exact SecondPrimeQuadraticScalarClass.population_le fam σ f Q hi hd hQ hf shape hn ht h2
      s V (by simpa [hS] using he)
  let M := (population fam σ f).map ⟨σ, σ.injective⟩
  have hb := SecondPrimeSylvesterFiberMass.exceptional_square_fiber_count s V H M hs hv hr hsep
    (fun z hz hsz hvz => by
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hz
      apply _root_.ProximityGap.DiscriminantSquareClass.square_fiber (σ x) he hsz hvz
      exact section_square f hd (σ x) ((fam.q x).map σ) (mem_filter.mp hx).2)
  have hcard : M.card = (population fam σ f).card := card_map _
  omega

end ArkLib.ProximityGap.Frontier.SecondPrimeQuadraticPopulation
