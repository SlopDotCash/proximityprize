/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-! # Quadratic interpolation at two prize rates and arbitrary block lengths

At lengths divisible by 32, the two rates have the same difference between
the required agreement and the degree bound. The strict dimension inequality
supplies a polynomial vanishing on all decoding witnesses.
-/

namespace ArkLib.ProximityGap.Frontier.LinearBudgetQuadraticInterpolation

open Polynomial Finset SecondPrimeQuarticInterpolation

variable {F ι : Type*} [Field F] [Fintype ι]

/-- The numerical dimension test for total degree 32 and value degree two. -/
private theorem capacity {t d a : ℕ} (ha : 0 < a) (hd : d ≤ 8*a) (ht : t = d+11*a+1) :
    32*a*(32+1) < Fintype.card (Monomials 32 2 d t) := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

/-- Actual trivariate interpolant on any field and injective length-32a
domain. It covers quarter-rate radius 13/32 and eighth-rate radius 17/32. -/
theorem quadratic (dom : ι ↪ F) (u v : ι → F) {a d t : ℕ}
    (ha : 0 < a) (hn : Fintype.card ι = 32*a)
    (h : (d = 8*a-1 ∧ t = 19*a) ∨ (d = 4*a-1 ∧ t = 15*a)) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i l, ((Q.coeff j).coeff i).coeff l ≠ 0 →
        j ≤ 2 ∧ i+j ≤ 32 ∧ l+j*d < t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset ι, t ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + z*v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  have hcount : Fintype.card ι*(32+1) < Fintype.card (Monomials 32 2 d t) := by
    rw [hn]
    exact capacity ha (by rcases h with h | h <;> omega)
      (by rcases h with h | h <;> omega)
  obtain ⟨c, hc, _, hroot⟩ := exists_curve dom u v
    (show 0 < t by rcases h with h | h <;> omega) hcount
  refine ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h, ?_⟩
  intro z q hq S hS hx
  rw [surface_eval]
  exact hroot z q hq S hS hx

end ArkLib.ProximityGap.Frontier.LinearBudgetQuadraticInterpolation

open ArkLib.ProximityGap.Frontier.LinearBudgetQuadraticInterpolation in
#print axioms quadratic
