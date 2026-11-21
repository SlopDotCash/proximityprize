/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.HasseMonomial

/-! # Interpolation of received lines at arbitrary multiplicity -/

set_option autoImplicit false
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorJetInterpolation
open SecondPrimeQuarticInterpolation

variable {F : Type} {ι : Type*} [Field F] [Fintype ι] {s v d t : ℕ}

/-- Select a scalar fiber of a supported three-variable polynomial. -/
noncomputable def fiber (c : Monomials s v d t → F) (g : F) : F[X][X] :=
  ∑ m, monomial m.1.val (monomial m.2.2.val (c m * g^m.2.1.val))

private theorem fiber_eval (c : Monomials s v d t → F) (g : F) (q : F[X]) :
    (fiber c g).eval q = specialize c g q := by
  simp only [fiber,specialize,eval_finsetSum,eval_monomial]

/-- A mixed Hasse coefficient, polynomial in the label along a received line. -/
noncomputable def jetTerm (m : Monomials s v d t) (i j : ℕ) (x a b : F) : F[X] :=
  monomial m.2.1.val ((m.2.2.val.choose i : F)*(m.1.val.choose j : F)*x^(m.2.2.val-i)) *
    (C a + X*C b)^(m.1.val-j)

private theorem jetTerm_degree (m : Monomials s v d t) (i j : ℕ) (x a b : F) (hj : j ≤ s) :
    (jetTerm m i j x a b).natDegree < s+1-j := by
  by_cases h : m.1.val < j
  · simp only [jetTerm,Nat.choose_eq_zero_of_lt h,Nat.cast_zero,mul_zero,zero_mul,
      map_zero,natDegree_zero]
    omega
  have hl : (C a + X*C b).natDegree ≤ 1 :=
    (natDegree_add_le ..).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
  have hp := (natDegree_pow_le (p := C a+X*C b) (n := m.1.val-j)).trans
    (Nat.mul_le_mul_left _ hl)
  have hm := m.2.1.isLt
  have hm' : m.1.val ≤ s := by omega
  have hh := (natDegree_mul_le (p := monomial m.2.1.val
    ((m.2.2.val.choose i : F)*(m.1.val.choose j : F)*x^(m.2.2.val-i)))
    (q := (C a+X*C b)^(m.1.val-j))).trans (Nat.add_le_add (natDegree_monomial_le _) hp)
  unfold jetTerm
  omega

private theorem fiber_jet (c : Monomials s v d t → F) (g x a b : F) (i j : ℕ) :
    GS.hasseCoeff i j (fiber c g) x (a+g*b) =
      (∑ m, C (c m)*jetTerm m i j x a b).eval g := by
  change GS.hasseCoeffLinearMap i j x (a+g*b) (fiber c g) = _
  simp only [fiber, map_sum, GS.hasseCoeffLinearMap_apply,jetTerm,
    eval_finsetSum,eval_mul,eval_monomial,eval_pow,eval_add,eval_X,eval_C]
  apply sum_congr rfl
  intro m _
  rw [GS.hasseCoeff_monomial]
  ring

/-- Each value-derivative row loses that many parameter coefficients. -/
abbrev JetRows (s r : ℕ) := (j : Fin r) × (Fin (r-j.val) × Fin (s+1-j.val))

/-- The full set of scalar-coefficient equations for all jets at all sites. -/
noncomputable def jetMatrix (dom : ι ↪ F) (u v₁ : ι → F) (s v d t r : ℕ) :
    Matrix (ι × JetRows s r) (Monomials s v d (r*t)) F := fun z m =>
  (jetTerm m z.2.2.1.val z.2.1.val (dom z.1) (u z.1) (v₁ z.1)).coeff z.2.2.2.val

/-- Rank lower bound for the full interpolation space over the base field. -/
theorem interpolation_dim (dom : ι ↪ F) (u v₁ : ι → F) (s v d t r : ℕ) :
    Fintype.card (Monomials s v d (r*t)) - Fintype.card ι * Fintype.card (JetRows s r) ≤
      Module.finrank F (LinearMap.ker (jetMatrix dom u v₁ s v d t r).mulVecLin) := by
  let M := jetMatrix dom u v₁ s v d t r
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h' := Submodule.finrank_le (LinearMap.range M.mulVecLin)
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_prod] at h h'
  change _ ≤ Module.finrank F (LinearMap.ker M.mulVecLin)
  omega

/-- A nonzero polynomial with every mixed jet vanishing identically along all the received
lines. Every sufficiently rich polynomial section is a root on its scalar fiber. -/
theorem exists_surface (dom : ι ↪ F) (u v₁ : ι → F) {r : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hs : r ≤ s+1)
    (hcount : Fintype.card ι * Fintype.card (JetRows s r) < Fintype.card (Monomials s v d (r*t))) :
    ∃ c : Monomials s v d (r*t) → F, c ≠ 0 ∧
      (∀ x i j, i+j<r → ∑ m, C (c m)*jetTerm m i j (dom x) (u x) (v₁ x) = 0) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset ι, t ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + g * v₁ x) → specialize c g q = 0 := by
  classical
  let M := jetMatrix dom u v₁ s v d t r
  have hfr : Module.finrank F ((ι × JetRows s r) → F) <
      Module.finrank F (Monomials s v d (r*t) → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_prod] using hcount
  obtain ⟨c,hc,hker⟩ := GSMultInterp.exists_ne_zero_map_eq_zero M.mulVecLin hfr
  change M.mulVec c = 0 at hker
  have hjets (x i j) (h : i+j<r) : ∑ m, C (c m)*jetTerm m i j (dom x) (u x) (v₁ x) = 0 := by
    ext k
    rw [finsetSum_coeff,coeff_zero]
    by_cases hk : k < s+1-j
    · have he := congrFun hker (x,⟨⟨j,by omega⟩,⟨i,by change i < r-j; omega⟩,⟨k,hk⟩⟩)
      simpa only [M,jetMatrix,Matrix.mulVec,dotProduct,Pi.zero_apply,coeff_C_mul,mul_comm] using he
    · apply sum_eq_zero
      intro m _
      rw [coeff_C_mul,coeff_eq_zero_of_natDegree_lt ((jetTerm_degree m i j _ _ _ (by omega)).trans_le
        (by omega : s+1-j ≤ k)),mul_zero]
  refine ⟨c,hc,hjets,fun g q hq S hS hag => ?_⟩
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn dom S r t dom.injective.injOn hS
  · intro x hx
    have hv : GS.vanishesToOrder r (fiber c g) (dom x) (u x+g*v₁ x) := by
      apply (GS.vanishesToOrder_iff_hasseCoeff ..).mpr
      intro i j h
      rw [fiber_jet,hjets x i j h,eval_zero]
    simpa only [fiber_eval] using hv.dvd_eval q (hag x hx)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast specialize_degree c g q hq (Nat.mul_pos hr ht))

/-- At the last production agreement count covered by the residual-module argument, a
quartic of total scalar/value degree fourteen has all the required site jets and sections. -/
theorem production (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824) :
    ∃ c : Monomials 14 4 536870911 (3*803929776) → F, c ≠ 0 ∧
      (∀ x i j, i+j<3 → ∑ m, C (c m)*jetTerm m i j (dom x) (u x) (v x) = 0) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 536870911 → ∀ S : Finset ι, 803929776 ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + g*v x) → specialize c g q = 0 := by
  apply exists_surface dom u v (by decide) (by decide) (by decide)
  rw [hn]
  simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- The production containment as a genuine weighted trivariate surface. -/
theorem production_surface (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i+j ≤ 14 ∧ a+j*536870911 < 3*803929776) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 536870911 → ∀ S : Finset ι, 803929776 ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + g*v x) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  obtain ⟨c,hc,_,hall⟩ := production dom u v hn
  refine ⟨surface c,surface_ne_zero hc,fun _ _ _ hh => surface_support c hh,?_⟩
  intro g q hq S hS ha
  rw [surface_eval]
  exact hall g q hq S hS ha

/-- Certified interpolation dimension at the million-degree cutoff, before extension
of the scalar label to a rational function field. -/
theorem production_dim (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824) :
    247782756 * 1000001 ≤ Module.finrank F
      (LinearMap.ker (jetMatrix dom u v 1000000 4 536870911 803929776 3).mulVecLin) := by
  refine le_trans ?_ (interpolation_dim dom u v 1000000 4 536870911 803929776 3)
  rw [hn]
  simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

#print axioms interpolation_dim
#print axioms production_dim
#print axioms exists_surface
#print axioms production
#print axioms production_surface
end ArkLib.ProximityGap.Frontier.HalfSuccessorJetInterpolation
