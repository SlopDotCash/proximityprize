/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.TruncatedJetMultipliers
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! # Intrinsic interpolation with scalar-polynomial multipliers

A forbidden subspace can account for all multiples of the original component.
The remaining solution has actual polynomial jet identities simultaneously at
each site, so they specialize at every scalar label.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Module
open scoped BigOperators Matrix

namespace ArkLib.ProximityGap.Frontier.PolynomialJetConstraintSpace

open TruncatedJetMultipliers

variable {K : Type} [Field K]
variable {I : Type} [Fintype I]
variable {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- There is a solution outside the forbidden subspace if the number of
parameters left after imposing equality in the target exceeds its dimension. -/
theorem exists_match_outside {A W : Type} [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (L : E →ₗ[K] W) (M : A →ₗ[K] W) (hi : Function.Injective M)
    (U : Submodule K E) (hb : finrank K W + finrank K U < finrank K E + finrank K A) :
    ∃ e ∉ U, ∃ q : A, L e = M q := by
  let G : E × A →ₗ[K] W := L.comp (LinearMap.fst K E A) - M.comp (LinearMap.snd K E A)
  by_contra! hn
  have hk (v : LinearMap.ker G) : L v.val.1 = M v.val.2 := by
    apply sub_eq_zero.mp
    exact v.property
  let proj : LinearMap.ker G →ₗ[K] E := (LinearMap.fst K E A).comp (LinearMap.ker G).subtype
  have hu (v : LinearMap.ker G) : proj v ∈ U := by
    by_contra h
    exact hn v.val.1 h v.val.2 (hk v)
  let J := proj.codRestrict U hu
  have hj : Function.Injective J := by
    intro x y hxy
    have hp : x.val.1 = y.val.1 := congrArg Subtype.val hxy
    apply Subtype.ext
    exact Prod.ext hp (hi ((hk x).symm.trans ((congrArg L hp).trans (hk y))))
  have hs := LinearMap.finrank_le_finrank_of_injective hj
  have hg := G.finrank_range_add_finrank_ker
  rw [Module.finrank_prod] at hg
  have hy := Submodule.finrank_le (LinearMap.range G)
  change finrank K (LinearMap.ker G) ≤ finrank K U at hs
  omega

/-- Scalar-coefficient length of a polynomial window. -/
theorem window_finrank (K : Type) [Field K] (s : ℕ) : finrank K (degreeLT K s) = s := by
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K s), Fintype.card_fin]

/-- Product of a column entry of degree at most m and a multiplier of length s-m. -/
private theorem product_mem {s m : ℕ} (a : K[X]) (ha : a.natDegree ≤ m)
    (hm : m ≤ s) (q : degreeLT K (s-m)) : a*q.val ∈ degreeLT K s := by
  by_cases hq : q.val = 0
  · simp [hq]
  have h := (natDegree_lt_iff_degree_lt hq).mpr (mem_degreeLT.mp q.property)
  have he : (a*q.val).natDegree < s := natDegree_mul_le.trans_lt (by omega)
  exact mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast he))

/-- Simultaneous polynomial multiplier map across all sites. Its columns are
the genuine jet coefficients of monomial multiples of each translated equation. -/
def multiplierMap {μ s m : ℕ} (r : I → ℕ) (G : I → K[X][X][X])
    (hm : m ≤ s) (hdeg : ∀ x i c, (columns μ (μ-r x) (G x) i c).natDegree ≤ m) :
    ((x : I) → JetIdx (μ-r x) → degreeLT K (s-m)) →ₗ[K]
      (I → JetIdx μ → degreeLT K s) where
  toFun q x i := ⟨∑ c, columns μ (μ-r x) (G x) i c * (q x c).val,
    (degreeLT K s).sum_mem (fun c _ => product_mem _ (hdeg x i c) hm _)⟩
  map_add' q u := by
    funext x i
    apply Subtype.ext
    change (∑ c, _ * ((q x c).val+(u x c).val)) = _
    simp only [mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' z q := by
    funext x i
    apply Subtype.ext
    change (∑ c, columns μ (μ-r x) (G x) i c * (z • (q x c).val)) =
      z • (∑ c, columns μ (μ-r x) (G x) i c * (q x c).val)
    simp only [mul_smul_comm, Finset.smul_sum]

omit [Fintype I] in
private theorem multiplier_injective {μ s m : ℕ} (r j : I → ℕ) (G : I → K[X][X][X])
    (hr : ∀ x, r x ≤ μ) (hlead : ∀ x, Leader (G x) (r x) (j x))
    (hm : m ≤ s) (hdeg : ∀ x i c, (columns μ (μ-r x) (G x) i c).natDegree ≤ m) :
    Function.Injective (multiplierMap r G hm hdeg) := by
  intro q u h
  funext x c
  apply Subtype.ext
  have hx : (fun h1 => (q x h1).val) = (fun h1 => (u x h1).val) := by
    apply columns_injective (G x) (hlead x) (hr x)
    funext i
    exact congrArg Subtype.val (congrFun (congrFun h x) i)
  exact congrFun hx c

/-- A genuine simultaneous solution in any finite-dimensional space of sections.
The integer s is the number of allowed scalar coefficients; m is the maximum
scalar degree of a multiplier column. All equations are polynomial identities. -/
theorem exists_polynomial_multipliers {μ s m : ℕ} (r j : I → ℕ) (G : I → K[X][X][X])
    (hr : ∀ x, r x ≤ μ) (hlead : ∀ x, Leader (G x) (r x) (j x))
    (hm : m ≤ s) (hdeg : ∀ x i c, (columns μ (μ-r x) (G x) i c).natDegree ≤ m)
    (L : E →ₗ[K] (I → JetIdx μ → degreeLT K s)) (U : Submodule K E)
    (hb : Fintype.card I * ((μ*(μ+1)/2)*s) + finrank K U <
      finrank K E + ∑ x, (((μ-r x)*(μ-r x+1)/2)*(s-m))) :
    ∃ e ∉ U, ∃ q : (x : I) → JetIdx (μ-r x) → degreeLT K (s-m),
      ∀ x, (fun i => (L e x i).val) =
        (columns μ (μ-r x) (G x)).mulVec (fun c => (q x c).val) := by
  have hk := exists_match_outside L (multiplierMap r G hm hdeg)
    (multiplier_injective r j G hr hlead hm hdeg) U
  have hdim {ν : ℕ} (k : ℕ) : finrank K (JetIdx ν → degreeLT K k) =
      (ν*(ν+1)/2)*k := by
    rw [Module.finrank_pi_fintype]
    simp only [window_finrank, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_jetIdx]
  have hleft : finrank K (I → JetIdx μ → degreeLT K s) =
      Fintype.card I*((μ*(μ+1)/2)*s) := by
    rw [Module.finrank_pi_fintype]
    simp only [hdim, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hright : finrank K ((x : I) → JetIdx (μ-r x) → degreeLT K (s-m)) =
      ∑ x, (((μ-r x)*(μ-r x+1)/2)*(s-m)) := by
    rw [Module.finrank_pi_fintype]
    simp only [hdim]
  have H := hk (by rwa [hleft, hright])
  obtain ⟨e,he,q,hq⟩ := H
  refine ⟨e,he,q,fun x => ?_⟩
  funext i
  exact congrArg Subtype.val (congrFun (congrFun hq x) i)

end ArkLib.ProximityGap.Frontier.PolynomialJetConstraintSpace

open ArkLib.ProximityGap.Frontier.PolynomialJetConstraintSpace in
#print axioms exists_polynomial_multipliers
