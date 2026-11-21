/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CubicSheetExcess
import ArkLib.Research.ProximityGap.Frontier.GenericProjectivePolarGcd

/-! # The global cubic received-site bound from two ordinary polar resultants -/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.CubicPolarSiteBudget

open GenericProjectivePolarGcd PolynomialLocalOrder
open ReceivedPolarContacts (dx)
open ScalarHessianLocalOrder (hessian)

variable {K : Type} [Field K] [Differential K]
local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩

private theorem root_sum_le (f : K[X]) (hf : f ≠ 0) (S : Finset K) :
    ∑ α ∈ S, f.rootMultiplicity α ≤ f.natDegree := by
  simpa only [local_order _ f hf, ENat.toNat_natCast] using sum_local_orders_le f hf S

private theorem lin_square (n : ℕ) : 3*n ≤ n^2+2 := by
  rcases n with _|_|n
  · decide
  · decide
  · nlinarith

/-- From a primitive cubic and actual received-site interpolation leaders,
a generic second polar gives the global budget on their total multiplicity.
The slope lies in a prescribed infinite subfield, outside any finite exception set. -/
theorem cubic_site_budget [IsSepClosed K] [Infinite K] [DecidableEq K]
    {k : Type} [Field k] [Infinite k] (φ : k →+* K) (p : ℕ) [CharP K p]
    (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (F : K[X][X]) (hf : F.natDegree = 3) (hprim : F.IsPrimitive)
    (hV : F.resultant F.derivative 3 3 ≠ 0) (hH : F.resultant (hessian F) 3 7 ≠ 0)
    (A : K[X]) (hA : A ≠ 0) (hAp : A.natDegree < p) (except : Finset k)
    (D : Finset K) (l : K → K) (r : K → ℕ)
    (hsite : ∀ α ∈ D, α′=0 ∧ (l α)′′=0 ∧ ∃ i, TruncatedJetMultipliers.Leader
        (ReceivedJetContact.shifted F α (l α)) (r α) i) :
    ∃ c ∉ except, let B := F.resultant (polar (dx F) F.derivative (φ c)) 3 3
      B ≠ 0 ∧ 3*(∑ α ∈ D, r α)+2*(GCDMonoid.gcd A B).natDegree ≤
        2*D.card+4*F.leadingCoeff.natDegree+(F.resultant (hessian F) 3 7).natDegree := by
  classical
  let H := F.resultant (hessian F) 3 7
  have hfn : F ≠ 0 := by rintro rfl; simp at hf
  have hL := leadingCoeff_ne_zero.mpr hfn
  have hY : F.derivative.natDegree ≤ 3 := (natDegree_derivative_le F).trans (by omega)
  obtain ⟨c₀,u,y,hcharts,hfactor⟩ := primitive_norm_charts F hf hprim h₂ h₃
  let a α i := -y α i
  let b α i := -(1+PowerSeries.C (c₀ α)*y α i)
  have hc : NormCharts F a b := hcharts
  obtain ⟨c,hexc,hB,hg⟩ := generic_gcd_charge p φ A hA hAp F (dx F) F.derivative 3
    ((CubicSheetExcess.dx_degree F).trans hf.le) hY hV a b hc except
  refine ⟨c,hexc,hB,?_⟩
  let B := F.resultant (polar (dx F) F.derivative (φ c)) 3 3
  let g := (GCDMonoid.gcd A B).natDegree
  let R α := if α ∈ D then r α else 0
  let S := D ∪ A.roots.toFinset
  let μ α i := min (sheetValue α (dx F) 3 (b α i) (a α i)).order
    (sheetValue α F.derivative 3 (b α i) (a α i)).order
  let j α i := (μ α i).toNat
  have hj (α i) : ((j α i : ℕ) : ℕ∞) = μ α i := by
    apply ENat.natCast_toNat_eq_self.mpr
    apply ne_top_of_le_ne_top _ (min_le_right ..)
    exact PowerSeries.order_eq_top.not.mpr (sheet_nonzero _ hV α _ (hc α _ 3 hY) i)
  have hg' : 6*g ≤ ∑ α ∈ A.roots.toFinset, ∑ i, j α i := by
    change 6 • (g : ℕ∞) ≤ ∑ α ∈ A.roots.toFinset, ∑ i, μ α i at hg
    simp only [← hj, ← Nat.cast_sum, nsmul_eq_mul] at hg
    exact_mod_cast hg
  have place (α : K) :
      2*(∑ i, j α i)+6*(R α)^2 ≤ 24*F.leadingCoeff.rootMultiplicity α+6*H.rootMultiplicity α := by
    obtain ⟨hu,hy,hab,hfactors⟩ := hfactor α
    have ha (i) : a α i ≠ 0 := neg_ne_zero.mpr (hy i)
    have hnorm (G : K[X][X]) (h : ℕ) (hG : G.natDegree ≤ h) (hne : F.resultant G 3 h ≠ 0) :
        6 • ((F.resultant G 3 h).rootMultiplicity α : ℕ∞) =
          ∑ i, (sheetValue α G h (b α i) (a α i)).order := by
      simpa only [local_order α _ hne] using hc α G h hG
    have hP := ProjectiveCubicLocalOrder.pole_order_of_tests F hf α (c₀ α) (y α) hnorm
    apply CubicSheetExcess.place F hf.le α (l α) (R α) _ (a α) (b α) ha hab (u α) hu hfactors
    · intro i
      exact BinaryBranchResultant.product_sheet_zero _ 3
        (natDegree_map_le.trans (natDegree_map_le.trans hf.le)) (a α) (b α) ha (u α) hfactors i
    · exact fun i => (hj α i).trans_le (min_le_left ..)
    · exact fun i => (hj α i).trans_le (min_le_right ..)
    · simpa only [a, PowerSeries.order_neg, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hP
    · simpa only [H, CubicSheetExcess.sheet, sheetValue, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using
        (hnorm (hessian F) 7 (CubicSheetExcess.hessian_degree F hf.le) hH).symm
    · by_cases h : α ∈ D
      · exact Or.inr (by simpa [R,h] using hsite α h)
      · exact Or.inl (by simp [R,h])
  have sumPlace := sum_le_sum (s := S) (fun α _ => place α)
  simp only [sum_add_distrib, ← mul_sum] at sumPlace
  have hgS : (∑ α ∈ A.roots.toFinset, ∑ i, j α i) ≤ ∑ α ∈ S, ∑ i, j α i :=
    sum_le_sum_of_subset_of_nonneg subset_union_right (by intros; exact Nat.zero_le _)
  have hD : (∑ α ∈ S, R α^2) = ∑ α ∈ D, (r α)^2 := by
    calc
      _ = ∑ α ∈ D, R α^2 := (sum_subset subset_union_left
        (fun α _ hn => by simp [R,hn])).symm
      _ = _ := sum_congr rfl fun α h => by simp [R,h]
  have hlin := sum_le_sum (s := D) (fun α _ => lin_square (r α))
  simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul] at hlin
  have hlc := root_sum_le _ hL S
  have hhr := root_sum_le H (show H ≠ 0 from hH) S
  have lin : 3*(∑ α ∈ D, r α) ≤ (∑ α ∈ D, (r α)^2)+2*D.card := by
    simpa only [Nat.cast_id, Nat.mul_comm D.card 2] using hlin
  rw [hD] at sumPlace
  change 3*(∑ α ∈ D, r α)+2*g ≤ 2*D.card+4*F.leadingCoeff.natDegree+H.natDegree
  have budget : ∀ (rSum sqSum jT jA gd len m n lc hd : ℕ),
      6*gd ≤ jA → jA ≤ jT → 2*jT+6*sqSum ≤ 24*m+6*n → m ≤ lc → n ≤ hd →
      3*rSum ≤ sqSum+2*len → 3*rSum+2*gd ≤ 2*len+4*lc+hd := by intros; omega
  exact budget _ _ _ _ _ _ _ _ _ _ hg' hgS sumPlace hlc hhr lin


open Polynomial.Bivariate ArkLib.BivariateDegreeToolkit in
/-- Weighted degree accounts for the Hessian determinant and the poles of
a cubic, using the unreduced Sylvester resultant and its leading coefficient. -/
theorem weighted_degree_budget (F : K[X][X]) (hf : F.natDegree=3) (d W : ℕ)
    (hd : 3*d ≤ W) (hw : natWeightedDegree F 1 d ≤ W) :
    4*F.leadingCoeff.natDegree+(F.resultant (hessian F) 3 7).natDegree+39*d ≤ 20*W := by
  have hD (q : K[X]) : q′.natDegree ≤ q.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (Differential.mapCoeffs q).coeff j = 0
    simp [coeff_eq_zero_of_natDegree_lt hj]
  have hgap := WeightedHessianResultant.hessian_weight hD F 1 d W (by omega) hw
  have coeffBound (G : K[X][X]) (m : ℕ) (h : natWeightedDegree G 1 d ≤ m)
      (i : ℕ) (hn : G.coeff i ≠ 0) : (G.coeff i).natDegree+d*i ≤ m := by
    simpa using (weight_coeff_le_natWeightedDegree G 1 d (mem_support_iff.mpr hn)).trans h
  have hne : F ≠ 0 := by rintro rfl; simp at hf
  have lc := coeffBound F W hw F.natDegree (leadingCoeff_ne_zero.mpr hne)
  change F.leadingCoeff.natDegree+d*F.natDegree ≤ W at lc
  rw [hf] at lc
  have hres := WeightedHessianResultant.weighted_resultant_le F (hessian F) 3 7 d W (3*W-2*d)
    (coeffBound F W hw) (coeffBound _ _ hgap)
  omega

/-- The production defect 201 pays 402 orders in the received-site count. -/
theorem production_received_bound {n W R g pole hdeg : ℕ} (hw : 3*67108863 ≤ W)
    (hbudget : 3*R+2*g ≤ 2*n+4*pole+hdeg)
    (hweight : 4*pole+hdeg+39*67108863 ≤ 20*W)
    (hpolar : 2*(W-67108863) ≤ g+201) :
    3*R+35*67108863 ≤ 2*n+16*W+402 := by omega

#print axioms weighted_degree_budget
#print axioms production_received_bound

#print axioms cubic_site_budget
end ArkLib.ProximityGap.Frontier.CubicPolarSiteBudget
