/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ScalarHessianLocalOrder
import ArkLib.ToMathlib.BivariateDegreeToolkit
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions

/-! # Weighted height of the actual reverse-Hessian resultant

The scalar derivative fixes the coordinate or acts on its coefficient field
without increasing coordinate degree. For a quartic of weight `W` with
coordinate weight one and value weight `d`, the Hessian has weight at most
`3*W-2*d`. The nominal degree-`(4,10)` Sylvester determinant has coordinate
degree at most `22*W-48*d`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Polynomial.Bivariate Finset ArkLib.BivariateDegreeToolkit
open scoped BigOperators Differential

namespace ArkLib.ProximityGap.Frontier.WeightedHessianResultant

open ScalarHessianLocalOrder

/-- A weighted-coordinate bound for a padded Sylvester resultant. Only actual
nonzero coefficient slots must satisfy their weighted budget. -/
theorem weighted_resultant_le {K : Type*} [CommRing K] (F G : K[X][X])
    (m n d A B : ℕ) (hF : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ A)
    (hG : ∀ j, G.coeff j ≠ 0 → (G.coeff j).natDegree+d*j ≤ B) :
    (resultant F G m n).natDegree ≤ n*A+m*B-m*n*d := by
  classical
  let M := sylvester F G m n
  let budget : Fin (m+n) → ℕ := Fin.addCases
    (fun j : Fin m => B+d*j) (fun j : Fin n => A+d*j)
  have hentry (σ : Equiv.Perm (Fin (m+n))) (i : Fin (m+n)) (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).natDegree + d*(σ i:ℕ) ≤ budget i := by
    cases i using Fin.addCases with
    | left j =>
      have hM : M (σ (.castAdd n j)) (.castAdd n j) =
          if (σ (.castAdd n j):ℕ) ∈ Set.Icc (j:ℕ) ((j:ℕ)+n) then
            G.coeff ((σ (.castAdd n j):ℕ)-j) else 0 := by simp [M,sylvester]
      rw [hM] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh := hG _ hne
        have he := Nat.sub_add_cancel h.1
        have hd := congrArg (d*·) he
        rw [Nat.mul_add] at hd
        simp only [budget,Fin.addCases_left]
        omega
      · contradiction
    | right j =>
      have hM : M (σ (.natAdd m j)) (.natAdd m j) =
          if (σ (.natAdd m j):ℕ) ∈ Set.Icc (j:ℕ) ((j:ℕ)+m) then
            F.coeff ((σ (.natAdd m j):ℕ)-j) else 0 := by simp [M,sylvester]
      rw [hM] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hh := hF _ hne
        have he := Nat.sub_add_cancel h.1
        have hd := congrArg (d*·) he
        rw [Nat.mul_add] at hd
        simp only [budget,Fin.addCases_right]
        omega
      · contradiction
  let S := (∑ j : Fin m, (j:ℕ))+∑ j : Fin n, (j:ℕ)
  have hbudget : ∑ i, budget i = m*B+n*A+d*S := by
    simp only [budget,S,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,← Finset.mul_sum]
    ring
  have hrow : ∑ i : Fin (m+n), (i:ℕ) = m*n+S := by
    simp only [S,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  change M.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  by_cases hz : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hz
    have hprod : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod, natDegree_zero]
    exact Nat.zero_le _
  · push Not at hz
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry σ i (hz i))
    have hσ := Equiv.sum_comp σ (fun i : Fin (m+n) => (i:ℕ))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hσ, hrow, Nat.mul_add, hbudget] at hs
    apply (natDegree_prod_le _ _).trans
    have hcomm : d*(m*n) = m*n*d := Nat.mul_comm _ _
    omega

variable {K : Type} [Field K] [Differential K[X]]

private theorem weight_mapCoeffs (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)
    (f : K[X][X]) (u v : ℕ) : natWeightedDegree (Differential.mapCoeffs f) u v ≤
      natWeightedDegree f u v := by
  refine Finset.sup_le fun j hj => ?_
  have hn : f.coeff j ≠ 0 := by
    rw [mem_support_iff] at hj
    intro hz
    simp [hz] at hj
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left u (hD _)) (v*j)).trans
    (weight_coeff_le_natWeightedDegree f u v (mem_support_iff.mpr hn))

omit [Differential K[X]] in
private theorem weight_derivative (f : K[X][X]) (u v W : ℕ) (hw : natWeightedDegree f u v ≤ W) :
    natWeightedDegree f.derivative u v ≤ W-v := by
  refine Finset.sup_le fun j hj => ?_
  have hnon : f.coeff (j+1) ≠ 0 := by
    rw [mem_support_iff] at hj
    intro hz
    simp [coeff_derivative, hz] at hj
  have h := (weight_coeff_le_natWeightedDegree f u v (mem_support_iff.mpr hnon)).trans hw
  have hd := Nat.mul_le_mul_left u (coeff_derivative_natDegree_le f j)
  rw [Nat.mul_succ] at h
  omega

omit [Differential K[X]] in
private theorem sub_weight (p q : K[X][X]) {u v W : ℕ} (hp : natWeightedDegree p u v ≤ W)
    (hq : natWeightedDegree q u v ≤ W) : natWeightedDegree (p-q) u v ≤ W := by
  rw [sub_eq_add_neg]
  apply (GuruswamiSudan.natWeightedDegree_add_le _ _ _ _).trans
  exact max_le hp (by simpa [natWeightedDegree] using hq)

omit [Differential K[X]] in
private theorem mul_weight (p q : K[X][X]) {u v A B : ℕ} (hp : natWeightedDegree p u v ≤ A)
    (hq : natWeightedDegree q u v ≤ B) : natWeightedDegree (p*q) u v ≤ A+B :=
  (natWeightedDegree_mul_le _ _ _ _).trans (Nat.add_le_add hp hq)

/-- Bidegree estimate for the actual three-term Hessian. The coordinate weight
`u` may be zero in order to recover the ordinary value-degree bound. -/
theorem hessian_weight (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)
    (f : K[X][X]) (u v W : ℕ) (hv : 2*v ≤ W) (hf : natWeightedDegree f u v ≤ W) :
    natWeightedDegree (hessian f) u v ≤ 3*W-2*v := by
  let D := Differential.mapCoeffs (A := K[X])
  have hDF := (weight_mapCoeffs hD f u v).trans hf
  have hDD := (weight_mapCoeffs hD (D f) u v).trans hDF
  have hY := weight_derivative f u v W hf
  have hYY := weight_derivative f.derivative u v (W-v) hY
  have hDY := weight_derivative (D f) u v W hDF
  have h1 := mul_weight _ _ hDD (mul_weight _ _ hY hY)
  have h2 := mul_weight _ _ (mul_weight _ _ hDY hY) hDF
  have h3 := mul_weight _ _ hYY (mul_weight _ _ hDF hDF)
  rw [hessian, pow_two, pow_two, show 2*(D f).derivative*f.derivative*D f =
    (D f).derivative*f.derivative*D f+(D f).derivative*f.derivative*D f by ring]
  apply (GuruswamiSudan.natWeightedDegree_add_le _ _ _ _).trans
  apply max_le
  · apply sub_weight
    · exact h1.trans (by omega)
    · exact (GuruswamiSudan.natWeightedDegree_add_le _ _ _ _).trans
        (max_le (h2.trans (by omega)) (h2.trans (by omega)))
  · exact h3.trans (by omega)

/-- A quartic with coordinate weight one and value weight `d` has a Hessian of
value degree at most ten, and the actual padded Hessian determinant has the
stated weighted coordinate budget. -/
theorem quartic_resultant_bound (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)
    (f : K[X][X]) (d W : ℕ) (hf : f.natDegree ≤ 4) (hW : 4*d ≤ W)
    (hw : natWeightedDegree f 1 d ≤ W) :
    (hessian f).natDegree ≤ 10 ∧ (resultant f (hessian f) 4 10).natDegree ≤ 22*W-48*d := by
  have hH := hessian_weight hD f 1 d W (by omega) hw
  constructor
  · change natDegreeY (hessian f) ≤ 10
    rw [degreeY_as_weighted_deg]
    change natDegreeY f ≤ 4 at hf
    rw [degreeY_as_weighted_deg] at hf
    exact hessian_weight hD f 0 1 4 (by decide) hf
  · have hcoeff (g : K[X][X]) (b : ℕ) (hg : natWeightedDegree g 1 d ≤ b)
        (j : ℕ) (hj : g.coeff j ≠ 0) : (g.coeff j).natDegree+d*j ≤ b := by
      simpa using (weight_coeff_le_natWeightedDegree g 1 d (mem_support_iff.mpr hj)).trans hg
    apply (weighted_resultant_le f (hessian f) 4 10 d W (3*W-2*d)
      (hcoeff f W hw) (hcoeff _ _ hH)).trans
    omega

/-- With the first degree exact, padding the second value degree preserves
nonvanishing of the resultant for an irreducible equation and a nonmultiple. -/
theorem padded_ne_zero {R E : Type*} [CommRing R] [Field E] (φ : R →+* E)
    (hi : Function.Injective φ) (F G : R[X]) (n : ℕ) (hn : G.natDegree ≤ n)
    (hir : Irreducible (F.map φ)) (hnd : ¬F.map φ ∣ G.map φ) :
    resultant F G F.natDegree n ≠ 0 := by
  intro hz
  have hh := congrArg φ hz
  rw [← resultant_map_map, map_zero, ← natDegree_map_eq_of_injective hi (p := F)] at hh
  have hg : (G.map φ).natDegree ≤ n := natDegree_map_le.trans hn
  rw [← Nat.add_sub_of_le hg, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree] at hh
  have hm := (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hir.ne_zero))
  exact (resultant_eq_zero_iff.mp hm).2 (hir.coprime_iff_not_dvd.mpr hnd)

/-- Production quartic multiplicity budget, including the exact padded degree,
nonvanishing from the field divisibility alternative, and every translated site.
The scalar parameter lies in `K`; the coefficient indeterminate is the coordinate. -/
theorem secondPrime_quartic_site_budget {E : Type*} [Field E] (φ : K[X] →+* E)
    (hinj : Function.Injective φ) (F : K[X][X]) (hf : F.natDegree = 4)
    (hir : Irreducible (F.map φ)) (hnd : ¬F.map φ ∣ (hessian F).map φ)
    (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)
    (hwF : natWeightedDegree F 1 67108863 ≤ 302954072)
    (S : Finset K) (w : K → K[X]) (r : K → ℕ) (hS : S.card = 1073741824)
    (hr : ∀ a ∈ S, r a ≤ 4) (hπ : ∀ a ∈ S, (Polynomial.X-C a : K[X])′ = 0)
    (hl : ∀ a ∈ S, ((w a)′)′ = 0)
    (hlocal : ∀ a ∈ S, HasOrder (Polynomial.X-C a) (r a) (F.taylor (w a))) :
    ∑ a ∈ S, r a ≤ 1412316443 := by
  obtain ⟨hH,hdeg⟩ := quartic_resultant_bound hD F _ _ hf.le (by decide) hwF
  have hres := padded_ne_zero φ hinj F (hessian F) 10 hH hir hnd
  rw [hf] at hres
  have hsum := quartic_hessian_site_sum F S w r hf hH hres hr hπ hl hlocal
  omega

end ArkLib.ProximityGap.Frontier.WeightedHessianResultant

open ArkLib.ProximityGap.Frontier.WeightedHessianResultant in
#print axioms secondPrime_quartic_site_budget
