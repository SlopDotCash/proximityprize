/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedHessianResultant
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Data.Polynomial.ResultantSpecialization
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.OfFn

/-! # The top coefficient of a weighted Sylvester determinant

The sum of the column weights minus the sum of the row weights is the
same in every permutation term. At that degree the determinant is exactly
the determinant of the top coefficients of its entries. -/

open Polynomial Finset Matrix

namespace ProximityGap.WeightedResultantInitial

variable {K I : Type*} [Field K]

private theorem coeff_product {ι : Type*} (s : Finset ι) (P : ι → K[X]) (w : ι → ℕ)
    (hw : ∀ i ∈ s, (P i).natDegree ≤ w i) :
    (∏ i ∈ s, P i).coeff (∑ i ∈ s, w i) = ∏ i ∈ s, (P i).coeff (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, (P i).natDegree ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, prod_insert ha, coeff_mul_add_eq_of_natDegree_le
      (hw _ (mem_insert_self ..)) ((natDegree_prod_le _ _).trans (Finset.sum_le_sum hs)), ih hs]

/-- The leading coefficient can be computed on the initial matrix. A cell
whose row cost exceeds its column budget must vanish in both matrices. -/
theorem determinant_coeff [Fintype I] [DecidableEq I] (M : Matrix I I K[X]) (T : Matrix I I K)
    (row col : I → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → (M i j).natDegree + row i ≤ col j)
    (hT : ∀ i j, T i j = if row i ≤ col j then (M i j).coeff (col j - row i) else 0) :
    M.det.coeff ((∑ j, col j) - ∑ i, row i) = T.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_smul]
  congr 1
  by_cases hz : ∃ j, M (σ j) j = 0
  · obtain ⟨j, hj⟩ := hz
    have ht : T (σ j) j = 0 := by simp [hT, hj]
    have h₁ : (∏ i, M (σ i) i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
    have h₂ : (∏ i, T (σ i) i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) ht
    rw [h₁, h₂, coeff_zero]
  · push Not at hz
    have h := fun j => hM (σ j) j (hz j)
    have hs (j) : row (σ j) ≤ col j := by have := h j; omega
    have hsum : (∑ j, (col j - row (σ j))) + ∑ j, row j = ∑ j, col j := by
      rw [← Equiv.sum_comp σ row, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hs j)
    rw [show (∑ j, col j) - ∑ i, row i = ∑ j, (col j - row (σ j)) by omega]
    rw [coeff_product _ _ _ (fun j _ => by have := h j; omega)]
    exact Finset.prod_congr rfl fun j _ => by simp [hT, hs j]

private theorem cell_degree (p : K[X][X]) (A d i j n : ℕ)
    (hp : ∀ a, p.coeff a ≠ 0 → (p.coeff a).natDegree+d*a ≤ A)
    (hz : (if i ∈ Set.Icc j (j+n) then p.coeff (i-j) else 0) ≠ 0) :
    (if i ∈ Set.Icc j (j+n) then p.coeff (i-j) else 0).natDegree + d*i ≤ A+d*j := by
  split_ifs at hz ⊢ with h
  · have hs := hp _ hz
    have he := congrArg (d*·) (Nat.sub_add_cancel h.1)
    rw [Nat.mul_add] at he
    omega
  · contradiction

private theorem cell_top (p : K[X][X]) (f : K[X]) (A d i j n : ℕ)
    (hf : ∀ a ≤ n, f.coeff a = if d*a ≤ A then (p.coeff a).coeff (A-d*a) else 0) :
    (if i ∈ Set.Icc j (j+n) then f.coeff (i-j) else 0) =
    if d*i ≤ A+d*j then
      (if i ∈ Set.Icc j (j+n) then p.coeff (i-j) else 0).coeff (A+d*j-d*i) else 0 := by
  by_cases h : i ∈ Set.Icc j (j+n)
  · simp only [h, ite_true]
    have hij := h.1
    have hin := h.2
    have he := congrArg (d*·) (Nat.sub_add_cancel hij)
    rw [Nat.mul_add] at he
    rw [hf _ (by omega)]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · simp [h]

/-- For padded value degrees `m,n`, the coefficient at the full weighted
resultant degree is the scalar resultant of the two weighted initial forms.
Zero coefficients and gaps in the value degree are allowed. -/
theorem resultant_coeff (P Q : K[X][X]) (f g : K[X]) (m n d A B : ℕ)
    (hP : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree+d*j ≤ A)
    (hQ : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree+d*j ≤ B)
    (hf : ∀ j ≤ m, f.coeff j = if d*j ≤ A then (P.coeff j).coeff (A-d*j) else 0)
    (hg : ∀ j ≤ n, g.coeff j = if d*j ≤ B then (Q.coeff j).coeff (B-d*j) else 0) :
    (resultant P Q m n).coeff (n*A+m*B-m*n*d) = resultant f g m n := by
  classical
  let col : Fin (m+n) → ℕ := Fin.addCases (fun j : Fin m => B+d*j) (fun j : Fin n => A+d*j)
  let row (i : Fin (m+n)) := d*(i:ℕ)
  have h := determinant_coeff (sylvester P Q m n) (sylvester f g m n) row col (by
    intro i j
    cases j using Fin.addCases with
    | left j => simpa [sylvester, row, col] using cell_degree Q B d i j n hQ
    | right j => simpa [sylvester, row, col] using cell_degree P A d i j m hP) (by
    intro i j
    cases j using Fin.addCases with
    | left j => simpa [sylvester, row, col] using cell_top Q g B d i j n hg
    | right j => simpa [sylvester, row, col] using cell_top P f A d i j m hf)
  let S := (∑ j : Fin m, (j:ℕ)) + ∑ j : Fin n, (j:ℕ)
  have hcols : ∑ j, col j = m*B+n*A+d*S := by
    simp only [col, S, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  have hrows : ∑ i : Fin (m+n), (i:ℕ) = m*n+S := by
    simp only [S, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  simp only [row, ← Finset.mul_sum, hrows, hcols, Nat.mul_add] at h
  rw [Nat.mul_comm d (m*n)] at h
  simpa only [resultant, Nat.add_sub_add_right, Nat.add_comm (m*B) (n*A)] using h

/-- A nonzero initial resultant certifies the exact coordinate degree of the
full resultant. -/
theorem resultant_degree (P Q : K[X][X]) (f g : K[X]) (m n d A B : ℕ)
    (hP : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree+d*j ≤ A)
    (hQ : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree+d*j ≤ B)
    (hf : ∀ j ≤ m, f.coeff j = if d*j ≤ A then (P.coeff j).coeff (A-d*j) else 0)
    (hg : ∀ j ≤ n, g.coeff j = if d*j ≤ B then (Q.coeff j).coeff (B-d*j) else 0)
    (hne : resultant f g m n ≠ 0) :
    (resultant P Q m n).natDegree = n*A+m*B-m*n*d := by
  refine le_antisymm (ArkLib.ProximityGap.Frontier.WeightedHessianResultant.weighted_resultant_le
    _ _ _ _ _ _ _ hP hQ) (le_natDegree_of_ne_zero ?_)
  rwa [resultant_coeff P Q f g m n d A B hP hQ hf hg]

/-- Initial form of the coordinate derivative of a polynomial of weighted
degree `W`, after substituting the ordinate with weight `d`. -/
noncomputable def initialPolar (f : K[X]) (W d : ℕ) : K[X] :=
  C (W:K)*f - C (d:K)*((Polynomial.X : K[X])*f.derivative)

private theorem initial_coeff (f : K[X]) (W d j : ℕ) :
    (initialPolar f W d).coeff j = (W-(d:K)*j)*f.coeff j := by
  cases j with
  | zero => simp [initialPolar]
  | succ j =>
    simp [initialPolar, coeff_X_mul, coeff_derivative, Nat.cast_succ]
    ring

/-- The initial polar has no common root with the initial curve when its roots
are simple and nonzero and the ordinate weight survives in the field. -/
theorem initial_coprime (f : K[X]) (W d : ℕ) (hf : f.Separable)
    (h0 : f.coeff 0 ≠ 0) (hd : (d:K) ≠ 0) : IsCoprime f (initialPolar f W d) := by
  have hX : IsCoprime f (Polynomial.X : K[X]) := ((irreducible_X.isCoprime_or_dvd f).resolve_right
    (fun h => h0 (X_dvd_iff.mp h))).symm
  obtain ⟨a,b,h⟩ := hX.mul_right (show IsCoprime f f.derivative from hf)
  have hdi : (C (d:K)⁻¹:K[X])*C (d:K) = 1 := by rw [← C_mul, inv_mul_cancel₀ hd, C_1]
  refine ⟨a + b * C (d:K)⁻¹ * C (W:K), -(b * C (d:K)⁻¹), ?_⟩
  calc
    _ = a*f + b*(C (d:K)⁻¹*C (d:K))*((Polynomial.X : K[X])*f.derivative) := by unfold initialPolar; ring
    _ = 1 := by rw [hdi, mul_one]; exact h

private theorem initial_polar_le (f : K[X]) (W d : ℕ) :
    (initialPolar f W d).natDegree ≤ f.natDegree := by
  unfold initialPolar
  refine (natDegree_sub_le ..).trans (max_le (natDegree_C_mul_le ..) ((natDegree_C_mul_le ..).trans ?_))
  by_cases h : f.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h, derivative_C, mul_zero, natDegree_zero]
    exact Nat.zero_le _
  · have hx := natDegree_mul_le (p := (Polynomial.X : K[X])) (q := f.derivative)
    have hf := natDegree_derivative_le f
    rw [natDegree_X] at hx
    omega

theorem initial_resultant_ne_zero (f : K[X]) (W d : ℕ) (hf : f.Separable)
    (h0 : f.coeff 0 ≠ 0) (hd : (d:K) ≠ 0) :
    resultant f (initialPolar f W d) f.natDegree f.natDegree ≠ 0 := by
  let g := initialPolar f W d
  have hg : g.natDegree ≤ f.natDegree := initial_polar_le f W d
  have hr := resultant_ne_zero f g (initial_coprime f W d hf h0 hd)
  have hn : f ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have hpad := resultant_add_right_deg f g f.natDegree g.natDegree (f.natDegree-g.natDegree) le_rfl
  simpa [Nat.add_sub_of_le hg, Nat.sub_add_cancel hg, coeff_natDegree, hn, hr, g] using
    (show resultant f g f.natDegree (g.natDegree+(f.natDegree-g.natDegree)) ≠ 0 by
      rw [hpad]
      exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hn)) hr)

/-- The prescribed coefficients of an ordinary first polar at ordinate index
`j`. The parameter is constant in the coordinate. -/
private theorem polar_coeff_top (a b : K[X]) (c : K) (W d j : ℕ) (hd : 1 < d) (hW : 0 < W)
    (hj : d*j ≤ W) (hb : b ≠ 0 → b.natDegree+d*(j+1) ≤ W) :
    (if d*j ≤ W-1 then
      (a.derivative + C c*(b*C ((j+1:ℕ):K))).coeff ((W-1)-d*j) else 0) =
    (W-(d:K)*j)*a.coeff (W-d*j) := by
  by_cases hs : d*j = W
  · have hn : ¬ d*j ≤ W-1 := by omega
    rw [ite_eq_right hn, ←hs, Nat.cast_mul, sub_self, zero_mul]
  · have hle : d*j ≤ W-1 := by omega
    have hidx : W-1-d*j+1 = W-d*j := by omega
    have hcast : ((W-d*j:ℕ):K) = (W:K)-(d:K)*j := by rw [Nat.cast_sub hj, Nat.cast_mul]
    have hlow : (C c*(b*C ((j+1:ℕ):K))).coeff (W-1-d*j) = 0 := by
      by_cases hz : b = 0
      · simp [hz]
      have hh := hb hz
      rw [Nat.mul_add, Nat.mul_one] at hh
      rw [mul_comm b, coeff_C_mul, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < W-1-d*j)]
      simp
    simp only [hle, ite_true, coeff_add, hlow, add_zero, coeff_derivative, ←Nat.cast_add_one,
      hidx, hcast, mul_comm]

/-- The usual `X`-derivative on the coefficient ring. -/
@[instance_reducible] private noncomputable def coordinateDifferential : Differential K[X] :=
  ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩

/-- The ordinary first polar `P_X + c P_Y`, with `c` constant in `X`. -/
noncomputable def ordinaryPolar (P : K[X][X]) (c : K) : K[X][X] :=
  let _ : Differential K[X] := coordinateDifferential
  Differential.mapCoeffs P + C (C c)*P.derivative

private theorem polar_coeff (P : K[X][X]) (c : K) (j : ℕ) :
    (ordinaryPolar P c).coeff j =
      (P.coeff j).derivative + C c*((P.coeff (j+1))*C ((j+1:ℕ):K)) := by
  simp only [ordinaryPolar, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul,
    coeff_derivative, Nat.cast_add_one, map_add, map_natCast, map_one]
  rfl

private theorem polar_weight (P : K[X][X]) (c : K) (d W : ℕ) (hd : 1 < d)
    (hP : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree+d*j ≤ W)
    (j : ℕ) (hn : (ordinaryPolar P c).coeff j ≠ 0) :
    ((ordinaryPolar P c).coeff j).natDegree+d*j ≤ W-1 := by
  rw [polar_coeff] at hn ⊢
  let a := (P.coeff j).derivative
  let b := C c*(P.coeff (j+1)*C ((j+1:ℕ):K))
  change a+b ≠ 0 at hn
  change (a+b).natDegree+d*j ≤ W-1
  have ha (h : a ≠ 0) : a.natDegree+d*j ≤ W-1 := by
    have hh : (P.coeff j).natDegree ≠ 0 := fun h0 => h
      ((congrArg Polynomial.derivative (eq_C_of_natDegree_eq_zero h0)).trans derivative_C)
    have hh' := hP j (fun h0 => hh (by rw [h0, natDegree_zero]))
    have hl : a.natDegree ≤ (P.coeff j).natDegree-1 := natDegree_derivative_le _
    omega
  have hb (h : b ≠ 0) : b.natDegree+d*j ≤ W-1 := by
    have hh := hP (j+1) (fun h0 => h (by simp [b, h0]))
    have hl : b.natDegree ≤ (P.coeff (j+1)).natDegree := by
      dsimp [b]
      rw [mul_comm (P.coeff (j+1))]
      exact (natDegree_C_mul_le ..).trans (natDegree_C_mul_le ..)
    rw [Nat.mul_add, Nat.mul_one] at hh
    omega
  by_cases h₁ : a = 0
  · rw [h₁, zero_add] at hn ⊢
    exact hb hn
  by_cases h₂ : b = 0
  · rw [h₂, add_zero]
    exact ha h₁
  have hs := natDegree_add_le a b
  have hs₁ := ha h₁
  have hs₂ := hb h₂
  omega

/-- The ordinary polar resultant of a weighted cubic has coordinate degree
exactly `6W-9d-3`. Here `f` is its supplied initial cubic, with three
simple nonzero geometric roots. All polar constants give the same degree. -/
theorem cubic_polar_degree (P : K[X][X]) (f : K[X]) (c : K) (W d : ℕ)
    (hd : 1 < d) (hw : 3*d ≤ W) (hchar : (d:K) ≠ 0)
    (hP : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree+d*j ≤ W)
    (hf : ∀ j ≤ 3, f.coeff j = (P.coeff j).coeff (W-d*j))
    (hm : f.natDegree = 3) (hs : f.Separable) (h0 : f.coeff 0 ≠ 0) :
    (resultant P (ordinaryPolar P c) 3 3).natDegree = 6*W-9*d-3 := by
  have hbound (j : ℕ) (hj : j ≤ 3) : d*j ≤ W :=
    (Nat.mul_le_mul_left d hj).trans (by simpa [Nat.mul_comm] using hw)
  have hW : 0 < W := by omega
  have hsep := initial_resultant_ne_zero f W d hs h0 hchar
  rw [hm] at hsep
  have h := resultant_degree P (ordinaryPolar P c) f (initialPolar f W d) 3 3 d W (W-1)
    hP (polar_weight P c d W hd hP) (fun j hj => by simp [hbound j hj, hf j hj])
    (fun j hj => by
      rw [initial_coeff, hf j hj, polar_coeff]
      exact (polar_coeff_top _ _ c W d j hd hW (hbound j hj) (hP (j+1))).symm) hsep
  omega

/-- The weighted transform of the four ordinate coefficients in the common
section chart. -/
noncomputable def chartCubic (P : K[X][X]) (r : K) (W d : ℕ) : K[X][X] := by
  classical
  exact Polynomial.ofFn 4 fun j => CommonSectionChart.change r (W-d*j) (P.coeff j)

/-- At any old coordinate where the leading coefficient, constant coefficient
and discriminant are nonzero, every ordinary polar in the new chart attains
the full coordinate degree. These three tests can be supplied directly to
`CommonSectionChart.simple_fibers`. -/
theorem chart_polar_degree (P : K[X][X]) (r c : K) (W d : ℕ)
    (hd : 1 < d) (hw : 3*d ≤ W) (hchar : (d:K) ≠ 0) (hm : P.natDegree ≤ 3)
    (hP : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree+d*j ≤ W)
    (hl : (P.coeff 3).eval r ≠ 0) (h0 : (P.coeff 0).eval r ≠ 0)
    (hr : (resultant P P.derivative 3 2).eval r ≠ 0) :
    (resultant (chartCubic P r W d) (ordinaryPolar (chartCubic P r W d) c) 3 3).natDegree =
      6*W-9*d-3 := by
  classical
  let f := P.map (evalRingHom r)
  have hc (j : ℕ) (hj : j ≤ 3) :
      (chartCubic P r W d).coeff j = CommonSectionChart.change r (W-d*j) (P.coeff j) := by
    unfold chartCubic
    exact ofFn_coeff_eq_val_of_lt _ (by omega : j < 4)
  have htop (j : ℕ) (hj : j ≤ 3) : f.coeff j = ((chartCubic P r W d).coeff j).coeff (W-d*j) := by
    rw [hc j hj, CommonSectionChart.top_coeff]
    simp [f]
  have hfield (j : ℕ) : f.coeff j = (P.coeff j).eval r := by simp [f]
  have hdeg : f.natDegree = 3 := le_antisymm (natDegree_map_le.trans hm)
    (le_natDegree_of_ne_zero (by rwa [hfield 3]))
  apply cubic_polar_degree _ f c W d hd hw hchar _ htop hdeg
    (separable_map_of_resultant_derivative_padded_ne_zero (evalRingHom r) P hm (by decide) hr)
    (by rwa [hfield 0])
  intro j hn
  by_cases hj : j ≤ 3
  · rw [hc j hj] at hn ⊢
    have hp : P.coeff j ≠ 0 := fun h => hn (by simp [h, CommonSectionChart.change])
    have hbound := hP j hp
    have hcap : (P.coeff j).natDegree ≤ W-d*j := by omega
    have hchanged := CommonSectionChart.degree_le r _ _ hcap
    omega
  · unfold chartCubic at hn
    exact (hn (ofFn_coeff_eq_zero_of_ge _ (by omega : 4 ≤ j))).elim

#print axioms chart_polar_degree
#print axioms cubic_polar_degree
#print axioms resultant_degree

end ProximityGap.WeightedResultantInitial
