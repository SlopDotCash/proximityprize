/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Research.ProximityGap.Frontier.CubicSheetExcess
import ArkLib.Research.ProximityGap.Frontier.ReceivedPowerSeriesHessian

/-! # Proper scalar-Hessian intersection under a weighted change of coordinates

One constant coordinate outside the zeros of the old resultant and leading
coefficient is sufficient. The fiber there changes only by nonzero scalings.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.ChartFiberHessian
open _root_.ProximityGap.CommonSectionChart (change)
open ScalarHessianLocalOrder (hessian)

variable {K : Type} [Field K]

/-- Scaling the equation and dilating its ordinate at a fiber. -/
def dilate (u v : K) (f : K[X]) := C u * f.comp (C v * (Polynomial.X : K[X]))

private theorem dilate_coeff (u v : K) (f : K[X]) (j : ℕ) :
    (dilate u v f).coeff j = u * (f.coeff j * v^j) := by
  simp only [dilate,coeff_C_mul,comp_C_mul_X_coeff]

theorem dilate_degree {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (f : K[X]) :
    (dilate u v f).natDegree = f.natDegree := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp [dilate_coeff, coeff_eq_zero_of_natDegree_lt hi]
  · by_cases hf : f=0
    · simp [hf]
    · apply le_natDegree_of_ne_zero
      rw [dilate_coeff,coeff_natDegree]
      exact mul_ne_zero hu (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (pow_ne_zero _ hv))

/-- The full polynomial at the new coordinate, given the defining transformed
coefficient slots and their original degree budgets. -/
theorem fiber_dilate (F G : K[X][X]) (r x : K) (hx : x ≠ r) (w d : ℕ)
    (hw : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (hG : ∀ j, G.coeff j = change r (w-d*j) (F.coeff j)) :
    let t := (x-r)⁻¹
    G.map (evalRingHom t) = dilate (t^w) ((t^d)⁻¹) (F.map (evalRingHom x)) := by
  intro t
  ext j
  simp only [coeff_map, dilate_coeff, coe_evalRingHom, hG]
  by_cases hf : F.coeff j = 0
  · simp [hf,change]
  obtain hb := hw j hf
  rw [_root_.ProximityGap.CommonSectionChart.eval_site r x _ _ (by omega) hx]
  have ht : t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hx)
  change t^(w-d*j) * (F.coeff j).eval x = _
  have he : t^(w-d*j) * (t^d)^j = t^w := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel (show d*j ≤ w by omega)]
  change t^(w-d*j) * _ = t^w * (_ * ((t^d)⁻¹)^j)
  have hi : (t^d)^j * ((t^d)⁻¹)^j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ ht), one_pow]
  rw [← he]
  calc
    _ = t^(w-d*j) * (F.coeff j).eval x * ((t^d)^j * ((t^d)⁻¹)^j) := by rw [hi,mul_one]
    _ = _ := by ring

private theorem coprime_dilate {u v z : K} (hu : u ≠ 0) (hz : z ≠ 0)
    {f g : K[X]} (h : IsCoprime f g) : IsCoprime (dilate u v f) (dilate z v g) := by
  obtain ⟨P,Q,H⟩ := h
  let δ := compRingHom (C v * (Polynomial.X : K[X]))
  refine ⟨δ P * C u⁻¹, δ Q * C z⁻¹, ?_⟩
  change δ P*C u⁻¹*(C u*δ f)+δ Q*C z⁻¹*(C z*δ g)=1
  calc
    _ = C (u⁻¹*u)*(δ P*δ f)+C (z⁻¹*z)*(δ Q*δ g) := by simp only [map_mul]; ring
    _ = 1 := by simpa [hu,hz] using congrArg δ H

/-- Multiplication and dilation by nonzero constants preserve a nonzero
padded resultant when the degree of the first test is exact. -/
theorem dilate_nonzero {f g : K[X]} {m n : ℕ} (hm : f.natDegree=m) (hfm : 0<m)
    (hg : g.natDegree ≤ n) (hr : f.resultant g m n ≠ 0) {u z v : K}
    (hu : u ≠ 0) (hz : z ≠ 0) (hv : v ≠ 0) :
    (dilate u v f).resultant (dilate z v g) m n ≠ 0 := by
  have ha : f ≠ 0 := by intro h; simp [h] at hm; omega
  have hc : IsCoprime f g := by
    by_contra h
    have hzero := (resultant_eq_zero_iff (f := f) (g := g)).mpr ⟨Or.inl ha,h⟩
    apply hr
    rw [← Nat.add_sub_of_le hg, resultant_add_right_deg _ _ _ _ _ le_rfl, ← hm,hzero,mul_zero]
  let F := dilate u v f
  let G := dilate z v g
  have hdeg : F.natDegree=m := (dilate_degree hu hv f).trans hm
  have hG : G.natDegree ≤ n := (dilate_degree hz hv g).trans_le hg
  have hne : F ≠ 0 := by intro h; simp [h] at hdeg; omega
  change F.resultant G m n ≠ 0
  rw [← Nat.add_sub_of_le hG, resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdeg,coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hne))
    (resultant_ne_zero _ _ (coprime_dilate hu hz hc))

variable [Differential K]

private theorem dilate_D (f : K[X]) {u v : K} (hu : u′=0) (hv : v′=0) :
    Differential.mapCoeffs (dilate u v f) = dilate u v (Differential.mapCoeffs f) := by
  ext i
  simp [Differential.coeff_mapCoeffs,dilate_coeff,Differential.deriv.leibniz,
    Differential.deriv.leibniz_pow,hu,hv,mul_comm]

omit [Differential K] in
theorem dilate_Y (f : K[X]) (u v : K) :
    (dilate u v f).derivative = dilate (u*v) v f.derivative := by
  ext i
  simp only [coeff_derivative,dilate_coeff,pow_succ]
  ring

/-- The actual scalar Hessian on a rescaled fiber acquires the single
nonzero factor u cubed times v squared. -/
theorem dilate_hessian (f : K[X]) {u v : K} (hu : u′=0) (hv : v′=0) :
    hessian (dilate u v f) = dilate (u^3*v^2) v (hessian f) := by
  unfold hessian
  simp only [dilate_D _ hu hv, dilate_Y]
  simp only [dilate, Polynomial.sub_comp, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.pow_comp, Polynomial.ofNat_comp, map_mul, map_pow]
  ring

local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩

private theorem eval_diff {x : K} (hx : x′=0) (q : K[X]) :
    (evalRingHom x) q′ = ((evalRingHom x) q)′ := by
  change (Differential.mapCoeffs q).eval x = (q.eval x)′
  simpa only [coe_aeval_eq_eval, hx, mul_zero, add_zero] using
    (Differential.deriv_aeval_eq x q).symm

/-- A good constant fiber witnesses proper intersection of the transformed
cubic with both its value derivative and its scalar Hessian. -/
theorem transfer {k : Type} [Field k] [Infinite k] (ι : k →+* K)
    (hι : ∀ a, (ι a)′ = 0) (F G : K[X][X]) (r : k) (w d : ℕ)
    (hf : F.natDegree=3)
    (hw : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (hG : ∀ j, G.coeff j = change (ι r) (w-d*j) (F.coeff j))
    (hV : F.resultant F.derivative 3 3 ≠ 0) (hH : F.resultant (hessian F) 3 7 ≠ 0) :
    G.resultant G.derivative 3 3 ≠ 0 ∧ G.resultant (hessian G) 3 7 ≠ 0 := by
  classical
  let tests : Finset K[X] := {F.leadingCoeff,F.resultant F.derivative 3 3,F.resultant (hessian F) 3 7}
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hf)
  have hn : ∀ q ∈ tests, q ≠ 0 := by
    intro q hq
    simp only [tests, Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with h | h | h
    · exact h.symm ▸ hlc
    · exact h.symm ▸ hV
    · exact h.symm ▸ hH
  obtain ⟨s,hs⟩ := Infinite.exists_notMem_finset (insert r (_root_.ProximityGap.CommonSectionChart.forbidden ι tests))
  have havoid := _root_.ProximityGap.CommonSectionChart.avoids_tests ι tests hn
    (fun h => hs (Finset.mem_insert_of_mem h))
  let x := ι s
  let t := (x-ι r)⁻¹
  have hxr : x ≠ ι r := ι.injective.ne (fun h => hs (h ▸ Finset.mem_insert_self ..))
  have ht : t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hxr)
  have htx : t′=0 := by simp [t,x,(Differential.deriv : Derivation ℤ K K).leibniz_inv,map_sub,hι]
  let u := t^w
  let v := (t^d)⁻¹
  have hu : u ≠ 0 := pow_ne_zero _ ht
  have hv : v ≠ 0 := inv_ne_zero (pow_ne_zero _ ht)
  have hdu : u′=0 := by simp [u,Differential.deriv.leibniz_pow,htx]
  have hdv : v′=0 := by simp [v,(Differential.deriv : Derivation ℤ K K).leibniz_inv,Differential.deriv.leibniz_pow,htx]
  let f := F.map (evalRingHom x)
  have hl := havoid F.leadingCoeff (by simp [tests])
  have hd : f.natDegree=3 := by
    apply le_antisymm (natDegree_map_le.trans hf.le)
    apply le_natDegree_of_ne_zero
    rw [show f.coeff 3 = (F.coeff 3).eval x from coeff_map .., ← hf, coeff_natDegree]
    exact hl
  have hh (q : K[X][X]) (a : K) (ha : a′=0) :
      (hessian q).map (evalRingHom a)=hessian (q.map (evalRingHom a)) :=
    ReceivedPowerSeriesHessian.hessian_map _ (eval_diff ha) _
  have hderRes : f.resultant f.derivative 3 3 ≠ 0 := by
    rw [show f.derivative = F.derivative.map (evalRingHom x) from derivative_map ..,resultant_map_map]
    exact havoid _ (by simp [tests])
  have hhesRes : f.resultant (hessian f) 3 7 ≠ 0 := by
    rw [← hh F x (hι s),resultant_map_map]
    exact havoid _ (by simp [tests])
  have hg : G.map (evalRingHom t)=dilate u v f := fiber_dilate F G (ι r) x hxr w d hw hG
  constructor
  · intro e
    have h := congrArg (evalRingHom t) e
    rw [←resultant_map_map,← derivative_map,hg,dilate_Y,map_zero] at h
    exact dilate_nonzero hd (by decide) (by have := natDegree_derivative_le f; omega) hderRes
      hu (mul_ne_zero hu hv) hv h
  · intro e
    have h := congrArg (evalRingHom t) e
    rw [←resultant_map_map,hh G t htx,hg,dilate_hessian _ hdu hdv,map_zero] at h
    exact dilate_nonzero hd (by decide) (by
      rw [←hh F x (hι s)]
      exact natDegree_map_le.trans (CubicSheetExcess.hessian_degree F hf.le)) hhesRes
      hu (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)) hv h

#print axioms transfer
#print axioms fiber_dilate
#print axioms dilate_nonzero
#print axioms dilate_hessian
end ArkLib.ProximityGap.Frontier.ChartFiberHessian
