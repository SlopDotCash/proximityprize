/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSparseInterpolation
import ArkLib.Research.ProximityGap.Frontier.ApolarCoordinateEquations
import ArkLib.Research.ProximityGap.Frontier.ApolarParameterTransition

/-! # The two coordinate interpolation equations of a sparse apolar pencil -/

set_option autoImplicit false
namespace ProximityGap.ApolarInverseCoordinates
open Finset Polynomial ApolarDividedLocator ApolarDividedPolynomial ApolarRootTransition
open ApolarSyndromeInterpolation ApolarSparseInterpolation ApolarParameterTransition

variable {K : Type*} [Field K] [DecidableEq K]
local notation "Biv" => K[X][X]

/-- Represent a nonzero coordinate as a unit, extending the function by one at zero. -/
noncomputable def siteUnit (x : K) : Kˣ := if h : x=0 then 1 else Units.mk0 x h

theorem siteUnit_eq {x : K} (hx : x≠0) : (siteUnit x : K) = x := by simp [siteUnit,hx]

/-- Units in the coefficient ring of the parameter polynomial. -/
noncomputable def coordinateUnit (x : K) : K[X]ˣ :=
  Units.map (C : K →+* K[X]).toMonoidHom (siteUnit x)

theorem coordinateUnit_eq {x : K} (hx : x≠0) : (coordinateUnit x : K[X]) = C x :=
  congrArg C (siteUnit_eq hx)

theorem coordinateUnit_inv {x : K} (hx : x≠0) : (↑(coordinateUnit x)⁻¹ : K[X]) = C x⁻¹ := by
  change C (↑(siteUnit x)⁻¹ : K) = C x⁻¹
  simp [siteUnit,hx]

/-- The weighted moment functional on inverted sites evaluates the reversed test form. -/
theorem weighted_inverse (D : Finset K) (hD : 0 ∉ D) (w : K → K) (p : K[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) :
    weighted (D.image Inv.inv) (RingHom.id K) (fun z => w z⁻¹*(z⁻¹)^d) p =
      weighted D (RingHom.id K) w (reflect d p) := by
  classical
  rw [weighted_apply,weighted_apply,Finset.sum_image (fun _ _ _ _ h => inv_injective h)]
  apply sum_congr rfl
  intro y hy
  have hn : y≠0 := fun h => hD (h ▸ hy)
  have hh := eval_reflect (siteUnit y) d p hp
  change (reflect d p).eval (siteUnit y:K) = _ at hh
  simp only [siteUnit_eq hn, Units.val_inv_eq_inv_val] at hh
  simp only [inv_inv,RingHom.id_apply,hh,mul_assoc]

/-- Inverted sparse measures agree on the entire degree window. -/
theorem sparse_inverse (D E : Finset K) (hD : 0∉D) (hE : E⊆D) (w v : K → K) (d : ℕ)
    (hs : ∀ p : K[X], p.natDegree ≤ d →
      weighted D (RingHom.id K) w p = weighted E (RingHom.id K) v p) :
    ∀ p : K[X], p.natDegree ≤ d →
      weighted (D.image Inv.inv) (RingHom.id K) (fun i => w i⁻¹*(i⁻¹)^d) p =
        weighted (E.image Inv.inv) (RingHom.id K) (fun i => v i⁻¹*(i⁻¹)^d) p := by
  intro p hp
  rw [weighted_inverse D hD w p d hp,weighted_inverse E (fun h => hD (hE h)) v p d hp]
  exact hs _ (natDegree_reflect_le.trans (max_le le_rfl hp))

/-- Apolarity also survives at fibers whose affine locator degree drops. -/
theorem apolar_inverse (D : Finset K) (hD : 0∉D) (w : K → K) (f : K[X]) (r s : ℕ)
    (hf : f.natDegree ≤ r) (ha : ApolarThrough (weighted D (RingHom.id K) w) f s) :
    ApolarThrough (weighted (D.image Inv.inv) (RingHom.id K) (fun i => w i⁻¹*(i⁻¹)^(r+s)))
      (reflect r f) s := by
  intro p hp
  have hd := natDegree_reflect_le.trans (max_le le_rfl hf)
  rw [weighted_inverse _ hD _ _ _ (natDegree_mul_le.trans (Nat.add_le_add hd hp)),
    reflect_mul _ _ hd hp,reflect_reflect]
  exact ha _ (natDegree_reflect_le.trans (max_le le_rfl hp))

/-- Any domain vanisher multiple of degree at most n reciprocates to a multiple
of the monic vanisher of the inverse coordinates. -/
theorem nodal_inverse_dvd (H : Finset K) (h0 : 0 ∉ H) (V : K[X]) (n : ℕ)
    (hd : V.natDegree ≤ n) (hV : Lagrange.nodal H id ∣ V) :
    Lagrange.nodal (H.image Inv.inv) id ∣ reflect n V := by
  classical
  by_cases hv : V=0
  · simp [hv,reflect_zero]
  obtain ⟨G,hG⟩ := hV
  have hv0 : Lagrange.nodal H id ≠ 0 ∧ G ≠ 0 := mul_ne_zero_iff.mp (hG ▸ hv)
  have hz := hd
  rw [hG,natDegree_mul hv0.1 hv0.2,Lagrange.natDegree_nodal] at hz
  rw [hG,show n=H.card+(n-H.card) by omega,reflect_mul _ _ (Lagrange.natDegree_nodal ..).le (by omega)]
  apply dvd_mul_of_dvd_left _ _
  have ht : Lagrange.nodal H (fun i => (siteUnit i:K)) = Lagrange.nodal H id := by
    apply Finset.prod_congr rfl
    intro y hy
    change X-C (siteUnit y:K) = X-C y
    rw [siteUnit_eq (fun h => h0 (h ▸ hy))]
  have hi : Lagrange.nodal (H.image Inv.inv) id = Lagrange.nodal H (fun i => (↑(siteUnit i)⁻¹:K)) := by
    rw [Lagrange.nodal,Finset.prod_image (fun _ _ _ _ h => inv_injective h)]
    apply Finset.prod_congr rfl
    intro y hy
    simp [siteUnit,show y≠0 from fun h => h0 (h ▸ hy)]
  rw [← ht,nodal_reverse H siteUnit,hi]
  exact dvd_mul_left _ _

/-- The reindexed polynomial before and after coordinate inversion. -/
theorem reindex_representative (D : Finset K) (hD : 0 ∉ D) (w : K → K[X]) (d : ℕ) (f : Biv) :
    representative (D.image Inv.inv) C (fun i => w i⁻¹*C ((i⁻¹)^d)) f =
      representative D (fun i => (↑(coordinateUnit i)⁻¹:K[X]))
        (fun i => w i*(coordinateUnit i:K[X])^d) f := by
  classical
  rw [representative,representative,Finset.sum_image (fun _ _ _ _ h => inv_injective h)]
  apply sum_congr rfl
  intro y hy
  have hn : y≠0 := fun h => hD (h ▸ hy)
  simp only [inv_inv,coordinateUnit_eq hn,coordinateUnit_inv hn,C_pow]

/-- The zero-free domain allows the forward representative to use unit-valued sites. -/
theorem reindex_forward (D : Finset K) (hD : 0∉D) (w : K → K[X]) (f : Biv) :
    representative D (fun i => (coordinateUnit i:K[X])) w f = representative D C w f := by
  apply sum_congr rfl
  intro y hy
  change C (w y)*divided f (coordinateUnit y:K[X]) = C (w y)*divided f (C y)
  rw [coordinateUnit_eq (fun h => hD (h ▸ hy))]

omit [DecidableEq K] in
/-- The parameter vanisher becomes a coordinate constant when exchanging variables. -/
theorem swap_nodal (G : Finset K) :
    Bivariate.swap (Lagrange.nodal G (C : K →+* K[X])) = C (Lagrange.nodal G id) := by
  simp only [Lagrange.nodal,map_prod,map_sub,Bivariate.swap_Y,Bivariate.swap_C_C,id_eq]

/-- The forward unit-site measure is the original parameter-valued measure. -/
theorem measure_forward (D : Finset K) (hD : 0∉D) (w : K → K[X]) :
    measure D (fun i => (coordinateUnit i:K[X])) w = measure D C w := by
  apply sum_congr rfl
  intro i hi
  change w i • Polynomial.leval (coordinateUnit i:K[X]) = w i • Polynomial.leval (C i)
  rw [coordinateUnit_eq (fun h => hD (h ▸ hi))]

/-- Paired interpolation on the original and reciprocal coordinate charts.
The returned polynomials Q,B,Qi,Bi are parameter-outer for degree bounds.
Their swaps appear on the coordinate-outer identities used for descent.
The polynomial V can be any degree-bounded multiple of the domain vanisher. -/
theorem paired_coordinates (D G : Finset K) (w : K → K[X]) (f : Biv) (V : K[X])
    (l r s n : ℕ) (hD : 0∉D) (hG : G.Nonempty) (hl : 0<l)
    (hV : Lagrange.nodal D id ∣ V) (hn : V.natDegree ≤ n)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hr : f.natDegree ≤ r) (hm : 3*(l+1) < G.card+l)
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ s+1 ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ r+s →
      weighted D (RingHom.id K) (fun i => (w i).eval t) p = weighted E (RingHom.id K) v p)
    (ha : ∀ t ∈ G, ApolarThrough (weighted D (RingHom.id K) (fun i => (w i).eval t))
      (f.map (evalRingHom t)) s) :
    ∃ Q B Qi Bi : Biv, Q.natDegree < G.card ∧ Qi.natDegree < G.card ∧
      B.natDegree < l ∧ Bi.natDegree < l ∧
      V.map C*(representative D (fun i => (coordinateUnit i:K[X])) w f)^3 =
        f*Bivariate.swap Q+C (Lagrange.nodal G id)*Bivariate.swap B ∧
      reflect n (V.map C)*(-representative D (fun i => (↑(coordinateUnit i)⁻¹:K[X]))
        (fun i => w i*(coordinateUnit i:K[X])^(r+s)) (reflect r f))^3 =
        reflect r f*Bivariate.swap Qi+C (Lagrange.nodal G id)*Bivariate.swap Bi := by
  classical
  obtain ⟨Q,B,hB,hQ,hb⟩ := interpolate D G w V f hG hV hw hf
    (Nat.add_le_add_right hr s) hm hsp ha
  let H := D.image Inv.inv
  let wi := fun i : K => w i⁻¹*C ((i⁻¹)^(r+s))
  have hiw (i : K) (hi : i ∈ H) : (wi i).natDegree ≤ 1 := by
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hi
    simp only [wi, inv_inv]
    exact (natDegree_mul_C_le ..).trans (hw y hy)
  have hif (j : ℕ) : ((reflect r f).coeff j).natDegree ≤ l := by
    rw [coeff_reflect]
    apply hf
  have hsp' (t : K) (ht : t ∈ G) : ∃ E ⊆ H, E.card ≤ s+1 ∧ ∃ v : K → K,
      ∀ p : K[X], p.natDegree ≤ r+s → weighted H (RingHom.id K) (fun i => (wi i).eval t) p =
        weighted E (RingHom.id K) v p := by
    obtain ⟨E,hE,hc,v,hv⟩ := hsp t ht
    refine ⟨E.image Inv.inv,image_subset_image hE,(card_image_le.trans hc),fun y => v y⁻¹*(y⁻¹)^(r+s),?_⟩
    simpa only [H,wi,eval_mul,eval_C] using sparse_inverse D E hD hE _ v (r+s) hv
  have ha' (t : K) (ht : t∈G) : ApolarThrough (weighted H (RingHom.id K) (fun i => (wi i).eval t))
      ((reflect r f).map (evalRingHom t)) s := by
    rw [← reflect_map]
    simpa only [H,wi,eval_mul,eval_C] using apolar_inverse D hD _ (f.map (evalRingHom t)) r s
      (natDegree_map_le.trans hr) (ha t ht)
  obtain ⟨Qi,Bi,hBi,hQi,hbi⟩ := interpolate H G wi (reflect n V) (reflect r f) hG
    (nodal_inverse_dvd D hD V n hn hV) hiw hif
    (Nat.add_le_add_right (natDegree_reflect_le.trans (max_le le_rfl hr)) s) hm hsp' ha'
  have fore := congrArg Bivariate.swap hB
  have back := congrArg Bivariate.swap hBi
  simp only [map_add,map_mul,map_pow,Bivariate.swap_C,Bivariate.swap_swap_apply,swap_nodal] at fore back
  have hb' : B.natDegree<l := hb.elim (fun h => by simpa [h] using hl) id
  have hbi' : Bi.natDegree<l := hbi.elim (fun h => by simpa [h] using hl) id
  refine ⟨Q,B,-Qi,-Bi,hQ,by simpa only [natDegree_neg] using hQi,hb',
    by simpa only [natDegree_neg] using hbi',?_,?_⟩
  · rw [reindex_forward D hD w f]
    exact fore
  · rw [reflect_map,← reindex_representative D hD w (r+s) (reflect r f),map_neg,map_neg]
    dsimp only [H,wi] at back
    linear_combination -back

#print axioms paired_coordinates
#print axioms weighted_inverse
#print axioms apolar_inverse
#print axioms nodal_inverse_dvd
#print axioms reindex_representative
end ProximityGap.ApolarInverseCoordinates
