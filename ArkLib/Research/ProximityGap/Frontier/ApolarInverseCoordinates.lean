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

#print axioms weighted_inverse
#print axioms apolar_inverse
#print axioms nodal_inverse_dvd
#print axioms reindex_representative
end ProximityGap.ApolarInverseCoordinates
