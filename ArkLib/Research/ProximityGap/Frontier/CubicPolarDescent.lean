/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CubicPolarSiteBudget
import ArkLib.Research.ProximityGap.Frontier.SeparableScalarDifferential

/-! # Descent of the projective cubic estimate to the original scalar field -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.CubicPolarDescent

open GenericProjectivePolarGcd (polar)
open ReceivedPolarContacts (dx)
open ScalarHessianLocalOrder (hessian)

variable {K L : Type} [Field K] [Field L]

private theorem shift_map (φ : K →+* L) (F : K[X][X]) (x y : K) :
    (ReceivedJetContact.shifted F x y).map (mapRingHom φ) =
      ReceivedJetContact.shifted (F.map (mapRingHom φ)) (φ x) (φ y) := by
  unfold ReceivedJetContact.shifted
  rw [map_taylor, coe_mapRingHom, map_C, Polynomial.map_map, Polynomial.map_map]
  congr 2
  exact RingHom.ext fun q => map_taylor q x φ

private theorem leader_map (φ : K →+* L) {F : K[X][X]} {x y : K} {r i : ℕ}
    (h : TruncatedJetMultipliers.Leader (ReceivedJetContact.shifted F x y) r i) :
    TruncatedJetMultipliers.Leader (ReceivedJetContact.shifted (F.map (mapRingHom φ)) (φ x) (φ y)) r i := by
  rw [← shift_map φ F x y]
  refine ⟨h.value_le,?_,?_⟩
  · simpa only [coeff_map, coe_mapRingHom, ne_eq, map_eq_zero] using h.nonzero
  · intro v q hq
    simp only [coeff_map, coe_mapRingHom, h.lower v q hq, map_zero]

private theorem dx_map (φ : K →+* L) (F : K[X][X]) :
    (dx F).map (mapRingHom φ) = dx (F.map (mapRingHom φ)) := by
  ext j : 1
  simp only [coeff_map, coe_mapRingHom, ReceivedPolarContacts.coeff_dx, derivative_map]

private theorem polar_map (φ : K →+* L) (U V : K[X][X]) (c : K) :
    (polar U V c).map (mapRingHom φ) = polar (U.map (mapRingHom φ)) (V.map (mapRingHom φ)) (φ c) := by
  simp [polar]

private theorem map_polar_resultant (φ : K →+* L) (F : K[X][X]) (x : K) :
    let G := F.map (mapRingHom φ)
    G.resultant (polar (dx G) G.derivative (φ x)) 3 3 =
      (F.resultant (polar (dx F) F.derivative x) 3 3).map φ := by
  dsimp only
  rw [derivative_map, ← dx_map, ← polar_map]
  exact resultant_map_map _ _ _ _ _

variable [Differential K]
local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩
local instance [Differential L] : Differential L[X] := ⟨Differential.mapCoeffs⟩

set_option maxRecDepth 4000 in
/-- The original cubic over an arbitrary differential field satisfies the
global estimate. Only its low-degree coordinate roots need separable splitting.
The second slope is selected in the prescribed constant subfield. -/
private theorem budget_of_extension [DecidableEq K] [IsSepClosed L] [Infinite L] [Differential L]
    [Algebra K L] (dc : ∀ x : K, (algebraMap K L x)′ = algebraMap K L x′) {k : Type} [Field k] [Infinite k] (ι : k →+* K)
    (p : ℕ) [CharP K p] (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (F : K[X][X]) (hf : F.natDegree=3) (hprim : F.IsPrimitive)
    (hV : F.resultant F.derivative 3 3 ≠ 0) (hH : F.resultant (hessian F) 3 7 ≠ 0)
    (A : K[X]) (hA : A ≠ 0) (hAp : A.natDegree < p) (except : Finset k)
    (D : Finset K) (l : K → K) (r : K → ℕ)
    (hsite : ∀ α ∈ D, α′=0 ∧ (l α)′′=0 ∧ ∃ i, TruncatedJetMultipliers.Leader
        (ReceivedJetContact.shifted F α (l α)) (r α) i) :
    ∃ c ∉ except, let B := F.resultant (polar (dx F) F.derivative (ι c)) 3 3
      B ≠ 0 ∧ 3*(∑ α ∈ D, r α)+2*(GCDMonoid.gcd A B).natDegree ≤
        2*D.card+4*F.leadingCoeff.natDegree+(F.resultant (hessian F) 3 7).natDegree := by
  classical
  let φ : K →+* L := algebraMap K L
  let : CharP L p := charP_of_injective_ringHom φ.injective p
  have hd (x : K) : (φ x)′ = φ x′ := dc x
  let m := mapRingHom φ
  let G := F.map m
  have hm : Function.Injective m := Polynomial.map_injective _ φ.injective
  have hg : G.natDegree = 3 := (natDegree_map_eq_of_injective hm _).trans hf
  have hgp : G.IsPrimitive := by
    apply isPrimitive_of_contentIdeal_eq_top
    rw [show G = F.map m from rfl, contentIdeal_map_eq_map_contentIdeal,
      (isPrimitive_iff_contentIdeal_eq_top F).mp hprim, Ideal.map_top]
  have hder (q : K[X]) : m q′ = (m q)′ := by
    ext j : 1
    change ((Differential.mapCoeffs q).map φ).coeff j = (Differential.mapCoeffs (q.map φ)).coeff j
    simp only [coeff_map, Differential.coeff_mapCoeffs]
    exact (hd _).symm
  have hh : (hessian F).map m = hessian G := ReceivedPowerSeriesHessian.hessian_map m hder F
  have hres (V : K[X][X]) (a b : ℕ) : G.resultant (V.map m) a b = (F.resultant V a b).map φ :=
    resultant_map_map F V a b m
  have yr : G.resultant G.derivative 3 3 = (F.resultant F.derivative 3 3).map φ := by
    rw [show G.derivative = F.derivative.map m from derivative_map F m]
    exact hres F.derivative 3 3
  have hr : G.resultant (hessian G) 3 7 = (F.resultant (hessian F) 3 7).map φ := by
    rw [← hh]; exact hres _ _ _
  have map_ne (q : K[X]) (hq : q ≠ 0) : q.map φ ≠ 0 := fun h => hq ((Polynomial.map_injective _ φ.injective) (h.trans (Polynomial.map_zero φ).symm))
  let emb : K ↪ L := ⟨φ,φ.injective⟩
  let inv := Function.invFun φ
  have hi (x : K) : inv (φ x) = x := Function.leftInverse_invFun φ.injective x
  have hn2 : (2:L) ≠ 0 := fun h => h₂ (φ.injective (by simpa only [map_ofNat,map_zero] using h))
  have hn3 : (3:L) ≠ 0 := fun h => h₃ (φ.injective (by simpa only [map_ofNat,map_zero] using h))
  have E := CubicPolarSiteBudget.cubic_site_budget (φ.comp ι) p
    hn2 hn3
    G hg hgp (by rw [yr]; exact map_ne _ hV) (by rw [hr]; exact map_ne _ hH)
    (A.map φ) (map_ne _ hA) (by simpa only [natDegree_map_eq_of_injective φ.injective] using hAp)
    except (D.map emb) (fun z => φ (l (inv z))) (fun z => r (inv z))
  have hsites : ∀ z ∈ D.map emb, z′=0 ∧ (φ (l (inv z)))′′=0 ∧
      ∃ i, TruncatedJetMultipliers.Leader (ReceivedJetContact.shifted G z (φ (l (inv z)))) (r (inv z)) i := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
    obtain ⟨h1,h2,i,h3⟩ := hsite x hx
    change (φ x)′ = 0 ∧ (φ (l (inv (φ x))))′′ = 0 ∧ _
    change (φ x)′ = 0 ∧ (φ (l (inv (φ x))))′′=0 ∧ ∃ i,
      TruncatedJetMultipliers.Leader (ReceivedJetContact.shifted G (φ x) (φ (l (inv (φ x))))) (r (inv (φ x))) i
    rw [hi, hd, hd, hd, h1, h2, map_zero]
    exact ⟨rfl,rfl,i,leader_map φ h3⟩
  obtain ⟨c,hc,hb,H⟩ := E hsites
  let B := F.resultant (polar (dx F) F.derivative (ι c)) 3 3
  have hB : G.resultant (polar (dx G) G.derivative (φ (ι c))) 3 3 = B.map φ :=
    map_polar_resultant φ F (ι c)
  dsimp only [RingHom.comp_apply] at hb H
  rw [hB] at hb
  have hBn : B ≠ 0 := by rintro hz; simp [hz] at hb
  refine ⟨c,hc,hBn,?_⟩
  let Q := GCDMonoid.gcd A B
  have hgcd : Q.map φ ∣ GCDMonoid.gcd (A.map φ) (B.map φ) :=
    dvd_gcd (Polynomial.map_dvd φ (gcd_dvd_left A B)) (Polynomial.map_dvd φ (gcd_dvd_right A B))
  have gne : GCDMonoid.gcd (A.map φ) (B.map φ) ≠ 0 := by
    intro hz; have hh := gcd_dvd_right (A.map φ) (B.map φ); rw [hz,zero_dvd_iff] at hh; exact hb hh
  have hdeg := natDegree_le_of_dvd hgcd gne
  rw [natDegree_map_eq_of_injective φ.injective] at hdeg
  have hsum : (∑ z ∈ D.map emb, r (inv z)) = ∑ z ∈ D, r z := by simp [emb,hi]
  have hlc : G.leadingCoeff.natDegree = F.leadingCoeff.natDegree := by
    change (F.map m).leadingCoeff.natDegree = _
    rw [leadingCoeff_map_of_injective hm]; exact natDegree_map_eq_of_injective φ.injective _
  have hgd := hdeg.trans_eq (congrArg (fun t : L[X] =>
    (GCDMonoid.gcd (A.map φ) t).natDegree) hB.symm)
  have hresdeg := (congrArg Polynomial.natDegree hr).trans (natDegree_map_eq_of_injective φ.injective _)
  have smaller := Nat.add_le_add (Nat.mul_le_mul_left 3 hsum.symm.le) (Nat.mul_le_mul_left 2 hgd)
  have larger := Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left 2 (Finset.card_map (s := D) (f := emb)).le)
    (Nat.mul_le_mul_left 4 hlc.le)) hresdeg.le
  have first := Nat.le_trans smaller H
  have combined := Nat.le_trans first larger
  exact combined

/-- Descend the sheet inequality through the absolute separable closure. -/
theorem cubic_site_budget [DecidableEq K] {k : Type} [Field k] [Infinite k] (ι : k →+* K)
    (p : ℕ) [CharP K p] (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (F : K[X][X]) (hf : F.natDegree=3) (hprim : F.IsPrimitive)
    (hV : F.resultant F.derivative 3 3 ≠ 0) (hH : F.resultant (hessian F) 3 7 ≠ 0)
    (A : K[X]) (hA : A ≠ 0) (hAp : A.natDegree < p) (except : Finset k)
    (D : Finset K) (l : K → K) (r : K → ℕ)
    (hsite : ∀ α ∈ D, α′=0 ∧ (l α)′′=0 ∧ ∃ i, TruncatedJetMultipliers.Leader
        (ReceivedJetContact.shifted F α (l α)) (r α) i) :
    ∃ c ∉ except, let B := F.resultant (polar (dx F) F.derivative (ι c)) 3 3
      B ≠ 0 ∧ 3*(∑ α ∈ D, r α)+2*(GCDMonoid.gcd A B).natDegree ≤
        2*D.card+4*F.leadingCoeff.natDegree+(F.resultant (hessian F) 3 7).natDegree := by
  let L := SeparableClosure K
  obtain ⟨d,hd⟩ := SeparableScalarDifferential.closure_extension (K := K)
  let : Differential L := d
  let : Infinite L := Infinite.of_injective ((algebraMap K L).comp ι) ((algebraMap K L).comp ι).injective
  exact budget_of_extension (L := L) hd ι p h₂ h₃ F hf hprim hV hH A hA hAp except D l r hsite

#print axioms cubic_site_budget
end ArkLib.ProximityGap.Frontier.CubicPolarDescent
