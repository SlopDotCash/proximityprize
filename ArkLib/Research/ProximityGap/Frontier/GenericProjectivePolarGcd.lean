/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectiveCubicLocalOrder
import ArkLib.Research.ProximityGap.Frontier.FiniteNormalizationColength
import Mathlib.Data.ENat.BigOperators

/-! # A constant second polar measures all first-polar fibers

After fixing the first resultant, choose the second slope in an arbitrary
infinite ground field. Its resultant has the required local multiplicities at
all roots of the first, even if two unrelated branches meet the same fiber.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.GenericProjectivePolarGcd

open BinaryBranchResultant PolynomialLocalOrder ProjectiveCubicLocalOrder FiniteNormalizationColength

variable {K : Type*} [Field K]

/-- Homogeneous evaluation in the sixth-root parameter at a finite coordinate. -/
def sheetValue (α : K) (G : K[X][X]) (h : ℕ) (b a : K⟦X⟧) : K⟦X⟧ :=
  binaryValue ((G.map (atPoint α)).map (PowerSeries.expand 6 (by decide) (R := K)).toRingHom) h b a

/-- A polar slope constant in both coordinate variables. -/
def polar (U V : K[X][X]) (c : K) := U + C (C c)*V

theorem polar_degree (U V : K[X][X]) (c : K) (h : ℕ) (hU : U.natDegree ≤ h)
    (hV : V.natDegree ≤ h) : (polar U V c).natDegree ≤ h :=
  natDegree_add_le_of_degree_le hU ((natDegree_C_mul_le ..).trans hV)

theorem sheetValue_polar (α : K) (U V : K[X][X]) (c : K) (h : ℕ) (b a : K⟦X⟧) :
    sheetValue α (polar U V c) h b a =
      sheetValue α U h b a + c • sheetValue α V h b a := by
  have hc : atPoint α (C c) = PowerSeries.C c := by
    change ((Polynomial.taylor α (C c) : K[X]) : K⟦X⟧) = _
    simp
  have he : (PowerSeries.expand 6 (by decide) (R := K)).toRingHom (PowerSeries.C c) =
      PowerSeries.C c := PowerSeries.expand_C _ _ _
  simp only [sheetValue, polar, Polynomial.map_add, Polynomial.map_mul, map_C,
    hc, he, binaryValue_add, binaryValue_C_mul, PowerSeries.smul_eq_C_mul]

/-- Every nonzero resultant has nonzero formal values on every sheet
in its local norm formula, including outside its finite root support. -/
theorem sheet_nonzero (R : K[X]) (hR : R ≠ 0) (α : K) (v : Fin 3 → K⟦X⟧)
    (h : 6 • (atPoint α R).order = ∑ i, (v i).order) (i : Fin 3) : v i ≠ 0 := by
  intro hz
  have hi : (v i).order ≤ ∑ j, (v j).order := single_le_sum (fun j _ => (show (0:ℕ∞) ≤ (v j).order from zero_le)) (mem_univ i)
  rw [hz, PowerSeries.order_zero, ← h, local_order α R hR] at hi
  have hfin : 6 • (R.rootMultiplicity α : ℕ∞) ≠ ⊤ := by
    simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using ENat.natCast_ne_top (6*R.rootMultiplicity α)
  exact hfin (top_le_iff.mp hi)

/-- The chosen charts may be shared with the Hessian. For every test their
padded norm measures the actual resultant order at every finite place. -/
def NormCharts (F : K[X][X]) (a b : K → Fin 3 → K⟦X⟧) : Prop :=
  ∀ α G h, G.natDegree ≤ h → 6 • (atPoint α (F.resultant G 3 h)).order =
    ∑ i, (sheetValue α G h (b α i) (a α i)).order

theorem generic_second_polar {k : Type*} [Field k] [Infinite k] (φ : k →+* K)
    (F U V : K[X][X]) (h : ℕ) (hU : U.natDegree ≤ h) (hV : V.natDegree ≤ h)
    (hR : F.resultant V 3 h ≠ 0) (a b : K → Fin 3 → K⟦X⟧) (H : NormCharts F a b)
    (s : Finset K) (except : Finset k) :
    ∃ c ∉ except, let R := F.resultant (polar U V (φ c)) 3 h
      R ≠ 0 ∧ ∀ α ∈ s, 6 • (R.rootMultiplicity α : ℕ∞) =
        ∑ i, min (sheetValue α U h (b α i) (a α i)).order
          (sheetValue α V h (b α i) (a α i)).order := by
  classical
  let S := insert 0 s
  let W (G : K[X][X]) (z : S × Fin 3) := sheetValue z.1.val G h (b z.1 z.2) (a z.1 z.2)
  have hv (z : S × Fin 3) : W V z ≠ 0 :=
    sheet_nonzero _ hR z.1 _ (H z.1 V h hV) z.2
  obtain ⟨c,hc,hgood⟩ := exists_generic_polar_in φ (W U) (W V) (fun z => Or.inr (hv z)) except
  let P := polar U V (φ c)
  let R := F.resultant P 3 h
  have hP : P.natDegree ≤ h := polar_degree U V _ h hU hV
  have localgood (α : K) (hα : α ∈ S) (i : Fin 3) :
      sheetValue α P h (b α i) (a α i) ≠ 0 ∧
      (sheetValue α P h (b α i) (a α i)).order =
      min (sheetValue α U h (b α i) (a α i)).order (sheetValue α V h (b α i) (a α i)).order := by
    rw [show P = _ from rfl, sheetValue_polar]
    exact hgood (⟨α,hα⟩,i)
  have hre : R ≠ 0 := by
    intro h0
    have h0' : F.resultant P 3 h=0 := h0
    have hsum := H 0 P h hP
    rw [h0', map_zero, PowerSeries.order_zero] at hsum
    have hfin : (∑ i, (sheetValue 0 P h (b 0 i) (a 0 i)).order) ≠ ⊤ :=
      ENat.sum_ne_top.mpr (fun i _ => PowerSeries.order_eq_top.not.mpr
        (localgood 0 (mem_insert_self 0 s) i).1)
    exact hfin (by simpa using hsum.symm)
  refine ⟨c,hc,hre,fun α hα => ?_⟩
  have hh := H α P h hP
  rw [local_order α R hre] at hh
  exact hh.trans (sum_congr rfl (fun i _ => (localgood α (mem_insert_of_mem hα) i).2))

/-- The requested degree charge is valid for every common divisor. This
also allows a common divisor transported from the smaller coefficient field. -/
theorem common_degree_charge [IsSepClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (A B D : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hp : A.natDegree < p)
    (hDA : D ∣ A) (hDB : D ∣ B) (ν : K → ℕ∞)
    (hν : ∀ α ∈ A.roots.toFinset, 6 • (B.rootMultiplicity α : ℕ∞) = ν α) :
    6 • (D.natDegree : ℕ∞) ≤ ∑ α ∈ A.roots.toFinset, ν α := by
  classical
  have hD := ne_zero_of_dvd_ne_zero hA hDA
  have hsplit := splits_of_degree_lt_characteristic p D ((natDegree_le_of_dvd hDA hA).trans_lt hp)
  have hs (α : K) (hα : α ∈ D.roots) : α ∈ A.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hA).mpr (Polynomial.dvd_iff_isRoot.mp
      ((Polynomial.dvd_iff_isRoot.mpr ((mem_roots hD).mp hα)).trans hDA)))
  have Hsum : ∑ α ∈ A.roots.toFinset, D.rootMultiplicity α = D.natDegree := by
    simpa only [← Polynomial.count_roots, ← splits_iff_card_roots.mp hsplit]
      using (Multiset.sum_count_eq_card hs)
  have HL (α : K) : D.rootMultiplicity α ≤ B.rootMultiplicity α :=
    (le_rootMultiplicity_iff hB).mpr ((pow_rootMultiplicity_dvd D α).trans hDB)
  calc
    _ = ∑ α ∈ A.roots.toFinset, 6 • (D.rootMultiplicity α : ℕ∞) := by
      rw [← Finset.smul_sum, ← Nat.cast_sum, Hsum]
    _ ≤ ∑ α ∈ A.roots.toFinset, 6 • (B.rootMultiplicity α : ℕ∞) := by
      apply sum_le_sum
      intro α _
      exact nsmul_le_nsmul_right (by exact_mod_cast HL α) 6
    _ = _ := sum_congr rfl hν

/-- Two ordinary first polars account for the degree of their actual gcd
on precisely the finite root set of the first resultant. -/
theorem generic_gcd_charge [IsSepClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    {k : Type*} [Field k] [Infinite k] (φ : k →+* K) (A : K[X]) (hA : A ≠ 0)
    (hp : A.natDegree < p) (F U V : K[X][X]) (h : ℕ)
    (hU : U.natDegree ≤ h) (hV : V.natDegree ≤ h) (hR : F.resultant V 3 h ≠ 0)
    (a b : K → Fin 3 → K⟦X⟧) (H : NormCharts F a b) (except : Finset k) :
    ∃ c ∉ except, let B := F.resultant (polar U V (φ c)) 3 h
      B ≠ 0 ∧ 6 • ((GCDMonoid.gcd A B).natDegree : ℕ∞) ≤
        ∑ α ∈ A.roots.toFinset, ∑ i, min (sheetValue α U h (b α i) (a α i)).order
          (sheetValue α V h (b α i) (a α i)).order := by
  obtain ⟨c,hc,hB,hν⟩ := generic_second_polar φ F U V h hU hV hR a b H A.roots.toFinset except
  exact ⟨c,hc,hB,common_degree_charge p A _ _ hA hB hp (gcd_dvd_left ..) (gcd_dvd_right ..) _ hν⟩

/-- The same cubic sheets exist simultaneously at all coordinates, and
they satisfy the norm identity also for test forms with identically zero
resultant. Their unimodularity and the original factorization are retained. -/
theorem primitive_norm_charts [IsSepClosed K] [Infinite K] (F : K[X][X]) (hF : F.natDegree=3)
    (hprim : F.IsPrimitive) (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0) :
    ∃ (c : K → K) (u : K → K⟦X⟧) (y : K → Fin 3 → K⟦X⟧),
      let a := fun α i => -y α i
      let b := fun α i => -(1+PowerSeries.C (c α)*y α i)
      NormCharts F a b ∧ ∀ α, IsUnit (u α) ∧ (∀ i, y α i ≠ 0) ∧
        (∀ i, IsCoprime (b α i) (a α i)) ∧
        (F.map (atPoint α)).map (PowerSeries.expand 6 (by decide) (R := K)).toRingHom =
          C (u α)*∏ i, (C (a α i)*X-C (b α i)) := by
  classical
  have H (α : K) := projective_resultant_orders (F.map (atPoint α))
    ((natDegree_map_eq_of_injective (atPoint_injective α) F).trans hF)
    (by rw [Polynomial.map_map]; exact primitive_map_ne_zero F hprim _) h₂ h₃
  choose c u y hu hy hco hf hn using H
  refine ⟨c,u,y,?_,fun α => ⟨hu α,hy α,hco α,hf α⟩⟩
  intro α G h hG
  have H' := hn α (G.map (atPoint α)) h (natDegree_map_le.trans hG)
  rw [resultant_map_map] at H'
  exact H'

#print axioms primitive_norm_charts
#print axioms generic_gcd_charge
#print axioms generic_second_polar

end ArkLib.ProximityGap.Frontier.GenericProjectivePolarGcd
