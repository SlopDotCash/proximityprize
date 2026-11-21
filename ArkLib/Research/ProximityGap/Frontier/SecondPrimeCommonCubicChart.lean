/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CommonSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSelectedSectionChart

/-! # A single integral coordinate chart for the simple cubic sections

The chart acts on each value coefficient in the coordinate variable before
specializing the scalar. Thus the exact ordinate derivative degrees in all simple
fibers belong to one integral trivariate cubic.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCommonCubicChart
open Polynomial Finset
open _root_.ProximityGap.CommonSectionChart

variable {K : Type} [Field K]

/-- Cleared coordinate change on the j-th value coefficient. The input order of
variables is K[Z][X][Y]. -/
noncomputable def chart {R : Type*} [CommRing R] (r : R) (W d : ℕ) (F : R[X][X]) : R[X][X] :=
  ∑ j ∈ range 4, monomial j (((F.coeff j).taylor r).reflect (W-j*d))

theorem coeff_chart {R : Type*} [CommRing R] (r : R) (W d : ℕ) (F : R[X][X]) (j : ℕ) :
    (chart r W d F).coeff j = if j < 4 then ((F.coeff j).taylor r).reflect (W-j*d) else 0 := by
  classical
  simp [chart, finset_sum_coeff, coeff_monomial]

theorem degree_chart {R : Type*} [CommRing R] (r : R) (W d : ℕ) (F : R[X][X]) :
    (chart r W d F).natDegree ≤ 3 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp [coeff_chart, show ¬j < 4 by omega]

/-- Coefficientwise ring maps commute with the entire cleared cubic chart. -/
theorem map_chart {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (W d : ℕ) (F : R[X][X]) :
    (chart r W d F).map (mapRingHom φ) = chart (φ r) W d (F.map (mapRingHom φ)) := by
  ext j : 1
  simp only [coeff_chart, coeff_map, coe_mapRingHom]
  split <;> simp only [← reflect_map, map_taylor, Polynomial.map_zero]

private theorem values (r : K) (v d : ℕ) (F : K[X][X]) (q : K[X]) :
    let F' := chart r (v+d+d+d) d F
    F'.eval q = cubic (change r (v+d+d+d) (F.coeff 0)) (change r (v+d+d) (F.coeff 1))
      (change r (v+d) (F.coeff 2)) (change r v (F.coeff 3)) q ∧
    F'.derivative.eval q = residual (change r (v+d+d) (F.coeff 1))
      (change r (v+d) (F.coeff 2)) (change r v (F.coeff 3)) q := by
  have h := section_values (chart r (v+d+d+d) d F) (degree_chart _ _ _ _) q
  simpa only [coeff_chart, if_pos (by decide : 0 < 4), if_pos (by decide : 1 < 4),
    if_pos (by decide : 2 < 4), if_pos (by decide : 3 < 4), Nat.zero_mul, Nat.sub_zero,
    Nat.one_mul, Nat.add_sub_cancel, show v+d+d+d-2*d = v+d by omega,
    show v+d+d+d-3*d = v by omega, change] using h

/-- Simultaneously transport simple roots of one integral surface. The choices may
avoid any finite set of base points and polynomial tests in a coefficient extension. -/
theorem simple_sections [Infinite K] (F : K[X][X][X]) (v d : ℕ)
    (hf : F.natDegree ≤ 3)
    (hw : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree + j*d ≤ v+d+d+d)
    (L : Finset K) (q : K → K[X]) (hq : ∀ z ∈ L, (q z).natDegree ≤ d)
    (hr : ∀ z ∈ L, (F.map (mapRingHom (evalRingHom z))).eval (q z) = 0)
    (hs : ∀ z ∈ L, (F.map (mapRingHom (evalRingHom z))).derivative.eval (q z) ≠ 0)
    (D : Finset K) {E : Type*} [Field E] (ψ : K →+* E) (tests : Finset E[X])
    (ht : ∀ p ∈ tests, p ≠ 0) :
    ∃ r : K, r ∉ D ∧ (∀ p ∈ tests, p.eval (ψ r) ≠ 0) ∧
      Function.Injective (fun x : K => (x-r)⁻¹) ∧ ∀ z ∈ L,
        let F' := (chart (C r) (v+d+d+d) d F).map (mapRingHom (evalRingHom z))
        let q' := change r d (q z)
        F'.eval q' = 0 ∧ (F'.derivative.eval q').natDegree = v+d+d := by
  let fiber (z : K) := F.map (mapRingHom (evalRingHom z))
  have hbd (z : K) (j : ℕ) (hjd : j*d ≤ v+d+d+d) :
      ((fiber z).coeff j).natDegree + j*d ≤ v+d+d+d := by
    simp only [fiber, coeff_map, coe_mapRingHom]
    by_cases h : F.coeff j = 0
    · simpa [h] using hjd
    exact (Nat.add_le_add_right natDegree_map_le _).trans (hw j h)
  obtain ⟨r, hD, htests, hinj, h⟩ := simple_fibers L D ψ tests ht fiber q v d
    (fun _ _ => natDegree_map_le.trans hf)
    (fun z _ => by have := hbd z 1 (by omega); omega)
    (fun z _ => by have := hbd z 2 (by omega); omega)
    (fun z _ => by have := hbd z 3 (by omega); omega) hq hr hs
  refine ⟨r, hD, htests, hinj, fun z hz => ?_⟩
  dsimp only
  rw [map_chart]
  simp only [coe_evalRingHom, eval_C]
  obtain ⟨h0, hdeg⟩ := h z hz
  have he := values r v d (fiber z) (change r d (q z))
  exact ⟨he.1.trans h0, (congrArg natDegree he.2).trans hdeg⟩

#print axioms simple_sections
end ArkLib.ProximityGap.Frontier.SecondPrimeCommonCubicChart
