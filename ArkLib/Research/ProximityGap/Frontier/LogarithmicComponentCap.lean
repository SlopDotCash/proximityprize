/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CoordinateChartAndHeightSum
import ArkLib.Research.ProximityGap.Frontier.TangentHeadCount

/-! # Unconditional algebraic logarithmic nonlinear component cap (Packet L1d)

Assembles `CoordinateChartAndHeightSum.coordinate_chart_height_and_loss` (L1c) with
`TangentHeadCount.tangent_head_population_of_loss` to prove the unconditional nonlinear
component label cap `logarithmic_component_cap` matching `logDerivPrice` from
`docs/research/proximity-gap/logarithmic-section-heights.md` and
`TwoSurfaceFactorAccounting.NonlinearComponentCap`.
-/

set_option autoImplicit false
noncomputable section

open Finset Polynomial
open scoped BigOperators
open ArkLib.ProximityGap.Frontier.CoordinateChartAndHeightSum
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree

namespace ArkLib.ProximityGap.Frontier.LogarithmicComponentCap

/-- Exact algebraic nonlinear factor cap from `docs/research/proximity-gap/logarithmic-section-heights.md`. -/
def logDerivPrice (n d t W m b : ℕ) : ℕ :=
  let A := (2 * b - 2) * W - b * (b - 1) * d
  let G := (2 * b - 2) * m - b * (b - 1)
  let C0 := 2 * A * G + 2 * W * m
  G + 2 * b * m + (2 * t * (G + m) * n + n * (2 * C0 + m * n)) / (t ^ 2 - n * d)

/-- Any single affine head `A + z B` contains at most `m` sections of an irreducible nonlinear
surface `F : K[X][X][X]` of total degree `≤ m` and value degree `≥ 2`. -/
theorem card_on_affine_head_le {K : Type} [Field K] [DecidableEq K]
    (F : K[X][X][X]) {m : ℕ}
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree) (hTot : TotalDegreeLe F m)
    (S : Finset K) (q : K → K[X])
    (hF0 : ∀ z ∈ S, (F.map (evalRingHom (C z))).eval (q z) = 0)
    (A B : K[X]) :
    (S.filter fun z => q z = A + C z * B).card ≤ m := by
  let L : K[X][X] := C A + C B * Polynomial.X
  let P : K[X][X] := F.eval L
  have hPne : P ≠ 0 := by
    intro h0
    have hdvd : (Polynomial.X - C L) ∣ F := dvd_iff_isRoot.mpr h0
    obtain ⟨Q, hQ⟩ := hdvd
    have hnu : ¬ IsUnit (Polynomial.X - C L) := fun hu =>
      (by rw [natDegree_X_sub_C]; decide : (Polynomial.X - C L).natDegree ≠ 0)
        (natDegree_eq_zero_of_isUnit hu)
    have hQunit : IsUnit Q := (hFirr.isUnit_or_isUnit hQ).resolve_left hnu
    have hFdeg : F.natDegree = 1 := by
      have hmon : (Polynomial.X - C L).Monic := monic_X_sub_C L
      have hQ0 : Q ≠ 0 := hQunit.ne_zero
      rw [hQ, hmon.natDegree_mul' hQ0, natDegree_X_sub_C, natDegree_eq_zero_of_isUnit hQunit]
    omega
  have hPdeg : P.natDegree ≤ m := by
    dsimp [P]
    rw [eval_eq_sum, sum_def]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have h1 := hTot j (mem_support_iff.mp hj)
    have hLdeg : L.natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_C]; exact Nat.zero_le 1
      · exact natDegree_mul_le.trans (by rw [natDegree_C, natDegree_X])
    have h2 := natDegree_mul_le (p := F.coeff j) (q := L ^ j)
    have h3 : (L ^ j).natDegree ≤ j := by
      simpa using (natDegree_pow_le (p := L) (n := j)).trans (Nat.mul_le_mul_left j hLdeg)
    omega
  have hsub : (S.filter fun z => q z = A + C z * B) ⊆ S.filter fun z => P.eval (C z) = 0 := by
    intro z hz
    obtain ⟨hzS, hqz⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzS, ?_⟩
    have hLeval : L.eval (C z) = q z := by
      rw [hqz]
      simp only [L, eval_add, eval_mul, eval_C, eval_X]
      ring
    dsimp [P]
    have hcomm := Polynomial.hom_eval₂ F (RingHom.id K[X][X]) (evalRingHom (C z)) L
    simp only [eval₂_id, RingHom.comp_id, coe_evalRingHom, hLeval] at hcomm
    have h0 := hF0 z hzS
    rw [eval_map] at h0
    exact hcomm.trans h0
  exact (Finset.card_le_card hsub).trans ((card_eval_C_eq_zero_le P hPne S).trans hPdeg)

/-- **Unconditional Algebraic Logarithmic Nonlinear Component Cap (Packet L1d)**:
matches `TwoSurfaceFactorAccounting.NonlinearComponentCap logDerivPrice` verbatim. -/
theorem logarithmic_component_cap {K I : Type} [Field K] [Infinite K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (dom : I ↪ K) (u₀ u₁ : I → K)
    {d t W m : ℕ} (F : K[X][X][X])
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hTot : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m)
    (hWt : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W)
    (hJ : Fintype.card I * d < t ^ 2)
    (hchar : ∀ r : ℕ, 0 < r →
      r ≤ max ((2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d) F.natDegree →
      (r : K) ≠ 0)
    (S : Finset K) (q : K → K[X])
    (hq : ∀ z ∈ S, (q z).natDegree ≤ d)
    (hF0 : ∀ z ∈ S, F.eval₂ (evalRingHom (C z)) (q z) = 0)
    (hAgree : ∀ z ∈ S, t ≤ (Finset.univ.filter fun x => (q z).eval (dom x) = u₀ x + z * u₁ x).card) :
    S.card ≤ logDerivPrice (Fintype.card I) d t W m F.natDegree := by
  let n := Fintype.card I
  let b := F.natDegree
  let A := (2 * b - 2) * W - b * (b - 1) * d
  let G := (2 * b - 2) * m - b * (b - 1)
  let C0 := 2 * A * G + 2 * W * m
  have hm : 1 ≤ m := by
    have hlc := leadingCoeff_ne_zero.mpr hFirr.ne_zero
    have hlc2 := leadingCoeff_ne_zero.mpr hlc
    have hlc3 := leadingCoeff_ne_zero.mpr hlc2
    have h := hTot b _ _ hlc3
    omega
  obtain ⟨S_ret, dom', u₀', u₁', F', q', s₁, s₂, J', hsub, hdisc, hF'irr, hF'deg, hF'Tot,
      hq'_deg, hF'0, hs₁_ne, hs₂_deg, hne, hV, hR, hheight, hlow⟩ :=
    coordinate_chart_height_and_loss dom u₀ u₁ F hFirr hb hTot hWt hchar S q hq hF0 hAgree
  have hpopR := ProximityGap.TangentHeadCount.tangent_head_population_of_loss
    dom' u₀' u₁' S_ret id q' s₁ s₂ (fun z => (s₁ z).natDegree) J' hm
    (fun _ _ _ _ hne => hne) hq'_deg hs₁_ne (fun _ _ => le_rfl) hs₂_deg hne hV hR
    (fun A_h B_h => by
      simpa only [id_eq] using
        card_on_affine_head_le F' hF'irr (by omega) hF'Tot S_ret q' hF'0 A_h B_h)
    hheight hlow
  have hret_le : S_ret.card ≤ (2 * t * (G + m) * n + n * (2 * C0 + m * n)) / (t ^ 2 - n * d) := by
    have hpos : 0 < t ^ 2 - n * d := Nat.sub_pos_of_lt hJ
    rw [Nat.le_div_iff_mul_le hpos]
    have hcast : ((S_ret.card * (t ^ 2 - n * d) : ℕ) : ℝ) ≤
        ((2 * t * (G + m) * n + n * (2 * C0 + m * n) : ℕ) : ℝ) := by
      have hsub_cast : ((t ^ 2 - n * d : ℕ) : ℝ) = (t : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) := by
        rw [Nat.cast_sub hJ.le, Nat.cast_pow, Nat.cast_mul]
      push_cast
      rw [hsub_cast]
      have hpopR' : (S_ret.card : ℝ) * ((t : ℝ) ^ 2 - (n : ℝ) * (d : ℝ)) ≤
          2 * (t : ℝ) * (((G : ℝ) + (m : ℝ)) * (n : ℝ)) +
            (n : ℝ) * ((m : ℝ) * (n : ℝ) + 2 * (C0 : ℝ)) := by
        change (S_ret.card : ℝ) * ((t : ℝ) ^ 2 - (n : ℝ) * (d : ℝ)) ≤
          2 * (t : ℝ) * (((G + m) * n : ℕ) : ℝ) +
            (n : ℝ) * ((m : ℝ) * (n : ℝ) + 2 * (C0 : ℝ)) at hpopR
        simpa only [Nat.cast_mul, Nat.cast_add] using hpopR
      linarith [hpopR']
    exact_mod_cast hcast
  have hsplit : S.card = (S \ S_ret).card + S_ret.card :=
    (Finset.card_sdiff_add_card_eq_card hsub).symm
  rw [hsplit]
  exact Nat.add_le_add hdisc hret_le

/-- `DecidableEq`-free variant of `logarithmic_component_cap` taking explicit agreement sets `J`. -/
theorem logarithmic_component_cap_exists_set {K I : Type} [Field K] [Infinite K]
    [Fintype I]
    (dom : I ↪ K) (u₀ u₁ : I → K)
    {d t W m : ℕ} (F : K[X][X][X])
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hTot : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m)
    (hWt : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W)
    (hJ : Fintype.card I * d < t ^ 2)
    (hchar : ∀ r : ℕ, 0 < r →
      r ≤ max ((2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d) F.natDegree →
      (r : K) ≠ 0)
    (S : Finset K) (q : K → K[X])
    (hq : ∀ z ∈ S, (q z).natDegree ≤ d)
    (hF0 : ∀ z ∈ S, F.eval₂ (evalRingHom (C z)) (q z) = 0)
    (hAgree : ∀ z ∈ S, ∃ J : Finset I, t ≤ J.card ∧
      ∀ x ∈ J, (q z).eval (dom x) = u₀ x + z * u₁ x) :
    S.card ≤ logDerivPrice (Fintype.card I) d t W m F.natDegree := by
  classical
  refine logarithmic_component_cap dom u₀ u₁ F hFirr hb hTot hWt hJ hchar S q hq hF0 ?_
  intro z hz
  obtain ⟨J, hJt, hJeq⟩ := hAgree z hz
  refine hJt.trans (Finset.card_le_card ?_)
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hJeq x hx⟩

#print axioms card_on_affine_head_le
#print axioms logarithmic_component_cap
#print axioms logarithmic_component_cap_exists_set

end ArkLib.ProximityGap.Frontier.LogarithmicComponentCap
