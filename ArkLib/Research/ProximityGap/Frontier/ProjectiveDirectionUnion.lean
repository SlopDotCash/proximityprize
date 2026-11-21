/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDirectionRigidity

/-! # Finite families of primitive nonlinear directions

When the allowed directions share the same affine head, the zero residual
charges only once. For all other challenges we assign a single witnessing
direction and sum the pair incidence inequalities before rounding.
-/

set_option autoImplicit false

namespace ProximityGap.ProjectiveDirectionUnion
open Finset Polynomial ProjectiveDirectionIncidence ProjectiveDirectionRigidity
open Classical

/-- Bound the union over any finite set of primitive nonlinear directions.
The estimate counts each challenge once even if it has several witnesses. -/
theorem bad_count {I F T : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]
    [Fintype F] [DecidableEq T] (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X])
    (dirs : Finset T) (U : T → (F[X])[X]) (s : T → ℕ) {D A : ℕ}
    (hDA : D < A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hD : ∀ t ∈ dirs, (U t).natDegree ≤ D) (hprim : ∀ t ∈ dirs, (U t).IsPrimitive)
    (hnl : ∀ t ∈ dirs, ∃ j, 2 ≤ ((U t).coeff j).natDegree)
    (height : ∀ t ∈ dirs, ∀ j, ((U t).coeff j).natDegree ≤ s t) :
    ((univ : Finset F).filter fun z => ∃ t ∈ dirs, ∃ (S : Finset I) (P : F[X]) (a : F),
      A ≤ S.card ∧ P.natDegree ≤ D ∧ (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ ∧
      ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*((U t).eval (C (dom i))).eval z).card ≤
      Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(∑ t ∈ dirs, (s t+1))/(A-D)^2 := by
  classical
  let w := residualRow dom u₀ u₁ q₀ q₁
  let V (t : T) (i : I) := (U t).eval (C (dom i))
  let B := (univ : Finset F).filter fun z => ∃ t ∈ dirs, ∃ (S : Finset I) (P : F[X]) (a : F),
      A ≤ S.card ∧ P.natDegree ≤ D ∧ (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ ∧
      ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*(V t i).eval z
  change B.card ≤ _
  by_cases hempty : IsEmpty T
  · have : B = ∅ := eq_empty_iff_forall_notMem.mpr fun z hz =>
      hempty.false (mem_filter.mp hz).2.choose
    simp [this]
  have := not_isEmpty_iff.mp hempty
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have wit (z : F) (hz : z ∈ B) : ∃ t ∈ dirs, ∃ (S : Finset I) (a : F), A ≤ S.card ∧
      (∀ i ∈ S, (w i).eval z = a*(V t i).eval z) ∧
      (a ≠ 0 → A-D ≤ (S.filter fun i => (w i).eval z ≠ 0).card) ∧ ∃ i ∈ S, w i ≠ 0 := by
    obtain ⟨t,ht,hit⟩ := (mem_filter.mp hz).2
    exact ⟨t,ht,prepare_witness dom u₀ u₁ q₀ q₁ (V t) hq₀ hq₁ hit⟩
  choose! t ht S a hs hf ha hind using wit
  let Z := B.filter fun z => a z = 0
  let R := B.filter fun z => a z ≠ 0
  have zero := ShiftedPowerCurveCount.zero_count w hw Z S A
    (fun z hz => hs z (mem_filter.mp hz).1)
    (fun z hz i hi => by rw [hf z (mem_filter.mp hz).1 i hi,(mem_filter.mp hz).2,zero_mul])
    (fun z hz => hind z (mem_filter.mp hz).1)
  let fiber (j : T) := R.filter fun z => t z = j
  have bound (j : T) (hj : j ∈ dirs) :
      (fiber j).card * (A-D)^2 ≤ Fintype.card I*(Fintype.card I-1)*(s j+1) := by
    have info {z : F} (hz : z ∈ fiber j) : z ∈ B ∧ a z ≠ 0 ∧ t z = j := by
      have h := mem_filter.mp hz
      exact ⟨(mem_filter.mp h.1).1,(mem_filter.mp h.1).2,h.2⟩
    have fit (z : F) (hz : z ∈ fiber j) (i : I) (hi : i ∈ S z) :
        (w i).eval z = a z*(V j i).eval z := by
      simpa only [(info hz).2.2] using hf z (info hz).1 i hi
    obtain ⟨l,hl⟩ := hnl j hj
    apply nonzero_count w (V j) (fiber j) S a D A (s j) hw
      (fun i => site_height (U j) (s j) (height j hj) (dom i))
      (fun z hz => hs z (info hz).1) fit (fun z hz => ha z (info hz).1 (info hz).2.1)
    intro z hz i hi hn
    apply class_card_le_of_primitive dom (U j) (hD j hj) (hprim j hj) hl w hw i
    · intro he
      rw [he,eval_zero] at hn
      exact hn rfl
    · intro he
      have hh := fit z hz i hi
      change V j i = 0 at he
      rw [he,eval_zero,mul_zero] at hh
      exact hn hh
  have partition : R.card = ∑ j ∈ dirs, (fiber j).card :=
    card_eq_sum_card_fiberwise (fun z hz => ht z (mem_filter.mp hz).1)
  have full : R.card*(A-D)^2 ≤ Fintype.card I*(Fintype.card I-1)*(∑ j ∈ dirs, (s j+1)) := by
    rw [partition,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_le_sum bound
  have nonzero := (Nat.le_div_iff_mul_le (pow_pos (Nat.sub_pos_of_lt hDA) 2)).mpr full
  have both : Z.card+R.card = B.card := card_filter_add_card_filter_not ..
  omega

/-- Maximum numbers of quadratic directions allowed by this estimate at the
four fixed agreement counts. The second entry uses the budget twice the length. -/
theorem quadratic_direction_budgets :
    let n : ℕ := 2^30
    let cut := fun (k A b h : ℕ) =>
      let cost := fun t => n-A+1+n*(n-1)*(3*t)/(A-(k-1))^2
      cost h ≤ b ∧ b < cost (h+1)
    (cut (2^29) (89*2^23) n 9493333 ∧ cut (2^29) (89*2^23) (2*n) 23146666) ∧
    (cut (2^28) (61*2^23) n 8755370 ∧ cut (2^28) (61*2^23) (2*n) 27127296) ∧
    (cut (2^27) (42*2^23) n 4845568 ∧ cut (2^27) (42*2^23) (2*n) 19613013) ∧
    (cut (2^26) (29*2^23) n 2182656 ∧ cut (2^26) (29*2^23) (2*n) 11816448) := by
  decide

end ProximityGap.ProjectiveDirectionUnion

#print axioms ProximityGap.ProjectiveDirectionUnion.bad_count

#print axioms ProximityGap.ProjectiveDirectionUnion.quadratic_direction_budgets
