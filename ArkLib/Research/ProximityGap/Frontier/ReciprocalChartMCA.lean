/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarCoordinateTransport
import ArkLib.Research.ProximityGap.Frontier.ReciprocalSubsetSeparation
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDirectionIncidence

/-! # Reciprocal charts preserve the exact line-MCA event

Transport from x to y=1/(t-x) multiplies each word coordinate by y^D
at degree cap D. This preserves the support of every codeword agreement
and leaves the challenge unchanged.
-/
set_option autoImplicit false

namespace ProximityGap.ReciprocalChartMCA
open Polynomial Finset ApolarCoordinateTransport
variable {I F : Type} [Field F]

/-- Evaluation after moving the pole to infinity. -/
def chart (x : I ↪ F) (t : F) : I ↪ F where
  toFun i := (t-x i)⁻¹
  inj' _ _ h := x.injective (sub_right_inj.mp (inv_injective h))

private def fits (x : I ↪ F) (D : ℕ) (S : Finset I) (u : I → F) : Prop :=
  ∃ P : F[X], P.natDegree ≤ D ∧ ∀ i ∈ S, P.eval (x i) = u i

private theorem fits_iff (x : I ↪ F) (t : F) (free : ∀ i, t ≠ x i) (D : ℕ)
    (S : Finset I) (u : I → F) :
    fits x D S u ↔ fits (chart x t) D S (fun i => (chart x t i)^D*u i) := by
  have yne (i : I) : chart x t i ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (free i))
  have d (i : I) : t-x i ≠ 0 := sub_ne_zero.mpr (free i)
  constructor
  · rintro ⟨P,hP,hit⟩
    let N : F[X] := C t*X-1
    have hN : N.natDegree ≤ 1 := (natDegree_sub_le ..).trans (max_le
      ((natDegree_C_mul_le ..).trans (by simp)) (by simp))
    refine ⟨substitute D N X P,substitute_degree N X P hN (by simp) hP,?_⟩
    intro i hi
    have hn : N.eval (chart x t i) / (chart x t i) = x i := by
      simp only [N,eval_sub,eval_mul,eval_C,eval_X,eval_one]
      change (t*(t-x i)⁻¹-1)/(t-x i)⁻¹ = x i
      field_simp [d i]
      ring
    rw [eval_substitute N X P hP _ (by simpa using yne i),eval_X,hn,hit i hi,mul_comm]
  · rintro ⟨Q,hQ,hit⟩
    let L : F[X] := C t-X
    have hL : L.natDegree ≤ 1 := (natDegree_sub_le ..).trans (by simp)
    refine ⟨substitute D 1 L Q,substitute_degree 1 L Q (by simp) hL hQ,?_⟩
    intro i hi
    have hd : L.eval (x i) ≠ 0 := by simpa [L] using d i
    rw [eval_substitute 1 L Q hQ _ hd]
    have he : (1 : F[X]).eval (x i) / L.eval (x i) = chart x t i := by
      change (1 : F[X]).eval (x i) / L.eval (x i) = (t-x i)⁻¹
      simp [L]
    rw [he,hit i hi]
    change ((t-x i)⁻¹ ^ D * u i) * L.eval (x i)^D = u i
    simp [L,inv_pow, mul_right_comm _ (u i),pow_ne_zero D (d i)]

private theorem fits_code [Fintype I] [DecidableEq I] [DecidableEq F]
    (x : I ↪ F) (D : ℕ) (S : Finset I) (u : I → F) :
    (∃ w ∈ (ReedSolomon.code x (D+1) : Set (I → F)), ∀ i ∈ S, w i = u i) ↔ fits x D S u := by
  constructor
  · rintro ⟨w,hw,h⟩
    obtain ⟨P,hP,he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    exact ⟨P,by omega,fun i hi => (he i).trans (h i hi)⟩
  · rintro ⟨P,hP,h⟩
    exact ⟨ReedSolomon.evalOnPoints x P,
      ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),h⟩

private theorem joint_iff [Fintype I] [DecidableEq I] [DecidableEq F] (x : I ↪ F) (D : ℕ)
    (S : Finset I) (u v : I → F) :
    pairJointAgreesOn (ReedSolomon.code x (D+1) : Set (I → F)) S u v ↔
      fits x D S u ∧ fits x D S v := by
  rw [← fits_code,← fits_code]
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    exact ⟨⟨a,ha,fun i hi => (h i hi).1⟩,⟨b,hb,fun i hi => (h i hi).2⟩⟩
  · rintro ⟨⟨a,ha,h⟩,⟨b,hb,h'⟩⟩
    exact ⟨a,ha,b,hb,fun i hi => ⟨h i hi,h' i hi⟩⟩

/-- The same challenge and the same support witness the two scalar MCA events. -/
theorem event_iff [Fintype I] [DecidableEq I] [Fintype F] [DecidableEq F]
    (x : I ↪ F) (t : F) (free : ∀ i, t ≠ x i) (D : ℕ)
    (δ : NNReal) (u v : I → F) (z : F) :
    mcaEvent (F:=F) (ReedSolomon.code x (D+1) : Set (I → F)) δ u v z ↔
    mcaEvent (F:=F) (ReedSolomon.code (chart x t) (D+1) : Set (I → F)) δ
      (fun i => (chart x t i)^D*u i) (fun i => (chart x t i)^D*v i) z := by
  unfold mcaEvent
  apply exists_congr
  intro S
  apply and_congr_right
  intro _
  simp only [joint_iff,fits_code,smul_eq_mul]
  have eq : (fun i => (chart x t i)^D*(u i+z*v i)) =
      (fun i => (chart x t i)^D*u i+z*((chart x t i)^D*v i)) := by funext i; ring
  rw [fits_iff x t free D S (fun i => u i+z*v i),eq,
    fits_iff x t free D S u,fits_iff x t free D S v]

/-- A single chart separates support fingerprints at order r and preserves every bad challenge
at every radius, for every received pair and every positive code dimension. -/
theorem exists_separating_chart [Fintype I] [DecidableEq I] [Fintype F] [DecidableEq F]
    (x : I ↪ F) (r : ℕ)
    (size : Fintype.card I + (Fintype.card I).choose r ^ 2 * (2*r) < Fintype.card F) :
    ∃ t : F, (∀ i, t ≠ x i) ∧ Set.InjOn
      (fun S : Finset I => ∑ i ∈ S, chart x t i) ((univ : Finset I).powersetCard r : Set (Finset I)) ∧
      ∀ (D : ℕ) (δ : NNReal) (u v : I → F) (z : F),
        mcaEvent (F:=F) (ReedSolomon.code x (D+1) : Set (I → F)) δ u v z ↔
        mcaEvent (F:=F) (ReedSolomon.code (chart x t) (D+1) : Set (I → F)) δ
          (fun i => (chart x t i)^D*u i) (fun i => (chart x t i)^D*v i) z := by
  obtain ⟨t,ht,he⟩ := ReciprocalSubsetSeparation.exists_chart x r size
  exact ⟨t,ht,he,event_iff x t ht⟩

end ProximityGap.ReciprocalChartMCA
#print axioms ProximityGap.ReciprocalChartMCA.event_iff
#print axioms ProximityGap.ReciprocalChartMCA.exists_separating_chart
