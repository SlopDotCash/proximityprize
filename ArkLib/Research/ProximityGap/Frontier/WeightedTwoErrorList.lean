/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListThreshold

/-! # List bounds at arbitrary length from a weighted two-error penalty cap -/

namespace ProximityGap.TwoErrorSlice

open Finset Polynomial Code ReflectionListSampling

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- Every charge at a nonzero extension-field scale comes from a base-field
scale. Thus the penalty cap is unchanged by scalar extension. -/
theorem PenaltyCap.map {K : Type*} [Field K] (D : I ↪ F) {S : ℕ} (cap : PenaltyCap D S)
    (φ : F →+* K) : PenaltyCap (D.trans ⟨φ,φ.injective⟩) S := by
  classical
  let E := D.trans (⟨φ,φ.injective⟩ : F ↪ K)
  have rat (u v x) : ratio E u v x=φ (ratio D u v x) := by simp [ratio,E]
  intro u v ne anti μ nz
  let U := (univ.erase u).erase v
  change (∑ x∈U,penalty (alternatives E u v (μ/ratio E u v x)).card) ≤ S
  by_cases rep : ∃ t,φ t=μ
  · obtain ⟨t,rfl⟩ := rep
    have equal (x) : alternatives E u v (φ t/ratio E u v x)=alternatives D u v (t/ratio D u v x) := by
      ext A
      simp only [mem_alternatives_iff,rat,←map_prod,←map_div₀,φ.injective.eq_iff]
    simp only [equal]
    apply cap u v ne _ t (fun h => nz (h ▸ map_zero φ))
    intro h
    apply anti
    change φ (D u) = -φ (D v)
    rw [h,map_neg]
  · have empty (x) (hx : x∈U) : alternatives E u v (μ/ratio E u v x)=∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨A,ha⟩
      obtain ⟨hxv,hxu⟩ := mem_erase.mp hx
      have rx := ratio_ne_zero D (mem_erase.mp hxu).1.symm hxv.symm
      have he := (mem_alternatives_iff.mp ha).2
      simp only [rat,←map_prod] at he
      apply rep
      exact ⟨(∏ i∈A,ratio D u v i)*ratio D u v x,
        (map_mul φ ..).trans ((eq_div_iff (fun h => rx (φ.injective (h.trans (map_zero φ).symm)))).mp he)⟩
    rw [sum_eq_zero (fun x hx => by simp [empty x hx,penalty])]
    exact Nat.zero_le _

/-- The bound for k+2 agreements using six units per puncture and a loss of
at most S from the 3(k+2) units available when varying the last correct site. -/
def weighted_bound (k r S : ℕ) : ℕ :=
  max 1 ((k+3+r).choose r*6/(((r+1).choose 2-(r+1)/2)*(3*(k+2)-S)))

/-- Arbitrary scalar centers through r+1 errors, with the same integer
endpoint condition used by the nonreflection transposition estimate. -/
theorem weighted_scalar (D : I ↪ F) {k r S : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r)
    (hr : 2≤r) (positive : S<3*(k+2))
    (payment : RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)))
    (cap : PenaltyCap D S) (δ : ℝ) (safe : δ*(Fintype.card I : ℝ)<r+2) :
    Lambda (ReedSolomon.code D k : Set (I → F)) δ ≤ (weighted_bound k r S : ℕ∞) := by
  let M (e : ℕ) := e.choose 2-e/2
  let C := 3*(k+2)-S
  have pos : 0<C := Nat.sub_pos_of_lt positive
  have pairs : r≤(r+1).choose 2 := by rw [Nat.choose_succ_succ' r 1,Nat.choose_one_right]; omega
  have mp : 0<M (r+1) := by dsimp [M]; omega
  apply scalar_of_sample_weights D hn (Nat.mul_pos mp pos)
    (fun u v t => 3-penalty (alternatives D u v t).card) (C:=C) _ _ _ δ safe
  · intro e lo hi
    have base := payment e lo hi
    have floor : M (r+1)*(k+2) ≤ M e*((k+3+r-e).choose (r+2-e)) := by
      apply Nat.le_of_mul_le_mul_right (c:=k+1) _ (by omega)
      simpa only [M,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using base
    simpa only [M,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_right C floor
  · intro E A Q err nz ca sub clean hQ room
    exact last_site_general D cap E A Q err nz ca sub clean hQ room
  · intro W V P inj E agree deg R room
    exact column_general D P inj W univ E (fun i _ => agree i) (fun i _ => deg i) R room

/-- The weighted upper bound holds at every interleaving width without
a relation between the list size and the cardinality of the field. -/
theorem weighted_interleaved (D : I ↪ F) {k r S : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r)
    (hr : 2≤r) (positive : S<3*(k+2))
    (payment : RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)))
    (cap : PenaltyCap D S) (m : ℕ) (δ : ℝ) (safe : δ*(Fintype.card I : ℝ)<r+2) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (weighted_bound k r S : ℕ∞) :=
  (ReedSolomon.Lambda_interleaved_le_ratFunc D k m δ).trans
    (weighted_scalar _ hn hr positive payment (cap.map D (algebraMap F (RatFunc F))) δ safe)

/-- Exact list threshold at n-k-1 errors whenever the weighted estimate through
n-k-2 errors and the smooth common-product witness straddle the budget. -/
theorem weighted_threshold {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] {k r S B : ℕ} [NeZero k]
    (hn : Fintype.card I=k+3+r) (hr : 2≤r) (positive : S<3*(k+2))
    (payment : RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)))
    (cap : PenaltyCap D S) (upper : weighted_bound k r S≤B)
    (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (B : ℕ∞) ↔ δ<((r+2 : ℕ):ℝ)/(Fintype.card I : ℝ) := by
  refine ⟨strict_radius_of_product D hn lower m hm δ,fun h => ?_⟩
  have npos : (0:ℝ)<Fintype.card I := by exact_mod_cast (hn ▸ (by omega : 0<k+3+r))
  apply (weighted_interleaved D hn hr positive payment cap m δ
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using (lt_div_iff₀ npos).mp h)).trans
  exact_mod_cast upper

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.weighted_threshold
