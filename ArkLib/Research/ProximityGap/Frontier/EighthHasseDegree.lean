/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthRichHeadSafety

/-! # Minimum mixed-Hasse value degree at five eighths -/
namespace ArkLib.ProximityGap.Frontier.EighthHasseDegree

open Finset Polynomial
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
set_option autoImplicit false

private abbrev n : ℕ := 1073741824
private abbrev t : ℕ := 402653184
private abbrev d : ℕ := 134217727

/-- Monomials minus jet equations in a scalar column whose highest value
degree is `h`. Derivatives above `h` make no contribution to this estimate. -/
def slice (r h : ℕ) : ℤ :=
  ∑ j ∈ range (h+1), (((r*t-j*d : ℕ) : ℤ) - ((n*(r-j) : ℕ) : ℤ))

/-- Sum the column balances up to the total-degree cap. Jet orders larger
than the value-degree cap are omitted. When `r ≤ v+1`, this gives the exact surplus. -/
def score (r v l : ℕ) : ℤ := ∑ h ∈ range (l+1), slice r (min v h)

private theorem slice_filter (r v h : ℕ) :
    slice r (min v h) = ∑ j ∈ range (v+1), if j≤h then
      (((r*t-j*d : ℕ) : ℤ) - ((n*(r-j) : ℕ) : ℤ)) else 0 := by
  rw [← sum_filter]
  have eq : (range (v+1)).filter (fun j => j≤h) = range (min v h+1) := by
    ext j
    simp only [mem_filter,mem_range]
    omega
  rw [eq]
  rfl

/-- The scalar-column count equals the usual weighted value-degree sum. -/
theorem score_eq (r v l : ℕ) :
    score r v l = ∑ j ∈ range (v+1), ((l+1-j : ℕ) : ℤ) *
      (((r*t-j*d : ℕ) : ℤ) - ((n*(r-j) : ℕ) : ℤ)) := by
  unfold score
  simp_rw [slice_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter,sum_const]
  have interval : (range (l+1)).filter (fun h => j≤h) = Ico j (l+1) := by
    ext h
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [interval,Nat.card_Ico,nsmul_eq_mul]

private def equations (r l j : ℕ) : ℤ :=
  (n : ℤ)*(((r-j : ℕ) : ℤ)*((l+1-j : ℕ) : ℤ))

private theorem matrix_difference (r v l : ℕ) :
    score r v l - ((Fintype.card (Monomials l v d (r*t)) : ℤ) -
      (n*Fintype.card (JetRows l r) : ℕ)) =
      (∑ j ∈ range r, equations r l j) - ∑ j ∈ range (v+1), equations r l j := by
  rw [score_eq]
  simp only [Monomials, JetRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    mul_sub, sum_sub_distrib, Nat.cast_mul, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((l+1-j : ℕ) : ℤ)*((r*t-j*d : ℕ) : ℤ)) (v+1),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => ((r-j : ℕ) : ℤ)*((l+1-j : ℕ) : ℤ)) r,
    Finset.mul_sum]
  have reorder (j : ℕ) : ((l+1-j : ℕ) : ℤ)*((n : ℤ)*((r-j : ℕ) : ℤ)) =
      equations r l j := by unfold equations; ring
  simp_rw [reorder]
  unfold equations
  ring

private theorem all_orders (r v l : ℕ) (hv : r≤v+1) :
    ∑ j ∈ range r, equations r l j = ∑ j ∈ range (v+1), equations r l j := by
  apply sum_subset (range_mono hv)
  intro i _ hi
  have h : r-i=0 := by have hh := mt mem_range.mpr hi; omega
  simp [equations,h]

private theorem tail (r v h : ℕ) (hv : v≤16) :
    score r v (16+h) = score r v 16 + (h : ℤ)*slice r v := by
  induction h with
  | zero => simp
  | succ h ih =>
    change score r v ((16+h)+1) = _
    rw [show score r v ((16+h)+1) = score r v (16+h) + slice r (min v ((16+h)+1)) from
      sum_range_succ .., ih, min_eq_left (by omega)]
    push_cast
    ring

private theorem positive_slice {r h : ℕ} (hr : 0<r) (hh : h≤16) (hp : 0<slice r h) :
    (r=5 ∧ 14≤h) ∨ (r=6 ∧ 15≤h) := by
  by_cases high : 23≤r
  · have nonpos : slice r h ≤ 0 := by
      apply sum_nonpos
      intro j hj
      have small : j≤16 := by have := mem_range.mp hj; omega
      unfold n t d
      omega
    omega
  · have table : ∀ (a : Fin 23) (b : Fin 17), 0 < a.val → 0 < slice a.val b.val →
      (a.val=5 ∧ 14≤b.val) ∨ (a.val=6 ∧ 15≤b.val) := by
      set_option maxRecDepth 12000 in
      set_option maxHeartbeats 2000000 in
      decide +kernel
    exact table ⟨r,by omega⟩ ⟨h,by omega⟩ hr hp

/-- The complete list of positive-surplus shapes through value degree sixteen,
over all positive multiplicities and every total scalar/value degree cap. -/
theorem positive_iff {r v l : ℕ} (hr : 0<r) (hv : v≤16) :
    0 < score r v l ↔
    (r=5 ∧ ((v=14 ∧ 511305640≤l) ∨ (15≤v ∧ 447392437≤l))) ∨
    (r=6 ∧ ((v=15 ∧ 715827893≤l) ∨ (v=16 ∧ 335≤l))) := by
  have profile (hp : 0<score r v l) : (r=5 ∧ 14≤v) ∨ (r=6 ∧ 15≤v) := by
    by_contra! hn
    have bound : score r v l≤0 := by
      apply sum_nonpos
      intro h _
      by_contra! pos
      have poss := positive_slice hr ((min_le_left v h).trans hv) pos
      omega
    omega
  by_cases hprof : (r=5 ∧ 14≤v) ∨ (r=6 ∧ 15≤v)
  · by_cases hsmall : l<16
    · have low : ∀ (a : Fin 17) (b : Fin 16), score 5 a.val b.val ≤ 0 ∧ score 6 a.val b.val ≤ 0 := by
        set_option maxRecDepth 12000 in
        set_option maxHeartbeats 2000000 in
        decide +kernel
      have k := low ⟨v,by omega⟩ ⟨l,by omega⟩
      simp only at k
      rcases hprof with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 16≤l)
      rw [tail r v m hv]
      have vals :
          score 5 14 16 = -53687090430 ∧ slice 5 14=105 ∧
          score 5 15 16 = -53687090400 ∧ slice 5 15=120 ∧
          score 5 16 16 = -53687090400 ∧ slice 5 16=120 ∧
          score 6 15 16 = -85899345120 ∧ slice 6 15=120 ∧
          score 6 16 16 = -85630909648 ∧ slice 6 16=268435592 := by decide +kernel
      rcases vals with ⟨a,b,c,e,f,g,h,i,j,k⟩
      rcases hprof with ⟨rfl,lo⟩ | ⟨rfl,lo⟩ <;> interval_cases v <;>
        simp_all <;> omega
  · constructor
    · exact fun hp => False.elim (hprof (profile hp))
    · omega

/-- Sharp feasibility of the actual rank-dimension test. This compares the
row and column types of the interpolation matrix used to produce the surface. -/
theorem matrix_positive_iff {r v l : ℕ} (hr : 0<r) (hv : v≤16) :
    n*Fintype.card (JetRows l r) < Fintype.card (Monomials l v d (r*t)) ↔
    (r=5 ∧ ((v=14 ∧ 511305640≤l) ∨ (15≤v ∧ 447392437≤l))) ∨
    (r=6 ∧ ((v=15 ∧ 715827893≤l) ∨ (v=16 ∧ 335≤l))) := by
  have diff := matrix_difference r v l
  by_cases all : r≤v+1
  · rw [all_orders r v l all,sub_self] at diff
    rw [← positive_iff hr hv]
    omega
  · have bound : (∑ j ∈ range (v+1), equations r l j) ≤ ∑ j ∈ range r, equations r l j := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro j _ _
      unfold equations
      positivity
    constructor
    · intro hp
      have scorePos : 0<score r v l := by omega
      exact (positive_iff hr hv).mp scorePos
    · omega

/-- The minimum value degree is attained on every received pair. The least
total degree for this value cap leaves a 90-dimensional coefficient surplus. -/
theorem degree_fourteen_surface {F : Type} [Field F] {I : Type*} [Fintype I]
    (dom : I ↪ F) (u v : I → F) (hn : Fintype.card I = n) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 →
        j ≤ 14 ∧ h+j ≤ 511305640 ∧ x+j*d < 5*t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ B : Finset I, t ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z*v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  have exactCard : 90+n*Fintype.card (JetRows 511305640 5) =
      Fintype.card (Monomials 511305640 14 d (5*t)) := by
    simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    norm_num [Fin.sum_univ_succ,d,t,n]
  obtain ⟨a,ha,_,hf⟩ := exists_surface dom u v (by decide : 0<5) (by decide : 0<t)
    (by decide : 5≤511305640+1) (by rw [hn,←exactCard]; omega)
  refine ⟨surface a,surface_ne_zero ha,fun _ _ _ h => surface_support a h,?_⟩
  intro z q hq B hB hg
  rw [surface_eval]
  exact hf z q hq B hB hg

#print axioms matrix_positive_iff
#print axioms positive_iff
#print axioms degree_fourteen_surface
end ArkLib.ProximityGap.Frontier.EighthHasseDegree
