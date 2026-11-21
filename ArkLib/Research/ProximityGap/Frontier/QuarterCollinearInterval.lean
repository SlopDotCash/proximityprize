/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitPencil

/-! # Three collinear heads on the first quarter-rate interval -/
namespace ArkLib.ProximityGap.Frontier.QuarterCollinearInterval
open SecondPrimeQuarticInterpolation

/-- The quartic at the known attack predecessor has a surplus of 1990 jet coefficients. -/
theorem quartic_capacity :
    Fintype.card (Monomials 121 4 268435455 (2*592794966)) = 365*1073741824+1990 := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- Weighted section caps for the three possible nonlinear degrees of the quartic. -/
theorem quartic_variance : ∀ b : Fin 3,
    let m : ℚ := 121
    let d : ℚ := 268435455
    let n : ℚ := 1073741824
    let t : ℚ := 592794966
    let K : ℚ := 81/100
    let v : ℚ := b.val+2
    let x := (2*v-2)*m-v*(v-1)+1
    let z := (2*v-2)*(2*t-1)-v*(v-1)*d+1
    let den := (5*K^4-4*K^5)*t-d
    let num := 2*K^5*v*(4*m*x*z+m*n+x*z)+(n-d)*(m+1)
    0<den ∧ 5≤2*K*(v+2) ∧ z≤3892314127 ∧
      x+num/den<(![1656827,8426793,20841577] : Fin 3 → ℚ) b := by
  intro b
  fin_cases b <;> norm_num

/-- The incidence cutoffs force three rich affine heads and make every rich
triple collinear, including when all four factors are rich. -/
theorem rich_cutoffs :
    268435455 < 592794966-121*1073741824/2048-3*(121*1073741824/(2048-121)) ∧
    2*(480946858+1)+4*20841576 < 1073741824 ∧
    1073741824+2*268435455 < 3*(592794966-480946858/2047) ∧
    1+4*(1073741824+3*268435455-3*(592794966-480946858/2047))+2047 < 1073741824 := by
  decide

/-- The local incidence inequality for three rich heads identifies the same full
degree fibers at each translated threshold. -/
theorem three_head_slack (j L A R s u : ℕ) (hj : j≤33554430) (hs : 1 ≤ s)
    (hA : 3*s ≤ A) (hL : 1073741824+6*j < L)
    (hinc : 6*(626349395-j)+L+2046*u+2*A+3*R≤3*1073741824+6*268435455) :
    A=3 ∧ R=0 ∧ s=1 ∧ u=0 ∧ L≤1073741826+6*j := by omega

/-- Four genuinely rich heads cannot reach the translated threshold. Before
469762049 errors their population is at most the first named budget itself. -/
theorem four_head_slack (j L : ℕ) (hj : j≤33554430)
    (hinc : 8*(626349395-j)+L ≤ 4*1073741824+6*(268435455-1)) :
    L≤1073741824+6*j ∧ (j≤22369620 → L≤1073741824) := by omega

/-- An outsider on the support T can meet each head at most d times. Outside T,
only a site in all three cores can contribute more than two incidences. -/
theorem outsider_core_sum {I : Type*} [Fintype I] [DecidableEq I]
    (C₀ C₁ C₂ T : Finset I) (d : ℕ)
    (h₀ : (C₀ ∩ T).card ≤ d) (h₁ : (C₁ ∩ T).card ≤ d) (h₂ : (C₂ ∩ T).card ≤ d) :
    C₀.card+C₁.card+C₂.card ≤ 3*d+2*(Finset.univ \ T).card+(C₀ ∩ C₁ ∩ C₂).card := by
  let outside₀ := C₀ \ T
  let outside₁ := C₁ \ T
  let outside₂ := C₂ \ T
  have hxy : (outside₀ ∪ outside₁).card ≤ (Finset.univ \ T).card := Finset.card_le_card (by
    intro a ha
    simp_all [outside₀,outside₁]
    tauto)
  have hxyz : ((outside₀ ∩ outside₁) ∪ outside₂).card ≤ (Finset.univ \ T).card := Finset.card_le_card (by
    intro a ha
    simp_all [outside₀,outside₁,outside₂]
    tauto)
  have ht : (outside₀ ∩ outside₁ ∩ outside₂).card ≤ (C₀ ∩ C₁ ∩ C₂).card := Finset.card_le_card (by
    intro a ha
    simp_all [outside₀,outside₁,outside₂])
  have h₃ := Finset.card_union_add_card_inter outside₀ outside₁
  have h₄ := Finset.card_union_add_card_inter (outside₀ ∩ outside₁) outside₂
  have h₅ := Finset.card_sdiff_add_card_inter C₀ T
  have h₆ := Finset.card_sdiff_add_card_inter C₁ T
  have h₇ := Finset.card_sdiff_add_card_inter C₂ T
  change outside₀.card+_=_ at h₅
  change outside₁.card+_=_ at h₆
  change outside₂.card+_=_ at h₇
  omega

/-- If the three rich heads have an outsider, its support imposes a large
penalty on their combined population. The 2047 exceptional labels cannot
offset that penalty anywhere in the bracket. -/
theorem outsider_cap (j L A R u rest : ℕ)
    (hj : j≤33554430) (hA : 3≤A) (hrest : rest≤2047)
    (hinc : 6*(626349395-j)+L+2046*u+2*A+3*R≤3*1073741824+6*268435455)
    (hout : 3*(626349395-j)≤3*268435455+2*(447392428+j)+R+u) :
    L+rest+536868843 ≤ 1073741824+21*j ∧ L+rest ≤ 1073741824+6*j ∧
      (j≤25565183 → L+rest≤1073741824) := by omega

#print axioms outsider_core_sum
#print axioms outsider_cap
#print axioms quartic_variance
#print axioms three_head_slack
#print axioms four_head_slack
end ArkLib.ProximityGap.Frontier.QuarterCollinearInterval
