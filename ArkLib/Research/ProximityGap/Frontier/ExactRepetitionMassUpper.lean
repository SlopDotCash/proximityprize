/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RepetitionLightLineDeficit

/-! # Uniform exact upper bound for weighted rich-line arrangements

Formalizes the complete uniform upper-bound engine and two-candidate formula of
`docs/research/proximity-gap/exact-repetition-mass.md`:

For any length `n`, integer agreement count `t` with `2048 ≤ t ≤ n` and `256 * n ≤ t ^ 2`, and
any weighted linear incidence arrangement `A` of total mass `n` at agreement threshold `t`,

  `A.lines.card ≤ exactMass n t`

where
  `exactMass n t = max_{1 ≤ h ≤ n / (t - 1)} (h * L_h + h.choose 2 + r_h)`,
  `L_h = n - h * (t - 1)`,
  `r_h = max { r < t | r * t - r.choose 2 ≤ L_h }`.

Moreover:
* In the concurrency regime `3 * t > 2 * n`, `A.lines.card ≤ n - t + 1 = exactMass n t` holds for
  every `0 < t ≤ n`.
* In the uniform regime `2048 ≤ t ≤ n` and `256 * n ≤ t ^ 2`, `exactMass n t` is achieved by at
  least one of the two integers straddling `(2 * n - 1) / (4 * t - 6)`, clamped to
  `[1, n / (t - 1)]`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ExactRepetitionMassUpper

open Finset
open ArkLib.ProximityGap.Frontier.WeightedRichLinePacking

/-! ## Section 1: The light-line capacity `r_h` and exact mass function `M(n, t)` -/

/-- Minimum light mass required by `r` rich lines of threshold `t` with pairwise overlaps ≤ 1:
`G(r, t) = r * t - C(r, 2)`. -/
def lightLineMass (r t : ℕ) : ℕ := r * t - r.choose 2

theorem choose_two_eq (r : ℕ) : r.choose 2 = r * (r - 1) / 2 := Nat.choose_two_right r

theorem two_mul_choose_two (r : ℕ) : 2 * r.choose 2 = r * (r - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd

theorem choose_two_le_mul (r t : ℕ) (hrt : r ≤ t) : r.choose 2 ≤ r * t := by
  have h2 := two_mul_choose_two r
  have hmul : r * (r - 1) ≤ 2 * (r * t) := by
    calc r * (r - 1) ≤ r * (2 * t) := Nat.mul_le_mul_left r (by omega)
      _ = 2 * (r * t) := by ring
  omega

theorem lightLineMass_zero (t : ℕ) : lightLineMass 0 t = 0 := by
  simp [lightLineMass]

theorem lightLineMass_succ (r t : ℕ) (hrt : r < t) :
    lightLineMass (r + 1) t = lightLineMass r t + (t - r) := by
  unfold lightLineMass
  rw [Nat.choose_succ_succ, Nat.choose_one_right]
  have hle : r.choose 2 ≤ r * t := choose_two_le_mul r t (Nat.le_of_lt hrt)
  have hle2 : r.choose 2 + r ≤ (r + 1) * t := by
    rw [Nat.succ_mul]
    omega
  rw [Nat.succ_mul] at hle2 ⊢
  change r * t + t - (r + r.choose 2) = r * t - r.choose 2 + (t - r)
  omega

theorem lightLineMass_strictMono {t r₁ r₂ : ℕ} (h12 : r₁ < r₂) (h2t : r₂ ≤ t) :
    lightLineMass r₁ t < lightLineMass r₂ t := by
  induction r₂ with
  | zero => omega
  | succ k ih =>
    rw [lightLineMass_succ k t (by omega)]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h12) with hlt | rfl
    · have := ih hlt (by omega)
      omega
    · omega

theorem lightLineMass_mono {t r₁ r₂ : ℕ} (h12 : r₁ ≤ r₂) (h2t : r₂ ≤ t) :
    lightLineMass r₁ t ≤ lightLineMass r₂ t := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · exact le_rfl
  · exact (lightLineMass_strictMono hlt h2t).le

/-- Step lower bound along the increasing branch `r₁ ≤ r₂ ≤ t`:
`lightLineMass r₂ t ≥ lightLineMass r₁ t + (r₂ - r₁) * (t - r₂ + 1)`. -/
theorem lightLineMass_step_ge {t r₁ r₂ : ℕ} (h12 : r₁ ≤ r₂) (h2t : r₂ ≤ t) :
    lightLineMass r₁ t + (r₂ - r₁) * (t - r₂ + 1) ≤ lightLineMass r₂ t := by
  induction r₂ with
  | zero =>
    have : r₁ = 0 := by omega
    subst this; simp
  | succ k ih =>
    rcases eq_or_lt_of_le h12 with rfl | hlt
    · simp
    · have hk : r₁ ≤ k := Nat.lt_succ_iff.mp hlt
      have ih' := ih hk (by omega)
      rw [lightLineMass_succ k t (by omega)]
      have h1 : t - (k + 1) + 1 = t - k := by omega
      have h2 : t - (k + 1) + 1 ≤ t - k + 1 := by omega
      have h3 : k + 1 - r₁ = (k - r₁) + 1 := by omega
      rw [h3, Nat.succ_mul, h1]
      have h4 : (k - r₁) * (t - k) ≤ (k - r₁) * (t - k + 1) := Nat.mul_le_mul_left _ (by omega)
      omega

/-- Largest `0 ≤ r < t` satisfying `r * t - C(r, 2) ≤ L`. -/
def richLightCap (L t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun r => lightLineMass r t ≤ L)).sup id

theorem richLightCap_lt {L t : ℕ} (ht : 0 < t) : richLightCap L t < t := by
  unfold richLightCap
  have hmem : 0 ∈ (Finset.range t).filter (fun r => lightLineMass r t ≤ L) := by
    simp [ht, lightLineMass_zero]
  have hle : ((Finset.range t).filter (fun r => lightLineMass r t ≤ L)).sup id ≤ t - 1 := by
    apply Finset.sup_le
    intro r hr
    have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    change r ≤ t - 1
    omega
  omega

theorem lightLineMass_richLightCap_le {L t : ℕ} (ht : 0 < t) :
    lightLineMass (richLightCap L t) t ≤ L := by
  unfold richLightCap
  let S := (Finset.range t).filter (fun r => lightLineMass r t ≤ L)
  have hne : S.Nonempty := ⟨0, by simp [S, ht, lightLineMass_zero]⟩
  obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup S hne id
  change lightLineMass (S.sup id) t ≤ L
  rw [hmax]
  exact (Finset.mem_filter.mp hr).2

theorem le_richLightCap_of_le {L t r : ℕ} (hrt : r < t) (h : lightLineMass r t ≤ L) :
    r ≤ richLightCap L t := by
  unfold richLightCap
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrt, h⟩)

theorem lt_lightLineMass_succ_richLightCap {L t : ℕ} (_ht : 0 < t)
    (hnext : richLightCap L t + 1 < t) :
    L < lightLineMass (richLightCap L t + 1) t := by
  by_contra hle
  push Not at hle
  have := le_richLightCap_of_le hnext hle
  omega

/-- Under `2048 ≤ t` and `256 * n ≤ t^2`, any light mass `L ≤ n` satisfies `r_h ≤ t - 2`. -/
theorem richLightCap_le_sub_two {n L t : ℕ} (ht : 2048 ≤ t) (hsq : 256 * n ≤ t ^ 2)
    (hLn : L ≤ n) : richLightCap L t ≤ t - 2 := by
  by_contra hgt
  push Not at hgt
  have hlt := richLightCap_lt (L := L) (by omega : 0 < t)
  have heq : richLightCap L t = t - 1 := by omega
  have hle := lightLineMass_richLightCap_le (L := L) (by omega : 0 < t)
  rw [heq] at hle
  have h2 := two_mul_choose_two (t - 1)
  have hcm := choose_two_le_mul (t - 1) t (by omega)
  unfold lightLineMass at hle
  have hge : 2 * ((t - 1) * t - (t - 1).choose 2) = (t - 1) * (t + 2) := by
    have hsub : 2 * ((t - 1) * t - (t - 1).choose 2) = 2 * ((t - 1) * t) - 2 * (t - 1).choose 2 := by
      omega
    rw [hsub, h2, show t - 1 - 1 = t - 2 by omega]
    have hmul : (t - 1) * (t - 2) ≤ 2 * ((t - 1) * t) := by
      calc (t - 1) * (t - 2) ≤ (t - 1) * (2 * t) := Nat.mul_le_mul_left (t - 1) (by omega)
        _ = 2 * ((t - 1) * t) := by ring
    zify [hmul, show 1 ≤ t by omega, show 2 ≤ t by omega]
    ring
  have h2L : (t - 1) * (t + 2) ≤ 2 * n := by omega
  have hge_t2 : t ^ 2 ≤ (t - 1) * (t + 2) := by
    zify [show 1 ≤ t by omega]
    have hzt : (2048 : ℤ) ≤ t := by exact_mod_cast ht
    have hexp : ((t : ℤ) - 1) * ((t : ℤ) + 2) = (t : ℤ) ^ 2 + t - 2 := by ring
    linarith only [hzt, hexp]
  have ht2_pos : 0 < t ^ 2 := by positivity
  omega

theorem richLightCap_eq_zero_of_lt {L t : ℕ} (ht : 0 < t) (hL : L < t) :
    richLightCap L t = 0 := by
  by_contra hne
  have h1 : 1 ≤ richLightCap L t := Nat.pos_of_ne_zero hne
  have hlt := richLightCap_lt (L := L) ht
  have hle := lightLineMass_richLightCap_le (L := L) ht
  have hstep : lightLineMass 1 t ≤ lightLineMass (richLightCap L t) t :=
    lightLineMass_mono h1 (Nat.le_of_lt hlt)
  have h1val : lightLineMass 1 t = t := by simp [lightLineMass]
  omega

/-- The quadratic center-secant part of candidate `h`. -/
def candidateQuad (n t h : ℕ) : ℕ := h * (n - h * (t - 1)) + h.choose 2

/-- Candidate bad-label count with `h` strong centers and `r_h` light-only rich lines. -/
def candidateMass (n t h : ℕ) : ℕ := candidateQuad n t h + richLightCap (n - h * (t - 1)) t

/-- Maximum candidate count over all feasible center counts `1 ≤ h ≤ n / (t - 1)`. -/
def exactMass (n t : ℕ) : ℕ := (Finset.Icc 1 (n / (t - 1))).sup (candidateMass n t)

theorem candidateMass_le_exactMass {n t h : ℕ} (h1 : 1 ≤ h) (h2 : h ≤ n / (t - 1)) :
    candidateMass n t h ≤ exactMass n t :=
  Finset.le_sup (f := candidateMass n t) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

theorem candidateQuad_le_exactMass {n t h : ℕ} (h1 : 1 ≤ h) (h2 : h ≤ n / (t - 1)) :
    candidateQuad n t h ≤ exactMass n t :=
  (Nat.le_add_right _ _).trans (candidateMass_le_exactMass h1 h2)

theorem candidateQuad_one {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    candidateQuad n t 1 = n - t + 1 := by
  unfold candidateQuad
  simp only [one_mul]
  have : (1 : ℕ).choose 2 = 0 := by decide
  rw [this]
  omega

/-- Exact value of `exactMass` when `3 * t > 2 * n`: `h = 1` achieves `n - t + 1` and dominates. -/
theorem exactMass_of_three_mul_gt {n t : ℕ} (ht : 2 ≤ t) (htn : t ≤ n) (hgt : 2 * n < 3 * t) :
    exactMass n t = n - t + 1 := by
  have h1_feas : 1 ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hc1 : candidateMass n t 1 = n - t + 1 := by
    unfold candidateMass
    rw [candidateQuad_one (by omega) htn]
    have hL : n - 1 * (t - 1) < t := by omega
    rw [richLightCap_eq_zero_of_lt (by omega) hL, add_zero]
  apply le_antisymm
  · unfold exactMass
    apply Finset.sup_le
    intro h hh
    obtain ⟨h1, hle⟩ := Finset.mem_Icc.mp hh
    have hfeas : h * (t - 1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hle
    have hh_le2 : h ≤ 2 := by
      by_contra h3
      have hge3 : 3 ≤ h := by omega
      have := Nat.mul_le_mul_right (t - 1) hge3
      omega
    rcases show h = 1 ∨ h = 2 by omega with rfl | rfl
    · rw [hc1]
    · unfold candidateMass candidateQuad
      have hL2 : n - 2 * (t - 1) < t := by omega
      rw [richLightCap_eq_zero_of_lt (by omega) hL2, add_zero]
      have hc2 : (2 : ℕ).choose 2 = 1 := by decide
      rw [hc2]
      omega
  · rw [← hc1]
    exact candidateMass_le_exactMass le_rfl h1_feas

/-! ## Section 2: The uniform two-candidate formula -/

/-- Integer floor of the quadratic vertex `(2 * n - 1) / (4 * t - 6)`, clamped to `[1, n/(t-1)]`. -/
def candidateLow (n t : ℕ) : ℕ := min (n / (t - 1)) (max 1 ((2 * n - 1) / (4 * t - 6)))

/-- Next integer above the vertex, clamped to `[1, n/(t-1)]`. -/
def candidateHigh (n t : ℕ) : ℕ := min (n / (t - 1)) (max 1 ((2 * n - 1) / (4 * t - 6) + 1))

private theorem two_mul_candidateQuad {n t h : ℕ} (ht : 2 ≤ t) (hfeas : h * (t - 1) ≤ n) :
    (2 * candidateQuad n t h : ℤ) = (h : ℤ) * (2 * n - 1) - (h : ℤ) ^ 2 * (2 * t - 3) := by
  unfold candidateQuad
  have h2 := two_mul_choose_two h
  have hmul : 2 * (h * (n - h * (t - 1)) + h.choose 2) =
      2 * (h * (n - h * (t - 1))) + h * (h - 1) := by omega
  have hle1 : 1 ≤ t := by omega
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · zify [hfeas, hle1, hpos] at hmul ⊢
    rw [hmul]; ring

/-- Uniform two-candidate formula: when `2048 ≤ t ≤ n` and `256 * n ≤ t^2`, `exactMass n t`
is achieved at `candidateLow n t` or `candidateHigh n t`. -/
theorem exactMass_eq_two_candidates {n t : ℕ} (ht : 2048 ≤ t) (htn : t ≤ n)
    (hsq : 256 * n ≤ t ^ 2) :
    exactMass n t = max (candidateMass n t (candidateLow n t))
      (candidateMass n t (candidateHigh n t)) := by
  have hmax_pos : 1 ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlow_mem : candidateLow n t ∈ Finset.Icc 1 (n / (t - 1)) := by
    unfold candidateLow
    exact Finset.mem_Icc.mpr ⟨le_min hmax_pos (le_max_left _ _), min_le_left _ _⟩
  have hhigh_mem : candidateHigh n t ∈ Finset.Icc 1 (n / (t - 1)) := by
    unfold candidateHigh
    exact Finset.mem_Icc.mpr ⟨le_min hmax_pos (le_max_left _ _), min_le_left _ _⟩
  apply le_antisymm
  · unfold exactMass
    apply Finset.sup_le
    intro h hh
    obtain ⟨h1, hle_max⟩ := Finset.mem_Icc.mp hh
    have hfeas : h * (t - 1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hle_max
    let v := (2 * n - 1) / (4 * t - 6)
    have hmod_le : v * (4 * t - 6) ≤ 2 * n - 1 := Nat.div_mul_le_self _ _
    have hmod_lt : 2 * n - 1 < (v + 1) * (4 * t - 6) := by
      have hlt := Nat.lt_div_mul_add (a := 2 * n - 1) (b := 4 * t - 6) (by omega)
      rw [Nat.add_mul, one_mul]; omega
    have hr_le : richLightCap (n - h * (t - 1)) t ≤ t - 2 :=
      richLightCap_le_sub_two ht hsq (Nat.sub_le _ _)
    by_cases hA : h = candidateLow n t
    · rw [hA]; exact le_max_left _ _
    by_cases hB : h = candidateHigh n t
    · rw [hB]; exact le_max_right _ _
    -- Either h < candidateLow n t or candidateHigh n t < h.
    have hcases : h < candidateLow n t ∨ candidateHigh n t < h := by
      unfold candidateLow at hA ⊢
      unfold candidateHigh at hB ⊢
      omega
    rcases hcases with hlt | hgt
    · -- Compare h against c = candidateLow n t (with h < c ≤ v).
      let c := candidateLow n t
      have hc_le_max : c ≤ n / (t - 1) := (Finset.mem_Icc.mp hlow_mem).2
      have hc_feas : c * (t - 1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hc_le_max
      have hc_le_v : c ≤ v := by
        unfold c candidateLow at hlt ⊢
        omega
      have hq1 := two_mul_candidateQuad (n := n) (t := t) (h := h) (by omega) hfeas
      have hq2 := two_mul_candidateQuad (n := n) (t := t) (h := c) (by omega) hc_feas
      have hdiff : (2 * t - 3 : ℤ) ≤ 2 * (candidateQuad n t c : ℤ) - 2 * (candidateQuad n t h : ℤ) := by
        have hch : (1 : ℤ) ≤ (c : ℤ) - h := by omega
        have hsum : (h : ℤ) + c ≤ 2 * v - 1 := by omega
        have hmul : ((h : ℤ) + c) * (2 * t - 3) ≤ (2 * v - 1) * (2 * t - 3) :=
          mul_le_mul_of_nonneg_right hsum (by omega)
        have hfact : 2 * (candidateQuad n t c : ℤ) - 2 * (candidateQuad n t h : ℤ) =
            ((c : ℤ) - h) * ((2 * n - 1 : ℤ) - ((h : ℤ) + c) * (2 * t - 3)) := by
          rw [hq1, hq2]; ring
        have hbr : (2 * t - 3 : ℤ) ≤ (2 * n - 1 : ℤ) - ((h : ℤ) + c) * (2 * t - 3) := by
          have hm : (v : ℤ) * (4 * t - 6) ≤ 2 * n - 1 := by zify [show 1 ≤ 2 * n by omega, show 6 ≤ 4 * t by omega] at hmod_le; exact hmod_le
          linarith only [hm, hmul]
        rw [hfact]
        have hzt : (2048 : ℤ) ≤ t := by exact_mod_cast ht
        nlinarith only [hch, hbr, hzt]
      have hqstep : candidateQuad n t h + (t - 1) ≤ candidateQuad n t c := by omega
      have hfin : candidateMass n t h ≤ candidateMass n t c := by
        unfold candidateMass
        omega
      exact hfin.trans (le_max_left _ _)
    · -- Compare h against c = candidateHigh n t (with v + 1 ≤ c < h).
      let c := candidateHigh n t
      have hc_le_max : c ≤ n / (t - 1) := (Finset.mem_Icc.mp hhigh_mem).2
      have hc_feas : c * (t - 1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hc_le_max
      have hc_ge_v1 : v + 1 ≤ c := by
        unfold c candidateHigh at hgt ⊢
        omega
      have hq1 := two_mul_candidateQuad (n := n) (t := t) (h := h) (by omega) hfeas
      have hq2 := two_mul_candidateQuad (n := n) (t := t) (h := c) (by omega) hc_feas
      have hdiff : (2 * t - 2 : ℤ) ≤ 2 * (candidateQuad n t c : ℤ) - 2 * (candidateQuad n t h : ℤ) := by
        have hhc : (1 : ℤ) ≤ (h : ℤ) - c := by omega
        have hsum : 2 * (v : ℤ) + 3 ≤ (h : ℤ) + c := by omega
        have hmul : (2 * (v : ℤ) + 3) * (2 * t - 3) ≤ ((h : ℤ) + c) * (2 * t - 3) :=
          mul_le_mul_of_nonneg_right hsum (by omega)
        have hfact : 2 * (candidateQuad n t c : ℤ) - 2 * (candidateQuad n t h : ℤ) =
            ((h : ℤ) - c) * (((h : ℤ) + c) * (2 * t - 3) - (2 * n - 1 : ℤ)) := by
          rw [hq1, hq2]; ring
        have hbr : (2 * t - 2 : ℤ) ≤ ((h : ℤ) + c) * (2 * t - 3) - (2 * n - 1 : ℤ) := by
          have hm : (2 * n - 1 : ℤ) < ((v : ℤ) + 1) * (4 * t - 6) := by
            zify [show 1 ≤ 2 * n by omega, show 6 ≤ 4 * t by omega] at hmod_lt; exact hmod_lt
          linarith only [hm, hmul]
        rw [hfact]
        have hzt : (2048 : ℤ) ≤ t := by exact_mod_cast ht
        nlinarith only [hhc, hbr, hzt]
      have hqstep : candidateQuad n t h + (t - 1) ≤ candidateQuad n t c := by omega
      have hfin : candidateMass n t h ≤ candidateMass n t c := by
        unfold candidateMass
        omega
      exact hfin.trans (le_max_right _ _)
  · exact max_le (Finset.le_sup (f := candidateMass n t) hlow_mem)
      (Finset.le_sup (f := candidateMass n t) hhigh_mem)

/-! ## Section 3: Sharp `C(h, 2)` multi-center decomposition -/

section Arrangements

variable {P J : Type} [DecidableEq P] [DecidableEq J]

/-- Lines meeting at least two points of `H`. -/
def multiLines {t : ℕ} (A : Arrangement P J t) (H : Finset P) : Finset J :=
  A.lines.filter (fun i => 2 ≤ (A.block i ∩ H).card)

omit [DecidableEq J] in
/-- Each pair of distinct centers lies on at most one line, so `#multiLines ≤ C(#H, 2)`. -/
theorem multiLines_card_le_choose_two {t : ℕ} (A : Arrangement P J t) (H : Finset P) :
    (multiLines A H).card ≤ H.card.choose 2 := by
  let D : J → Finset (Finset P) := fun i => (A.block i ∩ H).powersetCard 2
  have hd : (multiLines A H : Set J).PairwiseDisjoint D := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    obtain ⟨hSsub_i, hScard⟩ := Finset.mem_powersetCard.mp hSi
    obtain ⟨hSsub_j, _⟩ := Finset.mem_powersetCard.mp hSj
    have hSinter : S ⊆ A.block i ∩ A.block j := fun x hx =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hSsub_i hx)).1,
        (Finset.mem_inter.mp (hSsub_j hx)).1⟩
    have hle1 := A.linear i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
    have hle2 := Finset.card_le_card hSinter
    omega
  have hne : ∀ i ∈ multiLines A H, (D i).Nonempty := by
    intro i hi
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp hi).2
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩⟩
  have hsub : (multiLines A H).biUnion D ⊆ H.powersetCard 2 :=
    Finset.biUnion_subset.mpr fun i _ S hS => by
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.mp hS
      exact Finset.mem_powersetCard.mpr ⟨h1.trans Finset.inter_subset_right, h2⟩
  calc
    (multiLines A H).card ≤ ((multiLines A H).biUnion D).card :=
      Finset.card_le_card_biUnion hd hne
    _ ≤ (H.powersetCard 2).card := Finset.card_le_card hsub
    _ = H.card.choose 2 := Finset.card_powersetCard 2 H

/-- Sharp decomposition of an arrangement's lines with `C(#H, 2)` for multi-center lines. -/
theorem decomposition_choose_two {t : ℕ} (A : Arrangement P J t) (H : Finset P) :
    A.lines.card ≤ (A.away H).card + H.card.choose 2 + ∑ x ∈ H, (A.solo H x).card := by
  have hsub : A.lines ⊆ (A.away H ∪ multiLines A H) ∪ H.biUnion (A.solo H) := by
    intro i hi
    by_cases h : Disjoint (A.block i) H
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩))
    by_cases h2 : 2 ≤ (A.block i ∩ H).card
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h2⟩))
    obtain ⟨x, xi, xh⟩ := Finset.not_disjoint_iff.mp h
    have hs : A.block i ∩ H = {x} := by
      ext y
      rw [Finset.mem_singleton]
      exact ⟨fun hy => Finset.card_le_one.mp (by omega : (A.block i ∩ H).card ≤ 1)
        y hy x (Finset.mem_inter.mpr ⟨xi, xh⟩), fun h => h ▸ Finset.mem_inter.mpr ⟨xi, xh⟩⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, xh, Finset.mem_filter.mpr ⟨hi, hs⟩⟩)
  have h1 := Finset.card_union_le (A.away H ∪ multiLines A H) (H.biUnion (A.solo H))
  have h2 := Finset.card_union_le (A.away H) (multiLines A H)
  have h3 := Finset.card_biUnion_le (s := H) (t := A.solo H)
  have h4 := multiLines_card_le_choose_two A H
  have h5 := Finset.card_le_card hsub
  omega

/-! ## Section 4: Concurrency upper bound for `3 * t > 2 * n` -/

/-- When `3 * t > 2 * n`, any weighted arrangement has at most `n - t + 1` rich lines:
all lines must pass through a single common point when there are at least two. -/
theorem lines_card_le_of_three_mul_gt {t n : ℕ} (A : Arrangement P J t)
    (total : mass A.w A.points = n) (ht : 0 < t) (htn : t ≤ n) (hgt : 2 * n < 3 * t) :
    A.lines.card ≤ n - t + 1 := by
  by_cases hsmall : A.lines.card ≤ 1
  · omega
  push Not at hsmall
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hsmall
  -- Any two lines meet because 2 * t > n.
  have hmeet : (A.block i ∩ A.block j).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hdisj : Disjoint (A.block i) (A.block j) := Finset.disjoint_iff_inter_eq_empty.mpr hempty
    have hunion : mass A.w (A.block i ∪ A.block j) ≤ n := by
      rw [← total]
      exact Finset.sum_le_sum_of_subset (Finset.union_subset (A.inside i hi) (A.inside j hj))
    rw [show mass A.w (A.block i ∪ A.block j) = mass A.w (A.block i) + mass A.w (A.block j) from
      Finset.sum_union hdisj] at hunion
    have ri := A.rich i hi
    have rj := A.rich j hj
    omega
  obtain ⟨p, hp⟩ := hmeet
  have hpi : p ∈ A.block i := (Finset.mem_inter.mp hp).1
  have hpj : p ∈ A.block j := (Finset.mem_inter.mp hp).2
  have hp_pts : p ∈ A.points := A.inside i hi hpi
  -- Every line must pass through `p`; otherwise three nonconcurrent lines force `3 * t ≤ 2 * n`.
  have hall : ∀ k ∈ A.lines, p ∈ A.block k := by
    intro k hk
    by_contra hpk
    have hki : k ≠ i := fun heq => hpk (heq ▸ hpi)
    have hkj : k ≠ j := fun heq => hpk (heq ▸ hpj)
    have htriple : ∀ x ∈ A.points,
        (if x ∈ A.block i then A.w x else 0) +
        (if x ∈ A.block j then A.w x else 0) +
        (if x ∈ A.block k then A.w x else 0) ≤ 2 * A.w x := by
      intro x _
      by_cases hxi : x ∈ A.block i <;> by_cases hxj : x ∈ A.block j <;> by_cases hxk : x ∈ A.block k
      · -- x ∈ block i ∩ block j forces x = p, contradicting hpk
        have hxp : x = p := Finset.card_le_one.mp (A.linear i hi j hj hij) x
          (Finset.mem_inter.mpr ⟨hxi, hxj⟩) p hp
        exact (hpk (hxp ▸ hxk)).elim
      all_goals simp [hxi, hxj, hxk]; try omega
    have hsum := Finset.sum_le_sum htriple
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
    have hfi : A.points.filter (fun x => x ∈ A.block i) = A.block i :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (A.inside i hi))
    have hfj : A.points.filter (fun x => x ∈ A.block j) = A.block j :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (A.inside j hj))
    have hfk : A.points.filter (fun x => x ∈ A.block k) = A.block k :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (A.inside k hk))
    rw [hfi, hfj, hfk] at hsum
    change mass A.w (A.block i) + mass A.w (A.block j) + mass A.w (A.block k) ≤ 2 * mass A.w A.points at hsum
    have ri := A.rich i hi
    have rj := A.rich j hj
    have rk := A.rich k hk
    omega
  -- All lines lie in `A.solo {p} p`.
  have hsolo_eq : A.lines = A.solo {p} p := by
    ext k
    simp only [Arrangement.solo, Finset.mem_filter, iff_self_and]
    intro hk
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun hx => hx.2, fun hx => ⟨hx ▸ hall k hk, hx⟩⟩
  rw [hsolo_eq]
  obtain ⟨h1, h2⟩ := A.solo_bounds {p} p
  have hmass_sdiff : mass A.w (A.points \ {p}) + A.w p = n := by
    have := Finset.sum_sdiff (s₁ := {p}) (s₂ := A.points) (Finset.singleton_subset_iff.mpr hp_pts) (f := A.w)
    simpa [mass, total] using this
  have hcard_le : (A.points \ {p}).card ≤ mass A.w (A.points \ {p}) := by
    have := Finset.sum_le_sum (s := A.points \ {p}) (f := fun _ => 1) (g := A.w)
      (fun x hx => A.positive x (Finset.mem_sdiff.mp hx).1)
    simpa [mass] using this
  by_cases hwp : A.w p < t
  · have hstep : (A.solo {p} p).card * (t - A.w p) ≤ n - A.w p := by omega
    have hpos : 1 ≤ t - A.w p := by omega
    have hmul : (A.solo {p} p).card * (t - A.w p) ≤ (n - t + 1) * (t - A.w p) := by
      have : n - A.w p ≤ (n - t + 1) * (t - A.w p) := by
        have hdiff : (n - t) * (t - A.w p - 1) ≥ 0 := Nat.zero_le _
        zify [htn, hwp.le, show A.w p ≤ n by omega, show 1 ≤ t - A.w p by omega] at hdiff ⊢
        have hexp : ((n : ℤ) - t + 1) * ((t : ℤ) - A.w p) - ((n : ℤ) - A.w p) =
            ((n : ℤ) - t) * ((t : ℤ) - A.w p - 1) := by ring
        linarith only [hdiff, hexp]
      exact hstep.trans this
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  · have hle : (A.solo {p} p).card ≤ n - A.w p := h1.trans (by omega)
    omega

/-! ## Section 5: Uniform upper bound for `3 * t ≤ 2 * n`, `2048 ≤ t`, `256 * n ≤ t^2` -/

omit [DecidableEq J] in
private theorem card_le_mass_sub {t : ℕ} (A : Arrangement P J t) {S : Finset P}
    (hS : S ⊆ A.points) : S.card ≤ mass A.w S := by
  have := Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := A.w) (fun x hx => A.positive x (hS hx))
  simpa [mass] using this

/-- Pure arithmetic helper for Case 2 (`4 * h * t < n`): compare against `2 * h`. -/
private theorem arith_small_centers {n t h K cut : ℕ}
    (ht : 2048 ≤ t) (hh_pos : 1 ≤ h) (hsmall : 4 * h * t < n)
    (hcut_n : h * cut ≤ n) (h16cut : 15 * t ≤ 16 * cut) (h16K : 16 * K ≤ n) :
    K + h.choose 2 + h * (n - h * cut) ≤ candidateQuad n t (2 * h) := by
  have h2ch1 := two_mul_choose_two h
  have h2ch2 := two_mul_choose_two (2 * h)
  have h2h_sub : 2 * h * (t - 1) ≤ n := by
    have h1 : 2 * h * (t - 1) ≤ 2 * h * t := Nat.mul_le_mul_left (2 * h) (Nat.sub_le t 1)
    have h2 : 2 * (2 * h * t) = 4 * h * t := by ring
    omega
  unfold candidateQuad
  zify [hcut_n, h2h_sub, show 1 ≤ t by omega]
  have hz1 : (2 * (h.choose 2) : ℤ) = (h : ℤ) ^ 2 - h := by
    zify [hh_pos] at h2ch1; rw [h2ch1]; ring
  have hz2 : (2 * ((2 * h).choose 2) : ℤ) = 4 * (h : ℤ) ^ 2 - 2 * h := by
    zify [show 1 ≤ 2 * h by omega] at h2ch2; rw [h2ch2]; ring
  have hzcut : (15 : ℤ) * (h : ℤ) ^ 2 * t ≤ 16 * (h : ℤ) ^ 2 * cut := by
    have hm := Nat.mul_le_mul_left (h * h) h16cut
    zify at hm ⊢
    have h1 : ((h : ℤ) * h) * (15 * t) = 15 * (h : ℤ) ^ 2 * t := by ring
    have h2 : ((h : ℤ) * h) * (16 * cut) = 16 * (h : ℤ) ^ 2 * cut := by ring
    linarith only [hm, h1, h2]
  have hzK : (16 : ℤ) * K ≤ n := by exact_mod_cast h16K
  have hzsmall : (4 : ℤ) * h * t < n := by exact_mod_cast hsmall
  have hzh : (1 : ℤ) ≤ h := by exact_mod_cast hh_pos
  have hzt : (2048 : ℤ) ≤ t := by exact_mod_cast ht
  have h4ht : (4 : ℤ) * (h : ℤ) ^ 2 * t ≤ (h : ℤ) * n := by nlinarith only [hzsmall, hzh]
  have hnhn : (n : ℤ) ≤ (h : ℤ) * n := by nlinarith only [hzh, hzsmall, hzt]
  have h8h : (h : ℤ) ≤ (h : ℤ) ^ 2 := by nlinarith only [hzh]
  have hht_pos : (0 : ℤ) ≤ (h : ℤ) ^ 2 * t := by positivity
  have hgoal_eq : 16 * ((2 * (h : ℤ)) * ((n : ℤ) - 2 * (h : ℤ) * ((t : ℤ) - 1)) + ((2 * h).choose 2 : ℤ)) -
      16 * ((K : ℤ) + (h.choose 2 : ℤ) + (h : ℤ) * ((n : ℤ) - (h : ℤ) * cut)) =
      16 * ((h : ℤ) * n) - 16 * K - 64 * ((h : ℤ) ^ 2 * t) + 16 * ((h : ℤ) ^ 2 * cut) +
      64 * (h : ℤ) ^ 2 + 8 * (2 * ((2 * h).choose 2 : ℤ)) - 8 * (2 * (h.choose 2 : ℤ)) := by ring
  linarith only [hgoal_eq, hz1, hz2, hzcut, hzK, hnhn, h4ht, h8h, hht_pos]

/-- Pure arithmetic helper for Case 3 (`3 * n < 4 * h * t`): compare against `j = (h + 1) / 2`. -/
private theorem arith_large_centers {n t h K cut : ℕ}
    (ht : 2048 ≤ t) (hh_ge2 : 2 ≤ h) (hlarge : 3 * n < 4 * h * t)
    (hcut_n : h * cut ≤ n) (h16cut : 15 * t ≤ 16 * cut) (hKt2 : K * t ^ 2 ≤ 16 * n ^ 2) :
    ((h + 1) / 2) * (t - 1) ≤ n ∧
    K + h.choose 2 + h * (n - h * cut) ≤ candidateQuad n t ((h + 1) / 2) := by
  let j := (h + 1) / 2
  have hj_pos : 1 ≤ j := by omega
  have hj_ge : h ≤ 2 * j := by omega
  have h3j_le : 3 * j ≤ 2 * h := by omega
  have h15ht : 15 * h * t ≤ 16 * n := by
    have hm := Nat.mul_le_mul_left h h16cut
    nlinarith only [hm, hcut_n]
  have hj_sub : j * (t - 1) ≤ n := by
    have hjt : j * (t - 1) ≤ j * t := Nat.mul_le_mul_left j (Nat.sub_le t 1)
    have h3jt : 3 * (j * t) ≤ 2 * (h * t) := by
      calc 3 * (j * t) = (3 * j) * t := by ring
        _ ≤ (2 * h) * t := Nat.mul_le_mul_right t h3j_le
        _ = 2 * (h * t) := by ring
    have h15 : 15 * (h * t) = 15 * h * t := by ring
    omega
  refine ⟨hj_sub, ?_⟩
  have h2ch1 := two_mul_choose_two h
  have h2ch2 := two_mul_choose_two j
  have h9K : 9 * K ≤ 256 * h ^ 2 := by
    have h1 : 9 * K * t ^ 2 ≤ 144 * n ^ 2 := by nlinarith only [hKt2]
    have h2 : 9 * n ^ 2 ≤ 16 * h ^ 2 * t ^ 2 := by nlinarith only [hlarge]
    have ht_sq_pos : 0 < t ^ 2 := by positivity
    nlinarith only [h1, h2, ht_sq_pos]
  unfold candidateQuad
  change K + h.choose 2 + h * (n - h * cut) ≤ j * (n - j * (t - 1)) + j.choose 2
  zify [hcut_n, hj_sub, show 1 ≤ t by omega]
  have hz1 : (2 * (h.choose 2) : ℤ) = (h : ℤ) ^ 2 - h := by
    zify [show 1 ≤ h by omega] at h2ch1; rw [h2ch1]; ring
  have hz2 : (2 * (j.choose 2) : ℤ) = (j : ℤ) ^ 2 - j := by
    zify [hj_pos] at h2ch2; rw [h2ch2]; ring
  have hzcut : (15 : ℤ) * (h : ℤ) ^ 2 * t ≤ 16 * (h : ℤ) ^ 2 * cut := by
    have hm := Nat.mul_le_mul_left (h * h) h16cut
    zify at hm ⊢
    have h1 : ((h : ℤ) * h) * (15 * t) = 15 * (h : ℤ) ^ 2 * t := by ring
    have h2 : ((h : ℤ) * h) * (16 * cut) = 16 * (h : ℤ) ^ 2 * cut := by ring
    linarith only [hm, h1, h2]
  have hzK : (9 : ℤ) * K ≤ 256 * (h : ℤ) ^ 2 := by exact_mod_cast h9K
  have hzl : (3 : ℤ) * n < 4 * h * t := by exact_mod_cast hlarge
  have hzh : (2 : ℤ) ≤ h := by exact_mod_cast hh_ge2
  have hzt : (2048 : ℤ) ≤ t := by exact_mod_cast ht
  have hzj1 : (h : ℤ) ≤ 2 * j := by exact_mod_cast hj_ge
  have hzj2 : (3 : ℤ) * j ≤ 2 * h := by exact_mod_cast h3j_le
  have hquad : (48 : ℤ) * (j : ℤ) ^ 2 - 64 * (h : ℤ) * j + 19 * (h : ℤ) ^ 2 ≤ -(h : ℤ) ^ 2 := by
    have hf : (48 : ℤ) * (j : ℤ) ^ 2 - 64 * (h : ℤ) * j + 20 * (h : ℤ) ^ 2 =
        4 * (2 * (j : ℤ) - h) * (6 * (j : ℤ) - 5 * h) := by ring
    have hneg : 6 * (j : ℤ) - 5 * h ≤ 0 := by linarith only [hzj2, hzh]
    have hnn : 0 ≤ 2 * (j : ℤ) - h := by linarith only [hzj1]
    nlinarith only [hf, hneg, hnn]
  have hmul_t : 48 * ((j : ℤ) ^ 2 * t) - 64 * ((h : ℤ) * j * t) + 19 * ((h : ℤ) ^ 2 * t) ≤
      -((h : ℤ) ^ 2 * t) := by
    have hm := mul_le_mul_of_nonneg_right hquad (by linarith only [hzt])
    have he1 : ((48 : ℤ) * (j : ℤ) ^ 2 - 64 * (h : ℤ) * j + 19 * (h : ℤ) ^ 2) * t =
        48 * ((j : ℤ) ^ 2 * t) - 64 * ((h : ℤ) * j * t) + 19 * ((h : ℤ) ^ 2 * t) := by ring
    linarith only [hm, he1]
  have hhj : (0 : ℤ) ≤ (h : ℤ) - j := by linarith only [hzj2, hzh]
  have hnj : 3 * ((h : ℤ) * n) - 3 * ((j : ℤ) * n) ≤
      4 * ((h : ℤ) ^ 2 * t) - 4 * ((h : ℤ) * j * t) := by
    have hm := mul_le_mul_of_nonneg_left hzl.le hhj
    have he1 : ((h : ℤ) - j) * (3 * n) = 3 * ((h : ℤ) * n) - 3 * ((j : ℤ) * n) := by ring
    have he2 : ((h : ℤ) - j) * (4 * h * t) = 4 * ((h : ℤ) ^ 2 * t) - 4 * ((h : ℤ) * j * t) := by ring
    linarith only [hm, he1, he2]
  have hht : (2048 : ℤ) * (h : ℤ) ^ 2 ≤ (h : ℤ) ^ 2 * t := by nlinarith only [hzt, hzh]
  have hj2_nn : (0 : ℤ) ≤ (j : ℤ) ^ 2 := sq_nonneg (j : ℤ)
  have hgoal_eq : 144 * ((j : ℤ) * ((n : ℤ) - (j : ℤ) * ((t : ℤ) - 1)) + (j.choose 2 : ℤ)) -
      144 * ((K : ℤ) + (h.choose 2 : ℤ) + (h : ℤ) * ((n : ℤ) - (h : ℤ) * cut)) =
      -144 * ((h : ℤ) * n) + 144 * ((j : ℤ) * n) + 144 * ((h : ℤ) ^ 2 * cut) -
      144 * ((j : ℤ) ^ 2 * t) - 144 * K + 144 * (j : ℤ) ^ 2 +
      72 * (2 * (j.choose 2 : ℤ)) - 72 * (2 * (h.choose 2 : ℤ)) := by ring
  linarith only [hgoal_eq, hz1, hz2, hzcut, hzK, hmul_t, hnj, hht, hj2_nn, hhj]

/-- Pure arithmetic helper for Subcase 4a (at least one weak center `w ≥ 1`). -/
private theorem arith_weak_centers {n h K w d L Lh : ℕ}
    (hw_pos : 0 < w) (hw_le_h : w ≤ h) (h4Lh : n ≤ 4 * Lh)
    (h64hd : 64 * (h * d) ≤ 3 * n) (h16K : 16 * K ≤ n) (hL_weak : L ≤ Lh + w * d) :
    (2 * h - w) * L + 2 * K ≤ 2 * (h * Lh) := by
  have h2hd : 2 * (h * d) ≤ Lh := by omega
  have h1 : (2 * h - w) * (Lh + w * d) + w * (Lh - 2 * (h * d)) ≤ 2 * (h * Lh) := by
    zify [show w ≤ 2 * h by omega, h2hd]
    have hwwd : (0 : ℤ) ≤ (w : ℤ) * w * d := by positivity
    have hident : (2 * (h : ℤ) - w) * ((Lh : ℤ) + w * d) + w * ((Lh : ℤ) - 2 * (h : ℤ) * d) =
        2 * ((h : ℤ) * Lh) - (w : ℤ) * w * d := by ring
    linarith only [hident, hwwd]
  have hgap : 2 * K ≤ w * (Lh - 2 * (h * d)) := by
    have hbase : 2 * K ≤ Lh - 2 * (h * d) := by omega
    exact hbase.trans (Nat.le_mul_of_pos_left _ hw_pos)
  have hmul_L : (2 * h - w) * L ≤ (2 * h - w) * (Lh + w * d) := Nat.mul_le_mul_left _ hL_weak
  omega

/-- Pure arithmetic helper for Subcase 4b (strong centers): from `h * D < K` and `light_pair_moment`
bound, derive `4 * D < t` and `2 * K < t`. -/
private theorem arith_strong_K_bound {n t h K D : ℕ}
    (ht : 2048 ≤ t) (hsq : 256 * n ≤ t ^ 2) (_hh_pos : 1 ≤ h)
    (hsmall : n ≤ 4 * h * t) (hKt2 : K * t ^ 2 ≤ 16 * n ^ 2) (hhD_lt : h * D < K) :
    4 * D < t ∧
    (∀ T : ℕ, 3 * t ≤ 4 * T → K * T ^ 2 ≤ n * (T + (K - 1)) → 2 * K < t) := by
  have h4D_lt : 4 * D < t := by
    have h1 : h * D * t ^ 2 < K * t ^ 2 := Nat.mul_lt_mul_of_pos_right hhD_lt (by positivity)
    have h2 : h * D * t ^ 2 < 16 * n ^ 2 := h1.trans_le hKt2
    have h3 : 16 * n ^ 2 ≤ 64 * h * t * n := by nlinarith only [hsmall]
    have hDt : D * t < 64 * n := by
      have hmul : (D * t) * (h * t) < (64 * n) * (h * t) := by
        have e1 : (D * t) * (h * t) = h * D * t ^ 2 := by ring
        have e2 : (64 * n) * (h * t) = 64 * h * t * n := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_right hmul
    have h4Dt : 4 * D * t < t ^ 2 := by nlinarith only [hDt, hsq]
    nlinarith only [h4Dt, ht]
  refine ⟨h4D_lt, fun T h4T_ge hmoment => ?_⟩
  have hT2 : 144 * n ≤ T ^ 2 := by
    have h9 : 9 * t ^ 2 ≤ 16 * T ^ 2 := by nlinarith only [h4T_ge]
    nlinarith only [h9, hsq]
  have hKT : K * T ≤ 2 * n := by
    have h2 : K * T ^ 2 ≤ n * T + n * K := by
      have hsub : n * (T + (K - 1)) ≤ n * T + n * K := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left n (by omega)
      exact hmoment.trans hsub
    have hT_pos : 0 < T := by omega
    nlinarith only [h2, hT2, hT_pos]
  have h1 : 3 * t * K ≤ 8 * n := by nlinarith only [hKT, h4T_ge]
  have h2 : 96 * t * K ≤ t ^ 2 := by nlinarith only [h1, hsq]
  nlinarith only [h2, ht]

/-- **Uniform arrangement upper bound.** For every length `n` and integer agreement count `t` with
`2048 ≤ t ≤ n` and `256 * n ≤ t ^ 2`, every weighted linear arrangement of total mass `n` has at
most `exactMass n t` rich lines. -/
theorem uniform_arrangement_upper {t n : ℕ} (A : Arrangement P J t)
    (total : mass A.w A.points = n) (ht : 2048 ≤ t) (htn : t ≤ n) (hsq : 256 * n ≤ t ^ 2) :
    A.lines.card ≤ exactMass n t := by
  classical
  by_cases h32 : 2 * n < 3 * t
  · rw [exactMass_of_three_mul_gt (by omega) htn h32]
    exact lines_card_le_of_three_mul_gt A total (by omega) htn h32
  push Not at h32
  set c := (t + 15) / 16 with hc_def
  have hc_le : c ≤ t := by omega
  have h16c_ge : t ≤ 16 * c := by omega
  set cut := t - c + 1 with hcut_def
  have h16cut : 15 * t ≤ 16 * cut := by omega
  set d := c - 2 with hd_def
  have h16d : 16 * d ≤ t := by omega
  have hcut_eq : cut + d = t - 1 := by omega
  set H := A.points.filter (fun x => cut ≤ A.w x) with hH_def
  set Q := A.points \ H with hQ_def
  set L := mass A.w Q with hL_def
  set h := H.card with hh_def
  set K := (A.away H).card with hK_def
  have hHsub : H ⊆ A.points := Finset.filter_subset _ _
  have hparts : L + mass A.w H = n := (Finset.sum_sdiff hHsub).trans total
  have hHcost : h * cut ≤ mass A.w H := by
    simpa [hh_def, mass] using Finset.sum_le_sum (s := H) (f := fun _ => cut) (g := A.w)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hL_cut : L ≤ n - h * cut := by omega
  have hcut_n : h * cut ≤ n := by omega
  have hlight : ∀ x ∈ Q, A.w x ≤ t - c := by
    intro x hx
    obtain ⟨hxP, hxH⟩ := Finset.mem_sdiff.mp hx
    have : ¬ cut ≤ A.w x := fun hge => hxH (Finset.mem_filter.mpr ⟨hxP, hge⟩)
    omega
  have hKpairs : K * (t * c) ≤ n * n := by
    have := A.away_pairs H c hc_le hlight
    rwa [total] at this
  have hKt2 : K * t ^ 2 ≤ 16 * n ^ 2 := by
    have h1 : K * t ^ 2 ≤ K * (t * (16 * c)) := Nat.mul_le_mul_left K (by nlinarith only [h16c_ge])
    have h2 : K * (t * (16 * c)) = 16 * (K * (t * c)) := by ring
    nlinarith only [h1, h2, hKpairs]
  have h16K : 16 * K ≤ n := by
    have h1 : 16 * K * t ^ 2 ≤ 256 * n ^ 2 := by nlinarith only [hKt2]
    have h2 : 16 * K * (256 * n) ≤ 16 * K * t ^ 2 := Nat.mul_le_mul_left _ hsq
    have hn_pos : 0 < n := by omega
    nlinarith only [h1, h2, hn_pos]
  have hQleL : Q.card ≤ L := card_le_mass_sub A Finset.sdiff_subset
  have hdecomp : A.lines.card ≤ K + h.choose 2 + ∑ x ∈ H, (A.solo H x).card :=
    decomposition_choose_two A H
  have hsolo_all : (∑ x ∈ H, (A.solo H x).card) ≤ h * Q.card := by
    simpa [hh_def] using Finset.sum_le_sum (s := H) (fun x _ => (A.solo_bounds H x).1)
  have hlines_coarse : A.lines.card ≤ K + h.choose 2 + h * (n - h * cut) := by
    have h1 : h * Q.card ≤ h * (n - h * cut) := Nat.mul_le_mul_left h (hQleL.trans hL_cut)
    omega
  -- Case 1: Zero centers (`h = 0`).
  by_cases hh0 : h = 0
  · have hcard : A.lines.card ≤ K := by
      rw [hh0] at hlines_coarse
      simpa using hlines_coarse
    have h1_feas : 1 ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hcand1 := candidateQuad_le_exactMass (n := n) (t := t) (h := 1) le_rfl h1_feas
    rw [candidateQuad_one (by omega) htn] at hcand1
    omega
  have hh_pos : 1 ≤ h := Nat.pos_of_ne_zero hh0
  -- Case 2: Small number of centers (`4 * h * t < n`).
  by_cases hsmall : 4 * h * t < n
  · have h2h_feas : 2 * h ≤ n / (t - 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by
        have h1 : 2 * h * (t - 1) ≤ 2 * h * t := Nat.mul_le_mul_left (2 * h) (Nat.sub_le t 1)
        have h2 : 2 * (2 * h * t) = 4 * h * t := by ring
        omega)
    have hcand := candidateQuad_le_exactMass (n := n) (t := t) (h := 2 * h) (by omega) h2h_feas
    have hcmp := arith_small_centers ht hh_pos hsmall hcut_n h16cut h16K
    exact hlines_coarse.trans (hcmp.trans hcand)
  push Not at hsmall
  -- Case 3: Large number of centers (`3 * n < 4 * h * t`).
  by_cases hlarge : 3 * n < 4 * h * t
  · have hh_ge2 : 2 ≤ h := by
      by_contra h1
      have heq : h = 1 := by omega
      rw [heq] at hlarge
      omega
    obtain ⟨hj_sub, hcmp⟩ := arith_large_centers ht hh_ge2 hlarge hcut_n h16cut hKt2
    have hj_feas : (h + 1) / 2 ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr hj_sub
    have hcand := candidateQuad_le_exactMass (n := n) (t := t) (h := (h + 1) / 2) (by omega) hj_feas
    exact hlines_coarse.trans (hcmp.trans hcand)
  push Not at hlarge
  -- Case 4: Middle range `n ≤ 4 * h * t ∧ 4 * h * t ≤ 3 * n`.
  have h4eq : 4 * (h * t) = 4 * h * t := by ring
  have hh_le_ht : h * (t - 1) ≤ h * t := Nat.mul_le_mul_left h (Nat.sub_le t 1)
  have hh_sub : h * (t - 1) ≤ n := by omega
  have hh_feas : h ≤ n / (t - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr hh_sub
  set Lh := n - h * (t - 1) with hLh_def
  have h4Lh : n ≤ 4 * Lh := by omega
  have h64hd : 64 * (h * d) ≤ 3 * n := by
    have hmd := Nat.mul_le_mul_left h h16d
    nlinarith only [hmd, hlarge]
  -- Subcase 4a: At least one weak center (`w ≥ 1`).
  set W := H.filter (fun x => A.w x < t - 1) with hW_def
  by_cases hw_pos : 0 < W.card
  · set w := W.card with hw_def
    have hw_le_h : w ≤ h := Finset.card_le_card (Finset.filter_subset _ _)
    have hH_mass : h * (t - 1) - w * d ≤ mass A.w H := by
      have hsplit : mass A.w H = mass A.w W + mass A.w (H \ W) := by
        rw [add_comm]; exact (Finset.sum_sdiff (Finset.filter_subset _ _)).symm
      have hW_mass : w * cut ≤ mass A.w W := by
        simpa [hw_def, mass] using Finset.sum_le_sum (s := W) (f := fun _ => cut) (g := A.w)
          (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2)
      have hS_mass : (h - w) * (t - 1) ≤ mass A.w (H \ W) := by
        have hScard : (H \ W).card = h - w := by
          rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
        have hSge : ∀ x ∈ H \ W, t - 1 ≤ A.w x := by
          intro x hx
          obtain ⟨hxH, hxW⟩ := Finset.mem_sdiff.mp hx
          by_contra hlt
          push Not at hlt
          exact hxW (Finset.mem_filter.mpr ⟨hxH, hlt⟩)
        simpa [hScard, mass] using Finset.sum_le_sum (s := H \ W) (f := fun _ => t - 1) (g := A.w) hSge
      have hwd_le : w * d ≤ h * (t - 1) := Nat.mul_le_mul hw_le_h (by omega)
      have hid : w * cut + (h - w) * (t - 1) = h * (t - 1) - w * d := by
        zify [hw_le_h, hwd_le, show 1 ≤ t by omega, show cut ≤ t - 1 by omega]
        have hcd : (cut : ℤ) + d = (t : ℤ) - 1 := by zify [show 1 ≤ t by omega] at hcut_eq; exact hcut_eq
        nlinarith only [hcd]
      omega
    have hL_weak : L ≤ Lh + w * d := by omega
    have hsolo_weak : 2 * (∑ x ∈ H, (A.solo H x).card) ≤ (2 * h - w) * L := by
      have hsplit : (∑ x ∈ H, (A.solo H x).card) =
          (∑ x ∈ W, (A.solo H x).card) + (∑ x ∈ H \ W, (A.solo H x).card) := by
        rw [add_comm]; exact (Finset.sum_sdiff (Finset.filter_subset _ _)).symm
      have hW_solo : 2 * (∑ x ∈ W, (A.solo H x).card) ≤ w * L := by
        rw [Finset.mul_sum]
        have hterm : ∀ x ∈ W, 2 * (A.solo H x).card ≤ L := by
          intro x hx
          have hlt : A.w x < t - 1 := (Finset.mem_filter.mp hx).2
          have h2le : 2 ≤ t - A.w x := by omega
          calc
            2 * (A.solo H x).card = (A.solo H x).card * 2 := Nat.mul_comm _ _
            _ ≤ (A.solo H x).card * (t - A.w x) := Nat.mul_le_mul_left _ h2le
            _ ≤ L := (A.solo_bounds H x).2
        simpa [hw_def] using Finset.sum_le_sum hterm
      have hS_solo : (∑ x ∈ H \ W, (A.solo H x).card) ≤ (h - w) * L := by
        have hScard : (H \ W).card = h - w := by
          rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
        simpa [hScard] using Finset.sum_le_sum (s := H \ W)
          (fun x _ => (A.solo_bounds H x).1.trans hQleL)
      have hid : w * L + 2 * ((h - w) * L) = (2 * h - w) * L := by
        zify [hw_le_h, show w ≤ 2 * h by omega]; ring
      omega
    have hquad_weak := arith_weak_centers hw_pos hw_le_h h4Lh h64hd h16K hL_weak
    have hlines_le : A.lines.card ≤ candidateQuad n t h := by
      unfold candidateQuad
      rw [← hLh_def]
      omega
    exact hlines_le.trans (candidateQuad_le_exactMass hh_pos hh_feas)
  -- Subcase 4b: All centers are strong (`w = 0`).
  push Not at hw_pos
  have hstrong : ∀ x ∈ H, t - 1 ≤ A.w x := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have : x ∈ W := Finset.mem_filter.mpr ⟨hx, hlt⟩
    have := Finset.card_pos.mpr ⟨x, this⟩
    omega
  have hH_strong : h * (t - 1) ≤ mass A.w H := by
    simpa [hh_def, mass] using Finset.sum_le_sum (s := H) (f := fun _ => t - 1) (g := A.w) hstrong
  have hL_le_Lh : L ≤ Lh := by omega
  set D := Lh - Q.card with hD_def
  have hQ_le_Lh : Q.card ≤ Lh := hQleL.trans hL_le_Lh
  have hQD : Q.card + D = Lh := Nat.add_sub_of_le hQ_le_Lh
  set rh := richLightCap Lh t with hrh_def
  have hK_le : K ≤ rh + h * D := by
    by_contra hKgt
    push Not at hKgt
    have hhD_lt : h * D < K := by omega
    obtain ⟨h4D_lt, h2K_from_T⟩ := arith_strong_K_bound ht hsq hh_pos hsmall hKt2 hhD_lt
    let T := (3 * t + 3) / 4
    have h4T_ge : 3 * t ≤ 4 * T := by omega
    have hTD : T + D ≤ t := by omega
    have hmoment := A.light_pair_moment H (A.away H) Subset.rfl D T
      (by rw [← hQ_def, ← hL_def]; omega) hTD
    have hQ_le_n : Q.card ≤ n := hQ_le_Lh.trans (Nat.sub_le _ _)
    have h2K_lt_t : 2 * K < t := h2K_from_T T h4T_ge
      (hmoment.trans (Nat.mul_le_mul_right _ hQ_le_n))
    set k := rh + h * D + 1 with hk_def
    have hk_le_K : k ≤ K := by omega
    obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq hk_le_K
    have hdef := A.light_deficit_bound H G hGsub Lh hL_le_Lh
    rw [hGcard] at hdef
    have hrh_le : rh ≤ t - 2 := richLightCap_le_sub_two ht hsq (Nat.sub_le _ _)
    have hlt_next : Lh < lightLineMass (rh + 1) t :=
      lt_lightLineMass_succ_richLightCap (by omega) (by omega)
    have hk_lt_t : k ≤ t := by omega
    have hstep := lightLineMass_step_ge (t := t) (r₁ := rh + 1) (r₂ := k) (by omega) hk_lt_t
    have hk_sub : k - (rh + 1) = h * D := by omega
    rw [hk_sub] at hstep
    have hslope : k - 1 ≤ h * (t - k + 1) :=
      (show k - 1 ≤ t - k + 1 by omega).trans (Nat.le_mul_of_pos_left _ hh_pos)
    have hDmul : (k - 1) * D ≤ h * D * (t - k + 1) := by
      calc
        (k - 1) * D ≤ h * (t - k + 1) * D := Nat.mul_le_mul_right D hslope
        _ = h * D * (t - k + 1) := by ring
    have hchoose_le : k.choose 2 ≤ k * t := choose_two_le_mul k t hk_lt_t
    have hchoose_rh : (rh + 1).choose 2 ≤ (rh + 1) * t := choose_two_le_mul (rh + 1) t (by omega)
    unfold lightLineMass at hstep hlt_next
    change k * t ≤ Lh + k.choose 2 + (k - 1) * D at hdef
    omega
  have hlines_cand : A.lines.card ≤ candidateMass n t h := by
    unfold candidateMass candidateQuad
    have hmulQ : h * Q.card + h * D = h * Lh := by
      rw [← Nat.mul_add, hQD]
    change A.lines.card ≤ h * (n - h * (t - 1)) + h.choose 2 + richLightCap (n - h * (t - 1)) t
    rw [← hLh_def, ← hrh_def]
    omega
  exact hlines_cand.trans (candidateMass_le_exactMass hh_pos hh_feas)

#print axioms richLightCap_le_sub_two
#print axioms exactMass_of_three_mul_gt
#print axioms exactMass_eq_two_candidates
#print axioms multiLines_card_le_choose_two
#print axioms decomposition_choose_two
#print axioms lines_card_le_of_three_mul_gt
#print axioms uniform_arrangement_upper

end Arrangements
end ArkLib.ProximityGap.Frontier.ExactRepetitionMassUpper
