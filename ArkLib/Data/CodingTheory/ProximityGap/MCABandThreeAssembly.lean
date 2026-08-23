/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandThreeInfra
import ArkLib.Data.CodingTheory.ProximityGap.MCAHalfDistanceStaircase

/-!
# Round 4 / R4.2 (#357): the band-3 collapse theorem — `b = 3` of the corrected general law

The deep-core dichotomy assembly over the landed infrastructure
(`MCABandThreeInfra`: `extract3`, `ext_at`; `MCABandThreeCoredCollapse`: `cored_collapse`;
`MCABandTwoCollapse`: the pairing lemmas):

**`badScalar_card_le_three_of_dist7`** — every linear code with no nonzero codeword
supported on `≤ 6` points (distance `≥ 7 = 2b + 1`) has at most `3` bad scalars per stack
at every radius with `δ·n < 3`. With the doubled-column counterexample at `d = 6`
(`MCAHalfDistanceGeneralRefuted`) the distance threshold is **sharp** for general linear
codes. Corollaries: `generalStaircase_b3 : LinearStaircaseUpper C 3` (the first open
instance of `GeneralStaircaseConjecture`) and
`epsMCA_le_three_div_card_of_dist7 : ε_mca(C, δ) ≤ 3/|F|` on the whole band.

**Proof.** Four distinct bad scalars yield puncture data `(P_a, w_a)`, `|P_a| ≤ 2`
(`extract3`). Nested puncture sets are dead (`pairJoint_of_shared_witness`); two codeword
line points are dead (`pairJoint_of_two_codeword_points`). If some scalar's line point is
not a codeword, it has a **deep point**: a `j` lying in at least three of the four puncture
sets (`ext_at`: otherwise some triple extends the agreement across `j`). But a deep point
kills outright (`deep_dead`): its three host scalars are all cored at `j` — degenerate
hosts (`P = {j}`) are nested in the others, otherwise `P_i = {j, p_i}` with distinct
private punctures, and `cored_collapse` (which needs only distance `≥ 5`) finishes. So all
four line points are codewords — dead. ∎

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandThreeAssembly

open ProximityGap.MCABandTwoCollapse ProximityGap.MCABandThreeCoredCollapse
open ProximityGap.MCABandThreeInfra

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The band-3 collapse at `d ≥ 7`.** -/
theorem badScalar_card_le_three_of_dist7 (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < 3)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) Finset.univ).card ≤ 3 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨γ₁, γ₂, γ₃, γ₄, hm1, hm2, hm3, hm4, h12, h13, h14, h23, h24, h34⟩ :=
    exists_four_of_three_lt hgt
  rw [Finset.mem_filter] at hm1 hm2 hm3 hm4
  obtain ⟨P₁, w₁, hPc₁, hw₁, hagg₁, hno₁⟩ := extract3 C hn hδ hm1.2
  obtain ⟨P₂, w₂, hPc₂, hw₂, hagg₂, hno₂⟩ := extract3 C hn hδ hm2.2
  obtain ⟨P₃, w₃, hPc₃, hw₃, hagg₃, hno₃⟩ := extract3 C hn hδ hm3.2
  obtain ⟨P₄, w₄, hPc₄, hw₄, hagg₄, hno₄⟩ := extract3 C hn hδ hm4.2
  set γs : Fin 4 → F := ![γ₁, γ₂, γ₃, γ₄] with hγs
  set Ps : Fin 4 → Finset ι := ![P₁, P₂, P₃, P₄] with hPs
  set ws : Fin 4 → ι → A := ![w₁, w₂, w₃, w₄] with hws
  have hγne : ∀ a b : Fin 4, a ≠ b → γs a ≠ γs b := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact absurd rfl (by exact hab)
        | exact h12 | exact h13 | exact h14 | exact h23 | exact h24 | exact h34
        | exact Ne.symm h12 | exact Ne.symm h13 | exact Ne.symm h14
        | exact Ne.symm h23 | exact Ne.symm h24 | exact Ne.symm h34
  have hPc : ∀ a : Fin 4, (Ps a).card ≤ 2 := by
    intro a
    fin_cases a <;> first | exact hPc₁ | exact hPc₂ | exact hPc₃ | exact hPc₄
  have hwmem : ∀ a : Fin 4, ws a ∈ C := by
    intro a
    fin_cases a <;> first | exact hw₁ | exact hw₂ | exact hw₃ | exact hw₄
  have hag : ∀ (a : Fin 4) (j : ι), j ∉ Ps a → ws a j = u 0 j + γs a • u 1 j := by
    intro a
    fin_cases a <;> first | exact hagg₁ | exact hagg₂ | exact hagg₃ | exact hagg₄
  have hno : ∀ a : Fin 4,
      ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ \ Ps a) (u 0) (u 1) := by
    intro a
    fin_cases a <;> first | exact hno₁ | exact hno₂ | exact hno₃ | exact hno₄
  -- DEAD END 1: nested puncture sets
  have hnest : ∀ a b : Fin 4, a ≠ b → Ps b ⊆ Ps a → False := by
    intro a b hab hsub
    refine hno a (pairJoint_of_shared_witness C (hγne a b hab) (hwmem a) (hwmem b)
      (fun j hj => hag a j (Finset.mem_sdiff.mp hj).2)
      (fun j hj => hag b j fun hjb => (Finset.mem_sdiff.mp hj).2 (hsub hjb)))
  -- DEAD END 2: two codeword line points
  have hU2 : ∀ a b : Fin 4, a ≠ b →
      (u 0 + γs a • u 1) ∈ C → (u 0 + γs b • u 1) ∈ C → False := by
    intro a b hab hya hyb
    exact hno a (pairJoint_of_two_codeword_points C (hγne a b hab) hya hyb _)
  -- the indexed extension engine
  have hext : ∀ a b c : Fin 4, a ≠ b → a ≠ c → ∀ j : ι,
      j ∉ Ps a → j ∉ Ps c → ws b j = u 0 j + γs b • u 1 j := by
    intro a b c hab hac j hja hjc
    exact ext_at C hC (hγne a b hab) (hγne a c hac) (hwmem a) (hwmem b) (hwmem c)
      (hPc a) (hPc b) (hPc c) (hag a) (hag b) (hag c) hja hjc
  -- DEAD END 3 (the heart): a deep point kills via the cored collapse
  have hdeep_dead : ∀ (j : ι) (i₁ i₂ i₃ : Fin 4), i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
      j ∈ Ps i₁ → j ∈ Ps i₂ → j ∈ Ps i₃ → False := by
    intro j i₁ i₂ i₃ hi12 hi13 hi23 hj1 hj2 hj3
    -- extract private punctures (degenerate hosts are nested — dead)
    have hpriv : ∀ a b : Fin 4, a ≠ b → j ∈ Ps a → j ∈ Ps b →
        ∃ p, p ∈ Ps a ∧ p ≠ j := by
      intro a b hab hja hjb
      by_contra hcon
      push Not at hcon
      refine hnest b a (Ne.symm hab) fun y hy => ?_
      have hyj : y = j := hcon y hy
      rw [hyj]
      exact hjb
    obtain ⟨p₁, hp₁mem, hp₁j⟩ := hpriv i₁ i₂ hi12 hj1 hj2
    obtain ⟨p₂, hp₂mem, hp₂j⟩ := hpriv i₂ i₁ (Ne.symm hi12) hj2 hj1
    obtain ⟨p₃, hp₃mem, hp₃j⟩ := hpriv i₃ i₁ (Ne.symm hi13) hj3 hj1
    -- each host is exactly {j, p}
    have hPeq : ∀ (a : Fin 4) (p : ι), j ∈ Ps a → p ∈ Ps a → p ≠ j →
        Ps a = {j, p} := by
      intro a p hja hpa hpj
      have hsub : ({j, p} : Finset ι) ⊆ Ps a := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hja
        · rw [Finset.mem_singleton.mp hy]
          exact hpa
      have hcard2 : (({j, p} : Finset ι)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by
          rw [Finset.mem_singleton]
          exact fun h => hpj h.symm), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hPc a)).symm
    have hP1 : Ps i₁ = {j, p₁} := hPeq i₁ p₁ hj1 hp₁mem hp₁j
    have hP2 : Ps i₂ = {j, p₂} := hPeq i₂ p₂ hj2 hp₂mem hp₂j
    have hP3 : Ps i₃ = {j, p₃} := hPeq i₃ p₃ hj3 hp₃mem hp₃j
    -- private punctures are pairwise distinct (equal pairs are nested)
    have hpne : ∀ (a b : Fin 4) (p q : ι), a ≠ b → Ps a = {j, p} → Ps b = {j, q} →
        p ≠ q := by
      rintro a b p q hab hPa hPb rfl
      exact hnest a b hab (by rw [hPa, hPb])
    have hp12 : p₁ ≠ p₂ := hpne i₁ i₂ p₁ p₂ hi12 hP1 hP2
    have hp13 : p₁ ≠ p₃ := hpne i₁ i₃ p₁ p₃ hi13 hP1 hP3
    have hp23 : p₂ ≠ p₃ := hpne i₂ i₃ p₂ p₃ hi23 hP2 hP3
    -- the agreement bridges: off {j, p_a}
    have hagb : ∀ (a : Fin 4) (p : ι), Ps a = {j, p} →
        ∀ y : ι, y ≠ j → y ≠ p → ws a y = u 0 y + γs a • u 1 y := by
      intro a p hPa y hyj hyp
      refine hag a y ?_
      rw [hPa]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hyj, hyp⟩
    -- the cored collapse finishes
    refine cored_collapse C (noWeightLE4_of_LE6 hC) hp12 hp13 hp23 hp₁j hp₂j hp₃j
      (hγne i₁ i₂ hi12) (hγne i₁ i₃ hi13) (hγne i₂ i₃ hi23)
      (hwmem i₁) (hwmem i₂) (hwmem i₃)
      (hagb i₁ p₁ hP1) (hagb i₂ p₂ hP2) (hagb i₃ p₃ hP3)
      (S₂ := Finset.univ \ Ps i₂) (fun y hy => ?_) (hno i₂)
    intro hyj
    have hyP : y ∉ Ps i₂ := (Finset.mem_sdiff.mp hy).2
    rw [hyj] at hyP
    exact hyP hj2
  -- CLASSIFICATION: every line point must be a codeword
  have hYall : ∀ b : Fin 4, (u 0 + γs b • u 1) ∈ C := by
    intro b
    by_contra hY
    -- a disagreement point exists and lies in P_b
    obtain ⟨j, hjne⟩ : ∃ j : ι, ws b j ≠ u 0 j + γs b • u 1 j := by
      by_contra hall
      push Not at hall
      apply hY
      have heq : u 0 + γs b • u 1 = ws b := by
        funext y
        show u 0 y + γs b • u 1 y = ws b y
        exact (hall y).symm
      rw [heq]
      exact hwmem b
    have hjPb : j ∈ Ps b := by
      by_contra hjb
      exact hjne (hag b j hjb)
    -- the three others of b
    obtain ⟨o₁, o₂, o₃, ho₁b, ho₂b, ho₃b, ho₁₂, ho₁₃, ho₂₃⟩ :
        ∃ o₁ o₂ o₃ : Fin 4, o₁ ≠ b ∧ o₂ ≠ b ∧ o₃ ≠ b ∧ o₁ ≠ o₂ ∧ o₁ ≠ o₃ ∧ o₂ ≠ o₃ := by
      fin_cases b
      · exact ⟨1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · exact ⟨0, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · exact ⟨0, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · exact ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩
    -- j is in at least two of the others' puncture sets — then deep_dead fires
    by_cases hA : j ∈ Ps o₁
    · by_cases hB : j ∈ Ps o₂
      · -- deep at {b, o₁, o₂}
        exact hdeep_dead j b o₁ o₂ (Ne.symm ho₁b) (Ne.symm ho₂b) ho₁₂ hjPb hA hB
      · by_cases hCm : j ∈ Ps o₃
        · exact hdeep_dead j b o₁ o₃ (Ne.symm ho₁b) (Ne.symm ho₃b) ho₁₃ hjPb hA hCm
        · -- j avoids o₂ and o₃: the triple (o₂, b, o₃) extends w_b at j
          exact hjne (hext o₂ b o₃ ho₂b ho₂₃ j hB hCm)
    · by_cases hB : j ∈ Ps o₂
      · by_cases hCm : j ∈ Ps o₃
        · exact hdeep_dead j b o₂ o₃ (Ne.symm ho₂b) (Ne.symm ho₃b) ho₂₃ hjPb hB hCm
        · exact hjne (hext o₁ b o₃ ho₁b ho₁₃ j hA hCm)
      · exact hjne (hext o₁ b o₂ ho₁b ho₁₂ j hA hB)
  exact hU2 0 1 (by decide) (hYall 0) (hYall 1)

open Classical in
/-- The `b = 3` instance of the corrected general law: `LinearStaircaseUpper C 3` for
distance `≥ 7`. -/
theorem generalStaircase_b3 (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    (hn : 3 ≤ Fintype.card ι) :
    ProximityGap.MCAHalfDistanceStaircase.LinearStaircaseUpper C 3 := by
  intro δ hδ u
  refine badScalar_card_le_three_of_dist7 C hC hn ?_ u
  exact_mod_cast hδ

open Classical in
/-- `ε_mca ≤ 3/|F|` on the whole band `δ·n < 3`, for distance `≥ 7` — sharp on both sides
(spike floor below, the `d = 6` doubled-column counterexample for the distance bound). -/
theorem epsMCA_le_three_div_card_of_dist7 (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < 3) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 3 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_three_of_dist7 C hC hn hδ u

/-! ## Source audit -/

#print axioms badScalar_card_le_three_of_dist7
#print axioms generalStaircase_b3
#print axioms epsMCA_le_three_div_card_of_dist7

end ProximityGap.MCABandThreeAssembly
