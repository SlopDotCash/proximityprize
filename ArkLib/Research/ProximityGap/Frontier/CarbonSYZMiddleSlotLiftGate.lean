/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Extensions.Data.CodingTheory.ReedSolomon
import ArkLib.Research.ProximityGap.Frontier._F1RegionSyzygyInterface
import ArkLib.Research.ProximityGap.Frontier._SYZ38SylvesterInjectivity
import ArkLib.Research.ProximityGap.Frontier._SYZ65RankNullity
import ArkLib.Research.ProximityGap.Frontier._SYZ72F41MiddleSlotCertificate

/-!
# Algebraic Stack-Lift Gate for F1 Middle-Slot and Region-Syzygy Witnesses

This module proves the algebraic region-to-stack lift gate connecting on-domain region-syzygy
triples (`_F1RegionSyzygyInterface.lean`, `SYZ70–SYZ72`) to genuine `mcaEvent` / `mcaBadCount`
word stacks via syndrome-rank and μ-basis window dimension bounds:

1. **Universal Syndrome-Rank-1 Collapse (`mcaBadCount_le_one_of_collinear_syndrome`,
   `mcaBadCount_le_one_of_finrank_quotient_le_one`).**
   Over any finite field `F` and linear code `C ≤ F^ι`, if a stack `(u₀, u₁)` has syndrome cosets
   `C.mkQ u₀, C.mkQ u₁` inside a subspace of `F`-dimension `≤ 1`, then `mcaBadCount C δ u₀ u₁ ≤ 1`
   at **every** proximity radius `δ` (zero if `u₁ ∈ C`, and at most the unique `γ₀` with
   `u₀ + γ₀ • u₁ ∈ C` otherwise).
2. **Exact In-Budget Syzygy Window Dimension (`finrank_windowKD_bandStack`).**
   Combining `SYZ65.degree_sum_unconditional` with `SYZ64.finrank_windowKD` and G172 interior slack
   proves that for every pairwise-coprime triple `(WAB, WAC, WBC)` of degrees `(a, b, c)` satisfying
   `BandStack a b c t k` and `MinimalSyzygyDegree WAB WAC WBC δ₁`, the second μ-basis generator has
   degree `n₂ > k - t` and the in-budget window `windowKD ![a, b, c] (ker syzygyMap) (k - 1 - t)`
   has exact `K`-dimension `(k - t) - δ₁`. Whenever `k - t ≤ δ₁`, `SYZ38.SylvesterInjective` holds
   unconditionally — including across the entire PR #528 family `(d, d, d, d - 2, 2d - 1, d + 1)`.
3. **3-Core Cocycle Injection and Middle-Slot Lift Gate
   (`middleSlot_666_threeCore_mcaBadCount_le_one`,
   `zmod41_middleSlot_no_overBudget_threeCore_lift`).**
   On any full-partition `VennRegions` + `BandStack` + `MinimalSyzygyDegree` witness, the mismatch
   cocycle injects locally-RS 3-core words modulo `RS[Ω, k]` into the in-budget syzygy window of
   dimension `(k - t) - δ₁`. Consequently:
   - Every PR #528 `(d, d, d, d - 2, 2d - 1, d + 1)` 3-core pair-degenerate stack is a global
     codeword pair with `mcaBadCount = 0`.
   - Every `(6, 6, 6, 2, 10, 7)` first-middle-slot witness (`SYZ70–SYZ72`, over **every** finite
     field `F`, including `SYZ72.zmod41_regionSyzygyRealizable` and `F_181`) and every `(4, 4, 4, 2,
     7, 4)` witness (`SYZ50`) has `mcaBadCount ≤ 1` at every radius `δ`, so no such witness can
     lift to a multi-scalar (`≥ 2`) or over-budget (`> 2k - 1`) 3-core pair-degenerate MCA stack.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonSYZMiddleSlotLiftGate

open Finset Polynomial Module Submodule
open scoped NNReal

/-! ## 1. Universal syndrome-rank-1 collapse for `mcaBadCount` -/

section SyndromeRankOneCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- If the slope row `u₁` belongs to the linear code `C`, no scalar `γ` can fire `mcaEvent`: any
line agreement `w = u₀ + γ • u₁` on `S` yields the joint codeword pair `(w - γ • u₁, u₁)` on `S`. -/
theorem not_mcaEvent_of_snd_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ : ι → A) {u₁ : ι → A} (hu₁ : u₁ ∈ C) (γ : F) :
    ¬ _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, _hS, ⟨w, hw, hline⟩, hno⟩
  apply hno
  refine ⟨w - γ • u₁, C.sub_mem hw (C.smul_mem γ hu₁), u₁, hu₁, ?_⟩
  intro i hi
  refine ⟨?_, rfl⟩
  simp only [Pi.sub_apply, Pi.smul_apply, hline i hi, add_sub_cancel_right]

/-- If `u₁ ∈ C`, `mcaBadCount C δ u₀ u₁ = 0` at every radius `δ`. -/
theorem mcaBadCount_eq_zero_of_snd_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ : ι → A) {u₁ : ι → A} (hu₁ : u₁ ∈ C) :
    _root_.ProximityGap.mcaBadCount (F := F) (C : Set (ι → A)) δ u₀ u₁ = 0 :=
  _root_.ProximityGap.mcaBadCount_eq_zero_of_forall_not_mcaEvent
    (C : Set (ι → A)) δ u₀ u₁ (not_mcaEvent_of_snd_mem C δ u₀ hu₁)

/-- If both rows `u₀, u₁` belong to `C`, `mcaBadCount C δ u₀ u₁ = 0` at every radius `δ`. -/
theorem mcaBadCount_eq_zero_of_both_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (_hu₀ : u₀ ∈ C) (hu₁ : u₁ ∈ C) :
    _root_.ProximityGap.mcaBadCount (F := F) (C : Set (ι → A)) δ u₀ u₁ = 0 :=
  mcaBadCount_eq_zero_of_snd_mem C δ u₀ hu₁

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [Fintype A] [DecidableEq A] in
/-- **Unique bad scalar on a collinear-syndrome line.**
If `u₀ + γ₀ • u₁ ∈ C`, then `γ₀` is the *only* scalar capable of firing `mcaEvent`: any `γ ≠ γ₀`
whose fold agrees with `w ∈ C` on `S` pins `u₁` to `(γ - γ₀)⁻¹ • (w - (u₀ + γ₀ • u₁)) ∈ C` on `S`
and hence pins `u₀` to a codeword on `S` as well, violating `¬ pairJointAgreesOn`. -/
theorem mcaEvent_eq_of_combo_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} {γ₀ γ : F} (hcombo : u₀ + γ₀ • u₁ ∈ C)
    (hγ : _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) :
    γ = γ₀ := by
  by_contra hne
  obtain ⟨S, _hS, ⟨w, hw, hline⟩, hno⟩ := hγ
  have hsub_ne : γ - γ₀ ≠ 0 := sub_ne_zero.mpr hne
  set c₀ : ι → A := u₀ + γ₀ • u₁
  set v₁ : ι → A := (γ - γ₀)⁻¹ • (w - c₀)
  set v₀ : ι → A := c₀ - γ₀ • v₁
  have hv₁C : v₁ ∈ C := C.smul_mem _ (C.sub_mem hw hcombo)
  have hv₀C : v₀ ∈ C := C.sub_mem hcombo (C.smul_mem _ hv₁C)
  apply hno
  refine ⟨v₀, hv₀C, v₁, hv₁C, ?_⟩
  intro i hi
  have hdiff : w i - c₀ i = (γ - γ₀) • u₁ i := by
    simp only [c₀, Pi.add_apply, Pi.smul_apply, hline i hi]
    rw [sub_smul]
    abel
  have hv₁i : v₁ i = u₁ i := by
    simp only [v₁, Pi.smul_apply, Pi.sub_apply, hdiff]
    exact inv_smul_smul₀ hsub_ne (u₁ i)
  refine ⟨?_, hv₁i⟩
  simp only [v₀, c₀, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hv₁i, add_sub_cancel_right]

/-- **Syndrome-Rank-1 Collapse (span-of-coset form).**
If `C.mkQ u₀` and `C.mkQ u₁` lie in a common cyclic line `F ∙ C.mkQ z` inside `(ι → A) ⧸ C`, then
`mcaBadCount C δ u₀ u₁ ≤ 1` at every radius `δ`. -/
theorem mcaBadCount_le_one_of_collinear_syndrome (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (z : ι → A)
    (hu₀ : C.mkQ u₀ ∈ F ∙ C.mkQ z) (hu₁ : C.mkQ u₁ ∈ F ∙ C.mkQ z) :
    _root_.ProximityGap.mcaBadCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ 1 := by
  classical
  obtain ⟨a₀, ha₀⟩ := Submodule.mem_span_singleton.mp hu₀
  obtain ⟨a₁, ha₁⟩ := Submodule.mem_span_singleton.mp hu₁
  by_cases ha₁0 : a₁ = 0
  · have hu₁C : u₁ ∈ C := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change C.mkQ u₁ = 0
      rw [← ha₁, ha₁0, zero_smul]
    rw [mcaBadCount_eq_zero_of_snd_mem C δ u₀ hu₁C]
    omega
  · set γ₀ : F := -(a₀ * a₁⁻¹)
    have hcombo : u₀ + γ₀ • u₁ ∈ C := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change C.mkQ (u₀ + γ₀ • u₁) = 0
      rw [map_add, map_smul, ← ha₀, ← ha₁, smul_smul, ← add_smul]
      have hscal : a₀ + γ₀ * a₁ = 0 := by
        simp only [γ₀]
        rw [neg_mul, inv_mul_cancel_right₀ ha₁0, add_neg_cancel]
      rw [hscal, zero_smul]
    have hsub :
        Finset.univ.filter (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) ⊆
          {γ₀} := by
      intro γ hmem
      rw [Finset.mem_singleton]
      exact mcaEvent_eq_of_combo_mem C δ hcombo (Finset.mem_filter.mp hmem).2
    calc _root_.ProximityGap.mcaBadCount (F := F) (C : Set (ι → A)) δ u₀ u₁
        = (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card := rfl
      _ ≤ ({γ₀} : Finset F).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton γ₀

/-- **Syndrome-Rank-1 Collapse (subspace-dimension form).**
If `C.mkQ u₀` and `C.mkQ u₁` lie in a submodule `M ≤ (ι → A) ⧸ C` with `finrank F M ≤ 1`, then
`mcaBadCount C δ u₀ u₁ ≤ 1` at every radius `δ`. -/
theorem mcaBadCount_le_one_of_finrank_quotient_le_one (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (M : Submodule F ((ι → A) ⧸ C))
    (hfin : Module.finrank F M ≤ 1) (hu₀ : C.mkQ u₀ ∈ M) (hu₁ : C.mkQ u₁ ∈ M) :
    _root_.ProximityGap.mcaBadCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ 1 := by
  by_cases hq₁ : C.mkQ u₁ = 0
  · have hu₁C : u₁ ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hq₁
    rw [mcaBadCount_eq_zero_of_snd_mem C δ u₀ hu₁C]
    omega
  · set m₁ : M := ⟨C.mkQ u₁, hu₁⟩
    have hm₁_ne : m₁ ≠ 0 := fun h => hq₁ (congrArg Subtype.val h)
    have hspan_fr : Module.finrank F (F ∙ m₁) = 1 := finrank_span_singleton hm₁_ne
    have hM_fr : Module.finrank F M = 1 := by
      have hle := Submodule.finrank_le (F ∙ m₁)
      omega
    have htop : (F ∙ m₁) = ⊤ := Submodule.eq_top_of_finrank_eq (hspan_fr.trans hM_fr.symm)
    have hm₀ : (⟨C.mkQ u₀, hu₀⟩ : M) ∈ (F ∙ m₁) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a₀, ha₀⟩ := Submodule.mem_span_singleton.mp hm₀
    have hu₀_span : C.mkQ u₀ ∈ F ∙ C.mkQ u₁ :=
      Submodule.mem_span_singleton.mpr ⟨a₀, congrArg Subtype.val ha₀⟩
    have hu₁_span : C.mkQ u₁ ∈ F ∙ C.mkQ u₁ := Submodule.mem_span_singleton_self _
    exact mcaBadCount_le_one_of_collinear_syndrome C δ u₁ hu₀_span hu₁_span

end SyndromeRankOneCollapse

/-! ## 2. Exact in-budget syzygy window dimension formula on `BandStack` -/

section WindowDimensionFormula

variable {K : Type*} [Field K]

private noncomputable def windowToDom (d : Fin 3 → ℕ)
    (N : Submodule K[X] (Fin 3 → K[X])) (D : ℕ) :
    SYZ64.windowKD d N D →ₗ[K] SYZ65.Dom K d D where
  toFun w :=
    (⟨w.1 0, SYZ64.mem_degreeLT_of_pdeg_le (le_trans (SYZ62.pterm_le_pdeg d w.1 0) w.2.2)⟩,
      ⟨w.1 1, SYZ64.mem_degreeLT_of_pdeg_le (le_trans (SYZ62.pterm_le_pdeg d w.1 1) w.2.2)⟩,
      ⟨w.1 2, SYZ64.mem_degreeLT_of_pdeg_le (le_trans (SYZ62.pterm_le_pdeg d w.1 2) w.2.2)⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private instance instFiniteDimensionalWindowKD (d : Fin 3 → ℕ)
    (N : Submodule K[X] (Fin 3 → K[X])) (D : ℕ) :
    FiniteDimensional K (SYZ64.windowKD d N D) := by
  refine FiniteDimensional.of_injective (windowToDom d N D) fun x y h => ?_
  apply Subtype.ext
  funext i
  fin_cases i
  · exact congrArg Subtype.val (congrArg Prod.fst h)
  · exact congrArg Subtype.val (congrArg (fun p => p.2.1) h)
  · exact congrArg Subtype.val (congrArg (fun p => p.2.2) h)

private theorem slot_pterm_le_iff {gen r : K[X]} {m D : ℕ}
    (hgen : gen ≠ 0) (hdeg : gen.natDegree = m) :
    r.degree + (m : WithBot ℕ) ≤ (D : WithBot ℕ) ↔ (gen * r).natDegree ≤ D := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [degree_zero, mul_zero, natDegree_zero]
    exact ⟨fun _ => Nat.zero_le D, fun _ => bot_le⟩
  · rw [degree_eq_natDegree hr, ← Nat.cast_add, Nat.cast_le, natDegree_mul hgen hr, hdeg]
    omega

/-- Equivalence between `SYZ62.pdeg ![a, b, c] w ≤ D` and the three `F1RegionSyzygy` slot
product-degree bounds `(W_slot * w_slot).natDegree ≤ D`. -/
theorem pdeg_le_iff_slot_natDegree_le {WAB WAC WBC : K[X]} {a b c D : ℕ}
    (hAB0 : WAB ≠ 0) (hAC0 : WAC ≠ 0) (hBC0 : WBC ≠ 0)
    (hdAB : WAB.natDegree = a) (hdAC : WAC.natDegree = b) (hdBC : WBC.natDegree = c)
    (w : Fin 3 → K[X]) :
    SYZ62.pdeg ![a, b, c] w ≤ (D : WithBot ℕ) ↔
      (WAB * w 0).natDegree ≤ D ∧ (WAC * w 1).natDegree ≤ D ∧ (WBC * w 2).natDegree ≤ D := by
  simp only [SYZ62.pdeg, SYZ62.pterm, max_le_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [slot_pterm_le_iff hAB0 hdAB, slot_pterm_le_iff hAC0 hdAC, slot_pterm_le_iff hBC0 hdBC]
  tauto

/-- **Exact two-ramp window dimension from `MinimalSyzygyDegree`.**
For any pairwise-coprime triple `(WAB, WAC, WBC)` of degrees `(a, b, c)` with minimal syzygy
product-degree `δ₁`, the μ-basis degrees are `(δ₁, a + b + c - δ₁)` with `δ₁ ≤ a + b + c - δ₁`,
and for every `D : ℕ`,
`finrank K (windowKD ![a, b, c] (ker syzygyMap) D) = (D + 1 - δ₁) + (D + 1 - (a + b + c - δ₁))`. -/
theorem finrank_windowKD_of_minimalSyzygy {WAB WAC WBC : K[X]} {a b c δ₁ : ℕ}
    (hAB0 : WAB ≠ 0) (hAC0 : WAC ≠ 0) (hBC0 : WBC ≠ 0)
    (hdAB : WAB.natDegree = a) (hdAC : WAC.natDegree = b) (hdBC : WBC.natDegree = c)
    (hcopAB : IsCoprime WAB WAC) (hcopAC : IsCoprime WAB WBC)
    (hmin : F1RegionSyzygy.MinimalSyzygyDegree WAB WAC WBC δ₁) :
    δ₁ ≤ a + b + c - δ₁ ∧
      ∀ D : ℕ,
        Module.finrank K
            (SYZ64.windowKD ![a, b, c] (LinearMap.ker (SYZ61.syzygyMap WAB WAC WBC)) D) =
          (D + 1 - δ₁) + (D + 1 - (a + b + c - δ₁)) := by
  obtain ⟨e₁, e₂, n₁, n₂, he₁N, _he₂N, hpd₁, hpd₂, hn₁₂, hpair, hspan, hsum⟩ :=
    SYZ65.degree_sum_unconditional (d := ![a, b, c]) hAB0 hAC0 hBC0
      (by simpa using hdAB.symm)
      (by simpa using hdAC.symm)
      (by simpa using hdBC.symm)
      hcopAB hcopAC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hsum
  have hn₁_eq : n₁ = δ₁ := by
    apply le_antisymm
    · obtain ⟨⟨sAB, sAC, sBC, hsyz, hnz, hs0, hs1, hs2⟩, _⟩ := hmin
      set w : Fin 3 → K[X] := ![sAB, sAC, sBC]
      have hwN : w ∈ LinearMap.ker (SYZ61.syzygyMap WAB WAC WBC) := by
        rw [LinearMap.mem_ker, SYZ61.syzygyMap_apply]
        simpa only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] using hsyz
      have hw_pdeg : SYZ62.pdeg ![a, b, c] w ≤ (δ₁ : WithBot ℕ) :=
        (pdeg_le_iff_slot_natDegree_le hAB0 hAC0 hBC0 hdAB hdAC hdBC w).mpr ⟨hs0, hs1, hs2⟩
      rw [hspan, Submodule.mem_span_pair] at hwN
      obtain ⟨q₁, q₂, hqw⟩ := hwN
      have hcombo := SYZ64.pdeg_combo_ge hpd₁ hpd₂ hpair q₁ q₂
      rw [hqw] at hcombo
      have hq_not_both : q₁ ≠ 0 ∨ q₂ ≠ 0 := by
        by_contra hboth
        push Not at hboth
        rw [hboth.1, hboth.2, zero_smul, zero_smul, add_zero] at hqw
        apply hnz
        exact ⟨congrFun hqw.symm 0, congrFun hqw.symm 1, congrFun hqw.symm 2⟩
      rcases hq_not_both with hq₁ | hq₂
      · have hle1 : SYZ62.pdeg ![a, b, c] (q₁ • e₁) ≤ (δ₁ : WithBot ℕ) :=
          le_trans (le_max_left _ _) (le_trans hcombo hw_pdeg)
        rw [SYZ62.pdeg_smul, hpd₁, degree_eq_natDegree hq₁, ← Nat.cast_add, Nat.cast_le] at hle1
        omega
      · have hle2 : SYZ62.pdeg ![a, b, c] (q₂ • e₂) ≤ (δ₁ : WithBot ℕ) :=
          le_trans (le_max_right _ _) (le_trans hcombo hw_pdeg)
        rw [SYZ62.pdeg_smul, hpd₂, degree_eq_natDegree hq₂, ← Nat.cast_add, Nat.cast_le] at hle2
        omega
    · have he₁_ne : ¬ (e₁ 0 = 0 ∧ e₁ 1 = 0 ∧ e₁ 2 = 0) := by
        rintro ⟨h0, h1, h2⟩
        have he0 : e₁ = 0 := by
          funext i
          fin_cases i
          · exact h0
          · exact h1
          · exact h2
        rw [he0, SYZ62.pdeg_zero] at hpd₁
        exact WithBot.bot_ne_coe hpd₁
      have he₁_slots :=
        (pdeg_le_iff_slot_natDegree_le hAB0 hAC0 hBC0 hdAB hdAC hdBC e₁).mp (le_of_eq hpd₁)
      have he₁_syz : WAB * e₁ 0 + WAC * e₁ 1 + WBC * e₁ 2 = 0 := by
        rwa [LinearMap.mem_ker, SYZ61.syzygyMap_apply] at he₁N
      exact hmin.2 n₁ ⟨e₁ 0, e₁ 1, e₁ 2, he₁_syz, he₁_ne, he₁_slots.1, he₁_slots.2.1,
        he₁_slots.2.2⟩
  have hn₂_eq : n₂ = a + b + c - δ₁ := by omega
  refine ⟨by omega, fun D => ?_⟩
  rw [SYZ64.finrank_windowKD hpd₁ hpd₂ hpair hspan D, hn₁_eq, hn₂_eq]

/-- **Exact in-budget window dimension on `BandStack`.**
Under `F1RegionSyzygy.BandStack a b c t k`, G172 interior slack `2k + 1 ≤ a + b + c + 2t` forces
`(k - 1 - t) + 1 < a + b + c - δ₁`, killing the second μ-basis ramp and leaving
`finrank K (windowKD ![a, b, c] (ker syzygyMap) (k - 1 - t)) = (k - t) - δ₁`. -/
theorem finrank_windowKD_bandStack {WAB WAC WBC : K[X]} {a b c t k δ₁ : ℕ}
    (hAB0 : WAB ≠ 0) (hAC0 : WAC ≠ 0) (hBC0 : WBC ≠ 0)
    (hdAB : WAB.natDegree = a) (hdAC : WAC.natDegree = b) (hdBC : WBC.natDegree = c)
    (hcopAB : IsCoprime WAB WAC) (hcopAC : IsCoprime WAB WBC)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hmin : F1RegionSyzygy.MinimalSyzygyDegree WAB WAC WBC δ₁) :
    Module.finrank K
        (SYZ64.windowKD ![a, b, c] (LinearMap.ker (SYZ61.syzygyMap WAB WAC WBC)) (k - 1 - t)) =
      (k - t) - δ₁ := by
  obtain ⟨hδ_le, hwin⟩ :=
    finrank_windowKD_of_minimalSyzygy hAB0 hAC0 hBC0 hdAB hdAC hdBC hcopAB hcopAC hmin
  obtain ⟨_ha1, _hb1, _hc1, hbud, hslack⟩ := hband
  rw [hwin (k - 1 - t)]
  omega

/-- **Out-of-budget `MinimalSyzygyDegree` (`k - t ≤ δ₁`) forces `SYZ38.SylvesterInjective`.** -/
theorem sylvesterInjective_of_budget_le_minSyzygy {WAB WAC WBC : K[X]} {a b c t k δ₁ : ℕ}
    (hAC0 : WAC ≠ 0) (hBC0 : WBC ≠ 0)
    (hdAC : WAC.natDegree = b) (hdBC : WBC.natDegree = c)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hmin : F1RegionSyzygy.MinimalSyzygyDegree WAB WAC WBC δ₁)
    (hout : k - t ≤ δ₁) :
    SYZ38.SylvesterInjective WAB WAC WBC (k - 1 - (b + t)) (k - 1 - (c + t)) := by
  obtain ⟨_ha1, _hb1, _hc1, hbud, _hslack⟩ := hband
  intro rAC rBC hbAC hbBC hdvd
  obtain ⟨rAB, hrAB⟩ := hdvd
  by_contra hnot
  have hsyz : WAB * (-rAB) + WAC * rAC + WBC * (-rBC) = 0 := by linear_combination hrAB
  have hAC_deg : (WAC * rAC).natDegree ≤ k - 1 - t := by
    rcases eq_or_ne rAC 0 with rfl | hrAC0
    · simp only [mul_zero, natDegree_zero, Nat.zero_le]
    · rw [natDegree_mul hAC0 hrAC0, hdAC]
      have hb1 := hbAC hrAC0
      omega
  have hBC_deg : (WBC * (-rBC)).natDegree ≤ k - 1 - t := by
    rcases eq_or_ne rBC 0 with rfl | hrBC0
    · simp only [neg_zero, mul_zero, natDegree_zero, Nat.zero_le]
    · rw [mul_neg, natDegree_neg, natDegree_mul hBC0 hrBC0, hdBC]
      have hb2 := hbBC hrBC0
      omega
  have hAB_deg : (WAB * (-rAB)).natDegree ≤ k - 1 - t := by
    have heq : WAB * (-rAB) = -(WAC * rAC) + WBC * rBC := by linear_combination hsyz
    rw [heq]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rwa [natDegree_neg]
    · simpa only [mul_neg, natDegree_neg] using hBC_deg
  have hnz : ¬ (-rAB = 0 ∧ rAC = 0 ∧ -rBC = 0) := by
    rintro ⟨_, hACz, hBCz⟩
    exact hnot ⟨hACz, neg_eq_zero.mp hBCz⟩
  have hle : δ₁ ≤ k - 1 - t :=
    hmin.2 (k - 1 - t) ⟨-rAB, rAC, -rBC, hsyz, hnz, hAB_deg, hAC_deg, hBC_deg⟩
  omega

/-- **Across the entire PR #528 / `_F1RegionMiddleCounterexample` family
`(d, d, d, d - 2, 2d - 1, d + 1)` (`6 ≤ d`), `SYZ38.SylvesterInjective` holds unconditionally!**
Although `SYZ59.middleBand d d d (d + 1)` is occupied, `k - t = (2d - 1) - (d - 2) = d + 1 = δ₁`,
so the middle syzygy sits strictly above the `t`-loaded budget `k - 1 - t = d`. -/
theorem pr528_family_sylvesterInjective {SAB SAC SBC : Finset K} {d : ℕ}
    [DecidableEq K] (hd : 6 ≤ d)
    (hcAB : SAB.card = d) (hcAC : SAC.card = d) (hcBC : SBC.card = d)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) (d + 1)) :
    SYZ38.SylvesterInjective
      (F1RegionSyzygy.vanishing SAB)
      (F1RegionSyzygy.vanishing SAC)
      (F1RegionSyzygy.vanishing SBC)
      ((2 * d - 1) - 1 - (d + (d - 2)))
      ((2 * d - 1) - 1 - (d + (d - 2))) := by
  have _ := hcAB
  have hband : F1RegionSyzygy.BandStack d d d (d - 2) (2 * d - 1) :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  exact sylvesterInjective_of_budget_le_minSyzygy
    (a := d) (b := d) (c := d) (t := d - 2) (k := 2 * d - 1) (δ₁ := d + 1)
    (F1RegionSyzygy.vanishing_ne_zero SAC)
    (F1RegionSyzygy.vanishing_ne_zero SBC)
    ((F1RegionSyzygy.vanishing_natDegree SAC).trans hcAC)
    ((F1RegionSyzygy.vanishing_natDegree SBC).trans hcBC)
    hband hmin (by omega)

end WindowDimensionFormula

/-! ## 3. Three-core cocycle injection and the `(6, 6, 6, 2, 10, 7)` stack-lift gate -/

section ThreeCoreLiftGate

variable {F : Type} [Field F] [DecidableEq F]

/-- Canonical coordinate embedding of a finite domain `Ω ⊆ F` into `F`. -/
def domΩ (Ω : Finset F) : (↥Ω) ↪ F := Function.Embedding.subtype (· ∈ Ω)

/-- Coordinate subset of `↥Ω` cut out by `S : Finset F`. -/
def coreSubfinset (Ω S : Finset F) : Finset (↥Ω) :=
  Ω.attach.filter (fun x => (x : F) ∈ S)

omit [Field F] in
@[simp]
theorem mem_coreSubfinset {Ω S : Finset F} {x : ↥Ω} :
    x ∈ coreSubfinset Ω S ↔ (x : F) ∈ S := by
  simp only [coreSubfinset, Finset.mem_filter, Finset.mem_attach, true_and]

private theorem vanishing_dvd_of_eval_eq_zero (S : Finset F) {p : F[X]}
    (hp : ∀ s ∈ S, p.eval s = 0) :
    F1RegionSyzygy.vanishing S ∣ p := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [F1RegionSyzygy.vanishing, Finset.prod_empty]
    exact one_dvd p
  | @insert a s ha ih =>
    have hroot : X - C a ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr (hp a (Finset.mem_insert_self a s))
    have hrest : F1RegionSyzygy.vanishing s ∣ p :=
      ih (fun x hx => hp x (Finset.mem_insert_of_mem hx))
    have hcop : IsCoprime (X - C a) (F1RegionSyzygy.vanishing s) := by
      have hsing : F1RegionSyzygy.vanishing ({a} : Finset F) = X - C a := by
        simp only [F1RegionSyzygy.vanishing, Finset.prod_singleton]
      rw [← hsing]
      exact F1RegionSyzygy.vanishing_isCoprime (Finset.disjoint_singleton_left.mpr ha)
    unfold F1RegionSyzygy.vanishing at hrest ⊢
    rw [Finset.prod_insert ha]
    exact hcop.mul_dvd hroot hrest

omit [DecidableEq F] in
private theorem degreeLT_eq_of_agree_on_core {S : Finset F} {k : ℕ}
    (hcard : k ≤ S.card) {p₁ p₂ : Polynomial.degreeLT F k}
    (hagree : ∀ s ∈ S, (p₁ : F[X]).eval s = (p₂ : F[X]).eval s) :
    p₁ = p₂ := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (f := (p₁ : F[X]) - (p₂ : F[X]))
    (s := S) ?_ ?_
  · have hmem : (p₁ - p₂ : Polynomial.degreeLT F k).1 ∈ Polynomial.degreeLT F k := (p₁ - p₂).2
    rw [Polynomial.mem_degreeLT] at hmem
    exact lt_of_lt_of_le hmem (by exact_mod_cast hcard)
  · intro s hs
    rw [Polynomial.eval_sub, hagree s hs, sub_self]

/-- Submodule of words `w : ↥Ω → F` whose restrictions to each of the three band cores
`SAB ∪ SAC ∪ T`, `SAB ∪ SBC ∪ T`, and `SAC ∪ SBC ∪ T` agree with degree-`< k` polynomials. -/
def ThreeCoreGluedSubmodule (Ω SAB SAC SBC T : Finset F) (k : ℕ) : Submodule F (↥Ω → F) where
  carrier :=
    {w |
      (∃ pA : Polynomial.degreeLT F k,
        ∀ x ∈ coreSubfinset Ω (SAB ∪ SAC ∪ T), (pA : F[X]).eval (x : F) = w x) ∧
      (∃ pB : Polynomial.degreeLT F k,
        ∀ x ∈ coreSubfinset Ω (SAB ∪ SBC ∪ T), (pB : F[X]).eval (x : F) = w x) ∧
      (∃ pC : Polynomial.degreeLT F k,
        ∀ x ∈ coreSubfinset Ω (SAC ∪ SBC ∪ T), (pC : F[X]).eval (x : F) = w x)}
  zero_mem' := ⟨⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro w₁ w₂ ⟨⟨pA₁, hA₁⟩, ⟨pB₁, hB₁⟩, ⟨pC₁, hC₁⟩⟩ ⟨⟨pA₂, hA₂⟩, ⟨pB₂, hB₂⟩, ⟨pC₂, hC₂⟩⟩
    refine ⟨⟨pA₁ + pA₂, fun x hx => ?_⟩, ⟨pB₁ + pB₂, fun x hx => ?_⟩, ⟨pC₁ + pC₂, fun x hx => ?_⟩⟩
    · simp only [Submodule.coe_add, Polynomial.eval_add, Pi.add_apply, hA₁ x hx, hA₂ x hx]
    · simp only [Submodule.coe_add, Polynomial.eval_add, Pi.add_apply, hB₁ x hx, hB₂ x hx]
    · simp only [Submodule.coe_add, Polynomial.eval_add, Pi.add_apply, hC₁ x hx, hC₂ x hx]
  smul_mem' := by
    rintro c w ⟨⟨pA, hA⟩, ⟨pB, hB⟩, ⟨pC, hC⟩⟩
    refine ⟨⟨c • pA, fun x hx => ?_⟩, ⟨c • pB, fun x hx => ?_⟩, ⟨c • pC, fun x hx => ?_⟩⟩
    · simp only [Submodule.coe_smul, Polynomial.eval_smul, Pi.smul_apply, hA x hx]
    · simp only [Submodule.coe_smul, Polynomial.eval_smul, Pi.smul_apply, hB x hx]
    · simp only [Submodule.coe_smul, Polynomial.eval_smul, Pi.smul_apply, hC x hx]

/-- A stack `(u₀, u₁ : ↥Ω → F)` is **3-core pair-degenerate** when each of the three band cores
`C_A = SAB ∪ SAC ∪ T`, `C_B = SAB ∪ SBC ∪ T`, `C_C = SAC ∪ SBC ∪ T` carries a joint codeword pair
of `RS[Ω, k]` agreeing with `(u₀, u₁)`. -/
def ThreeCorePairDegenerate (Ω SAB SAC SBC T : Finset F) (k : ℕ) (u₀ u₁ : ↥Ω → F) : Prop :=
  _root_.ProximityGap.pairJointAgreesOn
      (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F))
      (coreSubfinset Ω (SAB ∪ SAC ∪ T)) u₀ u₁ ∧
    _root_.ProximityGap.pairJointAgreesOn
      (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F))
      (coreSubfinset Ω (SAB ∪ SBC ∪ T)) u₀ u₁ ∧
    _root_.ProximityGap.pairJointAgreesOn
      (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F))
      (coreSubfinset Ω (SAC ∪ SBC ∪ T)) u₀ u₁

theorem mem_threeCoreGlued_of_pairDegenerate {Ω SAB SAC SBC T : Finset F} {k : ℕ}
    {u₀ u₁ : ↥Ω → F} (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T k u₀ u₁) :
    u₀ ∈ ThreeCoreGluedSubmodule Ω SAB SAC SBC T k ∧
      u₁ ∈ ThreeCoreGluedSubmodule Ω SAB SAC SBC T k := by
  obtain ⟨⟨vA₀, hvA₀, vA₁, hvA₁, hA⟩, ⟨vB₀, hvB₀, vB₁, hvB₁, hB⟩, ⟨vC₀, hvC₀, vC₁, hvC₁, hC⟩⟩ :=
    hdeg
  rw [SetLike.mem_coe, ReedSolomon.code, Submodule.mem_map] at hvA₀ hvA₁ hvB₀ hvB₁ hvC₀ hvC₁
  obtain ⟨pA₀, hpA₀, rfl⟩ := hvA₀
  obtain ⟨pA₁, hpA₁, rfl⟩ := hvA₁
  obtain ⟨pB₀, hpB₀, rfl⟩ := hvB₀
  obtain ⟨pB₁, hpB₁, rfl⟩ := hvB₁
  obtain ⟨pC₀, hpC₀, rfl⟩ := hvC₀
  obtain ⟨pC₁, hpC₁, rfl⟩ := hvC₁
  exact ⟨⟨⟨⟨pA₀, hpA₀⟩, fun x hx => (hA x hx).1⟩,
      ⟨⟨pB₀, hpB₀⟩, fun x hx => (hB x hx).1⟩,
      ⟨⟨pC₀, hpC₀⟩, fun x hx => (hC x hx).1⟩⟩,
    ⟨⟨⟨pA₁, hpA₁⟩, fun x hx => (hA x hx).2⟩,
      ⟨⟨pB₁, hpB₁⟩, fun x hx => (hB x hx).2⟩,
      ⟨⟨pC₁, hpC₁⟩, fun x hx => (hC x hx).2⟩⟩⟩

private noncomputable def exactQuot (M : F[X]) {q : F[X]} (hdvd : M ∣ q) : F[X] :=
  Classical.choose hdvd

omit [DecidableEq F] in
private theorem exactQuot_spec (M : F[X]) {q : F[X]} (hdvd : M ∣ q) :
    M * exactQuot M hdvd = q :=
  (Classical.choose_spec hdvd).symm

omit [DecidableEq F] in
private theorem mul_smul_poly (r : F) (M u : F[X]) : M * (r • u) = r • (M * u) := by
  rw [← algebraMap_smul F[X] r u, ← algebraMap_smul F[X] r (M * u), smul_eq_mul, smul_eq_mul]
  ring

/-- **3-Core Cocycle Dimension Bound.**
On any full-partition (`a + b + c + t = 2 * k`) `VennRegions` + `BandStack` + `MinimalSyzygyDegree`
configuration over `F`, the syndrome image of `ThreeCoreGluedSubmodule` modulo `RS[Ω, k]` embeds
`F`-linearly into the in-budget syzygy window `windowKD ![a, b, c] (ker syzygyMap) (k - 1 - t)` and
therefore has `F`-dimension at most `(k - t) - δ₁`. -/
theorem finrank_threeCoreGlued_quotient_le {Ω SAB SAC SBC T : Finset F} {a b c t k δ₁ : ℕ}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T a b c t k)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hfull : a + b + c + t = 2 * k)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) δ₁) :
    Module.finrank F
        ((ThreeCoreGluedSubmodule Ω SAB SAC SBC T k).map
          (ReedSolomon.code (domΩ Ω) k).mkQ) ≤
      (k - t) - δ₁ := by
  classical
  obtain ⟨_hroots, hΩcard, hsAB, hsAC, hsBC, hsT, h12, h13, h1T, h23, h2T, h3T, ha, hb, hc, ht⟩ :=
    hV
  have ⟨_ha1, _hb1, _hc1, hbud, hslack⟩ := hband
  set G := ThreeCoreGluedSubmodule Ω SAB SAC SBC T k
  set C := ReedSolomon.code (domΩ Ω) k
  set WAB := F1RegionSyzygy.vanishing SAB
  set WAC := F1RegionSyzygy.vanishing SAC
  set WBC := F1RegionSyzygy.vanishing SBC
  set VT := F1RegionSyzygy.vanishing T
  set Win := SYZ64.windowKD ![a, b, c] (LinearMap.ker (SYZ61.syzygyMap WAB WAC WBC)) (k - 1 - t)
  have hsubA : SAB ∪ SAC ∪ T ⊆ Ω :=
    Finset.union_subset (Finset.union_subset hsAB hsAC) hsT
  have hsubB : SAB ∪ SBC ∪ T ⊆ Ω :=
    Finset.union_subset (Finset.union_subset hsAB hsBC) hsT
  have hsubC : SAC ∪ SBC ∪ T ⊆ Ω :=
    Finset.union_subset (Finset.union_subset hsAC hsBC) hsT
  have hcardA : k ≤ (SAB ∪ SAC ∪ T).card := by
    have hd : Disjoint (SAB ∪ SAC) T := Finset.disjoint_union_left.mpr ⟨h1T, h2T⟩
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint h12, ha, hb, ht]
    omega
  have hcardB : k ≤ (SAB ∪ SBC ∪ T).card := by
    have hd : Disjoint (SAB ∪ SBC) T := Finset.disjoint_union_left.mpr ⟨h1T, h3T⟩
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint h13, ha, hc, ht]
    omega
  have hcardC : k ≤ (SAC ∪ SBC ∪ T).card := by
    have hd : Disjoint (SAC ∪ SBC) T := Finset.disjoint_union_left.mpr ⟨h2T, h3T⟩
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint h23, hb, hc, ht]
    omega
  have hΩ_eq : SAB ∪ SAC ∪ SBC ∪ T = Ω := by
    have hd1 : Disjoint (SAB ∪ SAC) SBC := Finset.disjoint_union_left.mpr ⟨h13, h23⟩
    have hd2 : Disjoint (SAB ∪ SAC ∪ SBC) T :=
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h1T, h2T⟩, h3T⟩
    have hsub : SAB ∪ SAC ∪ SBC ∪ T ⊆ Ω :=
      Finset.union_subset (Finset.union_subset (Finset.union_subset hsAB hsAC) hsBC) hsT
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint h12, ha, hb, hc, ht, hΩcard, hfull]
  let pA_of (w : G) : Polynomial.degreeLT F k := Classical.choose w.2.1
  let pB_of (w : G) : Polynomial.degreeLT F k := Classical.choose w.2.2.1
  let pC_of (w : G) : Polynomial.degreeLT F k := Classical.choose w.2.2.2
  have hpA_spec : ∀ (w : G) (s : F) (hs : s ∈ SAB ∪ SAC ∪ T),
      (pA_of w : F[X]).eval s = (w : ↥Ω → F) ⟨s, hsubA hs⟩ :=
    fun w s hs => Classical.choose_spec w.2.1 ⟨s, hsubA hs⟩ (mem_coreSubfinset.mpr hs)
  have hpB_spec : ∀ (w : G) (s : F) (hs : s ∈ SAB ∪ SBC ∪ T),
      (pB_of w : F[X]).eval s = (w : ↥Ω → F) ⟨s, hsubB hs⟩ :=
    fun w s hs => Classical.choose_spec w.2.2.1 ⟨s, hsubB hs⟩ (mem_coreSubfinset.mpr hs)
  have hpC_spec : ∀ (w : G) (s : F) (hs : s ∈ SAC ∪ SBC ∪ T),
      (pC_of w : F[X]).eval s = (w : ↥Ω → F) ⟨s, hsubC hs⟩ :=
    fun w s hs => Classical.choose_spec w.2.2.2 ⟨s, hsubC hs⟩ (mem_coreSubfinset.mpr hs)
  have hpA_add : ∀ w₁ w₂ : G, pA_of (w₁ + w₂) = pA_of w₁ + pA_of w₂ := fun w₁ w₂ =>
    degreeLT_eq_of_agree_on_core hcardA fun s hs => by
      simp only [Submodule.coe_add, Polynomial.eval_add, hpA_spec _ s hs, Pi.add_apply]
  have hpB_add : ∀ w₁ w₂ : G, pB_of (w₁ + w₂) = pB_of w₁ + pB_of w₂ := fun w₁ w₂ =>
    degreeLT_eq_of_agree_on_core hcardB fun s hs => by
      simp only [Submodule.coe_add, Polynomial.eval_add, hpB_spec _ s hs, Pi.add_apply]
  have hpC_add : ∀ w₁ w₂ : G, pC_of (w₁ + w₂) = pC_of w₁ + pC_of w₂ := fun w₁ w₂ =>
    degreeLT_eq_of_agree_on_core hcardC fun s hs => by
      simp only [Submodule.coe_add, Polynomial.eval_add, hpC_spec _ s hs, Pi.add_apply]
  have hpA_smul : ∀ (r : F) (w : G), pA_of (r • w) = r • pA_of w := fun r w =>
    degreeLT_eq_of_agree_on_core hcardA fun s hs => by
      simp only [Submodule.coe_smul, Polynomial.eval_smul, hpA_spec _ s hs, Pi.smul_apply]
  have hpB_smul : ∀ (r : F) (w : G), pB_of (r • w) = r • pB_of w := fun r w =>
    degreeLT_eq_of_agree_on_core hcardB fun s hs => by
      simp only [Submodule.coe_smul, Polynomial.eval_smul, hpB_spec _ s hs, Pi.smul_apply]
  have hpC_smul : ∀ (r : F) (w : G), pC_of (r • w) = r • pC_of w := fun r w =>
    degreeLT_eq_of_agree_on_core hcardC fun s hs => by
      simp only [Submodule.coe_smul, Polynomial.eval_smul, hpC_spec _ s hs, Pi.smul_apply]
  have hdvdAB : ∀ w : G, VT * WAB ∣ ((pB_of w : F[X]) - (pA_of w : F[X])) := by
    intro w
    have hprod : F1RegionSyzygy.vanishing (T ∪ SAB) = VT * WAB := Finset.prod_union h1T.symm
    rw [← hprod]
    refine vanishing_dvd_of_eval_eq_zero (T ∪ SAB) fun s hs => ?_
    rcases Finset.mem_union.mp hs with hsT' | hsAB'
    · rw [Polynomial.eval_sub, hpB_spec w s (Finset.mem_union_right _ hsT'),
        hpA_spec w s (Finset.mem_union_right _ hsT'), sub_self]
    · rw [Polynomial.eval_sub,
        hpB_spec w s (Finset.mem_union_left _ (Finset.mem_union_left _ hsAB')),
        hpA_spec w s (Finset.mem_union_left _ (Finset.mem_union_left _ hsAB')), sub_self]
  have hdvdAC : ∀ w : G, VT * WAC ∣ ((pA_of w : F[X]) - (pC_of w : F[X])) := by
    intro w
    have hprod : F1RegionSyzygy.vanishing (T ∪ SAC) = VT * WAC := Finset.prod_union h2T.symm
    rw [← hprod]
    refine vanishing_dvd_of_eval_eq_zero (T ∪ SAC) fun s hs => ?_
    rcases Finset.mem_union.mp hs with hsT' | hsAC'
    · rw [Polynomial.eval_sub, hpA_spec w s (Finset.mem_union_right _ hsT'),
        hpC_spec w s (Finset.mem_union_right _ hsT'), sub_self]
    · rw [Polynomial.eval_sub,
        hpA_spec w s (Finset.mem_union_left _ (Finset.mem_union_right _ hsAC')),
        hpC_spec w s (Finset.mem_union_left _ (Finset.mem_union_left _ hsAC')), sub_self]
  have hdvdBC : ∀ w : G, VT * WBC ∣ ((pC_of w : F[X]) - (pB_of w : F[X])) := by
    intro w
    have hprod : F1RegionSyzygy.vanishing (T ∪ SBC) = VT * WBC := Finset.prod_union h3T.symm
    rw [← hprod]
    refine vanishing_dvd_of_eval_eq_zero (T ∪ SBC) fun s hs => ?_
    rcases Finset.mem_union.mp hs with hsT' | hsBC'
    · rw [Polynomial.eval_sub, hpC_spec w s (Finset.mem_union_right _ hsT'),
        hpB_spec w s (Finset.mem_union_right _ hsT'), sub_self]
    · rw [Polynomial.eval_sub,
        hpC_spec w s (Finset.mem_union_left _ (Finset.mem_union_right _ hsBC')),
        hpB_spec w s (Finset.mem_union_left _ (Finset.mem_union_right _ hsBC')), sub_self]
  have hVT0 : VT ≠ 0 := F1RegionSyzygy.vanishing_ne_zero T
  have hWAB0 : WAB ≠ 0 := F1RegionSyzygy.vanishing_ne_zero SAB
  have hWAC0 : WAC ≠ 0 := F1RegionSyzygy.vanishing_ne_zero SAC
  have hWBC0 : WBC ≠ 0 := F1RegionSyzygy.vanishing_ne_zero SBC
  have hVT_deg : VT.natDegree = t := (F1RegionSyzygy.vanishing_natDegree T).trans ht
  let cocycleVec (w : G) : Fin 3 → F[X] :=
    ![exactQuot (VT * WAB) (hdvdAB w),
      exactQuot (VT * WAC) (hdvdAC w),
      exactQuot (VT * WBC) (hdvdBC w)]
  have hdeg_slot : ∀ {W r diff : F[X]},
      VT * W * r = diff → diff ∈ Polynomial.degreeLT F k → (W * r).natDegree ≤ k - 1 - t := by
    intro W r diff hmul hmem
    rcases eq_or_ne (W * r) 0 with h0 | hWr0
    · rw [h0, natDegree_zero]
      omega
    · have hdiff0 : diff ≠ 0 := by
        rw [← hmul, mul_assoc]
        exact mul_ne_zero hVT0 hWr0
      rw [Polynomial.mem_degreeLT, degree_eq_natDegree hdiff0, Nat.cast_lt] at hmem
      have hnd : diff.natDegree = t + (W * r).natDegree := by
        rw [← hmul, mul_assoc, natDegree_mul hVT0 hWr0, hVT_deg]
      omega
  have hcocycle_mem : ∀ w : G, cocycleVec w ∈ Win := by
    intro w
    have hAB_eq := exactQuot_spec (VT * WAB) (hdvdAB w)
    have hAC_eq := exactQuot_spec (VT * WAC) (hdvdAC w)
    have hBC_eq := exactQuot_spec (VT * WBC) (hdvdBC w)
    rw [SYZ64.mem_windowKD]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, SYZ61.syzygyMap_apply]
      apply mul_left_cancel₀ hVT0
      rw [mul_zero]
      change VT * (WAB * exactQuot (VT * WAB) (hdvdAB w) +
          WAC * exactQuot (VT * WAC) (hdvdAC w) +
          WBC * exactQuot (VT * WBC) (hdvdBC w)) = 0
      linear_combination hAB_eq + hAC_eq + hBC_eq
    · refine (pdeg_le_iff_slot_natDegree_le hWAB0 hWAC0 hWBC0
        ((F1RegionSyzygy.vanishing_natDegree SAB).trans ha)
        ((F1RegionSyzygy.vanishing_natDegree SAC).trans hb)
        ((F1RegionSyzygy.vanishing_natDegree SBC).trans hc) (cocycleVec w)).mpr ?_
      exact ⟨hdeg_slot hAB_eq (pB_of w - pA_of w).2,
        hdeg_slot hAC_eq (pA_of w - pC_of w).2,
        hdeg_slot hBC_eq (pC_of w - pB_of w).2⟩
  let cocycleLM : G →ₗ[F] Win :=
    { toFun := fun w => ⟨cocycleVec w, hcocycle_mem w⟩
      map_add' := fun w₁ w₂ => by
        apply Subtype.ext
        have h0 : cocycleVec (w₁ + w₂) 0 = cocycleVec w₁ 0 + cocycleVec w₂ 0 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWAB0)
          change (VT * WAB) * exactQuot (VT * WAB) (hdvdAB (w₁ + w₂)) =
            (VT * WAB) * (exactQuot (VT * WAB) (hdvdAB w₁) + exactQuot (VT * WAB) (hdvdAB w₂))
          rw [mul_add, exactQuot_spec, exactQuot_spec, exactQuot_spec, hpB_add, hpA_add,
            Submodule.coe_add, Submodule.coe_add]
          ring
        have h1 : cocycleVec (w₁ + w₂) 1 = cocycleVec w₁ 1 + cocycleVec w₂ 1 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWAC0)
          change (VT * WAC) * exactQuot (VT * WAC) (hdvdAC (w₁ + w₂)) =
            (VT * WAC) * (exactQuot (VT * WAC) (hdvdAC w₁) + exactQuot (VT * WAC) (hdvdAC w₂))
          rw [mul_add, exactQuot_spec, exactQuot_spec, exactQuot_spec, hpA_add, hpC_add,
            Submodule.coe_add, Submodule.coe_add]
          ring
        have h2 : cocycleVec (w₁ + w₂) 2 = cocycleVec w₁ 2 + cocycleVec w₂ 2 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWBC0)
          change (VT * WBC) * exactQuot (VT * WBC) (hdvdBC (w₁ + w₂)) =
            (VT * WBC) * (exactQuot (VT * WBC) (hdvdBC w₁) + exactQuot (VT * WBC) (hdvdBC w₂))
          rw [mul_add, exactQuot_spec, exactQuot_spec, exactQuot_spec, hpC_add, hpB_add,
            Submodule.coe_add, Submodule.coe_add]
          ring
        funext i
        rcases i with ⟨_ | _ | _ | _, hi⟩
        · exact h0
        · exact h1
        · exact h2
        · omega
      map_smul' := fun r w => by
        apply Subtype.ext
        have h0 : cocycleVec (r • w) 0 = r • cocycleVec w 0 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWAB0)
          change (VT * WAB) * exactQuot (VT * WAB) (hdvdAB (r • w)) =
            (VT * WAB) * (r • exactQuot (VT * WAB) (hdvdAB w))
          rw [mul_smul_poly, exactQuot_spec, exactQuot_spec, hpB_smul, hpA_smul,
            Submodule.coe_smul, Submodule.coe_smul, smul_sub]
        have h1 : cocycleVec (r • w) 1 = r • cocycleVec w 1 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWAC0)
          change (VT * WAC) * exactQuot (VT * WAC) (hdvdAC (r • w)) =
            (VT * WAC) * (r • exactQuot (VT * WAC) (hdvdAC w))
          rw [mul_smul_poly, exactQuot_spec, exactQuot_spec, hpA_smul, hpC_smul,
            Submodule.coe_smul, Submodule.coe_smul, smul_sub]
        have h2 : cocycleVec (r • w) 2 = r • cocycleVec w 2 := by
          apply mul_left_cancel₀ (mul_ne_zero hVT0 hWBC0)
          change (VT * WBC) * exactQuot (VT * WBC) (hdvdBC (r • w)) =
            (VT * WBC) * (r • exactQuot (VT * WBC) (hdvdBC w))
          rw [mul_smul_poly, exactQuot_spec, exactQuot_spec, hpC_smul, hpB_smul,
            Submodule.coe_smul, Submodule.coe_smul, smul_sub]
        funext i
        rcases i with ⟨_ | _ | _ | _, hi⟩
        · exact h0
        · exact h1
        · exact h2
        · omega }
  let πG : G →ₗ[F] G.map C.mkQ := (C.mkQ.comp G.subtype).codRestrict (G.map C.mkQ) fun w =>
    Submodule.mem_map_of_mem w.2
  have hπG_surj : Function.Surjective πG := by
    rintro ⟨_, ⟨w, hwG, rfl⟩⟩
    exact ⟨⟨w, hwG⟩, rfl⟩
  have hker_le : LinearMap.ker cocycleLM ≤ LinearMap.ker πG := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hr0 : exactQuot (VT * WAB) (hdvdAB w) = 0 := congrFun (congrArg Subtype.val hw) 0
    have hpBA : (pB_of w : F[X]) = (pA_of w : F[X]) := by
      have heq := exactQuot_spec (VT * WAB) (hdvdAB w)
      rw [hr0, mul_zero] at heq
      exact sub_eq_zero.mp heq.symm
    have hwC : (w : ↥Ω → F) ∈ C := by
      dsimp only [C]
      rw [ReedSolomon.code, Submodule.mem_map]
      refine ⟨(pA_of w : F[X]), (pA_of w).2, ?_⟩
      funext x
      change (pA_of w : F[X]).eval (x : F) = (w : ↥Ω → F) x
      have hxΩ : (x : F) ∈ SAB ∪ SAC ∪ SBC ∪ T := by
        rw [hΩ_eq]
        exact x.2
      rcases Finset.mem_union.mp hxΩ with hxABC | hxT
      · rcases Finset.mem_union.mp hxABC with hxAB | hxBC
        · exact hpA_spec w (x : F) (Finset.mem_union_left _ hxAB)
        · rw [← hpBA]
          exact hpB_spec w (x : F) (Finset.mem_union_left _ (Finset.mem_union_right _ hxBC))
      · exact hpA_spec w (x : F) (Finset.mem_union_right _ hxT)
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero C).mpr hwC
  have : FiniteDimensional F (↥Ω → F) := Module.Finite.pi
  have : FiniteDimensional F G := FiniteDimensional.of_injective G.subtype Subtype.val_injective
  have hrn_π := LinearMap.finrank_range_add_finrank_ker πG
  rw [LinearMap.range_eq_top.mpr hπG_surj, finrank_top] at hrn_π
  have hrn_c := LinearMap.finrank_range_add_finrank_ker cocycleLM
  have hker_fr : Module.finrank F (LinearMap.ker cocycleLM) ≤ Module.finrank F (LinearMap.ker πG) :=
    Submodule.finrank_mono hker_le
  have hrange_le : Module.finrank F (LinearMap.range cocycleLM) ≤ Module.finrank F Win :=
    Submodule.finrank_le (LinearMap.range cocycleLM)
  have hwin_fr : Module.finrank F Win = (k - t) - δ₁ :=
    finrank_windowKD_bandStack hWAB0 hWAC0 hWBC0
      ((F1RegionSyzygy.vanishing_natDegree SAB).trans ha)
      ((F1RegionSyzygy.vanishing_natDegree SAC).trans hb)
      ((F1RegionSyzygy.vanishing_natDegree SBC).trans hc)
      (F1RegionSyzygy.vanishing_isCoprime h12)
      (F1RegionSyzygy.vanishing_isCoprime h13)
      hband hmin
  omega

omit [DecidableEq F] in
private theorem nonempty_domΩ {Ω SAB SAC SBC T : Finset F} {a b c t k : ℕ}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T a b c t k) (ha1 : 1 ≤ a) :
    Nonempty ↥Ω := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hV.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact ha1)
  exact ⟨⟨x, hV.2.2.1 hx⟩⟩

/-- **Out-of-budget 3-core gate (`k - t ≤ δ₁`):**
Every 3-core pair-degenerate stack on a full-partition witness with `k - t ≤ δ₁` is a global
codeword pair `u₀ ∈ RS[Ω, k] ∧ u₁ ∈ RS[Ω, k]`, and has `mcaBadCount = 0` at every radius `δ`. -/
theorem threeCore_mcaBadCount_eq_zero_of_budget_le_minSyzygy [Fintype F]
    {Ω SAB SAC SBC T : Finset F} {a b c t k δ₁ : ℕ}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T a b c t k)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hfull : a + b + c + t = 2 * k)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) δ₁)
    (hout : k - t ≤ δ₁) (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T k u₀ u₁) :
    letI : Nonempty ↥Ω := nonempty_domΩ hV hband.1
    u₀ ∈ ReedSolomon.code (domΩ Ω) k ∧
      u₁ ∈ ReedSolomon.code (domΩ Ω) k ∧
      _root_.ProximityGap.mcaBadCount (F := F)
          (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F)) δ u₀ u₁ = 0 := by
  have : Nonempty ↥Ω := nonempty_domΩ hV hband.1
  set C := ReedSolomon.code (domΩ Ω) k
  set M := (ThreeCoreGluedSubmodule Ω SAB SAC SBC T k).map C.mkQ
  have hfr_le := finrank_threeCoreGlued_quotient_le hV hband hfull hmin
  change Module.finrank F M ≤ (k - t) - δ₁ at hfr_le
  have hfr0 : Module.finrank F M = 0 := by omega
  have hMbot : M = ⊥ := Submodule.finrank_eq_zero.mp hfr0
  obtain ⟨hu₀G, hu₁G⟩ := mem_threeCoreGlued_of_pairDegenerate hdeg
  have hq₀ : C.mkQ u₀ = 0 := by
    have hm : C.mkQ u₀ ∈ M := Submodule.mem_map_of_mem hu₀G
    rwa [hMbot, Submodule.mem_bot] at hm
  have hq₁ : C.mkQ u₁ = 0 := by
    have hm : C.mkQ u₁ ∈ M := Submodule.mem_map_of_mem hu₁G
    rwa [hMbot, Submodule.mem_bot] at hm
  have hu₀C : u₀ ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hq₀
  have hu₁C : u₁ ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hq₁
  exact ⟨hu₀C, hu₁C, mcaBadCount_eq_zero_of_both_mem C δ hu₀C hu₁C⟩

/-- **Single-syzygy 3-core gate (`(k - t) - δ₁ ≤ 1`):**
Every 3-core pair-degenerate stack on a full-partition witness with `(k - t) - δ₁ ≤ 1` has
collinear syndrome cosets and therefore `mcaBadCount ≤ 1` at every radius `δ`. -/
theorem threeCore_mcaBadCount_le_one_of_window_le_one [Fintype F]
    {Ω SAB SAC SBC T : Finset F} {a b c t k δ₁ : ℕ}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T a b c t k)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hfull : a + b + c + t = 2 * k)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) δ₁)
    (hwin1 : (k - t) - δ₁ ≤ 1) (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T k u₀ u₁) :
    letI : Nonempty ↥Ω := nonempty_domΩ hV hband.1
    _root_.ProximityGap.mcaBadCount (F := F)
        (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F)) δ u₀ u₁ ≤ 1 := by
  have : Nonempty ↥Ω := nonempty_domΩ hV hband.1
  set C := ReedSolomon.code (domΩ Ω) k
  set M := (ThreeCoreGluedSubmodule Ω SAB SAC SBC T k).map C.mkQ
  have hfr_le := (finrank_threeCoreGlued_quotient_le hV hband hfull hmin).trans hwin1
  obtain ⟨hu₀G, hu₁G⟩ := mem_threeCoreGlued_of_pairDegenerate hdeg
  exact mcaBadCount_le_one_of_finrank_quotient_le_one C δ M hfr_le
    (Submodule.mem_map_of_mem hu₀G) (Submodule.mem_map_of_mem hu₁G)

/-- **Necessary window-slack gate for multi-scalar 3-core lifts
(`2 ≤ mcaBadCount ⟹ 2 ≤ (k - t) - δ₁`).**
Any 3-core pair-degenerate stack on a full-partition witness achieving `2 ≤ mcaBadCount` must
satisfy `δ₁ + 2 ≤ k - t`. -/
theorem threeCore_multiScalar_requires_window_slack_two [Fintype F]
    {Ω SAB SAC SBC T : Finset F} {a b c t k δ₁ : ℕ}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T a b c t k)
    (hband : F1RegionSyzygy.BandStack a b c t k)
    (hfull : a + b + c + t = 2 * k)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) δ₁)
    (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T k u₀ u₁)
    (hbad :
      letI : Nonempty ↥Ω := nonempty_domΩ hV hband.1
      2 ≤ _root_.ProximityGap.mcaBadCount (F := F)
          (ReedSolomon.code (domΩ Ω) k : Set (↥Ω → F)) δ u₀ u₁) :
    2 ≤ (k - t) - δ₁ := by
  by_contra hlt
  have hle1 :=
    threeCore_mcaBadCount_le_one_of_window_le_one hV hband hfull hmin (by omega) δ hdeg
  omega

/-- **Complete 3-core stack-lift closure of the PR #528 / `_F1RegionMiddleCounterexample` family
`(d, d, d, d - 2, 2d - 1, d + 1)` (`6 ≤ d`, over every finite field `F`).**
Every 3-core pair-degenerate stack lies in `RS[Ω, 2d - 1]^2` and has `mcaBadCount = 0`. -/
theorem pr528_family_threeCore_mcaBadCount_eq_zero [Fintype F]
    {Ω SAB SAC SBC T : Finset F} {d : ℕ} (hd : 6 ≤ d)
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T d d d (d - 2) (2 * d - 1))
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) (d + 1))
    (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T (2 * d - 1) u₀ u₁) :
    letI : Nonempty ↥Ω := nonempty_domΩ hV (by omega)
    u₀ ∈ ReedSolomon.code (domΩ Ω) (2 * d - 1) ∧
      u₁ ∈ ReedSolomon.code (domΩ Ω) (2 * d - 1) ∧
      _root_.ProximityGap.mcaBadCount (F := F)
          (ReedSolomon.code (domΩ Ω) (2 * d - 1) : Set (↥Ω → F)) δ u₀ u₁ = 0 :=
  threeCore_mcaBadCount_eq_zero_of_budget_le_minSyzygy hV
    ⟨by omega, by omega, by omega, by omega, by omega⟩ (by omega) hmin (by omega) δ hdeg

/-- **Complete 3-core stack-lift gate on `SYZ70–SYZ72`'s first balanced middle slot
`(6, 6, 6, 2, 10, 7)` over EVERY finite field `F`!**
Every `(6, 6, 6, 2, 10, 7)` witness has window dimension `(10 - 2) - 7 = 1`, forcing every 3-core
pair-degenerate stack to satisfy `mcaBadCount ≤ 1 < 19 = 2k - 1` at every radius `δ`. -/
theorem middleSlot_666_threeCore_mcaBadCount_le_one [Fintype F]
    {Ω SAB SAC SBC T : Finset F}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T 6 6 6 2 10)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) 7)
    (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T 10 u₀ u₁) :
    letI : Nonempty ↥Ω := nonempty_domΩ hV (by decide)
    _root_.ProximityGap.mcaBadCount (F := F)
        (ReedSolomon.code (domΩ Ω) 10 : Set (↥Ω → F)) δ u₀ u₁ ≤ 1 :=
  threeCore_mcaBadCount_le_one_of_window_le_one hV
    ⟨by decide, by decide, by decide, by decide, by decide⟩ rfl hmin (by decide) δ hdeg

/-- **Explicit specialization to `SYZ72`'s `F_41`, `μ_20` middle-slot witness:**
`ZMod 41` hosts a certified `(6, 6, 6, 2, 10, 7)` middle-slot region-syzygy witness
(`SYZ72.zmod41_regionSyzygyRealizable`), and **no** `(6, 6, 6, 2, 10, 7)` witness over `ZMod 41`
can lift to a 3-core pair-degenerate stack with `mcaBadCount ≥ 2` (or `> 19 = n - 1`). -/
theorem zmod41_middleSlot_no_overBudget_threeCore_lift :
    letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    ∃ (Ω SAB SAC SBC T : Finset (ZMod 41))
      (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T 6 6 6 2 10),
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) 7 ∧
      ∀ (δ : ℝ≥0) (u₀ u₁ : ↥Ω → ZMod 41),
        ThreeCorePairDegenerate Ω SAB SAC SBC T 10 u₀ u₁ →
        letI : Nonempty ↥Ω := nonempty_domΩ hV (by decide)
        _root_.ProximityGap.mcaBadCount (F := ZMod 41)
            (ReedSolomon.code (domΩ Ω) 10 : Set (↥Ω → ZMod 41)) δ u₀ u₁ ≤ 1 := by
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  obtain ⟨Ω, SAB, SAC, SBC, T, hV, _hband, hmin⟩ := SYZ72.zmod41_regionSyzygyRealizable
  refine ⟨Ω, SAB, SAC, SBC, T, hV, hmin, fun δ u₀ u₁ hdeg => ?_⟩
  exact middleSlot_666_threeCore_mcaBadCount_le_one hV hmin δ hdeg

/-- **Complete 3-core stack-lift gate on `SYZ50` Question-C's `(4, 4, 4, 2, 7, 4)` profile
over every finite field `F`:** `(7 - 2) - 4 = 1`, so every 3-core pair-degenerate stack has
`mcaBadCount ≤ 1 < 13 = 2k - 1` (sharpening `SYZ50.lift_ceiling_le_budget`'s `≤ 12` to `≤ 1`). -/
theorem syz50_444_threeCore_mcaBadCount_le_one [Fintype F]
    {Ω SAB SAC SBC T : Finset F}
    (hV : F1RegionSyzygy.VennRegions Ω SAB SAC SBC T 4 4 4 2 7)
    (hmin :
      F1RegionSyzygy.MinimalSyzygyDegree
        (F1RegionSyzygy.vanishing SAB)
        (F1RegionSyzygy.vanishing SAC)
        (F1RegionSyzygy.vanishing SBC) 4)
    (δ : ℝ≥0) {u₀ u₁ : ↥Ω → F}
    (hdeg : ThreeCorePairDegenerate Ω SAB SAC SBC T 7 u₀ u₁) :
    letI : Nonempty ↥Ω := nonempty_domΩ hV (by decide)
    _root_.ProximityGap.mcaBadCount (F := F)
        (ReedSolomon.code (domΩ Ω) 7 : Set (↥Ω → F)) δ u₀ u₁ ≤ 1 :=
  threeCore_mcaBadCount_le_one_of_window_le_one hV
    ⟨by decide, by decide, by decide, by decide, by decide⟩ rfl hmin (by decide) δ hdeg

end ThreeCoreLiftGate

#print axioms mcaBadCount_le_one_of_collinear_syndrome
#print axioms mcaBadCount_le_one_of_finrank_quotient_le_one
#print axioms finrank_windowKD_of_minimalSyzygy
#print axioms finrank_windowKD_bandStack
#print axioms sylvesterInjective_of_budget_le_minSyzygy
#print axioms pr528_family_sylvesterInjective
#print axioms finrank_threeCoreGlued_quotient_le
#print axioms threeCore_mcaBadCount_eq_zero_of_budget_le_minSyzygy
#print axioms threeCore_mcaBadCount_le_one_of_window_le_one
#print axioms threeCore_multiScalar_requires_window_slack_two
#print axioms pr528_family_threeCore_mcaBadCount_eq_zero
#print axioms middleSlot_666_threeCore_mcaBadCount_le_one
#print axioms zmod41_middleSlot_no_overBudget_threeCore_lift
#print axioms syz50_444_threeCore_mcaBadCount_le_one

end ArkLib.ProximityGap.Frontier.CarbonSYZMiddleSlotLiftGate
