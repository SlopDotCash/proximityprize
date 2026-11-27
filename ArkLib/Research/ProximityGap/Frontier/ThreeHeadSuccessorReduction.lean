/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeEighthAssembly
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadResidualSecant
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadSuccessorIncidence

/-! # Three-head successor reduction and moment-cell closures (Packet L4c)

Reduces any over-budget (`> 2^31`) bad-scalar family in the ten-row successor window
(`715,827,871 ≤ e ≤ 715,827,880`, `d ≤ 77,807,385`) to three saturated noncollinear affine heads,
conditional only on `NonlinearComponentCap logDerivPrice`, and closes:
- `ThreeHeadResidualSecant` (`k = 76,695,848`, `e = 715,827,877`),
- `ThreeHeadSuccessorIncidence` Row 1 (`k = 71,582,790`, `e = 715,827,880`),
- `ThreeHeadSuccessorIncidence` Rows 4–10 (all seven `momentCell` rows up to `k = 77,807,386`).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorReduction

open Finset Polynomial Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting
open ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction
open ArkLib.ProximityGap.Frontier.SecondPrimeEighthAssembly
open ArkLib.ProximityGap.Frontier.ThreeHeadResidualSecant
open ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorIncidence
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open scoped NNReal ENNReal

abbrev N : ℕ := 1073741824
abbrev dMax : ℕ := 77807385
abbrev tMin : ℕ := 357913944
abbrev tMax : ℕ := 357913953
abbrev Lcut : ℕ := 499999

private theorem successor_lin_gap :
    (25 * (Lcut + 1 - 25) + 3 * (Lcut + 1) * (25 - 1)) * N <
      (Lcut + 1) * (Lcut + 1 - 25) * (tMin - dMax) := by
  decide

private theorem successor_logDeriv_envelope :
    ∀ b : Fin 8, 2 ≤ b.val →
      let A := (2 * b.val - 2) * (2 * tMin - 1)
      let G := (2 * b.val - 2) * 25 - b.val * (b.val - 1)
      let C0 := 2 * A * G + 2 * (2 * tMin - 1) * 25
      G + 2 * b.val * 25 +
        (2 * tMax * (G + 25) * N + N * (2 * C0 + 25 * N)) / (tMin ^ 2 - N * dMax) ≤ Lcut := by
  decide

private theorem logDerivPrice_le_cut_of_successor {d t W m b : ℕ}
    (hd : d ≤ dMax) (htLo : tMin ≤ t) (htHi : t ≤ tMax)
    (hW : W ≤ 2 * tMin - 1) (hm : m ≤ 25) (hbLo : 2 ≤ b) (hbHi : b ≤ 7) :
    logDerivPrice N d t W m b ≤ Lcut := by
  unfold logDerivPrice
  dsimp only
  have hA : (2 * b - 2) * W - b * (b - 1) * d ≤ (2 * b - 2) * (2 * tMin - 1) :=
    (Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hW)
  have hG : (2 * b - 2) * m - b * (b - 1) ≤ (2 * b - 2) * 25 - b * (b - 1) :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hm) _
  have hC0 : 2 * ((2 * b - 2) * W - b * (b - 1) * d) * ((2 * b - 2) * m - b * (b - 1)) +
      2 * W * m ≤
      2 * ((2 * b - 2) * (2 * tMin - 1)) * ((2 * b - 2) * 25 - b * (b - 1)) +
      2 * (2 * tMin - 1) * 25 :=
    Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hG)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hW) hm)
  have hdenPos : 0 < tMin ^ 2 - N * dMax := by decide
  have hdenLe : tMin ^ 2 - N * dMax ≤ t ^ 2 - N * d := by
    have ht2 : tMin ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left htLo 2
    have hnd : N * d ≤ N * dMax := Nat.mul_le_mul_left N hd
    omega
  have hnumLe :
      2 * t * (((2 * b - 2) * m - b * (b - 1)) + m) * N +
        N * (2 * (2 * ((2 * b - 2) * W - b * (b - 1) * d) * ((2 * b - 2) * m - b * (b - 1)) +
          2 * W * m) + m * N) ≤
      2 * tMax * (((2 * b - 2) * 25 - b * (b - 1)) + 25) * N +
        N * (2 * (2 * ((2 * b - 2) * (2 * tMin - 1)) * ((2 * b - 2) * 25 - b * (b - 1)) +
          2 * (2 * tMin - 1) * 25) + 25 * N) := by
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_right N
        (Nat.mul_le_mul (Nat.mul_le_mul_left 2 htHi) (Nat.add_le_add hG hm))
    · exact Nat.mul_le_mul_left N
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hC0) (Nat.mul_le_mul_right N hm))
  have hdiv := (Nat.div_le_div_right hnumLe).trans (Nat.div_le_div_left hdenLe hdenPos)
  exact (Nat.add_le_add (Nat.add_le_add hG (Nat.mul_le_mul_left (2 * b) hm)) hdiv).trans
    (successor_logDeriv_envelope ⟨b, by omega⟩ hbLo)

private theorem successor_collinear_table :
    ∀ j : Fin 8, 3 ≤ j.val →
      let c := tMin - (N - tMin) / Lcut
      let den := c + (j.val - 1) * dMax
      let U := max (j.val * c - j.val.choose 2 * dMax) ((j.val * c ^ 2 + den - 1) / den)
      25 + (j.val * N - (j.val - 1) * U) + (7 - j.val) * Lcut ≤ 2147483648 := by
  decide

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Universal reduction to three saturated noncollinear heads across ALL ten successor rows
(`715,827,871 ≤ e ≤ 715,827,880`, `d ≤ 77,807,385`): if `fam.G.card > 2^31`, then there exist
three distinct heads `a, b, c ∈ lineParameters fam` with `threeLineDeterminant a b c ≠ 0`,
each having joint core `≥ N - e - 1`, and at most `2,000,025` labels of `fam.G` off their union. -/
theorem three_saturated_noncollinear_of_over_budget (hcap : NonlinearComponentCap logDerivPrice)
    {d e : ℕ} (hd : d ≤ dMax) (heLo : 715827871 ≤ e) (heHi : e ≤ 715827880)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = N - e)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F)
    (hover : 2147483648 < fam.G.card) :
    ∃ a b c : LineParameter F,
      a ∈ lineParameters fam ∧ b ∈ lineParameters fam ∧ c ∈ lineParameters fam ∧
      threeLineDeterminant a b c ≠ 0 ∧
      (∀ x ∈ ({a, b, c} : Finset _), N - e - 1 ≤ (jointCore dom (u 0) (u 1) x.1 x.2).card) ∧
      (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card ≤ 2000025 := by
  classical
  have : Infinite (RatFunc F) := ratFunc_infinite F
  let φ := ratFuncHom F
  let domK : I ↪ RatFunc F := dom.trans ⟨φ, φ.injective⟩
  let t : ℕ := N - e
  have htLo : tMin ≤ t := by dsimp [t, N, tMin]; omega
  have htHi : t ≤ tMax := by dsimp [t, N, tMax]; omega
  have hte : t + e = N := by dsimp [t, N]; omega
  obtain ⟨Q, hQne, hQsupp, hQroot⟩ := ThreeHeadSuccessorIncidence.common_surface domK
    (fun x => φ (u 0 x)) (fun x => φ (u 1 x)) hn
  have hQsupp' : ∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ 7 ∧ h + j ≤ 25 ∧ x + j * d < 2 * tMin := by
    intro j h x hne
    obtain ⟨h1, h2, h3⟩ := hQsupp j h x hne
    have hjd : j * d ≤ j * dMax := Nat.mul_le_mul_left j hd
    dsimp [dMax, tMin] at hjd ⊢
    exact ⟨h1, h2, by omega⟩
  obtain ⟨hQDeg, hQTot, hQWt⟩ := surface_bounds_of_support hQsupp'
  have hQrootG : ∀ z ∈ fam.G, Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    intro z hz
    refine hQroot (φ z) ((fam.q z).map φ)
      (natDegree_map_le.trans (by have := fam.degree_lt z hz; dsimp [dMax] at hd; omega))
      (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (by have := fam.threshold_le z hz; dsimp [N] at ht; omega) ?_
    intro x hx
    have hag := (Finset.mem_filter.mp hx).2
    simpa only [domK, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      eval_map_apply, map_add, map_mul] using congrArg φ hag
  have hLinGap' : (25 * (Lcut + 1 - 25) + 3 * (Lcut + 1) * (25 - 1)) * N <
      (Lcut + 1) * (Lcut + 1 - 25) * (t - d) :=
    successor_lin_gap.trans_le (Nat.mul_le_mul_left _ (by dsimp [t, N, tMin, dMax] at hd ⊢; omega))
  have hJ : N * d < t ^ 2 := by
    have h0 : N * dMax < tMin ^ 2 := by decide
    have h1 : N * d ≤ N * dMax := Nat.mul_le_mul_left N hd
    have h2 : tMin ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left htLo 2
    omega
  obtain ⟨l, H, S, labels, hl, hHsub, hHle, hHrich, hSpos, hSdeg, hTot, hEach⟩ :=
    two_surface_accounting_simple φ fam hn
      (by dsimp [t, N] at ht ⊢; omega : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
      (by dsimp [t, N, dMax] at hd ⊢; omega : d < t) hJ (by decide : 1 ≤ 25) (by decide : 25 < Lcut + 1)
      Q Q hQne hQne hQDeg hQTot hQWt hQTot hQrootG
      (fun _ _ _ _ hfQ _ _ _ => hfQ) hLinGap' hcap
      (char_ok_of_ringChar_gt (by dsimp [tMin] at hchar ⊢; omega : max ((2 * 7 - 2) * (2 * tMin - 1)) 7 < ringChar F))
  have hEachCut : ∀ f ∈ S, labels f ≤ Lcut := by
    intro f hf
    have h1 := hEach f hf
    by_cases hdeg1 : f.natDegree ≤ 1
    · simpa only [hdeg1, ↓reduceIte] using h1
    · simp only [hdeg1, ↓reduceIte] at h1
      have hfLe : f.natDegree ≤ l :=
        (Finset.single_le_sum (f := natDegree) (fun _ _ => Nat.zero_le _) hf).trans (by omega)
      have hlp : logDerivPrice N d t (2 * tMin - 1 - (l - f.natDegree) * d) (25 - H.card) f.natDegree ≤ Lcut :=
        logDerivPrice_le_cut_of_successor hd htLo htHi (Nat.sub_le _ _) (Nat.sub_le _ _)
          (by omega) (by omega)
      exact h1.trans (max_le le_rfl hlp)
  have hScard : S.card ≤ l - H.card := by
    have h1 : S.card = ∑ _f ∈ S, 1 := by simp
    rw [h1, ← hSdeg]
    exact Finset.sum_le_sum fun f hf => hSpos f hf
  have hSumLabels : ∑ f ∈ S, labels f ≤ (7 - H.card) * Lcut :=
    (Finset.sum_le_sum hEachCut).trans (by
      rw [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right Lcut (by omega))
  have hHge3 : 3 ≤ H.card := by
    by_contra! hle2
    have hHbd : (H.biUnion (pointsOn fam)).card ≤ H.card * (e + 1) :=
      Finset.card_biUnion_le.trans
        ((Finset.sum_le_sum fun h hh =>
          line_occupancy_le_e_add_one fam hn (by omega) hte (hHsub hh)).trans_eq (by simp))
    have hmul : H.card * (e + 1) ≤ 2 * (e + 1) := Nat.mul_le_mul_right _ (by omega)
    dsimp [Lcut] at hSumLabels
    omega
  let cMin : ℕ := tMin - (N - tMin) / Lcut
  have hcoreMin : ∀ h ∈ H, cMin ≤ (jointCore dom (u 0) (u 1) h.1 h.2).card := by
    intro h hh
    have h1 := rich_head_core_ge fam hn (by omega : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
      hte (by decide : 0 < Lcut) (hHsub hh) (hHrich h hh)
    have hdiv : e / Lcut ≤ (N - tMin) / Lcut := Nat.div_le_div_right (by dsimp [N, tMin]; omega)
    dsimp [cMin]; omega
  have hNotAllColl : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → ∃ c ∈ H, threeLineDeterminant a b c ≠ 0 := by
    intro a _ b _ hab
    by_contra! hall
    have hcoll : ∀ h ∈ H, lineDeterminant a b h = 0 := fun h hh => by
      rw [lineDet_eq_threeLineDet]; exact hall h hh
    let C (h : LineParameter F) := jointCore dom (u 0) (u 1) h.1 h.2
    let Uset := H.biUnion C
    have hcol := TerminalCollinearHeadCount.collinear_card fam H hHsub a b hab hcoll
    change (H.biUnion (pointsOn fam)).card ≤ Uset.card + (Fintype.card I - Uset.card) * H.card at hcol
    rw [hn] at hcol
    have hUn : Uset.card ≤ N := hn ▸ Finset.card_le_univ Uset
    have hpair : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ ≠ h₂ → (C h₁ ∩ C h₂).card ≤ dMax := fun h₁ hh₁ h₂ hh₂ hne =>
      (pairwise_core_inter_le fam (by omega) (hHsub hh₁) (hHsub hh₂) hne).trans (by omega)
    have hbon := bonferroni_core_union H C hcoreMin hpair
    have hcs := cauchy_core_union H C hcoreMin hpair
    change _ ≤ Uset.card at hbon hcs
    have hUmax : max (H.card * cMin - H.card.choose 2 * dMax)
        ((H.card * cMin ^ 2 + (cMin + (H.card - 1) * dMax) - 1) / (cMin + (H.card - 1) * dMax)) ≤
        Uset.card := max_le hbon hcs
    have hrew : Uset.card + (N - Uset.card) * H.card = H.card * N - (H.card - 1) * Uset.card := by
      have h1 : (N - Uset.card) * H.card + Uset.card * H.card = N * H.card := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hUn]
      have h2 : (H.card - 1) * Uset.card + Uset.card = Uset.card * H.card := by
        rw [Nat.mul_comm Uset.card H.card]
        cases hH0 : H.card with
        | zero => omega
        | succ m => simp [Nat.succ_mul, Nat.add_comm]
      rw [Nat.mul_comm H.card N]; omega
    rw [hrew] at hcol
    have hsub := Nat.sub_le_sub_left (Nat.mul_le_mul_left (H.card - 1) hUmax) (H.card * N)
    have htab := successor_collinear_table ⟨H.card, by omega⟩ hHge3
    dsimp only [cMin, N, tMin, dMax, Lcut] at hsub htab hSumLabels hcol ⊢
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < H.card)
  obtain ⟨c, hc, hdet⟩ := hNotAllColl a ha b hb hab
  have hac : c ≠ a := by intro heq; subst heq; apply hdet; unfold threeLineDeterminant; ring
  have hbc : c ≠ b := by intro heq; subst heq; apply hdet; unfold threeLineDeterminant; ring
  have hHcard3 : H.card = 3 := by
    by_contra hne3
    have h4 : 4 ≤ H.card := by omega
    have hcard3 : ({a, b, c} : Finset (LineParameter F)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac.symm]),
        Finset.card_insert_of_notMem (by simp [hbc.symm]), Finset.card_singleton]
    have hdiff : (H \ {a, b, c}).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)
      omega
    obtain ⟨w, hw⟩ := hdiff
    obtain ⟨hwH, hwNot⟩ := Finset.mem_sdiff.mp hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwNot
    have h4core := ThreeHeadResidualSecant.fourth_core fam a b c w (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact hHsub (by assumption))
      hdet hwNot.1 hwNot.2.1 hwNot.2.2
    rw [hn] at h4core
    change (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
      (jointCore dom (u 0) (u 1) c.1 c.2).card + (jointCore dom (u 0) (u 1) w.1 w.2).card ≤
      N + 4 * d at h4core
    have hca := hcoreMin a ha; have hcb := hcoreMin b hb
    have hcc := hcoreMin c hc; have hcw := hcoreMin w hwH
    dsimp [cMin, N, tMin, Lcut, dMax] at hca hcb hcc hcw h4core hd
    omega
  have hHeq : H = {a, b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [hab, hac.symm]),
        Finset.card_insert_of_notMem (by simp [hbc.symm]), Finset.card_singleton, hHcard3]
  have hHbiU : H.biUnion (pointsOn fam) = pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c := by
    rw [hHeq]; ext z; simp
  have hoff : (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card ≤ 2000025 := by
    have hsubU : pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ⊆ fam.G :=
      Finset.union_subset (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
        (pointsOn_subset_G fam c)
    have hsd := Finset.card_sdiff_add_card_eq_card hsubU
    rw [hHbiU] at hTot
    rw [hHcard3] at hSumLabels
    dsimp [Lcut] at hSumLabels
    omega
  have hcores : ∀ x ∈ ({a, b, c} : Finset _), t - 1 ≤ (jointCore dom (u 0) (u 1) x.1 x.2).card := by
    intro x hx
    by_contra! hsmall
    have hxH : x ∈ H := by rw [hHeq]; exact hx
    have hpack := pointsOn_card_mul_max_add_core_le fam (hHsub hxH)
    rw [ht, hn] at hpack
    have hdef2 : 2 ≤ max 1 (t - (jointCore dom (u 0) (u 1) x.1 x.2).card) := by
      dsimp [t]; omega
    have hxLe : (pointsOn fam x).card ≤ 1 + e / 2 := by
      have hshare := EighthRichDeficits.head_share hte hpack
      have hmono : e / max 1 (t - (jointCore dom (u 0) (u 1) x.1 x.2).card) ≤ e / 2 :=
        Nat.div_le_div_left hdef2 (by decide)
      unfold EighthRichDeficits.price EighthRichDeficits.deficit at hshare
      dsimp [t] at hdef2 hmono hshare ⊢
      omega
    have hbound (y : LineParameter F) (hy : y ∈ H) : (pointsOn fam y).card ≤ e + 1 :=
      line_occupancy_le_e_add_one fam hn (by omega) hte (hHsub hy)
    have hUcard : (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c).card ≤
        (pointsOn fam a).card + (pointsOn fam b).card + (pointsOn fam c).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hsubU : pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ⊆ fam.G :=
      Finset.union_subset (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
        (pointsOn_subset_G fam c)
    have hsd := Finset.card_sdiff_add_card_eq_card hsubU
    have hpa := hbound a ha; have hpb := hbound b hb; have hpc := hbound c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  exact ⟨a, b, c, hHsub ha, hHsub hb, hHsub hc, hdet, hcores, hoff⟩

/-- At `k = 76,695,848` (`d = 76,695,847`) and `e = 715,827,877`, `fam.G.card ≤ 2^31` conditional
on `NonlinearComponentCap logDerivPrice`. -/
theorem residual_secant_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 76695848 δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913947)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  by_contra! hover
  obtain ⟨a, b, c, ha, hb, hc, hdet, hcores, _⟩ :=
    three_saturated_noncollinear_of_over_budget hcap (d := 76695847) (e := 715827877)
      (by decide) (by decide) (by decide) fam hn ht hchar hover
  have hbd := ThreeHeadResidualSecant.core_budget fam (by decide) (by decide) hn ht a b c (by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption) hdet hcores
  omega

/-- Row 1 (`k = 71,582,790`, `e = 715,827,880`): zero outside witnesses can exist. -/
theorem successor_row1_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 71582790 δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913944)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  by_contra! hover
  obtain ⟨a, b, c, ha, hb, hc, hdet, hcores, _⟩ :=
    three_saturated_noncollinear_of_over_budget hcap (d := 71582789) (e := 715827880)
      (by decide) (by decide) (by decide) fam hn ht hchar hover
  have hcov := ThreeHeadDeterminantCover.cover_of_three_noncollinear fam (by decide) a b c
    ha hb hc hdet (by
      have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
      rw [ht, hn]; dsimp [N] at *; omega)
  have hbound (x : LineParameter F) (hx : x ∈ lineParameters fam) : (pointsOn fam x).card ≤ 715827881 :=
    line_occupancy_le_e_add_one fam hn (by omega) (by decide : 357913944 + 715827880 = N) hx
  have h1 := (Finset.card_le_card hcov).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have ha' := hbound a ha; have hb' := hbound b hb; have hc' := hbound c hc
  omega

/-- Rows 4–10 (`ThreeHeadSuccessorIncidence.momentCell i` for all `i : Fin 7`, up to `k = 77,807,386`). -/
theorem successor_moment_cell_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    (i : Fin 7) {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom ((momentCell i).2 + 1) δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = N - (momentCell i).1)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  by_contra! hover
  let e := (momentCell i).1
  let d := (momentCell i).2
  let t := N - e
  have hparams : d ≤ dMax ∧ 715827871 ≤ e ∧ e ≤ 715827880 ∧ 1 ≤ d + 1 ∧ 3 * d ≤ t := by
    fin_cases i <;> decide
  obtain ⟨a, b, c, ha, hb, hc, hdet, hcores, _⟩ :=
    three_saturated_noncollinear_of_over_budget hcap hparams.1 hparams.2.1 hparams.2.2.1
      fam hn ht hchar hover
  let U3 := pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c
  have hU3le : U3.card ≤ 3 * (e + 1) := by
    have hbd (x : LineParameter F) (hx : x ∈ lineParameters fam) : (pointsOn fam x).card ≤ e + 1 :=
      line_occupancy_le_e_add_one (t := t) fam hn (by rw [ht]) (by dsimp [t, N]; omega) hx
    have h1 := (Finset.card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have := hbd a ha; have := hbd b hb; have := hbd c hc
    dsimp only [U3]; omega
  let m : ℕ := 2 * N + 1 - 3 * (e + 1)
  have hOutGe : m ≤ (fam.G \ U3).card := by
    have hsub : U3 ⊆ fam.G := Finset.union_subset
      (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
      (pointsOn_subset_G fam c)
    have hsd := Finset.card_sdiff_add_card_eq_card hsub
    dsimp [m, N] at *; omega
  obtain ⟨Gout, hGoutSub, hGoutCard⟩ := Finset.exists_subset_card_eq hOutGe
  let core3 : Finset I :=
    jointCore dom (u 0) (u 1) a.1 a.2 ∪ jointCore dom (u 0) (u 1) b.1 b.2 ∪
      jointCore dom (u 0) (u 1) c.1 c.2
  let J := {x : I // x ∉ core3}
  have hJcard : Fintype.card J ≤ N + 2 * d - 3 * (t - 1) := by
    have hdegA := lineParameter_degree_lt fam ha
    have hdegB := lineParameter_degree_lt fam hb
    have hdegC := lineParameter_degree_lt fam hc
    have hD := natDegree_threeLineDeterminant_le_two_mul_sub_two hdegA.1 hdegA.2 hdegB.1 hdegB.2 hdegC.1 hdegC.2
    have hU := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b c hdet
    simp only [coreSet_eq_jointCore] at hU
    have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
    have hfc : Fintype.card J = N - core3.card := by
      dsimp only [J]
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hn]
    change (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
      (jointCore dom (u 0) (u 1) c.1 c.2).card ≤ core3.card + _ at hU
    dsimp [t, e, d] at hca hcb hcc hD hU ⊢
    omega
  let A (z : F) : Finset J :=
    Finset.univ.filter fun x : J => x.val ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)
  have hAcard (z : F) (hz : z ∈ fam.G \ U3) : t - 3 * d ≤ (A z).card := by
    have hG := (Finset.mem_sdiff.mp hz).1
    have hoff := (Finset.mem_sdiff.mp hz).2
    simp only [U3, Finset.mem_union, not_or] at hoff
    have hi (l : LineParameter F) (hl : l ∈ lineParameters fam) (hn' : z ∉ pointsOn fam l) :
        (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) l.1 l.2).card ≤ d := by
      have hd' := lineParameter_degree_lt fam hl
      exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) (by omega)
        (fam.degree_lt z hG) hd'.1 hd'.2 (fun he => hn' ((mem_pointsOn_iff fam l z).2 ⟨hG, he⟩))
    have h1 := hi a ha hoff.1.1
    have h2 := hi b hb hoff.1.2
    have h3 := hi c hc hoff.2
    have h4 := Finset.card_union_le
      (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) a.1 a.2)
      (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) b.1 b.2)
    have h5 := Finset.card_union_le
      ((fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) a.1 a.2) ∪
       (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) b.1 b.2))
      (fullAgreement dom (u 0) (u 1) z (fam.q z) ∩ jointCore dom (u 0) (u 1) c.1 c.2)
    have h6 := Finset.card_sdiff_add_card_inter (fullAgreement dom (u 0) (u 1) z (fam.q z)) core3
    simp only [core3, Finset.inter_union_distrib_left] at h6
    have hbij : (A z).card = (fullAgreement dom (u 0) (u 1) z (fam.q z) \ core3).card := by
      refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
      · intro x hx; exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hx).2, x.property⟩
      · intro x₁ _ x₂ _ h; exact Subtype.ext h
      · intro y hy; obtain ⟨h1', h2'⟩ := Finset.mem_sdiff.mp hy
        exact ⟨⟨y, h2'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩, rfl⟩
    have hth := fam.threshold_le z hG
    rw [ht] at hth
    rw [hbij]; dsimp only [t, e, core3] at *; omega
  let s := N + 2 * d - 3 * (t - 1)
  let τ := t - 3 * d
  let h := m * τ / s
  let p := h.choose 2
  let q := h * p - h.choose 3
  have hcell : (∀ a : Fin (m + 1), p * a.val ≤ a.val.choose 3 + q) ∧
      m.choose 3 * d + s * q < p * (m * τ) ∧ 3 * s + 2 * d < 5 * τ ∧
      N + (m - 1) * (N + 4 * d - 3 * (t - 1)) < m * t :=
    ThreeHeadSuccessorIncidence.moment_cells i
  obtain ⟨hsup, hgap, hforce, hcap4⟩ := hcell
  obtain ⟨T, hTmem, hTgt⟩ := ThreeHeadSuccessorIncidence.popular_triple Gout A p q d τ s
    hJcard (fun z hz => hAcard z (hGoutSub hz))
    (fun w hw => hsup ⟨w, by omega⟩) (by rwa [hGoutCard])
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  obtain ⟨g, z₁, z₂, hgz1, hgz2, hz12, hTeq⟩ := Finset.card_eq_three.mp hTcard
  have hgOut : g ∈ fam.G \ U3 := hGoutSub (hTsub (by rw [hTeq]; simp))
  have hz1Out : z₁ ∈ fam.G \ U3 := hGoutSub (hTsub (by rw [hTeq]; simp))
  have hz2Out : z₂ ∈ fam.G \ U3 := hGoutSub (hTsub (by rw [hTeq]; simp))
  have hgG := (Finset.mem_sdiff.mp hgOut).1
  have hz1G := (Finset.mem_sdiff.mp hz1Out).1
  have hz2G := (Finset.mem_sdiff.mp hz2Out).1
  have hTripInter : d < (fullAgreement dom (u 0) (u 1) g (fam.q g) ∩
      fullAgreement dom (u 0) (u 1) z₁ (fam.q z₁) ∩
      fullAgreement dom (u 0) (u 1) z₂ (fam.q z₂)).card := by
    refine hTgt.trans_le ?_
    have hsubC : (HalfPredecessorThirdMomentUpper.commonCoordinates A T).image Subtype.val ⊆
        fullAgreement dom (u 0) (u 1) g (fam.q g) ∩ fullAgreement dom (u 0) (u 1) z₁ (fam.q z₁) ∩
        fullAgreement dom (u 0) (u 1) z₂ (fam.q z₂) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hall : ∀ w ∈ T, x ∈ A w := by
        simpa [HalfPredecessorThirdMomentUpper.commonCoordinates] using hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp (hall g (by rw [hTeq]; simp))).2,
         (Finset.mem_filter.mp (hall z₁ (by rw [hTeq]; simp))).2⟩,
        (Finset.mem_filter.mp (hall z₂ (by rw [hTeq]; simp))).2⟩
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    exact Finset.card_le_card hsubC
  let H4 := secantParameter fam g z₁
  have hH4mem : H4 ∈ lineParameters fam := secantParameter_mem_lineParameters fam hgG hz1G hgz1
  have hslope : slopePolynomial g z₁ (fam.q g) (fam.q z₁) = slopePolynomial g z₂ (fam.q g) (fam.q z₂) := by
    by_contra hne
    exact (Nat.not_lt_of_ge (triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
      (by omega) hgz1 hgz2 (fam.degree_lt g hgG) (fam.degree_lt z₁ hz1G) (fam.degree_lt z₂ hz2G) hne)) hTripInter
  have hgOn : g ∈ pointsOn fam H4 := first_point_mem_pointsOn_secant fam hgG
  have hz1On : z₁ ∈ pointsOn fam H4 := second_point_mem_pointsOn_secant fam hz1G hgz1
  have hz2On : z₂ ∈ pointsOn fam H4 := (mem_pointsOn_iff fam H4 z₂).mpr ⟨hz2G, by
    simpa only [H4, secantParameter] using third_point_on_secant_line_of_slope_eq hgz2 hslope.symm⟩
  let coreH4J : Finset J := Finset.univ.filter fun x : J => x.val ∈ jointCore dom (u 0) (u 1) H4.1 H4.2
  have hthree : 3 * τ ≤ s + 2 * coreH4J.card := by
    have hdisj {w₁ w₂ : F} (hw₁ : w₁ ∈ pointsOn fam H4) (hw₂ : w₂ ∈ pointsOn fam H4) (hne : w₁ ≠ w₂) :
        Disjoint (A w₁ \ coreH4J) (A w₂ \ coreH4J) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      obtain ⟨ha₁, ho₁⟩ := Finset.mem_sdiff.mp hx₁
      obtain ⟨ha₂, _⟩ := Finset.mem_sdiff.mp hx₂
      have h1 := (Finset.mem_filter.mp ha₁).2
      have h2 := (Finset.mem_filter.mp ha₂).2
      obtain ⟨_, hq₁⟩ := (mem_pointsOn_iff fam H4 w₁).mp hw₁
      obtain ⟨_, hq₂⟩ := (mem_pointsOn_iff fam H4 w₂).mp hw₂
      rw [hq₁] at h1; rw [hq₂] at h2
      have he1 := (Finset.mem_filter.mp h1).2
      have he2 := (Finset.mem_filter.mp h2).2
      simp only [eval_add, eval_mul, eval_C] at he1 he2
      have hv : H4.2.eval (dom x.val) = u 1 x.val := by
        have hdiff : (w₁ - w₂) * (H4.2.eval (dom x.val) - u 1 x.val) = 0 := by linear_combination he1 - he2
        exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne))
      have hu : H4.1.eval (dom x.val) = u 0 x.val := by rw [hv] at he1; exact add_right_cancel he1
      exact ho₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hv⟩⟩)
    have hdis1 := hdisj hgOn hz1On hgz1
    have hdis2 := hdisj hgOn hz2On hgz2
    have hdis3 := hdisj hz1On hz2On hz12
    have hun1 : ((A g \ coreH4J) ∪ (A z₁ \ coreH4J) ∪ (A z₂ \ coreH4J)).card =
        (A g \ coreH4J).card + (A z₁ \ coreH4J).card + (A z₂ \ coreH4J).card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdis2, hdis3⟩),
        Finset.card_union_of_disjoint hdis1]
    have hsubAll : ((A g \ coreH4J) ∪ (A z₁ \ coreH4J) ∪ (A z₂ \ coreH4J)).card ≤ s - coreH4J.card := by
      have hsub' : (A g \ coreH4J) ∪ (A z₁ \ coreH4J) ∪ (A z₂ \ coreH4J) ⊆ Finset.univ \ coreH4J := by
        intro x hx; simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
        rcases hx with (⟨_, ho⟩ | ⟨_, ho⟩) | ⟨_, ho⟩ <;> exact ⟨Finset.mem_univ _, ho⟩
      have h1 := Finset.card_le_card hsub'
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at h1
      omega
    have hsd1 := Finset.card_sdiff_add_card_inter (A g) coreH4J
    have hsd2 := Finset.card_sdiff_add_card_inter (A z₁) coreH4J
    have hsd3 := Finset.card_sdiff_add_card_inter (A z₂) coreH4J
    have hi1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := A g) (s₂ := coreH4J))
    have hi2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := A z₁) (s₂ := coreH4J))
    have hi3 := Finset.card_le_card (Finset.inter_subset_right (s₁ := A z₂) (s₂ := coreH4J))
    have hgA := hAcard g hgOut; have hz1A := hAcard z₁ hz1Out; have hz2A := hAcard z₂ hz2Out
    have hcLe : coreH4J.card ≤ s := (Finset.card_le_univ _).trans hJcard
    omega
  have hGoutOnH4 : Gout ⊆ pointsOn fam H4 := by
    intro w hw
    by_contra hwNot
    have hwOut := hGoutSub hw
    have hwG := (Finset.mem_sdiff.mp hwOut).1
    have hdH4 := lineParameter_degree_lt fam hH4mem
    have hov : (A w ∩ coreH4J).card ≤ d := by
      have hle := fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) (by omega)
        (fam.degree_lt w hwG) hdH4.1 hdH4.2 (fun he => hwNot ((mem_pointsOn_iff fam H4 w).mpr ⟨hwG, he⟩))
      have hsubI : (A w ∩ coreH4J).image Subtype.val ⊆
          fullAgreement dom (u 0) (u 1) w (fam.q w) ∩ jointCore dom (u 0) (u 1) H4.1 H4.2 := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx1).2, (Finset.mem_filter.mp hx2).2⟩
      rw [← Finset.card_image_of_injective _ Subtype.val_injective]
      exact (Finset.card_le_card hsubI).trans (by omega)
    have hun := Finset.card_union_add_card_inter (A w) coreH4J
    have hleS : (A w ∪ coreH4J).card ≤ s := (Finset.card_le_univ _).trans hJcard
    have hwA := hAcard w hwOut
    exact ThreeHeadSuccessorIncidence.three_force_line hthree (by omega : τ + coreH4J.card ≤ s + d) hforce
  have hH4neA : H4 ≠ a := fun he => (Finset.mem_sdiff.mp hgOut).2
    (Finset.mem_union_left _ (Finset.mem_union_left _ (he ▸ hgOn)))
  have hH4neB : H4 ≠ b := fun he => (Finset.mem_sdiff.mp hgOut).2
    (Finset.mem_union_left _ (Finset.mem_union_right _ (he ▸ hgOn)))
  have hH4neC : H4 ≠ c := fun he => (Finset.mem_sdiff.mp hgOut).2
    (Finset.mem_union_right _ (he ▸ hgOn))
  have h4c := ThreeHeadResidualSecant.fourth_core fam a b c H4 (by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption) hdet hH4neA hH4neB hH4neC
  rw [hn] at h4c
  change (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
    (jointCore dom (u 0) (u 1) c.1 c.2).card + (jointCore dom (u 0) (u 1) H4.1 H4.2).card ≤
    N + 4 * d at h4c
  have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
  have hc4 : (jointCore dom (u 0) (u 1) H4.1 H4.2).card ≤ N + 4 * d - 3 * (t - 1) := by
    dsimp [t, e] at hca hcb hcc ⊢; omega
  have hpack := pointsOn_card_mul_max_add_core_le fam hH4mem
  rw [ht, hn] at hpack
  have hmLe : m ≤ (pointsOn fam H4).card := by rw [← hGoutCard]; exact Finset.card_le_card hGoutOnH4
  have hmul : m * (t - (jointCore dom (u 0) (u 1) H4.1 H4.2).card) +
      (jointCore dom (u 0) (u 1) H4.1 H4.2).card ≤ N :=
    (Nat.add_le_add_right (Nat.mul_le_mul hmLe (Nat.le_max_right 1 _)) _).trans hpack
  have hmt : m * t ≤ N + (m - 1) * (jointCore dom (u 0) (u 1) H4.1 H4.2).card := by
    have hm1 : 1 ≤ m := by fin_cases i <;> decide
    have hcLeT : (jointCore dom (u 0) (u 1) H4.1 H4.2).card ≤ t := by
      have : N + 4 * d - 3 * (t - 1) ≤ t := by fin_cases i <;> decide
      omega
    have h1 : m * (t - (jointCore dom (u 0) (u 1) H4.1 H4.2).card) +
        m * (jointCore dom (u 0) (u 1) H4.1 H4.2).card = m * t := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hcLeT]
    have h2 : (m - 1) * (jointCore dom (u 0) (u 1) H4.1 H4.2).card +
        (jointCore dom (u 0) (u 1) H4.1 H4.2).card = m * (jointCore dom (u 0) (u 1) H4.1 H4.2).card := by
      cases hm0 : m with
      | zero => omega
      | succ r => simp [Nat.succ_mul, Nat.add_comm]
    omega
  have hmulC := Nat.mul_le_mul_left (m - 1) hc4
  omega

#print axioms three_saturated_noncollinear_of_over_budget
#print axioms residual_secant_badCount_le
#print axioms successor_row1_badCount_le
#print axioms successor_moment_cell_badCount_le

end ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorReduction
