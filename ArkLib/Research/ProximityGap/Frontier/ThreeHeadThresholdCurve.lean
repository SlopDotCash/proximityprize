/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FiveEighthsPlateauThreshold
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicBudgetWindow

/-! # The five-eighths plateau and the following three-head interval -/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ThreeHeadThresholdCurve
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- One formula gives the first failing count on 581,610,155 consecutive prime-field budgets. -/
theorem prime_classification {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 1565873494≤B) (hu : B≤2147483648) (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((max 671088640 (B/3):ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  dsimp only
  by_cases hh : B≤2013265922
  · rw [max_eq_left (by omega : B/3≤671088640)]
    have eqn : ((671088640:ℕ):ℝ≥0)/n=5/8 := by norm_num [n]
    rw [eqn]
    exact FiveEighthsPlateauThreshold.prime_classification dom hn (by omega) (by omega) width
  · rw [max_eq_right (by omega : 671088640≤B/3)]
    exact UniversalCubicBudgetWindow.prime_classification dom hn hB (by omega) hu width

/-- Equality at every Hamming count from the plateau endpoint, including the first step.
The quadratic field-size condition separates all projected labels. -/
theorem exact_eps (dom : I ↪ F) (hn : Fintype.card I=n) {p e : ℕ} [CharP F p]
    (hp : 1744830589<p) (hl : 671088640≤e) (hu : e≤715827881)
    (hq : (3*(e+1)).choose 2≤Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  refine le_antisymm (UniversalCubicBudgetWindow.eps_upper dom hn (.inl hp) hl hu) ?_
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have hg := ExceptionalHeadLocatorMass.grid_mass (m:=3) (t:=n-e) (k:=k) x ((e:ℝ≥0)/n)
    (by decide) (by decide) (by dsimp [n,k]; omega) (Nat.sub_le ..) (by dsimp [n,k]; omega)
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub])
  rw [show n-(n-e)=e by dsimp [n]; omega] at hg
  have hret : 3*(e+1) ≤ AveragedPencilProjection.retained (3*(e+1)) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hq),Nat.sub_zero]
    exact le_max_left ..
  exact (ENNReal.div_le_div_right (by exact_mod_cast hret) _).trans hg

/-- A common field-size floor gives 44,739,242 consecutive exact probabilities at all widths. -/
theorem prime_exact_eps {p e : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hp : 2305843008139952128≤p) (hl : 671088640≤e) (hu : e≤715827881)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  have hq : (3*(e+1)).choose 2 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    apply (Nat.choose_le_choose 2 (by omega : 3*(e+1)≤2147483648)).trans
    rw [Nat.choose_two_right]
    omega
  simpa only [ZMod.card] using exact_eps dom hn (p:=p) (by omega) hl hu hq width

#print axioms prime_classification
#print axioms prime_exact_eps
end ArkLib.ProximityGap.Frontier.ThreeHeadThresholdCurve
