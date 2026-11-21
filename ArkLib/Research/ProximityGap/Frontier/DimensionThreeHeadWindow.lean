/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionMultiplierMCA
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadThresholdCurve

/-! # Simultaneous dimension and budget intervals for three-head line-MCA

On an arbitrary domain of size $2^{30}$, the dimension transfer gives the
three-head security bound at every smaller dimension. The exceptional-head
construction realizes its full numerator once three private blocks fit. At
dimension two this is supplied by the affine common-locator construction.
-/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.DimensionThreeHeadWindow
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- The numerator cap holds for all smaller positive dimensions, independent of
whether the three-head lower construction fits at that dimension. -/
theorem eps_upper (dom : I ↪ F) (hn : Fintype.card I = n) {p d e : ℕ} [CharP F p]
    (hp : 1744830589 < p) (hd : 0 < d) (hd' : d ≤ k) (hl : 671088640 ≤ e) (hu : e ≤ 715827881) :
    epsMCA (F := F) (ReedSolomon.code dom d : Set (I → F)) ((e : ℝ≥0)/n) ≤
      ((3*(e+1) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  have ha := TwoCorePackingThreshold.agreement_ceiling e (by dsimp [n]; omega)
  rw [Fintype.card_fin] at ha
  exact (DimensionMultiplierMCA.epsMCA_mono_dimension dom hd hd' _
    (by rw [hn, ha]; dsimp [n,k]; omega)).trans
      (UniversalCubicBudgetWindow.eps_upper dom hn (.inl hp) hl hu)

/-- All three heads fit when three times the agreement count is at most the
domain length plus twice the message dimension. -/
private theorem mass (dom : I ↪ F) (hn : Fintype.card I = n) {d e : ℕ}
    (hd : 2 ≤ d) (hd' : d ≤ k) (he : e ≤ 715827882) (hfit : 3*(n-e) ≤ n+2*d) :
    ((AveragedPencilProjection.retained (3*(e+1)) (Fintype.card F) : ℕ) : ℝ≥0∞) /
      (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (ReedSolomon.code dom d : Set (I → F)) ((e : ℝ≥0)/n) := by
  classical
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have hsize : (1-(e : ℝ≥0)/n)*n ≤ ((n-e : ℕ) : ℝ≥0) := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num [n]), ← Nat.cast_tsub]
  have hle : n-e ≤ n := Nat.sub_le ..
  have hlt : d < n-e := by dsimp [n,k] at *; omega
  have hcnt : n-(n-e)=e := by dsimp [n] at *; omega
  by_cases h3 : 3 ≤ d
  · have h := ExceptionalHeadLocatorMass.grid_mass (m := 3) (k := d) (t := n-e) x _
      (by decide) h3 hlt hle (by omega) hsize
    rwa [hcnt] at h
  · have h := ManyHeadLocatorMass.grid_mass (m := 3) (k := d) (t := n-e) x _
      (by decide) hd hlt hle (by dsimp [n] at *; omega) hsize
    rwa [hcnt] at h

/-- The exact line-MCA error on each of the 44,739,242 Hamming steps in the
three-head window, whenever the dimension and field separate all keys. -/
theorem exact_eps (dom : I ↪ F) (hn : Fintype.card I = n) {p d e : ℕ} [CharP F p]
    (hp : 1744830589 < p) (hd : 2 ≤ d) (hd' : d ≤ k) (hl : 671088640 ≤ e)
    (hu : e ≤ 715827881) (hfit : 3*(n-e) ≤ n+2*d)
    (hq : (3*(e+1)).choose 2 ≤ Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom d : Set (I → F)) ^⋈ (Fin width)) ((e : ℝ≥0)/n) =
      ((3*(e+1) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  refine le_antisymm (eps_upper dom hn hp (by omega) hd' hl hu) ?_
  have h := mass dom hn hd hd' (by omega : e ≤ 715827882) hfit
  have hretain : 3*(e+1) ≤ AveragedPencilProjection.retained (3*(e+1)) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hq), Nat.sub_zero]
    exact le_max_left ..
  exact (ENNReal.div_le_div_right (by exact_mod_cast hretain) _).trans h

/-- At 128-bit security the full sharp interval transfers to each dimension
allowing three private blocks at the first failing grid point. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I = n) {p B d : ℕ} [CharP F p]
    (hp : 1744830589 < p) (hB : Fintype.card F / 2^128 = B)
    (hl : 2013265923 ≤ B) (hu : B ≤ 2147483648)
    (hd : 2 ≤ d) (hd' : d ≤ k) (hfit : 3*(n-B/3) ≤ n+2*d) (width : ℕ) [NeZero width] :
    let t := ((B/3 : ℕ) : ℝ≥0)/n
    mcaDeltaStar (F := F) ((ReedSolomon.code dom d : Set (I → F)) ^⋈ (Fin width)) tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom d : Set (I → F)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ < t := by
  classical
  let e := B/3
  let t : ℝ≥0 := (e : ℝ≥0)/n
  let t₀ : ℝ≥0 := ((e-1 : ℕ) : ℝ≥0)/n
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) d
  have he : e ≤ 715827882 := by dsimp [e]; omega
  have hatt := mass dom hn hd hd' he hfit
  have hbound : Fintype.card F ≤ 2^256 := by
    have h := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0 < 2^128)
    omega
  have hbad := AveragedPencilProjection.tolerance_budget_lt_retained (by decide : 0 < 2^128)
    (show Fintype.card F ≤ (2^128)^2 by convert hbound using 1)
    (show Fintype.card F / 2^128 < 3*(e+1) by dsimp [e]; omega)
  have hb : tolerance < epsMCA (F := F) (ReedSolomon.code dom d : Set (I → F)) t := by
    by_contra! good
    apply hbad.not_ge
    apply (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).mp
    exact hatt.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using good)
  have hprev : epsMCA (F := F) (ReedSolomon.code dom d : Set (I → F)) t₀ ≤ tolerance := by
    have hcount := eps_upper dom hn hp (by omega : 0 < d) hd' (e := e-1)
      (by dsimp [e]; omega) (by omega)
    have hratio := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).2
      (show 3*((e-1)+1) ≤ Fintype.card F / 2^128 by dsimp [e]; omega)
    exact hcount.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hratio)
  have heq : mcaDeltaStar (F := F) (ReedSolomon.code dom d : Set (I → F)) tolerance = t := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a := e) (by dsimp [e]; omega) (by dsimp [n]; omega) _ _
      (by rw [← hre]; exact hprev) (by rw [← hre]; exact hb)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    exact hδ.not_ge (heq ▸ mcaDeltaStar_le_of_bad _ _ bad)

/-- In prime fields the budget and upper field-size tests suffice. -/
theorem prime_classification {p B d : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I = n)
    (hB : p/2^128 = B) (hl : 2013265923 ≤ B) (hu : B ≤ 2147483648)
    (hd : 2 ≤ d) (hd' : d ≤ k) (hfit : 3*(n-B/3) ≤ n+2*d) (width : ℕ) [NeZero width] :
    let t := ((B/3 : ℕ) : ℝ≥0)/n
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom d : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F := ZMod p) ((ReedSolomon.code dom d : Set (I → ZMod p)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ < t := by
  exact classification dom hn (p := p) (by omega) (by simpa only [ZMod.card] using hB) hl hu hd hd' hfit width

#print axioms exact_eps
#print axioms prime_classification
end ArkLib.ProximityGap.Frontier.DimensionThreeHeadWindow
