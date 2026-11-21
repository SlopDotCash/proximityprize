/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalCubicBudgetWindow
import ArkLib.Research.ProximityGap.Frontier.ExceptionalHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier.FiveEighthThreeHeadCover
import ArkLib.Research.ProximityGap.Frontier.PlateauThreeHeadPredecessor

/-! # Rate-one-sixteenth crossing at five eighths

At the crossing, three polynomial heads fit exactly on the domain.
A population bound at the preceding Hamming count suffices for every real radius.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.FiveEighthsPlateauThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity HalfPredecessorBadEventRichPointBridge
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- The three exceptional heads already exceed the entire plateau budget at radius five eighths. -/
theorem endpoint_bad (dom : I ↪ F) (hn : Fintype.card I=n)
    (hu : Fintype.card F/2^128≤2013265922) :
    tolerance < epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) (5/8) := by
  classical
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have hs := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  exact ExceptionalHeadLocatorMass.over_budget_128 (m:=3) (t:=402653184) x (5/8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [tsub_mul,one_mul,tsub_le_iff_right]; norm_num [n]) (by omega) (by unfold n; omega)

/-- A sharp predecessor count, together with the endpoint attack, classifies all real radii. -/
theorem classification_of_cap (dom : I ↪ F) (hn : Fintype.card I=n)
    (hl : 1565873494≤Fintype.card F/2^128) (hu : Fintype.card F/2^128≤2013265922)
    (hcap : ∀ u : Code.WordStack F (Fin 2) I, (canonicalBadScalarRichPointFamily dom
      (k:=k) (671088639/n) u (by decide)).G.card≤1565873494)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance=5/8 ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<5/8 := by
  classical
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) k
  have hb := endpoint_bad dom hn hu
  have hp : epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) (671088639/n)≤tolerance := by
    have hcount := epsMCA_le_of_badCount_le (ReedSolomon.code dom k : Set (I → F)) (671088639/n) 1565873494 hcap
    have hratio := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0<2^128)).2 hl
    exact hcount.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hratio)
  have hpin : mcaDeltaStar (F:=F) (ReedSolomon.code dom k : Set (I → F)) tolerance=5/8 := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    have heq : ((671088640:ℝ≥0)/n)=5/8 := by norm_num [n]
    rw [← heq]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a:=671088640) (by decide) (by decide) _ _
      (by rw [← hre]; exact hp) (by rw [← hre]; change tolerance < epsMCA (F:=F) _ ((671088640:ℝ≥0)/n); rwa [heq])
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact hpin,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    exact hδ.not_ge (hpin ▸ mcaDeltaStar_le_of_bad _ _ bad)

/-- Every received pair is within the plateau budget at the preceding Hamming count. -/
theorem predecessor_cap (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p]
    (hp : 1744830589<p) (u : Code.WordStack F (Fin 2) I) :
    (canonicalBadScalarRichPointFamily dom (k:=k) (671088639/n) u (by decide)).G.card≤1565873494 := by
  classical
  let fam := canonicalBadScalarRichPointFamily dom (k:=k) (671088639/n) u (by decide)
  change fam.G.card ≤ 1565873494
  have ht : ⌈(1-(671088639:ℝ≥0)/n)*(Fintype.card I:ℝ≥0)⌉₊=402653185 := by
    rw [hn]
    have h := TwoCorePackingThreshold.agreement_ceiling 671088639 (by decide)
    rw [Fintype.card_fin] at h
    exact h
  by_contra! hbig
  obtain ⟨H,hH,hthree,hlarge,hex⟩ := FiveEighthThreeHeadCover.cover fam hp hn ht hbig
  exact hbig.not_ge (PlateauThreeHeadPredecessor.cap fam hn ht H hH hthree.le hlarge (by omega))

/-- All positive widths on every injective domain have exactly the good radii below five eighths. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p]
    (hp : 1744830589<p) (hl : 1565873494≤Fintype.card F/2^128)
    (hu : Fintype.card F/2^128≤2013265922) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance=5/8 ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<5/8 :=
  classification_of_cap dom hn hl hu (predecessor_cap dom hn hp) width

/-- The field budget discharges the characteristic constraint in prime fields. -/
theorem prime_classification {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hl : 1565873494≤p/2^128) (hu : p/2^128≤2013265922) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance=5/8 ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<5/8 :=
  classification dom hn (p:=p) (by omega) (by simpa only [ZMod.card] using hl)
    (by simpa only [ZMod.card] using hu) width

#print axioms prime_classification
#print axioms endpoint_bad
#print axioms classification_of_cap
end ArkLib.ProximityGap.Frontier.FiveEighthsPlateauThreshold
