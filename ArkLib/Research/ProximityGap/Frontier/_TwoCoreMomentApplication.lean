/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount
import ArkLib.Research.ProximityGap.Frontier._TwoCoreMomentForcing

/-!
# A two-line bound for the production rate-sixteenth Reed–Solomon code

If no pair of points in a large subfamily determines a large core, line packing
bounds the collinear fraction and every collinear triple's common agreement.
The production moment contradiction then supplies a large-core secant from the
subfamily. Applying this first to the whole family and then outside that secant
bounds the number of bad scalars by twice the error allowance plus two.
-/

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.TwoCoreMomentApplication

private theorem line_card_le_of_small_core {e t z L : ℕ} (hz : z < t - 1626881)
    (hp : L * max 1 (t - z) + z ≤ e + t) : L ≤ 1 + e / 1626882 := by
  have hwidth : 1626882 ≤ t - z := by omega
  rw [max_eq_right (by omega : 1 ≤ t - z)] at hp
  cases L with
  | zero => omega
  | succ m =>
    rw [Nat.succ_mul] at hp
    have hm := Nat.mul_le_mul_left m hwidth
    omega

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- The cap for actual rich families throughout the production interval. -/
theorem production_family_card_le (fam : BadScalarRichPointFamily dom k δ u)
    {e t : ℕ} (hn : Fintype.card ι = 1073741824) (het : e + t = 1073741824)
    (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = t)
    (htlo : 426115517 ≤ t) (hthi : t ≤ 570425344) :
    fam.G.card ≤ 2 * e + 2 := by
  classical
  apply TwoLargeCoreCount.card_le_two_mul_add_two fam (zmin := t - 1626881)
    hk (by omega) (by omega) ht (by omega)
  intro H hH hsize
  by_contra hnone
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  have hsmall {a b : F} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) :
      (D (secantParameter fam a b)).card < t - 1626881 := by
    by_contra! h
    exact hnone ⟨a, ha, b, hb, hab, h⟩
  let B := 1 + e / 1626882
  have hline (l : LineParameter F) : (linePoints H (onFamilyLine fam) l).card ≤ B := by
    by_cases htwo : 1 < (linePoints H (onFamilyLine fam) l).card
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
      obtain ⟨haH, hal⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbH, hbl⟩ := Finset.mem_filter.mp hb
      have hl : secantParameter fam a b = l :=
        secantParameter_eq_of_mem_pointsOn fam l hal hbl hab
      have hz := hsmall haH hbH hab
      rw [hl] at hz
      have hpar := secantParameter_mem_lineParameters fam (hH haH) (hH hbH) hab
      rw [hl] at hpar
      have hp := pointsOn_card_mul_max_add_core_le fam hpar
      rw [ht, hn, ← het] at hp
      have hcap := line_card_le_of_small_core hz hp
      have hsub : linePoints H (onFamilyLine fam) l ⊆ pointsOn fam l :=
        fun _ h => (Finset.mem_filter.mp h).2
      exact (Finset.card_le_card hsub).trans hcap
    · dsimp only [B]
      omega
  apply TwoCoreMomentForcing.production_small_lines_impossible H (selectedAgreements fam)
    (onFamilyLine fam) (secantParameter fam) t B hn (by omega) htlo hthi
  · intro a ha
    simpa only [ht, selectedAgreements] using fam.threshold_le a (hH ha)
  · dsimp only [B]
    omega
  · intro a ha b hb hab
    exact ⟨first_point_mem_pointsOn_secant fam (beta := b) (hH ha),
      second_point_mem_pointsOn_secant fam (hH hb) hab⟩
  · intro l a b hab hal hbl
    exact (secantParameter_eq_of_mem_pointsOn fam l hal hbl hab).symm
  · exact hline
  · intro T hT hnc
    have hTG : T ∈ fam.G.powersetCard 3 :=
      Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hT).1.trans hH, (Finset.mem_powersetCard.mp hT).2⟩
    exact (tripleWeight_le_degree_pred_of_not_collinear fam hk T hTG hnc).trans (by omega)
  · intro T hT
    obtain ⟨hTH, hc, l, hl⟩ := (mem_collinearTriples_iff H (onFamilyLine fam) T).mp hT
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have hal : a ∈ pointsOn fam l := hl a ha
    have hbl : b ∈ pointsOn fam l := hl b hb
    have heq := secantParameter_eq_of_mem_pointsOn fam l hal hbl hab
    have hz := hsmall (hTH ha) (hTH hb) hab
    rw [heq] at hz
    have hcore : selectedAgreements fam a ∩ selectedAgreements fam b = D l := by
      rw [selectedAgreements, selectedAgreements, (mem_pointsOn_iff fam l a).mp hal |>.2,
        (mem_pointsOn_iff fam l b).mp hbl |>.2]
      exact fullAgreement_inter_eq_jointCore dom (u 0) (u 1) l.1 l.2 hab
    have hsub : commonCoordinates (selectedAgreements fam) T ⊆
        selectedAgreements fam a ∩ selectedAgreements fam b := by
      intro i hi
      simp only [commonCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_inter.mpr ⟨hi a ha, hi b hb⟩
    have h := Finset.card_le_card hsub
    rw [hcore] at h
    omega

end ArkLib.ProximityGap.Frontier.TwoCoreMomentApplication

#print axioms ArkLib.ProximityGap.Frontier.TwoCoreMomentApplication.production_family_card_le
