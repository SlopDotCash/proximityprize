/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorIncidenceAssembly

/-!
# A pair of agreement sets forces all witnesses onto its secant

Sixteen large agreement sets have a large pairwise intersection by the second
moment. A witness outside the corresponding secant cannot agree on enough
positions of that intersection. The ordinary line-packing bound then applies.
-/

set_option autoImplicit false
open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open scoped NNReal BigOperators

namespace ArkLib.ProximityGap.Frontier.RateQuarterPairOverlap

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- A pairwise second-moment criterion for the sharp single-line count. -/
theorem family_card_of_pair_mass (fam : BadScalarRichPointFamily dom k δ u) {e t : ℕ}
    (hn : Fintype.card ι = e+t) (hk : 1≤k) (he : 14≤e)
    (ht : ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊ = t)
    (gap : (e+t)*(16*(e+t)+16*15*(e+(k-1))) < (16*t)^2) : fam.G.card ≤ e+1 := by
  classical
  by_contra! counter
  obtain ⟨S,hs,hs16⟩ := Finset.exists_subset_card_eq (show 16 ≤ fam.G.card by omega)
  let A := selectedAgreements fam
  have hcap (a : F) (ha : a ∈ S) (b : F) (hb : b ∈ S) (hab : a≠b) :
      (A a ∩ A b).card ≤ e+(k-1) := by
    let l := secantParameter fam a b
    let D := jointCore dom (u 0) (u 1) l.1 l.2
    have hl : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam (hs ha) (hs hb) hab
    have hal := first_point_mem_pointsOn_secant fam (beta := b) (hs ha)
    have hbl := second_point_mem_pointsOn_secant fam (hs hb) hab
    have hcore : A a ∩ A b = D := by
      rw [show A a = selectedAgreements fam a by rfl,show A b = selectedAgreements fam b by rfl,
        selectedAgreements, selectedAgreements, (mem_pointsOn_iff fam l a).mp hal |>.2,
        (mem_pointsOn_iff fam l b).mp hbl |>.2]
      exact fullAgreement_inter_eq_jointCore dom (u 0) (u 1) l.1 l.2 hab
    have occ := TwoLargeCoreCount.line_occupancy_le fam hn ht hl
    have part := pointsOn_card_add_outsideLine_card fam l
    obtain ⟨g,hg⟩ := Finset.card_pos.mp (by omega : 0<(outsideLine fam l).card)
    have fresh := threshold_sub_pred_le_fresh_card fam l hk hl hg
    have hsub : (fullAgreement dom (u 0) (u 1) g (fam.q g) \ D) ⊆ Dᶜ :=
      fun _ h => Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2
    have bound := Finset.card_le_card hsub
    rw [Finset.card_compl,hn] at bound
    have hd := Finset.card_le_univ D
    rw [hn] at hd
    rw [ht] at fresh
    change t-(k-1) ≤ (fullAgreement dom (u 0) (u 1) g (fam.q g) \ D).card at fresh
    rw [hcore]
    omega
  have low : 16*t ≤ ∑ a ∈ S, (A a).card := by
    calc
      16*t = ∑ _a ∈ S, t := by simp [hs16]
      _ ≤ _ := sum_le_sum fun a ha => ht ▸ fam.threshold_le a (hs ha)
  have diag : ∑ a ∈ S, (A a).card ≤ 16*(e+t) := by
    calc
      _ ≤ ∑ _a ∈ S, Fintype.card ι := sum_le_sum fun a _ => Finset.card_le_univ (A a)
      _ = _ := by simp [hs16,hn]
  have cs := GCXK25SecondMoment.sq_sum_card_le_card_mul_sum_sum_card_inter S A
  rw [GCXK25SecondMoment.sum_sum_card_inter_eq_diag_add_offdiag,hn] at cs
  have off := GCXK25SecondMoment.offdiag_le S A hcap
  rw [hs16] at off
  exact gap.not_ge ((Nat.pow_le_pow_left low 2).trans
    (cs.trans (Nat.mul_le_mul_left _ (Nat.add_le_add diag off))))

/-- The actual boundary-field budget fits all code dimensions up to one quarter. -/
theorem family_card_le (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι = 1073741824) (hk : 1≤k) (hkmax : k≤268435456)
    (ht : ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊=805306367) : fam.G.card ≤ 268435458 := by
  apply family_card_of_pair_mass (e := 268435457) (t := 805306367) fam hn hk (by decide) ht
  have h : k-1 ≤ 268435455 := by omega
  omega

#print axioms family_card_of_pair_mass
#print axioms family_card_le

end ArkLib.ProximityGap.Frontier.RateQuarterPairOverlap
