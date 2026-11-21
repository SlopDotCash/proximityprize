/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeficitWindow
import ArkLib.Research.ProximityGap.Frontier.QuarterRateFreshPairExtension
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicCharacteristic

/-! # The exact two-head numerator through the degree-saturated rate-sixteenth step -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SixteenthSaturatedHeads
open SecondPrimeActualPopulations HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterComplementaryCores
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private theorem heavy_pair (fam : Family dom δ u) {p e : ℕ} [CharP F p]
    (hp : 1744830589<p) (hn : Fintype.card I=1073741824) (hl : 610000000≤e) (hu : e≤671088639)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e) (large : 2*(e+1)<fam.G.card) :
    ∃ a∈lineParameters fam, ∃ b∈lineParameters fam, a≠b ∧
      400000000 < (pointsOn fam a).card ∧ 300000000 < (pointsOn fam b).card := by
  classical
  obtain ⟨U,hU,hcov,hcomp⟩ := FiveEighthThreeHeadCover.linear_cover fam hp hn hl hu ht large
  let P := population fam (algebraMap F (AlgebraicClosure F))
  have hfirst : ∃ f∈U, 400000000<(P f).card := by
    by_contra! none
    have hs := sum_le_sum none
    simp only [sum_const,smul_eq_mul] at hs
    have all := (card_le_card hcov).trans card_biUnion_le
    change fam.G.card≤∑ j∈U,(P j).card at all
    omega
  obtain ⟨f,hf,hfpop⟩ := hfirst
  obtain ⟨a,ha,hfa⟩ := hcomp f hf (by change 48<(P f).card; omega)
  have hcap := TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht ha
  let M := pointsOn fam a
  let V := U.erase f
  have cov : fam.G ⊆ M ∪ V.biUnion (fun g => P g \ M) := by
    intro z hz
    by_cases hm : z∈M
    · exact mem_union_left _ hm
    obtain ⟨g,hg,hzg⟩ := mem_biUnion.mp (hcov hz)
    have hgf : g≠f := fun h => hm (hfa (h ▸ hzg))
    exact mem_union_right _ (mem_biUnion.mpr ⟨g,mem_erase.mpr ⟨hgf,hg⟩,mem_sdiff.mpr ⟨hzg,hm⟩⟩)
  have hsecond : ∃ g∈V, 300000000 < (P g \ M).card := by
    by_contra! none
    have hs := sum_le_sum none
    simp only [sum_const,smul_eq_mul] at hs
    have huge := (card_le_card cov).trans ((card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _))
    change fam.G.card≤(pointsOn fam a).card+ ∑ j∈V,(P j \ M).card at huge
    have hv : V.card=U.card-1 := card_erase_of_mem hf
    omega
  obtain ⟨g,hg,hgpop⟩ := hsecond
  have hsize : (P g \ M).card≤(P g).card := card_le_card sdiff_subset
  obtain ⟨b,hb,hgb⟩ := hcomp g (mem_of_mem_erase hg) (by change 48<(P g).card; omega)
  refine ⟨a,ha,b,hb,?_,hfpop.trans_le (card_le_card hfa),hgpop.trans_le (hsize.trans (card_le_card hgb))⟩
  intro heq
  have hsub : P g ⊆ M := by simpa only [M,heq] using hgb
  rw [sdiff_eq_empty_iff_subset.mpr hsub,card_empty] at hgpop
  omega

/-- Any violation of the two-head count has two distinct secants with core deficits
of at most one and two sites, respectively. -/
theorem near_full_pair (fam : Family dom δ u) {p e : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (hl : 610000000≤e) (hu : e≤671088639)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e) (large : 2*(e+1)<fam.G.card) :
    ∃ a∈lineParameters fam, ∃ b∈lineParameters fam, a≠b ∧
      400000000 < (pointsOn fam a).card ∧ 300000000 < (pointsOn fam b).card ∧
      1073741824-e-1 ≤ (jointCore dom (u 0) (u 1) a.1 a.2).card ∧
      1073741824-e-2 ≤ (jointCore dom (u 0) (u 1) b.1 b.2).card := by
  obtain ⟨a,ha,b,hb,hab,hA,hB⟩ := heavy_pair fam hp hn hl hu ht large
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let t := 1073741824-e
  have pack (l : LineParameter F) (h : l ∈ lineParameters fam) :
      (pointsOn fam l).card*max 1 (t-(D l).card)+(D l).card≤1073741824 := by
    have hh := pointsOn_card_mul_max_add_core_le fam h
    rwa [ht,hn] at hh
  have nearA : t-1≤(D a).card := by
    have h := Nat.mul_le_mul hA (Nat.le_max_right 1 (t-(D a).card))
    have h' := pack _ ha
    dsimp [t] at *
    omega
  have nearB : t-2≤(D b).card := by
    have h := Nat.mul_le_mul hB (Nat.le_max_right 1 (t-(D b).card))
    have h' := pack _ hb
    dsimp [t] at *
    omega
  exact ⟨a,ha,b,hb,hab,hA,hB,nearA,nearB⟩

/-- Every received pair has at most two full secants' worth of bad scalars,
including the endpoint where the complement estimate alone can attain equality. -/
theorem family_cap (fam : Family dom δ u) {p e : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (hl : 610000000≤e) (hu : e≤648719019)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e) : fam.G.card≤2*(e+1) := by
  classical
  by_contra! large
  obtain ⟨a,ha,b,hb,hab,hA,hB,nearA,nearB⟩ := near_full_pair fam hp hn hl (by omega) ht large
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let t := 1073741824-e
  change t-1≤(D a).card at nearA
  change t-2≤(D b).card at nearB
  have hole : t≤(univ \ (D a ∪ D b)).card+2*67108863 := by
    by_contra! below
    have cc := G_subset_two_lines_of_small_core_complement fam (by decide) (h:=t-1)
      (by rw [ht]; dsimp [t]; omega) a b ha hb (by simpa only [show t-1+1=t by dsimp [t]; omega] using below)
    have hg := (card_le_card cc).trans (card_union_le ..)
    have h1 := TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht ha
    have h2 := TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht hb
    omega
  have hi : (D a ∩ D b).card≤67108863 := jointCore_inter_card_le_degree_pred fam (by decide) ha hb hab
  have huAB := card_union_add_card_inter (D a) (D b)
  have hnU := (card_le_univ (D a ∪ D b)).trans_eq hn
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at hole
  by_cases short : (D b).card+2≤t
  · have one := QuarterRateFreshPairExtension.points_on_one_short fam hb ha hab.symm ht.ge short
      (by change 67108863≤(D b ∩ D a).card+1; rw [inter_comm]; dsimp [t] at *; omega)
    change (pointsOn fam b).card≤(univ \ (D b ∪ D a)).card+1 at one
    rw [union_comm,card_sdiff_of_subset (subset_univ _),card_univ,hn] at one
    dsimp [t] at *
    omega
  · have saturated := QuarterRateSaturatedCores.points_on_saturated fam ha hb hab
      (by change 67108863≤(D a ∩ D b).card; dsimp [t] at *; omega)
    change (pointsOn fam a).card≤(univ \ (D a ∪ D b)).card+1 at saturated
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at saturated
    dsimp [t] at *
    omega

/-- Uniform rate-sixteenth probability bound, including at every positive interleaving width. -/
theorem eps_upper (dom : I ↪ F) (hn : Fintype.card I=n) {p e : ℕ} [CharP F p]
    (hp : 1744830589<p) (hl : 610000000≤e) (hu : e≤648719019) (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) ≤
      ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  apply epsMCA_le_of_badCount_le
  intro u
  apply family_cap (canonicalBadScalarRichPointFamily dom (k:=k) ((e:ℝ≥0)/n) u (by decide)) hp hn hl hu
  rw [hn]
  have h := TwoCorePackingThreshold.agreement_ceiling e (by change e≤1073741824; omega)
  rw [Fintype.card_fin] at h
  exact h

/-- On large fields two full affine secants attain the bound on every injective domain. -/
theorem exact_mass (dom : I ↪ F) (hn : Fintype.card I=n) {p e : ℕ} [CharP F p]
    (hp : 1744830589<p) (hl : 610000000≤e) (hu : e≤648719019)
    (hq : (2*(e+1)).choose 2≤Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) :=
  le_antisymm (eps_upper dom hn hp hl hu width)
    (ThreeHeadDeficitWindow.eps_interval dom hn hp (x:=671088640-e) (by omega) (by omega) hl hq width).1

/-- For every field of sufficient characteristic, the exact budget threshold is its
integer half-budget. This also classifies safety at every real radius. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I=n) {p B : ℕ} [CharP F p]
    (hp : 1744830589<p) (hB : Fintype.card F/2^128=B) (hl : 1220000002≤B)
    (hu : B≤1297438041) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    mcaDeltaStar (F:=F) C tolerance=((B/2:ℕ):ℝ≥0)/n ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) C δ≤tolerance ↔ δ<((B/2:ℕ):ℝ≥0)/n := by
  dsimp only
  let e := B/2-1
  have he : 610000000≤e := by dsimp [e]; omega
  have he' : e≤648719019 := by dsimp [e]; omega
  have ratio := (BoundarySecurityBudget.count_ratio_le_iff (Fintype.card_pos (α:=F)) (by decide : 0<2^128)).2
    (show 2*(e+1)≤Fintype.card F/2^128 by dsimp [e]; omega)
  have safe := (eps_upper dom hn hp he he' width).trans
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ratio : _ ≤ tolerance)
  have bad := ThreeHeadDeficitWindow.two_head_bad dom hn (e:=B/2) (by omega) (by omega) (by omega)
  have bad' : tolerance < epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) (((B/2:ℕ):ℝ≥0)/n) := by
    rw [epsMCA_interleaved_eq]; exact bad
  have left := ThreeHeadDeficitWindow.successor_le_supremum dom hn (by dsimp [n]; omega) width safe
  rw [show e+1=B/2 by dsimp [e]; omega] at left
  have pin := le_antisymm (mcaDeltaStar_le_of_bad _ _ bad') left
  refine ⟨pin,fun δ => ⟨?_,?_⟩⟩
  · intro good
    by_contra! hδ
    exact bad'.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! fail
    exact hδ.not_ge (pin ▸ mcaDeltaStar_le_of_bad _ _ fail)

/-- Smoothness and the finite budget discharge the characteristic condition,
including for non-prime fields. -/
theorem smooth_threshold (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I=n)
    {B : ℕ} (hB : Fintype.card F/2^128=B) (hl : 1220000002≤B) (hu : B≤1297438041)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    mcaDeltaStar (F:=F) C tolerance=((B/2:ℕ):ℝ≥0)/n ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) C δ≤tolerance ↔ δ<((B/2:ℕ):ℝ≥0)/n := by
  have h := SmoothCubicCharacteristic.characteristic dom hn (by omega)
  exact classification dom hn (p:=ringChar F) (by omega) hB hl hu width

/-- Prime-field specialization for all injective domains. -/
theorem prime_threshold {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 1220000002≤B) (hu : B≤1297438041) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    mcaDeltaStar (F:=ZMod p) C tolerance=((B/2:ℕ):ℝ≥0)/n ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) C δ≤tolerance ↔ δ<((B/2:ℕ):ℝ≥0)/n :=
  classification dom hn (p:=p) (by omega) (by simpa only [ZMod.card] using hB) hl hu width

#print axioms smooth_threshold
#print axioms prime_threshold
#print axioms exact_mass
#print axioms family_cap
end ArkLib.ProximityGap.Frontier.SixteenthSaturatedHeads
