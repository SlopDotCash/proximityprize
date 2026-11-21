/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._TwoCoreMomentApplication
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeConditionedCubic

/-! # Conditioning a family of bad scalars on an agreement coordinate and a secant core -/

open Finset hiding falling
open Polynomial
open _root_.ProximityGap Code
open _root_.ProximityGap.SecondPrimeConditionedCubic
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeConditionedIncidence

private theorem falling_cast (n : ℕ) : falling n = 6*(n.choose 3 : ℚ) := by
  rcases n with _ | n
  · norm_num [falling]
  rcases n with _ | n
  · norm_num [falling, Nat.choose]
  have h := Nat.descFactorial_eq_factorial_mul_choose (n+2) 3
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  have h' := congrArg ((↑) : ℕ → ℚ) h
  push_cast at h'
  dsimp [falling]
  push_cast
  nlinarith only [h']

private theorem sum_multiplicity {U Point : Type*} [DecidableEq U] (S : Finset U) (H : Finset Point)
    (A : Point → Finset U) :
    (∑ i ∈ S, (H.filter (fun x => i ∈ A x)).card) = ∑ x ∈ H, ((A x) ∩ S).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.inter_comm, ← Finset.sum_filter]
  congr 1

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

private abbrev core (dom : ι ↪ F) (u : WordStack F (Fin 2) ι) (l : LineParameter F) :=
  jointCore dom (u 0) (u 1) l.1 l.2

private theorem off_line (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) {l : LineParameter F} (hl : l ∈ lineParameters fam)
    {x : F} (hx : x ∈ fam.G) (hoff : x ∉ pointsOn fam l) :
    (selectedAgreements fam x ∩ core dom u l).card ≤ k-1 := by
  have hdeg := lineParameter_degree_lt fam hl
  apply fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
    (fam.degree_lt x hx) hdeg.1 hdeg.2
  exact fun he => hoff ((mem_pointsOn_iff fam l x).mpr ⟨hx, he⟩)

private theorem weighted_cap (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι = 1073741824) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 426114723)
    (H : Finset F) (hH : H ⊆ fam.G) (M z B : ℕ) (hM : H.card = M)
    (hB : 1 ≤ B) (hZ : z ≤ 426114723) (hprice : 647627101 < B * (426114723 + 1 - z))
    (hsmall : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (core dom u (secantParameter fam a b)).card < z) :
    (∑ i, falling ((H.filter fun x => i ∈ selectedAgreements fam x).card : ℚ)) ≤
      ((67108863*M*(M-1)*(M-2)+(B-2)*(z-1-67108863)*M*(M-1) : ℕ) : ℚ) := by
  classical
  have hline (l : LineParameter F) : (linePoints H (onFamilyLine fam) l).card ≤ B := by
    by_cases htwo : 1 < (linePoints H (onFamilyLine fam) l).card
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
      obtain ⟨haH, hal⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbH, hbl⟩ := Finset.mem_filter.mp hb
      have he := secantParameter_eq_of_mem_pointsOn fam l hal hbl hab
      have hs := hsmall a haH b hbH hab
      have hl := secantParameter_mem_lineParameters fam (hH haH) (hH hbH) hab
      rw [he] at hs hl
      have hp := pointsOn_card_mul_max_add_core_le fam hl
      rw [ht, hn] at hp
      change (pointsOn fam l).card * max 1 (426114723 - (core dom u l).card) +
        (core dom u l).card ≤ 1073741824 at hp
      have hz : 1 ≤ 426114723 - (core dom u l).card := by omega
      rw [max_eq_right hz] at hp
      have hsub : linePoints H (onFamilyLine fam) l ⊆ pointsOn fam l :=
        fun _ h => (Finset.mem_filter.mp h).2
      apply (Finset.card_le_card hsub).trans
      by_contra! h
      have hh := Nat.mul_le_mul (show B+1 ≤ (pointsOn fam l).card by omega)
        (show 426114723 - (core dom u l).card ≤ 426114723 - (core dom u l).card by rfl)
      rw [Nat.succ_mul] at hh
      have hw := Nat.mul_le_mul_left B (show 426114723+1-z ≤ 426114723-(core dom u l).card by omega)
      omega
    · omega
  have hupper := ThirdMomentUpperLineCap.weightedTripleSum_upper_lineCap H (onFamilyLine fam)
    (secantParameter fam) (fun T => (commonCoordinates (selectedAgreements fam) T).card)
    67108863 (z-1-67108863) B
    (fun a ha b hb hab => ⟨first_point_mem_pointsOn_secant fam (beta := b) (hH ha),
      second_point_mem_pointsOn_secant fam (hH hb) hab⟩)
    (fun l a b hab hal hbl => (secantParameter_eq_of_mem_pointsOn fam l hal hbl hab).symm) hline
    (fun T hT hnc => by
      obtain ⟨hTH, hc⟩ := Finset.mem_powersetCard.mp hT
      have htG := Finset.mem_powersetCard.mpr ⟨hTH.trans hH, hc⟩
      exact (tripleWeight_le_degree_pred_of_not_collinear fam hk T htG hnc).trans (by omega))
    (fun T hT => by
      obtain ⟨hTH, hc, l, hl⟩ := (mem_collinearTriples_iff H (onFamilyLine fam) T).mp hT
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
      have hal : a ∈ pointsOn fam l := hl a ha
      have hbl : b ∈ pointsOn fam l := hl b hb
      have he := secantParameter_eq_of_mem_pointsOn fam l hal hbl hab
      have hs := hsmall a (hTH ha) b (hTH hb) hab
      rw [he] at hs
      have hh : selectedAgreements fam a ∩ selectedAgreements fam b = core dom u l := by
        rw [selectedAgreements, selectedAgreements, (mem_pointsOn_iff fam l a).mp hal |>.2,
          (mem_pointsOn_iff fam l b).mp hbl |>.2]
        exact fullAgreement_inter_eq_jointCore dom (u 0) (u 1) l.1 l.2 hab
      have hsub : commonCoordinates (selectedAgreements fam) T ⊆
          selectedAgreements fam a ∩ selectedAgreements fam b := by
        intro i hi
        simp only [commonCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_inter.mpr ⟨hi a ha, hi b hb⟩
      have hh' := Finset.card_le_card hsub
      rw [hh] at hh'
      omega)
  rw [← sum_choose_incidence_eq_sum_commonCoordinates_card, hM] at hupper
  simp only [falling_cast, ← Finset.mul_sum]
  exact_mod_cast hupper

omit [Nonempty ι] [Fintype F] in
private theorem total_mass (fam : BadScalarRichPointFamily dom k δ u)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 426114723)
    (H : Finset F) (hH : H ⊆ fam.G) :
    H.card * 426114723 ≤ ∑ i, (H.filter fun x => i ∈ selectedAgreements fam x).card := by
  rw [sum_multiplicity]
  simpa using (Finset.sum_le_sum (s := H) (f := fun _ => 426114723)
    (g := fun x => (selectedAgreements fam x).card) (fun x hx =>
      ht ▸ fam.threshold_le x (hH hx)))

private theorem seed (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι = 1073741824) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 426114723)
    (hsize : 2147483649 ≤ fam.G.card) :
    ∃ l ∈ lineParameters fam, 172000000 ≤ (core dom u l).card := by
  classical
  obtain ⟨G, hG, hM⟩ := Finset.exists_subset_card_eq hsize
  have hex : ∃ i : ι, 852229447 ≤ (G.filter fun x => i ∈ selectedAgreements fam x).card := by
    by_contra! h
    have hh := Finset.sum_le_sum (s := (univ : Finset ι))
      (g := fun _ => 852229446) (fun x _ => Nat.le_of_lt_succ (h x))
    have hm := total_mass fam ht G hG
    rw [hM] at hm
    simp only [sum_const, card_univ, hn, nsmul_eq_mul] at hh
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨H, hHi, hHm⟩ := Finset.exists_subset_card_eq hi
  have hH : H ⊆ fam.G := hHi.trans ((Finset.filter_subset ..).trans hG)
  let m (j : ι) := (H.filter fun x => j ∈ selectedAgreements fam x).card
  have hmi : m i = 852229447 := by
    dsimp only [m]
    rw [Finset.filter_eq_self.mpr (fun x hx => (Finset.mem_filter.mp (hHi hx)).2), hHm]
  let S := (univ : Finset ι).erase i
  have hS : S.card = 1073741823 := by
    dsimp only [S]
    rw [card_erase_of_mem (mem_univ _), card_univ, hn]
  have hmass := total_mass fam ht H hH
  change H.card * 426114723 ≤ ∑ j, m j at hmass
  rw [hHm, ← sum_erase_add _ _ (mem_univ i), hmi] at hmass
  have hrest : 852229447 * 426114722 ≤ ∑ j ∈ S, m j := by dsimp only [S]; omega
  let v : ℚ := 852229447 * 426114722 /1073741823
  have hl := uniform_cubic S (fun j => (m j : ℚ)) v (fun _ _ => Nat.cast_nonneg _) (by norm_num [v])
    (by rw [hS]; norm_num [v]; exact_mod_cast hrest)
  rw [hS] at hl
  by_contra! hnone
  have hu := weighted_cap fam hn hk hkmax ht H hH 852229447 172000000 3 hHm
    (by decide) (by decide) (by decide) (fun a ha b hb hab =>
      hnone _ (secantParameter_mem_lineParameters fam (hH ha) (hH hb) hab))
  change ∑ j, falling (m j : ℚ) ≤ _ at hu
  rw [← sum_erase_add _ _ (mem_univ i), hmi] at hu
  change (∑ j ∈ S, falling (m j : ℚ)) + _ ≤ _ at hu
  norm_num [v, falling] at hl hu
  linarith only [hl,hu]

private theorem conditioned (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι = 1073741824) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 426114723)
    {l : LineParameter F} (hl : l ∈ lineParameters fam) (hz : 172000000 ≤ (core dom u l).card)
    (G : Finset F) (hG : G ⊆ fam.G) (hoff : ∀ x ∈ G, x ∉ pointsOn fam l)
    (hsize : 204602343 ≤ G.card) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ 350093427 ≤ (core dom u (secantParameter fam a b)).card := by
  classical
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hz
  obtain ⟨H, hH, hM⟩ := Finset.exists_subset_card_eq hsize
  let T := (univ : Finset ι) \ S
  have hTc : T.card = 901741824 := by
    dsimp only [T]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn, hSc]
  let m (i : ι) := (H.filter fun x => i ∈ selectedAgreements fam x).card
  have hsv : (∑ i ∈ S, m i) ≤ 204602343*67108863 := by
    dsimp only [m]
    rw [sum_multiplicity]
    calc
      _ ≤ ∑ _x ∈ H, 67108863 := Finset.sum_le_sum (fun x hx => by
        have h1 := off_line fam hk hl (hG (hH hx)) (hoff x (hH hx))
        have h2 := Finset.card_le_card (show selectedAgreements fam x ∩ S ⊆ selectedAgreements fam x ∩ core dom u l from
          fun j hj => mem_inter.mpr ⟨(mem_inter.mp hj).1, hS (mem_inter.mp hj).2⟩)
        omega)
      _ = _ := by simp [hM]
  have hmass := total_mass fam ht H (hH.trans hG)
  change H.card * 426114723 ≤ ∑ j, m j at hmass
  rw [hM, ← Finset.sum_sdiff (Finset.subset_univ S)] at hmass
  have htotal : 204602343 * 426114723 ≤ (∑ i ∈ S, m i) + ∑ i ∈ T, m i := by
    dsimp only [T]; omega
  let a : ℚ := 204602343*67108863/172000000
  let b : ℚ := 204602343*(426114723-67108863)/901741824
  have hlow := split_cubic S T (fun j => (m j : ℚ)) (fun j => (m j : ℚ)) a b
    (by norm_num [a]) (by norm_num [a,b]) (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (by rw [hSc]; norm_num [a]; exact_mod_cast hsv)
    (by rw [hSc,hTc]; norm_num [a,b]; exact_mod_cast htotal)
  rw [hSc,hTc] at hlow
  by_contra! hnone
  have hu := weighted_cap fam hn hk hkmax ht H (hH.trans hG) 204602343 350093427 9 hM
    (by decide) (by decide) (by decide) (fun x hx y hy hxy => hnone x (hH hx) y (hH hy) hxy)
  change ∑ j, falling (m j : ℚ) ≤ _ at hu
  rw [← Finset.sum_sdiff (Finset.subset_univ S)] at hu
  change (∑ i ∈ T, falling (m i : ℚ)) + (∑ i ∈ S, falling (m i : ℚ)) ≤ _ at hu
  norm_num [a,b,falling] at hlow hu
  linarith only [hlow, hu]

/-- Every bad-scalar witness family fits the second field budget at this predecessor. -/
theorem family_card_le (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι = 1073741824) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 426114723) :
    fam.G.card ≤ 2147483648 := by
  classical
  by_contra! hbig
  obtain ⟨l₀, hl₀, hz₀⟩ := seed fam hn hk hkmax ht hbig
  have cap (l : LineParameter F) (hl : l ∈ lineParameters fam) : (pointsOn fam l).card ≤ 647627102 :=
    TwoLargeCoreCount.line_occupancy_le (e := 647627101) fam hn ht hl
  let H₀ := fam.G \ pointsOn fam l₀
  have h₀ : H₀ ⊆ fam.G := sdiff_subset
  have hcount₀ := card_le_card_sdiff_add_card (s := fam.G) (t := pointsOn fam l₀)
  change fam.G.card ≤ H₀.card + _ at hcount₀
  have hcap₀ := cap l₀ hl₀
  have extract (G : Finset F) (hG : G ⊆ H₀) (hsize : 204602343 ≤ G.card) :
      ∃ l ∈ lineParameters fam, 350093427 ≤ (core dom u l).card ∧
        ∃ x ∈ G, x ∈ pointsOn fam l := by
    obtain ⟨a, ha, b, hb, hab, hz⟩ := conditioned fam hn hk hkmax ht hl₀ hz₀ G (hG.trans h₀)
      (fun x hx => (mem_sdiff.mp (hG hx)).2) hsize
    exact ⟨_, secantParameter_mem_lineParameters fam (h₀ (hG ha)) (h₀ (hG hb)) hab,
      hz, a, ha, first_point_mem_pointsOn_secant fam (beta := b) (h₀ (hG ha))⟩
  obtain ⟨l₁, hl₁, hz₁, _, _, _⟩ := extract H₀ (by rfl) (by omega)
  let H₁ := H₀ \ pointsOn fam l₁
  have h₁ : H₁ ⊆ H₀ := sdiff_subset
  have hcount₁ := card_le_card_sdiff_add_card (s := H₀) (t := pointsOn fam l₁)
  change H₀.card ≤ H₁.card + _ at hcount₁
  have hcap₁ := cap l₁ hl₁
  obtain ⟨l₂, hl₂, hz₂, x₂, hx₂, hx₂l⟩ := extract H₁ h₁ (by omega)
  have hne₁₂ : l₁ ≠ l₂ := fun e => (mem_sdiff.mp hx₂).2 (e ▸ hx₂l)
  let H₂ := H₁ \ pointsOn fam l₂
  have h₂ : H₂ ⊆ H₁ := sdiff_subset
  have hcount₂ := card_le_card_sdiff_add_card (s := H₁) (t := pointsOn fam l₂)
  change H₁.card ≤ H₂.card + _ at hcount₂
  have hcap₂ := cap l₂ hl₂
  obtain ⟨l₃, hl₃, hz₃, x₃, hx₃, hx₃l⟩ := extract H₂ (h₂.trans h₁) (by omega)
  have hne₂₃ : l₂ ≠ l₃ := fun e => (mem_sdiff.mp hx₃).2 (e ▸ hx₃l)
  have hne₁₃ : l₁ ≠ l₃ := fun e => (mem_sdiff.mp (h₂ hx₃)).2 (e ▸ hx₃l)
  let D := core dom u
  have pair {a b : LineParameter F} (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
      (hne : a ≠ b) : (D a ∩ D b).card ≤ 67108863 :=
    (HalfPredecessorRateEighthFullWiring.jointCore_inter_card_le_degree_pred fam hk ha hb hne).trans
      (by omega)
  have h₁₂ := pair hl₁ hl₂ hne₁₂
  have h₁₃ := pair hl₁ hl₃ hne₁₃
  have h₂₃ := pair hl₂ hl₃ hne₂₃
  let U := D l₁ ∪ D l₂ ∪ D l₃
  have hU : 848953692 ≤ U.card := by
    have hu₁ := card_union_add_card_inter (D l₁) (D l₂)
    have hu₂ := card_union_add_card_inter (D l₁ ∪ D l₂) (D l₃)
    have hi : (D l₁ ∪ D l₂) ∩ D l₃ = D l₁ ∩ D l₃ ∪ D l₂ ∩ D l₃ := by ext; simp; tauto
    rw [hi] at hu₂
    have hbound := card_union_le (D l₁ ∩ D l₃) (D l₂ ∩ D l₃)
    change 350093427 ≤ (D l₁).card at hz₁
    change 350093427 ≤ (D l₂).card at hz₂
    change 350093427 ≤ (D l₃).card at hz₃
    dsimp only [U]
    omega
  let L := pointsOn fam l₁ ∪ pointsOn fam l₂ ∪ pointsOn fam l₃
  have sub : fam.G ⊆ L := by
    intro x hx
    by_contra hnL
    dsimp only [L] at hnL
    simp only [mem_union, not_or] at hnL
    let A := selectedAgreements fam x
    have hA (l : LineParameter F) (hl : l ∈ lineParameters fam) (hxL : x ∉ pointsOn fam l) :
        (A ∩ D l).card ≤ 67108863 := (off_line fam hk hl hx hxL).trans (by omega)
    have hA₁ := hA l₁ hl₁ hnL.1.1
    have hA₂ := hA l₂ hl₂ hnL.1.2
    have hA₃ := hA l₃ hl₃ hnL.2
    have hi : (A ∩ U).card ≤ 3*67108863 := by
      simp only [U, inter_union_distrib_left]
      have h₁' := card_union_le (A ∩ D l₁) (A ∩ D l₂)
      have h₂' := card_union_le (A ∩ D l₁ ∪ A ∩ D l₂) (A ∩ D l₃)
      omega
    have hcomp : A \ U ⊆ (univ : Finset ι) \ U := by intro i h; exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp h).2⟩
    have hc := card_le_card hcomp
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn] at hc
    have hall := card_sdiff_add_card_inter A U
    have hr := fam.threshold_le x hx
    change _ ≤ A.card at hr
    rw [ht] at hr
    omega
  have hcap₃ := cap l₃ hl₃
  have hL₁ := card_union_le (pointsOn fam l₁) (pointsOn fam l₂)
  have hL₂ := card_union_le (pointsOn fam l₁ ∪ pointsOn fam l₂) (pointsOn fam l₃)
  have hsub := card_le_card sub
  dsimp only [L] at hsub
  omega

#print axioms family_card_le

end ArkLib.ProximityGap.Frontier.SecondPrimeConditionedIncidence
