/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._TwoCoreMomentApplication
import ArkLib.Research.ProximityGap.Frontier._IncidenceTripleMass
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-! # The two-line upper bound at general finite parameters

Two numerical inequalities force two polynomial lines to cover all bad scalars.
The first compares the cubic incidence moment with the common agreements of a
noncollinear triple. The second uses the size of the two extracted line cores.
-/
namespace ProximityGap.GeneralTwoLineSafety

open Finset Code
open ArkLib.ProximityGap.Frontier
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap
open scoped NNReal ENNReal BigOperators

private theorem cube_le (v : ℕ) : v^3 ≤ 6*v.choose 3+3*v^2 := by
  have h2 := Nat.choose_succ_right_eq v 1
  have h3 := Nat.choose_succ_right_eq v 2
  norm_num only [Nat.reduceAdd, Nat.choose_one_right] at h2 h3
  by_cases hv : 2 ≤ v
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hv
    rw [show 2+j-1=1+j by omega] at h2
    rw [show 2+j-2=j by omega] at h3
    nlinarith [congrArg (fun x : ℕ => x*j) h2]
  · interval_cases v <;> decide

/-- A line cap and a bound on noncollinear triple agreement imply a finite cubic inequality. -/
theorem cubic_cap {I A Line : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (H : Finset A) (S : A → Finset I) (onLine : Line → A → Prop) (line : A → A → Line)
    {k t L : ℕ} (hM : 0 < H.card) (hrich : ∀ i ∈ H, t ≤ (S i).card)
    (hpair : ∀ i ∈ H, ∀ j ∈ H, i ≠ j → onLine (line i j) i ∧ onLine (line i j) j)
    (hunique : ∀ l i j, i ≠ j → onLine l i → onLine l j → l=line i j)
    (hline : ∀ l, (linePoints H onLine l).card ≤ L)
    (hnoncol : ∀ T ∈ H.powersetCard 3, ¬ Collinear onLine T →
      (commonCoordinates S T).card ≤ k) (hL : 2 ≤ L) :
    H.card*t^3 ≤ H.card*k*(Fintype.card I)^2+(L+2)*(Fintype.card I)^3 := by
  classical
  let M := H.card
  let n := Fintype.card I
  let v (x : I) := (H.filter fun i => x ∈ S i).card
  have hsum : ∑ x, v x = ∑ i ∈ H, (S i).card := by
    simp only [v,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hMsum : M*t ≤ ∑ x, v x := by
    rw [hsum]
    simpa only [M,sum_const,nsmul_eq_mul,Nat.cast_id] using sum_le_sum (s := H) (fun i hi => hrich i hi)
  have hv (x : I) : v x ≤ M := card_filter_le _ _
  have hu := weightedTripleSum_upper_lineCap H onLine line
    (fun T => (commonCoordinates S T).card) k n L hpair hunique hline hnoncol
    (fun T _ => (Finset.card_le_univ (commonCoordinates S T)).trans (by dsimp [n]; omega))
  rw [← sum_choose_incidence_eq_sum_commonCoordinates_card H S] at hu
  change 6*∑ x, (v x).choose 3 ≤ k*M*(M-1)*(M-2)+(L-2)*n*M*(M-1) at hu
  have hub : 6*∑ x, (v x).choose 3 ≤ k*M^3+(L-2)*n*M^2 := by
    apply hu.trans
    calc k*M*(M-1)*(M-2)+(L-2)*n*M*(M-1)
        ≤ k*M*M*M+(L-2)*n*M*M := by gcongr <;> omega
      _ = _ := by ring
  have hcub : ∑ x, (v x)^3 ≤ 6*(∑ x, (v x).choose 3)+3*n*M^2 := by
    calc ∑ x, (v x)^3 ≤ ∑ x : I, (6*(v x).choose 3+3*M^2) := by
            exact sum_le_sum fun x _ => (cube_le _).trans (by gcongr; exact hv x)
      _ = _ := by simp only [sum_add_distrib,← Finset.mul_sum,sum_const,card_univ,nsmul_eq_mul];
                  dsimp [n]; ring
  have hbound : ∑ x, (v x)^3 ≤ k*M^3+(L+2)*n*M^2 := by
    apply hcub.trans
    have base := Nat.add_le_add_right hub (3*n*M^2)
    apply base.trans
    have he : L-2+2=L := by omega
    nlinarith [congrArg (fun l : ℕ => l*n*M^2) he]
  have hc := IncidenceTripleMass.nat_cube_sum_le_card_sq_mul_sum_cube v
  have ht := (Nat.pow_le_pow_left hMsum 3).trans (hc.trans (Nat.mul_le_mul_left (n^2) hbound))
  have hd : M^2*(M*t^3) ≤ M^2*(M*k*n^2+(L+2)*n^3) := by
    calc _ = (M*t)^3 := by ring
      _ ≤ _ := ht
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hd (pow_pos hM 2)

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F] {D : I ↪ F} {k : ℕ} {δ : ℝ≥0}
  {u : WordStack F (Fin 2) I}

/-- Any selected subfamily of at least e+2 bad challenges determines a polynomial
line with at least t−⌊n/L⌋ common original-row agreements. -/
theorem exists_large_core (fam : BadScalarRichPointFamily D k δ u) {n t e L : ℕ}
    (hn : Fintype.card I = n) (hk : 1≤k) (hL : 2≤L)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (H : Finset F) (hH : H ⊆ fam.G) (hcard : e+2 ≤ H.card) :
    ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ t-n/L ≤
      (jointCore D (u 0) (u 1) (secantParameter fam a b).1 (secantParameter fam a b).2).card := by
  classical
  let z := t-n/L
  obtain ⟨G,hGH,hG⟩ := exists_subset_card_eq hcard
  have sub : G ⊆ fam.G := hGH.trans hH
  by_contra! hnone
  have hcap (l : LineParameter F) : (linePoints G (onFamilyLine fam) l).card ≤ L := by
    by_contra! large
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < (linePoints G (onFamilyLine fam) l).card by omega)
    obtain ⟨haG,hal⟩ := mem_filter.mp ha
    obtain ⟨hbG,hbl⟩ := mem_filter.mp hb
    have hl := secantParameter_eq_of_mem_pointsOn fam l hal hbl hab
    have hpar := secantParameter_mem_lineParameters fam (sub haG) (sub hbG) hab
    rw [hl] at hpar
    let c := (jointCore D (u 0) (u 1) l.1 l.2).card
    have hp := pointsOn_card_mul_max_add_core_le fam hpar
    rw [ht,hn] at hp
    change (pointsOn fam l).card * max 1 (t-c) + c ≤ n at hp
    have hsub : linePoints G (onFamilyLine fam) l ⊆ pointsOn fam l :=
      fun _ h => (mem_filter.mp h).2
    have hlower : L ≤ (pointsOn fam l).card := large.le.trans (card_le_card hsub)
    have hc : L*(t-c) ≤ n := (Nat.mul_le_mul hlower (le_max_right 1 (t-c))).trans (by omega)
    have hd : t-c ≤ n/L := (Nat.le_div_iff_mul_le (by omega : 0<L)).2 (by simpa [mul_comm] using hc)
    have small := hnone a (hGH haG) b (hGH hbG) hab
    rw [hl] at small
    change c < z at small
    dsimp [z] at small
    omega
  have bound := cubic_cap G (selectedAgreements fam) (onFamilyLine fam) (secantParameter fam)
    (k := k) (t := t) (L := L) (by omega) (fun a ha => by
      simpa only [ht,selectedAgreements] using fam.threshold_le a (sub ha))
    (fun a ha b hb hab => ⟨first_point_mem_pointsOn_secant fam (beta := b) (sub ha),
      second_point_mem_pointsOn_secant fam (sub hb) hab⟩)
    (fun l a b hab hal hbl => (secantParameter_eq_of_mem_pointsOn fam l hal hbl hab).symm)
    hcap (fun T htT hnc => by
      have hT : T ∈ fam.G.powersetCard 3 := mem_powersetCard.mpr
        ⟨(mem_powersetCard.mp htT).1.trans sub,(mem_powersetCard.mp htT).2⟩
      exact (tripleWeight_le_degree_pred_of_not_collinear fam hk T hT hnc).trans (Nat.sub_le _ _)) hL
  rw [hG,hn] at bound
  omega

/-- General two-line safety for each rich-point family arising from a fixed pair of words. -/
theorem family_card_le (fam : BadScalarRichPointFamily D k δ u) {n t e L : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (htk : k≤t) (hL : 2≤L)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+3*k)*L+2*n < 3*t*L) : fam.G.card ≤ 2*e+2 := by
  classical
  let z := t-n/L
  have geom : n+3*(k-1) < t+2*z := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right L h
    have h2 := Nat.mul_le_mul_right L (show t ≤ z+n/L by dsimp [z]; omega)
    have h3 := Nat.div_mul_le_self n L
    have h4 := Nat.mul_le_mul_right (3*L) (Nat.sub_le k 1)
    nlinarith
  apply TwoLargeCoreCount.card_le_two_mul_add_two fam hk (by omega) (hn.trans he.symm) ht
    (hn ▸ geom)
  intro H hH hcard
  exact exists_large_core fam hn hk hL ht hm H hH hcard

open Classical in
/-- The actual number of bad scalars is bounded uniformly for arbitrary received words. -/
theorem count_le (D : I ↪ F) (u₀ u₁ : I → F) (δ : ℝ≥0) {n k t e L : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (htk : k≤t) (hL : 2≤L)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+3*k)*L+2*n < 3*t*L) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card ≤ 2*e+2 :=
  family_card_le (canonicalBadScalarRichPointFamily D (k := k) δ ![u₀,u₁] hk)
    hn he hk htk hL ht hm hg

/-- The corresponding proximity error upper bound normalized by the field size. -/
theorem epsMCA_le (D : I ↪ F) (δ : ℝ≥0) {n k t e L : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (htk : k≤t) (hL : 2≤L)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+3*k)*L+2*n < 3*t*L) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤
      ((2*e+2 : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le _ _ _ (fun u => count_le D (u 0) (u 1) δ hn he hk htk hL ht hm hg)

#print axioms family_card_le
#print axioms count_le
#print axioms epsMCA_le

end ProximityGap.GeneralTwoLineSafety
