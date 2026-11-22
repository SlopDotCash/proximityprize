/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListSampling
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryReflectionRow
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-! # A list threshold from non-dihedral pair bounds at arbitrary block length and width -/
namespace ProximityGap.ReflectionListSampling

open Finset Polynomial Code TwoErrorSlice

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- The per-word sample counts suffice for the desired minimum row weight. -/
def RowBudget (k r L : ℕ) : Prop := ∀ e, 3≤e → e≤r+1 →
  (k+2)*L ≤ (e.choose 2-e/2)*((k+3+r-e).choose (r+2-e)*(k+1))

/-- The arbitrary-center scalar estimate. The puncture keeps k+3 sites, and the
radius allows at most r+1 errors, where n=k+3+r. -/
theorem scalar_of_sample_weights (D : I ↪ F) {k r T C L : ℕ} [NeZero k]
    (hn : Fintype.card I=k+3+r) (hL : 0<L) (reward' : I → I → F → ℕ)
    (pay : ∀ e, 3≤e → e≤r+1 →
      (k+2)*L ≤ (e.choose 2-e/2)*((k+3+r-e).choose (r+2-e)*C))
    (last : ∀ (E A Q : Finset I) (err : I → F), (∀ x∈E,err x≠0) → A.card=2 → A⊆E →
      (∀ u∈A,∀ v∈A,u≠v → D u≠-D v) → Q⊆univ \ E → ((univ \ E) \ Q).card=k+2 →
      C ≤ ∑ x∈(univ \ E) \ Q,sampleWeight D reward' E err ((E \ A) ∪ insert x Q))
    (col : ∀ (W : I → F) (V : Finset (I → F)) (P : V → F[X]), Function.Injective P →
      ∀ E : V → Finset I, (∀ j x,x∈E j ↔ (P j).eval (D x)≠W x) →
      (∀ j,(P j).natDegree<k) → ∀ R : Finset I,(univ \ R).card=k+3 →
      (∑ j : V,sampleWeight D reward' (E j) (fun x => (P j).eval (D x)-W x) R)≤T)
    (δ : ℝ) (hδ : δ*(Fintype.card I : ℝ)<r+2) :
    Lambda (ReedSolomon.code D k : Set (I → F)) δ ≤ (max 1 ((k+3+r).choose r*T/L) : ℕ) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro W S hS
  have hm (j : S) := mem_closeCodewordsRel_iff.mp (hS j.val j.property)
  choose P hdeg hval using fun j : S => ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hm j).1
  have hin : Function.Injective P := by
    intro i j he
    apply Subtype.ext
    funext x
    rw [←hval i x,←hval j x,he]
  let E (j : S) := univ.filter fun x => j.val x≠W x
  have he (j : S) (x : I) : x∈E j ↔ (P j).eval (D x)≠W x := by simp [E,hval]
  have hsize (j : S) : (E j).card≤r+1 := by
    have hh := (hm j).2
    rw [relHammingDist_coe,hammingDist_comm] at hh
    have pos : (0:ℝ)<Fintype.card I := by exact_mod_cast (hn ▸ (by omega : 0<k+3+r))
    have lt := ((div_le_iff₀ pos).mp hh).trans_lt hδ
    have nat : hammingDist j.val W<r+2 := by exact_mod_cast lt
    change hammingDist j.val W≤r+1
    omega
  by_cases one : ∃ j : S,(E j).card ≤ 2
  · obtain ⟨j,hj⟩ := one
    have unique (i : S) : i=j := by
      apply hin
      let U := (univ : Finset I) \ (E i ∪ E j)
      have size : k≤U.card := by
        have hc := card_union_le (E i) (E j)
        have hi := hsize i
        dsimp [U]; rw [card_sdiff_of_subset (subset_univ _),card_univ,hn]
        omega
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P i) (P j)
        (f := fun x : U => D x.val) (D.injective.comp Subtype.val_injective)
      · intro x
        have no := (mem_sdiff.mp x.property).2
        exact (not_ne_iff.mp (fun h => no (mem_union_left _ ((he i _).mpr h)))).trans
          (not_ne_iff.mp (fun h => no (mem_union_right _ ((he j _).mpr h)))).symm
      · rw [Fintype.card_coe]; exact (max_lt (hdeg i) (hdeg j)).trans_le size
    apply le_trans _ (le_max_left ..)
    exact card_le_one.mpr fun i hi j hj => congrArg Subtype.val ((unique ⟨i,hi⟩).trans (unique ⟨j,hj⟩).symm)
  let samples := (univ : Finset I).powersetCard r
  let w (j : S) := sampleWeight D reward' (E j) (fun x => (P j).eval (D x)-W x)
  have perRow (j : S) : L ≤ ∑ R∈samples,w j R := by
    have lo : 3≤(E j).card := by by_contra! h; exact one ⟨j,by omega⟩
    have row := row_from_extensions D (E j) (w j) (C:=C) hn (r:=r) (by omega) lo (hsize j)
      (fun A hA sub clean Q hQ sites => by
        apply last _ _ _ _ (fun x hx => sub_ne_zero.mpr ((he j x).mp hx)) hA sub clean hQ
        omega)
    rw [show k+3+r-r-1=k+2 by omega] at row
    exact Nat.le_of_mul_le_mul_left ((pay _ lo (hsize j)).trans row) (by omega)
  have perCol (R) (hR : R∈samples) : ∑ j : S,w j R ≤ T := by
    apply col W S P hin E he hdeg
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn,(mem_powersetCard.mp hR).2]
    omega
  have lo := sum_le_sum (s := (univ : Finset S)) (fun j _ => perRow j)
  rw [sum_comm] at lo
  have hi := lo.trans (sum_le_sum perCol)
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe,Nat.cast_id,samples,card_powersetCard,hn] at hi
  exact (Nat.le_div_iff_mul_le hL).mpr hi |>.trans (le_max_right ..)

/-- Unit credit for nonreflection products gives the unweighted transposition bound. -/
theorem scalar (D : I ↪ F) {k r T L : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r)
    (rigid : PairCap D T) (hL : 0<L) (pay : RowBudget k r L) (δ : ℝ)
    (hδ : δ*(Fintype.card I : ℝ)<r+2) : Lambda (ReedSolomon.code D k : Set (I → F)) δ ≤
      (max 1 ((k+3+r).choose r*T/L) : ℕ) := by
  apply scalar_of_sample_weights D hn hL (reward D) pay _ _ δ hδ
  · intro E A Q err nonzero size sub clean hQ room
    have ct := final_site D E A Q err nonzero size sub clean hQ
    rw [room] at ct
    simpa only [show k+2-1=k+1 by omega] using ct
  · intro W V P hin E agree deg R room
    exact column D rigid P hin W univ E (fun i _ => agree i) (fun i _ => deg i) R room

/-- Every realized pair product in a field extension is the image of a base
field product. Thus extending the scalars preserves the nonreflection cap. -/
theorem PairCap.map {K : Type*} [Field K] (D : I ↪ F) {T : ℕ} (cap : PairCap D T)
    (hT : 1≤T) (φ : F →+* K) : PairCap (D.trans ⟨φ,φ.injective⟩) T := by
  classical
  let E := D.trans (⟨φ,φ.injective⟩ : F ↪ K)
  have rat (u v x : I) : ratio E u v x=φ (ratio D u v x) := by simp [ratio,E]
  intro u v ne anti t nt
  change (alternatives E u v t).card+1 ≤ T
  by_cases empty : alternatives E u v t=∅
  · simpa only [empty,card_empty,Nat.zero_add] using hT
  obtain ⟨A,hA⟩ := nonempty_iff_ne_empty.mpr empty
  let q := ∏ x∈A,ratio D u v x
  have val : φ q=t := by simpa only [q,map_prod,←rat] using (mem_alternatives_iff.mp hA).2
  have eq : alternatives E u v t = alternatives D u v q := by
    ext B
    simp only [mem_alternatives_iff,rat,←map_prod,←val,φ.injective.eq_iff]
  rw [eq]
  refine cap u v ne ?_ q ?_
  · intro h; apply anti; change φ (D u) = -φ (D v); rw [h,map_neg]
  · intro h; apply nt; change t=φ (D u)/φ (D v); rw [←val,h,map_div₀]

/-- Packing symbols as rational functions gives the same upper bound at every
width, with no restriction on the cardinality of the list or the field. -/
theorem interleaved (D : I ↪ F) {k r T L : ℕ} [NeZero k] (hn : Fintype.card I=k+3+r)
    (rigid : PairCap D T) (hT : 1≤T) (hL : 0<L) (pay : RowBudget k r L) (m : ℕ) (δ : ℝ)
    (hδ : δ*(Fintype.card I : ℝ)<r+2) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (max 1 ((k+3+r).choose r*T/L) : ℕ) :=
  (ReedSolomon.Lambda_interleaved_le_ratFunc D k m δ).trans
    (scalar _ hn (PairCap.map D rigid hT (algebraMap F (RatFunc F))) hL pay δ hδ)

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.interleaved
