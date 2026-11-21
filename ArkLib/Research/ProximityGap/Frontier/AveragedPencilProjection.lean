/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import ArkLib.Research.ProximityGap.Frontier.FiniteFingerprintCount

/-! # Projecting a pencil after averaging its collisions -/

set_option autoImplicit false
open Finset Polynomial Code ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.AveragedPencilProjection

variable {S F T : Type} [Field F]
private def agrees {B : Type} (f : S → B) (U : Finset S) := ∀ a∈U, ∀ b∈U, f a=f b

open Classical in
private noncomputable def pairs {B : Type} (P : Finset S) (f : S → B) :=
  (P.powersetCard 2).filter (agrees f)

private theorem loss {B : Type} [DecidableEq B] (P : Finset S) (f : S → B) :
    P.card ≤ (P.image f).card+(pairs P f).card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have mono : pairs P f ⊆ pairs (insert a P) f := by
      intro U hU
      obtain ⟨hs,hc⟩ := mem_filter.mp hU
      obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hs
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub.trans (subset_insert ..),hcard⟩,hc⟩
    rw [card_insert_of_notMem ha,image_insert]
    by_cases hx : f a ∈ P.image f
    · rw [insert_eq_of_mem hx]
      obtain ⟨b,hb,he⟩ := mem_image.mp hx
      have hne : a≠b := fun h => ha (h.symm ▸ hb)
      let U : Finset S := {a,b}
      have hu : U ∈ pairs (insert a P) f := by
        apply mem_filter.mpr
        refine ⟨mem_powersetCard.mpr ⟨by simp [U,hb],by simp [U,hne]⟩,?_⟩
        intro x hx y hy
        simp only [U,mem_insert,mem_singleton] at hx hy
        rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp_all
      have hout : U ∉ pairs P f := fun h =>
        ha ((mem_powersetCard.mp (mem_filter.mp h).1).1 (by simp [U]))
      have hh := card_le_card (insert_subset hu mono)
      rw [card_insert_of_notMem hout] at hh
      omega
    · rw [card_insert_of_notMem hx]
      have h := card_le_card mono
      omega

open Classical in
/-- Some fingerprint loses at most the average number of unordered colliding
pairs when each pair collides at most once. -/
theorem exists_image_with_pair_loss {B : Type} [Fintype T] [Nonempty T] [DecidableEq B]
    (P : Finset S) (v : T → S → B)
    (hp : ∀ a∈P, ∀ b∈P, a≠b → (univ.filter fun t => v t a=v t b).card≤1) :
    ∃ t, P.card-P.card.choose 2 / Fintype.card T ≤ (P.image (v t)).card := by
  classical
  let m (t : T) := (pairs P (v t)).card
  have total : ∑ t, m t ≤ P.card.choose 2 := by
    calc ∑ t, m t = ∑ U∈P.powersetCard 2, (univ.filter fun t => agrees (v t) U).card := by
           simp only [m,pairs,card_filter]
           rw [sum_comm]
         _ ≤ ∑ _U∈P.powersetCard 2, 1 := by
           apply sum_le_sum
           intro U hU
           obtain ⟨sub,card⟩ := mem_powersetCard.mp hU
           obtain ⟨a,b,hn,rfl⟩ := card_eq_two.mp card
           apply le_trans ?_ (hp a (sub (by simp)) b (sub (by simp)) hn)
           apply card_le_card
           intro t ht
           exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ht).2 a (by simp) b (by simp)⟩
         _ = _ := by simp
  obtain ⟨t,ht⟩ : ∃ t, m t * Fintype.card T ≤ P.card.choose 2 := by
    by_contra! hh
    have h := sum_lt_sum_of_nonempty (univ_nonempty (α:=T)) fun t _ => hh t
    rw [sum_const, card_univ,smul_eq_mul, ← sum_mul] at h
    exact (Nat.mul_le_mul_right (Fintype.card T) total).not_gt (by simpa [Nat.mul_comm] using h)
  have ht' := (Nat.le_div_iff_mul_le Fintype.card_pos).mpr ht
  have hl := loss P (v t)
  exact ⟨t,by dsimp [m] at ht'; omega⟩

private def linear (key : S → Fin 2 → F) (t : Option F) (i : S) : F :=
  t.elim (key i 1) (fun z => key i 0+z*key i 1)

open Classical in
private theorem unique_collision [Fintype F] (key : S → Fin 2 → F) (hi : Function.Injective key)
    {i j : S} (hne : i≠j) : (univ.filter fun t => linear key t i=linear key t j).card≤1 := by
  apply card_le_one.mpr
  intro x hx y hy
  have h := (mem_filter.mp hx).2
  have g := (mem_filter.mp hy).2
  have distinct (he0 : key i 0=key j 0) (he1 : key i 1=key j 1) : False := hne (hi (by
    funext z; fin_cases z <;> assumption))
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      change key i 1=key j 1 at h
      change key i 0+y*key i 1=key j 0+y*key j 1 at g
      exact (distinct (by simpa only [h,add_left_inj] using g) h).elim
  | some x =>
    change key i 0+x*key i 1=key j 0+x*key j 1 at h
    cases y with
    | none =>
      change key i 1=key j 1 at g
      exact (distinct (by simpa only [g,add_left_inj] using h) g).elim
    | some y =>
      change key i 0+y*key i 1=key j 0+y*key j 1 at g
      have he : (x-y)*(key i 1-key j 1)=0 := by linear_combination h-g
      rcases mul_eq_zero.mp he with hxy|hij
      · exact congrArg some (sub_eq_zero.mp hxy)
      · have eq := sub_eq_zero.mp hij
        exact (distinct (by simpa only [eq,add_left_inj] using h) eq).elim

variable [Fintype S] [Fintype F]

open Classical in
/-- One homogeneous linear projection retains both the pair-loss bound and the
second-moment bound. This includes full separation when `choose M 2 ≤ q`. -/
theorem projected_counts (key : S → Fin 2 → F) (hi : Function.Injective key) :
    ∃ a b : F, let m := Fintype.card S; let q := Fintype.card F
               let n := (univ.image (fun i => a*key i 0+b*key i 1)).card
               m-m.choose 2/(q+1) ≤ n ∧ m*(q+1) ≤ n*(q+1+(m-1)) := by
  classical
  let v := linear key
  have hp (a : S) (_ : a∈univ) (b : S) (_ : b∈univ) (hne : a≠b) := unique_collision key hi hne
  obtain ⟨t,ht⟩ := exists_image_with_pair_loss univ v hp
  obtain ⟨s,hs⟩ := FiniteFingerprintCount.exists_large_image univ v 1 hp
  simp only [card_univ,Fintype.card_option,Nat.mul_one] at ht hs
  obtain ⟨z,hz,hz'⟩ : ∃ z, (univ.image (v t)).card ≤ (univ.image (v z)).card ∧
      (univ.image (v s)).card ≤ (univ.image (v z)).card := by
    rcases le_total (univ.image (v t)).card (univ.image (v s)).card with h|h
    · exact ⟨s,h,le_rfl⟩
    · exact ⟨t,le_rfl,h⟩
  have first := ht.trans hz
  have second := hs.trans (Nat.mul_le_mul_right _ hz')
  cases z with
  | none =>
    have eq : v none = fun i => key i 1 := rfl
    rw [eq] at first second
    exact ⟨0,1,by simpa using first,by simpa using second⟩
  | some z =>
    have eq : v (some z) = fun i => key i 0+z*key i 1 := rfl
    rw [eq] at first second
    exact ⟨1,z,by simpa using first,by simpa using second⟩

/-- Number of image labels guaranteed by counting pairs and by Cauchy–Schwarz. -/
def retained (m q : ℕ) :=
  max (m-m.choose 2/(q+1)) ((m*(q+1)) ⌈/⌉ (q+1+(m-1)))

open Classical in
theorem exists_retained (key : S → Fin 2 → F) (hi : Function.Injective key) :
    ∃ a b : F, retained (Fintype.card S) (Fintype.card F) ≤
      (univ.image fun i => a*key i 0+b*key i 1).card := by
  obtain ⟨a,b,h,g⟩ := projected_counts key hi
  refine ⟨a,b,max_le h ((ceilDiv_le_iff_le_mul (by omega)).mpr ?_)⟩
  simpa only [Nat.mul_comm] using g

/-- At any integer budget whose square fits the field, a strictly over-budget
key family stays strictly over budget after projection. -/
theorem budget_lt_retained {m q B : ℕ} (hm : B < m) (hq : B^2 < q+1) :
    B < retained m q := by
  unfold retained
  apply lt_of_lt_of_le _ (le_max_right ..)
  by_contra! h
  have raw := (ceilDiv_le_iff_le_mul (by omega : 0 < q+1+(m-1))).mp h
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hm
  have he : m=B+1+s := by omega
  have he' : m-1=B+s := by omega
  have hBq : B≤q := by nlinarith [Nat.le_mul_self B]
  rw [he',he] at raw
  nlinarith [Nat.mul_le_mul_right s hBq]

/-- For tolerance `1/Q` and field order at most `Q²`, every unprojected
count above the security budget stays above it. -/
theorem tolerance_budget_lt_retained {m q Q : ℕ} (hQ : 0 < Q) (hq : q ≤ Q^2) (hm : q/Q < m) :
    q/Q < retained m q := by
  have hdiv : q/Q ≤ Q := (Nat.div_le_div_right hq).trans_eq (by simp [sq,hQ.ne'])
  apply budget_lt_retained hm
  calc (q/Q)^2 = (q/Q)*(q/Q) := by rw [sq]
       _ ≤ (q/Q)*Q := Nat.mul_le_mul_left _ hdiv
       _ < q+1 := (Nat.div_mul_le_self ..).trans_lt (Nat.lt_succ_self _)

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

open Classical in
/-- Every distinct image value is a genuine bad scalar on the same received pair. -/
theorem mass_of_projection
    (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (core : S → Finset I) (site : S → I)
    (p q r : S → F[X]) (u v w : I → F) (key : S → Fin 2 → F)
    (hp : ∀ i, (p i).degree < (k : WithBot ℕ))
    (hq : ∀ i, (q i).degree < (k : WithBot ℕ))
    (hr : ∀ i, (r i).degree < (k : WithBot ℕ))
    (hcore : ∀ i x, x ∈ core i → (p i).eval (dom x) = u x ∧
      (q i).eval (dom x) = v x ∧ (r i).eval (dom x) = w x)
    (hcard : ∀ i, k ≤ (core i).card)
    (hsize : ∀ i, (1-δ) * (Fintype.card I : ℝ≥0) ≤ (((core i).card+1 : ℕ) : ℝ≥0))
    (hmis : ∀ i, (r i).eval (dom (site i)) ≠ w (site i))
    (hkey : ∀ i,
      key i 0 * ((r i).eval (dom (site i)) - w (site i)) = u (site i) - (p i).eval (dom (site i)) ∧
      key i 1 * ((r i).eval (dom (site i)) - w (site i)) = v (site i) - (q i).eval (dom (site i)))
    (a b : F) :
    (((univ.image (fun i => a*key i 0+b*key i 1)).card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let rows : WordStack F (Fin 2) I := ![fun x => a*u x+b*v x, w]
  let first (i : S) := C a * p i + C b * q i
  have degree_mul (c : F) (f : F[X]) (hf : f.degree < (k : WithBot ℕ)) :
      (C c * f).degree < (k : WithBot ℕ) := by
    by_cases hz : c = 0
    · simp [hz]
    · simpa [degree_C_mul hz] using hf
  have deg_first (i : S) : (first i).degree < (k : WithBot ℕ) :=
    (degree_add_le _ _).trans_lt (max_lt (degree_mul _ _ (hp i)) (degree_mul _ _ (hq i)))
  have event (i : S) : mcaEvent (F := F) (ReedSolomon.code dom k : Set (I → F))
      δ (rows 0) (rows 1) (a*key i 0+b*key i 1) := by
    apply ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
      dom k δ rows (a*key i 0+b*key i 1) (core i) (site i) (first i) (r i)
    · exact fun he => hmis i (hcore i _ he).2.2
    · exact deg_first i
    · exact hr i
    · exact (degree_add_le _ _).trans_lt (max_lt (deg_first i) (degree_mul _ _ (hr i)))
    · exact hcard i
    · exact hsize i
    · intro x hx
      obtain ⟨heu, hev, hew⟩ := hcore i x hx
      simp [first, rows, heu, hev, hew]
    · change (first i + C (a*key i 0+b*key i 1) * r i).eval (dom (site i)) =
        a*u (site i)+b*v (site i)+(a*key i 0+b*key i 1)*w (site i)
      simp only [first, eval_add, eval_mul, eval_C]
      linear_combination a*(hkey i).1 + b*(hkey i).2
    · exact fun he => hmis i (congrArg Prod.snd he)
  apply MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ rows
  intro z hz
  obtain ⟨i, _, rfl⟩ := mem_image.mp hz
  exact event i

/-- Guaranteed MCA mass for an arbitrary collection of distinct two-component
keys. Both received rows are shared by all retained labels. -/
theorem mass_averaged
    (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) (core : S → Finset I) (site : S → I)
    (p q r : S → F[X]) (u v w : I → F) (key : S → Fin 2 → F)
    (hp : ∀ i, (p i).degree < (k : WithBot ℕ))
    (hq : ∀ i, (q i).degree < (k : WithBot ℕ))
    (hr : ∀ i, (r i).degree < (k : WithBot ℕ))
    (hcore : ∀ i x, x ∈ core i → (p i).eval (dom x) = u x ∧
      (q i).eval (dom x) = v x ∧ (r i).eval (dom x) = w x)
    (hcard : ∀ i, k ≤ (core i).card)
    (hsize : ∀ i, (1-δ) * (Fintype.card I : ℝ≥0) ≤ (((core i).card+1 : ℕ) : ℝ≥0))
    (hmis : ∀ i, (r i).eval (dom (site i)) ≠ w (site i))
    (hkey : ∀ i,
      key i 0 * ((r i).eval (dom (site i)) - w (site i)) = u (site i) - (p i).eval (dom (site i)) ∧
      key i 1 * ((r i).eval (dom (site i)) - w (site i)) = v (site i) - (q i).eval (dom (site i)))
    (hi : Function.Injective key) :
    ((retained (Fintype.card S) (Fintype.card F) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  obtain ⟨a,b,h⟩ := exists_retained key hi
  have hm := mass_of_projection dom k δ core site p q r u v w key hp hq hr hcore hcard hsize hmis hkey a b
  refine le_trans ?_ hm
  gcongr

#print axioms projected_counts
#print axioms budget_lt_retained
#print axioms tolerance_budget_lt_retained
#print axioms mass_of_projection
#print axioms mass_averaged
end ArkLib.ProximityGap.Frontier.AveragedPencilProjection
