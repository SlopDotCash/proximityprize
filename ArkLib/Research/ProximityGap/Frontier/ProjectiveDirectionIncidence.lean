/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ShiftedPowerCurveCount

/-! # Counting scalar directions by pairs of coordinates

If two coordinate pencils have distinct ratios w_i/V_i and w_j/V_j, a common
specialized multiplier at both sites forces a root of a nonzero polynomial
of degree at most s+1. An anchor with ratio class of size at most D therefore
supplies at least A-D usable second sites in any support of size A.
-/
set_option autoImplicit false
namespace ProximityGap.ProjectiveDirectionIncidence
open Finset Polynomial
variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- Pair incidence bound when every selected label supplies enough nonzero
anchors. The class-size condition is needed only on those anchors. -/
theorem nonzero_count (w V : I → F[X]) (B : Finset F) (S : F → Finset I) (a : F → F)
    (D A s : ℕ) (hw : ∀ i, (w i).natDegree ≤ 1) (hV : ∀ i, (V i).natDegree ≤ s)
    (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(V i).eval z)
    (hanchor : ∀ z ∈ B, A-D ≤ ((S z).filter fun i => (w i).eval z ≠ 0).card)
    (hclass : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z ≠ 0 →
      (univ.filter fun j => w i*V j = w j*V i).card ≤ D) :
    B.card*(A-D)^2 ≤ Fintype.card I*(Fintype.card I-1)*(s+1) := by
  classical
  let H (z : F) := (S z).filter fun i => (w i).eval z ≠ 0
  let pairs (z : F) := (H z ×ˢ S z).filter fun ij => w ij.1*V ij.2 ≠ w ij.2*V ij.1
  let R (z : F) (ij : I × I) := ij ∈ pairs z
  have hleft (z : F) (hz : z ∈ B) : (A-D)^2 ≤ (univ.offDiag.bipartiteAbove R z).card := by
    have hrow (i : I) (hi : i ∈ H z) :
        A-D ≤ ((S z).filter fun j => w i*V j ≠ w j*V i).card := by
      have hsmall := hclass z hz i (mem_filter.mp hi).1 (mem_filter.mp hi).2
      have hcut : ((S z).filter fun j => w i*V j = w j*V i).card ≤ D :=
        (card_le_card (filter_subset_filter _ (subset_univ _))).trans hsmall
      have hsum : ((S z).filter fun j => w i*V j = w j*V i).card +
          ((S z).filter fun j => w i*V j ≠ w j*V i).card = (S z).card :=
        card_filter_add_card_filter_not ..
      have := hsize z hz
      omega
    calc (A-D)^2 ≤ (H z).card*(A-D) := by rw [sq]; gcongr; exact hanchor z hz
         _ = ∑ _i ∈ H z, (A-D) := by simp
         _ ≤ ∑ i ∈ H z, ((S z).filter fun j => w i*V j ≠ w j*V i).card :=
           sum_le_sum hrow
         _ = (pairs z).card := by simp [pairs,card_filter,sum_product]
         _ ≤ _ := by
           apply card_le_card
           intro ij hij
           refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,?_⟩,hij⟩
           exact fun heq => (mem_filter.mp hij).2 (by rw [heq])
  have hright (ij : I × I) (_hij : ij ∈ (univ : Finset I).offDiag) :
      (B.bipartiteBelow R ij).card ≤ s+1 := by
    obtain he | ⟨z,hz⟩ := (B.bipartiteBelow R ij).eq_empty_or_nonempty
    · simp [he]
    let P := w ij.1*V ij.2-w ij.2*V ij.1
    have hne : P ≠ 0 := sub_ne_zero.mpr (mem_filter.mp (mem_filter.mp hz).2).2
    have hd : P.natDegree ≤ s+1 := by
      apply (natDegree_sub_le ..).trans (max_le _ _)
      · exact natDegree_mul_le.trans ((Nat.add_le_add (hw _) (hV _)).trans_eq (Nat.add_comm ..))
      · exact natDegree_mul_le.trans ((Nat.add_le_add (hw _) (hV _)).trans_eq (Nat.add_comm ..))
    apply (card_le_degree_of_subset_roots (p:=P) _).trans hd
    intro t ht
    obtain ⟨ht,hpair⟩ := mem_filter.mp (show t ∈ B.bipartiteBelow R ij from ht)
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hpair).1
    apply (mem_roots hne).mpr
    simp only [P,IsRoot,eval_sub,eval_mul,hfit t ht _ (mem_filter.mp hi).1,hfit t ht _ hj]
    ring
  simpa only [offDiag_card,card_univ,Nat.mul_sub,Nat.mul_one] using
    card_mul_le_card_mul R hleft hright

/-- Zero multipliers add at most n−A+1 labels when every such support sees a
nonzero received affine pencil. Only a nonzero multiplier incurs pair counting. -/
theorem total_count (w V : I → F[X]) (B : Finset F) (S : F → Finset I) (a : F → F)
    (D A s : ℕ) (hDA : D < A) (hw : ∀ i, (w i).natDegree ≤ 1) (hV : ∀ i, (V i).natDegree ≤ s)
    (hsize : ∀ z ∈ B, A ≤ (S z).card)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(V i).eval z)
    (hanchor : ∀ z ∈ B, a z ≠ 0 → A-D ≤ ((S z).filter fun i => (w i).eval z ≠ 0).card)
    (hclass : ∀ z ∈ B, a z ≠ 0 → ∀ i ∈ S z, (w i).eval z ≠ 0 →
      (univ.filter fun j => w i*V j = w j*V i).card ≤ D)
    (hind : ∀ z ∈ B, a z = 0 → ∃ i ∈ S z, w i ≠ 0) :
    B.card ≤ Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(s+1)/(A-D)^2 := by
  classical
  let Z := B.filter fun z => a z = 0
  let U := B.filter fun z => a z ≠ 0
  have hZ := ShiftedPowerCurveCount.zero_count w hw Z S A
    (fun z hz => hsize z (mem_filter.mp hz).1)
    (fun z hz i hi => by rw [hfit z (mem_filter.mp hz).1 i hi,(mem_filter.mp hz).2,zero_mul])
    (fun z hz => hind z (mem_filter.mp hz).1 (mem_filter.mp hz).2)
  have hU := nonzero_count w V U S a D A s hw hV (fun z hz => hsize z (mem_filter.mp hz).1)
    (fun z hz => hfit z (mem_filter.mp hz).1)
    (fun z hz => hanchor z (mem_filter.mp hz).1 (mem_filter.mp hz).2)
    (fun z hz => hclass z (mem_filter.mp hz).1 (mem_filter.mp hz).2)
  have hu := (Nat.le_div_iff_mul_le (pow_pos (Nat.sub_pos_of_lt hDA) 2)).mpr hU
  have hZU : Z.card+U.card = B.card := card_filter_add_card_filter_not ..
  omega

/-- At site i, the affine received word after subtracting the specified pair
of codeword heads, as a polynomial in the challenge. -/
noncomputable def residualRow {I F : Type*} [Field F] (dom : I ↪ F) (u₀ u₁ : I → F)
    (q₀ q₁ : F[X]) (i : I) : F[X] :=
  C (u₀ i-q₀.eval (dom i))+X*C (u₁ i-q₁.eval (dom i))

omit [Fintype I] [DecidableEq I] in
/-- Every nonzero coordinate polynomial of degree at most D leaves at
least A−D nonvanishing anchor sites in any support of size at least A. -/
theorem anchors_of_nonzero (dom : I ↪ F) (Q : F[X]) (S : Finset I) (A D : ℕ)
    (hs : A ≤ S.card) (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ D) :
    A-D ≤ (S.filter fun i => Q.eval (dom i) ≠ 0).card := by
  classical
  let T := S.filter fun i => Q.eval (dom i) = 0
  have cut : T.card ≤ D := by
    rw [← card_image_of_injective T dom.injective]
    apply (card_le_degree_of_subset_roots (p:=Q) _).trans hdeg
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (show x ∈ T.image dom from hx)
    exact (mem_roots hQ).mpr (mem_filter.mp hi).2
  have hsum : T.card+(S.filter fun i => Q.eval (dom i) ≠ 0).card = S.card :=
    card_filter_add_card_filter_not ..
  omega

section MCA
open Classical

/-- Among arbitrary received rows, bound every selected scalar having a
nonjoint support and one decoding polynomial in the stated direction. -/
theorem captured_count {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (V : I → F[X]) (D A s : ℕ)
    (hDA : D < A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hV : ∀ i, (V i).natDegree ≤ s)
    (hclass : ∀ i, residualRow dom u₀ u₁ q₀ q₁ i ≠ 0 → V i ≠ 0 →
      (univ.filter fun j => residualRow dom u₀ u₁ q₀ q₁ i*V j =
        residualRow dom u₀ u₁ q₀ q₁ j*V i).card ≤ D)
    (B : Finset F) (hcapture : ∀ z ∈ B, ∃ (S : Finset I) (P : F[X]) (a : F),
      A ≤ S.card ∧ P.natDegree ≤ D ∧ (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ ∧
      ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*(V i).eval z) :
    B.card ≤ Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(s+1)/(A-D)^2 := by
  classical
  let w := residualRow dom u₀ u₁ q₀ q₁
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have wit (z : F) (hz : z ∈ B) : ∃ (S : Finset I) (a : F), A ≤ S.card ∧
      (∀ i ∈ S, (w i).eval z = a*(V i).eval z) ∧
      (a ≠ 0 → A-D ≤ (S.filter fun i => (w i).eval z ≠ 0).card) ∧
      (∃ i ∈ S, w i ≠ 0) := by
    obtain ⟨S,P,c,hs,hp,hfold,hind,hdir⟩ := hcapture z hz
    let Q := P-(q₀+C z*q₁)
    have heq (i : I) (hi : i ∈ S) : (w i).eval z = Q.eval (dom i) := by
      simp only [w,residualRow,Q,eval_sub,eval_mul,eval_add,eval_C,eval_X,hfold i hi]
      ring
    have hnon : ∃ i ∈ S, w i ≠ 0 := by
      by_contra! hnone
      apply hind
      refine ⟨ReedSolomon.evalOnPoints dom q₀,ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),
        ReedSolomon.evalOnPoints dom q₁,ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt (by omega),?_⟩
      intro i hi
      have hz₀ := congrArg (fun f : F[X] => f.coeff 0) (hnone i hi)
      have hz₁ := congrArg (fun f : F[X] => f.coeff 1) (hnone i hi)
      simp [w,residualRow] at hz₀ hz₁
      exact ⟨(sub_eq_zero.mp hz₀).symm,(sub_eq_zero.mp hz₁).symm⟩
    by_cases hQ : Q = 0
    · exact ⟨S,0,hs,fun i hi => by simp [heq i hi,hQ],fun hn => (hn rfl).elim,hnon⟩
    · refine ⟨S,c,hs,fun i hi => (heq i hi).trans (hdir i hi),fun _ => ?_,hnon⟩
      have hd : Q.natDegree ≤ D := (natDegree_sub_le ..).trans (max_le hp
        ((natDegree_add_le ..).trans (max_le hq₀ (natDegree_mul_le.trans (by simpa using hq₁)))))
      have hS : (S.filter fun i => Q.eval (dom i) ≠ 0) = (S.filter fun i => (w i).eval z ≠ 0) :=
        filter_congr fun i hi => by rw [heq i hi]
      exact (anchors_of_nonzero dom Q S A D hs hQ hd).trans_eq (congrArg card hS)
  choose! S a hs hf ha hind using wit
  apply total_count w V B S a D A s hDA hw hV hs hf ha _ (fun z hz _ => hind z hz)
  intro z hz _ i hi hn
  apply hclass i
  · intro he; change w i = 0 at he; rw [he,eval_zero] at hn; exact hn rfl
  · intro he; have ht := hf z hz i hi; rw [he,eval_zero,mul_zero] at ht; exact hn ht

/-- A literal local MCA bound for received pairs whose decoding witnesses
belong, after subtracting a common affine head, to the supplied direction. -/
theorem mca_count {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F] [Fintype F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (V : I → F[X]) (D A s : ℕ) (δ : NNReal)
    (hDA : D < A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hV : ∀ i, (V i).natDegree ≤ s)
    (hclass : ∀ i, residualRow dom u₀ u₁ q₀ q₁ i ≠ 0 → V i ≠ 0 →
      (univ.filter fun j => residualRow dom u₀ u₁ q₀ q₁ i*V j =
        residualRow dom u₀ u₁ q₀ q₁ j*V i).card ≤ D)
    (hr : ∀ S : Finset I, (1-δ)*(Fintype.card I : NNReal) ≤ S.card → A ≤ S.card)
    (hcurve : ∀ (z : F) (P : F[X]) (S : Finset I), P.natDegree ≤ D → A ≤ S.card →
      (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) →
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ →
      ∃ a : F, ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*(V i).eval z) :
    (univ.filter (mcaEvent (F:=F) (ReedSolomon.code dom (D+1) : Set (I → F)) δ u₀ u₁)).card ≤
      Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(s+1)/(A-D)^2 := by
  classical
  apply captured_count dom u₀ u₁ q₀ q₁ V D A s hDA hq₀ hq₁ hV hclass
  intro z hz
  obtain ⟨S,hs,⟨c,hc,hfit⟩,hind⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hp,hcP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  have hf (i : I) (hi : i ∈ S) : P.eval (dom i) = u₀ i+z*u₁ i := (hcP i).trans (hfit i hi)
  obtain ⟨a,ha⟩ := hcurve z P S (by omega) (hr S hs) hf hind
  exact ⟨S,P,a,hr S hs,by omega,hf,hind,ha⟩
end MCA

/-- For each of the four known test radii this identifies the adjacent
parameter degrees on opposite sides of each of the two production budgets. -/
theorem production_degree_cuts :
    let n : ℕ := 2^30
    let crosses := fun (k A b s : ℕ) =>
      let cost := fun j => n-A+1+n*(n-1)*(j+1)/(A-(k-1))^2
      cost s ≤ b ∧ b < cost (s+1)
    (crosses (2^29) (89*2^23) n 28479999 ∧ crosses (2^29) (89*2^23) (2*n) 69439999) ∧
    (crosses (2^28) (61*2^23) n 26266111 ∧ crosses (2^28) (61*2^23) (2*n) 81381887) ∧
    (crosses (2^27) (42*2^23) n 14536703 ∧ crosses (2^27) (42*2^23) (2*n) 58839039) ∧
    (crosses (2^26) (29*2^23) n 6547967 ∧ crosses (2^26) (29*2^23) (2*n) 35449343) := by
  decide

#print axioms production_degree_cuts
#print axioms mca_count
#print axioms captured_count
#print axioms nonzero_count
#print axioms total_count
#print axioms anchors_of_nonzero
end ProximityGap.ProjectiveDirectionIncidence
