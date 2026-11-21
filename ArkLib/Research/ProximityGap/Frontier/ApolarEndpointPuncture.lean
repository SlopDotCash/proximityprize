/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarEndpointExact
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Puncturing beyond the sharp unique-decoding boundary -/

set_option autoImplicit false
open Finset Code Polynomial ProximityGap Classical
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.ApolarEndpointPuncture
variable {I F : Type} [Fintype I] [DecidableEq I] [Field F]
variable (dom : I ↪ F) (k : ℕ) (u v : I → F)

private def Fits (S : Finset I) (a : I → F) : Prop :=
  ∃ w ∈ ReedSolomon.code dom k, ∀ i ∈ S, w i = a i

private theorem exact_witness [Nonempty I] {n e : ℕ} (hn : Fintype.card I = n) (ha : k + 1 ≤ n - e)
    {t : F} (ht : mcaEvent (ReedSolomon.code dom k : Set (I → F)) ((e : ℝ≥0) / n) u v t) :
    ∃ S : Finset I, S.card = n - e ∧ Fits dom k S (fun i => u i + t * v i) ∧
      ¬ Fits dom k S v := by
  classical
  obtain ⟨A, hA, mix, notJoint⟩ := ht
  have hag : n - e ≤ A.card := by
    have h := one_sub_div_mul_cast (ι := I) e (by omega)
    rw [hn] at h hA
    rw [h] at hA
    exact_mod_cast hA
  have hnon : ¬ Fits dom k A v := by
    rintro ⟨d, hd, hdv⟩
    obtain ⟨w, hw, hwv⟩ := mix
    apply notJoint
    refine ⟨w - t • d, (ReedSolomon.code dom k).sub_mem hw ((ReedSolomon.code dom k).smul_mem t hd),
      d, hd, fun i hi => ⟨?_, hdv i hi⟩⟩
    change w i - t * d i = u i
    rw [hwv i hi, hdv i hi]
    simp
  have hden := CircuitDensity.detecting_density (ReedSolomon.code dom k : Set (I → F)) v A k
    (fun _ hc _ hd _ hcard hag => ReedSolomon.eq_of_agree_of_card_le hc hd hcard hag)
    (card_pos.mp (by omega)) hnon
  have hpos : 0 < (A.card - 1).choose k := Nat.choose_pos (by omega)
  obtain ⟨U, hU⟩ := card_pos.mp (hpos.trans_le hden)
  obtain ⟨hin, huc⟩ := mem_powersetCard.mp (mem_filter.mp hU).1
  obtain ⟨S, hUS, hSA, hs⟩ := exists_subsuperset_card_eq hin (by omega : U.card ≤ n-e) hag
  refine ⟨S,hs,?_,?_⟩
  · obtain ⟨w, hw, h⟩ := mix
    exact ⟨w,hw,fun i hi => h i (hSA hi)⟩
  · rintro ⟨w, hw, h⟩
    exact (mem_filter.mp hU).2 ⟨w,hw,fun i hi => h i (hUS hi)⟩

omit [Fintype I] in
private theorem retained_event {R S : Finset I} [Nonempty R] {e' : ℕ} (hSR : S ⊆ R)
    (hs : S.card = R.card - e') (he : e' ≤ R.card) {t : F}
    (hmix : Fits dom k S (fun i => u i + t * v i)) (hnon : ¬ Fits dom k S v) :
    mcaEvent (ReedSolomon.code ((Function.Embedding.subtype (·∈ R)).trans dom) k : Set (R → F))
      ((e' : ℝ≥0) / R.card) (fun i => u i) (fun i => v i) t := by
  classical
  let into : S ↪ R := ⟨fun i => ⟨i, hSR i.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun x : R => (x : I)) h)⟩
  let U : Finset R := S.attach.map into
  have hU : U.card = S.card := by simp [U]
  refine ⟨U, ?_, ?_, ?_⟩
  · have h := one_sub_div_mul_cast (ι := R) e' (by simpa using he)
    simpa only [Fintype.card_coe,hU,hs] using h.le
  · obtain ⟨w, hw, h⟩ := hmix
    obtain ⟨p, hp, hpe⟩ := ReedSolomon.mem_code_iff_eval.mp hw
    refine ⟨fun i => w i, ReedSolomon.mem_code_iff_eval.mpr ⟨p,hp,fun i => hpe i⟩,?_⟩
    intro i hi
    obtain ⟨j,_,rfl⟩ := mem_map.mp hi
    exact h j j.property
  · rintro ⟨_,_,w,hw,h⟩
    obtain ⟨p,hp,hpe⟩ := ReedSolomon.mem_code_iff_eval.mp hw
    apply hnon
    refine ⟨fun i => p.eval (dom i), ReedSolomon.mem_code_iff_eval.mpr ⟨p,hp,fun _ => rfl⟩,?_⟩
    intro i hi
    let j : R := ⟨i,hSR hi⟩
    have hj : j ∈ U := mem_map.mpr ⟨⟨i,hi⟩,mem_attach _ _,rfl⟩
    exact (hpe j).trans (h j hj).2

/-- Uniform endpoint caps on all c-point punctures control the original scalar
count, including every witness outside unique decoding. -/
theorem count [Fintype F] [DecidableEq F] [Nonempty I] {n e c : ℕ}
    (hn : Fintype.card I = n) (hk : 0 < k) (he : c < e) (ha : k + 1 ≤ n-e)
    (hshape : n-c = k+2*(e-c)) :
    (univ.filter fun t : F => mcaEvent (ReedSolomon.code dom k : Set (I → F))
      ((e : ℝ≥0) / n) u v t).card * e.choose c ≤
        n.choose c * ApolarEndpointExact.numerator (n-c) (e-c) := by
  classical
  let G := univ.filter fun t : F => mcaEvent (ReedSolomon.code dom k : Set (I → F))
    ((e : ℝ≥0) / n) u v t
  have witness (t : F) (ht : t ∈ G) := exact_witness dom k u v hn ha (mem_filter.mp ht).2
  choose! S hs hmix hnon using witness
  let E (t : F) := (univ : Finset I) \ S t
  let all := (univ : Finset I).powersetCard c
  let rel (t : F) (P : Finset I) := P ⊆ E t
  have above (t : F) (ht : t ∈ G) : e.choose c ≤ (all.bipartiteAbove rel t).card := by
    have hE : (E t).card = e := by
      simp only [E,card_sdiff_of_subset (subset_univ _),card_univ,hs t ht,hn]
      omega
    have heq : all.bipartiteAbove rel t = (E t).powersetCard c := by
      ext P
      simp only [all,Finset.bipartiteAbove,rel,mem_filter,mem_powersetCard,subset_univ,true_and]
      exact and_comm
    rw [heq,card_powersetCard,hE]
  have below (P : Finset I) (hP : P ∈ all) :
      (G.bipartiteBelow rel P).card ≤ ApolarEndpointExact.numerator (n-c) (e-c) := by
    let R := (univ : Finset I) \ P
    have hR : R.card = n-c := by
      simp only [R,card_sdiff_of_subset (subset_univ _),card_univ,hn,(mem_powersetCard.mp hP).2]
    let _ : Nonempty R := Finset.card_pos.mp (by omega : 0 < R.card) |>.to_subtype
    let α := (Function.Embedding.subtype (·∈ R)).trans dom
    have hb := ApolarEndpointExact.pair_bound α (fun i => u i) (fun i => v i)
      ((Fintype.card_coe R).trans hR) hshape hk (by omega : 0<e-c)
    apply (card_le_card ?_).trans hb
    intro t ht
    obtain ⟨htG,hsub⟩ := mem_filter.mp ht
    have hSR : S t ⊆ R := by
      intro i hi
      apply mem_sdiff.mpr
      refine ⟨mem_univ _, fun hp => ?_⟩
      exact (mem_sdiff.mp (hsub hp)).2 hi
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [← hR]
    exact retained_event dom k u v hSR (by rw [hs t htG,hR]; omega)
      (by omega) (hmix t htG) (hnon t htG)
  have h := Finset.card_nsmul_le_card_nsmul rel above below
  simpa only [G,Nat.nsmul_eq_mul,all,card_powersetCard,card_univ,hn] using h

/-- Every pair on any production-length domain at half rate has at most
twelve times the length minus sixty bad labels one error beyond unique decoding. -/
theorem production_successor [Fintype F] [DecidableEq F] [Nonempty I]
    (hn : Fintype.card I = 1073741824) :
    (univ.filter fun t : F => mcaEvent (ReedSolomon.code dom 536870912 : Set (I → F))
      ((268435457 : ℝ≥0) / 1073741824) u v t).card ≤ 12884901828 := by
  have h := count dom 536870912 u v (e := 268435457) (c := 2) hn
    (by decide) (by decide) (by decide) (by decide)
  rw [Nat.choose_two_right, Nat.choose_two_right] at h
  norm_num [ApolarEndpointExact.numerator] at h
  omega

set_option pp.fullNames true
#print axioms count
#print axioms production_successor
end ArkLib.ProximityGap.Frontier.ApolarEndpointPuncture
