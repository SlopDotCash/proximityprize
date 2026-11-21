/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Monotonicity of Reed–Solomon line-MCA error in the message dimension -/

noncomputable section
namespace ProximityGap.DimensionMultiplierMCA
open Polynomial Finset Module Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Nonempty I]

/-- At most q proper vector subspaces cannot cover the affine plane over a field of size q. -/
private theorem outside (G : Finset F) (W : F → Submodule F (F × F))
    (hw : ∀ z ∈ G, W z ≠ ⊤) : ∃ a, ∀ z ∈ G, a ∉ W z := by
  classical
  let q := Fintype.card F
  let T (z : F) := ((W z : Set (F × F)).toFinset).erase 0
  have bound (z : F) (hz : z ∈ G) : (T z).card ≤ q-1 := by
    have h := (W z).finrank_lt (hw z hz)
    rw [finrank_prod, finrank_self, one_add_one_eq_two] at h
    have card : Fintype.card (W z) ≤ q := by
      rw [Module.card_eq_pow_finrank (K := F)]
      change q ^ finrank F (W z) ≤ q
      obtain h0 | h1 : finrank F (W z) = 0 ∨ finrank F (W z) = 1 := by omega
      · rw [h0, pow_zero]
        exact Fintype.card_pos
      · rw [h1, pow_one]
    dsimp [T]
    rw [card_erase_of_mem (by simp), Set.toFinset_card]
    exact Nat.sub_le_sub_right card 1
  by_contra! h
  have cov : (univ : Finset (F × F)).erase 0 ⊆ G.biUnion T := by
    intro a ha
    obtain ⟨z,hz,hm⟩ := h a
    exact mem_biUnion.mpr ⟨z,hz,mem_erase.mpr ⟨(mem_erase.mp ha).1,Set.mem_toFinset.mpr hm⟩⟩
  have hc := (card_le_card cov).trans (card_biUnion_le.trans (sum_le_sum bound))
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_prod, sum_const, nsmul_eq_mul] at hc
  have hG : G.card ≤ q := G.card_le_univ
  change q*q-1 ≤ _ at hc
  have hp : 1 < q := Fintype.one_lt_card
  have he := hc.trans (Nat.mul_le_mul_right (q-1) hG)
  have hq : q-1+1 = q := by omega
  have hqq : 0 < q*q := Nat.mul_pos (by omega) (by omega)
  nlinarith [Nat.sub_add_cancel hqq, congrArg (fun x => q*x) hq]

private def restricted (D : I ↪ F) (S : Finset I) : S ↪ F :=
  ⟨fun i => D i.val, D.injective.comp Subtype.val_injective⟩

private def scaled (D : I ↪ F) (S : Finset I) (y : I → F) : (F × F) →ₗ[F] (S → F) where
  toFun a i := (a.1 + a.2 * D i.val) * y i.val
  map_add' a b := by ext i; change (a.1 + b.1 + (a.2 + b.2) * D i.val) * y i.val =
    (a.1 + a.2 * D i.val) * y i.val + (b.1 + b.2 * D i.val) * y i.val; ring
  map_smul' c a := by ext i; change (c * a.1 + c * a.2 * D i.val) * y i.val = c * ((a.1 + a.2 * D i.val) * y i.val); ring

private def fits (D : I ↪ F) (S : Finset I) (k : ℕ) (y : I → F) :=
  (ReedSolomon.code (restricted D S) (k+1)).comap (scaled D S y)

private theorem recover (D : I ↪ F) (S : Finset I) {k : ℕ} (hk : 0 < k)
    (hs : k+1 < S.card) (y : I → F) (h : fits D S k y = ⊤) :
    ∃ P : F[X], P.degree < k ∧ ∀ i ∈ S, P.eval (D i) = y i := by
  classical
  letI : NeZero (k+1) := ⟨by omega⟩
  have both (a : F × F) : scaled D S y a ∈ ReedSolomon.code (restricted D S) (k+1) := by
    change a ∈ fits D S k y
    rw [h]; trivial
  obtain ⟨P,hP,eP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (both (1,0))
  obtain ⟨Q,hQ,eQ⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (both (0,1))
  have hp (i : S) : P.eval (D i.val) = y i.val := by simpa [scaled,restricted] using eP i
  have hq (i : S) : Q.eval (D i.val) = D i.val * y i.val := by simpa [scaled,restricted] using eQ i
  have he : X*P = Q := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun i : S => D i.val)
      (D.injective.comp Subtype.val_injective)
    · intro i
      rw [eval_mul, eval_X, hp, hq]
    · rw [Fintype.card_coe]
      apply max_lt _ (by omega)
      have hmul : (X*P).natDegree ≤ (X : F[X]).natDegree + P.natDegree := natDegree_mul_le
      rw [natDegree_X] at hmul
      omega
  refine ⟨P, ?_, fun i hi => hp ⟨i,hi⟩⟩
  by_cases hp0 : P = 0
  · simp [hp0]
  · rw [← natDegree_lt_iff_degree_lt hp0]
    rw [← he, natDegree_mul X_ne_zero hp0, natDegree_X] at hQ
    omega

private def scaleStack (a : F × F) (D : I ↪ F) (u : WordStack F (Fin 2) I) :
    WordStack F (Fin 2) I := fun j i => (a.1 + a.2 * D i) * u j i

/-- One affine multiplier preserves every bad scalar of a stack on passing to
the next message dimension when each witness has more than that many sites. -/
theorem step (D : I ↪ F) {k : ℕ} (hk : 0 < k) (δ : ℝ≥0)
    (ht : k+1 < ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊) (u : WordStack F (Fin 2) I) :
    ∃ a : F × F, badScalars D k δ u ⊆ badScalars D (k+1) δ (scaleStack a D u) := by
  classical
  let G := badScalars D k δ u
  let S (z : F) : Finset I := if hz : z ∈ G then (selectedDecode D k δ u z hz).S else ∅
  let W (z : F) := fits D (S z) k (u 0) ⊓ fits D (S z) k (u 1)
  have proper (z : F) (hz : z ∈ G) : W z ≠ ⊤ := by
    let dec := selectedDecode D k δ u z hz
    have he : S z = dec.S := dif_pos hz
    have hsize : k+1 < (S z).card := he ▸ ht.trans_le (Nat.ceil_le.mpr dec.hcard)
    intro h
    have hh := inf_eq_top_iff.mp h
    obtain ⟨P,hP,eP⟩ := recover D (S z) hk hsize (u 0) hh.1
    obtain ⟨Q,hQ,eQ⟩ := recover D (S z) hk hsize (u 1) hh.2
    apply dec.hnjp
    rw [← he]
    exact ⟨_, ReedSolomon.evalOnPoints_mem_code_of_degree_lt hP,
      _, ReedSolomon.evalOnPoints_mem_code_of_degree_lt hQ, fun i hi => ⟨eP i hi, eQ i hi⟩⟩
  obtain ⟨a,ha⟩ := outside G W proper
  refine ⟨a, ?_⟩
  intro z hz
  let dec := selectedDecode D k δ u z hz
  have he : S z = dec.S := dif_pos hz
  let L : F[X] := C a.1 + C a.2 * X
  have hL : L.natDegree ≤ 1 := (natDegree_add_le ..).trans
    (max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp)))
  have hd : (L * dec.P).natDegree < k+1 := by
    have hi : dec.P.natDegree < k := by
      by_cases he : dec.P = 0
      · simpa [he] using hk
      · exact (natDegree_lt_iff_degree_lt he).mpr dec.hdeg
    exact natDegree_mul_le.trans_lt (by omega)
  apply (mem_badScalars_iff ..).mpr
  refine ⟨dec.S,dec.hcard,⟨_, ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt hd, ?_⟩, ?_⟩
  · intro i hi
    change (L * dec.P).eval (D i) = _ + _ * _
    rw [eval_mul, dec.hagree i hi]
    simp [L,scaleStack,smul_eq_mul]
    ring
  · rintro ⟨v,hv,w,hw,eh⟩
    apply ha z hz
    obtain ⟨P,hP,eP⟩ := ReedSolomon.mem_code_iff_eval.mp hv
    obtain ⟨Q,hQ,eQ⟩ := ReedSolomon.mem_code_iff_eval.mp hw
    constructor
    · apply ReedSolomon.mem_code_iff_eval.mpr
      refine ⟨P,hP,fun i => (eP i.val).trans (eh i.val (he ▸ i.property)).1⟩
    · apply ReedSolomon.mem_code_iff_eval.mpr
      refine ⟨Q,hQ,fun i => (eQ i.val).trans (eh i.val (he ▸ i.property)).2⟩

/-- At fixed radius the worst-case line-MCA error increases weakly with dimension
as long as the required support is larger than the upper dimension. -/
theorem epsMCA_mono_dimension (D : I ↪ F) {k K : ℕ} (hk : 0 < k) (hle : k ≤ K)
    (δ : ℝ≥0) (ht : K < ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤
      epsMCA (F := F) (ReedSolomon.code D K : Set (I → F)) δ := by
  induction K, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ K hle ih =>
    refine (ih (by omega)).trans ?_
    unfold epsMCA
    apply iSup_le
    intro u
    obtain ⟨a,ha⟩ := step D (hk.trans_le hle) δ ht u
    apply le_iSup_of_le (scaleStack a D u)
    apply Pr_le_Pr_of_implies
    intro z hz
    exact (mem_badScalars_iff ..).mp (ha ((mem_badScalars_iff ..).mpr hz))

#print axioms epsMCA_mono_dimension
end ProximityGap.DimensionMultiplierMCA
