/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarHankelMinors
import ArkLib.Research.ProximityGap.Hab25CaptureKernel

/-! # From the MCA event to a sparse syndrome specialization -/

open Polynomial Finset Code
open scoped NNReal
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarHankelMinors
namespace ProximityGap.ApolarMcaSyndrome

variable {K ι : Type} [Field K] [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- A row on the evaluation domain, expressed in the coordinate alphabet. -/
noncomputable def coordinateRow (dom : ι ↪ K) (u : ι → K) : K → K :=
  Function.extend dom u (fun _ => 0)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
@[simp] theorem coordinateRow_apply (dom : ι ↪ K) (u : ι → K) (i : ι) :
    coordinateRow dom u (dom i) = u i := dom.injective.extend_apply u _ i

/-- For an actual bad scalar on a Reed–Solomon domain, all syndrome moments
through the parity-check degree are represented by at most the allowed number
of errors, with the same support and weights for every moment. -/
theorem sparse_moments_of_mcaEvent [Fintype K] [DecidableEq K] (dom : ι ↪ K) {k e d : ℕ}
    {δ : ℝ≥0} {u : WordStack K (Fin 2) ι} {t : K} (hk : 1 ≤ k)
    (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (hm : mcaEvent (ReedSolomon.code dom k : Set (ι → K)) δ (u 0) (u 1) t) :
    let H := (univ : Finset ι).map dom
    let a := coordinateRow dom (u 0)
    let b := coordinateRow dom (u 1)
    ∃ E ⊆ H, E.card ≤ e ∧ ∃ w : K → K, ∀ j ≤ d,
      (moment H a b j).eval t = ∑ y ∈ E, w y * y^j := by
  classical
  dsimp only
  let H := (univ : Finset ι).map dom
  let a := coordinateRow dom (u 0)
  let b := coordinateRow dom (u 1)
  obtain ⟨dec⟩ := exists_mcaDecode_of_mcaEvent hm
  let E := ((univ : Finset ι) \ dec.S).map dom
  have hE : E ⊆ H := Finset.map_subset_map.mpr sdiff_subset
  have hsize : E.card ≤ e := by
    dsimp only [E]
    rw [card_map, card_sdiff_of_subset (subset_univ _),card_univ]
    have hi := he.trans (Nat.ceil_le.mpr dec.hcard)
    omega
  have deg : dec.P.natDegree < k := by
    by_cases h : dec.P=0
    · rw [h, natDegree_zero]
      omega
    · exact (natDegree_lt_iff_degree_lt h).mpr dec.hdeg
  have hoff : ∀ y ∈ H, y ∉ E → a y+t*b y=dec.P.eval y := by
    rintro y hy hn
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hy
    have hS : i ∈ dec.S := by
      by_contra hs
      exact hn (mem_map.mpr ⟨i,mem_sdiff.mpr ⟨hi,hs⟩,rfl⟩)
    simpa only [a,b,coordinateRow_apply,smul_eq_mul] using (dec.hagree i hS).symm
  refine ⟨E,hE,hsize,rowWeight H (fun y => a y+t*b y-dec.P.eval y),?_⟩
  intro j hj
  have hprod : dec.P.natDegree + ((X : K[X])^j).natDegree < H.card - 1 := by
    simp only [H,card_map,card_univ,natDegree_X_pow]
    omega
  have hred := syndrome_reduced H E (fun y => a y+t*b y) dec.P (X^j) (RingHom.id K) hE hoff hprod
  rw [syndrome_pencil, LinearMap.add_apply, LinearMap.smul_apply, weighted_apply] at hred
  simpa only [moment, Polynomial.eval_add, Polynomial.eval_mul, eval_X, eval_C, RingHom.id_apply,
    eval_pow, smul_eq_mul, add_comm] using hred

#print axioms sparse_moments_of_mcaEvent

end ProximityGap.ApolarMcaSyndrome
