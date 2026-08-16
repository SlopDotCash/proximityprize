/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

open Finset
open Polynomial
open scoped NNReal

namespace ArkLib.ProximityGap.PromotedHypotheses

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι)

def decList (C : Finset (ι → F)) (r : ι → F) (e : ℕ) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c r ≤ e)

def bundleCenters (C : Finset (ι → F)) (U : Finset (ι → F)) (e : ℕ) : Finset (ι → F) :=
  Finset.univ.filter (fun c => c ∈ C ∧ (U.filter (fun u => hammingDist c u ≤ e)).Nonempty)

theorem hyp45_list_intersection (C : Finset (ι → F)) (U V : Finset (ι → F)) (e : ℕ) (x : ι → F)
    (hxU : x ∈ U) (hxV : x ∈ V) (hclose : ∃ c ∈ C, hammingDist c x ≤ e) :
    (bundleCenters C U e ∩ bundleCenters C V e).Nonempty := by
  obtain ⟨c, hc_mem, hc_dist⟩ := hclose
  use c
  rw [Finset.mem_inter]
  constructor
  · rw [bundleCenters, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, hc_mem, ?_⟩
    rw [Finset.filter_nonempty_iff]
    exact ⟨x, hxU, hc_dist⟩
  · rw [bundleCenters, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, hc_mem, ?_⟩
    rw [Finset.filter_nonempty_iff]
    exact ⟨x, hxV, hc_dist⟩

theorem h30_agreement_lower_bound (f : F → F) (S : Finset F) :
    ∃ p : Polynomial F, p.degree < (S.card : WithBot ℕ) ∧ ∀ x ∈ S, p.eval x = f x := by
  use Lagrange.interpolate S id f
  constructor
  · exact Lagrange.degree_interpolate_lt f (fun _ _ _ _ h => h)
  · intro x hx
    exact Lagrange.eval_interpolate_at_node f (fun _ _ _ _ h => h) hx

include hk in
open Classical in
theorem hyp30_max_agreement_not_k_minus_one (v : ι → F) :
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k := by
  have hk' : k ≤ Finset.card (Finset.univ : Finset ι) := by rw [Finset.card_univ]; exact hk
  have h_exists : ∃ S : Finset ι, S.card = k := by
    obtain ⟨S, _, hS_card⟩ := Finset.exists_subset_card_eq hk'
    exact ⟨S, hS_card⟩
  obtain ⟨S, hS_card⟩ := h_exists
  let f : F → F := fun x => if hx : ∃ i ∈ S, domain i = x then v (Classical.choose hx) else 0
  have h_bound := h30_agreement_lower_bound f (S.map domain)
  obtain ⟨p, hp_deg, hp_eval⟩ := h_bound
  let c : ι → F := fun i => p.eval (domain i)
  use c
  constructor
  · apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p
    · rw [Finset.card_map, hS_card] at hp_deg
      exact hp_deg
    · intro i
      rfl
  · rw [← hS_card]
    apply Finset.card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    have h_mem : domain i ∈ S.map domain := Finset.mem_map_of_mem domain hi
    have eval_eq := hp_eval (domain i) h_mem
    change p.eval (domain i) = v i
    rw [eval_eq]
    dsimp [f]
    have hx : ∃ j ∈ S, domain j = domain i := ⟨i, hi, rfl⟩
    have hx_choose := Classical.choose_spec hx
    have h_choose_eq : domain (Classical.choose hx) = domain i := hx_choose.2
    have h_i : Classical.choose hx = i := domain.injective h_choose_eq
    rw [dif_pos hx, h_i]

open Classical in
theorem hyp8_translation_invariance (x y c : ι → F) :
    hammingDist (x + c) (y + c) = hammingDist x y := by
  dsimp [hammingDist, dist]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h heq; apply h; rw [heq]
  · intro h heq; apply h; exact add_right_cancel heq

open Classical in
theorem hyp7_barycentric_center (c_map : F → (ι → F))
    (h_valid : ∀ γ : F, c_map γ ∈ (ReedSolomon.code domain k : Set (ι → F))) :
    (∑ γ : F, c_map γ) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  exact Submodule.sum_mem (ReedSolomon.code domain k) fun γ _ => h_valid γ

end ArkLib.ProximityGap.PromotedHypotheses
