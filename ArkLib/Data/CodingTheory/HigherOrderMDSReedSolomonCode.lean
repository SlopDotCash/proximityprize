/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The general-position list bound for `ReedSolomon.code` (#389, layer 6)

Bridges `reedSolomon_genpos_list_bound` (layer 5, stated over the Vandermonde frame and
dual message functionals) to the repo's actual `ReedSolomon.code` submodule and its
codewords.  The map `evalMapₗ : Dual(Kᵏ) → (ι → K)`, `m ↦ (m(frameᵢ))ᵢ`, is linear and
its image is exactly `ReedSolomon.code` — a message functional `m` *is* the codeword
`(p_m(Dᵢ))ᵢ`.  Hence the capacity-radius general-position list bound holds verbatim for
honest RS codewords:

* `reedSolomonCode_genpos_list_bound` — for distinct evaluation points, `2 ≤ k`,
  `1 ≤ L < k`: an affinely-independent family of `L+1` codewords of `ReedSolomon.code D k`
  cannot all agree with a received word `y` on more than `(L·n + k − L)/(L+1)` coordinates.

Issue #389.
-/

open Finset Module Polynomial ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluation map from message functionals to words: `m ↦ (m(frameᵢ))ᵢ`. -/
noncomputable def evalMapₗ (D : ι → K) (k : ℕ) :
    Module.Dual K (Fin k → K) →ₗ[K] (ι → K) where
  toFun m := fun i => m (reedSolomonFrame D k i)
  map_add' m m' := by funext i; simp
  map_smul' c m := by funext i; simp

@[simp] theorem evalMapₗ_apply (D : ι → K) (k : ℕ) (m : Module.Dual K (Fin k → K)) (i : ι) :
    evalMapₗ D k m i = m (reedSolomonFrame D k i) := rfl

/-- Every codeword of `ReedSolomon.code` is `evalMapₗ` of some message functional. -/
theorem exists_message_of_mem_code {D : ι ↪ K} {k : ℕ} {c : ι → K}
    (hc : c ∈ ReedSolomon.code D k) :
    ∃ m : Module.Dual K (Fin k → K), evalMapₗ (⇑D) k m = c := by
  classical
  obtain ⟨p, hp, rfl⟩ := hc
  have hpdeg : p.degree < (k : WithBot ℕ) := Polynomial.mem_degreeLT.mp hp
  refine ⟨∑ j : Fin k, p.coeff (j : ℕ) • LinearMap.proj j, ?_⟩
  funext i
  simp only [evalMapₗ_apply, reedSolomonFrame, LinearMap.coeFn_sum, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, Finset.sum_apply]
  show (∑ j : Fin k, p.coeff (j : ℕ) * (D i) ^ (j : ℕ)) = (ReedSolomon.evalOnPoints D p) i
  rw [ReedSolomon.evalOnPoints]
  show (∑ j : Fin k, p.coeff (j : ℕ) * (D i) ^ (j : ℕ)) = p.eval (D i)
  rcases eq_or_ne p 0 with rfl | h0
  · simp
  · have hnd : p.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt h0).2 hpdeg
    rw [eval_eq_sum_range' hnd, Fin.sum_univ_eq_sum_range (fun j => p.coeff j * (D i) ^ j) k]

/-- **The general-position list bound for `ReedSolomon.code`.**  For distinct evaluation
points and `2 ≤ k`, `1 ≤ L < k`: an affinely-independent family of `L+1` codewords of
`ReedSolomon.code D k` cannot all agree with a received word `y` on more than the
capacity-radius fraction — `(L+1)·a ≤ L·n + (k − L)`. -/
theorem reedSolomonCode_genpos_list_bound [DecidableEq K] {D : ι ↪ K} {k : ℕ} (hk : 2 ≤ k)
    {L : ℕ} (hL1 : 1 ≤ L) (hLk : L < k) {y : ι → K}
    (c : Fin (L + 1) → (ι → K)) (hc : ∀ i, c i ∈ ReedSolomon.code D k)
    (hindep : LinearIndependent K (fun j : Fin L => c j.succ - c 0))
    {a : ℕ} (hagree : ∀ i, a ≤ (Finset.univ.filter (fun l => c i l = y l)).card) :
    (L + 1) * a ≤ L * Fintype.card ι + (k - L) := by
  classical
  choose m hm using fun i => exists_message_of_mem_code (hc i)
  -- transfer affine independence through the linear map evalMapₗ
  have hindep' : LinearIndependent K (fun j : Fin L => m j.succ - m 0) := by
    refine LinearIndependent.of_comp (evalMapₗ (⇑D) k) ?_
    have hcomp : (evalMapₗ (⇑D) k) ∘ (fun j : Fin L => m j.succ - m 0)
        = (fun j : Fin L => c j.succ - c 0) := by
      funext j; simp [map_sub, hm]
    rw [hcomp]; exact hindep
  -- transfer agreement counts
  have hagree' : ∀ i, a ≤ (agreeFinset (reedSolomonFrame (⇑D) k) y (m i)).card := by
    intro i
    refine le_trans (hagree i) (le_of_eq ?_)
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_agreeFinset]
    rw [show (reedSolomonFrame (⇑D) k) l = reedSolomonFrame (⇑D) k l from rfl,
      ← evalMapₗ_apply, hm i]
  exact reedSolomon_genpos_list_bound D.injective hk hL1 hLk hindep' hagree'

/-- **High-agreement RS codewords are affinely dependent** (structural foundation of the
full BGM bound).  Above the general-position capacity radius `L·n + (k−L) < (L+1)·a`, any
`L+1` codewords of `ReedSolomon.code D k` each agreeing with `y` on `≥ a` coordinates are
affinely dependent (their difference family is linearly dependent), so they lie in an
affine flat of dimension `< L`. -/
theorem reedSolomonCode_highAgreement_not_affineIndependent [DecidableEq K] {D : ι ↪ K}
    {k : ℕ} (hk : 2 ≤ k) {L : ℕ} (hL1 : 1 ≤ L) (hLk : L < k) {y : ι → K}
    (c : Fin (L + 1) → (ι → K)) (hc : ∀ i, c i ∈ ReedSolomon.code D k)
    {a : ℕ} (hagree : ∀ i, a ≤ (Finset.univ.filter (fun l => c i l = y l)).card)
    (hbig : L * Fintype.card ι + (k - L) < (L + 1) * a) :
    ¬ LinearIndependent K (fun j : Fin L => c j.succ - c 0) := by
  intro hindep
  have := reedSolomonCode_genpos_list_bound hk hL1 hLk c hc hindep hagree
  omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.exists_message_of_mem_code
#print axioms ArkLib.HigherOrderMDS.reedSolomonCode_genpos_list_bound
