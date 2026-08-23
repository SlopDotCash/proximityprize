/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction

/-!
# THE LINE-LIST COLLAPSE (#389): the affine-line list is a single-word list one degree up

`LineListReduction.lean` reduced the per-scalar MCA supply to the **affine-line list size**
`Λ` — the codewords of `rsCode dom k` coming within agreement `a` of *some* word on the
bad-scalar line `{u₀ + γ·xᵏ}` — and named "bound `Λ` sub-trivially (affine-subspace list
decoding)" as the wall.  This file **collapses that generality**: for the MCA direction
`u₁ = xᵏ` far from the code,

> **`lineList_card_le_codeword_list`** — `Λ ≤ #{Q ∈ rsCode dom (k+1) : agreement(Q, u₀) ≥ a}`,
> the ordinary **single-word** sub-Johnson list of `u₀` in the **one-dimension-larger** code
> `rsCode dom (k+1)`.

Mechanism: a line-list codeword `c = P_c` agreeing with `u₀ + γ_c·xᵏ` on a set `S` means
`Q_c := P_c − γ_c·Xᵏ` (degree `≤ k`, so a codeword of `rsCode dom (k+1)`) agrees with `u₀`
on `S`.  The map `c ↦ Q_c` is **injective**: `Q_c = Q_{c'}` forces
`P_c − P_{c'} = (γ_c − γ_{c'})·Xᵏ`, whose left side has degree `< k`; so `γ_c = γ_{c'}` unless
`xᵏ ∈ rsCode dom k` — excluded by the far-direction hypothesis — and then `P_c = P_{c'}`.

So the affine-*subspace* list-decoding the supply wall seemed to need is exactly the
single-*word* sub-Johnson list-decoding problem one dimension up — the object the ladder/fibre
(`ladder_list_card_mul_le`) and additive-energy (`cubicSupply_pow_le_of_gvRepBound`) lanes
bound.  No new list-decoding generality is required; the two reductions compose to read the
supply wall as a single sub-Johnson list bound.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE LINE-LIST COLLAPSE**: with the far MCA direction `xᵏ ∉ rsCode dom k`, the affine-
line list of `rsCode dom k` along `{u₀ + γ·xᵏ}` injects into the single-word agreement-`a`
list of `u₀` in the one-larger code `rsCode dom (k+1)`. -/
theorem lineList_card_le_codeword_list (dom : Fin n ↪ F) (k a : ℕ) (u₀ : Fin n → F)
    (hfar : (fun i => (dom i) ^ k) ∉ (rsCode dom k : Submodule F (Fin n → F))) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun Q => Q ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F))
            ∧ a ≤ (agreeSet Q u₀).card)).card := by
  classical
  set LHS := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card) with hLHS
  -- choose a witness scalar for each line-list codeword
  have hwit : ∀ c ∈ LHS, ∃ γ : F,
      a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card :=
    fun c hc => (Finset.mem_filter.mp hc).2.2
  choose! γ hγ using hwit
  -- the down-shifted codeword
  set Φ : (Fin n → F) → (Fin n → F) := fun c => fun i => c i - γ c • (dom i) ^ k with hΦ
  refine Finset.card_le_card_of_injOn Φ ?_ ?_
  · -- `Φ c` is a `rsCode dom (k+1)` codeword agreeing with `u₀` on `≥ a` points
    intro c hc
    obtain ⟨-, hcmem, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨P, hPdeg, hPeq⟩ := hcmem
    have hagrset : agreeSet (Φ c) u₀
        = agreeSet c (fun i => u₀ i + γ c • (dom i) ^ k) := by
      ext i
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, hΦ, smul_eq_mul]
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨P - C (γ c) * X ^ k, ?_, ?_⟩, ?_⟩
    · -- degree `≤ k < k+1`
      refine lt_of_le_of_lt (le_trans (degree_sub_le _ _) (max_le ?_ ?_))
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self k))
      · exact le_of_lt hPdeg
      · exact degree_C_mul_X_pow_le _ _
    · funext i
      simp only [hΦ, hPeq, eval_sub, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
    · rw [hagrset]; exact hγ c hc
  · -- injectivity: `Φ c = Φ c'` forces `c = c'`
    intro c hc c' hc' hΦeq
    obtain ⟨-, hcmem, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hc'mem, -⟩ := Finset.mem_filter.mp hc'
    have hdiff : ∀ i, c i - c' i = (γ c - γ c') • (dom i) ^ k := by
      intro i
      have h := congrFun hΦeq i
      simp only [hΦ, smul_eq_mul] at h ⊢
      linear_combination h
    have hcsub : (fun i => c i - c' i) ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      (rsCode dom k).sub_mem hcmem hc'mem
    have hγeq : γ c = γ c' := by
      by_contra hne
      apply hfar
      have hscale : (fun i => (dom i) ^ k)
          = (γ c - γ c')⁻¹ • (fun i => c i - c' i) := by
        funext i
        rw [Pi.smul_apply, hdiff i, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
      rw [hscale]
      exact (rsCode dom k).smul_mem _ hcsub
    funext i
    have h := hdiff i
    rw [hγeq, sub_self, zero_smul] at h
    exact sub_eq_zero.mp h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.lineList_card_le_codeword_list
