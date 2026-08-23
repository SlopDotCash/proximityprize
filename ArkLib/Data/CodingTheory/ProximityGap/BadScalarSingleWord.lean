/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordCollapse

/-!
# THE SUPPLY WALL IS ONE SINGLE-WORD LIST (#389): the composed reduction

Chains the two reductions — the line-list reduction (`badScalar_card_le_lineList_mul`,
`#badScalars ≤ Λ·⌊n/a⌋`) and the line-list collapse (`lineList_card_le_codeword_list`,
`Λ ≤` single-word list one degree up) — into a single statement, for the MCA direction
`u₁ = xᵏ` over a `0 ∉` domain (so `xᵏ` is both nonvanishing and far):

> **`badScalar_card_le_codeword_list_mul`** — the scalars `γ` for which some codeword of
> `rsCode dom k` agrees with `u₀ + γ·xᵏ` on `≥ a` points number at most
> `#{Q ∈ rsCode dom (k+1) : agreement(Q, u₀) ≥ a} · ⌊n/a⌋`.

So the entire positive-direction supply wall is governed by **one ordinary single-word
sub-Johnson list** — of `u₀`, in the one-dimension-larger code `rsCode dom (k+1)`, at the
band agreement `a` — times the trivial heavy-bucket factor `⌊n/a⌋`.  No affine-subspace
list decoding, no per-scalar worst case: bound that one list sub-trivially and the supply
wall closes.  This is the cleanest single-inequality statement of the #389 open core,
with both reductions machine-checked.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The evaluation `xᵏ` is far from `rsCode dom k` whenever the domain has more than `k`
points — a degree-`k` polynomial cannot be matched on all `n > k` points by a degree-`< k`
one. -/
theorem xpow_not_mem_rsCode (dom : Fin n ↪ F) {k : ℕ} (hk : k < n) :
    (fun i => (dom i) ^ k) ∉ (rsCode dom k : Submodule F (Fin n → F)) := by
  classical
  rintro ⟨P, hPdeg, hPeq⟩
  -- `X^k − P` vanishes on all `n` domain points but has degree `k < n`
  set g : F[X] := X ^ k - P with hg
  have hgdeg : g.degree = (k : WithBot ℕ) := by
    rw [hg, degree_sub_eq_left_of_degree_lt (by rw [degree_X_pow]; exact hPdeg), degree_X_pow]
  have hg0 : g ≠ 0 := by
    intro h; rw [h, degree_zero] at hgdeg; exact WithBot.bot_ne_coe hgdeg
  have hroots : ∀ i, g.IsRoot (dom i) := by
    intro i
    have := congrFun hPeq i
    simp only [IsRoot, hg, eval_sub, eval_pow, eval_X]
    rw [← this]; ring
  have hcard : (n : ℕ) ≤ g.natDegree := by
    calc (n : ℕ) = (Finset.univ : Finset (Fin n)).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ = (Finset.univ.image dom).card :=
          (Finset.card_image_of_injective _ dom.injective).symm
      _ ≤ g.roots.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          rw [Multiset.mem_toFinset, mem_roots hg0]; exact hroots i
      _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := card_roots' _
  rw [natDegree_eq_of_degree_eq_some hgdeg] at hcard
  omega

open Classical in
/-- **THE COMPOSED SUPPLY REDUCTION**: for the MCA direction `xᵏ` over a domain with
`0 ∉ image` and `k < n`, the bad scalars of `u₀ + γ·xᵏ` number at most the single-word
agreement-`a` list of `u₀` in `rsCode dom (k+1)`, times `⌊n/a⌋`. -/
theorem badScalar_card_le_codeword_list_mul (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (hk : k < n) (u₀ : Fin n → F) (hdom : ∀ i, dom i ≠ 0) :
    ((Finset.univ : Finset F).filter
        (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun Q => Q ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F))
            ∧ a ≤ (agreeSet Q u₀).card)).card * (n / a) := by
  have hne : ∀ i, (dom i) ^ k ≠ 0 := fun i => pow_ne_zero k (hdom i)
  refine le_trans (badScalar_card_le_lineList_mul dom k a ha u₀
    (fun i => (dom i) ^ k) hne) ?_
  exact Nat.mul_le_mul_right _
    (lineList_card_le_codeword_list dom k a u₀ (xpow_not_mem_rsCode dom hk))

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.xpow_not_mem_rsCode
#print axioms ProximityGap.Ownership.badScalar_card_le_codeword_list_mul
