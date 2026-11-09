/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipBound

/-!
# The owned-triple count (k = 2 universal law, crux brick)

The geometric count that the `k = 2` universal below-UDR law needs, mirroring
`owned_pairs_card_ge` (the `k = 1` value-multiplicity count) one dimension up.

For a witness set `W` and direction `u₁` whose **collinearity is bounded by `ν`**
(every distinct pair `(i,j)` has at most `ν` points `c ∈ W` with
`residual dom 2 ![i,j,c] u₁ = 0`, i.e. on the line through the two graph points),
at least `|W|·(|W|−1)·(|W|−ν)` ordered triples are **owned** (non-collinear,
`residual ≠ 0`). These feed `badScalars_card_mul_le_ownership` at `k = 2`.
-/

open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

open Classical in
/-- **The owned-triple lower bound.** If `u₁` has collinearity `≤ ν` on `W`
(every distinct pair owns at most `ν` collinear completions), then at least
`|W|·(|W|−1)·(|W|−ν)` ordered triples of `W` are non-collinear. -/
theorem owned_triples_card_ge (dom : Fin n ↪ F) (W : Finset (Fin n))
    {u₁ : Fin n → F} {ν : ℕ}
    (hν : ∀ i ∈ W, ∀ j ∈ W, i ≠ j →
      (W.filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card ≤ ν) :
    W.card * (W.card - 1) * (W.card - ν)
      ≤ ((W ×ˢ W ×ˢ W).filter
          (fun p => residual dom 2 ![p.1, p.2.1, p.2.2] u₁ ≠ 0)).card := by
  -- count owned triples fiberwise over the first two coordinates
  set owned := (W ×ˢ W ×ˢ W).filter
    (fun p : Fin n × Fin n × Fin n => residual dom 2 ![p.1, p.2.1, p.2.2] u₁ ≠ 0)
    with howned
  -- the projection to the first two coordinates
  have hfib : owned.card
      = ∑ ij ∈ W ×ˢ W, (owned.filter
          (fun p : Fin n × Fin n × Fin n => (p.1, p.2.1) = ij)).card := by
    refine Finset.card_eq_sum_card_fiberwise
      (f := fun p : Fin n × Fin n × Fin n => (p.1, p.2.1)) ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_product.mpr ⟨hp1, (Finset.mem_product.mp hp2).1⟩
  rw [hfib]
  -- lower bound the diagonal-free pairs by |W| − ν each
  have hbound : ∀ ij ∈ W ×ˢ W, ij.1 ≠ ij.2 →
      W.card - ν ≤ (owned.filter
        (fun p : Fin n × Fin n × Fin n => (p.1, p.2.1) = ij)).card := by
    intro ij hij hne
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    -- the fiber over (i,j) bijects with {c ∈ W : residual ![i,j,c] ≠ 0}
    have hbij : (owned.filter (fun p => (p.1, p.2.1) = ij)).card
        = (W.filter (fun c => residual dom 2 ![ij.1, ij.2, c] u₁ ≠ 0)).card := by
      refine Finset.card_nbij' (fun p => p.2.2) (fun c => (ij.1, ij.2, c)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, howned, Finset.mem_filter, Finset.mem_product] at hp ⊢
        obtain ⟨⟨⟨_, _, hpc⟩, hres⟩, hp2⟩ := hp
        have h1 : p.1 = ij.1 := congrArg Prod.fst hp2
        have h2 : p.2.1 = ij.2 := congrArg Prod.snd hp2
        refine ⟨hpc, ?_⟩
        rw [← h1, ← h2]; exact hres
      · intro c hc
        simp only [Finset.mem_coe, howned, Finset.mem_filter, Finset.mem_product] at hc ⊢
        exact ⟨⟨⟨hi, hj, hc.1⟩, hc.2⟩, trivial⟩
      · intro p hp
        simp only [Finset.mem_coe, howned, Finset.mem_filter] at hp
        have h1 : p.1 = ij.1 := congrArg Prod.fst hp.2
        have h2 : p.2.1 = ij.2 := congrArg Prod.snd hp.2
        ext <;> simp_all
      · intro c hc; rfl
    rw [hbij]
    -- |W| − ν ≤ |{c : ≠0}| = |W| − |{c : =0}|, and |{c: =0}| ≤ ν
    simp only [ne_eq]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := W) (p := fun c => residual dom 2 ![ij.1, ij.2, c] u₁ = 0)
    have hle := hν ij.1 hi ij.2 hj hne
    omega
  -- sum: drop the diagonal, each off-diagonal pair contributes ≥ |W| − ν
  calc W.card * (W.card - 1) * (W.card - ν)
      = ∑ _ij ∈ (W ×ˢ W).filter (fun ij => ij.1 ≠ ij.2), (W.card - ν) := by
        rw [Finset.sum_const, smul_eq_mul]
        congr 1
        -- |off-diagonal pairs| = |W|·(|W|−1)
        have hoff : ((W ×ˢ W).filter (fun ij => ij.1 ≠ ij.2)).card
            = W.card * W.card - W.card := by
          have hd := Finset.card_filter_add_card_filter_not
            (s := W ×ˢ W) (p := fun ij => ij.1 = ij.2)
          rw [Finset.card_product] at hd
          have hdiag : ((W ×ˢ W).filter (fun ij => ij.1 = ij.2)).card = W.card := by
            refine Finset.card_nbij' (fun ij => ij.1) (fun i => (i, i)) ?_ ?_ ?_ ?_
            · intro ij hij
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hij ⊢
              exact hij.1.1
            · intro i hi
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hi ⊢
              exact ⟨⟨hi, hi⟩, trivial⟩
            · intro ij hij
              simp only [Finset.mem_coe, Finset.mem_filter] at hij
              exact Prod.ext rfl hij.2
            · intro i _; rfl
          rw [hdiag] at hd
          simp only [ne_eq]
          omega
        rw [hoff]
        generalize W.card = s
        cases s with
        | zero => rfl
        | succ k => simp only [Nat.succ_sub_one, Nat.mul_succ]; omega
    _ ≤ ∑ ij ∈ (W ×ˢ W).filter (fun ij => ij.1 ≠ ij.2),
          (owned.filter (fun p => (p.1, p.2.1) = ij)).card := by
        refine Finset.sum_le_sum fun ij hij => ?_
        obtain ⟨hijW, hijne⟩ := Finset.mem_filter.mp hij
        exact hbound ij hijW hijne
    _ ≤ ∑ ij ∈ W ×ˢ W, (owned.filter (fun p => (p.1, p.2.1) = ij)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.owned_triples_card_ge
