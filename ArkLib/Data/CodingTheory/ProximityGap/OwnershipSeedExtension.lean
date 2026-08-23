/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipBound

/-!
# Seed-extension ownership counting (#371)

This file factors out the finite counting brick needed for the general-`k`
version of the multiplicity theorem.

Fix a witness set `S`.  A `k`-seed is an injective ordered `k`-tuple inside `S`.
If, for every seed, at most `μ` extensions fail a predicate `good`, then at least
`#seeds * (|S| - μ)` seed-extension pairs are good.  The snoc map sends those
pairs injectively into ordered `(k+1)`-tuples.

The residual wrapper specializes `good` to `residual dom k t u₁ ≠ 0`.  It is the
combinatorial half of the planned general-`k` multiplicity theorem; the remaining
mathematical bridge is the interpolation statement that a zero-residual extension
lies in the agreement fibre of the degree-`< k` interpolant determined by its seed.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {α : Type} [Fintype α] [DecidableEq α]

open Classical in
/-- Injective ordered `k`-seeds whose entries lie in `S`. -/
def injectiveSeeds (S : Finset α) (k : ℕ) : Finset (Fin k → α) :=
  Finset.univ.filter (fun s => Function.Injective s ∧ ∀ a, s a ∈ S)

@[simp]
theorem mem_injectiveSeeds {S : Finset α} {k : ℕ} {s : Fin k → α} :
    s ∈ injectiveSeeds S k ↔ Function.Injective s ∧ ∀ a, s a ∈ S := by
  simp [injectiveSeeds]

open Classical in
/-- Good seed-extension pairs, before quotienting them into `(k+1)`-tuples. -/
def seedExtensionPairs (S : Finset α) (k : ℕ)
    (good : (Fin (k + 1) → α) → Prop) [DecidablePred good] :
    Finset ((Fin k → α) × α) :=
  (injectiveSeeds S k ×ˢ S).filter (fun p => good (Fin.snoc p.1 p.2))

open Classical in
/-- If each seed has at most `μ` bad extensions, then many seed-extension pairs
are good.  This is the pure counting core of the general multiplicity route. -/
theorem seedExtensionPairs_card_ge (S : Finset α) (k μ : ℕ)
    (good : (Fin (k + 1) → α) → Prop) [DecidablePred good]
    (hμ : ∀ s ∈ injectiveSeeds S k,
      (S.filter (fun x => ¬ good (Fin.snoc s x))).card ≤ μ) :
    (injectiveSeeds S k).card * (S.card - μ)
      ≤ (seedExtensionPairs S k good).card := by
  set seeds := injectiveSeeds S k with hseeds
  have hper : ∀ s ∈ seeds,
      S.card - μ ≤ (S.filter (fun x => good (Fin.snoc s x))).card := by
    intro s hs
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun x => good (Fin.snoc s x))
    have hbad : (S.filter (fun x => ¬ good (Fin.snoc s x))).card ≤ μ := by
      exact hμ s (by simpa [hseeds] using hs)
    omega
  have hfiber :
      (seedExtensionPairs S k good).card =
        ∑ s ∈ seeds, (S.filter (fun x => good (Fin.snoc s x))).card := by
    unfold seedExtensionPairs
    rw [← hseeds]
    have hfib :
        ((seeds ×ˢ S).filter (fun p => good (Fin.snoc p.1 p.2))).card
          = ∑ s ∈ seeds,
              (((seeds ×ˢ S).filter (fun p => good (Fin.snoc p.1 p.2))).filter
                (fun p => p.1 = s)).card := by
      refine Finset.card_eq_sum_card_fiberwise (f := Prod.fst) ?_
      intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [hfib]
    refine Finset.sum_congr rfl fun s hs => ?_
    refine Finset.card_nbij (fun p => p.2) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
      obtain ⟨hp', hps⟩ := hp
      obtain ⟨hpp, hgood⟩ := Finset.mem_filter.mp hp'
      exact ⟨(Finset.mem_product.mp hpp).2, by simpa [hps] using hgood⟩
    · intro p hp q hq hq2
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have hp1 : p.1 = s := hp.2
      have hq1 : q.1 = s := hq.2
      exact Prod.ext (hp1.trans hq1.symm) hq2
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      refine ⟨(s, x), ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hs, hx.1⟩, hx.2⟩
  calc (injectiveSeeds S k).card * (S.card - μ)
      = ∑ _s ∈ seeds, (S.card - μ) := by
          rw [hseeds, Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ s ∈ seeds, (S.filter (fun x => good (Fin.snoc s x))).card :=
          Finset.sum_le_sum hper
    _ = (seedExtensionPairs S k good).card := hfiber.symm

open Classical in
/-- The snoc map from seed-extension pairs to `(k+1)`-tuples is injective, so the
pair count lower-bounds the number of good ordered tuples. -/
theorem seedExtensionTuples_card_ge (S : Finset α) (k μ : ℕ)
    (good : (Fin (k + 1) → α) → Prop) [DecidablePred good]
    (hμ : ∀ s ∈ injectiveSeeds S k,
      (S.filter (fun x => ¬ good (Fin.snoc s x))).card ≤ μ) :
    (injectiveSeeds S k).card * (S.card - μ)
      ≤ (Finset.univ.filter good).card := by
  refine le_trans (seedExtensionPairs_card_ge S k μ good hμ) ?_
  refine Finset.card_le_card_of_injOn (fun p => Fin.snoc p.1 p.2) ?_ ?_
  · intro p hp
    have hp' : p ∈ (injectiveSeeds S k ×ˢ S).filter
        (fun p => good (Fin.snoc p.1 p.2)) := by
      simpa [seedExtensionPairs] using hp
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp').2⟩
  · intro p hp q hq hsnoc
    refine Prod.ext ?_ ?_
    · funext a
      have := congrFun hsnoc a.castSucc
      simpa [Fin.snoc_castSucc] using this
    · have := congrFun hsnoc (Fin.last k)
      simpa [Fin.snoc_last] using this

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

open Classical in
/-- Residual-specialized seed-extension count.  To use this as the general-`k`
multiplicity input, it remains to prove the hypothesis from a max-agreement bound:
for a fixed injective seed, zero residual extensions are contained in the agreement
fibre of the unique degree-`< k` interpolant through the seed. -/
theorem residual_seedExtensionTuples_card_ge (dom : Fin n ↪ F)
    (S : Finset (Fin n)) (k μ : ℕ) (u₁ : Fin n → F)
    (hμ : ∀ s ∈ injectiveSeeds S k,
      (S.filter (fun x =>
        ProximityGap.Ownership.residual dom k (Fin.snoc s x) u₁ = 0)).card ≤ μ) :
    (injectiveSeeds S k).card * (S.card - μ)
      ≤ (Finset.univ.filter
          (fun t : Fin (k + 1) → Fin n =>
            ProximityGap.Ownership.residual dom k t u₁ ≠ 0)).card := by
  refine seedExtensionTuples_card_ge S k μ
    (fun t : Fin (k + 1) → Fin n =>
      ProximityGap.Ownership.residual dom k t u₁ ≠ 0) ?_
  intro s hs
  simpa using hμ s hs

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.seedExtensionPairs_card_ge
#print axioms ProximityGap.Ownership.seedExtensionTuples_card_ge
#print axioms ProximityGap.Ownership.residual_seedExtensionTuples_card_ge
