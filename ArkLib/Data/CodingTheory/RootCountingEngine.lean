/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The reusable root-counting engine

Extracts the `hcount`/biUnion root-counting block used (in slightly different guises) in
`curveBadCount_udr_le` (`CurveUDRBadCount.lean`) and `badGamma_le` (`MCAUDRBound.lean`):

* `card_le_of_subset_biUnion_roots` — if every element of a finite set `G` of field elements is
  a root of one of an indexed family of nonzero polynomials of degree `≤ D` supported on `Supp`,
  then `G.card ≤ D * Supp.card`.

* `card_le_of_eFamily` — the exact instance consumed in `curveBadCount_udr_le`:
  `P i = ∑ k : Fin L, C (e k i) * X ^ (k : ℕ)`, nonzero on the support filter, degree `≤ L − 1`.
-/

namespace ArkLib.RootCounting

open Finset Polynomial

/-- **The root-counting engine.** If every `γ ∈ G` is a root of some `P i` with `i ∈ Supp`,
where each `P i` (for `i ∈ Supp`) is nonzero of `natDegree ≤ D`, then `G.card ≤ D * Supp.card`.

Proof: `G ⊆ Supp.biUnion (roots-toFinset)`, then `card_biUnion_le`, then per-index
`Multiset.toFinset_card_le` and `Polynomial.card_roots'`. -/
theorem card_le_of_subset_biUnion_roots {F : Type} [Field F] [DecidableEq F]
    {κ : Type} [DecidableEq κ] (G : Finset F) (Supp : Finset κ) (P : κ → Polynomial F) (D : ℕ)
    (hdeg : ∀ i ∈ Supp, (P i).natDegree ≤ D)
    (hne : ∀ i ∈ Supp, P i ≠ 0)
    (hG : ∀ γ ∈ G, ∃ i ∈ Supp, (P i).IsRoot γ) :
    G.card ≤ D * Supp.card := by
  have hsub : G ⊆ Supp.biUnion (fun i => (P i).roots.toFinset) := by
    intro γ hγ
    obtain ⟨i, hi, hroot⟩ := hG γ hγ
    rw [Finset.mem_biUnion]
    refine ⟨i, hi, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hne i hi, hroot⟩
  calc G.card ≤ (Supp.biUnion (fun i => (P i).roots.toFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Supp, ((P i).roots.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Supp, D := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        calc ((P i).roots.toFinset).card
            ≤ Multiset.card (P i).roots := Multiset.toFinset_card_le _
          _ ≤ (P i).natDegree := Polynomial.card_roots' _
          _ ≤ D := hdeg i hi
    _ = D * Supp.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Coefficient extraction for the `e`-family polynomial: the `(k : ℕ)`-th coefficient of
`∑ j : Fin L, C (a j) * X ^ (j : ℕ)` is `a k`. -/
private lemma coeff_eFamily {F : Type} [Semiring F] {L : ℕ} (a : Fin L → F) (k : Fin L) :
    (∑ j : Fin L, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (k : ℕ) = a k := by
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro b _ hbk
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_neg (fun h => hbk ((Fin.ext h).symm)), mul_zero]
  · intro habs; exact absurd (Finset.mem_univ k) habs

/-- **The `e`-family instance consumed in `curveBadCount_udr_le`.** If every `γ ∈ G` kills the
linear combination `∑ k, γ^k · e k i` at some coordinate `i` where the stack `e · i` is not
identically zero, then `G.card ≤ (L − 1) * |{i : ∃ k, e k i ≠ 0}|`.

This is the `hcount` block of `curveBadCount_udr_le`, derived from the engine with
`P i = ∑ k : Fin L, C (e k i) * X ^ (k : ℕ)` and `D = L − 1`. -/
theorem card_le_of_eFamily {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {L : ℕ} (e : Fin L → ι → F) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧ ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0) :
    G.card ≤ (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card := by
  refine card_le_of_subset_biUnion_roots G
    (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0))
    (fun i => ∑ k : Fin L, Polynomial.C (e k i) * Polynomial.X ^ (k : ℕ)) (L - 1)
    ?_ ?_ ?_
  · -- degree bound
    intro i _
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have hk := k.isLt
    omega
  · -- nonzero on the support filter
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    intro habs
    apply hk
    have h := congrArg (fun p => Polynomial.coeff p (k : ℕ)) habs
    simp only [Polynomial.coeff_zero] at h
    rw [coeff_eFamily (fun j => e j i) k] at h
    exact h
  · -- every γ ∈ G is a root of its coordinate polynomial
    intro γ hγ
    obtain ⟨i, hik, hsum⟩ := hG γ hγ
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩, ?_⟩
    rw [Polynomial.IsRoot, Polynomial.eval_finset_sum, ← hsum]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]; ring)

end ArkLib.RootCounting

#print axioms ArkLib.RootCounting.card_le_of_subset_biUnion_roots
#print axioms ArkLib.RootCounting.card_le_of_eFamily
