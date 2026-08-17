/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Lattice2.Spec

open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Open beyond-UDR Guruswami-Sudan mass-bound route for the prize. -/
def mcaPrize_beyond_udr_bound {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

/-- Lemma bounding the density of false-positive roots for univariate polynomials. -/
lemma root_density_bound_univ {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (p : Polynomial F) (hp : p ≠ 0) :
    (Finset.univ.filter fun x => p.eval x = 0).card ≤ p.natDegree := by
  have h_roots := Polynomial.card_roots' p
  have h_subset : (Finset.univ.filter fun x => p.eval x = 0) ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hx
  have h_card := Finset.card_le_card h_subset
  have h_nodup := Multiset.toFinset_card_le p.roots
  exact le_trans h_card (le_trans h_nodup h_roots)

end ArkLib.CodingTheory.Research
