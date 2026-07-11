/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph

/-!
# P1 matched secants: the pair-interaction graph has independence at most four

The forced-secant matching contains roughly half a billion vertex-disjoint scalar pairs.  This
file passes the sharp five-set overlap theorem to the quotient whose vertices are those pairs.
Two pair-vertices interact when some endpoint witness from the first overlaps some endpoint
witness from the second on at least `K` coordinates.

Among any five vertex-disjoint pairs, choose (say) endpoint zero from each pair.  Those five
threshold-size witnesses force a `K`-overlap, hence two of the pair-vertices interact.  Therefore
the pair-interaction graph has independence number at most four.  This is the first global
constraint that acts directly on the matched-secant population rather than on individual scalar
witnesses or core cardinalities.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

open P1RateQuarterAgreementOverlapGraph

/-- Endpoint selector for an indexed collection of pairs. -/
def endpoint {J : Type} (pair : Fin 5 → J × J) (z : Fin 5 × Fin 2) : J :=
  if z.2 = 0 then (pair z.1).1 else (pair z.1).2

@[simp]
theorem endpoint_zero {J : Type} (pair : Fin 5 → J × J) (i : Fin 5) :
    endpoint pair (i, 0) = (pair i).1 := by simp [endpoint]

@[simp]
theorem endpoint_one {J : Type} (pair : Fin 5 → J × J) (i : Fin 5) :
    endpoint pair (i, 1) = (pair i).2 := by simp [endpoint]

/-- Some endpoint of `p` has a large agreement overlap with some endpoint of `q`. -/
def PairInteracts {J : Type} (witness : J → Finset (Fin N))
    (p q : J × J) : Prop :=
  K ≤ (witness p.1 ∩ witness q.1).card ∨
  K ≤ (witness p.1 ∩ witness q.2).card ∨
  K ≤ (witness p.2 ∩ witness q.1).card ∨
  K ≤ (witness p.2 ∩ witness q.2).card

theorem PairInteracts.symm
    {J : Type} {witness : J → Finset (Fin N)} {p q : J × J}
    (h : PairInteracts witness p q) : PairInteracts witness q p := by
  rcases h with h | h | h | h
  · exact Or.inl (by simpa only [Finset.inter_comm] using h)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [Finset.inter_comm] using h)))
  · exact Or.inr (Or.inl (by simpa only [Finset.inter_comm] using h))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [Finset.inter_comm] using h)))

/-- **Five-pair interaction forcing.**  Five vertex-disjoint matched pairs with threshold-size
endpoint witnesses contain two distinct pair-vertices that interact. -/
theorem exists_interacting_pair_of_five
    {J : Type} (witness : J → Finset (Fin N))
    (pair : Fin 5 → J × J)
    (hendpoint : Function.Injective (endpoint pair))
    (hsize : ∀ z : Fin 5 × Fin 2, T ≤ (witness (endpoint pair z)).card) :
    ∃ i j : Fin 5, i ≠ j ∧ pair i ≠ pair j ∧
      PairInteracts witness (pair i) (pair j) := by
  let S : Fin 5 → Finset (Fin N) := fun i => witness (endpoint pair (i, 0))
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_five S (fun i => hsize (i, 0))
  have hpij : pair i ≠ pair j := by
    intro hp
    have he : endpoint pair (i, 0) = endpoint pair (j, 0) := by simp [hp]
    exact hij (congrArg Prod.fst (hendpoint he))
  refine ⟨i, j, hij, hpij, Or.inl ?_⟩
  simpa only [S, endpoint_zero] using hoverlap

/-- Relation-theoretic form: no five vertex-disjoint pairs can be pairwise noninteracting. -/
theorem not_five_pairwise_noninteracting
    {J : Type} (witness : J → Finset (Fin N))
    (pair : Fin 5 → J × J)
    (hendpoint : Function.Injective (endpoint pair))
    (hsize : ∀ z : Fin 5 × Fin 2, T ≤ (witness (endpoint pair z)).card) :
    ¬ ∀ i j : Fin 5, i ≠ j → ¬ PairInteracts witness (pair i) (pair j) := by
  intro hnone
  obtain ⟨i, j, hij, _hpij, hinteract⟩ :=
    exists_interacting_pair_of_five witness pair hendpoint hsize
  exact hnone i j hij hinteract

end ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

open ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

#print axioms PairInteracts.symm
#print axioms exists_interacting_pair_of_five
#print axioms not_five_pairwise_noninteracting
