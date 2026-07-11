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

/-- Select one endpoint of an unindexed pair. -/
def endpointAt {J : Type} (p : J × J) (e : Fin 2) : J :=
  if e = 0 then p.1 else p.2

@[simp]
theorem endpointAt_zero {J : Type} (p : J × J) : endpointAt p 0 = p.1 := by
  simp [endpointAt]

@[simp]
theorem endpointAt_one {J : Type} (p : J × J) : endpointAt p 1 = p.2 := by
  simp [endpointAt]

/-- Exact four-colour orientation form of pair interaction. -/
theorem pairInteracts_iff_exists_orientation
    {J : Type} (witness : J → Finset (Fin N)) (p q : J × J) :
    PairInteracts witness p q ↔
      ∃ e f : Fin 2,
        K ≤ (witness (endpointAt p e) ∩ witness (endpointAt q f)).card := by
  constructor
  · intro h
    rcases h with h | h | h | h
    · exact ⟨0, 0, by simpa using h⟩
    · exact ⟨0, 1, by simpa using h⟩
    · exact ⟨1, 0, by simpa using h⟩
    · exact ⟨1, 1, by simpa using h⟩
  · rintro ⟨e, f, h⟩
    fin_cases e <;> fin_cases f <;> simp only [endpointAt_zero, endpointAt_one] at h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- Canonical chosen endpoint orientation for an interacting pair of pair-vertices. -/
noncomputable def interactionOrientation
    {J : Type} (witness : J → Finset (Fin N)) (p q : J × J)
    (h : PairInteracts witness p q) : Fin 2 × Fin 2 :=
  let hex := (pairInteracts_iff_exists_orientation witness p q).mp h
  (Classical.choose hex, Classical.choose (Classical.choose_spec hex))

/-- The chosen orientation really carries a `K`-overlap. -/
theorem interactionOrientation_spec
    {J : Type} (witness : J → Finset (Fin N)) (p q : J × J)
    (h : PairInteracts witness p q) :
    K ≤ (witness (endpointAt p (interactionOrientation witness p q h).1) ∩
      witness (endpointAt q (interactionOrientation witness p q h).2)).card := by
  exact Classical.choose_spec (Classical.choose_spec
    ((pairInteracts_iff_exists_orientation witness p q).mp h))

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

/-! ## The global interaction graph on an arbitrary matching -/

/-- Endpoint-disjointness data carried by a matching of scalar pairs. -/
def PairMatching {J : Type} (M : Finset (J × J)) : Prop :=
  (∀ p ∈ M, p.1 ≠ p.2) ∧
  ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

/-- Graph on the matched pairs, with an edge for any cross-endpoint `K`-overlap. -/
noncomputable def interactionGraph
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) : SimpleGraph M where
  Adj p q := p ≠ q ∧ PairInteracts witness p.1 q.1
  symm := by
    intro p q h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- The complement interaction graph is `K₅`-free. -/
theorem interactionGraph_compl_cliqueFree_five
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (hmatching : PairMatching M)
    (hsize : ∀ p ∈ M, T ≤ (witness p.1).card ∧ T ≤ (witness p.2).card) :
    (interactionGraph witness M)ᶜ.CliqueFree 5 := by
  classical
  intro G5 hG5
  have he : G5 ≃ Fin 5 := by
    rw [← hG5.card_eq]
    exact G5.equivFin
  let pair : Fin 5 → J × J := fun i => (he.symm i).1.1
  have hpairM : ∀ i, pair i ∈ M := fun i => (he.symm i).1.2
  have hpairNe : ∀ i j, i ≠ j → pair i ≠ pair j := by
    intro i j hij hp
    apply hij
    apply he.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hp
  have hendpoint : Function.Injective (endpoint pair) := by
    rintro ⟨i, e⟩ ⟨j, f⟩ h
    by_cases hij : i = j
    · subst j
      fin_cases e <;> fin_cases f <;> simp only [endpoint_zero, endpoint_one] at h ⊢
      · exact (hmatching.1 (pair i) (hpairM i) h).elim
      · exact (hmatching.1 (pair i) (hpairM i) h.symm).elim
    · have hpq := hmatching.2 (pair i) (hpairM i) (pair j) (hpairM j)
          (hpairNe i j hij)
      fin_cases e <;> fin_cases f <;> simp only [endpoint_zero, endpoint_one] at h ⊢
      · exact (hpq.1 h).elim
      · exact (hpq.2.1 h).elim
      · exact (hpq.2.2.1 h).elim
      · exact (hpq.2.2.2 h).elim
  have hendpointSize : ∀ z : Fin 5 × Fin 2,
      T ≤ (witness (endpoint pair z)).card := by
    rintro ⟨i, e⟩
    fin_cases e
    · simpa only [endpoint_zero] using (hsize (pair i) (hpairM i)).1
    · simpa only [endpoint_one] using (hsize (pair i) (hpairM i)).2
  obtain ⟨i, j, hij, hpij, hinteract⟩ :=
    exists_interacting_pair_of_five witness pair hendpoint hendpointSize
  let vi : M := ⟨pair i, hpairM i⟩
  let vj : M := ⟨pair j, hpairM j⟩
  have hvij : vi ≠ vj := by
    intro h
    exact hpij (congrArg Subtype.val h)
  have hadj : (interactionGraph witness M).Adj vi vj := ⟨hvij, hinteract⟩
  have hi : vi ∈ G5 := (he.symm i).2
  have hj : vj ∈ G5 := (he.symm j).2
  have hcompl := hG5.isClique hi hj hvij
  exact ((SimpleGraph.compl_adj _ _ _).mp hcompl).2 hadj

end ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

open ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

#print axioms PairInteracts.symm
#print axioms pairInteracts_iff_exists_orientation
#print axioms interactionOrientation_spec
#print axioms exists_interacting_pair_of_five
#print axioms not_five_pairwise_noninteracting
#print axioms interactionGraph_compl_cliqueFree_five
