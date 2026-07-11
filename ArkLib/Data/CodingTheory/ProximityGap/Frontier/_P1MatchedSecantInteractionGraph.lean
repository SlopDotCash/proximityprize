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

/-- A complement-`K₅`-free finite graph has a dominating independent set of cardinality at most
four.  This is the maximal-independent-set form of the density input and avoids edge counting. -/
theorem exists_dominating_indep_card_le_four
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hfree : Gᶜ.CliqueFree 5) :
    ∃ I : Finset V, I.card ≤ 4 ∧ G.IsIndepSet I ∧
      ∀ v : V, v ∉ I → ∃ i ∈ I, G.Adj v i := by
  classical
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  have hIcard : I.card ≤ 4 := by
    by_contra hnot
    have hfive : 5 ≤ I.card := by omega
    obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq hfive
    have hSindep : G.IsIndepSet S := hI.isIndepSet.mono hSI
    exact hfree S ⟨(G.isClique_compl.mpr hSindep), hScard⟩
  refine ⟨I, hIcard, hI.isIndepSet, ?_⟩
  intro v hvI
  by_contra hnone
  push Not at hnone
  have hInsertClique : Gᶜ.IsClique (insert v I) := by
    apply (G.isClique_compl.mpr hI.isIndepSet).insert
    intro b hb hvb
    rw [SimpleGraph.compl_adj]
    exact ⟨hvb, hnone b hb⟩
  have hInsertIndep : G.IsIndepSet (↑(insert v I) : Set V) := by
    rw [← G.isClique_compl]
    simpa only [Finset.coe_insert] using hInsertClique
  have hmax := hI.maximum (insert v I) hInsertIndep
  rw [Finset.card_insert_of_notMem hvI] at hmax
  omega

/-- **Four-centre matched-secant domination.**  Every matched pair outside a set of at most four
pair-vertices interacts with one of those centres. -/
theorem exists_four_interaction_centres
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (hmatching : PairMatching M)
    (hsize : ∀ p ∈ M, T ≤ (witness p.1).card ∧ T ≤ (witness p.2).card) :
    ∃ I : Finset M, I.card ≤ 4 ∧
      ∀ p : M, p ∉ I → ∃ q ∈ I, PairInteracts witness p.1 q.1 := by
  obtain ⟨I, hIcard, _hIindep, hdom⟩ :=
    exists_dominating_indep_card_le_four (interactionGraph witness M)
      (interactionGraph_compl_cliqueFree_five witness M hmatching hsize)
  refine ⟨I, hIcard, ?_⟩
  intro p hp
  obtain ⟨q, hq, hadj⟩ := hdom p hp
  exact ⟨q, hq, hadj.2⟩

/-- Matched pairs outside a chosen centre set. -/
abbrev OutsideCentres {J : Type} {M : Finset (J × J)} (I : Finset M) :=
  {p : M // p ∉ I}

/-- **Deterministic four-centre routing.**  In addition to the bounded centre set, choose for
every outside matched pair one centre, one endpoint on the outside pair, and one endpoint on the
centre, with the exact `K`-overlap certificate. -/
theorem exists_four_centres_with_oriented_routing
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (hmatching : PairMatching M)
    (hsize : ∀ p ∈ M, T ≤ (witness p.1).card ∧ T ≤ (witness p.2).card) :
    ∃ I : Finset M, I.card ≤ 4 ∧
      ∃ centre : OutsideCentres I → I,
      ∃ orient : OutsideCentres I → Fin 2 × Fin 2,
      ∀ p : OutsideCentres I,
        K ≤ (witness (endpointAt p.1.1 (orient p).1) ∩
          witness (endpointAt (centre p).1.1 (orient p).2)).card := by
  obtain ⟨I, hIcard, hdom⟩ :=
    exists_four_interaction_centres witness M hmatching hsize
  have hex : ∀ p : OutsideCentres I,
      ∃ q : I, PairInteracts witness p.1.1 q.1.1 := by
    intro p
    obtain ⟨q, hq, hinteract⟩ := hdom p.1 p.2
    exact ⟨⟨q, hq⟩, hinteract⟩
  let centre : OutsideCentres I → I := fun p => Classical.choose (hex p)
  have hcentre : ∀ p, PairInteracts witness p.1.1 (centre p).1.1 := fun p =>
    Classical.choose_spec (hex p)
  let orient : OutsideCentres I → Fin 2 × Fin 2 := fun p =>
    interactionOrientation witness p.1.1 (centre p).1.1 (hcentre p)
  refine ⟨I, hIcard, centre, orient, ?_⟩
  intro p
  exact interactionOrientation_spec witness p.1.1 (centre p).1.1 (hcentre p)

/-! ## Decoded-family cross-secant connector -/

open _root_.ProximityGap Code
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

/-- Agreement witness set attached to one selected decoded scalar. -/
noncomputable def familyWitness
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u) (gamma : F) : Finset (Fin N) :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma)

/-- **One routed interaction is a literal large-core cross-secant.**  If two endpoint-disjoint
matched pairs interact, some oriented cross-pair canonical secant has joint core at least `K`. -/
theorem pairInteracts_exists_crossSecant_core
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (p q : F × F)
    (hp : p.1 ∈ family.G ∧ p.2 ∈ family.G)
    (hq : q.1 ∈ family.G ∧ q.2 ∈ family.G)
    (hcross : ∀ e f : Fin 2, endpointAt p e ≠ endpointAt q f)
    (hinteract : PairInteracts (familyWitness family) p q) :
    ∃ e f : Fin 2,
      K ≤ (jointCore dom (u 0) (u 1)
        (secantParameter family (endpointAt p e) (endpointAt q f)).1
        (secantParameter family (endpointAt p e) (endpointAt q f)).2).card := by
  obtain ⟨e, f, hoverlap⟩ :=
    (pairInteracts_iff_exists_orientation (familyWitness family) p q).mp hinteract
  let gamma := endpointAt p e
  let beta := endpointAt q f
  have hgamma : gamma ∈ family.G := by
    fin_cases e
    · simpa only [gamma, endpointAt_zero] using hp.1
    · simpa only [gamma, endpointAt_one] using hp.2
  have hbeta : beta ∈ family.G := by
    fin_cases f
    · simpa only [beta, endpointAt_zero] using hq.1
    · simpa only [beta, endpointAt_one] using hq.2
  have hne : gamma ≠ beta := hcross e f
  let line := secantParameter family gamma beta
  have hgammaOn : gamma ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family hgamma
  have hbetaOn : beta ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family hbeta hne
  have hgammaLine := (mem_pointsOn_iff family line gamma).mp hgammaOn |>.2
  have hbetaLine := (mem_pointsOn_iff family line beta).mp hbetaOn |>.2
  refine ⟨e, f, ?_⟩
  show K ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  rw [← fullAgreement_inter_eq_jointCore
    dom (u 0) (u 1) line.1 line.2 hne]
  simpa only [familyWitness, gamma, beta, line, hgammaLine, hbetaLine] using hoverlap

/-! ## Two-sided endpoint domination -/

/-- Fixed-endpoint overlap graph: compare endpoint `e` on both matched pairs. -/
noncomputable def fixedEndpointGraph
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (e : Fin 2) : SimpleGraph M where
  Adj p q := p ≠ q ∧
    K ≤ (witness (endpointAt p.1 e) ∩ witness (endpointAt q.1 e)).card
  symm := by
    intro p q h
    exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- Each fixed-endpoint graph separately has independence number at most four. -/
theorem fixedEndpointGraph_compl_cliqueFree_five
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (e : Fin 2)
    (hsize : ∀ p ∈ M, T ≤ (witness (endpointAt p e)).card) :
    (fixedEndpointGraph witness M e)ᶜ.CliqueFree 5 := by
  classical
  intro G5 hG5
  have heq : G5 ≃ Fin 5 := by
    rw [← hG5.card_eq]
    exact G5.equivFin
  let vertex : Fin 5 → M := fun i => (heq.symm i).1
  let S : Fin 5 → Finset (Fin N) := fun i => witness (endpointAt (vertex i).1 e)
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_five S (fun i => hsize (vertex i).1 (vertex i).2)
  have hvij : vertex i ≠ vertex j := by
    intro h
    exact hij (heq.symm.injective (Subtype.ext h))
  have hadj : (fixedEndpointGraph witness M e).Adj (vertex i) (vertex j) :=
    ⟨hvij, by simpa only [S] using hoverlap⟩
  have hi : vertex i ∈ G5 := (heq.symm i).2
  have hj : vertex j ∈ G5 := (heq.symm j).2
  have hcompl := hG5.isClique hi hj hvij
  exact ((SimpleGraph.compl_adj _ _ _).mp hcompl).2 hadj

/-- One fixed endpoint is dominated by at most four centre pairs. -/
theorem exists_four_fixedEndpoint_centres
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J)) (e : Fin 2)
    (hsize : ∀ p ∈ M, T ≤ (witness (endpointAt p e)).card) :
    ∃ I : Finset M, I.card ≤ 4 ∧ ∀ p : M, p ∉ I →
      ∃ q ∈ I, K ≤
        (witness (endpointAt p.1 e) ∩ witness (endpointAt q.1 e)).card := by
  obtain ⟨I, hIcard, _hIindep, hdom⟩ :=
    exists_dominating_indep_card_le_four (fixedEndpointGraph witness M e)
      (fixedEndpointGraph_compl_cliqueFree_five witness M e hsize)
  refine ⟨I, hIcard, ?_⟩
  intro p hp
  obtain ⟨q, hq, hadj⟩ := hdom p hp
  exact ⟨q, hq, hadj.2⟩

/-- **Eight-centre two-endpoint domination.**  Outside one set of at most eight matched pairs,
both endpoints of every pair have a same-oriented `K`-overlap with an endpoint of a centre pair.
This supplies the two independent routed equations missing from one-endpoint propagation. -/
theorem exists_eight_centres_dominating_both_endpoints
    {J : Type} [DecidableEq J] (witness : J → Finset (Fin N))
    (M : Finset (J × J))
    (hsize : ∀ p ∈ M, T ≤ (witness p.1).card ∧ T ≤ (witness p.2).card) :
    ∃ C : Finset M, C.card ≤ 8 ∧ ∀ p : M, p ∉ C →
      (∃ q ∈ C, K ≤ (witness p.1.1 ∩ witness q.1.1).card) ∧
      (∃ q ∈ C, K ≤ (witness p.1.2 ∩ witness q.1.2).card) := by
  obtain ⟨I₀, hI₀card, hdom₀⟩ :=
    exists_four_fixedEndpoint_centres witness M 0 (fun p hp => by
      simpa only [endpointAt_zero] using (hsize p hp).1)
  obtain ⟨I₁, hI₁card, hdom₁⟩ :=
    exists_four_fixedEndpoint_centres witness M 1 (fun p hp => by
      simpa only [endpointAt_one] using (hsize p hp).2)
  refine ⟨I₀ ∪ I₁, (Finset.card_union_le I₀ I₁).trans
    (Nat.add_le_add hI₀card hI₁card), ?_⟩
  intro p hp
  have hp₀ : p ∉ I₀ := fun h => hp (Finset.mem_union_left I₁ h)
  have hp₁ : p ∉ I₁ := fun h => hp (Finset.mem_union_right I₀ h)
  obtain ⟨q₀, hq₀, hover₀⟩ := hdom₀ p hp₀
  obtain ⟨q₁, hq₁, hover₁⟩ := hdom₁ p hp₁
  exact ⟨⟨q₀, Finset.mem_union_left I₁ hq₀, by simpa only [endpointAt_zero] using hover₀⟩,
    ⟨q₁, Finset.mem_union_right I₀ hq₁, by simpa only [endpointAt_one] using hover₁⟩⟩

end ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

open ArkLib.ProximityGap.Frontier.P1MatchedSecantInteractionGraph

#print axioms PairInteracts.symm
#print axioms pairInteracts_iff_exists_orientation
#print axioms interactionOrientation_spec
#print axioms exists_interacting_pair_of_five
#print axioms not_five_pairwise_noninteracting
#print axioms interactionGraph_compl_cliqueFree_five
#print axioms exists_dominating_indep_card_le_four
#print axioms exists_four_interaction_centres
#print axioms exists_four_centres_with_oriented_routing
#print axioms pairInteracts_exists_crossSecant_core
#print axioms fixedEndpointGraph_compl_cliqueFree_five
#print axioms exists_four_fixedEndpoint_centres
#print axioms exists_eight_centres_dominating_both_endpoints
