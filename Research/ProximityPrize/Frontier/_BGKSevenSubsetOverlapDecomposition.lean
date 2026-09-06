/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Exact overlap cancellation for seven-subset sum collisions

An ordered pair of `k`-subsets `(A,B)` with equal sum has a canonical sunflower decomposition

`A = X ∪ C`, `B = Y ∪ C`,

where `C=A∩B`, `X=A\B`, and `Y=B\A`.  The petals `X,Y` are disjoint, have the same cardinality
`r`, and have equal sum.  Conversely, a disjoint equal-sum petal pair of size `r` can be completed
by any `(k-r)`-subset of `G \ (X∪Y)`.  There are exactly

`choose (|G|-2r) (k-r)`

such cores.  Consequently

`subsetCollisionCount(G,k)
  = sum_{r=0}^k choose(|G|-2r,k-r) * disjointCollisionCount(G,r)`.

At `k=7`, the `r=7` coefficient is one.  Thus the overlap strata `|A∩B|≥1` are exactly the
depths `r≤6`, while the sole residual term is the globally-disjoint depth-seven sector.  This is
an exact reparametrization: it does not itself bound any disjoint collision count.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKSevenSubsetOverlapDecomposition

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- Ordered equal-sum pairs of `k`-subsets of `G`. -/
noncomputable def subsetCollisionPairs (G : Finset α) (k : Nat) :
    Finset (Finset α × Finset α) :=
  (G.powersetCard k ×ˢ G.powersetCard k).filter fun p =>
    (∑ x ∈ p.1, x) = ∑ x ∈ p.2, x

/-- Collision pairs whose two sides differ in exactly `r` elements. -/
noncomputable def overlapStratumPairs (G : Finset α) (k r : Nat) :
    Finset (Finset α × Finset α) :=
  (subsetCollisionPairs G k).filter fun p => (p.1 \ p.2).card = r

/-- Ordered disjoint equal-sum pairs of `r`-subsets of `G`. -/
noncomputable def disjointCollisionPairs (G : Finset α) (r : Nat) :
    Finset (Finset α × Finset α) :=
  (G.powersetCard r ×ˢ G.powersetCard r).filter fun p =>
    Disjoint p.1 p.2 ∧ (∑ x ∈ p.1, x) = ∑ x ∈ p.2, x

/-- Remove the common core from a pair. -/
def residualPair (p : Finset α × Finset α) : Finset α × Finset α :=
  (p.1 \ p.2, p.2 \ p.1)

/-- Common core of a pair. -/
def pairCore (p : Finset α × Finset α) : Finset α := p.1 ∩ p.2

/-- Adjoin the same core to both petals. -/
def completePair (p : Finset α × Finset α) (C : Finset α) :
    Finset α × Finset α :=
  (p.1 ∪ C, p.2 ∪ C)

/-- Completions of a fixed petal pair by a common core. -/
noncomputable def coreChoices (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) : Finset (Finset α) :=
  (G \ (p.1 ∪ p.2)).powersetCard (k - r)

/-- The fiber of the residual-pair map over one disjoint petal pair. -/
noncomputable def completionFiber (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) : Finset (Finset α × Finset α) :=
  (overlapStratumPairs G k r).filter fun z => residualPair z = p

/-! ## Core cancellation -/

/-- Cancelling the common intersection preserves equality of sums. -/
theorem sum_sdiff_eq_of_sum_eq (A B : Finset α)
    (h : (∑ x ∈ A, x) = ∑ x ∈ B, x) :
    (∑ x ∈ A \ B, x) = ∑ x ∈ B \ A, x := by
  have hA : (∑ x ∈ A, x) = (∑ x ∈ A ∩ B, x) + ∑ x ∈ A \ B, x := by
    rw [Finset.sum_inter_add_sum_diff A B]
  have hB : (∑ x ∈ B, x) = (∑ x ∈ B ∩ A, x) + ∑ x ∈ B \ A, x := by
    rw [Finset.sum_inter_add_sum_diff B A]
  rw [Finset.inter_comm B A] at hB
  rw [hA, hB] at h
  exact add_left_cancel h

/-- Equal-size sets have equal-size residual petals. -/
theorem card_sdiff_eq_of_card_eq (A B : Finset α) (h : A.card = B.card) :
    (A \ B).card = (B \ A).card := by
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  omega

/-- A residual petal cannot be larger than the original subset. -/
theorem card_sdiff_le_of_mem_subsetCollisionPairs {G : Finset α} {k : Nat}
    {p : Finset α × Finset α} (hp : p ∈ subsetCollisionPairs G k) :
    (p.1 \ p.2).card ≤ k := by
  classical
  rw [subsetCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
  obtain ⟨⟨⟨_hAsub, hAcard⟩, _hBsub, _hBcard⟩, _hsum⟩ := hp
  have hle : (p.1 \ p.2).card ≤ p.1.card :=
    Finset.card_le_card Finset.sdiff_subset
  omega

/-- Every overlap-stratum pair maps to a disjoint equal-sum petal pair. -/
theorem residualPair_mem_disjointCollisionPairs {G : Finset α} {k r : Nat}
    {z : Finset α × Finset α} (hz : z ∈ overlapStratumPairs G k r) :
    residualPair z ∈ disjointCollisionPairs G r := by
  classical
  rw [overlapStratumPairs, Finset.mem_filter, subsetCollisionPairs,
    Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
    Finset.mem_powersetCard] at hz
  obtain ⟨⟨⟨⟨hAsub, hAcard⟩, hBsub, hBcard⟩, hsum⟩, hr⟩ := hz
  have hrcard : (z.2 \ z.1).card = r := by
    rw [← hr]
    exact (card_sdiff_eq_of_card_eq z.1 z.2 (by rw [hAcard, hBcard])).symm
  rw [disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard]
  exact ⟨
    ⟨⟨Finset.sdiff_subset.trans hAsub, hr⟩,
      Finset.sdiff_subset.trans hBsub, hrcard⟩,
    disjoint_sdiff_sdiff,
    sum_sdiff_eq_of_sum_eq z.1 z.2 hsum⟩

/-- The common core of a collision pair is a legal completion of its residual petals. -/
theorem inter_mem_coreChoices {G : Finset α} {k r : Nat}
    {z : Finset α × Finset α} (hz : z ∈ overlapStratumPairs G k r) :
    z.1 ∩ z.2 ∈ coreChoices G k r (residualPair z) := by
  classical
  rw [overlapStratumPairs, Finset.mem_filter, subsetCollisionPairs,
    Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
    Finset.mem_powersetCard] at hz
  obtain ⟨⟨⟨⟨hAsub, hAcard⟩, hBsub, hBcard⟩, _hsum⟩, hr⟩ := hz
  rw [coreChoices, Finset.mem_powersetCard]
  constructor
  · intro x hx
    have hxAB := Finset.mem_inter.mp hx
    rw [Finset.mem_sdiff]
    refine ⟨hAsub hxAB.1, ?_⟩
    intro hxres
    rcases Finset.mem_union.mp hxres with hxleft | hxright
    · exact (Finset.mem_sdiff.mp hxleft).2 hxAB.2
    · exact (Finset.mem_sdiff.mp hxright).2 hxAB.1
  · have hsplit := Finset.card_sdiff_add_card_inter z.1 z.2
    omega

/-- A pair is recovered from its residual petals and common core. -/
theorem completePair_pairCore_eq_of_residualPair_eq
    (z p : Finset α × Finset α) (hres : residualPair z = p) :
    completePair p (pairCore z) = z := by
  have hA : (residualPair z).1 ∪ pairCore z = z.1 := by
    ext x
    simp [residualPair, pairCore]
    tauto
  have hB : (residualPair z).2 ∪ pairCore z = z.2 := by
    ext x
    simp [residualPair, pairCore]
    tauto
  rw [hres] at hA hB
  exact Prod.ext_iff.mpr ⟨hA, hB⟩

/-- Pairwise-disjoint petals and core have exactly the prescribed common intersection. -/
theorem pairCore_completePair_eq (p : Finset α × Finset α) (C : Finset α)
    (hXY : Disjoint p.1 p.2) (hXC : Disjoint p.1 C) (hYC : Disjoint p.2 C) :
    pairCore (completePair p C) = C := by
  ext x
  simp only [pairCore, completePair, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hxX | hxC, hxY | hxC'⟩
    · exact False.elim ((Finset.disjoint_left.mp hXY) hxX hxY)
    · exact hxC'
    · exact hxC
    · exact hxC
  · intro hxC
    exact ⟨Or.inr hxC, Or.inr hxC⟩

/-! ## Fixed-petal completion fiber -/

/-- Take the common core of a pair in one fixed residual fiber. -/
noncomputable def completionFiberToCore (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (z : {z // z ∈ completionFiber G k r p}) :
    {C // C ∈ coreChoices G k r p} := by
  have hz := (Finset.mem_filter.mp z.2).1
  have hres := (Finset.mem_filter.mp z.2).2
  refine ⟨pairCore z.1, ?_⟩
  have hcore := inter_mem_coreChoices hz
  change pairCore z.1 ∈ coreChoices G k r (residualPair z.1) at hcore
  rwa [hres] at hcore

/-- Complete fixed disjoint petals by one legal common core. -/
noncomputable def coreToCompletion (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (hp : p ∈ disjointCollisionPairs G r) (hrk : r ≤ k)
    (C : {C // C ∈ coreChoices G k r p}) :
    {z // z ∈ completionFiber G k r p} := ⟨completePair p C.1, by
  classical
  rw [disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
  obtain ⟨⟨⟨hXsub, hXcard⟩, hYsub, hYcard⟩, hXY, hsum⟩ := hp
  have hCmem : C.1 ∈ (G \ (p.1 ∪ p.2)).powersetCard (k - r) := C.2
  rw [Finset.mem_powersetCard] at hCmem
  obtain ⟨hCsub, hCcard⟩ := hCmem
  have hCsubG : C.1 ⊆ G := fun _ hx => (Finset.mem_sdiff.mp (hCsub hx)).1
  have hXC : Disjoint p.1 C.1 := by
    rw [Finset.disjoint_left]
    intro x hxX hxC
    exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (Finset.mem_union_left _ hxX)
  have hYC : Disjoint p.2 C.1 := by
    rw [Finset.disjoint_left]
    intro x hxY hxC
    exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (Finset.mem_union_right _ hxY)
  let A := (completePair p C.1).1
  let B := (completePair p C.1).2
  have hAcard : A.card = k := by
    dsimp [A, completePair]
    rw [Finset.card_union_of_disjoint hXC, hXcard, hCcard]
    omega
  have hBcard : B.card = k := by
    dsimp [B, completePair]
    rw [Finset.card_union_of_disjoint hYC, hYcard, hCcard]
    omega
  have hsumAB : (∑ x ∈ A, x) = ∑ x ∈ B, x := by
    dsimp [A, B, completePair]
    rw [Finset.sum_union hXC, Finset.sum_union hYC, hsum]
  have hleft : A \ B = p.1 := by
    ext x
    simp only [A, B, completePair, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxX | hxC, hnot⟩
      · exact hxX
      · exact False.elim (hnot (Or.inr hxC))
    · intro hxX
      refine ⟨Or.inl hxX, ?_⟩
      intro hx
      rcases hx with hxY | hxC
      · exact (Finset.disjoint_left.mp hXY) hxX hxY
      · exact (Finset.disjoint_left.mp hXC) hxX hxC
  have hright : B \ A = p.2 := by
    ext x
    simp only [A, B, completePair, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxY | hxC, hnot⟩
      · exact hxY
      · exact False.elim (hnot (Or.inr hxC))
    · intro hxY
      refine ⟨Or.inl hxY, ?_⟩
      intro hx
      rcases hx with hxX | hxC
      · exact (Finset.disjoint_left.mp hXY) hxX hxY
      · exact (Finset.disjoint_left.mp hYC) hxY hxC
  change (A, B) ∈ completionFiber G k r p
  rw [completionFiber, Finset.mem_filter]
  constructor
  · rw [overlapStratumPairs, Finset.mem_filter, subsetCollisionPairs,
      Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
      Finset.mem_powersetCard]
    exact ⟨
      ⟨
        ⟨⟨Finset.union_subset hXsub hCsubG, hAcard⟩,
          Finset.union_subset hYsub hCsubG, hBcard⟩,
        hsumAB⟩,
      by rw [hleft, hXcard]⟩
  · exact Prod.ext hleft hright⟩

@[simp]
theorem completionFiberToCore_val (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (z : {z // z ∈ completionFiber G k r p}) :
    (completionFiberToCore G k r p z).1 = pairCore z.1 := by
  rfl

@[simp]
theorem coreToCompletion_val (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (hp : p ∈ disjointCollisionPairs G r) (hrk : r ≤ k)
    (C : {C // C ∈ coreChoices G k r p}) :
    (coreToCompletion G k r p hp hrk C).1 = completePair p C.1 := by
  rfl

/-- For fixed disjoint petals, taking the common intersection is a bijection from overlap
collisions in that residual fiber to legal common cores. -/
noncomputable def completionFiberEquivCoreChoices (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (hp : p ∈ disjointCollisionPairs G r) (hrk : r ≤ k) :
    {z // z ∈ completionFiber G k r p} ≃ {C // C ∈ coreChoices G k r p} where
  toFun := completionFiberToCore G k r p
  invFun := coreToCompletion G k r p hp hrk
  left_inv z := by
    apply Subtype.ext
    rw [coreToCompletion_val, completionFiberToCore_val]
    exact completePair_pairCore_eq_of_residualPair_eq z.1 p
      (Finset.mem_filter.mp z.2).2
  right_inv C := by
    apply Subtype.ext
    rw [completionFiberToCore_val, coreToCompletion_val]
    rw [disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    obtain ⟨⟨⟨_hXsub, _hXcard⟩, _hYsub, _hYcard⟩, hXY, _hsum⟩ := hp
    have hCmem : C.1 ∈ (G \ (p.1 ∪ p.2)).powersetCard (k - r) := C.2
    rw [Finset.mem_powersetCard] at hCmem
    obtain ⟨hCsub, _hCcard⟩ := hCmem
    have hXC : Disjoint p.1 C.1 := by
      rw [Finset.disjoint_left]
      intro x hxX hxC
      exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (Finset.mem_union_left _ hxX)
    have hYC : Disjoint p.2 C.1 := by
      rw [Finset.disjoint_left]
      intro x hxY hxC
      exact (Finset.mem_sdiff.mp (hCsub hxC)).2 (Finset.mem_union_right _ hxY)
    exact pairCore_completePair_eq p C.1 hXY hXC hYC

/-- Every completion fiber has the expected binomial cardinality. -/
theorem card_completionFiber (G : Finset α) (k r : Nat)
    (p : Finset α × Finset α) (hp : p ∈ disjointCollisionPairs G r) (hrk : r ≤ k) :
    (completionFiber G k r p).card = (G.card - 2 * r).choose (k - r) := by
  classical
  rw [← Fintype.card_coe,
    Fintype.card_congr (completionFiberEquivCoreChoices G k r p hp hrk),
    Fintype.card_coe, coreChoices, Finset.card_powersetCard]
  rw [disjointCollisionPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
  obtain ⟨⟨⟨hXsub, hXcard⟩, hYsub, hYcard⟩, hXY, _hsum⟩ := hp
  have hUsub : p.1 ∪ p.2 ⊆ G := Finset.union_subset hXsub hYsub
  have hUcard : (p.1 ∪ p.2).card = 2 * r := by
    rw [Finset.card_union_of_disjoint hXY, hXcard, hYcard]
    omega
  have hcomp : (G \ (p.1 ∪ p.2)).card = G.card - 2 * r := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUsub, hUcard]
  rw [hcomp]

/-! ## Exact stratum and total identities -/

/-- One overlap stratum is a constant-size completion bundle over disjoint petals. -/
theorem card_overlapStratumPairs (G : Finset α) (k r : Nat) (hrk : r ≤ k) :
    (overlapStratumPairs G k r).card =
      (disjointCollisionPairs G r).card * (G.card - 2 * r).choose (k - r) := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := overlapStratumPairs G k r)
    (t := disjointCollisionPairs G r)
    (f := residualPair)
    (fun z hz => residualPair_mem_disjointCollisionPairs hz)
  rw [hpart]
  calc
    (∑ p ∈ disjointCollisionPairs G r,
        ((overlapStratumPairs G k r).filter fun z => residualPair z = p).card) =
        ∑ _p ∈ disjointCollisionPairs G r,
          (G.card - 2 * r).choose (k - r) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_completionFiber G k r p hp hrk
    _ = (disjointCollisionPairs G r).card *
        (G.card - 2 * r).choose (k - r) := by simp

/-- Collision pairs are the disjoint union of their residual-cardinality strata. -/
theorem card_subsetCollisionPairs_eq_sum_strata (G : Finset α) (k : Nat) :
    (subsetCollisionPairs G k).card =
      ∑ r ∈ Finset.range (k + 1), (overlapStratumPairs G k r).card := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := subsetCollisionPairs G k)
    (t := Finset.range (k + 1))
    (f := fun p => (p.1 \ p.2).card)
    (fun p hp => by
      apply Finset.mem_range.mpr
      have hle := card_sdiff_le_of_mem_subsetCollisionPairs hp
      exact Nat.lt_succ_of_le hle)
  simpa [overlapStratumPairs] using hpart

/-- **General overlap-cancellation identity.** -/
theorem card_subsetCollisionPairs_eq_sum_disjoint (G : Finset α) (k : Nat) :
    (subsetCollisionPairs G k).card =
      ∑ r ∈ Finset.range (k + 1),
        (disjointCollisionPairs G r).card * (G.card - 2 * r).choose (k - r) := by
  rw [card_subsetCollisionPairs_eq_sum_strata]
  apply Finset.sum_congr rfl
  intro r hr
  exact card_overlapStratumPairs G k r (by
    rw [Finset.mem_range] at hr
    omega)

/-- **Depth-seven specialization.**  The `r=7` coefficient is exactly one; all overlap strata are
the depths `r≤6`, and the last summand is the globally-disjoint depth-seven collision sector. -/
theorem card_sevenSubsetCollisionPairs_eq_overlap_plus_primitive (G : Finset α) :
    (subsetCollisionPairs G 7).card =
      (∑ r ∈ Finset.range 7,
        (disjointCollisionPairs G r).card * (G.card - 2 * r).choose (7 - r)) +
      (disjointCollisionPairs G 7).card := by
  rw [card_subsetCollisionPairs_eq_sum_disjoint]
  rw [Finset.sum_range_succ]
  simp

/-! ## Characteristic-zero lift marker: the wraparound decomposition -/

section LiftMarker

variable {β : Type*} [AddCommGroup β] [DecidableEq β]

/-- Signed value of a pair through an auxiliary additive label.  For the FS11 application this is
the characteristic-zero cyclotomic lift. -/
def signedPairLabel (lift : α → β) (p : Finset α × Finset α) : β :=
  (∑ x ∈ p.1, lift x) - ∑ x ∈ p.2, lift x

/-- Cancelling a common core preserves every additive signed label. -/
theorem signedPairLabel_residualPair (lift : α → β)
    (p : Finset α × Finset α) :
    signedPairLabel lift (residualPair p) = signedPairLabel lift p := by
  have hA : (∑ x ∈ p.1, lift x) =
      (∑ x ∈ p.1 ∩ p.2, lift x) + ∑ x ∈ p.1 \ p.2, lift x := by
    rw [Finset.sum_inter_add_sum_diff p.1 p.2]
  have hB : (∑ x ∈ p.2, lift x) =
      (∑ x ∈ p.2 ∩ p.1, lift x) + ∑ x ∈ p.2 \ p.1, lift x := by
    rw [Finset.sum_inter_add_sum_diff p.2 p.1]
  rw [Finset.inter_comm p.2 p.1] at hB
  unfold signedPairLabel residualPair
  rw [hA, hB]
  abel

/-- Equal-sum collisions whose auxiliary signed lift is nonzero. -/
noncomputable def markedCollisionPairs (G : Finset α) (k : Nat) (lift : α → β) :
    Finset (Finset α × Finset α) :=
  (subsetCollisionPairs G k).filter fun p => signedPairLabel lift p ≠ 0

/-- Marked collision pairs in residual-cardinality stratum `r`. -/
noncomputable def markedOverlapStratumPairs (G : Finset α) (k r : Nat)
    (lift : α → β) : Finset (Finset α × Finset α) :=
  (overlapStratumPairs G k r).filter fun p => signedPairLabel lift p ≠ 0

/-- Disjoint equal-sum petals carrying a nonzero auxiliary label. -/
noncomputable def markedDisjointCollisionPairs (G : Finset α) (r : Nat)
    (lift : α → β) : Finset (Finset α × Finset α) :=
  (disjointCollisionPairs G r).filter fun p => signedPairLabel lift p ≠ 0

/-- Completion fiber inside the marked overlap stratum. -/
noncomputable def markedCompletionFiber (G : Finset α) (k r : Nat)
    (lift : α → β) (p : Finset α × Finset α) :
    Finset (Finset α × Finset α) :=
  (markedOverlapStratumPairs G k r lift).filter fun z => residualPair z = p

theorem card_sdiff_le_of_mem_markedCollisionPairs
    {G : Finset α} {k : Nat} {lift : α → β} {p : Finset α × Finset α}
    (hp : p ∈ markedCollisionPairs G k lift) :
    (p.1 \ p.2).card ≤ k := by
  rw [markedCollisionPairs, Finset.mem_filter] at hp
  exact card_sdiff_le_of_mem_subsetCollisionPairs hp.1

/-- A marked overlap pair maps to a marked disjoint petal pair. -/
theorem residualPair_mem_markedDisjointCollisionPairs
    {G : Finset α} {k r : Nat} {lift : α → β}
    {z : Finset α × Finset α} (hz : z ∈ markedOverlapStratumPairs G k r lift) :
    residualPair z ∈ markedDisjointCollisionPairs G r lift := by
  rw [markedOverlapStratumPairs, Finset.mem_filter] at hz
  rw [markedDisjointCollisionPairs, Finset.mem_filter]
  refine ⟨residualPair_mem_disjointCollisionPairs hz.1, ?_⟩
  rw [signedPairLabel_residualPair]
  exact hz.2

/-- Over a marked petal pair, every legal common core remains marked, so the marked completion
fiber is the entire completion fiber. -/
theorem markedCompletionFiber_eq_completionFiber
    (G : Finset α) (k r : Nat) (lift : α → β)
    (p : Finset α × Finset α) (hp : p ∈ markedDisjointCollisionPairs G r lift) :
    markedCompletionFiber G k r lift p = completionFiber G k r p := by
  rw [markedDisjointCollisionPairs, Finset.mem_filter] at hp
  ext z
  simp only [markedCompletionFiber, markedOverlapStratumPairs, completionFiber,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hz, _hlabel⟩, hres⟩
    exact ⟨hz, hres⟩
  · rintro ⟨hz, hres⟩
    refine ⟨⟨hz, ?_⟩, hres⟩
    have hlabel := signedPairLabel_residualPair lift z
    rw [hres] at hlabel
    intro hzero
    apply hp.2
    exact hlabel.trans hzero

/-- A marked completion fiber has the same binomial cardinality. -/
theorem card_markedCompletionFiber (G : Finset α) (k r : Nat) (lift : α → β)
    (p : Finset α × Finset α) (hp : p ∈ markedDisjointCollisionPairs G r lift)
    (hrk : r ≤ k) :
    (markedCompletionFiber G k r lift p).card =
      (G.card - 2 * r).choose (k - r) := by
  rw [markedCompletionFiber_eq_completionFiber G k r lift p hp]
  exact card_completionFiber G k r p (Finset.mem_filter.mp hp).1 hrk

/-- Exact marked overlap-stratum completion formula. -/
theorem card_markedOverlapStratumPairs (G : Finset α) (k r : Nat)
    (lift : α → β) (hrk : r ≤ k) :
    (markedOverlapStratumPairs G k r lift).card =
      (markedDisjointCollisionPairs G r lift).card *
        (G.card - 2 * r).choose (k - r) := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := markedOverlapStratumPairs G k r lift)
    (t := markedDisjointCollisionPairs G r lift)
    (f := residualPair)
    (fun z hz => residualPair_mem_markedDisjointCollisionPairs hz)
  rw [hpart]
  calc
    (∑ p ∈ markedDisjointCollisionPairs G r lift,
        ((markedOverlapStratumPairs G k r lift).filter
          fun z => residualPair z = p).card) =
        ∑ _p ∈ markedDisjointCollisionPairs G r lift,
          (G.card - 2 * r).choose (k - r) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_markedCompletionFiber G k r lift p hp hrk
    _ = (markedDisjointCollisionPairs G r lift).card *
        (G.card - 2 * r).choose (k - r) := by simp

/-- Marked collisions partition exactly by residual depth. -/
theorem card_markedCollisionPairs_eq_sum_strata
    (G : Finset α) (k : Nat) (lift : α → β) :
    (markedCollisionPairs G k lift).card =
      ∑ r ∈ Finset.range (k + 1),
        (markedOverlapStratumPairs G k r lift).card := by
  classical
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := markedCollisionPairs G k lift)
    (t := Finset.range (k + 1))
    (f := fun p => (p.1 \ p.2).card)
    (fun p hp => by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (card_sdiff_le_of_mem_markedCollisionPairs hp))
  simpa [markedCollisionPairs, markedOverlapStratumPairs, overlapStratumPairs,
    Finset.filter_filter, and_assoc, and_left_comm, and_comm] using hpart

/-- **Exact marked/wraparound overlap-cancellation identity.** -/
theorem card_markedCollisionPairs_eq_sum_disjoint
    (G : Finset α) (k : Nat) (lift : α → β) :
    (markedCollisionPairs G k lift).card =
      ∑ r ∈ Finset.range (k + 1),
        (markedDisjointCollisionPairs G r lift).card *
          (G.card - 2 * r).choose (k - r) := by
  rw [card_markedCollisionPairs_eq_sum_strata]
  apply Finset.sum_congr rfl
  intro r hr
  apply card_markedOverlapStratumPairs G k r lift
  rw [Finset.mem_range] at hr
  omega

/-- **Depth-seven wraparound split.**  All common-core configurations reduce to marked disjoint
petals of depth at most six; the only remaining term is the marked globally-disjoint depth-seven
sector, with coefficient one. -/
theorem card_markedSevenCollisionPairs_eq_overlap_plus_primitive
    (G : Finset α) (lift : α → β) :
    (markedCollisionPairs G 7 lift).card =
      (∑ r ∈ Finset.range 7,
        (markedDisjointCollisionPairs G r lift).card *
          (G.card - 2 * r).choose (7 - r)) +
      (markedDisjointCollisionPairs G 7 lift).card := by
  rw [card_markedCollisionPairs_eq_sum_disjoint]
  rw [Finset.sum_range_succ]
  simp

/-- Weighted contribution of all marked overlap strata at depth seven. -/
noncomputable def markedSevenOverlapContribution
    (G : Finset α) (lift : α → β) : Nat :=
  ∑ r ∈ Finset.range 7,
    (markedDisjointCollisionPairs G r lift).card *
      (G.card - 2 * r).choose (7 - r)

/-- Exact two-term socket: lower-depth marked petals plus the globally-disjoint primitive sector. -/
theorem card_markedSevenCollisionPairs_eq_lowerDepth_plus_primitive
    (G : Finset α) (lift : α → β) :
    (markedCollisionPairs G 7 lift).card =
      markedSevenOverlapContribution G lift +
        (markedDisjointCollisionPairs G 7 lift).card := by
  exact card_markedSevenCollisionPairs_eq_overlap_plus_primitive G lift

/-- **Honest target equivalence.**  Existing depth-at-most-six estimates control all common-core
strata exactly when they bound `markedSevenOverlapContribution`; after that, and only after that,
the remaining obligation is the globally-disjoint marked depth-seven count. -/
theorem markedSeven_target_iff_lowerDepth_plus_primitive
    (G : Finset α) (lift : α → β) (target : Nat) :
    (markedCollisionPairs G 7 lift).card ≤ target ↔
      markedSevenOverlapContribution G lift +
        (markedDisjointCollisionPairs G 7 lift).card ≤ target := by
  rw [card_markedSevenCollisionPairs_eq_lowerDepth_plus_primitive]

end LiftMarker

#print axioms sum_sdiff_eq_of_sum_eq
#print axioms residualPair_mem_disjointCollisionPairs
#print axioms completionFiberEquivCoreChoices
#print axioms card_completionFiber
#print axioms card_overlapStratumPairs
#print axioms card_subsetCollisionPairs_eq_sum_disjoint
#print axioms card_sevenSubsetCollisionPairs_eq_overlap_plus_primitive
#print axioms signedPairLabel_residualPair
#print axioms card_markedCollisionPairs_eq_sum_disjoint
#print axioms card_markedSevenCollisionPairs_eq_overlap_plus_primitive
#print axioms markedSeven_target_iff_lowerDepth_plus_primitive

end ArkLib.ProximityGap.Frontier.BGKSevenSubsetOverlapDecomposition
