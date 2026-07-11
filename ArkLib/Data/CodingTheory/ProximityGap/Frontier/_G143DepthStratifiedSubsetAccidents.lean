/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G142SubsetCollisionCancellationCore

/-!
# G143: exact depth stratification of subset-sum accidents

This file turns G142's pointwise cancellation core into an exact finite census.  For the sum map
on `r`-subsets of `G`, the G141 off-diagonal accident set partitions by the common cardinality of
`S \ T` and `T \ S`.

The zero stratum is empty, every accident has depth at most `r`, and the depth-`r` stratum is
exactly the support-disjoint equal-sum subset pairs.  Thus the literal DC excess from G140--G141
is the sum of positive cancellation-depth strata, with the final stratum matching the
fully-disjoint convention of `depthFiber`.

An important correction to the initial G143 plan is recorded by the construction: below full
depth, the map `(S,T) ↦ (S\T,T\S)` forgets the common intersection.  It is therefore not injective
without an additional intersection-multiplicity factor.  At full depth the intersection is empty,
and the canonical enumeration below gives the clean injection into `depthFiber G r r`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G141OffDiagonalAccidentIdentity
open ArkLib.ProximityGap.Frontier.G142SubsetCollisionCancellationCore
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- The finite type of `r`-subsets of `G`. -/
abbrev SubsetFamily (G : Finset F) (r : ℕ) :=
  {S : Finset F // S ∈ G.powersetCard r}

/-- Additive sum on the `r`-subset family. -/
def subsetSumMap (G : Finset F) (r : ℕ) (S : SubsetFamily G r) : F :=
  ∑ x ∈ S.1, x

/-- The literal ordered, distinct subset-sum accident census. -/
def subsetAccidents (G : Finset F) (r : ℕ) :
    Finset (SubsetFamily G r × SubsetFamily G r) :=
  offDiagonalCollisions (subsetSumMap G r)

/-- Cancellation depth of an ordered subset pair. -/
def subsetPairDepth {G : Finset F} {r : ℕ}
    (p : SubsetFamily G r × SubsetFamily G r) : ℕ :=
  (p.1.1 \ p.2.1).card

/-- Accidents of one exact cancellation depth. -/
def subsetAccidentStratum (G : Finset F) (r t : ℕ) :
    Finset (SubsetFamily G r × SubsetFamily G r) :=
  (subsetAccidents G r).filter fun p => subsetPairDepth p = t

theorem mem_subsetAccidents_iff {G : Finset F} {r : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r} :
    p ∈ subsetAccidents G r ↔
      subsetSumMap G r p.1 = subsetSumMap G r p.2 ∧ p.1 ≠ p.2 := by
  simp [subsetAccidents, offDiagonalCollisions]

theorem endpoint_card {G : Finset F} {r : ℕ} (S : SubsetFamily G r) :
    S.1.card = r :=
  (Finset.mem_powersetCard.mp S.2).2

/-- Every accident has depth in `1..r`. -/
theorem accident_depth_pos_le {G : Finset F} {r : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r} (hp : p ∈ subsetAccidents G r) :
    0 < subsetPairDepth p ∧ subsetPairDepth p ≤ r := by
  obtain ⟨hsum, hne⟩ := mem_subsetAccidents_iff.mp hp
  have hsum' : ∑ x ∈ p.1.1, x = ∑ x ∈ p.2.1, x := hsum
  have hne' : p.1.1 ≠ p.2.1 := by
    intro h
    apply hne
    exact Subtype.ext h
  have hcore := collision_cancellation_core
    (endpoint_card p.1) (endpoint_card p.2) hne' hsum'
  exact ⟨hcore.2.2.2.1, hcore.2.2.2.2.1⟩

/-- The depth-zero accident stratum is empty. -/
theorem subsetAccidentStratum_zero (G : Finset F) (r : ℕ) :
    subsetAccidentStratum G r 0 = ∅ := by
  unfold subsetAccidentStratum
  rw [Finset.filter_eq_empty_iff]
  intro p hpacc hpzero
  exact (Nat.ne_of_gt (accident_depth_pos_le hpacc).1) hpzero

/-- No accident lies above depth `r`. -/
theorem subsetAccidentStratum_eq_empty_of_lt {G : Finset F} {r t : ℕ} (hrt : r < t) :
    subsetAccidentStratum G r t = ∅ := by
  unfold subsetAccidentStratum
  rw [Finset.filter_eq_empty_iff]
  intro p hpacc hpt
  have hle := (accident_depth_pos_le hpacc).2
  omega

/-- **Exact depth partition.** The literal accident census is the sum of strata `0..r`. -/
theorem card_subsetAccidents_eq_sum_strata (G : Finset F) (r : ℕ) :
    (subsetAccidents G r).card =
      ∑ t ∈ Finset.range (r + 1), (subsetAccidentStratum G r t).card := by
  have hmaps : ∀ p ∈ subsetAccidents G r,
      subsetPairDepth p ∈ Finset.range (r + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (accident_depth_pos_le hp).2)
  simpa [subsetAccidentStratum] using
    (Finset.card_eq_sum_card_fiberwise
      (f := subsetPairDepth) (s := subsetAccidents G r)
      (t := Finset.range (r + 1)) hmaps)

/-- Removing the empty zero stratum gives the positive-depth form. -/
theorem card_subsetAccidents_eq_sum_positive_strata (G : Finset F) (r : ℕ) :
    (subsetAccidents G r).card =
      ∑ t ∈ Finset.Icc 1 r, (subsetAccidentStratum G r t).card := by
  rw [card_subsetAccidents_eq_sum_strata]
  have hrange : Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) := by
    ext t
    simp
    omega
  rw [hrange, Finset.sum_insert]
  · rw [subsetAccidentStratum_zero]
    simp
  · simp

/-- The full-depth stratum consists exactly of disjoint accidents. -/
theorem mem_fullDepth_stratum_iff {G : Finset F} {r : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r} :
    p ∈ subsetAccidentStratum G r r ↔
      p ∈ subsetAccidents G r ∧ Disjoint p.1.1 p.2.1 := by
  rw [subsetAccidentStratum, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hdepth⟩
    exact ⟨hp, (card_sdiff_eq_card_iff_disjoint p.1.1 p.2.1).mp
      (by simpa [subsetPairDepth, endpoint_card p.1] using hdepth)⟩
  · rintro ⟨hp, hdisj⟩
    refine ⟨hp, ?_⟩
    have h := (card_sdiff_eq_card_iff_disjoint p.1.1 p.2.1).mpr hdisj
    simpa [subsetPairDepth, endpoint_card p.1] using h

/-! ## Full-depth comparison with the ordered-word census -/

/-- Canonical enumeration of a finite set of known cardinality. -/
noncomputable def enumSubset (S : Finset F) {r : ℕ} (hS : S.card = r) : Fin r → F :=
  fun i => ((S.equivFinOfCardEq hS).symm i).1

theorem enumSubset_injective (S : Finset F) {r : ℕ} (hS : S.card = r) :
    Function.Injective (enumSubset S hS) := by
  intro i j hij
  exact (S.equivFinOfCardEq hS).symm.injective (Subtype.ext hij)

theorem enumSubset_mem (S : Finset F) {r : ℕ} (hS : S.card = r) (i : Fin r) :
    enumSubset S hS i ∈ S :=
  ((S.equivFinOfCardEq hS).symm i).2

theorem sum_enumSubset (S : Finset F) {r : ℕ} (hS : S.card = r) :
    ∑ i, enumSubset S hS i = ∑ x ∈ S, x := by
  let e : Fin r ≃ S := (S.equivFinOfCardEq hS).symm
  have h := Fintype.sum_equiv e (fun i : Fin r => enumSubset S hS i)
    (fun x : S => x.1) (fun _ => rfl)
  have hs : ∑ x ∈ S, x = ∑ x : S, x.1 :=
    Finset.sum_subtype S (fun _ => Iff.rfl) (fun x => x)
  exact h.trans hs.symm

theorem valueBag_enumSubset_toFinset (S : Finset F) {r : ℕ} (hS : S.card = r) :
    (valueBag (enumSubset S hS)).toFinset = S := by
  ext x
  constructor
  · intro hx
    rw [Multiset.mem_toFinset] at hx
    change x ∈ List.ofFn (enumSubset S hS) at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact enumSubset_mem S hS i
  · intro hx
    let y : S := ⟨x, hx⟩
    let i : Fin r := S.equivFinOfCardEq hS y
    have hi : enumSubset S hS i = x := by
      change ((S.equivFinOfCardEq hS).symm (S.equivFinOfCardEq hS y)).1 = x
      simp [y]
    rw [Multiset.mem_toFinset]
    change x ∈ List.ofFn (enumSubset S hS)
    rw [List.mem_ofFn]
    exact ⟨i, hi⟩

/-- Canonical ordered endpoints attached to a subset pair. -/
noncomputable def enumPair {G : Finset F} {r : ℕ}
    (p : SubsetFamily G r × SubsetFamily G r) :
    (Fin r → F) × (Fin r → F) :=
  (enumSubset p.1.1 (endpoint_card p.1), enumSubset p.2.1 (endpoint_card p.2))

/-- Canonical enumeration sends every full-depth subset accident into the existing full-depth
ordered-word fiber. -/
theorem enumPair_maps_fullDepth {G : Finset F} {r : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r r) :
    enumPair p ∈ (energySet G r).filter (fun q => cancelDepth q = r) := by
  obtain ⟨hpacc, hdisj⟩ := mem_fullDepth_stratum_iff.mp hp
  obtain ⟨hsum, -⟩ := mem_subsetAccidents_iff.mp hpacc
  have hSsub : p.1.1 ⊆ G := (Finset.mem_powersetCard.mp p.1.2).1
  have hTsub : p.2.1 ⊆ G := (Finset.mem_powersetCard.mp p.2.2).1
  have haG : (enumPair p).1 ∈ Fintype.piFinset (fun _ : Fin r => G) := by
    rw [Fintype.mem_piFinset]
    intro i
    exact hSsub (enumSubset_mem p.1.1 (endpoint_card p.1) i)
  have hbG : (enumPair p).2 ∈ Fintype.piFinset (fun _ : Fin r => G) := by
    rw [Fintype.mem_piFinset]
    intro i
    exact hTsub (enumSubset_mem p.2.1 (endpoint_card p.2) i)
  have hsums : ∑ i, (enumPair p).1 i = ∑ i, (enumPair p).2 i := by
    rw [enumPair, sum_enumSubset, sum_enumSubset]
    exact hsum
  have hbagdisj : Disjoint (valueBag (enumPair p).1) (valueBag (enumPair p).2) := by
    rw [Multiset.disjoint_iff_ne]
    intro x hx y hy hxy
    have hxS : x ∈ p.1.1 := by
      have hx' : x ∈ (valueBag (enumPair p).1).toFinset := Multiset.mem_toFinset.mpr hx
      simpa [enumPair, valueBag_enumSubset_toFinset] using hx'
    have hyT : x ∈ p.2.1 := by
      have hy' : x ∈ (valueBag (enumPair p).2).toFinset :=
        Multiset.mem_toFinset.mpr (hxy ▸ hy)
      simpa [enumPair, valueBag_enumSubset_toFinset] using hy'
    exact (Finset.disjoint_left.mp hdisj) hxS hyT
  rw [Finset.mem_filter]
  refine ⟨?_, (cancelDepth_eq_length_iff_disjoint _ _).mpr hbagdisj⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haG, hbG⟩, hsums⟩

theorem enumPair_injOn_fullDepth (G : Finset F) (r : ℕ) :
    Set.InjOn enumPair (↑(subsetAccidentStratum G r r) :
      Set (SubsetFamily G r × SubsetFamily G r)) := by
  intro p hp q hq heq
  apply Prod.ext
  · apply Subtype.ext
    have hfun : (enumPair p).1 = (enumPair q).1 := congrArg Prod.fst heq
    have hbag := congrArg (fun a => (valueBag a).toFinset) hfun
    simpa [enumPair, valueBag_enumSubset_toFinset] using hbag
  · apply Subtype.ext
    have hfun : (enumPair p).2 = (enumPair q).2 := congrArg Prod.snd heq
    have hbag := congrArg (fun a => (valueBag a).toFinset) hfun
    simpa [enumPair, valueBag_enumSubset_toFinset] using hbag

/-- **Full-depth enumerative weld.** The full-depth subset accident census injects into the
existing ordered-word `depthFiber`.  The stronger factorial-squared equality follows by counting
all endpoint orderings; this canonical form is the injection needed by downstream upper bounds. -/
theorem fullDepth_subsetAccidents_le_depthFiber (G : Finset F) (r : ℕ) :
    (subsetAccidentStratum G r r).card ≤ depthFiber G r r := by
  unfold depthFiber
  exact Finset.card_le_card_of_injOn enumPair
    (fun _ hp => enumPair_maps_fullDepth hp)
    (enumPair_injOn_fullDepth G r)

#print axioms accident_depth_pos_le
#print axioms subsetAccidentStratum_zero
#print axioms subsetAccidentStratum_eq_empty_of_lt
#print axioms card_subsetAccidents_eq_sum_strata
#print axioms card_subsetAccidents_eq_sum_positive_strata
#print axioms mem_fullDepth_stratum_iff
#print axioms sum_enumSubset
#print axioms valueBag_enumSubset_toFinset
#print axioms enumPair_maps_fullDepth
#print axioms enumPair_injOn_fullDepth
#print axioms fullDepth_subsetAccidents_le_depthFiber

end ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
