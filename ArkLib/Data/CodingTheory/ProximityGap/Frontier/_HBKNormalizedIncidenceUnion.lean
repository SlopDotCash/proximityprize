/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalTopPrefix
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKRepCountMomentIdentities

/-!
# The normalized incidence union in Heath--Brown--Konyagin Lemma 5

For a multiplicative subgroup `G` and a nonzero coset representative `u`, HBK use
`C(u) = {x in G | x-u in G}` and its normalization `D(u)=u⁻¹ C(u)`.  If the representatives
belong to distinct multiplicative cosets, the sets `D(u)` are disjoint.  Consequently their union
has cardinality the sum of the corresponding additive representation counts.  This is the exact
incidence-set bridge between the ordered-prefix container and the Stepanov point-count engine.

Reference: Heath-Brown--Konyagin (2000), equations (9)--(10) and Lemma 5. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion

open scoped BigOperators
open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open HBKTransversalTopPrefix HBKTransversalRepProfile HBKRepCountMomentIdentities

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- HBK's unnormalized incidence fiber `C(u)`. -/
def incidenceFiber (G : Finset F) (u : F) : Finset F :=
  G.filter fun x => x - u ∈ G

/-- HBK's normalized fiber `D(u)=u⁻¹C(u)`, written as an image to make the bijection explicit. -/
def normalizedFiber (G : Finset F) (u : F) : Finset F :=
  (incidenceFiber G u).image fun x => u⁻¹ * x

/-- The normalized incidence set attached to a family of coset representatives. -/
def incidenceUnion (G U : Finset F) : Finset F :=
  U.biUnion (normalizedFiber G)

/-- Negation closure identifies HBK's convention `x-u∈G` with the repository convention
`u-x∈G` for `repCount`. -/
theorem incidenceFiber_card_eq_repCount
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (u : F) :
    (incidenceFiber G u).card = repCount G u := by
  congr 1
  apply Finset.filter_congr
  intro x hx
  constructor
  · intro hxu
    have := hneg (x - u) hxu
    simpa only [neg_sub] using this
  · intro hux
    have := hneg (u - x) hux
    simpa only [neg_sub] using this

/-- Scaling by a nonzero representative preserves the fiber cardinality. -/
theorem normalizedFiber_card (G : Finset F) {u : F} (hu : u ≠ 0) :
    (normalizedFiber G u).card = (incidenceFiber G u).card := by
  classical
  rw [normalizedFiber, Finset.card_image_iff.mpr]
  intro x _ y _ hxy
  apply (mul_left_cancel₀ (inv_ne_zero hu))
  exact hxy

private theorem mem_normalizedFiber_iff (G : Finset F) {u y : F} (hu : u ≠ 0) :
    y ∈ normalizedFiber G u ↔ u * y ∈ G ∧ u * y - u ∈ G := by
  classical
  rw [normalizedFiber, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Finset.mem_filter.mp hx
    simpa [hu] using hx'
  · rintro ⟨huy, huyu⟩
    refine ⟨u * y, Finset.mem_filter.mpr ⟨huy, huyu⟩, ?_⟩
    field_simp [hu]

private theorem cosetLabel_eq_of_ratio_mem {n : ℕ} (hn : 0 < n) {u v : F}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hratio : v * u⁻¹ ∈ nthRootsFinset n (1 : F)) :
    cosetLabel n u = cosetLabel n v := by
  classical
  let q := v * u⁻¹
  have hqu : q * u = v := by simp [q, hu]
  have hd : dilate q (nthRootsFinset n (1 : F)) = nthRootsFinset n (1 : F) :=
    dilate_self_eq hratio
  rw [cosetLabel, cosetLabel]
  calc
    dilate u (nthRootsFinset n (1 : F)) =
        dilate u (dilate q (nthRootsFinset n (1 : F))) := congrArg (dilate u) hd.symm
    _ = dilate (q * u) (nthRootsFinset n (1 : F)) := by
      apply Finset.ext
      intro z
      simp only [dilate, Finset.mem_image]
      constructor
      · rintro ⟨g, ⟨a, ha, hqa⟩, hzg⟩
        refine ⟨a, ha, ?_⟩
        rw [← hzg, ← hqa]
        ring
      · rintro ⟨a, ha, hza⟩
        refine ⟨q * a, ⟨a, ha, rfl⟩, ?_⟩
        rw [← hza]
        ring
    _ = dilate v (nthRootsFinset n (1 : F)) := by rw [hqu]

/-- Normalized fibers belonging to distinct transversal representatives are disjoint. -/
theorem normalizedFiber_disjoint_of_transversal
    {n : ℕ} (hn : 0 < n) {T U : Finset F} (hT : IsCosetTransversal n T)
    (hUT : U ⊆ T) {u v : F} (huU : u ∈ U) (hvU : v ∈ U) (huv : u ≠ v) :
    Disjoint (normalizedFiber (nthRootsFinset n (1 : F)) u)
      (normalizedFiber (nthRootsFinset n (1 : F)) v) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyu hyv
  have huT := hUT huU
  have hvT := hUT hvU
  have hu0 : u ≠ 0 := by
    have := hT.subset huT
    simpa using (mem_nonzeroFreqs.mp this)
  have hv0 : v ≠ 0 := by
    have := hT.subset hvT
    simpa using (mem_nonzeroFreqs.mp this)
  have hyu' := (mem_normalizedFiber_iff _ hu0).mp hyu
  have hyv' := (mem_normalizedFiber_iff _ hv0).mp hyv
  have huy0 : u * y ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hyu'.1
  have hvy0 : v * y ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hyv'.1
  have hy0 : y ≠ 0 := fun hy => huy0 (by simp [hy])
  have hratio : v * u⁻¹ ∈ nthRootsFinset n (1 : F) := by
    have hinv : (u * y)⁻¹ ∈ nthRootsFinset n (1 : F) := by
      rw [mem_nthRootsFinset hn] at hyu' ⊢
      rw [inv_pow, hyu'.1, inv_one]
    have hprod := mul_mem_nthRootsFinset hyv'.1 hinv
    rw [show v * u⁻¹ = (v * y) * (u * y)⁻¹ by field_simp [hu0, hy0]]
    simpa using hprod
  exact huv (hT.inj u huT v hvT (cosetLabel_eq_of_ratio_mem hn hu0 hv0 hratio))

/-- The HBK incidence union has cardinality equal to the sum of its representation counts. -/
theorem incidenceUnion_card_eq_sum_repCount
    {n : ℕ} (hn : 0 < n) {T U : Finset F} (hT : IsCosetTransversal n T)
    (hUT : U ⊆ T) (hneg : ∀ x ∈ nthRootsFinset n (1 : F), -x ∈ nthRootsFinset n (1 : F)) :
    (incidenceUnion (nthRootsFinset n (1 : F)) U).card =
      ∑ u ∈ U, repCount (nthRootsFinset n (1 : F)) u := by
  classical
  rw [incidenceUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [normalizedFiber_card _ (by
      have := hT.subset (hUT hu)
      exact mem_nonzeroFreqs.mp this), incidenceFiber_card_eq_repCount _ hneg]
  · intro u hu v hv huv
    exact normalizedFiber_disjoint_of_transversal hn hT hUT hu hv huv

/-- For an even-order root subgroup, the normalized incidence union over the realized top prefix
has cardinality exactly the canonical profile prefix sum. -/
theorem incidenceUnion_topPrefix_card
    {n : ℕ} (hn : 0 < n) (heven : Even n) {T : Finset F}
    (hT : IsCosetTransversal n T) {k : ℕ} (hk : k ≤ T.card) :
    (incidenceUnion (nthRootsFinset n (1 : F))
      (topPrefix (nthRootsFinset n (1 : F)) T k)).card =
      ∑ i ∈ Finset.range k, transversalRepProfile (nthRootsFinset n (1 : F)) T i := by
  rw [incidenceUnion_card_eq_sum_repCount hn hT
    (topPrefix_subset (nthRootsFinset n (1 : F)) T k)
    (fun x hx => neg_mem_nthRootsFinset_of_even hn heven hx)]
  exact sum_topPrefix_repCount _ _ hk

end ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion

#print axioms ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion.incidenceFiber_card_eq_repCount
#print axioms ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion.normalizedFiber_disjoint_of_transversal
#print axioms ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion.incidenceUnion_card_eq_sum_repCount
#print axioms ArkLib.ProximityGap.Frontier.HBKNormalizedIncidenceUnion.incidenceUnion_topPrefix_card
