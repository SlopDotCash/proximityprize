/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96DepthMomentWeld

/-!
# G97: the fiber–sector bridge and the shallow centered discharge

Two towers now stand: the analytic tower (`depthFiber`, welded to `DCEnergyBound` by G96) and
the counting tower (the relativized G88 `MaxCancellationCollisionSector` with the injective
value map `ι`, whose corrected envelopes are kernel-affordable at shallow depths).  They did not
touch.  This file is the bridge:

1. `map_inter_of_injective` / `card_leftCore_map`: maximal-cancellation depth is invariant
   under an injective value map of the bags (count-based multiset lemmas, upstreamable).
2. `depthFiber_le_sectorCard` (**the bridge**): the depth-`s` slice of the `G`-supported
   equal-sum pair cube injects into the subgroup-alphabet collision sector
   `MaxCancellationCollisionSector {x // x ∈ G} F Subtype.val r s`.
3. `depthFiber_le_correctedPadEnvelope`: composed with the relativized G88 counting, the TRUE
   fibers consumed by G96 satisfy the `#G^(2s-1)` corrected envelope — a theorem, no longer an
   interface hypothesis (for `1 ≤ s ≤ r`).
4. `depthFiber_zero_eq` / `centered_bound_zero`: depth `0` is an identity (equal bags force
   equal sums), so its centered bound is free.
5. `production_shallow_caps_affordable`: at `(#G, r) = (2^30, 110)` the shallow envelope caps
   for depths `0–3` total under the full Wick budget (kernel-checked, ≈ `2^-25` headroom).

Together with G96's `dcEnergyBound_of_centered_depth_bounds`, the production `DCEnergyBound`
now reduces to centered per-depth bounds for `4 ≤ s ≤ 110` only, with the shallow caps
discharged by counting alone.

**Honest scope.**  The deep centered bounds remain the open analytic wall; no claim is made
about them.  CORE remains OPEN / ON-BGK.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder
open ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld

/-! ## Depth is invariant under injective value maps -/

section MultisetLemmas

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}

/-- Intersection commutes with an injective multiset map (upstreamable). -/
theorem map_inter_of_injective (hf : Function.Injective f) (M N : Multiset α) :
    (M ∩ N).map f = M.map f ∩ N.map f := by
  ext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [Multiset.count_map_eq_count' f _ hf, Multiset.count_inter,
      Multiset.count_inter, Multiset.count_map_eq_count' f _ hf,
      Multiset.count_map_eq_count' f _ hf]
  · have hnot : ∀ M' : Multiset α, b ∉ M'.map f := by
      intro M' hmem
      obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hmem
      exact hb ⟨a, ha⟩
    rw [Multiset.count_eq_zero.mpr (hnot _), Multiset.count_inter,
      Multiset.count_eq_zero.mpr (hnot M), Multiset.count_eq_zero.mpr (hnot N)]
    simp

/-- Maximal-cancellation residual depth is invariant under an injective value map. -/
theorem card_leftCore_map (hf : Function.Injective f) (M N : Multiset α) :
    (leftCore (M.map f) (N.map f)).card = (leftCore M N).card := by
  unfold leftCore commonPart
  rw [← map_inter_of_injective hf]
  rw [Multiset.card_sub (Multiset.map_le_map Multiset.inter_le_left),
    Multiset.card_sub Multiset.inter_le_left,
    Multiset.card_map, Multiset.card_map]

end MultisetLemmas

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Lifting a `G`-supported ambient word to the subgroup alphabet preserves the value bag. -/
theorem valueBag_lift (G : Finset F) {r : ℕ} (v : Fin r → F) (hv : ∀ i, v i ∈ G) :
    valueBag v =
      (valueBag (fun i => (⟨v i, hv i⟩ : {x // x ∈ G}))).map Subtype.val := by
  unfold valueBag
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

/-- **The fiber–sector bridge.**  The depth-`s` slice of the `G`-supported equal-sum pair cube
injects into the relativized collision sector over the subgroup alphabet. -/
theorem depthFiber_le_sectorCard (G : Finset F) (r s : ℕ) :
    depthFiber G r s ≤
      Fintype.card (MaxCancellationCollisionSector {x // x ∈ G} F
        (fun x => (x : F)) r s) := by
  classical
  rw [depthFiber, ← Fintype.card_coe]
  have props : ∀ y : {x // x ∈ (energySet G r).filter (fun x => cancelDepth x = s)},
      (∀ i, y.1.1 i ∈ G) ∧ (∀ i, y.1.2 i ∈ G) ∧
        (∑ i, y.1.1 i = ∑ i, y.1.2 i) ∧ cancelDepth y.1 = s := by
    intro y
    have hy := Finset.mem_filter.mp y.2
    have hmem := Finset.mem_filter.mp hy.1
    have hprod := Finset.mem_product.mp hmem.1
    exact ⟨fun i => Fintype.mem_piFinset.mp hprod.1 i,
      fun i => Fintype.mem_piFinset.mp hprod.2 i, hmem.2, hy.2⟩
  apply Fintype.card_le_of_injective (fun y =>
    ⟨(fun i => ⟨y.1.1 i, (props y).1 i⟩, fun i => ⟨y.1.2 i, (props y).2.1 i⟩),
      by
        -- depth is preserved under the injective value map
        have hdepth := (props y).2.2.2
        unfold cancelDepth at hdepth
        rw [valueBag_lift G y.1.1 (props y).1, valueBag_lift G y.1.2 (props y).2.1,
          card_leftCore_map Subtype.val_injective] at hdepth
        exact hdepth,
      by
        -- equal sums transport along the value map
        have hsum := (props y).2.2.1
        unfold wordSum
        exact hsum⟩)
  intro a b hab
  have hfst : ∀ i, a.1.1 i = b.1.1 i := fun i =>
    congrArg Subtype.val (congrFun (congrArg (fun t => t.1.1) hab) i)
  have hsnd : ∀ i, a.1.2 i = b.1.2 i := fun i =>
    congrArg Subtype.val (congrFun (congrArg (fun t => t.1.2) hab) i)
  apply Subtype.ext
  exact Prod.ext (funext hfst) (funext hsnd)

/-- **True fibers satisfy the corrected envelope.**  Composing the bridge with the relativized
G88 counting: for `1 ≤ s ≤ r`, the depth-`s` fiber consumed by G96 obeys the `#G^(2s-1)`
factorial-corrected envelope — a theorem, not an interface hypothesis. -/
theorem depthFiber_le_correctedPadEnvelope (G : Finset F) {r s : ℕ}
    (hs : 1 ≤ s) (hsr : s ≤ r) :
    depthFiber G r s ≤ correctedPadEnvelope G.card r (G.card ^ (2 * s - 1)) s := by
  refine (depthFiber_le_sectorCard G r s).trans ?_
  have h := card_collisionSector_le_factorialCorrected {x // x ∈ G} F
    (fun x => (x : F)) Subtype.val_injective r s hsr hs
  rw [Fintype.card_coe] at h
  refine h.trans (le_of_eq ?_)
  unfold correctedPadEnvelope
  ring

/-! ## Depth `0` is an identity -/

/-- Equal value bags force equal sums, so the depth-`0` collision fiber equals the depth-`0`
population fiber. -/
theorem depthFiber_zero_eq (G : Finset F) (r : ℕ) :
    depthFiber G r 0 = allPairsDepthFiber G r 0 := by
  classical
  unfold depthFiber allPairsDepthFiber energySet
  rw [Finset.filter_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _, hd⟩
    exact ⟨hx, hd⟩
  · rintro ⟨hx, hd⟩
    refine ⟨hx, ?_, hd⟩
    have hcard0 : (leftCore (valueBag x.1) (valueBag x.2)).card = 0 := hd
    have hle : valueBag x.1 ≤ valueBag x.2 := by
      have hzero : leftCore (valueBag x.1) (valueBag x.2) = 0 :=
        Multiset.card_eq_zero.mp hcard0
      have hrec := left_reconstruct (valueBag x.1) (valueBag x.2)
      rw [hzero, zero_add] at hrec
      rw [← hrec]
      unfold commonPart
      exact Multiset.inter_le_right
    have hbags : valueBag x.1 = valueBag x.2 := by
      apply Multiset.eq_of_le_of_card_le hle
      simp [valueBag]
    have hsums := congrArg Multiset.sum hbags
    simpa [valueBag, List.sum_ofFn] using hsums

/-- The depth-`0` centered bound is free: the collision fiber never exceeds its own population
allowance. -/
theorem centered_bound_zero (G : Finset F) (r cap : ℕ) :
    Fintype.card F * depthFiber G r 0
      ≤ Fintype.card F * cap + Fintype.card F * allPairsDepthFiber G r 0 := by
  rw [depthFiber_zero_eq]
  exact Nat.le_add_left _ _

/-! ## Production shallow affordability -/

/-- **The shallow caps are affordable.**  At `(#G, r) = (2^30, 110)`, the corrected envelope
caps for depths `0, 1, 2, 3` — with the depth-`0` cap the full permutation envelope and the
depth-`s` caps carrying the `#G^(2s-1)` equal-sum core counts — total under one production
Wick budget, with ≈ `2^-25` relative headroom. -/
theorem production_shallow_caps_affordable :
    correctedPadEnvelope (2 ^ 30) 110 1 0 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 1) 1 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 3) 2 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 5) 3
      ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- Depth-`0` fibers fit the permutation envelope: the fully-cancelled sector is bags-equal
pairs, bounded by the `s = 0` corrected envelope `r! · #G^r` via the G96 population count. -/
theorem depthFiber_zero_le_envelope (G : Finset F) {r : ℕ} :
    depthFiber G r 0 ≤ correctedPadEnvelope G.card r 1 0 := by
  refine (depthFiber_le_sectorCard G r 0).trans ?_
  have h := card_collisionSector_le_correctedCoreCount {x // x ∈ G} F
    (fun x => (x : F)) r 0 (Nat.zero_le r)
  rw [Fintype.card_coe] at h
  refine h.trans ?_
  unfold correctedPadEnvelope
  have hcore : Fintype.card (EqualSumCorePair {x // x ∈ G} F (fun x => (x : F)) 0) ≤ 1 := by
    have : Subsingleton (EqualSumCorePair {x // x ∈ G} F (fun x => (x : F)) 0) := by
      constructor
      intro a b
      apply Subtype.ext
      apply Prod.ext <;> funext i <;> exact absurd i.2 (Nat.not_lt_zero _)
    exact Fintype.card_le_one_iff_subsingleton.mpr this
  calc
    Fintype.card (EqualSumCorePair {x // x ∈ G} F (fun x => (x : F)) 0) *
        (r.descFactorial 0) ^ 2 * (r - 0).factorial * G.card ^ (r - 0)
        ≤ 1 * (r.descFactorial 0) ^ 2 * (r - 0).factorial * G.card ^ (r - 0) := by
      gcongr
    _ = 1 * (r.descFactorial 0) ^ 2 * (r - 0).factorial * G.card ^ (r - 0) := rfl

end ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.map_inter_of_injective
#print axioms ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.card_leftCore_map
#print axioms ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.depthFiber_le_sectorCard
#print axioms
  ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.depthFiber_le_correctedPadEnvelope
#print axioms ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.depthFiber_zero_eq
#print axioms ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.centered_bound_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.production_shallow_caps_affordable
#print axioms
  ArkLib.ProximityGap.Frontier.G97RelativizedSectorBound.depthFiber_zero_le_envelope
