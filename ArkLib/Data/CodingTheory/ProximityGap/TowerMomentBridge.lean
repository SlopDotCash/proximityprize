/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentSupplyIdentity
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardSumZero

/-!
# Wiring the tower-word orchard count into the moment–supply machine (#389)

`MomentSupplyIdentity.lean` proves the general binomial-moment identity (`moment_supply_identity`):
for any word `w` and `j ≥ k`, the `j`-th binomial moment of the agreement spectrum equals the
degenerate-`j`-set count,
`∑_c C(a_c, j) = #{j-subsets S : w|_S extends to a degree-<k polynomial}`.

`GeneralOrchardSumZero.lean` proves the polynomial orchard "iff": a degree-`<k` polynomial agrees
with `x^{k+1}` on a `(k+1)`-subset `T` **iff** `∑ T = 0`.

This file welds them: for the **tower word `x^{k+1}`**, the degenerate-`(k+1)`-sets are *exactly*
the zero-sum `(k+1)`-subsets, so the moment machine consumes an exact combinatorial input.

* **`tower_degenerateSets_eq`** — `degenerateSets dom k (k+1) x^{k+1}` = the zero-sum-`(k+1)`-
  subsets of the domain.
* **`tower_moment_eq_zeroSum`** — `∑_c C(agreement(c, x^{k+1}), k+1) = #{zero-sum (k+1)-subsets}`.

This is the bridge between the agreement-spectrum (list-decoding) side that the second-moment
machinery uses and the zero-sum-subset (additive-combinatorics) side that the even- and
odd-tower growth bounds (`EvenTowerSupplyGrowth`, `CubicCosetSupplyGrowth`) control:
the `(k+1)`-th moment of the tower word *is* the zero-sum count, exactly, for any RS domain.
Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- For a `(k+1)`-subset `S`, the tower word `x^{k+1}` is explainable on `S` **iff** the domain
values of `S` sum to zero — the orchard "iff" pulled back through the domain embedding. -/
theorem tower_explainable_iff (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (hS : S.card = k + 1) :
    ExplainableOn dom k (fun i => (dom i) ^ (k + 1)) S ↔ ∑ i ∈ S, dom i = 0 := by
  classical
  have hTcard : (S.image dom).card = k + 1 := by
    rw [Finset.card_image_of_injective _ dom.injective, hS]
  have hsum : ∑ a ∈ S.image dom, a = ∑ i ∈ S, dom i :=
    Finset.sum_image (fun i _ j _ h => dom.injective h)
  constructor
  · rintro ⟨c, ⟨P, hPdeg, rfl⟩, hagree⟩
    have hP : ∀ a ∈ S.image dom, P.eval a = a ^ (k + 1) := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact hagree i hi
    have hzero := ProximityGap.GeneralOrchard.sum_eq_zero_of_agree P hk hPdeg (S.image dom)
      hTcard hP
    rwa [hsum] at hzero
  · intro hzero
    obtain ⟨P, hPdeg, hP⟩ := ProximityGap.GeneralOrchard.exists_agree_of_sum_zero (S.image dom)
      hTcard (by rw [hsum]; exact hzero)
    exact ⟨fun i => P.eval (dom i), ⟨P, hPdeg, rfl⟩,
      fun i hi => hP (dom i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩

open Classical in
/-- **The tower word's degenerate-`(k+1)`-sets are exactly the zero-sum `(k+1)`-subsets.** -/
theorem tower_degenerateSets_eq (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    degenerateSets dom k (k + 1) (fun i => (dom i) ^ (k + 1))
      = ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
          (fun S => ∑ i ∈ S, dom i = 0) := by
  classical
  unfold degenerateSets
  apply Finset.filter_congr
  intro S hS
  obtain ⟨-, hScard⟩ := Finset.mem_powersetCard.mp hS
  exact tower_explainable_iff dom hk hScard

open Classical in
/-- **The tower-word moment identity.**  The `(k+1)`-th binomial moment of the agreement
spectrum of `x^{k+1}` equals the zero-sum-`(k+1)`-subset count of the domain — the moment
machine's input, supplied exactly by the orchard combinatorics. -/
theorem tower_moment_eq_zeroSum (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    ∑ c ∈ codewordFinset dom k,
        ((agreeSet c (fun i => (dom i) ^ (k + 1))).card.choose (k + 1))
      = (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
          (fun S => ∑ i ∈ S, dom i = 0)).card := by
  rw [moment_supply_identity dom (Nat.le_succ k) (fun i => (dom i) ^ (k + 1)),
    tower_degenerateSets_eq dom hk]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.tower_explainable_iff
#print axioms ProximityGap.PairRank.tower_degenerateSets_eq
#print axioms ProximityGap.PairRank.tower_moment_eq_zeroSum
