/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88EqualSumCorrectedDecoder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G89AllDepthWickAssembly
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy
import Mathlib.Algebra.Order.Chebyshev

/-!
# G95: raw cardinality cannot satisfy the deep budget caps — the weighting is mandatory

G89 reduced the all-depth production absorption to the per-depth budget caps.  This file proves
an unconditional **no-go**: at the production point, NO core-count function `J` can satisfy the
caps if the per-depth masses are instantiated with the *raw cardinalities* of the equal-sum
depth fibers.  Hence every future consumer of the G89 gate must instantiate `J`/`W` with
normalized (`1/p`-scale, relation-weighted) masses, as in the DC-subtracted moment — the
weighting is not a convenience but a mathematical necessity.

The engine is a Cauchy–Schwarz pigeonhole lower bound, new to the tree and upstreamable:

```text
#A^(2r) ≤ card α * addREnergy r A
```

— any `A` in a finite ambient group has `r`-fold additive energy at least `#A^(2r)/card α`.
Partitioning the energy by G83M maximal-cancellation depth and feeding the fibers through the
G89 assembly yields `#A^(2r) ≤ card α * (2r-1)!! * #A^r` whenever envelopes and caps all hold.
At the prize shape (`#A = 2^30`, `r = 110`, ambient `ZMod P` with
`P = 2^30*(2^128+192)+1 ≈ 2^158`) the left side is `2^6600` while the right side is below
`2^4157`: kernel-checked contradiction.

**Honest scope.**  This does NOT refute the padding/assembly route: it proves the route's
masses must be sub-cardinality (weighted).  It makes no claim about the weighted deep caps,
which remain the open analytic wall.  CORE remains OPEN / ON-BGK.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption
open ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly

variable {α : Type*}

/-! ## The Cauchy–Schwarz pigeonhole floor for `addREnergy` (upstreamable) -/

/-- **Pigeonhole energy floor.**  In a finite ambient monoid, the `r`-fold additive energy of
any finset `A` is at least `#A^(2r) / card α`, stated ℕ-cleanly.  Dual to the in-tree upper
bound `Finset.addREnergy_le`. -/
theorem card_pow_le_card_mul_addREnergy [Fintype α] [AddCommMonoid α] [DecidableEq α]
    (r : ℕ) (A : Finset α) :
    A.card ^ (2 * r) ≤ Fintype.card α * Finset.addREnergy r A := by
  classical
  have hpart :
      ∑ t : α, #{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}
        = #(piFinset (fun _ : Fin r => A)) :=
    (Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (∑ i, v i))).symm
  have henergy :
      Finset.addREnergy r A
        = ∑ t : α, (#{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}) ^ 2 := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := {x ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
          ∑ i, x.1 i = ∑ i, x.2 i})
      (t := (Finset.univ : Finset α)) (f := fun x => ∑ i, x.1 i)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.addREnergy_def, hfib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hset :
        ({x ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
              ∑ i, x.1 i = ∑ i, x.2 i}.filter
            fun x => ∑ i, x.1 i = t)
          = {v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t} ×ˢ
              {w ∈ piFinset (fun _ : Fin r => A) | ∑ i, w i = t} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, heq⟩, ht⟩
        exact ⟨⟨h1, ht⟩, h2, (heq.symm.trans ht)⟩
      · rintro ⟨⟨h1, ht1⟩, h2, ht2⟩
        exact ⟨⟨⟨h1, h2⟩, ht1.trans ht2.symm⟩, ht1⟩
    rw [hset, Finset.card_product, sq]
  have hcs :
      (∑ t : α, #{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}) ^ 2
        ≤ #(Finset.univ : Finset α)
            * ∑ t : α, (#{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    A.card ^ (2 * r) = (A.card ^ r) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm r 2]
    _ = (#(piFinset (fun _ : Fin r => A))) ^ 2 := by rw [card_piFinset_const]
    _ = (∑ t : α, #{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}) ^ 2 := by
      rw [hpart]
    _ ≤ #(Finset.univ : Finset α)
          * ∑ t : α, (#{v ∈ piFinset (fun _ : Fin r => A) | ∑ i, v i = t}) ^ 2 := hcs
    _ = Fintype.card α * Finset.addREnergy r A := by
      rw [Finset.card_univ, henergy]

/-! ## Partitioning the energy by maximal-cancellation depth -/

/-- The G83M maximal-cancellation depth of an ordered endpoint pair. -/
def cancelDepth [DecidableEq α] {r : ℕ} (x : (Fin r → α) × (Fin r → α)) : ℕ :=
  (leftCore (valueBag x.1) (valueBag x.2)).card

theorem cancelDepth_le [DecidableEq α] {r : ℕ} (x : (Fin r → α) × (Fin r → α)) :
    cancelDepth x ≤ r := by
  unfold cancelDepth
  calc
    (leftCore (valueBag x.1) (valueBag x.2)).card
        ≤ (valueBag x.1).card := by
      unfold leftCore
      exact Multiset.card_le_card (Multiset.sub_le_self _ _)
    _ = r := by simp [valueBag]

/-- The equal-sum pair set of `A` at length `r` (the `addREnergy` carrier). -/
def energySet [AddCommMonoid α] [DecidableEq α] (A : Finset α) (r : ℕ) :
    Finset ((Fin r → α) × (Fin r → α)) :=
  {x ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
    ∑ i, x.1 i = ∑ i, x.2 i}

theorem card_energySet [AddCommMonoid α] [DecidableEq α] (A : Finset α) (r : ℕ) :
    #(energySet A r) = Finset.addREnergy r A := rfl

/-- The cardinality of the depth-`s` slice of the equal-sum pair set. -/
def depthFiber [AddCommMonoid α] [DecidableEq α] (A : Finset α) (r s : ℕ) : ℕ :=
  #((energySet A r).filter fun x => cancelDepth x = s)

/-- **Depth partition.**  The `r`-fold additive energy decomposes exactly as the sum of the
maximal-cancellation depth fibers over `s = 0, …, r`. -/
theorem addREnergy_eq_sum_depthFiber [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (r : ℕ) :
    Finset.addREnergy r A = ∑ s ∈ Finset.range (r + 1), depthFiber A r s := by
  rw [← card_energySet]
  exact Finset.card_eq_sum_card_fiberwise
    (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (cancelDepth_le x)))

/-! ## The no-go -/

/-- **Generic energy ceiling from envelopes + caps.**  If the raw depth-fiber cardinalities fit
the factorial-corrected envelopes and every depth satisfies its G89 budget cap, then the ambient
group forces `#A^(2r) ≤ card α * (2r-1)!! * #A^r`. -/
theorem cardinality_caps_force_energy_ceiling
    [Fintype α] [AddCommMonoid α] [DecidableEq α]
    {r : ℕ} {A : Finset α} {J : ℕ → ℕ}
    (hW : ∀ s ∈ Finset.range (r + 1),
      depthFiber A r s ≤ correctedPadEnvelope A.card r (J s) s)
    (hJ : ∀ s ∈ Finset.range (r + 1), depthBudgetCap A.card r (J s) s) :
    A.card ^ (2 * r)
      ≤ Fintype.card α * (Nat.doubleFactorial (2 * r - 1) * A.card ^ r) := by
  calc
    A.card ^ (2 * r) ≤ Fintype.card α * Finset.addREnergy r A :=
      card_pow_le_card_mul_addREnergy r A
    _ = Fintype.card α * ∑ s ∈ Finset.range (r + 1), depthFiber A r s := by
      rw [addREnergy_eq_sum_depthFiber]
    _ ≤ Fintype.card α * (Nat.doubleFactorial (2 * r - 1) * A.card ^ r) :=
      Nat.mul_le_mul_left _ (allDepth_correctedSectors_le_fullWick hW hJ)

/-- **Production cardinality no-go.**  At the prize shape — alphabet of size `2^30` inside
`ZMod P` with the certified prize prime `P = 2^30*(2^128+192)+1`, depth `r = 110` — NO
core-count function `J` can make the raw depth-fiber cardinalities satisfy both the
factorial-corrected envelopes and the G89 budget caps: `2^6600` pigeonholed equal-sum pairs
cannot fit a `< 2^4157` Wick ceiling.  Every viable instantiation of the all-depth gate must
therefore use normalized sub-cardinality (relation-weighted) masses. -/
theorem production_cardinality_caps_impossible
    {A : Finset (ZMod (2 ^ 30 * (2 ^ 128 + 192) + 1))} (hA : A.card = 2 ^ 30)
    {J : ℕ → ℕ}
    (hW : ∀ s ∈ Finset.range 111,
      depthFiber A 110 s ≤ correctedPadEnvelope (2 ^ 30) 110 (J s) s) :
    ¬ (∀ s ∈ Finset.range 111, depthBudgetCap (2 ^ 30) 110 (J s) s) := by
  intro hJ
  haveI : NeZero (2 ^ 30 * (2 ^ 128 + 192) + 1) := ⟨by positivity⟩
  have hcard :
      Fintype.card (ZMod (2 ^ 30 * (2 ^ 128 + 192) + 1))
        = 2 ^ 30 * (2 ^ 128 + 192) + 1 := ZMod.card _
  have hceil := cardinality_caps_force_energy_ceiling
    (r := 110) (A := A) (J := J) (by rw [hA]; exact hW) (by rw [hA]; exact hJ)
  rw [hA, hcard] at hceil
  revert hceil
  norm_num [Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo.card_pow_le_card_mul_addREnergy
#print axioms
  ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo.cancelDepth_le
#print axioms
  ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo.addREnergy_eq_sum_depthFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo.cardinality_caps_force_energy_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo.production_cardinality_caps_impossible
