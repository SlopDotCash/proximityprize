/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Round 9 (Issue #232, ABF26) — additive energy `≤ (1+M)|G|²` from a representation bound (over `F_q`).

`RootsOfUnityAdditiveEnergy` proved, in **characteristic 0**, that the roots of unity have minimal
additive energy `E ≤ 3|G|²`, via the unit-circle fact that a nonzero `s` has `≤ 2` representations
`s = y + (s−y)`. That fact uses complex conjugation and has **no finite-field analogue**. This file
isolates the *combinatorial* half — which works over **any** field, in particular `F_q` — as a clean
residual consumer:

> `additiveEnergy_le_of_repBound`: if every nonzero `t` has at most `M` representations as an ordered
> sum of two elements of `G` (`#{y∈G : t−y∈G} ≤ M`), then the additive energy is `≤ (1+M)·|G|²`.

So over the Proximity Prize's finite field `F_q`, the additive energy of the `2^k`-subgroup `G` — the
single quantity the deep-interior question was reduced to (`SubgroupGaussSumFourthMoment`:
`∑_b ‖η_b‖⁴ = q·E(G)`) — is `≤ 3|G|²` **the moment one proves the representation bound `r(t) ≤ 2`**.
That representation bound `r(t) = #{c∈G : c+t∈G} ≤ 2` for the `2^k`-subgroup over `F_q` is *exactly* the
open Weil-type / sum-product input: `c` and `c+t` both being `2^k`-th roots of unity is a curve-point
count over `F_q`, which Mathlib's elementary toolkit cannot bound (it holds for "generic" `q` but is a
genuine RH-for-curves statement). This file makes the reduction `r(t)≤M ⟹ E≤(1+M)|G|²` a theorem,
pinning the *entire* remaining gap to that one curve-point bound. All `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- The number of ordered representations `t = c + (t−c)` of `t` inside `G`. -/
def repCount (G : Finset F) (t : F) : ℕ := (G.filter (fun y => t - y ∈ G)).card

/-- The additive energy `E(G) = ∑_{a,b∈G} #{y∈G : (a+b)−y∈G} = #{(a,b,c,d)∈G⁴ : a+b = c+d}`. -/
def additiveEnergy (G : Finset F) : ℕ := ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b)

/-- The representation count of `t = 0` is at most `|G|` (the map `y ↦ −y` is injective). -/
theorem repCount_zero_le (G : Finset F) : repCount G 0 ≤ G.card :=
  Finset.card_filter_le _ _

/-- **Additive energy from a representation bound (works over any field, e.g. `F_q`).** If every
nonzero `t` has at most `M` representations as an ordered sum of two elements of `G`, then
`E(G) ≤ (1 + M)·|G|²`. For `M = 2` (the roots-of-unity / minimal-energy regime) this is `E(G) ≤ 3|G|²`. -/
theorem additiveEnergy_le_of_repBound (G : Finset F) (M : ℕ)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ M) :
    additiveEnergy G ≤ (1 + M) * G.card ^ 2 := by
  classical
  -- Bound each inner count by `if a+b = 0 then |G| else M`.
  have hbound : ∀ a ∈ G, ∀ b ∈ G, repCount G (a + b) ≤ (if a + b = 0 then G.card else M) := by
    intro a _ b _
    by_cases h0 : a + b = 0
    · rw [if_pos h0, h0]; exact repCount_zero_le G
    · rw [if_neg h0]; exact hrep (a + b) h0
  calc additiveEnergy G
      = ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b) := rfl
    _ ≤ ∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else M) :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hbound a ha b hb))
    _ ≤ ∑ a ∈ G, (G.card + M * G.card) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        calc ∑ b ∈ G, (if a + b = 0 then G.card else M)
            ≤ ∑ b ∈ G, (if a + b = 0 then G.card else 0)
              + ∑ b ∈ G, (if a + b = 0 then 0 else M) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_le_sum (fun b _ => ?_)
              by_cases h : a + b = 0 <;> simp [h]
          _ ≤ G.card + M * G.card := by
              gcongr
              · calc ∑ b ∈ G, (if a + b = 0 then G.card else 0)
                    ≤ ∑ b ∈ G, (if b = -a then G.card else 0) := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0
                      · have hba : b = -a := by linear_combination h
                        simp [h, hba]
                      · simp [h]
                  _ ≤ G.card := by
                      rw [Finset.sum_ite_eq' G (-a) (fun _ => G.card)]
                      split <;> simp
              · calc ∑ b ∈ G, (if a + b = 0 then 0 else M)
                    ≤ ∑ _b ∈ G, M := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0 <;> simp [h]
                  _ = M * G.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ = (1 + M) * G.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]; ring

/-- **Specialization: representation bound `2` ⟹ minimal additive energy `E(G) ≤ 3|G|²`.** This is the
finite-field form of the roots-of-unity minimal-energy statement: it holds over `F_q` *the moment* one
proves `r(t) ≤ 2` for the `2^k`-subgroup (the open curve-point / Weil input). -/
theorem additiveEnergy_le_three_of_repTwo (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2) :
    additiveEnergy G ≤ 3 * G.card ^ 2 := by
  have := additiveEnergy_le_of_repBound G 2 hrep
  simpa using this

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_of_repBound
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_three_of_repTwo
