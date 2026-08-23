/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Additive energy from a representation bound, over ANY abelian group (#389)

The in-tree `AdditiveEnergyRepBound.lean` proves `E(G) ≤ (1+M)·|G|²` from `r(t) ≤ M`
(`t ≠ 0`) but only over a **field** `F`. The char-0 model of the 2-power NTT subgroup is
the **signed standard basis** `{±eᵢ} ⊆ ℤ^N` (`N = n/2`) — an abelian group that is *not* a
field — so the field hypothesis blocks using the machine on the very model that explains
why the energy is `Θ(n²)` (`probe_energy_doubling.py`: `E(μ_{2^m}) = 3n²−3n`). This file
removes the hypothesis: the rep-bound energy inequality needs only `AddCommGroup`.

* `repCount G t` — ordered representations `t = c + (t−c)` inside `G` (group version).
* `additiveEnergy G = ∑_{a,b∈G} repCount G (a+b)`.
* `additiveEnergy_le_of_repBound` — `(∀ t ≠ 0, r(t) ≤ M) ⟹ E(G) ≤ (1+M)·|G|²`, over any
  `AddCommGroup`. The proof is the field proof with `eq_neg_of_add_eq_zero_left` in place of
  the ring `linear_combination`.

This is the reusable enabler for the rigorous char-0 energy model (`ℤ^N` signed basis,
`r(t) ≤ 2`), the structural reason the smooth-domain additive energy is minimal.
-/

open Finset

namespace ArkLib.ProximityGap.AddEnergyGroupRepBound

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Ordered representations `t = c + (t−c)` inside `S`. -/
def repCount (S : Finset G) (t : G) : ℕ := (S.filter (fun y => t - y ∈ S)).card

/-- The additive energy `E(S) = ∑_{a,b∈S} #{y∈S : (a+b)−y∈S}`. -/
def additiveEnergy (S : Finset G) : ℕ := ∑ a ∈ S, ∑ b ∈ S, repCount S (a + b)

/-- `r(0) ≤ |S|` (the map `y ↦ −y` is injective). -/
theorem repCount_zero_le (S : Finset G) : repCount S 0 ≤ S.card :=
  Finset.card_filter_le _ _

/-- **Additive energy from a representation bound, over any abelian group.** If every
nonzero `t` has at most `M` representations `t = c + d` with `c, d ∈ S`, then
`E(S) ≤ (1 + M)·|S|²`. -/
theorem additiveEnergy_le_of_repBound (S : Finset G) (M : ℕ)
    (hrep : ∀ t : G, t ≠ 0 → repCount S t ≤ M) :
    additiveEnergy S ≤ (1 + M) * S.card ^ 2 := by
  classical
  have hbound : ∀ a ∈ S, ∀ b ∈ S,
      repCount S (a + b) ≤ (if a + b = 0 then S.card else M) := by
    intro a _ b _
    by_cases h0 : a + b = 0
    · rw [if_pos h0, h0]; exact repCount_zero_le S
    · rw [if_neg h0]; exact hrep (a + b) h0
  calc additiveEnergy S
      = ∑ a ∈ S, ∑ b ∈ S, repCount S (a + b) := rfl
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, (if a + b = 0 then S.card else M) :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hbound a ha b hb))
    _ ≤ ∑ a ∈ S, (S.card + M * S.card) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        calc ∑ b ∈ S, (if a + b = 0 then S.card else M)
            ≤ ∑ b ∈ S, (if a + b = 0 then S.card else 0)
              + ∑ b ∈ S, (if a + b = 0 then 0 else M) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_le_sum (fun b _ => ?_)
              by_cases h : a + b = 0 <;> simp [h]
          _ ≤ S.card + M * S.card := by
              gcongr
              · calc ∑ b ∈ S, (if a + b = 0 then S.card else 0)
                    ≤ ∑ b ∈ S, (if b = -a then S.card else 0) := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0
                      · have hba : b = -a := by
                          rw [add_comm] at h; exact eq_neg_of_add_eq_zero_left h
                        simp [h, hba]
                      · simp [h]
                  _ ≤ S.card := by
                      rw [Finset.sum_ite_eq' S (-a) (fun _ => S.card)]
                      split <;> simp
              · calc ∑ b ∈ S, (if a + b = 0 then 0 else M)
                    ≤ ∑ _b ∈ S, M := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0 <;> simp [h]
                  _ = M * S.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ = (1 + M) * S.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]; ring

/-- **Minimal-energy specialization**: `r(t) ≤ 2` for `t ≠ 0` ⟹ `E(S) ≤ 3·|S|²`, over any
abelian group — the group-level form of the roots-of-unity minimal additive energy. -/
theorem additiveEnergy_le_three_of_repTwo (S : Finset G)
    (hrep : ∀ t : G, t ≠ 0 → repCount S t ≤ 2) :
    additiveEnergy S ≤ 3 * S.card ^ 2 := by
  have := additiveEnergy_le_of_repBound S 2 hrep
  simpa using this

/-! ## Source audit -/

#print axioms additiveEnergy_le_of_repBound
#print axioms additiveEnergy_le_three_of_repTwo

end ArkLib.ProximityGap.AddEnergyGroupRepBound
