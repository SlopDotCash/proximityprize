/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R306Depth3CharZeroFloor

/-!
# LANE B2 (#466 round 307): SHADOW INJECTIVITY ⟹ EXACT CHAR-0 ENERGY — the formal
  good-prime condition at depth 3

Completes the r306 floor with the equality half: if the shadow evaluation `evalVec g` is
INJECTIVE on the key set (no two distinct char-0 3-sum vectors collide mod p — the r305
"no wraparound" condition, which the census establishes for every prime beyond the largest
class-norm divisor), then the depth-3 energy equals the char-0 shadow energy EXACTLY:

* **`depth3_energy_eq_of_shadow_injective`** :
  `(∀ v ∈ keys, ∀ w ∈ keys, evalVec g v = evalVec g w → v = w) →
   Σ_{c : F} rep₃(c)² = Σ_v N₃(v)²`.

Together with r306 (`shadow_energy_le_depth3_energy`), this machine-checks the full r305
dichotomy: the depth-3 energy is the char-0 value PLUS a nonnegative collision mass, and
the collision mass vanishes exactly on shadow-injective instances.  Injectivity on the
finite key set is the precise good-prime condition the census computes — for `n = 32`, it
holds for every prime `p > 3487801441` (probe-established; the Lean-side condition is now a
clean named hypothesis a census certificate can discharge per prime).  Issue #466,
round 307, LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R307ShadowInjectivityExactEnergy

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- If a finset has at most one element, the square of its sum is the sum of squares. -/
theorem sq_sum_eq_sum_sq_of_card_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card ≤ 1) (f : α → ℕ) :
    (∑ v ∈ s, f v) ^ 2 = ∑ v ∈ s, (f v) ^ 2 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (le_antisymm hs (Finset.card_pos.mpr h))
    simp [hv]

/-- **Shadow injectivity ⟹ exact char-0 energy** (the equality half of r306): if no two
distinct shadow keys collide under evaluation, the depth-3 energy equals the char-0 shadow
energy exactly — zero excess. -/
theorem depth3_energy_eq_of_shadow_injective (g : F) (n m : ℕ) (hm : 0 < m)
    (hn : n = 2 * m) (hg : g ^ m = -1)
    (hinj : ∀ v ∈ keys n m, ∀ w ∈ keys n m, evalVec g m v = evalVec g m w → v = w) :
    ∑ c : F, (rep3F g n c) ^ 2 = ∑ v ∈ keys n m, (N3 n m v) ^ 2 := by
  classical
  -- each evaluation fiber of the key set has at most one element
  have hfib : ∀ c : F, ((keys n m).filter (fun v => evalVec g m v = c)).card ≤ 1 := by
    intro c
    rw [Finset.card_le_one]
    intro v hv w hw
    rw [Finset.mem_filter] at hv hw
    exact hinj v hv.1 w hw.1 (by rw [hv.2, hw.2])
  -- rewrite each fiber square as a fiber sum of squares, then departition
  have hstep : ∀ c : F, (rep3F g n c) ^ 2
      = ∑ v ∈ (keys n m).filter (fun v => evalVec g m v = c), (N3 n m v) ^ 2 := by
    intro c
    rw [rep3F_eq_sum_N3 g n m hm hn hg c]
    exact sq_sum_eq_sum_sq_of_card_le_one _ (hfib c) _
  rw [Finset.sum_congr rfl (fun c _ => hstep c)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => evalVec g m v)
    (f := fun v => (N3 n m v) ^ 2)
    (fun v _ => Finset.mem_univ (evalVec g m v))]

end ArkLib.ProximityGap.Frontier.R307ShadowInjectivityExactEnergy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R307ShadowInjectivityExactEnergy.sq_sum_eq_sum_sq_of_card_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R307ShadowInjectivityExactEnergy.depth3_energy_eq_of_shadow_injective
