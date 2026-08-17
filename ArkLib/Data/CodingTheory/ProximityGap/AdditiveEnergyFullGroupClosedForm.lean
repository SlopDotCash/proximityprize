/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# Round 11 (Issue #232, ABF26) — the GENERAL closed form for the additive energy of `F_p^×`.

`SubgroupAdditiveEnergyTowerF17` computed, by `decide`, the energy of each subgroup of `F₁₇^×`,
ending with the full group `E(F₁₇^×) = 3856`. This file proves the **general** closed form, for
**every** prime `p` (no `decide` — a real combinatorial proof):

> `additiveEnergy_units_eq`:  `E(F_p^×) = (p−1)² + (p−1)(p−2)²`.

(For `p = 17`: `16² + 16·15² = 256 + 3600 = 3856`, matching the `decide` value.) The mechanism is
the
representation-count `repCount (F_p^×) s = (F_p^× .erase s).card`, which is `p−1` at `s = 0` and
`p−2`
otherwise; the unique `b = −a` realizing `a + b = 0` carries the `p−1` term and the other `p−2`
pairs carry `p−2`.

This is the **top of the subgroup tower** (`|G| = p−1 = q−1`, the endpoint regime), where
`E ≈ p³` — maximal concentration. It is the closed-form companion to the `decide` tower and the
general `μ_{dm}^d = μ_m` law. *Honest scope:* this is the `|G| ~ q` endpoint; the prize regime
`|G| = 2^k ≪ q` is the open Weil/sum-product quantity, untouched here. `sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
#232.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.AdditiveEnergyRepBound Finset

namespace ArkLib.ProximityGap.AdditiveEnergyFullGroupClosedForm

variable {p : ℕ} [Fact p.Prime]

/-- The full multiplicative group `F_p^× = {x : ZMod p | x ≠ 0}`. -/
def G (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := Finset.univ.filter (fun x => x ≠ 0)

theorem mem_G {x : ZMod p} : x ∈ G p ↔ x ≠ 0 := by simp [G]

theorem G_card : (G p).card = p - 1 := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  have h : G p = (Finset.univ : Finset (ZMod p)).erase 0 := by
    ext x; simp [G, Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

/-- **The representation count of the full group.** `repCount (F_p^×) s = (F_p^×).erase s).card`,
which equals `p−1` when `s = 0` (every nonzero `y` works) and `p−2` otherwise (`y ≠ 0, y ≠ s`). -/
theorem repCount_eq (s : ZMod p) : repCount (G p) s = if s = 0 then p - 1 else p - 2 := by
  unfold repCount
  have hfilter : (G p).filter (fun y => s - y ∈ G p) = (G p).erase s := by
    rw [← Finset.filter_ne' (G p) s]
    apply Finset.filter_congr
    intro y _
    rw [mem_G, sub_ne_zero]
    exact ne_comm
  rw [hfilter]
  by_cases h : s = 0
  · subst h
    rw [if_pos rfl, Finset.erase_eq_of_notMem (by rw [mem_G]; simp), G_card]
  · rw [if_neg h, Finset.card_erase_of_mem (mem_G.mpr h), G_card]
    omega

/-- **The general closed form for the additive energy of `F_p^×`.** For every prime `p`,
`E(F_p^×) = (p−1)² + (p−1)(p−2)²`. -/
theorem additiveEnergy_units_eq :
    additiveEnergy (G p) = (p - 1) ^ 2 + (p - 1) * (p - 2) ^ 2 := by
  classical
  unfold additiveEnergy
  -- inner sum is constant in `a`: one `b = −a` gives `p−1`, the other `p−2` pairs give `p−2`.
  have inner : ∀ a ∈ G p,
      (∑ b ∈ G p, repCount (G p) (a + b)) = (p - 1) + (p - 2) ^ 2 := by
    intro a ha
    rw [Finset.sum_congr rfl (fun b _ => repCount_eq (a + b)), Finset.sum_ite,
      Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have e1 : ((G p).filter (fun b => a + b = 0)).card = 1 := by
      have hset : (G p).filter (fun b => a + b = 0) = {-a} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_singleton, mem_G]
        constructor
        · rintro ⟨_, hab⟩; linear_combination hab
        · rintro rfl; exact ⟨neg_ne_zero.mpr (mem_G.mp ha), by ring⟩
      rw [hset, Finset.card_singleton]
    have e2 : ((G p).filter (fun b => ¬ (a + b = 0))).card = p - 2 := by
      have htot := Finset.card_filter_add_card_filter_not
        (s := G p) (fun b => a + b = 0)
      rw [e1, G_card] at htot
      omega
    rw [e1, e2, one_mul, ← pow_two]
  rw [Finset.sum_congr rfl inner, Finset.sum_const, G_card, smul_eq_mul]
  generalize p - 1 = m
  generalize p - 2 = k
  ring

/-- **Sanity check against the `decide` value:** at `p = 17`, the closed form gives
`16² + 16·15² = 3856`, matching `SubgroupAdditiveEnergyTowerF17.energy_G16`. -/
theorem additiveEnergy_units_F17 [Fact (Nat.Prime 17)] : additiveEnergy (G 17) = 3856 := by
  rw [additiveEnergy_units_eq]; norm_num

end ArkLib.ProximityGap.AdditiveEnergyFullGroupClosedForm

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyFullGroupClosedForm.additiveEnergy_units_eq
