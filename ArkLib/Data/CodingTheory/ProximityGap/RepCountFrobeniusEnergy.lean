/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFrobeniusBound
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCharZeroEnergy

/-!
# THE ADDITIVE ENERGY IS `O(n²)` IN THE INERT REGIME `n ∣ p+1` (#389)

The full char-`p` Garcia–Voloch bound `repCount_le_two_of_dvd_succ` (`r(c) ≤ 2` for *every*
`c ≠ 0` when `n ∣ p+1`) gives, by the same counting as the char-0 case, an unconditional
`O(n²)` additive-energy bound on the inert/conjugate-NTT subgroup:

> **`additiveEnergy_le_of_dvd_succ`** — over a char-`p` field with `μ_n ⊂ F_{p²}` (`n ∣ p+1`),
> `E(μ_n) ≤ 3·|μ_n|²`.

This is the **complete** energy bound (over *all* `c`, no Stepanov, no GV residual) for the
inert regime — an order below the split-case Heath-Brown–Konyagin target `|G|^{8/3}`.  Via the
in-tree cubic bridge (`zeroSumTriples_sq_le_card_mul_energy`) it pins the smooth-domain
sub-Johnson supply on these fields, completing the unconditional δ* picture for `n ∣ p+1` and
isolating the open Stepanov wall to *exactly* the split deployed-prize case `n ∣ p−1`.
Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The energy bound from a pointwise `≤ 2` rep-count** (the abstract core shared by the
char-0 and inert-regime instances): if `r(c) ≤ 2` for every `c ≠ 0`, then `E(G) ≤ 3·|G|²`. -/
theorem additiveEnergy_le_of_repCount_le_two {F : Type*} [Field F] [DecidableEq F]
    {G : Finset F} (hr2 : ∀ c : F, c ≠ 0 → repCount G c ≤ 2) :
    additiveEnergy G ≤ 3 * G.card ^ 2 := by
  classical
  rw [additiveEnergy]
  calc ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b)
      ≤ ∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else 2) := by
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        by_cases hab : a + b = 0
        · rw [if_pos hab]; exact repCount_le_card G _
        · rw [if_neg hab]; exact hr2 _ hab
    _ ≤ ∑ a ∈ G, (G.card + 2 * G.card) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        calc ∑ b ∈ G, (if a + b = 0 then G.card else 2)
            ≤ ∑ b ∈ G, (if a + b = 0 then G.card else 0) + ∑ b ∈ G, 2 := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_le_sum (fun b _ => ?_)
              by_cases hab : a + b = 0 <;> simp [hab]
          _ ≤ G.card + 2 * G.card := by
              refine add_le_add ?_ ?_
              · have hcard1 : (G.filter (fun b => a + b = 0)).card ≤ 1 := by
                  calc (G.filter (fun b => a + b = 0)).card
                      ≤ ({-a} : Finset F).card := by
                        refine Finset.card_le_card (fun b hb => ?_)
                        rw [Finset.mem_filter] at hb
                        rw [Finset.mem_singleton]
                        linear_combination hb.2
                    _ = 1 := Finset.card_singleton _
                calc ∑ b ∈ G, (if a + b = 0 then G.card else 0)
                    = (G.filter (fun b => a + b = 0)).card * G.card := by
                      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
                  _ ≤ 1 * G.card := Nat.mul_le_mul_right _ hcard1
                  _ = G.card := one_mul _
              · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 3 * G.card ^ 2 := by rw [Finset.sum_const, smul_eq_mul]; ring

variable {F : Type*} [Field F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- **THE INERT-REGIME ENERGY BOUND**: over a char-`p` field with `n ∣ p+1`,
`E(μ_n) ≤ 3·|μ_n|²` — unconditional, no Stepanov. -/
theorem additiveEnergy_le_of_dvd_succ {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (ndvd : n ∣ p + 1) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    additiveEnergy G ≤ 3 * G.card ^ 2 :=
  additiveEnergy_le_of_repCount_le_two
    (fun c hc0 => repCount_le_two_of_dvd_succ hn ndvd hGmem hc0)

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_of_repCount_le_two
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_of_dvd_succ
