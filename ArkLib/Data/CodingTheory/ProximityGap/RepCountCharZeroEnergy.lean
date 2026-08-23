/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCharZeroBound

/-!
# THE CHAR-0 ADDITIVE ENERGY OF `μ_n` IS `O(n²)` (#389)

Direct consequence of `repCount_le_two` (the char-0 Garcia–Voloch bound `r(c) ≤ 2`): over
`ℂ`, the additive energy of `μ_n` is at most `3·|μ_n|²`.

> **`additiveEnergy_charZero_le`** — over `ℂ`, `E(μ_n) ≤ 3·|μ_n|²`.

`E = Σ_{a,b∈μ_n} r(a+b)`: each off-diagonal term (`a+b ≠ 0`) is `≤ 2` by `repCount_le_two`,
and the `≤ |μ_n|` diagonal terms (`a+b = 0`) are `≤ |μ_n|` trivially — so
`E ≤ 2|G|² + |G|² = 3|G|²`.

Contrast with the characteristic-`p` Heath-Brown–Konyagin bound `E(μ_n) ≪ |G|^{8/3}`: the
char-`0` energy is `O(n²)`, an order of magnitude smaller — the whole `n^{8/3}` (and the
`n^{2/3}` pointwise) lives in the **characteristic-`p` surplus**, confirming the wall is purely
a prime-characteristic phenomenon.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- The trivial bound `r(s) ≤ |G|` (the representation set is a subset of `G`). -/
theorem repCount_le_card {F : Type*} [Field F] [DecidableEq F] (G : Finset F) (s : F) :
    repCount G s ≤ G.card :=
  Finset.card_filter_le _ _

/-- **THE CHAR-0 ENERGY BOUND**: over `ℂ`, `E(μ_n) ≤ 3·|μ_n|²`. -/
theorem additiveEnergy_charZero_le {G : Finset ℂ} {n : ℕ} (hn : n ≠ 0)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    additiveEnergy G ≤ 3 * G.card ^ 2 := by
  classical
  rw [additiveEnergy]
  -- bound each `r(a+b)` by `2` off the diagonal and by `|G|` on it
  calc ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b)
      ≤ ∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else 2) := by
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        by_cases hab : a + b = 0
        · rw [if_pos hab]; exact repCount_le_card G _
        · rw [if_neg hab]; exact repCount_le_two hn hGmem hab
    _ ≤ ∑ a ∈ G, (G.card + 2 * G.card) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        -- at most one `b` with `a+b=0`, contributing `≤ |G|`; the rest contribute `2` each
        calc ∑ b ∈ G, (if a + b = 0 then G.card else 2)
            ≤ ∑ b ∈ G, (if a + b = 0 then G.card else 0)
              + ∑ b ∈ G, 2 := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_le_sum (fun b _ => ?_)
                by_cases hab : a + b = 0 <;> simp [hab]
          _ ≤ G.card + 2 * G.card := by
                refine add_le_add ?_ ?_
                · -- the diagonal sum has at most one nonzero term, `≤ |G|`
                  have hcard1 : (G.filter (fun b => a + b = 0)).card ≤ 1 := by
                    calc (G.filter (fun b => a + b = 0)).card
                        ≤ ({-a} : Finset ℂ).card := by
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
    _ = 3 * G.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]; ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_charZero_le
