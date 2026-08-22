/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Attack #02 — Gaussian periods / Stickelberger / Gross–Koblitz (the wrong-direction lemma)

This scratch brick records, axiom-clean, the precise reason the Gauss-period /
Stickelberger / Gross–Koblitz route **cannot** supply the prize upper bound on
`M = max_{b≠0} ‖η_b‖`.

The Gross–Koblitz / Stickelberger machinery pins the **p-adic valuation** of a Gauss
sum `τ(χ)` (equivalently of the period `η_b`, an algebraic integer in `ℤ[ζ_p]`).
Two facts about that information:

* archimedean: `‖τ(χ)‖ = √q` **exactly** for every nontrivial `χ` (`norm_gaussSum_eq_sqrt`),
  so the valuation adds nothing archimedean about a single Gauss sum;
* the period `η_b` is an **average / sum** of `t = (q−1)/d` such Gauss sums, and the
  archimedean magnitude of that sum is governed by **phase cancellation**, which the
  valuation is blind to.

Every product-of-conjugates (norm) / valuation argument yields a **lower** bound on the
house, never an upper bound. We make that precise here: the second-moment identity
forces SOME nonzero frequency to have `‖η_b‖² ≥ |G|·q/(q−1) > |G|`. So the *only* thing
the algebraic (multiplicative / valuation) side proves about the house is a lower bound
`M ≥ √|G|` — the wrong direction for the prize, which needs the upper bound `M ≲ √(n log q)`.

This is a documented obstruction (a `*_house_lower` brick), not a closure.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.Attack02GaussPeriodHouse

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The house lower bound from the second moment (the wrong-direction lemma).**

For any primitive additive character `ψ` and any frequency set `G` with
`0 < |G| < q`, there is a NONZERO frequency `b` with
`‖η_b‖² ≥ |G| · q / (q − 1)`.

Proof: `η_0 = |G|`, so the `b = 0` term of the second moment `∑_b ‖η_b‖² = q·|G|`
contributes `|G|²`; the remaining `q−1` nonzero frequencies carry `q·|G| − |G|² =
|G|(q − |G|)` of mass, so the maximum over them is at least the average
`|G|(q − |G|)/(q − 1) ≥ |G|·(q − |G|)/(q−1)`. Since `|G| < q`, this exceeds `|G|`
whenever `|G| < q`, giving a strict house lower bound `M > √|G|`.

This is exactly the bound the valuation / Stickelberger route can reach (a lower
bound), and it goes the WRONG way for the prize. -/
theorem exists_nonzero_house_lower
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG0 : 0 < G.card) (hGq : G.card < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) * (Fintype.card F - G.card) / (Fintype.card F - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  classical
  -- total second moment
  have htot : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  -- the b = 0 term is |G|²
  have heta0 : eta ψ G 0 = (G.card : ℂ) := by
    have : eta ψ G 0 = ∑ _y ∈ G, (1 : ℂ) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [zero_mul, AddChar.map_zero_eq_one]
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0sq : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [heta0, Complex.norm_natCast]
  -- split off b = 0
  have hsplit : ‖eta ψ G 0‖ ^ 2
      + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card := by
    rw [Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ 2)
      (Finset.mem_univ (0 : F))]
    exact htot
  -- mass on the nonzero frequencies
  have hmass : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (G.card : ℝ) * (Fintype.card F - G.card) := by
    have := hsplit
    rw [h0sq] at this
    have hcard : (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
        = (G.card : ℝ) * (Fintype.card F - G.card) := by ring
    linarith [this, hcard]
  -- number of nonzero frequencies
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    have := Fintype.one_lt_card (α := F); omega
  have hcarderase : (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  -- average over the nonzero frequencies ≤ max
  set avg : ℝ := (G.card : ℝ) * (Fintype.card F - G.card) / (Fintype.card F - 1) with havg
  have hpos : (0 : ℝ) < (Fintype.card F - 1 : ℝ) := by
    have h := Fintype.one_lt_card (α := F)
    have : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast h
    linarith
  have hHle : ∑ _b ∈ Finset.univ.erase (0 : F), avg
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 := by
    refine le_of_eq ?_
    rw [Finset.sum_const, hcarderase, nsmul_eq_mul, hmass]
    have hcast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
      have h := Fintype.one_lt_card (α := F)
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast, havg, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self (ne_of_gt hpos), mul_one]
  obtain ⟨b, hbmem, hbmax⟩ := Finset.exists_le_of_sum_le hne hHle
  exact ⟨b, Finset.ne_of_mem_erase hbmem, hbmax⟩

end ArkLib.ProximityGap.Attack02GaussPeriodHouse

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms
  ArkLib.ProximityGap.Attack02GaussPeriodHouse.exists_nonzero_house_lower
