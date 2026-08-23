/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetRepSecondMomentCensus

/-!
# DC-subtracted far-frequency count budget at the prize scale (#444)

This brick specializes the proven Chebyshev/large-sieve tail
(`card_large_frequencies_mul_le`, `∑_b ‖η_b‖² = q·n`) and the exact **nonzero** second moment
(`CosetRepSecondMomentCensus.nonzero_secondMoment_eq`, `∑_{b≠0} ‖η_b‖² = q·n − n²`) to the EXACT
campaign "exceedance budget" object: the number of NON-ZERO frequencies whose squared period
reaches a threshold `L`.

* `card_dc_subtracted_large_frequencies_mul_le` — for any `L`,
  `#{b≠0 : ‖η_b‖² ≥ L} · L ≤ q·n − n²`. (DC-subtracted Markov; pure Parseval, no Weil.)
* `card_dc_subtracted_large_frequencies_le` — for `L > 0`,
  `#{b≠0 : ‖η_b‖² ≥ L} ≤ (q·n − n²)/L`.
* `card_prize_budget_frequencies_le` — at the **prize / Johnson scale** `L = q`:
  `#{b≠0 : ‖η_b‖² ≥ q} ≤ n = |G|`, i.e. the count of "far" frequencies is **linear in `n`** and
  **does NOT grow with `q`** — the exact unconditional `O(n)` ceiling the bad-side family argument
  and the union-count growth-law frontier both cite as a budget.

**Honest scope.** This bounds the COUNT of large frequencies, NOT their MAGNITUDE (the open
BGK/Paley wall). It therefore CANNOT close the prize — exactly the right scope: it discharges the
named "at most `O(n)` bad scalars at production budget" hypothesis (faces 3/4 of the open core),
and nothing more.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.CosetRepSecondMomentCensus

namespace ArkLib.ProximityGap.Frontier.FarFrequencyBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **DC-subtracted Markov budget.** From the exact nonzero second moment
`∑_{b≠0} ‖η_b‖² = q·n − n²`, for any threshold `L` the number of NON-ZERO frequencies whose squared
Gauss sum reaches `L` satisfies `#{b≠0 : ‖η_b‖² ≥ L}·L ≤ q·n − n²`. No Weil input. -/
theorem card_dc_subtracted_large_frequencies_mul_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {L : ℝ} :
    (((Finset.univ.erase (0 : F)).filter (fun b : F => L ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) * L
      ≤ (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  classical
  set S := (Finset.univ.erase (0 : F)).filter (fun b : F => L ≤ ‖eta ψ G b‖ ^ 2) with hS
  calc ((S.card : ℝ)) * L
      = ∑ _b ∈ S, L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
    _ ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun b _ _ => by positivity)
    _ = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := nonzero_secondMoment_eq hψ G

/-- **DC-subtracted far-frequency count.** For `L > 0`,
`#{b≠0 : ‖η_b‖² ≥ L} ≤ (q·n − n²)/L`. -/
theorem card_dc_subtracted_large_frequencies_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {L : ℝ} (hL : 0 < L) :
    (((Finset.univ.erase (0 : F)).filter (fun b : F => L ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / L := by
  rw [le_div_iff₀ hL]
  exact card_dc_subtracted_large_frequencies_mul_le hψ G

/-- **Prize-scale budget: the far-frequency count is `≤ |G| = n`, q-independent.** At the
Johnson/full-field scale `L = q = |F|`, the number of NON-ZERO frequencies reaching the prize
threshold is at most `|G|`: linear in `n`, NOT growing with `q`. (In fact `≤ n − n²/q < n`.) This
is the exact unconditional `O(n)` exceedance budget; it bounds the COUNT, not the open MAGNITUDE
wall. -/
theorem card_prize_budget_frequencies_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (((Finset.univ.erase (0 : F)).filter
        (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card) ≤ G.card := by
  classical
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  set S := (Finset.univ.erase (0 : F)).filter
      (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2) with hS
  -- `|S|·q ≤ q·n − n² ≤ q·n`, so `|S| ≤ n` over ℝ, then cast to ℕ.
  have hmul : (S.card : ℝ) * (Fintype.card F : ℝ)
      ≤ (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 :=
    card_dc_subtracted_large_frequencies_mul_le hψ G
  have hsq : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 := by positivity
  have hmul2 : (S.card : ℝ) * (Fintype.card F : ℝ) ≤ (Fintype.card F : ℝ) * G.card := by
    have := hmul
    nlinarith [hsq, hmul]
  have hle : (S.card : ℝ) ≤ (G.card : ℝ) := by
    rw [mul_comm (Fintype.card F : ℝ) (G.card : ℝ)] at hmul2
    exact le_of_mul_le_mul_right hmul2 hqR
  exact_mod_cast hle

end ArkLib.ProximityGap.Frontier.FarFrequencyBudget

#print axioms
  ArkLib.ProximityGap.Frontier.FarFrequencyBudget.card_dc_subtracted_large_frequencies_mul_le
#print axioms
  ArkLib.ProximityGap.Frontier.FarFrequencyBudget.card_dc_subtracted_large_frequencies_le
#print axioms
  ArkLib.ProximityGap.Frontier.FarFrequencyBudget.card_prize_budget_frequencies_le
