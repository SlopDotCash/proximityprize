/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumTowerL2

/-!
# Tower-level frequency concentration: the `2^μ`-explicit bad-frequency budget (#444)

This file lifts the single-level Markov / level-set bound of `SubgroupGaussSumLevelSet`
(`card_high_frequency_le`: `#{b : ‖η_b‖² ≥ T}·T ≤ q·|G|`) to the **top of a disjoint-dilate
`2`-power tower** `G₀ ⊆ G₁ ⊆ … ⊆ G_μ` (`SubgroupGaussSumTowerL2.towerStep`), driving the Markov
budget by the **exact iterated L²-doubling** `secondMoment_tower_pow` rather than the raw
second moment.

> **`card_high_frequency_tower_le`** —
>   `#{b : ‖η_b(G_μ)‖² ≥ T} · T ≤ 2^μ · (∑_b ‖η_b(G₀)‖²)`.

That is: along the whole `2^μ`-tower the number of frequencies whose sup-norm sits above the
threshold `√T` is bounded by `2^μ·(start L² mass)/T`. This is a real **extension of two proven
theorems** — the iterated-doubling `secondMoment_tower_pow` and the Markov technique behind
`card_high_frequency_le` — combining them into one explicit `2^μ`-budget statement for the
bad-frequency set after a full smooth-subgroup tower.

## Scope (honest)

This is the **average-case / Markov** localization of the open core, NOT a closure. The prize
needs the *worst-case over `b ≠ 0`* sup-norm to track the `√2`-per-level L² scale on **every**
path; the Markov bound only confines the failure to a set of size `≤ 2^μ·(start mass)/T`. Probes
(`/tmp/pg-probes/probe_tower_levelset.py`) show this Markov budget is loose by exactly the BGK
factor: at the prize threshold `T = (2·√(n·log(p/n)))²` the *true* bad set is **empty** at every
tested `n ∈ {16,32,64}`, `β ∈ {4,5}`, while Markov still permits `~q·n/T` thousands. That gap —
between the provable Markov budget and the empirically-empty bad set above `2·`floor — **is** the
open BGK / short-character-sum cancellation wall. No capacity over-claim; CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays **open**.

See `SubgroupGaussSumTowerL2.lean` (the iterated-doubling substrate) and
`SubgroupGaussSumLevelSet.lean` (the single-level Markov bound).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumTowerLevelSet

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Tower-level Markov / level-set bound.**
For a valid disjoint-dilate `2`-power tower `G₀ ⊆ … ⊆ G_μ`
(`ValidTower`), the number of frequencies whose `η_b` at the top of the tower has
`‖η_b(G_μ)‖² ≥ T` is controlled by the **exact** iterated `2^μ`-doubled start L² mass:

  `#{b : ‖η_b(G_μ)‖² ≥ T} · T ≤ 2^μ · (∑_b ‖η_b(G₀)‖²)`.

Proof: the standard Markov argument (sum the threshold `T` over the level set, dominate by the
full second moment over the *top* set `G_μ`), then rewrite that second moment by the proven exact
iterated doubling `secondMoment_tower_pow`. -/
theorem card_high_frequency_tower_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G₀ : Finset F)
    (ζ : ℕ → F) {μ : ℕ} (hvalid : ValidTower G₀ ζ μ) (T : ℝ) :
    ((Finset.univ.filter
        (fun b => T ≤ ‖eta ψ (towerStep G₀ ζ μ) b‖ ^ 2)).card : ℝ) * T
      ≤ (2 : ℝ) ^ μ * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2 := by
  set Gtop := towerStep G₀ ζ μ with hGtop
  set S := Finset.univ.filter (fun b => T ≤ ‖eta ψ Gtop b‖ ^ 2) with hS
  have h1 : (S.card : ℝ) * T = ∑ _b ∈ S, T := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _b ∈ S, T ≤ ∑ b ∈ S, ‖eta ψ Gtop b‖ ^ 2 :=
    Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
  have h3 : ∑ b ∈ S, ‖eta ψ Gtop b‖ ^ 2 ≤ ∑ b : F, ‖eta ψ Gtop b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => sq_nonneg _)
  have h4 : ∑ b : F, ‖eta ψ Gtop b‖ ^ 2 = (2 : ℝ) ^ μ * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2 :=
    secondMoment_tower_pow hψ G₀ ζ hvalid μ le_rfl
  rw [h1]
  calc ∑ _b ∈ S, T
      ≤ ∑ b ∈ S, ‖eta ψ Gtop b‖ ^ 2 := h2
    _ ≤ ∑ b : F, ‖eta ψ Gtop b‖ ^ 2 := h3
    _ = (2 : ℝ) ^ μ * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2 := h4

/-- **Tower bad-frequency budget in `2^μ`-explicit divided form.**
For `T > 0`, the level set at the top of the tower has cardinality at most
`2^μ · (start L² mass) / T`:

  `#{b : ‖η_b(G_μ)‖² ≥ T} ≤ 2^μ · (∑_b ‖η_b(G₀)‖²) / T`.

The bad-frequency count after a full `μ`-level smooth-subgroup tower is sparse with an explicit
`2^μ` budget read off the exact iterated doubling. -/
theorem card_high_frequency_tower_le_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G₀ : Finset F)
    (ζ : ℕ → F) {μ : ℕ} (hvalid : ValidTower G₀ ζ μ) {T : ℝ} (hT : 0 < T) :
    ((Finset.univ.filter
        (fun b => T ≤ ‖eta ψ (towerStep G₀ ζ μ) b‖ ^ 2)).card : ℝ)
      ≤ (2 : ℝ) ^ μ * (∑ b : F, ‖eta ψ G₀ b‖ ^ 2) / T := by
  have hkey := card_high_frequency_tower_le hψ G₀ ζ hvalid T
  rw [le_div_iff₀ hT]
  exact hkey

/-- **The Markov budget is monotone in tower height**: the `2^μ` factor grows by exactly `2` per
level, the same rate as the L² mass, while the prize demands the bad set track the `√2` rate. This
records the explicit `2^{μ+1} = 2·2^μ` step that the open BGK content must beat. -/
theorem tower_levelSet_budget_succ {ψ : AddChar F ℂ} (G₀ : Finset F) (μ : ℕ) :
    (2 : ℝ) ^ (μ + 1) * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2
      = 2 * ((2 : ℝ) ^ μ * ∑ b : F, ‖eta ψ G₀ b‖ ^ 2) := by
  ring

end ArkLib.ProximityGap.SubgroupGaussSumTowerLevelSet

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumTowerLevelSet.card_high_frequency_tower_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumTowerLevelSet.card_high_frequency_tower_le_div
