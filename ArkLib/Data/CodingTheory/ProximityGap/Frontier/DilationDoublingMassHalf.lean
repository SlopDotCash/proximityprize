/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationRealSignCocycle

/-!
# The doubling-mass halving law for the dilation sign cocycle

This file proves the quantitative cap the `DilationRealSignCocycle` doc-comment **asserts but does
not prove**: along a genuine disjoint tower step `G ⊔ ζ•G` (negation-closed `G`, `Disjoint G
(dilate ζ G)`), the L²-weighted mass of the **doubling** (same-sign, `+`) frequencies is **exactly
half** the total cross-mass, hence at most `½·q·|G|`.

## The mechanism (extends two proven theorems, no new analytic input)

For a negation-closed `G` the period `η_b(G)` is **real** (`eta_eq_ofReal_re`), so the real signed
cross-product `s_b := (η_b).re · (η_{ζb}).re` satisfies `|s_b| = ‖η_b‖ · ‖η_{ζb}‖` (product of
absolute values of two reals = absolute value of their product). Split the frequencies by the sign of
`s_b`:

* `plusMass  := ∑_{s_b ≥ 0} ‖η_b‖·‖η_{ζb}‖`  (the **doubling** trajectory — the only frequencies that
  can carry the trivial `2·M` scaling at the step, by `union_norm_eq_add_of_same_sign`),
* `minusMass := ∑_{s_b < 0} ‖η_b‖·‖η_{ζb}‖`  (the **cancelling** trajectory).

Two proven inputs:

* `sign_balance_zero`: `∑_b s_b = 0`. Since `s_b = +|s_b|` on the `+`-set and `s_b = −|s_b|` on the
  `−`-set, the signed sum is `plusMass − minusMass`, so **`plusMass = minusMass`**.
* `total_doublingMass_le`: `plusMass + minusMass = ∑_b ‖η_b‖·‖η_{ζb}‖ ≤ q·|G|`.

Combining: **`plusMass = ½·(total cross-mass) ≤ ½·q·|G|`**. The cocycle cannot place all frequencies
on the doubling trajectory; the L²-weighted doubling mass is hard-capped at `q|G|/2`.

## Scope / honesty

This is an **average-case L²-budget cap on the sign cocycle**, an exact extension of two proven
theorems — NOT a CORE closure. It quantifies *how much* doubling mass the tower step can carry in
aggregate (≤ half), but the prize wall is the **worst-case single-frequency deep-descent** sign word,
which this global average does not control (a single frequency may sit on the `+`-trajectory through
many levels; the average only forbids *all* of them doing so). Thinness enters exactly as in the
parent file: the halving rests on negation-closure (`-1 ∈ μ_{2^i}`, `i ≥ 1`), which makes `η` real.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

See `DilationRealSignCocycle` (`sign_balance_zero`, `total_doublingMass_le`).
-/

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The signed real cross-product of the period at `b` and its dilate at `ζb`. For negation-closed
`G` this is real and equals `±‖η_b‖·‖η_{ζb}‖`. -/
noncomputable def crossSign (ψ : AddChar F ℂ) (G : Finset F) (ζ b : F) : ℝ :=
  (eta ψ G b).re * (eta ψ G (ζ * b)).re

/-- The absolute cross-mass `‖η_b‖·‖η_{ζb}‖`. -/
noncomputable def crossMass (ψ : AddChar F ℂ) (G : Finset F) (ζ b : F) : ℝ :=
  ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖

/-- For a negation-closed `G`, the absolute cross-mass equals the absolute value of the real signed
cross-product: `‖η_b‖·‖η_{ζb}‖ = |(η_b).re · (η_{ζb}).re|`. -/
theorem crossMass_eq_abs_crossSign {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) (ζ b : F) :
    crossMass ψ G ζ b = |crossSign ψ G ζ b| := by
  unfold crossMass crossSign
  rw [abs_mul, norm_eta_eq_abs_re G hG b, norm_eta_eq_abs_re G hG (ζ * b)]

/-- The doubling (`+`-sign, same-sign) cross-mass: the L²-weighted mass of frequencies whose two
children agree in sign (`s_b ≥ 0`). These are exactly the frequencies that can carry the trivial
`2·M` doubling at the step (`union_norm_eq_add_of_same_sign`). -/
noncomputable def plusMass (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b), crossMass ψ G ζ b

/-- The cancelling (`−`-sign, opposite-sign) cross-mass: `s_b < 0`. -/
noncomputable def minusMass (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => crossSign ψ G ζ b < 0), crossMass ψ G ζ b

omit [DecidableEq F] in
/-- The signed cross-sum splits as `plusMass − minusMass`: on the `+`-set `s_b = +crossMass`, on the
`−`-set `s_b = −crossMass`. -/
theorem signedSum_eq_plus_sub_minus {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) (ζ : F) :
    (∑ b : F, crossSign ψ G ζ b) = plusMass ψ G ζ - minusMass ψ G ζ := by
  classical
  unfold plusMass minusMass
  -- split the full sum over the sign of crossSign
  have hsplit :
      (∑ b : F, crossSign ψ G ζ b)
        = (∑ b ∈ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b), crossSign ψ G ζ b)
          + ∑ b ∈ Finset.univ.filter (fun b => ¬ (0 ≤ crossSign ψ G ζ b)), crossSign ψ G ζ b := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hposset :
      (∑ b ∈ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b), crossSign ψ G ζ b)
        = ∑ b ∈ Finset.univ.filter (fun b => 0 ≤ crossSign ψ G ζ b), crossMass ψ G ζ b := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [crossMass_eq_abs_crossSign G hG, abs_of_nonneg hb.2]
  -- on the negative set, ¬(0 ≤ s) ↔ s < 0, and crossSign = - crossMass
  have hnegset :
      (∑ b ∈ Finset.univ.filter (fun b => ¬ (0 ≤ crossSign ψ G ζ b)), crossSign ψ G ζ b)
        = - ∑ b ∈ Finset.univ.filter (fun b => crossSign ψ G ζ b < 0), crossMass ψ G ζ b := by
    have hfeq : (Finset.univ.filter (fun b => ¬ (0 ≤ crossSign ψ G ζ b)))
        = Finset.univ.filter (fun b => crossSign ψ G ζ b < 0) := by
      apply Finset.filter_congr
      intro b _
      simp [not_le]
    rw [hfeq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [crossMass_eq_abs_crossSign G hG, abs_of_neg hb.2, neg_neg]
  rw [hposset, hnegset]
  ring

/-- **The halving law.** For a negation-closed `G` with disjoint dilate, the doubling cross-mass
equals the cancelling cross-mass: `plusMass = minusMass`. (From `sign_balance_zero`: the signed sum,
which equals `plusMass − minusMass`, is `0`.) -/
theorem plusMass_eq_minusMass {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    plusMass ψ G ζ = minusMass ψ G ζ := by
  have hzero : (∑ b : F, crossSign ψ G ζ b) = 0 := sign_balance_zero hψ G hG hdisj
  have heq := signedSum_eq_plus_sub_minus (ψ := ψ) G hG ζ
  rw [hzero] at heq
  linarith [heq]

omit [DecidableEq F] in
/-- The total absolute cross-mass is the sum of the doubling and cancelling masses. -/
theorem total_eq_plus_add_minus {ψ : AddChar F ℂ} (G : Finset F) (ζ : F) :
    (∑ b : F, crossMass ψ G ζ b) = plusMass ψ G ζ + minusMass ψ G ζ := by
  classical
  unfold plusMass minusMass
  have hfeq : (Finset.univ.filter (fun b => ¬ (0 ≤ crossSign ψ G ζ b)))
      = Finset.univ.filter (fun b => crossSign ψ G ζ b < 0) := by
    apply Finset.filter_congr; intro b _; simp [not_le]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun b => 0 ≤ crossSign ψ G ζ b) (crossMass ψ G ζ), hfeq]

/-- The total absolute cross-mass is at most `q·|G|` (`total_doublingMass_le` repackaged). -/
theorem totalCrossMass_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) :
    (∑ b : F, crossMass ψ G ζ b) ≤ (Fintype.card F : ℝ) * G.card :=
  total_doublingMass_le hψ G hζ

/-- **The doubling-mass cap.** Along a genuine disjoint tower step (`negation-closed G`, `ζ ≠ 0`,
`Disjoint G (dilate ζ G)`), the L²-weighted mass of the **doubling** (same-sign) frequencies is at
most **half** the second moment: `plusMass ≤ ½·q·|G|`.

This discharges the quantitative claim asserted (but not proven) in `DilationRealSignCocycle`'s
`total_doublingMass_le` doc-comment. The trivial `2·M` scaling at the step can only be carried by a
bounded total mass of frequencies — at most half — not by all of them. -/
theorem plusMass_le_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    plusMass ψ G ζ ≤ (Fintype.card F : ℝ) * G.card / 2 := by
  have hpm : plusMass ψ G ζ = minusMass ψ G ζ := plusMass_eq_minusMass hψ G hG hdisj
  have htot : (∑ b : F, crossMass ψ G ζ b) = plusMass ψ G ζ + minusMass ψ G ζ :=
    total_eq_plus_add_minus G ζ
  have hle : (∑ b : F, crossMass ψ G ζ b) ≤ (Fintype.card F : ℝ) * G.card :=
    totalCrossMass_le hψ G hζ
  -- total = 2·plusMass ≤ qG ⟹ plusMass ≤ qG/2
  rw [htot, ← hpm] at hle
  linarith [hle]

/-- Corollary: the cancelling (`−`-sign) cross-mass is likewise at most `½·q·|G|`. -/
theorem minusMass_le_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    minusMass ψ G ζ ≤ (Fintype.card F : ℝ) * G.card / 2 := by
  have hpm : plusMass ψ G ζ = minusMass ψ G ζ := plusMass_eq_minusMass hψ G hG hdisj
  have := plusMass_le_half_card hψ G hG hζ hdisj
  rw [hpm] at this
  exact this

#print axioms ProximityGap.SubgroupGaussSumSecondMoment.plusMass_le_half_card
#print axioms ProximityGap.SubgroupGaussSumSecondMoment.plusMass_eq_minusMass

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
