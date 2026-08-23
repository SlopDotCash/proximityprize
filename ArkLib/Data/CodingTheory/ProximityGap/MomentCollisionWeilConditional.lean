/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionSpectral
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — the conditional Weil bridge: a per-character energy bound SUFFICES for M2
# anti-concentration.

`MomentCollisionSpectral.lean` proved the Plancherel identity `collision · |A| = ∑_ψ ‖Tψ‖²` and
isolated the off-diagonal `∑_{ψ ≠ 0} ‖Tψ‖²` as the open "Weil" magnitude. This file closes the
reduction **modulo that one analytic input**: it shows a uniform bound on the *per-character* energy
`‖Tψ‖²` (`ψ ≠ 0`) — exactly what a subgroup-restricted Weil/Riemann-hypothesis-for-curves estimate
would supply — yields the M2 anti-concentration the prize needs.

## Main results

* `plancherel_collision_real` — the Plancherel identity over `ℝ`: `collision · |A| = ∑_ψ ‖Tψ‖²`.
* `collision_le_of_offDiagonal_bound` — **the conditional bridge.** If `‖Tψ‖² ≤ B` for every `ψ ≠ 0`,
  then `M2 · |A| ≤ C(|G|,a)² + (|A| − 1)·B`. The open analytic input is isolated as the single
  hypothesis `hB`; everything else is the proven Plancherel arithmetic.
* `collision_le_of_relative_bound` — **the prize-survival form.** If `‖Tψ‖² ≤ ε·C(|G|,a)²` for every
  `ψ ≠ 0`, then `M2 ≤ C(|G|,a)²/|A| + ε·C(|G|,a)²` — `M2` is anti-concentrated (the prize-favourable
  regime) whenever `1/|A|` and `ε` are small. This is the exact statement of how a Weil-type
  cancellation bound on the subgroup character sums pins `M2`.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). The theorems are unconditional
*given* the per-character energy hypothesis; they do **not** establish that hypothesis — the
subgroup-restricted partial quadratic character-sum bound (Weil-on-curves) is the open input, absent
from Mathlib. What is new is the proof that this single input *suffices*: the prize reduction is now
complete modulo exactly one named analytic fact.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset Complex BigOperators
open ArkLib.ProximityGap.MomentCollisionSpectral

namespace ArkLib.ProximityGap.MomentCollisionWeilConditional

variable {F : Type*} [DecidableEq F]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The real-valued Plancherel identity: `collision · |A| = ∑_ψ ‖Tψ‖²` over `ℝ`. -/
theorem plancherel_collision_real (G : Finset F) (a : ℕ) (stat : Finset F → A) :
    (collision G a stat : ℝ) * (Fintype.card A : ℝ)
      = ∑ ψ : AddChar A ℂ, Complex.normSq (charSum G a stat ψ) := by
  have hC := plancherel_collision G a stat
  have : ((collision G a stat : ℝ) * (Fintype.card A : ℝ) : ℂ)
      = ((∑ ψ : AddChar A ℂ, Complex.normSq (charSum G a stat ψ) : ℝ) : ℂ) := by
    push_cast
    rw [hC]
  exact_mod_cast this

/-- **The conditional Weil bridge.** If every nontrivial Fourier coefficient has bounded energy
`‖Tψ‖² ≤ B` (`ψ ≠ 0`) — exactly the subgroup-restricted Weil estimate the prize is missing — then the
moment-collision scalar obeys

  `M2 · |A|  ≤  C(|G|,a)²  +  (|A| − 1) · B`.

So a per-character energy bound `B` *suffices* to pin `M2` near its anti-concentration floor: the open
analytic input is isolated as the single hypothesis `hB`, and the reduction is complete modulo it. -/
theorem collision_le_of_offDiagonal_bound (G : Finset F) (a : ℕ) (stat : Finset F → A) (B : ℝ)
    (hB : ∀ ψ : AddChar A ℂ, ψ ≠ 0 → Complex.normSq (charSum G a stat ψ) ≤ B) :
    (collision G a stat : ℝ) * (Fintype.card A : ℝ)
      ≤ ((G.powersetCard a).card : ℝ) ^ 2 + ((Fintype.card A : ℝ) - 1) * B := by
  rw [plancherel_collision_real]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : AddChar A ℂ))]
  rw [normSq_charSum_zero G a stat]
  have hbound :
      ∑ ψ ∈ Finset.univ.erase (0 : AddChar A ℂ), Complex.normSq (charSum G a stat ψ)
        ≤ (Finset.univ.erase (0 : AddChar A ℂ)).card • B :=
    Finset.sum_le_card_nsmul _ _ B (fun ψ hψ => hB ψ (Finset.ne_of_mem_erase hψ))
  have hcard : (Finset.univ.erase (0 : AddChar A ℂ)).card = Fintype.card A - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq]
  have hpos : 1 ≤ Fintype.card A := Fintype.card_pos
  have hcast : ((Fintype.card A - 1 : ℕ) : ℝ) = (Fintype.card A : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; norm_num
  rw [hcard, nsmul_eq_mul, hcast] at hbound
  linarith [hbound]

/-- **Corollary (prize-survival form).** If the per-character energy is `B = ε · C(|G|,a)²` for a small
`ε`, then `M2 ≤ (1/|A| + ε) · C(|G|,a)²` — anti-concentrated whenever `ε` and `1/|A|` are small. The
exact statement of how a Weil-type cancellation bound yields the prize-favourable regime. -/
theorem collision_le_of_relative_bound (G : Finset F) (a : ℕ) (stat : Finset F → A) (ε : ℝ)
    (hq : 0 < Fintype.card A) (hε : 0 ≤ ε)
    (hB : ∀ ψ : AddChar A ℂ, ψ ≠ 0 →
        Complex.normSq (charSum G a stat ψ) ≤ ε * ((G.powersetCard a).card : ℝ) ^ 2) :
    (collision G a stat : ℝ)
      ≤ ((G.powersetCard a).card : ℝ) ^ 2 / (Fintype.card A : ℝ)
        + ε * ((G.powersetCard a).card : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hq
  have hmain := collision_le_of_offDiagonal_bound G a stat
    (ε * ((G.powersetCard a).card : ℝ) ^ 2) hB
  have hCnn : (0 : ℝ) ≤ ((G.powersetCard a).card : ℝ) ^ 2 := by positivity
  have heq : ((G.powersetCard a).card : ℝ) ^ 2 / (Fintype.card A : ℝ)
        + ε * ((G.powersetCard a).card : ℝ) ^ 2
      = (((G.powersetCard a).card : ℝ) ^ 2
          + ε * ((G.powersetCard a).card : ℝ) ^ 2 * (Fintype.card A : ℝ)) / (Fintype.card A : ℝ) := by
    field_simp
  rw [heq, le_div_iff₀ hqR]
  have hstep : ((Fintype.card A : ℝ) - 1) * (ε * ((G.powersetCard a).card : ℝ) ^ 2)
      ≤ ε * ((G.powersetCard a).card : ℝ) ^ 2 * (Fintype.card A : ℝ) := by
    nlinarith [mul_nonneg hε hCnn, hqR]
  linarith [hmain, hstep]

end ArkLib.ProximityGap.MomentCollisionWeilConditional

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionWeilConditional.plancherel_collision_real
#print axioms ArkLib.ProximityGap.MomentCollisionWeilConditional.collision_le_of_offDiagonal_bound
#print axioms ArkLib.ProximityGap.MomentCollisionWeilConditional.collision_le_of_relative_bound
