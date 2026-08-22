/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification
import Mathlib.Algebra.Order.Chebyshev

/-!
# Depth-6 amplified no-go: the coset-amplified threshold is EXACTLY depth 7 — #466

`_BGKCosetAmplification` lowered the sufficiency threshold to depth 7
(`E₇ ≤ 2¹⁸·n⁷ ⟹ M ≤ 2⁵¹`). This file proves the matching lower bound: even WITH the
factor-`n` coset amplification, the depth-6 certificate can never reach the nine-bit target.

The amplified depth-6 tool is `n·max‖η‖¹² ≤ ∑_{b≠0}‖η_b‖¹²`; it certifies `M ≤ 2⁵¹` only if
`∑_{b≠0}‖η_b‖¹² ≤ n·(2⁵¹)⁶ = 2³³⁶`. But Parseval + Jensen force the opposite, for EVERY
`G` of production size (no structure needed):

* off-zero Parseval (landed): `∑_{b≠0}‖η_b‖² = n(q−n)` exactly;
* Jensen (`pow_sum_le_card_mul_sum_pow`): `(∑‖η‖²)⁶ ≤ (q−1)⁵·∑‖η‖¹²`;
* arithmetic at `n = 2³⁰`, `q ≥ 2¹⁵⁸`: `∑_{b≠0}‖η_b‖¹² ≥ n⁶(q−n)⁶/q⁵ ≥ n⁶·q/2 ≥ 2³³⁷ > 2³³⁶`.

So `depthSix_amplified_noGo`: `n·(2⁵¹)⁶ < ∑_{b≠0}‖η_b‖¹²` always. Combined with
`depthSeven_amplified_closes`, the coset-amplified moment ladder's threshold for the
nine-bit target is EXACTLY depth 7 — the open input `E₇(μ_n) ≤ 2¹⁸·n⁷` is the sharp form.
Nothing here discharges it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024
set_option maxRecDepth 16384

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower

namespace ArkLib.ProximityGap.Frontier.BGKDepthSixAmplifiedNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The depth-6 amplified certificate floor**: for ANY `G` of production size
(`|G| = 2³⁰`, `q ≥ 2¹⁵⁸`) and primitive `ψ`, the off-zero twelfth-moment mass exceeds the
certification budget `n·(2⁵¹)⁶`:

  `2³³⁶ = n·(2⁵¹)⁶ < ∑_{b≠0} ‖η_b‖¹²`.

Hence the coset-amplified depth-6 moment tool can NEVER certify `M ≤ 2⁵¹` — depth 7 is the
exact amplified threshold. Pure Parseval + Jensen; no structural hypothesis on `G`. -/
theorem depthSix_amplified_noGo {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) * ((2 : ℝ) ^ 51) ^ 6
      < ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 12 := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hnval : n = (2 : ℝ) ^ 30 := by rw [hndef, hcard]; norm_num
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  -- Jensen: `(∑‖η‖²)⁶ ≤ (q−1)⁵ · ∑ (‖η‖²)⁶`.
  have hjensen : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2) ^ 6
      ≤ ((Finset.univ.erase (0 : F)).card : ℝ) ^ 5
        * ∑ b ∈ Finset.univ.erase (0 : F), (‖eta ψ G b‖ ^ 2) ^ 6 := by
    simpa using _root_.pow_sum_le_card_mul_sum_pow
      (s := Finset.univ.erase (0 : F)) (f := fun b => ‖eta ψ G b‖ ^ 2)
      (fun b _ => sq_nonneg _) 5
  -- exact Parseval mass on the left.
  have hpars := offZero_secondMoment hψ G
  -- card of the punctured frequency set is `q − 1 ≤ q`.
  have hcard_erase : ((Finset.univ.erase (0 : F)).card : ℝ) ≤ q := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have h1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
      have := Fintype.card_pos (α := F)
      exact_mod_cast this
    push_cast [Nat.cast_sub (Fintype.card_pos (α := F))]
    linarith
  have hcard_nn : (0 : ℝ) ≤ ((Finset.univ.erase (0 : F)).card : ℝ) := by positivity
  set S : ℝ := ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 12 with hSdef
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun b _ => by positivity)
  have hpow12 : ∑ b ∈ Finset.univ.erase (0 : F), (‖eta ψ G b‖ ^ 2) ^ 6 = S := by
    rw [hSdef]
    exact Finset.sum_congr rfl (fun b _ => by rw [← pow_mul])
  -- combine: `(n(q−n))⁶ ≤ q⁵·S`.
  have hkey : (n * (q - n)) ^ 6 ≤ q ^ 5 * S := by
    have hL : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 = n * (q - n) := by
      rw [hpars]; ring
    rw [hL, hpow12] at hjensen
    calc (n * (q - n)) ^ 6
        ≤ ((Finset.univ.erase (0 : F)).card : ℝ) ^ 5 * S := hjensen
      _ ≤ q ^ 5 * S := by
          have h5 : ((Finset.univ.erase (0 : F)).card : ℝ) ^ 5 ≤ q ^ 5 :=
            pow_le_pow_left₀ hcard_nn hcard_erase 5
          exact mul_le_mul_of_nonneg_right h5 hS_nn
  -- `q − n ≥ (255/256)·q` since `n = 2³⁰ ≤ q/256`.
  have hqn : q * (255 / 256) ≤ q - n := by
    have hn_small : n ≤ q / 256 := by
      rw [hnval]
      have : (2 : ℝ) ^ 30 ≤ (2 : ℝ) ^ 158 / 256 := by norm_num
      linarith
    linarith
  -- hence `2·(q−n)⁶ ≥ q⁶`  (since `2·(255/256)⁶ > 1`).
  have hx6 : q ^ 6 ≤ 2 * (q - n) ^ 6 := by
    have hqn_nn : (0 : ℝ) ≤ q * (255 / 256) := by positivity
    have h6 : (q * (255 / 256)) ^ 6 ≤ (q - n) ^ 6 := pow_le_pow_left₀ hqn_nn hqn 6
    have hconst : q ^ 6 ≤ 2 * (q * (255 / 256)) ^ 6 := by
      have hexpand : 2 * (q * (255 / 256)) ^ 6 = q ^ 6 * (2 * (255 / 256) ^ 6) := by ring
      rw [hexpand]
      have : (1 : ℝ) ≤ 2 * (255 / 256) ^ 6 := by norm_num
      nlinarith [pow_nonneg (le_of_lt hq0) 6]
    linarith
  -- floor: `S ≥ n⁶·q/2`, i.e. `2·q⁵·S ≥ n⁶·q⁶`.
  have hfloor : n ^ 6 * q ^ 6 ≤ 2 * (q ^ 5 * S) := by
    have h1 : n ^ 6 * q ^ 6 ≤ n ^ 6 * (2 * (q - n) ^ 6) := by
      have hn6 : (0 : ℝ) ≤ n ^ 6 := by positivity
      exact mul_le_mul_of_nonneg_left hx6 hn6
    have h2 : n ^ 6 * (2 * (q - n) ^ 6) = 2 * (n * (q - n)) ^ 6 := by ring
    have h3 : 2 * (n * (q - n)) ^ 6 ≤ 2 * (q ^ 5 * S) := by linarith [hkey]
    linarith
  -- numeric finish: `n·(2⁵¹)⁶ = 2³³⁶ < 2³³⁷ ≤ n⁶·q/2 ≤ S`.
  have hSlow : n ^ 6 * q ≤ 2 * S := by
    have hq5 : (0 : ℝ) < q ^ 5 := by positivity
    nlinarith [hfloor, hq5, hS_nn]
  have hnum : n * ((2 : ℝ) ^ 51) ^ 6 * 2 < n ^ 6 * q := by
    rw [hnval]
    calc (2 : ℝ) ^ 30 * ((2 : ℝ) ^ 51) ^ 6 * 2 = (2 : ℝ) ^ 337 := by
          norm_num [← pow_mul, ← pow_add]
      _ < (2 : ℝ) ^ 338 := by
          have : (2 : ℝ) ^ 337 * 1 < (2 : ℝ) ^ 337 * 2 := by
            have : (0 : ℝ) < (2 : ℝ) ^ 337 := by positivity
            linarith
          calc (2 : ℝ) ^ 337 = (2 : ℝ) ^ 337 * 1 := by ring
            _ < (2 : ℝ) ^ 337 * 2 := this
            _ = (2 : ℝ) ^ 338 := by rw [← pow_succ]
      _ = ((2 : ℝ) ^ 30) ^ 6 * (2 : ℝ) ^ 158 := by
          norm_num [← pow_mul, ← pow_add]
      _ ≤ ((2 : ℝ) ^ 30) ^ 6 * q := by
          have h30 : (0 : ℝ) ≤ ((2 : ℝ) ^ 30) ^ 6 := by positivity
          exact mul_le_mul_of_nonneg_left hq h30
  linarith

end ArkLib.ProximityGap.Frontier.BGKDepthSixAmplifiedNoGo

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSixAmplifiedNoGo.depthSix_amplified_noGo
