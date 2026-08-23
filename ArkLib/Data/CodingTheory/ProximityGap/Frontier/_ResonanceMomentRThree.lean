/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The `r = 3` rung of the resonance moment (#407 / #444)

Extends `GaussPhaseResonance` and the `r = 1` (`_ResonanceMomentBaseCase`, `T 1 = m-1`) and
`r = 2` (`_ResonanceMomentRTwo` / `_ResonanceMomentRTwoBounds`, `(m-1)² ≤ T 2 ≤ m(m-1)²`) rungs.
This file supplies the NEXT rung `r = 3`, the first ODD non-trivial phase-sum: a double restricted
convolution of the unit phases.

## The convolution collapse

> `phaseSum u 3 c = ∑_{a≠0, b≠0, c-a-b≠0} u(a) u(b) u(c-a-b)`.

The depth-3 phase-sum is the off-diagonal triple convolution at `c`, ranging over the pairs
`(a, b)` with all three of `a`, `b`, `c-a-b` nonzero. The exact `r = 3` analogue of the `r = 2`
`phaseSum_two` collapse (reindex the `Fin 3 → ZMod m` filter by its first two coordinates).

## The trivial L∞ / L² bounds

For a unit-phase vector (`‖u l‖ = 1`, the Gauss-sum normalisation `u_l = τ(χ^l)/√p`):

* `phaseSum_three_norm_le` — per-frequency L∞ ceiling `‖phaseSum u 3 c‖ ≤ (m-1)²`
  (triangle inequality on at most `(m-1)²` unit triples).
* `resonanceMoment_three_le` — aggregate L² ceiling `T 3 ≤ m·(m-1)⁴`.

## Honest scope

Unlike `r = 2` there is NO clean conjugate-symmetric diagonal value: `r = 3` is odd, so the three
residues cannot pair up antipodally and `phaseSum u 3 0` has no closed form (probe-confirmed: it
fluctuates in sign and magnitude, no `m-1`-type law). So this file supplies only the UPPER bounds
(the trivial triangle route), not a matching lower bound. Probe truth: `T 3 = Θ(m³)`, sitting FAR
below the `m(m-1)⁴` trivial ceiling and far below the conjecture ceiling `(2 m log m)³`
(`T 3/(2m log m)³ ≈ 0.02–0.06`, decreasing) — i.e. the off-diagonal triple convolution has strong
cancellation that the triangle bound cannot see. Closing that gap is the same L²→L∞ sup-norm wall.

NO CORE / cancellation / completion / moment-saving / anti-concentration / capacity claim.
CORE `M(μ_n) ≤ C √(n log m)` UNCHANGED / OPEN. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The `r = 3` filter membership criterion: `X : Fin 3 → ZMod m` lies in the phase-sum filter at
`c` iff all three entries are nonzero and `X 0 + X 1 + X 2 = c`. -/
theorem mem_phaseSum_three_filter (c : ZMod m) (X : Fin 3 → ZMod m) :
    (X ∈ (Finset.univ.filter (fun X : Fin 3 → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))) ↔
      (X 0 ≠ 0 ∧ X 1 ≠ 0 ∧ X 2 ≠ 0 ∧ X 0 + X 1 + X 2 = c) := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hsum⟩
    refine ⟨hne 0, hne 1, hne 2, ?_⟩
    simpa [Fin.sum_univ_three] using hsum
  · rintro ⟨h0, h1, h2, hsum⟩
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · simpa [Fin.sum_univ_three] using hsum

/-- **`phaseSum u 3 c = ∑_{a≠0, b≠0, c-a-b≠0} u(a) u(b) u(c-a-b)`.** The depth-3 phase-sum is the
off-diagonal triple convolution of the unit phases at `c`. -/
theorem phaseSum_three (u : ZMod m → ℂ) (c : ZMod m) :
    phaseSum u 3 c =
      ∑ p ∈ (Finset.univ : Finset (ZMod m × ZMod m)).filter
          (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ c - p.1 - p.2 ≠ 0),
        u p.1 * u p.2 * u (c - p.1 - p.2) := by
  classical
  unfold phaseSum
  refine Finset.sum_nbij' (fun X => (X 0, X 1)) (fun p => ![p.1, p.2, c - p.1 - p.2]) ?_ ?_ ?_ ?_ ?_
  · -- maps into the target filter
    intro X hX
    rw [mem_phaseSum_three_filter] at hX
    obtain ⟨h0, h1, h2, hsum⟩ := hX
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, h0, h1, ?_⟩
    have : c - X 0 - X 1 = X 2 := by rw [← hsum]; ring
    rw [this]; exact h2
  · -- inverse maps back into the source filter
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, h0, h1, h2⟩ := hp
    rw [mem_phaseSum_three_filter]
    refine ⟨by simpa using h0, by simpa using h1, ?_, ?_⟩
    · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact h2
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring
  · -- left inverse
    intro X hX
    rw [mem_phaseSum_three_filter] at hX
    obtain ⟨_, _, _, hsum⟩ := hX
    funext i
    fin_cases i
    · rfl
    · rfl
    · show c - X 0 - X 1 = X 2
      rw [← hsum]; ring
  · -- right inverse
    intro p _
    simp
  · -- the summand matches
    intro X hX
    rw [mem_phaseSum_three_filter] at hX
    obtain ⟨_, _, _, hsum⟩ := hX
    have : X 2 = c - X 0 - X 1 := by rw [← hsum]; ring
    rw [Fin.prod_univ_three, this, mul_assoc]

/-- **Per-frequency L∞ ceiling: `‖phaseSum u 3 c‖ ≤ (m-1)²`.** For a unit-phase vector the depth-3
phase-sum at any `c` is the off-diagonal triple convolution of at most `(m-1)²` unit terms (the pair
`(a, b)` ranges over a subset of `{a≠0}×{b≠0}`). -/
theorem phaseSum_three_norm_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (c : ZMod m) :
    ‖phaseSum u 3 c‖ ≤ ((m : ℝ) - 1) ^ 2 := by
  classical
  rw [phaseSum_three]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (ZMod m × ZMod m)).filter
      (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ c - p.1 - p.2 ≠ 0),
      ‖u p.1 * u p.2 * u (c - p.1 - p.2)‖ = 1 := by
    intro p _
    rw [norm_mul, norm_mul, hu p.1, hu p.2, hu (c - p.1 - p.2)]; norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the filtered set is a subset of {a≠0} ×ˢ {b≠0}, card ≤ (m-1)²
  have hsub : ((Finset.univ : Finset (ZMod m × ZMod m)).filter
      (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ c - p.1 - p.2 ≠ 0)) ⊆
      ((Finset.univ.filter (fun a : ZMod m => a ≠ 0)) ×ˢ
       (Finset.univ.filter (fun b : ZMod m => b ≠ 0))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, h0, h1, _⟩ := hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, h0⟩, ⟨Finset.mem_univ _, h1⟩⟩
  have hcardle := Finset.card_le_card hsub
  have hcard0 : (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  rw [Finset.card_product, hcard0] at hcardle
  have hm : 1 ≤ m := NeZero.one_le
  calc (((Finset.univ : Finset (ZMod m × ZMod m)).filter
          (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ c - p.1 - p.2 ≠ 0)).card : ℝ)
      ≤ (((m - 1) * (m - 1) : ℕ) : ℝ) := by exact_mod_cast hcardle
    _ = ((m : ℝ) - 1) ^ 2 := by push_cast [Nat.cast_sub hm]; ring

/-- **Aggregate L² ceiling: `T 3 = resonanceMoment u 3 ≤ m · (m-1)⁴`.** Squaring the per-frequency
ceiling `‖phaseSum u 3 c‖ ≤ (m-1)²` and summing over the `m` frequencies. Probe truth `T 3 = Θ(m³)`
sits FAR below this trivial ceiling (the triangle bound is loose by the off-diagonal cancellation;
closing the gap is the open prize sup-norm wall). -/
theorem resonanceMoment_three_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    resonanceMoment u 3 ≤ (m : ℝ) * ((m : ℝ) - 1) ^ 4 := by
  classical
  unfold resonanceMoment
  have hbd : ∀ c : ZMod m, ‖phaseSum u 3 c‖ ^ 2 ≤ (((m : ℝ) - 1) ^ 2) ^ 2 := by
    intro c
    have h1 := phaseSum_three_norm_le u hu c
    have h0 : (0 : ℝ) ≤ ‖phaseSum u 3 c‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  calc ∑ c : ZMod m, ‖phaseSum u 3 c‖ ^ 2
      ≤ ∑ _c : ZMod m, (((m : ℝ) - 1) ^ 2) ^ 2 := Finset.sum_le_sum (fun c _ => hbd c)
    _ = (Finset.univ.card : ℝ) * (((m : ℝ) - 1) ^ 2) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) * ((m : ℝ) - 1) ^ 4 := by
        rw [Finset.card_univ, ZMod.card]; ring

/-- **Trivial `r = 3` bracket.**  The odd third resonance rung is a nonnegative quadratic form and
is bounded above by the triangle-count ceiling.  This deliberately records only the bookkeeping
bracket: the measured `Θ(m³)` cancellation and the conjectural `(2m log m)³` scale remain open and
are not claimed here. -/
theorem resonanceMoment_three_bracket (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    0 ≤ resonanceMoment u 3 ∧ resonanceMoment u 3 ≤ (m : ℝ) * ((m : ℝ) - 1) ^ 4 :=
  ⟨resonanceMoment_nonneg u 3, resonanceMoment_three_le u hu⟩

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_three
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_three_norm_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_three_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_three_bracket
