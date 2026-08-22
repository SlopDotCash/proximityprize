/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentBaseCase

/-!
# Convolution submultiplicativity of the resonance phase-sum L∞ norm (#407 / #444)

Direct consequence of the EXACT convolution recursion
`phaseSum u (r+1) c = ∑_{a≠0} u(a)·phaseSum u r (c−a)` (`_ResonancePhaseSumConvolutionRecursion`):
the L∞ (sup over `c`) norm of the phase-sum is **submultiplicative under the single step**, with
the step-factor being the kernel L¹ mass `∑_{a≠0} ‖u a‖` (= `m−1` for unit phases).

> **`‖phaseSum u (r+1) c‖ ≤ (∑_{a≠0} ‖u a‖) · (⨆_d ‖phaseSum u r d‖)`** (pointwise in `c`),

hence, taking the sup over `c` and iterating,

> **`‖phaseSum u r c‖ ≤ (m−1)^{r-1}`** for unit phases (the trivial L∞ ceiling),

now derived from the recursion's submultiplicativity rather than the bespoke filter-card argument
in `_ResonanceMomentGeneralCeiling`. The two routes AGREE, locking the trivial ceiling as a genuine
fixed point of the convolution recursion (the kernel mass `m−1` is the multiplier).

## Why this is the right structural follow-on (not a re-confirmation)

The filter-card ceiling (`_ResonanceMomentGeneralCeiling.card_phaseSum_filter_le`) bounds the
COUNT; this file bounds the NORM via the recursion's convolution structure, exposing the
multiplier `m−1` as the kernel L¹ mass `K̂(0) = ∑_{a≠0}‖u a‖`. The honest constraint it makes
explicit: any improvement over `(m−1)^{r-1}` must come from CANCELLATION inside the convolution
(the kernel mass `m−1` is an L¹ quantity that ignores phase), i.e. exactly the `K̂(b)` profile at
`b≠0` (the open BGK object) and NOT the trivially-bounded `K̂(0)`. This is the door-(iv)
phase-essential content stated at the level of the recursion.

## Honest scope

CERTAIN exact consequences of the recursion (an L∞ submultiplicativity + its iterate). They do NOT
beat `(m−1)^{r-1}` — that requires bounding `K̂(b)` for `b≠0`, the open Gauss-period/BGK content.
CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **Pointwise convolution submultiplicativity of the phase-sum L∞ norm.**
`‖phaseSum u (r+1) c‖ ≤ (∑_{a≠0} ‖u a‖) · B` whenever `B` dominates every `‖phaseSum u r d‖`.
Triangle inequality on the exact recursion, bounding each `‖phaseSum u r (c−a)‖ ≤ B`. -/
theorem norm_phaseSum_succ_le (u : ZMod m → ℂ) (r : ℕ) (c : ZMod m)
    (B : ℝ) (hB : ∀ d : ZMod m, ‖phaseSum u r d‖ ≤ B) :
    ‖phaseSum u (r + 1) c‖
      ≤ (∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0), ‖u a‖) * B := by
  classical
  rw [phaseSum_succ]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro a _
  rw [norm_mul]
  have hBnn : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB (c - a))
  exact mul_le_mul_of_nonneg_left (hB (c - a)) (norm_nonneg _)

/-- **Unit-phase step factor = `m − 1`.** For unit-modulus phases the kernel L¹ mass collapses to
the count of nonzero residues, `∑_{a≠0} ‖u a‖ = m − 1`. -/
theorem kernel_l1_mass_of_unit (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    (∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0), ‖u a‖) = ((m : ℝ) - 1) := by
  classical
  rw [Finset.sum_congr rfl (fun a _ => hu a), Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  rw [hcard]
  have hm : 1 ≤ m := NeZero.one_le
  push_cast [Nat.cast_sub hm]; ring

/-- **Unit-phase pointwise submultiplicativity: `‖phaseSum u (r+1) c‖ ≤ (m−1)·B`** when `B`
dominates every depth-`r` phase-sum norm. The kernel multiplier is exactly `m − 1`. -/
theorem norm_phaseSum_succ_le_unit (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ) (c : ZMod m) (B : ℝ) (hB : ∀ d : ZMod m, ‖phaseSum u r d‖ ≤ B) :
    ‖phaseSum u (r + 1) c‖ ≤ ((m : ℝ) - 1) * B := by
  rw [← kernel_l1_mass_of_unit u hu]
  exact norm_phaseSum_succ_le u r c B hB

/-- **Recursion-driven trivial L∞ ceiling: `‖phaseSum u r c‖ ≤ (m−1)^{r-1}`** for unit phases and
`r ≥ 1`, derived purely from the convolution submultiplicativity by induction on `r`. Agrees with
`_ResonanceMomentGeneralCeiling.phaseSum_norm_le_general` (filter-card route); this is the
recursion-native derivation, exhibiting `(m−1)^{r-1}` as the iterate of the kernel multiplier. -/
theorem phaseSum_norm_le_pow_of_unit (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    ∀ (r : ℕ), 1 ≤ r → ∀ c : ZMod m, ‖phaseSum u r c‖ ≤ ((m : ℝ) - 1) ^ (r - 1) := by
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast NeZero.one_le
    linarith
  intro r
  induction r with
  | zero => intro h; omega
  | succ k ih =>
    intro _ c
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- r = 1: ‖phaseSum u 1 c‖ ≤ (m-1)^0 = 1
      subst hk
      simp only [Nat.add_sub_cancel, pow_zero]
      rw [phaseSum_one]
      by_cases hc : c = 0
      · simp [hc]
      · rw [if_neg hc, hu]
    · -- r = k+1, k ≥ 1: apply submultiplicativity with B = (m-1)^(k-1)
      have hBdom : ∀ d : ZMod m, ‖phaseSum u k d‖ ≤ ((m : ℝ) - 1) ^ (k - 1) :=
        fun d => ih hk d
      have hstep := norm_phaseSum_succ_le_unit u hu k c (((m : ℝ) - 1) ^ (k - 1)) hBdom
      refine le_trans hstep ?_
      -- (m-1) * (m-1)^(k-1) = (m-1)^k = (m-1)^((k+1)-1)
      rw [Nat.add_sub_cancel]
      have : ((m : ℝ) - 1) * ((m : ℝ) - 1) ^ (k - 1) = ((m : ℝ) - 1) ^ k := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_phaseSum_succ_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernel_l1_mass_of_unit
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_phaseSum_succ_le_unit
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_norm_le_pow_of_unit
