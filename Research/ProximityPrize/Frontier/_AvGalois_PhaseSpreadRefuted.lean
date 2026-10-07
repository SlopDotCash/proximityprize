/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Research.ProximityPrize.Frontier._AvGalois_StickelbergerPhaseDescent

/-!
# The abstract Galois phase-spread residual is false (machine-checked refutation)

`_AvGalois_StickelbergerPhaseDescent.lean` records the Paley/BGK reduction's named residual
`GaloisPhaseSpreadResidual`, whose docstring states it "is FALSE for arbitrary `v` (no
concentration)". This file machine-checks that claim, and strengthens it: the abstract
implication cannot hold for **any** constant, because the RMS identity alone permits a
one-point mass whose max/RMS ratio grows without bound.

## What is refuted

`GaloisPhaseSpreadResidual m n v C` asserts that the Plancherel identity `Σ vᵢ² = m·n` alone
forces the orbit maximum below `C·√(n·log m)`. The constant family `v ≡ 1` at `(m, n, C) =
(2, 1, 1)` satisfies the identity but violates the bound (`log 2 < 1`), and the one-point-mass
family `v 0 = √m`, `v i = 0` otherwise, with `n = 1`, satisfies the identity while its maximum
`√m` eventually exceeds `C·√(log m)` for every real `C`.

## Consequence for the reduction

The lane's honest statement ("Galois/Stickelberger pins the RMS and is blind to the phase
anti-correlation") is therefore not merely informal: no constant makes the recorded
implication hold uniformly over all dimensions and RMS-normalised families. Any future closure
must quantify over the actual `η` orbit family rather than an arbitrary RMS-normalised
`v : Fin m → ℝ`; the abstract implication carries no concentration
information.

All results below are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only; no
`sorryAx`).
-/

namespace ArkLib.ProximityGap.GaloisStickelberger

open Finset

/-- **Concrete counterexample: the residual is false at `(m, n, C) = (2, 1, 1)`.**

The constant family `v ≡ 1` satisfies the Plancherel identity `Σ vᵢ² = 2 = m·n`, but its
orbit maximum `1` exceeds `1·√(1·log 2)`, since `log 2 < 1`. -/
theorem not_galoisPhaseSpreadResidual_at_two :
    ¬ GaloisPhaseSpreadResidual 2 1 (fun _ => (1 : ℝ)) 1 := by
  intro h
  have hRMS : GaloisOrbitRMS 2 1 (fun _ => (1 : ℝ)) := by
    unfold GaloisOrbitRMS
    norm_num [Fin.sum_univ_two]
  have hb := h hRMS 0
  push_cast at hb
  simp only [one_mul] at hb
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    linarith
  have hsqrt : Real.sqrt (Real.log 2) < 1 := by
    rw [Real.sqrt_lt (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using hlog2
  linarith

/-- For every real `C` there is a natural `m ≥ 2` with `C²·log m < m`.

This is the arithmetic core of the refutation: `log` is little-o of the identity, so the
linear-in-`log` budget is eventually beaten by `m` itself. -/
theorem exists_sq_log_lt_self (C : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ C ^ 2 * Real.log (m : ℝ) < (m : ℝ) := by
  have hε : (0 : ℝ) < 1 / (max (C ^ 2) 1 + 1) := by positivity
  have hnatO : (fun n : ℕ => Real.log (n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hnat : ∀ᶠ n : ℕ in Filter.atTop, C ^ 2 * Real.log (n : ℝ) < (n : ℝ) := by
    have hb := hnatO.def hε
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hn1'
    have hlogx : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
    rw [Real.norm_eq_abs, abs_of_nonneg hlogx, Real.norm_eq_abs,
      abs_of_nonneg hnpos] at hn
    have hC2 : C ^ 2 ≤ max (C ^ 2) 1 := le_max_left _ _
    have hden : (0 : ℝ) < max (C ^ 2) 1 + 1 := by positivity
    have hfrac : max (C ^ 2) 1 / (max (C ^ 2) 1 + 1) < 1 := by
      rw [div_lt_one hden]; linarith
    calc C ^ 2 * Real.log (n : ℝ)
        ≤ max (C ^ 2) 1 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hC2 hlogx
      _ ≤ max (C ^ 2) 1 * ((1 / (max (C ^ 2) 1 + 1)) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (max (C ^ 2) 1 / (max (C ^ 2) 1 + 1)) * (n : ℝ) := by ring
      _ < 1 * (n : ℝ) := mul_lt_mul_of_pos_right hfrac (lt_of_lt_of_le zero_lt_one hn1')
      _ = (n : ℝ) := one_mul _
  obtain ⟨m, hm⟩ := (hnat.and (Filter.eventually_ge_atTop 2)).exists
  exact ⟨m, hm.2, hm.1⟩

/-- **No constant works: the abstract residual fails for every `C`.**

For each real `C` there is an RMS-normalised family whose orbit maximum exceeds
`C·√(n·log m)`. The witness is a one-point mass at `n = 1`: with `m ≥ 2` chosen so that
`C²·log m < m`, the family `v 0 = √m`, `v i = 0` otherwise, satisfies `Σ vᵢ² = m = m·n`
while `v 0 = √m > C·√(log m)`. -/
theorem not_galoisPhaseSpreadResidual_for_any_constant (C : ℝ) :
    ∃ (m n : ℕ) (v : Fin m → ℝ),
      GaloisOrbitRMS m n v ∧
        ¬ (∀ i, v i ≤ C * Real.sqrt ((n : ℝ) * Real.log (m : ℝ))) := by
  obtain ⟨m, hm2, hmlog⟩ := exists_sq_log_lt_self C
  haveI : NeZero m := ⟨by omega⟩
  refine ⟨m, 1, fun i => if i = 0 then Real.sqrt (m : ℝ) else 0, ?_, ?_⟩
  · have hsum :
        (∑ i : Fin m, (if i = 0 then Real.sqrt (m : ℝ) else 0) ^ 2) = (m : ℝ) := by
      rw [Finset.sum_eq_single 0]
      · simp [Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) by positivity)]
      · intro b _ hb; simp [if_neg hb]
      · intro h; exact absurd (Finset.mem_univ 0) h
    unfold GaloisOrbitRMS
    rw [hsum]; norm_num
  · intro h
    have hb := h 0
    simp only [if_true, Nat.cast_one, one_mul] at hb
    have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have hsqrtpos : 0 < Real.sqrt (Real.log (m : ℝ)) := Real.sqrt_pos.mpr hlogpos
    have hCnn : 0 ≤ C := by
      by_contra hc
      rw [not_le] at hc
      have hneg : C * Real.sqrt (Real.log (m : ℝ)) < 0 :=
        mul_neg_of_neg_of_pos hc hsqrtpos
      have hnn : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
      linarith
    have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤ (C * Real.sqrt (Real.log (m : ℝ))) ^ 2 := by
      simpa only [sq] using mul_self_le_mul_self (Real.sqrt_nonneg _) hb
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) by positivity), mul_pow,
      Real.sq_sqrt (le_of_lt hlogpos)] at hsq
    nlinarith [hmlog, hsq]

end ArkLib.ProximityGap.GaloisStickelberger

/-! ## Axiom audit — must show exactly `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.GaloisStickelberger.not_galoisPhaseSpreadResidual_at_two
#print axioms ArkLib.ProximityGap.GaloisStickelberger.exists_sq_log_lt_self
#print axioms ArkLib.ProximityGap.GaloisStickelberger.not_galoisPhaseSpreadResidual_for_any_constant
