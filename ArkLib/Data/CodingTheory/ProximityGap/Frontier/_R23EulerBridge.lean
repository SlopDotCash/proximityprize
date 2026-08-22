/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovS2
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovAssembly

/-!
# LANE EULER (#466 round 23): the S2Output wiring — Euler-criterion bridge

The two gaps between `_R22StepanovS2.cubic_stepanov_S2` (PROVEN) and the assembly
consumer `S2Output` (`_R22StepanovAssembly.lean`) are closed here:

* **(a) SHAPE MATCH / Euler bridge.**  S2's vanishing set is the power-form
  `{s : f(s)^{(q−1)/2} = 1}`; the assembly's `NPlus` is the character-form
  `{s : χ(f(s)) = 1}`.  These are EQUAL at every odd finite field —
  `mem_nPlus_iff_pow` (both directions, via Mathlib's
  `quadraticChar_eq_pow_of_char_ne_two`); the zero fiber is excluded on both sides
  (`0^e = 0 ≠ 1` since `e ≥ 1` at odd `q ≥ 3`).  `s2Output_of_stepanov` then packages
  `cubic_stepanov_S2` verbatim into `S2Output F m Dtot` with
  `Dtot = 3(m+e) + D + q(J−1)`.
* **(b) COUNT bridge audit.**  `charSum_eq_two_nplus` needs `0, u, v` pairwise distinct
  (through `cubic_zero_count`); `S2Output` quantifies over exactly `u ≠ 0, v ≠ 0, u ≠ v`,
  so the hypotheses thread with no gap (checked; nothing to add).

Composition corollaries (generic in the parameters — the PARAM lane supplies `(m,J,D,B,k)`):
`s2OutputSized_of_params` and the end-to-end
`fourthMoment_quadChar_of_params` (params + scalar budget ⟹ the r=2 rung bound
`(k+4)·|G|²·q`, small fields `q ≤ k²` via the trivial branch).

Probe: `scratchpad/probe_r23_euler_pipeline.py` — `q = 13, 17, 37, 101`, ALL `(u,v)`:
Euler set equality exact, count identity `S = 2#N⁺ + 3 − q` exact, and for the best
admissible `(m,J,D)` the composed bound `S ≤ B` holds (`B/√q = 9.98 / 9.22 / 9.70 / 7.36`,
trending to the asymptotic `≈ 6.7`).  All checks pass.

## Honest scope

This file makes the pipeline fire GIVEN an admissible parameter tuple.  What it does NOT
do: choose `(m,J,D,B)` as explicit functions of `q` with the side conditions discharged
for all `q > q₀` — that scalar arithmetic (the PARAM lane) is the sole remaining input to
an unconditional `LegendreCubicHasseC F K`.  No closure claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R23EulerBridge

open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge
open ArkLib.ProximityGap.Frontier.R21StepanovS1
open ArkLib.ProximityGap.Frontier.R22StepanovS2
open ArkLib.ProximityGap.Frontier.R22StepanovAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The Euler-criterion bridge (both directions) -/

/-- **The Euler bridge**: at odd `q`, the character-form positive set (`NPlus`, the
assembly's object) IS the power-form positive fiber (`cubic_stepanov_S2`'s vanishing
set): `χ(f(a)) = 1 ↔ f(a)^{(q−1)/2} = 1`.  The zero fiber is excluded on both sides. -/
theorem mem_nPlus_iff_pow (hF : ringChar F ≠ 2) (hq_odd : Odd (Fintype.card F))
    (u v a : F) :
    a ∈ NPlus u v ↔ ((cubic u v).eval a) ^ ((Fintype.card F - 1) / 2) = 1 := by
  have hcard3 : 3 ≤ Fintype.card F := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rcases hq_odd with ⟨t, ht⟩
    omega
  have hexp : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rcases hq_odd with ⟨t, ht⟩
    omega
  have he_pos : 0 < (Fintype.card F - 1) / 2 := by omega
  rw [cubic_eval]
  set x : F := a * ((a - u) * (a - v)) with hx
  constructor
  · intro ha
    have hχ : quadraticChar F x = 1 := by
      simpa [NPlus, hx] using ha
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0] at hχ
      simp at hχ
    have := quadraticChar_eq_pow_of_char_ne_two hF hx0
    rw [hχ] at this
    by_cases hpow : x ^ (Fintype.card F / 2) = 1
    · rwa [hexp] at hpow
    · rw [if_neg hpow] at this
      norm_num at this
  · intro hpow
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_pow he_pos.ne'] at hpow
      exact zero_ne_one hpow
    have hpow' : x ^ (Fintype.card F / 2) = 1 := by rwa [hexp]
    have hχ : quadraticChar F x = 1 := by
      rw [quadraticChar_eq_pow_of_char_ne_two hF hx0, if_pos hpow']
    simp only [NPlus, mem_filter, mem_univ, true_and]
    exact hχ

/-! ## 2. S2 packaged into the assembly interface `S2Output` -/

/-- **The shape match (gap (a) closed)**: `cubic_stepanov_S2`'s output, transported along
the Euler bridge, IS `S2Output F m Dtot` with `Dtot = 3(m+e) + D + q(J−1)`. -/
theorem s2Output_of_stepanov (hF : ringChar F ≠ 2) (hq_odd : Odd (Fintype.card F))
    {m J D : ℕ} (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1))) :
    S2Output F m
      (3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1)) := by
  intro u v hu hv huv
  obtain ⟨P, hP0, hPdeg, hPvan⟩ := cubic_stepanov_S2 hq_odd hu hv huv hJ hme hD hcount
  refine ⟨P, hP0, ?_, hPdeg⟩
  intro a ha k hk
  exact hPvan a ((mem_nPlus_iff_pow hF hq_odd u v a).mp ha) k hk

/-! ## 3. The sized supply from admissible parameters (generic — PARAM lane fills in) -/

/-- Admissible S2 parameters + the scalar budget give the sized supply `S2OutputSized F K`.
The side conditions are exactly: the S2 budget (`hme`, `hD`, `hcount`), the degree/count
arithmetic (`harith`, with `Dtot = 3(m+e)+D+q(J−1)` substituted), and `B² ≤ K·q`. -/
theorem s2OutputSized_of_params (hF : ringChar F ≠ 2) (hq_odd : Odd (Fintype.card F))
    {m J D : ℕ} {K B : ℤ} (hm : 0 < m) (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1)))
    (hB0 : 0 ≤ B) (hBK : B ^ 2 ≤ K * (Fintype.card F : ℤ))
    (harith :
      2 * ((3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) : ℕ) : ℤ)
        + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ))) :
    S2OutputSized F K :=
  ⟨m, 3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1), B,
    hm, hB0, hBK, harith, s2Output_of_stepanov hF hq_odd hJ hme hD hcount⟩

/-! ## 4. End-to-end compositions -/

/-- Admissible parameters ⟹ the generic-constant Hasse bound `S² ≤ K·q`. -/
theorem legendreCubicHasseC_of_params (hF : ringChar F ≠ 2)
    (hq_odd : Odd (Fintype.card F))
    {m J D : ℕ} {K B : ℤ} (hm : 0 < m) (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1)))
    (hB0 : 0 ≤ B) (hBK : B ^ 2 ≤ K * (Fintype.card F : ℤ))
    (harith :
      2 * ((3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) : ℕ) : ℤ)
        + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ))) :
    LegendreCubicHasseC F K :=
  legendreCubicHasseC_cases hF (Or.inr
    (s2OutputSized_of_params hF hq_odd hm hJ hme hD hcount hB0 hBK harith))

/-- **END-TO-END (the lane deliverable)**: admissible S2 parameters at constant `k`
(large-`q` branch) OR `q ≤ k²` (small-`q` branch) give the r=2 rung quadratic-face
fourth-moment bound `(k+4)·|G|²·q` — zero named hypotheses beyond the parameter
arithmetic the PARAM lane discharges. -/
theorem fourthMoment_quadChar_of_params (hF : ringChar F ≠ 2)
    (hq_odd : Odd (Fintype.card F)) {k : ℤ} (hk : 1 ≤ k)
    (h : (Fintype.card F : ℤ) ≤ k ^ 2 ∨
      ∃ (m J D : ℕ) (B : ℤ), 0 < m ∧ 0 < J ∧
        m ≤ (Fintype.card F - 1) / 2 ∧
        2 * D + 3 < Fintype.card F ∧
        m * (D + 2 * m + J) < 2 * (J * (D + 1)) ∧
        0 ≤ B ∧ B ^ 2 ≤ k ^ 2 * (Fintype.card F : ℤ) ∧
        2 * ((3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) : ℕ) : ℤ)
          + 3 * (m : ℤ) ≤ (m : ℤ) * (B + (Fintype.card F : ℤ)))
    (G : Finset F) (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ ((k : ℝ) + 4) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  refine fourthMoment_quadChar_of_s2output_pipeline hF hk ?_ G hp
  rcases h with hq | ⟨m, J, D, B, hm, hJ, hme, hD, hcount, hB0, hBK, harith⟩
  · exact Or.inl hq
  · exact Or.inr (s2OutputSized_of_params hF hq_odd hm hJ hme hD hcount hB0 hBK harith)

end ArkLib.ProximityGap.Frontier.R23EulerBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R23EulerBridge.mem_nPlus_iff_pow
#print axioms ArkLib.ProximityGap.Frontier.R23EulerBridge.s2Output_of_stepanov
#print axioms ArkLib.ProximityGap.Frontier.R23EulerBridge.s2OutputSized_of_params
#print axioms ArkLib.ProximityGap.Frontier.R23EulerBridge.legendreCubicHasseC_of_params
#print axioms ArkLib.ProximityGap.Frontier.R23EulerBridge.fourthMoment_quadChar_of_params
