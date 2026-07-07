/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovAssembly

/-!
# ROUND 23 MILESTONE (#466): UNCONDITIONAL `LegendreCubicHasseC F 625` at every odd
# finite field — the r=2 rung quadratic face fires with ZERO named hypotheses

This file closes the last two inputs of the round-22 pipeline
(`fourthMoment_quadChar_of_s2output_pipeline`, `_R22StepanovAssembly.lean`):

* **The parameter choice (PARAM input, discharged here).**  For every odd `q > 625`,
  with `s = ⌊√q⌋`, the explicit triple
  `m = 3s/5`, `J = (m+1)/2 + 1`, `D = (q−5)/2`, budget `B = 10s`
  satisfies ALL the S2 side conditions (`r23_params_admissible`): the rank–nullity
  count `m(D+2m+J) < 2J(D+1)`, the S1 window `2D+3 < q`, the Hasse-order cap
  `m ≤ (q−1)/2`, the budget conversion `2·Dtot + 3m ≤ m(B+q)` for the S2 degree
  `Dtot = 3(m+(q−1)/2) + D + q(J−1)`, and `B² = 100s² ≤ 100q ≤ 625q`.
  (Probe `probe_r23_milestone_params.py`: the formula holds for every odd
  `q ∈ (287, 2·10⁶]`; the Lean proof works from `s ≥ 25`, i.e. `q > 625`, where the
  bounding chain `5s² ≥ 117s − 40` has slack.)

* **The small-`q` branch (free by constant inflation).**  `K = 625` covers every
  `q ≤ 625` by the trivial bound `S ≤ q ⟹ S² ≤ q² ≤ 625·q`
  (`legendreCubicHasseC_of_card_le`).  Since the Stepanov branch starts exactly at
  `q > 625 = K`, the case split is GAP-FREE: no per-field finite verification remains.

## The milestone theorems (all axiom-clean, no named hypothesis Props)

* `legendreCubicHasseC_unconditional : ringChar F ≠ 2 → LegendreCubicHasseC F 625` —
  `(∑_s χ₂(s(s−u)(s−v)))² ≤ 625·q` for ALL `u ≠ v`, `u,v ≠ 0`, at EVERY odd finite
  field.  This is an unconditional elementary (Stepanov) Hasse-type bound with the
  explicit (non-sharp) constant `25` in `|S| ≤ 25√q`.
* `quarticWeilInputC_unconditional` — the quartic Weil face at constant `26`.
* `fourthMoment_quadChar_unconditional` — for `|G|⁴ ≤ p`:
  `∑_s ‖T_{χ₂}(s)‖⁴ ≤ 29·|G|²·p`, the r=2 rung quadratic face, unconditional.

## Honest scope

This is the **d = 2 (quadratic-character) face of ONE rung (r = 2) of the B-tower**,
now unconditional with an explicit constant.  It is NOT the prize: the higher-order
character faces of the rung (round-21 `TripleLinearHasse`) and the deep-depth
`r ≈ log p` moments remain open, and the δ* window core is untouched.  The constant
`25` is elementary-Stepanov-sized, far from the Weil-sharp `2`; every downstream
consumer carries the constant parametrically, so sharpening is drop-in.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R23Milestone

open ArkLib.ProximityGap.Frontier.R19HasseAudit
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge
open ArkLib.ProximityGap.Frontier.R22StepanovS2
open ArkLib.ProximityGap.Frontier.R22StepanovAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The explicit parameter choice: all S2 budgets for odd `q > 625` -/

set_option maxHeartbeats 800000 in
-- The explicit floor/sqrt/division certificate is nonlinear enough that the default
-- heartbeat cap times out on the final `nlinarith` call.
/-- **The parameter arithmetic** (the PARAM lane input, discharged): for odd
`q > 625`, `s = ⌊√q⌋`, the choice `m = 3s/5`, `J = (m+1)/2+1`, `D = (q−5)/2`,
`B = 10s` satisfies every side condition of the S2 pipeline. -/
theorem r23_params_admissible {q : ℕ} (hq : 625 < q) (hodd : q % 2 = 1) :
    0 < ((3 * Nat.sqrt q / 5 + 1) / 2 + 1) ∧
    0 < 3 * Nat.sqrt q / 5 ∧
    3 * Nat.sqrt q / 5 ≤ (q - 1) / 2 ∧
    2 * ((q - 5) / 2) + 3 < q ∧
    (3 * Nat.sqrt q / 5) * ((q - 5) / 2 + 2 * (3 * Nat.sqrt q / 5)
        + ((3 * Nat.sqrt q / 5 + 1) / 2 + 1))
      < 2 * (((3 * Nat.sqrt q / 5 + 1) / 2 + 1) * ((q - 5) / 2 + 1)) ∧
    (0 : ℤ) ≤ 10 * (Nat.sqrt q : ℤ) ∧
    (10 * (Nat.sqrt q : ℤ)) ^ 2 ≤ 625 * (q : ℤ) ∧
    2 * ((3 * (3 * Nat.sqrt q / 5 + (q - 1) / 2) + (q - 5) / 2
          + q * (((3 * Nat.sqrt q / 5 + 1) / 2 + 1) - 1) : ℕ) : ℤ)
        + 3 * ((3 * Nat.sqrt q / 5 : ℕ) : ℤ)
      ≤ ((3 * Nat.sqrt q / 5 : ℕ) : ℤ) * (10 * (Nat.sqrt q : ℤ) + (q : ℤ)) := by
  set s : ℕ := Nat.sqrt q with hs
  set m : ℕ := 3 * s / 5 with hmdef
  set j2 : ℕ := (m + 1) / 2 with hj2def
  set D : ℕ := (q - 5) / 2 with hDdef
  set e : ℕ := (q - 1) / 2 with hedef
  -- sqrt bracketing
  have hs1 : s * s ≤ q := Nat.sqrt_le q
  have hs2 : q < (s + 1) * (s + 1) := Nat.lt_succ_sqrt q
  have hs25 : 25 ≤ s := by nlinarith
  -- division bracketing (omega handles / and % by literals)
  have hm5 : 5 * m ≤ 3 * s ∧ 3 * s < 5 * m + 5 := by omega
  have hj2b : 2 * j2 ≤ m + 1 ∧ m + 1 ≤ 2 * j2 + 1 := by omega
  have hDq : 2 * D + 5 = q := by omega
  have heq : 2 * e + 1 = q := by omega
  -- `s² ≥ 25s` (the only nonlinear fact omega needs help with)
  have h25s : 25 * s ≤ s * s := Nat.mul_le_mul_right s hs25
  have h5m31 : 5 * m + 31 ≤ q := by linarith [h25s, hs1, hm5.1, hs25]
  have h2s1 : 2 * s + 1 ≤ q := by linarith [h25s, hs1, hs25]
  -- squared bracketing for the count inequality
  have hmm : (5 * m) * (5 * m) ≤ (3 * s) * (3 * s) :=
    Nat.mul_le_mul hm5.1 hm5.1
  have hkey : 5 * (m * m) + m + 6 < 2 * q := by nlinarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, by positivity, ?_, ?_⟩
  · -- the rank–nullity count `m(D+2m+J) < 2(J(D+1))`, `J = j2 + 1`
    have hA : m * (2 * (j2 + 1)) ≤ m * (m + 3) :=
      Nat.mul_le_mul_left m (by omega)
    have hB : (m + 2) * (2 * (D + 1)) ≤ (2 * (j2 + 1)) * (2 * (D + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    linarith [hA, hB, hkey]
  · -- `(10s)² = 100 s² ≤ 100 q ≤ 625 q`
    have h1 : ((s : ℤ)) * s ≤ (q : ℤ) := by exact_mod_cast hs1
    have h0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    nlinarith
  · -- the budget conversion `2·Dtot + 3m ≤ m(10s + q)`
    have hJ1 : ((m + 1) / 2 + 1) - 1 = j2 := by omega
    rw [hJ1]
    push_cast
    -- integer versions of all the bracketing facts
    have z1 : 2 * (e : ℤ) + 1 = (q : ℤ) := by exact_mod_cast heq
    have z2 : 2 * (D : ℤ) + 5 = (q : ℤ) := by exact_mod_cast hDq
    have z3 : 2 * (j2 : ℤ) ≤ (m : ℤ) + 1 := by exact_mod_cast hj2b.1
    have z4 : 5 * (m : ℤ) ≤ 3 * (s : ℤ) := by exact_mod_cast hm5.1
    have z5 : 3 * (s : ℤ) ≤ 5 * (m : ℤ) + 4 := by
      have := hm5.2; omega
    have z6 : ((s : ℤ)) * s ≤ (q : ℤ) := by exact_mod_cast hs1
    have z7 : (q : ℤ) ≤ (s : ℤ) * s + 2 * s := by
      have hnat : q ≤ s * s + 2 * s := by nlinarith [hs2]
      exact_mod_cast hnat
    have z8 : (25 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs25
    have zq0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    have zs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    -- product hints: `q·2j2 ≤ q(m+1)` and `10s·3s ≤ 10s(5m+4)`
    have p1 : (q : ℤ) * (2 * j2) ≤ (q : ℤ) * ((m : ℤ) + 1) :=
      mul_le_mul_of_nonneg_left z3 zq0
    have p2 : (10 * (s : ℤ)) * (3 * s) ≤ (10 * (s : ℤ)) * (5 * m + 4) :=
      mul_le_mul_of_nonneg_left z5 (by positivity)
    have p3 : (25 : ℤ) * s ≤ (s : ℤ) * s :=
      mul_le_mul_of_nonneg_right z8 zs0
    nlinarith [p1, p2, p3, z1, z2, z4, z6, z7, z8]

/-! ## 2. The sized S2 supply at every odd `q > 625` (the PARAM+Euler weld) -/

/-- **The unconditional sized S2 supply**: at every odd finite field with
`q > 625`, `S2OutputSized F 625` holds — the explicit parameters of
`r23_params_admissible` fed through the concrete S2 theorem
(`s2Output_of_cubic_stepanov_S2`). -/
theorem s2OutputSized_holds (hF : ringChar F ≠ 2)
    (hq : 625 < Fintype.card F) :
    S2OutputSized F 625 := by
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hq_odd : Odd (Fintype.card F) := Nat.odd_iff.mpr hodd
  obtain ⟨hJ, hm, hme, hD, hcount, hB0, hBK, harith⟩ :=
    r23_params_admissible hq hodd
  exact ⟨3 * Nat.sqrt (Fintype.card F) / 5,
    3 * (3 * Nat.sqrt (Fintype.card F) / 5 + (Fintype.card F - 1) / 2)
      + (Fintype.card F - 5) / 2
      + Fintype.card F * (((3 * Nat.sqrt (Fintype.card F) / 5 + 1) / 2 + 1) - 1),
    10 * (Nat.sqrt (Fintype.card F) : ℤ), hm, hB0, hBK, harith,
    s2Output_of_cubic_stepanov_S2 hF hq_odd hJ hme hD hcount⟩

/-! ## 3. THE MILESTONE: unconditional theorems, zero named hypotheses -/

/-- **THE MILESTONE (round 23)**: at EVERY odd finite field,
`(∑_s χ₂(s(s−u)(s−v)))² ≤ 625·q` uniformly over the nondegenerate cubic family —
an UNCONDITIONAL elementary Hasse-type bound (`|S| ≤ 25√q`), no named hypotheses.
Small fields (`q ≤ 625`) by the trivial bound; large fields by the explicit-parameter
Stepanov method. -/
theorem legendreCubicHasseC_unconditional (hF : ringChar F ≠ 2) :
    LegendreCubicHasseC F 625 := by
  rcases Nat.lt_or_ge 625 (Fintype.card F) with h | h
  · exact legendreCubicHasseC_of_s2outputSized hF (s2OutputSized_holds hF h)
  · exact legendreCubicHasseC_of_card_le hF (by exact_mod_cast h)

/-- The quartic Weil face, unconditional at constant `26` (`625 = 25²`). -/
theorem quarticWeilInputC_unconditional (hF : ringChar F ≠ 2) (G : Finset F) :
    QuarticWeilInputC (quadCharC F) G 26 := by
  have h625 := legendreCubicHasseC_unconditional hF
  have heq : (625 : ℤ) = (25 : ℤ) ^ 2 := by norm_num
  rw [heq] at h625
  have h : QuarticWeilInputC (quadCharC F) G (((25 : ℤ) : ℝ) + 1) :=
    quarticWeilInputC_of_cubicHasseC hF (k := 25) (by norm_num) h625 G
  have hC : (((25 : ℤ) : ℝ) + 1) = 26 := by norm_num
  rwa [hC] at h

/-- **The r=2 rung quadratic face, UNCONDITIONAL**: for every odd finite field and
every `G` with `|G|⁴ ≤ p`, `∑_s ‖T_{χ₂}(s)‖⁴ ≤ 29·|G|²·p`.  Zero named hypotheses;
axiom audit below. -/
theorem fourthMoment_quadChar_unconditional (hF : ringChar F ≠ 2)
    (G : Finset F) (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ 29 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  have hW := quarticWeilInputC_unconditional hF G
  have hb := fourthMoment_le_of_quarticWeilInputC (quadCharC F) G
    (Cq := 26) (by norm_num) hW hp
  calc ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ (3 + 26) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := hb
    _ = 29 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by norm_num

end ArkLib.ProximityGap.Frontier.R23Milestone

/-! ## Axiom audit (must be exactly {propext, Classical.choice, Quot.sound}) -/
#print axioms ArkLib.ProximityGap.Frontier.R23Milestone.r23_params_admissible
#print axioms ArkLib.ProximityGap.Frontier.R23Milestone.s2OutputSized_holds
#print axioms ArkLib.ProximityGap.Frontier.R23Milestone.legendreCubicHasseC_unconditional
#print axioms ArkLib.ProximityGap.Frontier.R23Milestone.quarticWeilInputC_unconditional
#print axioms ArkLib.ProximityGap.Frontier.R23Milestone.fourthMoment_quadChar_unconditional
