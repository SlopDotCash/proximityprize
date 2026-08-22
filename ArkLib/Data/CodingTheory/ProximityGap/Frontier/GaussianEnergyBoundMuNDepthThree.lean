/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality

/-!
# The `r = 3` rung of the open energy ladder for `μ_n`, conditional on the char-0 census value (#444)

The prize per-frequency bound is carried (via the in-tree `GaussPeriodMomentBound` consumer chain)
by the named family `GaussianEnergyBound G r : E_r(G) ≤ (2r−1)‼·|G|^r` at depth `r ≈ ln q`. The
energy-ladder reduction (`Frontier/_EnergyRatioMonotoneReduction.lean`, `gaussianEnergyBound_of_ERM`)
steps the bound up one order from a base rung. The base rungs are landed:

* `r = 1`, the trivial Parseval base `E_1 = |G|`.
* `r = 2`, `GaussianEnergyBoundMuNDepthTwo.gaussianEnergyBound_muN_two`, **UNCONDITIONAL** for `μ_n`
  (`E_2(μ_n) = 3n²−3n ≤ 3n²`), thinness-essential.

This file lands the **next rung, `r = 3`** (`E_3(μ_n) ≤ (2·3−1)‼·n³ = 15n³`), with one honest
caveat that distinguishes it from the `r = 2` rung.

## Why `r = 3` is CONDITIONAL where `r = 2` was unconditional (the wall onset, made quantitative)

The exact depth-3 additive-energy closed form `E_3(μ_n) = 15n³−45n²+40n` is the **characteristic-0**
census (in-tree `BalancedCountConcrete` #450; the real-object link `REnergyThreeCharZero` needs
`[CharZero L]`). In characteristic `p` the forward Lam–Leung structure is **FALSE at depth**: that
IS the open BGK/Burgess wall (`REnergyThreeCharZero` says so explicitly). `r = 2` has NO non-trivial
char-`p` additive coincidences (only the antipodal `z + (−z) = 0`), so `E_2(μ_n) = 3n²−3n`
unconditionally. `r = 3` is the FIRST depth where 3-term mod-`p` relations beyond the antipodally
count-balanced ones can occur, so `E_3(μ_n)` can EXCEED the char-0 census by a char-`p` "excess".

A fleet sweep (`scripts/probes/probe_e3_charp_rung_onset.py`,
`probe_e3_charp_rung_thin_sweep.py`, `probe_e3_clean_onset_witness.py`) makes this quantitative:

* **In the thin / prize regime `p > 2^n`** (`n = 8,16,32`, all primes scanned, `β` up to ≈ 4.9):
  the char-`p` excess is **0** (`E_3(μ_n) = 15n³−45n²+40n` exactly), so the `r = 3` ceiling
  `E_3 ≤ 15n³` HOLDS, with slack exactly `45n²−40n`.
* **In the thick regime `p ≤ 2^n`** the excess is `> 0` and can BREACH the ceiling (e.g. `μ_8 ⊂ F_17`:
  `E_3 = 15560 > 15·8³ = 7680`, where even the `r = 2` rung degenerates; and `μ_32 ⊂ F_65537`
  (`β = 3.20`): `E_3 = 703520 > 491520`).

So `GaussianEnergyBound (μ_n) 3` is **NOT a free unconditional fact** in char-`p` (unlike the `r = 2`
rung): its truth is exactly the statement that the char-`p` depth-3 excess stays `≤ 45n²−40n`, which
the sweep confirms throughout the thin window but which is the OPEN char-`p` Lam–Leung-at-depth-3
problem in general. We therefore land the rung **from the census value as a hypothesis**
`E_3(μ_n) = 15n³−45n²+40n` (the in-tree-proven char-0 value, valid in the thin regime), exactly as
`Frontier/CrossStepRungThree`/`CrossStepRungFour` already consume `hE3`. The pure arithmetic
`15n³−45n²+40n ≤ 15n³` is unconditional.

## What this file lands

* `gaussianEnergyBound_muN_three_of_exactE3` (HEADLINE), from `E_3(μ_n) = 15n³−45n²+40n` (the
  thin-regime census value) and `|μ_n| = n`, the rung `GaussianEnergyBound (μ_n) 3`
  (`E_3 ≤ 15n³`), slack exactly `45n²−40n`. `(2·3−1)‼ = 5‼ = 15` matches.
* `gaussianEnergyBound_three_thinness_essential` (rule-3 CONSTRAINT LEMMA), for ANY domain `G` with
  `E_3(G) > 15·|G|³`, the rung FAILS (`¬ GaussianEnergyBound G 3`). The thick-regime breach witnesses
  above instantiate it: the rung is a thin-subgroup lever, NOT a thickness-monotone inequality.
* `eta_sixth_le_muN_three_of_exactE3`, the per-frequency consumer: from the rung,
  `‖η_b‖⁶ ≤ q·15·n³` for every `b` (the `r = 3` instance of the moment-method power bound).

## Honest scope (rules 1, 3, 5, 6 + ASYMPTOTIC GUARD)

NOT a CORE closure. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))` lives at the DEEP order `r ≈ ln q`
(the full DC-Wick ladder / BGK √-cancellation wall), unreachable here: the global energy-ratio step
`ERM` is REFUTED past `r ≈ n/4` (`Frontier/_EnergyRatioMonotoneReduction.lean`), and the char-`p`
excess hypothesis at depth 3 IS the wall in general. This file does **not** prove the census value
unconditionally (that would be claiming the wall) and does **not** re-derive the additive-energy
moment route as a PROVING mechanism for CORE (rule 5): it lands ONE rung conditionally + records its
thinness-essentiality (rule 3 / rule 4 = a constraint-lemma WIN). NO capacity / beyond-Johnson /
growth-law claim; the cliff-at-`n/2` is the over-det/incidence face, untouched (this is the
under-det/additive-energy face). EXTEND-proven on `GaussianEnergyBound` +
`SidonModNegEnergyEquality.mu_n_card_eq`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389 / #450.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthThree

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **The `r = 3` Gaussian energy rung for `μ_n`, from the char-0 census value.**
Given the depth-3 additive-energy census value `E_3(μ_n) = 15n³−45n²+40n` (the in-tree-proven
characteristic-0 closed form, which the fleet sweep confirms holds with zero char-`p` excess
throughout the thin regime `p > 2^n`) and `|μ_n| = n` (`mu_n_card_eq`), the `r = 3` Gaussian energy
bound `GaussianEnergyBound (μ_n) 3` holds, i.e. `E_3(μ_n) ≤ (2·3−1)‼·n³ = 15n³`, with slack exactly
`45n²−40n ≥ 0`. The pure arithmetic step `15n³−45n²+40n ≤ 15n³ ⇔ 40n ≤ 45n²` is unconditional for
`n ≥ 1`. The hypothesis `hE3` is the SAME census value `Frontier/CrossStepRungThree` consumes; it is
NOT proved unconditionally here (that is the open char-`p` Lam–Leung-at-depth-3 wall). -/
theorem gaussianEnergyBound_muN_three_of_exactE3 (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    (hE3 : rEnergy (muN p n) 3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) :
    GaussianEnergyBound (muN p n) 3 := by
  -- n = 2^m with m ≥ 1, so n ≥ 2 (the census ℕ-value's truncating subtraction is benign for n ≥ 2;
  -- it FAILS at n = 1, which is not a valid thin 2-power subgroup).
  have hn_ge2 : 2 ≤ n := by rw [hn2]; calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  -- Unfold the bound: E_3 ≤ doubleFactorial(5) · |μ_n|³.
  change (rEnergy (muN p n) 3 : ℝ)
      ≤ (Nat.doubleFactorial (2 * 3 - 1) : ℝ) * ((muN p n).card : ℝ) ^ 3
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hcard, hdf]
  -- The ℕ value `(15n³ − 45n²) + 40n` has a truncating subtraction (it FAILS at n = 1, ruled out by
  -- n ≥ 2). To cast cleanly to ℝ, first bound rEnergy ≤ 15n³ in ℕ. omega treats n^2, n^3 as atoms,
  -- so we supply `3*n^2 ≤ n^3` (⟹ 45n² ≤ 15n³) and `40*n ≤ 45*n^2`.
  have hnat : rEnergy (muN p n) 3 ≤ 15 * n ^ 3 := by
    rw [hE3]
    rcases Nat.lt_or_ge n 3 with hlt | hge3
    · -- n = 2 (the only value with 2 ≤ n < 3): the ℕ closed form is (120−180)+80 = 80 ≤ 120.
      interval_cases n
      · decide
    · -- n ≥ 3: 3*n² ≤ n³ (so 45n² ≤ 15n³) and 40n ≤ 45n², so (15n³−45n²)+40n ≤ 15n³.
      have h3n2 : 3 * n ^ 2 ≤ n ^ 3 := by
        have : 3 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hge3
        calc 3 * n ^ 2 ≤ n * n ^ 2 := this
          _ = n ^ 3 := by ring
      have h1 : n ≤ n ^ 2 := by
        calc n = n ^ 1 := (pow_one n).symm
          _ ≤ n ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h40 : 40 * n ≤ 45 * n ^ 2 := by
        calc 40 * n ≤ 45 * n := by omega
          _ ≤ 45 * n ^ 2 := by nlinarith [h1]
      omega
  calc (rEnergy (muN p n) 3 : ℝ)
      ≤ ((15 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 15 * (n : ℝ) ^ 3 := by push_cast; ring

set_option linter.unusedFintypeInType false in
/-- **CONSTRAINT LEMMA (rule 3): the `r = 3` Gaussian rung is THINNESS-ESSENTIAL.**
For ANY finite domain `G` over a field whose depth-3 additive energy strictly exceeds `15·|G|³`,
the `r = 3` Gaussian energy bound FAILS. Contrapositive of unfolding `GaussianEnergyBound G 3`
(`E_3(G) ≤ 15·|G|³`, since `(2·3−1)‼ = 15`). Together with `gaussianEnergyBound_muN_three_of_exactE3`
this pins that the `μ_n` rung is a genuine thin-subgroup lever, NOT a thickness-monotone inequality:
the thick-regime breach witnesses (`μ_8 ⊂ F_17`: `E_3 = 15560 > 7680`; `μ_32 ⊂ F_65537`:
`E_3 = 703520 > 491520`, probes `probe_e3_charp_rung_onset.py` / `probe_e3_charp_rung_thin_sweep.py`)
satisfy the hypothesis, so `¬ GaussianEnergyBound G 3` applies, the bound is FALSE off the thin
regime, where char-`p` depth-3 additive coincidences inflate `E_3`. -/
theorem gaussianEnergyBound_three_thinness_essential {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (G : Finset F) (hbig : 15 * (G.card : ℝ) ^ 3 < (rEnergy G 3 : ℝ)) :
    ¬ GaussianEnergyBound G 3 := by
  intro h
  have hb : (rEnergy G 3 : ℝ) ≤ (Nat.doubleFactorial (2 * 3 - 1) : ℝ) * (G.card : ℝ) ^ 3 := h
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at hb
  linarith

/-- **The `r = 3` per-frequency 6th-power bound for `μ_n`, from the census value.** Chaining the
in-tree consumer `eta_pow_le_of_energyBound` through `gaussianEnergyBound_muN_three_of_exactE3`:
under the census value `E_3(μ_n) = 15n³−45n²+40n`, every Gauss period of `μ_n` satisfies
`‖η_b‖⁶ ≤ q·15·n³` for EVERY frequency `b` (`q = |F| = card (ZMod p)`, `n = |μ_n|`). Equivalently
`‖η_b‖ ≤ (15q)^{1/6}·√n`: the `r = 3` completion ceiling on the per-frequency Gauss sum. The prize
wants the DEEP-`r` optimized version `≈ √(2 n ln q)`, NOT reachable at `r = 3`. -/
theorem eta_sixth_le_muN_three_of_exactE3 (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hE3 : rEnergy (muN p n) 3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) (b : ZMod p) :
    ‖eta ψ (muN p n) b‖ ^ 6
      ≤ (Fintype.card (ZMod p) : ℝ) * 15 * ((muN p n).card : ℝ) ^ 3 := by
  have hbound := eta_pow_le_of_energyBound hψ
    (gaussianEnergyBound_muN_three_of_exactE3 hn2 hm hω hE3) b
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at hbound
  have h26 : (2 * 3 : ℕ) = 6 := by norm_num
  rw [h26] at hbound
  exact hbound

end ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthThree

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthThree.gaussianEnergyBound_muN_three_of_exactE3
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthThree.gaussianEnergyBound_three_thinness_essential
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthThree.eta_sixth_le_muN_three_of_exactE3
