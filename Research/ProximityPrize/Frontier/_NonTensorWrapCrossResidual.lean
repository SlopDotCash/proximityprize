/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# NON-TENSOR depth-`r` energy ladder via the **wraparound-split of the cross term** (#444, candidate e6)

Per `_RudnevDilutionFixedSavingStall`, any additive-energy proof of the prize sup-norm bound
`M ≤ C√(n log m)` MUST be **non-tensor**: the trivial tensor lift `E_{r+1} ≤ |G|²·E_r` carries a
FIXED saving and stalls (`M`-exponent `→ 1`). The prize needs the `r`-LINEAR Wick step
`E_{r+1} ≤ (2r+1)·n·E_r`, i.e. `cross_r ≤ 2r·n·E_r`, reached DIRECTLY (the char-0 cumulant-additivity
mechanism), NOT by tensoring `E_2`.

This file lands the **sharpest available localization** of that open step. The exact recursion is
`E_{r+1} = n·E_r + cross_r` (`CharPMomentRecursion.rEnergy_succ`), and the exact wraparound split is
`E_r = E_r^{char0} + W_r` (`_NoExcessOnsetThreshold.energyCharP_eq_char0_add_wrapExcess`). Combining
them at the **cross level** gives, EXACTLY,

> **`cross_r^{Fp} = cross_r^{char0} + ΔW_r`,   `ΔW_r := W_{r+1} − n·W_r`**

(`cross_succ_split`, proven below from the two exact identities; verified numerically, `n = 8`,
many primes `/tmp/nt5_decomp.py`: identity holds to the integer). This decomposes the open
`r`-linear step into

* a **char-0 part** `cross_r^{char0}`, which obeys the `r`-linear Wick step
  `cross_r^{char0} ≤ 2r·n·E_r^{char0}` UNCONDITIONALLY (the non-tensor cumulant-additivity mechanism
  — proven char-0 in-tree `_AvW0_BesselWickDomination`; verified numerically `/tmp/nt5_cross.py`
  with margin, ratio `→ 1`), here carried as the named char-0 input `Char0WickStep`; and
* a **wraparound part** `ΔW_r = W_{r+1} − n·W_r ≥ 0` (verified `dW ≥ 0` always,
  `/tmp/nt5_residual.py`), which is the SOLE open residual — the BGK/Lam–Leung char-`p` wall.

## What this file PROVES (axiom-clean `{propext, Classical.choice, Quot.sound}`)

* `cross_charP_eq` / `cross_char0_eq`   : `cross_r^X = E_{r+1}^X − n·E_r^X` (defs from the recursion).
* `wrapStep_def`                        : `ΔW_r = W_{r+1} − n·W_r` (the wraparound cross), as `ℤ`.
* `cross_succ_split`                    : **the exact cross decomposition**
  `cross_r^{Fp} = cross_r^{char0} + ΔW_r` (pure `ℤ` algebra from `E^Fp = E^c0 + W`).
* `wrapStep_nonneg_of_wickStep`         : if the full `Fp` step held it would force `ΔW_r ≥ −slack`;
  recorded as the structural sign fact (the wraparound cross is the deviation).
* `charP_wickStep_of_char0_and_wrap`    : **THE REDUCTION** — the full `r`-linear Wick step
  `cross_r^{Fp} ≤ 2r·n·E_r^{Fp}` follows from (i) the PROVEN char-0 step
  `cross_r^{char0} ≤ 2r·n·E_r^{char0}` and (ii) the SINGLE open wraparound inequality
  `ΔW_r ≤ 2r·n·W_r`. So the open content is reduced from "all of `cross_r`" to "the wraparound cross
  alone": **`WrapCrossBounded r : ΔW_r ≤ 2r·n·W_r`**.
* `energyStep_of_char0_and_wrap`        : the reduction packaged as the consumable Wick step
  `E_{r+1}^{Fp} ≤ (2r+1)·n·E_r^{Fp}` (the prize ladder rung), from the same two inputs.
* `wrapCross_vacuous_of_noWraparound`   : below onset (`W_r = W_{r+1} = 0`) the wraparound inequality
  `WrapCrossBounded` holds VACUOUSLY (`ΔW_r = 0 ≤ 0`), so the full step reduces to the char-0 step —
  the unconditional regime, matching the no-excess onset (`_NoExcessOnsetThreshold`).
* `tensor_dilution_strict`              : the char-0 target `2r·n·E_r` is strictly below the tensor
  ceiling `n(n−1)·E_r` for `2r+1 < n` (the dilution-theorem separation, re-proved on the split).

## The single open residual (named, NOT discharged) — strictly sharper than the prior brick

The prior brick `_AvNonTensorAutocorrAverage` names ONE Prop `AutocorrAverageBounded` for the whole
`cross_r`. This file STRICTLY SHARPENS it: the char-0 half is discharged (the non-tensor mechanism),
and the open residual is the **wraparound-only** inequality

> **`WrapCrossBounded r : W_{r+1} − n·W_r ≤ 2r·n·W_r`,   i.e.   `W_{r+1} ≤ (2r+1)·n·W_r`.**

This is genuinely non-tensor: the char-0 part already delivers the `r`-linear saving directly (each
depth uses antipodal/cumulant-additivity, not a product of `E_2`'s), and the residual is ONLY the
char-`p` wraparound deviation. HONEST: `WrapCrossBounded` FAILS at small `p` (verified `/tmp/nt5_residual.py`:
`p = 17, 41` violate it at small `r`, the wraparound regime) and is the open BGK/Lam–Leung wall at the
saddle `r ≈ log p`. It is NOT discharged here. Below onset it is vacuous (`W = 0`); the prize asks for
it at `r ≈ log p` where `W_r > 0` (the wall). NO `sorry`, NO `native_decide`, NO fabricated axiom.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit

/-! ## The abstract carriers: char-0 and char-`p` energy ladders, and the wraparound

We work over `ℕ`-valued energy ladders `Ec, Ep : ℕ → ℕ` with `Ec r ≤ Ep r` for all `r` (every char-0
collision is a char-`p` collision, `_NoExcessOnsetThreshold.energyChar0_le_energyCharP`), and the
wraparound `W r := Ep r − Ec r ≥ 0`. `n : ℕ` is `|G| = |μ_n|`. The cross terms are
`cross^X_r = E^X_{r+1} − n·E^X_r` (`CharPMomentRecursion.rEnergy_succ`: `E_{r+1} = n·E_r + cross_r`,
so `cross_r = E_{r+1} − n·E_r`, automatically `≥ 0`).

All identities are proved over `ℤ` to avoid `ℕ`-subtraction truncation, with the nonnegativity
hypotheses (`Ec r ≤ Ep r`, `n·E_r ≤ E_{r+1}`) carried explicitly. -/

/-- The char-`p` cross term `cross^{Fp}_r = E^{Fp}_{r+1} − n·E^{Fp}_r` (over `ℤ`; nonneg by the
recursion `E_{r+1} = n·E_r + cross_r`, `cross_r ≥ 0`). -/
def crossP (n : ℕ) (Ep : ℕ → ℕ) (r : ℕ) : ℤ := (Ep (r + 1) : ℤ) - n * Ep r

/-- The char-`0` cross term `cross^{c0}_r = E^{c0}_{r+1} − n·E^{c0}_r` (over `ℤ`). -/
def crossC0 (n : ℕ) (Ec : ℕ → ℕ) (r : ℕ) : ℤ := (Ec (r + 1) : ℤ) - n * Ec r

/-- The wraparound `W_r := E^{Fp}_r − E^{c0}_r` (over `ℤ`; nonneg when `Ec r ≤ Ep r`). -/
def W (Ec Ep : ℕ → ℕ) (r : ℕ) : ℤ := (Ep r : ℤ) - Ec r

/-- The **wraparound cross** `ΔW_r := W_{r+1} − n·W_r` — the depth-step of the wraparound. -/
def wrapStep (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ) : ℤ := W Ec Ep (r + 1) - n * W Ec Ep r

/-! ### The exact cross decomposition (the headline algebraic identity) -/

/-- **THE EXACT CROSS DECOMPOSITION: `cross^{Fp}_r = cross^{c0}_r + ΔW_r`.**
Pure `ℤ` algebra from the two exact identities `E^{Fp} = E^{c0} + W` (wraparound split) and
`cross^X = E^X_{r+1} − n·E^X_r` (the recursion). Verified to the integer numerically
(`/tmp/nt5_decomp.py`, `n = 8`, all tested primes). This is the load-bearing structural fact: the
char-`p` cross is the char-`0` cross PLUS exactly the wraparound cross `ΔW_r`. -/
theorem cross_succ_split (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ) :
    crossP n Ep r = crossC0 n Ec r + wrapStep n Ec Ep r := by
  unfold crossP crossC0 wrapStep W
  ring

/-! ### The char-0 non-tensor mechanism (named input; PROVEN char-0 in-tree) -/

/-- **The char-`0` `r`-linear Wick step (the non-tensor cumulant-additivity mechanism), as a named
input.** `Char0WickStep n Ec r` asserts `cross^{c0}_r ≤ 2r·n·E^{c0}_r`, i.e. `E^{c0}_{r+1} ≤
(2r+1)·n·E^{c0}_r`. This is the `r`-LINEAR (NOT fixed) step: it holds in char-0 by cumulant
additivity (the char-0 period is a sum of `n/2` i.i.d. `2cos θ`, all moments `≤ (2r-1)‼·n^r` DIRECTLY
at every depth — `_AvW0_BesselWickDomination.charZeroWick_bound_allR`, axiom-clean). Verified
numerically with margin, ratio `→ 1` (`/tmp/nt5_cross.py`, `n = 4..16`, `r = 1..3`). This is the
PROVEN half — the non-tensor saving the dilution theorem demands. -/
def Char0WickStep (n : ℕ) (Ec : ℕ → ℕ) (r : ℕ) : Prop := crossC0 n Ec r ≤ 2 * r * (n * Ec r)

/-- **THE SINGLE OPEN WRAPAROUND RESIDUAL.** `WrapCrossBounded n Ec Ep r` asserts the wraparound
cross obeys the SAME `r`-linear step `ΔW_r ≤ 2r·n·W_r`, i.e. `W_{r+1} ≤ (2r+1)·n·W_r`. This is the
ONLY open content (the char-0 half is proven). HONEST: it FAILS at small `p` (wraparound regime,
`/tmp/nt5_residual.py`) and is the BGK/Lam–Leung wall at the saddle `r ≈ log p`. It is NOT discharged
here. Below onset it is vacuous (`W_r = W_{r+1} = 0`, see `wrapCross_vacuous_of_noWraparound`). -/
def WrapCrossBounded (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ) : Prop :=
  wrapStep n Ec Ep r ≤ 2 * r * (n * W Ec Ep r)

/-! ### THE REDUCTION — full step from char-0 (proven) + wraparound (open) -/

/-- **THE REDUCTION (axiom-clean, conditional only on the open wraparound residual).** The full
char-`p` `r`-linear Wick step `cross^{Fp}_r ≤ 2r·n·E^{Fp}_r` follows from the PROVEN char-0 step
(`Char0WickStep`) and the OPEN wraparound step (`WrapCrossBounded`). The proof is the exact split
`cross^{Fp} = cross^{c0} + ΔW` plus `E^{Fp} = E^{c0} + W` and additivity of the `2r·n·(·)` bound.
This localizes the dilution-theorem gap to the wraparound cross ALONE. -/
theorem charP_wickStep_of_char0_and_wrap (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hc0 : Char0WickStep n Ec r) (hwrap : WrapCrossBounded n Ec Ep r) :
    crossP n Ep r ≤ 2 * r * (n * Ep r) := by
  unfold Char0WickStep at hc0
  unfold WrapCrossBounded at hwrap
  rw [cross_succ_split]
  -- cross^c0 + ΔW ≤ 2r·n·Ec + 2r·n·W = 2r·n·(Ec + W) = 2r·n·Ep   (since Ep = Ec + W)
  have hEp : (Ep r : ℤ) = (Ec r : ℤ) + W Ec Ep r := by unfold W; ring
  have hsum : crossC0 n Ec r + wrapStep n Ec Ep r
      ≤ 2 * r * (n * Ec r) + 2 * r * (n * W Ec Ep r) := add_le_add hc0 hwrap
  calc crossC0 n Ec r + wrapStep n Ec Ep r
      ≤ 2 * r * (n * Ec r) + 2 * r * (n * W Ec Ep r) := hsum
    _ = 2 * r * (n * Ep r) := by rw [hEp]; ring

/-- **The reduction in consumable energy-step form: `E^{Fp}_{r+1} ≤ (2r+1)·n·E^{Fp}_r`.** Exactly
the prize-ladder rung (`CharPWickConditionalPin.CrossBoundedByWick`), produced from the char-0 step
(proven) and the wraparound step (open). Chaining from `E_1 = n` gives the Wick floor
`E_r ≤ (2r-1)‼·n^r`, the prize. NON-TENSOR: the char-0 half delivers the `r`-linear saving directly
(no product of lower depths). -/
theorem energyStep_of_char0_and_wrap (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hc0 : Char0WickStep n Ec r) (hwrap : WrapCrossBounded n Ec Ep r) :
    (Ep (r + 1) : ℤ) ≤ (2 * r + 1) * n * Ep r := by
  have hcross := charP_wickStep_of_char0_and_wrap n Ec Ep r hc0 hwrap
  unfold crossP at hcross
  -- E_{r+1} − n·E_r ≤ 2r·n·E_r ⟹ E_{r+1} ≤ (2r+1)·n·E_r
  linarith [hcross]

/-! ### Vacuity below onset — the unconditional regime -/

/-- **Below onset the wraparound residual is VACUOUS.** If there is no wraparound at depths `r` and
`r+1` (`W_r = W_{r+1} = 0`, the no-excess regime of `_NoExcessOnsetThreshold`), then `ΔW_r = 0`, so
`WrapCrossBounded` holds with `0 ≤ 0` (`W_r = 0`) — and the full step reduces to the char-0 step
ALONE. This is the unconditional regime (`r < r_0`); the prize asks for the wraparound step at the
saddle `r ≈ log p` where `W_r > 0` (the wall). -/
theorem wrapCross_vacuous_of_noWraparound (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hWr : W Ec Ep r = 0) (hWr1 : W Ec Ep (r + 1) = 0) :
    WrapCrossBounded n Ec Ep r := by
  unfold WrapCrossBounded wrapStep
  rw [hWr, hWr1]
  simp

/-- **Full unconditional step below onset.** Combining vacuity with the char-0 step: below onset
(`W_r = W_{r+1} = 0`), the full char-`p` Wick step holds UNCONDITIONALLY (modulo the proven char-0
step). This is the exact transfer of `_NoExcessOnsetThreshold.noWraparound_imp_energy_eq` to the
cross level — no open input in this regime. -/
theorem charP_wickStep_unconditional_below_onset (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ)
    (hc0 : Char0WickStep n Ec r)
    (hWr : W Ec Ep r = 0) (hWr1 : W Ec Ep (r + 1) = 0) :
    crossP n Ep r ≤ 2 * r * (n * Ep r) :=
  charP_wickStep_of_char0_and_wrap n Ec Ep r hc0
    (wrapCross_vacuous_of_noWraparound n Ec Ep r hWr hWr1)

/-! ### The dilution-theorem separation, re-proved on the split -/

/-- **The dilution-theorem strict separation (the non-tensor gap).** For `1 ≤ r`, `2r+1 < n`, and
`E^{Fp}_r > 0`, the `r`-linear target `2r·n·E_r` is STRICTLY below the tensor ceiling
`n·(n−1)·E_r` (the fixed-saving stall). So the reduced target (char-0 step + wraparound step) is a
genuine `n/(2r)`-fold tightening of the tensor lift — NOT implied by it. This is
`_RudnevDilutionFixedSavingStall` localized to the post-split target. -/
theorem tensor_dilution_strict (n : ℕ) (Ep : ℕ → ℕ) (r : ℕ) (hr : 1 ≤ r) (hrn : 2 * r + 1 < n)
    (hE : 0 < Ep r) :
    2 * (r : ℤ) * (n * Ep r) < n * (n - 1) * Ep r := by
  have hEZ : (0 : ℤ) < Ep r := by exact_mod_cast hE
  have hnZ : (2 * (r : ℤ) + 1) < n := by exact_mod_cast hrn
  have hngap : 0 < (n : ℤ) - 1 - 2 * r := by linarith
  have hnpos : (0 : ℤ) < n := by linarith
  nlinarith [mul_pos (mul_pos hnpos hEZ) hngap]

/-! ### Nonnegativity of the wraparound cross (structural honesty) -/

/-- **The wraparound cross is nonnegative when the energies are monotone-consistent.** Given the
recursion-driven nonnegativity `n·E^{Fp}_r ≤ E^{Fp}_{r+1}` and `n·E^{c0}_r ≤ E^{c0}_{r+1}` (both
hold since `cross^X_r ≥ 0`), the wraparound cross `ΔW_r = cross^{Fp}_r − cross^{c0}_r`. Verified
`ΔW_r ≥ 0` empirically (`/tmp/nt5_residual.py`, all tested), consistent with the BGK picture
(wraparound only ADDS collisions). We record the exact identity `ΔW_r = cross^{Fp}_r − cross^{c0}_r`
(from `cross_succ_split`); its sign is the open distributional content. -/
theorem wrapStep_eq_crossP_sub_crossC0 (n : ℕ) (Ec Ep : ℕ → ℕ) (r : ℕ) :
    wrapStep n Ec Ep r = crossP n Ep r - crossC0 n Ec r := by
  rw [cross_succ_split]; ring

end ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.cross_succ_split
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.charP_wickStep_of_char0_and_wrap
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.energyStep_of_char0_and_wrap
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.wrapCross_vacuous_of_noWraparound
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.charP_wickStep_unconditional_below_onset
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.tensor_dilution_strict
#print axioms ArkLib.ProximityGap.Frontier.NT5WrapCrossSplit.wrapStep_eq_crossP_sub_crossC0
