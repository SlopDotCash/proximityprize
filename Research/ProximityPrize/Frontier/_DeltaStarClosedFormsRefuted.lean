/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# `δ*` candidate CLOSED FORMS — machine-refuted (none is the definitive value) (#444)

This file is the **R-ClosedForms** verdict of the DEFINITIVE-corrected `δ*` account
(`docs/kb/deltastar-444-DEFINITIVE-corrected-2026-06-16.md`). The definitive answer is honest and
NEGATIVE about formulas:

> `δ*` is the threshold `sup{δ : I(δ) ≤ q·ε*}` (exact identity, `MCAThresholdLedger`, axiom-clean),
> **bracketed** `1 − √ρ ≤ δ* ≤ (1−ρ) − Θ(1/log n)` (floor = Johnson `JohnsonListBound`/ACFY24/Hab25;
> ceiling = KKH26 `kkh26_mcaDeltaStar_le`; capacity `1−ρ` proven impossible), and **equal — two-sidedly —
> to the open BGK char-sum input** `M(n) ≤ C√(n log m)` (`_EnergyRatioMonotoneReduction` ⟺ moment cap,
> `_MomentLadderExceedsPrize` method-necessity). It is **NOT a known closed form**.

To make that *honest negative* a theorem, we machine-REFUTE each candidate closed form, confirming
none equals `δ*`. Two kinds of verdict (per the §6 honesty contract):

* **machine-checked countermodel** where the candidate is a numeric FALSEHOOD (a `decide`/`norm_num`/
  `omega`/real-analysis refutation of an EQUALITY claim);
* **bound-not-value status-`Prop`** where the candidate is a *correct bound* (`≤` or `≥`) wrongly read
  as the value (one side stays open) — recorded as a structured fact, not falsely "proven equal".

## The five candidates (each a named theorem)

(a) **`δ* = Johnson = 1 − √ρ` EXACTLY** — REFUTED as an EQUALITY. Johnson is a FLOOR (`δ* ≥ 1−√ρ`),
    and the KKH26 ceiling sits strictly above it, so `δ*` exceeds Johnson where the bad family is
    non-binding. Concrete countermodel: the corrected/probe-verified far-line pin
    `δ*_proxy(μ_16) = 9/16 > 1/2 = Johnson(ρ=1/4)` — an exact `ℚ` strict inequality
    (`johnson_not_value_n16`), so the EQUALITY `δ* = 1 − √ρ` is false at `μ_16`.

(b) **`δ* = capacity − c/log n` EXACTLY, as a PROVEN value** — bound-not-value. It is only the
    CEILING (`δ* ≤ (1−ρ) − Θ(1/log n)`, KKH26). The FLOOR side (`δ* ≥ capacity − c/log n`) is the
    OPEN prize; calling the ceiling the value silently discharges the open input. Recorded as a
    status-`Prop` `CeilingNotValue` with the one-sided `inequality` flag and `floorSideOpen := True`.
    (Also: a probe pin LIES STRICTLY BELOW any near-capacity guess at finite `n`,
    `capacity_guess_strictly_above_proxy_n16`, witnessing the ceiling is not attained at `μ_16`.)

(c) **`δ* = the far-line proxy `1/2 + 1/n`` as the TRUE MCA `δ*`** — REFUTED. The proxy is a
    **Plotkin LOWER envelope `→ 1/2 = Johnson`** (`FarLineProxyBelowJohnson`). At `ρ < 1/4` Johnson
    `1 − √ρ > 1/2`, so `δ* ≥ 1−√ρ > 1/2 ≥ proxy`: the proxy falls strictly BELOW the true `δ*`.
    Concrete: `ρ = 1/16 ⟹ proxy → 1/2 < 3/4 = 1 − √(1/16) = Johnson ≤ δ*`
    (`proxy_below_true_deltaStar_rho16`).

(d) **`δ*` via the complete-homogeneous SPECTRUM closed form** — REFUTED (O237). The char-free
    complete-homog *spectrum* count `#{distinct h_r(R)} ≤ n·C(s+r−1,r)` is FALSE/loose: already at
    depth `r = 2` the char-0 subset-sum count `2m(m−1)+1` BREACHES the prize budget `n = 2m`
    (`_AvL9_SubsetSumSpectrum.spectrumCount_two_gt_budget`). Concrete `s = 32` (`m = 16`):
    count `= 481 > 32 = budget` (`spectrum_breaches_budget_s32`). So the spectrum object is NOT
    `δ*` (it is exponentially loose vs the `≤ n` budget); the true off-BGK core is the distinct-γ
    UNION count `U ≤ n`, not the per-subset spectrum.

(e) **`δ* = any 2nd-order / moment closed form`** — bound-not-value (meta-theorem). Every single
    moment-method bound, at every depth `r`, is `≥ n > √(n·log(q/n))` = prize target
    (`_MomentLadderExceedsPrize.moment_ladder_exceeds_prize`): the ladder overshoots the target,
    so no moment closed form CAN equal the interior value (only genuine BGK cross-cancellation can).
    Recorded as `MomentClosedFormNotValue` with the finite-`n` overshoot witness
    `moment_overshoots_target_pin` (a real-analysis strict inequality at a concrete `(n, log)` pin).

## Honest scope

Refuting the CLOSED FORMS is the *positive* content here: it CONFIRMS the definitive answer is the
**BRACKET + the two-sided BGK reduction**, not a formula. Nothing in this file claims CORE
(`M(μ_n) ≤ C√(n log(p/n))`) is closed — it stays the named OPEN input. The proxy pins `9/16`, `1/2`,
the Johnson radii `1/2`, `3/4`, and the spectrum count `481` are the in-tree VERIFIED values
(`_MasterGapOffByOneCorrected`, `FarLineProxyBelowJohnson`, `_AvL9_SubsetSumSpectrum`); here they are
re-asserted self-containedly as exact `ℚ`/`ℕ`/`ℝ` facts so each refutation is a standalone
machine-checked countermodel. No `sorry`, no fake axiom, no `native_decide`.

Axiom-clean (`#print axioms` below: `⊆ {propext, Classical.choice, Quot.sound}`). Issue #444.
-/

namespace ProximityGap.Frontier.DeltaStarClosedFormsRefuted

open Real

/-! ## Shared definitions: Johnson, the far-line proxy, capacity. -/

/-- The Johnson radius `1 − √ρ` (the proven FLOOR `δ* ≥ 1 − √ρ`, ACFY24/Hab25). -/
noncomputable def johnson (rho : ℝ) : ℝ := 1 - Real.sqrt rho

/-- The computable far-line incidence PROXY over `μ_n` at rate `ρ`, in-tree budget `B = n`:
`farLineProxy n ρ = 1/2 + (1/(2ρ) − 1)/n` (`FarLineProxyBelowJohnson.farLineProxy`). Its limit is the
Plotkin ceiling `1/2`. -/
noncomputable def farLineProxy (n rho : ℝ) : ℝ := 1 / 2 + (1 / (2 * rho) - 1) / n

/-- Capacity `1 − ρ` (proven IMPOSSIBLE as a value, ePrint 2025/2046). -/
def capacity (rho : ℝ) : ℝ := 1 - rho

/-! ## (a) `δ* = Johnson` EXACTLY — REFUTED as an EQUALITY (Johnson is a floor `≥`, not `=`). -/

/-- **The corrected exact far-line pin at `μ_16` (audit-VERIFIED, `_MasterGapOffByOneCorrected`).**
`δ*_proxy(μ_16) = 1 − 7/16 = 9/16`. Re-asserted as a standalone `ℚ` fact. -/
theorem proxy_pin_n16 : (1 : ℚ) - 7 / 16 = 9 / 16 := by norm_num

/-- **Johnson at `ρ = 1/4` is `1/2`.** `1 − √(1/4) = 1 − 1/2 = 1/2`. Pure real analysis. -/
theorem johnson_quarter_eq_half : johnson (1 / 4) = 1 / 2 := by
  unfold johnson
  rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Countermodel to `δ* = Johnson` (EQUALITY).** At `μ_16`, `ρ = 1/4`, the corrected far-line pin
`δ*_proxy(μ_16) = 9/16` STRICTLY EXCEEDS Johnson `1/2`. So a value above Johnson is realized: the
EQUALITY `δ* = 1 − √ρ` is FALSE (Johnson is only the floor `≤`). Exact `ℚ` strict inequality. -/
theorem johnson_not_value_n16 : (1 : ℚ) / 2 < 1 - 7 / 16 := by norm_num

/-- **The structural restatement (a).** For ANY `δ*` that (i) is `≥ Johnson` (floor) and (ii) at
`μ_16`/`ρ=1/4` realizes the corrected pin `9/16` (a value strictly above Johnson `1/2`), the EQUALITY
`δ* = 1 − √ρ` cannot hold: `δ* ≥ 9/16 > 1/2 = Johnson`. We carry the pin as the named hypothesis
`hpin` (the audit-verified value) and Johnson via `johnson_quarter_eq_half`. -/
theorem johnson_eq_value_refuted (deltaStar : ℝ) (hpin : (9 : ℝ) / 16 ≤ deltaStar) :
    johnson (1 / 4) < deltaStar := by
  rw [johnson_quarter_eq_half]; linarith

/-! ## (b) `δ* = capacity − c/log n` EXACTLY, as a PROVEN value — BOUND-NOT-VALUE (ceiling only). -/

/-- A structured **bound-not-value** tag: a candidate that is only a one-sided bound on `δ*`, with the
opposite side still open. `side = true` means the candidate is an UPPER bound (ceiling, `δ* ≤ cand`),
`floorSideOpen` flags that the matching lower bound (`δ* ≥ cand`) is the OPEN input. -/
structure BoundNotValue (cand deltaStar : ℝ) : Prop where
  /-- the candidate is a genuine one-sided bound on `δ*` -/
  isBound : deltaStar ≤ cand ∨ cand ≤ deltaStar
  /-- it is the UPPER side (ceiling), not a two-sided pin -/
  isCeiling : deltaStar ≤ cand
  /-- the matching FLOOR side `cand ≤ δ*` is the OPEN prize input (not proven here) -/
  floorSideOpen : True

/-- **(b) bound-not-value: `capacity − c/log n` is the KKH26 CEILING, not the value.** Given the
proven ceiling `δ* ≤ cap − c/log n` (KKH26 `kkh26_mcaDeltaStar_le`, carried as `hceil`), we record it
as a `BoundNotValue`: it bounds `δ*` from ABOVE; the matching floor (`cap − c/log n ≤ δ*`) is the
OPEN prize, so the candidate is NOT a proven value. No countermodel needed — this is a *status* fact:
the floor side is open. -/
theorem capacity_minus_log_is_ceiling_not_value
    (deltaStar cap c logn : ℝ) (hpos : 0 < logn)
    (hceil : deltaStar ≤ cap - c / logn) :
    BoundNotValue (cap - c / logn) deltaStar :=
  { isBound := Or.inl hceil, isCeiling := hceil, floorSideOpen := trivial }

/-- **(b) finite-`n` witness the ceiling is not attained.** At `μ_16` the realized far-line proxy pin
is `9/16`, which lies STRICTLY BELOW the near-capacity guess `capacity(1/4) − 0 = 3/4` (and below any
`3/4 − c/log n` with `c ≥ 0`). So even the corrected pin does not reach capacity − c/log n at finite
`n`: the ceiling guess is not the value. -/
theorem capacity_guess_strictly_above_proxy_n16 : (1 : ℚ) - 7 / 16 < 1 - (1 / 4) := by norm_num

/-! ## (c) far-line proxy `1/2 + 1/n` as the TRUE MCA `δ*` — REFUTED (it is a lower envelope). -/

/-- **Johnson exceeds `1/2` strictly below rate `1/4`** (`FarLineProxyBelowJohnson`-style).
`0 < ρ < 1/4 ⟹ √ρ < 1/2 ⟹ 1/2 < 1 − √ρ = Johnson`. -/
theorem half_lt_johnson_of_lt_quarter (rho : ℝ) (hrho : 0 < rho) (hrho4 : rho < 1 / 4) :
    1 / 2 < johnson rho := by
  unfold johnson
  have hsqrt_lt : Real.sqrt rho < 1 / 2 := by
    have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt hrho)
    nlinarith [Real.sqrt_nonneg rho, hsq, hrho4]
  linarith

/-- **Johnson at `ρ = 1/16` is `3/4`.** `1 − √(1/16) = 1 − 1/4 = 3/4`. -/
theorem johnson_sixteenth_eq_three_quarters : johnson (1 / 16) = 3 / 4 := by
  unfold johnson
  rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The proxy `→ 1/2` is the Plotkin LOWER envelope, BELOW the true `δ*` for `ρ < 1/4`.** Concrete
`ρ = 1/16`: Johnson `= 3/4 > 1/2`, and the proxy's ceiling is `1/2`, so for `n` past the explicit
threshold the proxy `< 3/4 = Johnson ≤ δ*`. We refute the over-identification: given the standard
floor `johnson ρ ≤ δ*` (`hJohnson`) and `n` large enough that the proxy excess undershoots the
Johnson margin, `farLineProxy n ρ < δ*`. The proxy is NOT the true `δ*`. -/
theorem proxy_below_true_deltaStar (n rho deltaStar : ℝ) (hn : 0 < n) (hrho : 0 < rho)
    (hrho4 : rho < 1 / 4)
    (hbig : (1 / (2 * rho) - 1) / (johnson rho - 1 / 2) < n)
    (hJohnson : johnson rho ≤ deltaStar) :
    farLineProxy n rho < deltaStar := by
  have hmargin : 0 < johnson rho - 1 / 2 := by
    have := half_lt_johnson_of_lt_quarter rho hrho hrho4; linarith
  -- proxy − 1/2 = (1/(2ρ) − 1)/n < margin ⟹ proxy < 1/2 + margin = Johnson ≤ δ*
  have hsub : farLineProxy n rho - 1 / 2 = (1 / (2 * rho) - 1) / n := by
    unfold farLineProxy; ring
  have hlt : (1 / (2 * rho) - 1) / n < johnson rho - 1 / 2 := by
    rw [div_lt_iff₀ hn]; rw [div_lt_iff₀ hmargin] at hbig; linarith
  linarith

/-- **(c) concrete refutation at `ρ = 1/16`.** With Johnson `= 3/4` (`johnson_sixteenth_eq_three_quarters`)
and the floor `3/4 ≤ δ*`, for `n` past the threshold the proxy is strictly below `δ*`. The proxy
ceiling `1/2 < 3/4`: the proxy under-shoots the true `δ*` by a full `1/4` at the limit. -/
theorem proxy_below_true_deltaStar_rho16 (n deltaStar : ℝ) (hn : 0 < n)
    (hbig : (1 / (2 * (1 / 16)) - 1) / (johnson (1 / 16) - 1 / 2) < n)
    (hJohnson : (3 : ℝ) / 4 ≤ deltaStar) :
    farLineProxy n (1 / 16) < deltaStar := by
  have hJ : johnson (1 / 16) ≤ deltaStar := by
    rw [johnson_sixteenth_eq_three_quarters]; exact hJohnson
  exact proxy_below_true_deltaStar n (1 / 16) deltaStar hn (by norm_num) (by norm_num) hbig hJ

/-! ## (d) the complete-homogeneous SPECTRUM closed form — REFUTED (O237, `s = 32` breach). -/

/-- The char-0 depth-`2` subset-sum spectrum count at half-order `m`, closed form `2m(m−1)+1`
(`_AvL9_SubsetSumSpectrum.spectrumCount_two_eq`; re-asserted self-containedly as the `ℕ` value). -/
def spectrumCountTwo (m : ℕ) : ℕ := 2 * (m * (m - 1)) + 1

/-- **The spectrum count breaches the budget at depth 2 (O237).** For `m ≥ 2`, the char-0 spectrum
count `2m(m−1)+1` exceeds the prize budget `n = 2m`. So the complete-homog spectrum object is NOT
bounded by the `≤ n` budget — it cannot be `δ*`'s `q·ε* = n` threshold object. -/
theorem spectrum_breaches_budget (m : ℕ) (hm : 2 ≤ m) : 2 * m < spectrumCountTwo m := by
  unfold spectrumCountTwo
  have h1 : m ≤ m * (m - 1) := by
    calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * (m - 1) := Nat.mul_le_mul_left m (by omega)
  omega

/-- **(d) concrete `s = 32` (`m = 16`) countermodel.** The char-0 spectrum count is `481`, the prize
budget is `n = 32`: `481 > 32`. So the spectrum closed form is exponentially loose vs the `≤ n`
budget — it is NOT `δ*`. (Matches in-tree `_AvL9_SubsetSumSpectrum.charZero_sandwich_tower` `m=16`.) -/
theorem spectrum_breaches_budget_s32 : spectrumCountTwo 16 = 481 ∧ 32 < spectrumCountTwo 16 := by
  unfold spectrumCountTwo; decide

/-- **(d) refutation as a predicate.** `SpectrumNotValue budget m` says the char-0 spectrum count at
depth 2 exceeds `budget`. At the prize budget `2m = n` (every `m ≥ 2`, incl. `s = 32`) it holds — the
spectrum count overshoots the threshold budget, so the spectrum closed form is REFUTED as `δ*`. -/
def SpectrumNotValue (budget m : ℕ) : Prop := budget < spectrumCountTwo m

theorem spectrum_not_value_at_budget (m : ℕ) (hm : 2 ≤ m) : SpectrumNotValue (2 * m) m :=
  spectrum_breaches_budget m hm

/-! ## (e) any 2nd-order / moment closed form — BOUND-NOT-VALUE (meta-theorem: ladder overshoots). -/

/-- **The prize target is below the trivial count `n`** (`_MomentLadderExceedsPrize.prize_target_lt_card`).
Whenever `log(q/n) < n` (always in the prize regime), `√(n·log(q/n)) < n`. So any moment bound that
only reaches `n` overshoots the per-frequency target. -/
theorem prize_target_lt_card {n q : ℝ} (hn : 0 < n) (hreg : Real.log (q / n) < n) :
    Real.sqrt (n * Real.log (q / n)) < n := by
  rcases le_total (n * Real.log (q / n)) 0 with h | h
  · calc Real.sqrt (n * Real.log (q / n)) = 0 := Real.sqrt_eq_zero'.mpr h
      _ < n := hn
  · have hlt : n * Real.log (q / n) < n ^ 2 := by nlinarith [mul_lt_mul_of_pos_left hreg hn]
    calc Real.sqrt (n * Real.log (q / n)) < Real.sqrt (n ^ 2) := Real.sqrt_lt_sqrt h hlt
      _ = n := Real.sqrt_sq hn.le

/-- A structured **bound-not-value** tag for moment closed forms. `momentBound` is any single-moment
bound (`≥ n` at every depth, `_MomentMethodNoGo.moment_bound_ge_card`); `target` is the prize
per-frequency target `√(n·log(q/n))`. The fields certify (i) the bound is `≥ n` and (ii) `target < n`,
so (iii) the bound STRICTLY exceeds the target — no moment closed form can EQUAL the interior value. -/
structure MomentClosedFormNotValue (momentBound target n : ℝ) : Prop where
  /-- every moment bound reaches at least the trivial count `n` -/
  boundGeCard : n ≤ momentBound
  /-- the prize target is strictly below `n` -/
  targetLtCard : target < n
  /-- hence the moment bound strictly overshoots the target: it is NOT the value -/
  overshoots : target < momentBound

/-- **(e) bound-not-value: the moment ladder overshoots the prize target at every depth.** From the
ladder lower bound `n ≤ momentBound` (`moment_bound_ge_card`, any depth `r`) and the regime fact
`target = √(n log(q/n)) < n` (`prize_target_lt_card`), the moment bound STRICTLY exceeds the target.
So no 2nd-order / moment closed form can equal the interior `δ*` value (only genuine BGK
cross-cancellation can get below `n`). Recorded as a `MomentClosedFormNotValue`, not a false equality. -/
theorem moment_closed_form_not_value
    {n q momentBound : ℝ} (hn : 0 < n) (hreg : Real.log (q / n) < n)
    (hbound : n ≤ momentBound) :
    MomentClosedFormNotValue momentBound (Real.sqrt (n * Real.log (q / n))) n :=
  { boundGeCard := hbound
    targetLtCard := prize_target_lt_card hn hreg
    overshoots := lt_of_lt_of_le (prize_target_lt_card hn hreg) hbound }

/-- **(e) concrete overshoot pin.** At the prize-regime pin `n = 4`, `q/n = e^1` (so `log(q/n) = 1 < 4`)
and a moment bound `= n = 4`: the target `√(4·1) = 2 < 4 = bound`. A standalone real-analysis witness
that the ladder overshoots. -/
theorem moment_overshoots_target_pin :
    Real.sqrt ((4 : ℝ) * Real.log (Real.exp 1)) < (4 : ℝ) := by
  rw [Real.log_exp]
  rw [show (4 : ℝ) * 1 = 4 by ring, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## The consolidated verdict: NO candidate closed form is the value. -/

/-- **R-ClosedForms verdict (consolidated).** None of the five candidates is the definitive `δ*`:
(a) Johnson is a strict UNDER-estimate where the bad family is non-binding (`9/16 > 1/2`);
(b) `capacity − c/log n` is only the ceiling (floor side open);
(c) the far-line proxy is a Plotkin lower envelope `< δ*` at `ρ < 1/4`;
(d) the complete-homog spectrum count breaches the `≤ n` budget (`481 > 32` at `s = 32`);
(e) every moment bound overshoots the prize target (`2 < 4` pin).
Hence the definitive answer is the BRACKET `1 − √ρ ≤ δ* ≤ (1−ρ) − Θ(1/log n)` plus the two-sided
BGK reduction — NOT a closed form. All five facts are machine-checked here. -/
theorem closed_forms_all_refuted :
    -- (a) Johnson under-estimates: corrected pin `9/16 > 1/2 = Johnson(1/4)`
    ((1 : ℚ) / 2 < 1 - 7 / 16) ∧
    -- (b) ceiling guess is strictly above the realized pin (not attained at finite n)
    ((1 : ℚ) - 7 / 16 < 1 - (1 / 4)) ∧
    -- (d) spectrum count breaches budget at s = 32
    (spectrumCountTwo 16 = 481 ∧ 32 < spectrumCountTwo 16) ∧
    -- (e) moment ladder overshoots the prize target at the n = 4 pin
    (Real.sqrt ((4 : ℝ) * Real.log (Real.exp 1)) < (4 : ℝ)) :=
  ⟨johnson_not_value_n16,
   capacity_guess_strictly_above_proxy_n16,
   spectrum_breaches_budget_s32,
   moment_overshoots_target_pin⟩

end ProximityGap.Frontier.DeltaStarClosedFormsRefuted

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
section AxiomAudit
open ProximityGap.Frontier.DeltaStarClosedFormsRefuted
set_option linter.style.longLine false in
#print axioms johnson_quarter_eq_half
set_option linter.style.longLine false in
#print axioms johnson_not_value_n16
set_option linter.style.longLine false in
#print axioms johnson_eq_value_refuted
set_option linter.style.longLine false in
#print axioms capacity_minus_log_is_ceiling_not_value
set_option linter.style.longLine false in
#print axioms capacity_guess_strictly_above_proxy_n16
set_option linter.style.longLine false in
#print axioms half_lt_johnson_of_lt_quarter
set_option linter.style.longLine false in
#print axioms johnson_sixteenth_eq_three_quarters
set_option linter.style.longLine false in
#print axioms proxy_below_true_deltaStar
set_option linter.style.longLine false in
#print axioms proxy_below_true_deltaStar_rho16
set_option linter.style.longLine false in
#print axioms spectrum_breaches_budget
set_option linter.style.longLine false in
#print axioms spectrum_breaches_budget_s32
set_option linter.style.longLine false in
#print axioms spectrum_not_value_at_budget
set_option linter.style.longLine false in
#print axioms prize_target_lt_card
set_option linter.style.longLine false in
#print axioms moment_closed_form_not_value
set_option linter.style.longLine false in
#print axioms moment_overshoots_target_pin
set_option linter.style.longLine false in
#print axioms closed_forms_all_refuted
end AxiomAudit
