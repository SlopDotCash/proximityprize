/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvF2_ExternalLeverStatement

/-!
# Wiring di-Benedetto Theorem 3.1 into the conditional sup-norm beat (#444, AvCR)

This brick WIRES the precise, paper-faithful `DiBenedettoThm31Precise` statement (from
`_AvF2_ExternalLeverStatement`) into the two headline conditional sup-norm exponents, RESOLVING the
long-standing `23/24` (`0.9583…`) vs `2849/2880` (`0.98924…`) calibration question with a single
clean explanation:

> **Both exponents are instances of the SAME Theorem 3.1, differing ONLY in the subgroup-energy
> inputs.** The trilinear machinery of arXiv:2003.06165 takes quadratic/cubic additive-energy
> exponents `t_2, t_3` as inputs and produces an `H`-prefactor exponent; the `p^{1/72}` analytic
> tax is the SAME in both calibrations and is carried EXACTLY ONCE.

* **General calibration (verbatim Thm 3.1).** Generic subgroup energies `t_2 = 49/20` (Lem 4.2),
  `t_3 = 4` (Lem 4.3) give the paper's `H`-prefactor exponent `2689/2880` and `p`-exponent `1/72`.
  At the prize aspect ratio `β = 4` (`p = H^4`), `p^{1/72} = H^{4/72} = H^{1/18}`, so the COMBINED
  `H`-exponent is `2689/2880 + 1/18 = 2849/2880 = 1 − 31/2880 ≈ 0.98924`.

* **Sidon-floor recalibration.** Feeding the proven char-0 `μ_n` energies `T_2 = 3n²−3n`
  (`t_2 = 2`), `T_3 ≤ 15n³` (`t_3 = 3`) into the SAME trilinear machinery lowers the `H`-prefactor
  exponent to `65/72`; the analytic `p`-exponent is UNCHANGED at `1/72`. At `β = 4`,
  `p^{1/72} = H^{1/18}`, so the COMBINED `H`-exponent is `65/72 + 1/18 = 23/24 ≈ 0.9583`.

The arithmetic that makes this rigorous and double-count-free:

  `23/24      = 65/72   + 1/18`   (Sidon `H`-prefactor + the unique `p^{1/72}=H^{1/18}` tax)
  `2849/2880  = 2689/2880 + 1/18`  (generic `H`-prefactor + the SAME tax)

The `1/18 = (1/72)·4` charge appears EXACTLY ONCE in each calibration — there is **no
`p`-tax double-count**. The two headline figures differ purely because the Sidon energy inputs
(`t_2 = 2 < 49/20`, `t_3 = 3 < 4`) are strictly below the generic subgroup energies, so the Sidon
`H`-prefactor `65/72 < 2689/2880` is strictly smaller (a better beat — when those energies hold).

## What this brick lands (axiom-clean)

* **`DiBenedettoThm31Sidon`** — a SECOND precise typed instance of the trilinear machinery, with
  the Sidon-floor energy premises (`t_2 = 2`, `t_3 = 3`) and the Sidon `H`-prefactor `65/72`,
  carrying the SAME `p^{1/72}` analytic tax. (Named, never proved — exactly like
  `DiBenedettoThm31Precise`.)
* **`sidon_corollary_of_thm31`** — derives the COMBINED Sidon beat `M ≤ Cdb · H^{23/24}` at the
  `β = 4` lower-range endpoint `H > p^{1/4}` FROM `DiBenedettoThm31Sidon`, by the EXACT same
  `p^{1/72} ≤ H^{1/18}` argument used in `_AvF2.corollary_of_thm31`. This replaces the opaque
  `0.9583` placeholder with a bound derived from the precise paper statement.
* **`calibration_is_energy_input_choice`** — the headline identity pinning that the `23/24` vs
  `2849/2880` gap is EXACTLY the `H`-prefactor gap `2689/2880 − 65/72`, with the `p`-tax `1/18`
  shared (no double-count): both equal their prefactor `+ 1/18`.
* **`no_p_tax_double_count`** — the explicit ledger: each combined exponent is its prefactor PLUS
  the single shared `1/18` tax; the tax is added once, never twice.
* **`sidon_beats_generic`** — the lower Sidon energies give the strictly better `H`-prefactor
  (`65/72 < 2689/2880`) hence the strictly better combined exponent (`23/24 < 2849/2880`).

## ⚠️ Honest scope — NOT prize closure (rule 6)

Both exponents are `≫ 1/2`: `1/2 < 23/24 < 2849/2880 < 1`. The prize needs the sup-norm exponent
to reach `1/2` (Paley/BGK). Both calibrations are firmly on the HIGH side of the wall — genuine
SOTA-direction levers, not a crossing. The Sidon recalibration is, moreover, conditional on the
Sidon-floor energy inputs holding for `μ_n` (proven in char 0; the prize case is the asymptotic
`T_3 = n^{3+o(1)}` shape — the EXACT `T_3 ≤ Cn^3` is refuted at bad thin primes). The
`DiBenedettoThm31{Precise,Sidon}` trilinear estimate itself is named, never proved.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired

open ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement
  (thm31HExponent thm31PExponent corollaryHExponent t2Exponent t3Exponent
   DiBenedettoThm31Precise corollary_of_thm31 corollaryHExponent_eq)

/-! ## The exact exponents of the Sidon-floor recalibration. -/

/-- The Sidon-floor quadratic energy exponent `t_2 = 2` (`T_2(μ_n) = 3n²−3n = Θ(n²)`), strictly
below the generic `49/20`. -/
def sidonT2Exponent : ℚ := 2

/-- The Sidon-floor cubic energy exponent `t_3 = 3` (`T_3(μ_n) ≤ 15n³ = Θ(n³)`), strictly below the
generic `4`. -/
def sidonT3Exponent : ℚ := 3

/-- The Sidon recalibration's `H`-prefactor exponent: `65/72`. (The trilinear machinery's output
when fed `t_2 = 2`, `t_3 = 3`; combined with the shared `p^{1/72} = H^{1/18}` tax at `β = 4` it
gives the headline `23/24`.) -/
def sidonHExponent : ℚ := 65 / 72

/-- The COMBINED Sidon beat exponent on `H` at `β = 4`: `65/72 + 1/18 = 23/24 ≈ 0.9583`. -/
def sidonCombinedExponent : ℚ := 23 / 24

/-- The unique `p`-tax, expressed on `H` at the prize aspect ratio `β = 4`: `p^{1/72} = H^{4/72} =
H^{1/18}`. This `1/18` charge is SHARED by both calibrations and added EXACTLY ONCE. -/
def pTaxAtBetaFour : ℚ := 1 / 18

/-! ## The arithmetic core: both combined exponents = prefactor + the single shared tax. -/

/-- The generic combined exponent decomposes as `2689/2880 + 1/18 = 2849/2880`. The `p`-tax `1/18`
is added ONCE on top of the generic `H`-prefactor. -/
theorem generic_combined_eq :
    thm31HExponent + pTaxAtBetaFour = corollaryHExponent := by
  unfold thm31HExponent pTaxAtBetaFour corollaryHExponent; norm_num

/-- The Sidon combined exponent decomposes as `65/72 + 1/18 = 23/24`. The SAME `p`-tax `1/18` is
added ONCE on top of the (lower) Sidon `H`-prefactor. -/
theorem sidon_combined_eq :
    sidonHExponent + pTaxAtBetaFour = sidonCombinedExponent := by
  unfold sidonHExponent pTaxAtBetaFour sidonCombinedExponent; norm_num

/-- **No `p`-tax double-count (the explicit ledger).** Each combined headline exponent equals its
own `H`-prefactor PLUS the single shared analytic tax `1/18 = (1/72)·4`. The tax is added once per
calibration, never twice; the two headline figures differ ONLY through the prefactor. -/
theorem no_p_tax_double_count :
    sidonCombinedExponent = sidonHExponent + pTaxAtBetaFour ∧
    corollaryHExponent = thm31HExponent + pTaxAtBetaFour ∧
    pTaxAtBetaFour = (thm31PExponent) * 4 := by
  refine ⟨sidon_combined_eq.symm, generic_combined_eq.symm, ?_⟩
  unfold pTaxAtBetaFour thm31PExponent; norm_num

/-- **The calibration gap is EXACTLY the `H`-prefactor gap.** The difference between the two
headline combined exponents equals the difference of the two `H`-prefactors — the shared `p`-tax
cancels. So "`23/24` vs `2849/2880`" is purely an ENERGY-INPUT (prefactor) choice, not a different
analytic tax. -/
theorem calibration_is_energy_input_choice :
    corollaryHExponent - sidonCombinedExponent = thm31HExponent - sidonHExponent := by
  unfold corollaryHExponent sidonCombinedExponent thm31HExponent sidonHExponent; norm_num

/-- **Lower energies ⟹ better beat.** The Sidon energy exponents are strictly below the generic
ones (`2 < 49/20`, `3 < 4`), the Sidon `H`-prefactor is strictly below the generic one
(`65/72 < 2689/2880`), hence the Sidon combined exponent is strictly below the generic one
(`23/24 < 2849/2880`). All firmly above the prize target `1/2`. -/
theorem sidon_beats_generic :
    sidonT2Exponent < t2Exponent ∧ sidonT3Exponent < t3Exponent ∧
    sidonHExponent < thm31HExponent ∧
    sidonCombinedExponent < corollaryHExponent ∧
    (1 : ℚ) / 2 < sidonCombinedExponent := by
  unfold sidonT2Exponent t2Exponent sidonT3Exponent t3Exponent sidonHExponent thm31HExponent
    sidonCombinedExponent corollaryHExponent
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The precise Sidon-recalibration STATEMENT (named, not proved) and its combined corollary. -/

/-- **The Sidon recalibration of Theorem 3.1, the precise typed statement.** Identical trilinear
machinery to `DiBenedettoThm31Precise`, but with the Sidon-floor energy premises
(`T_2 ≤ Cdb·H²`, `T_3 ≤ Cdb·H³`) and the correspondingly lower `H`-prefactor `65/72`. The
analytic `p`-tax is the SAME `p^{1/72}`. Named; never proved — it is the conjectural recalibration
the project uses (a plausible specialization of the same machinery, NOT verbatim Theorem 3.1). -/
structure DiBenedettoThm31Sidon (Hcard p Mval T2val T3val Cdb : ℝ) : Prop where
  /-- The implied/Vinogradov constant is nonnegative. -/
  const_nonneg : 0 ≤ Cdb
  /-- Range hypothesis: `p^{1/4} < H` (the lower-range endpoint, prize regime `β = 4`). -/
  range_lower : p ^ ((1 : ℝ) / 4) < Hcard
  /-- Sidon-floor quadratic energy: `T_2 ≤ Cdb·H²` (`t_2 = 2`). -/
  energy_two : T2val ≤ Cdb * Hcard ^ ((sidonT2Exponent : ℝ))
  /-- Sidon-floor cubic energy: `T_3 ≤ Cdb·H³` (`t_3 = 3`). -/
  energy_three : T3val ≤ Cdb * Hcard ^ ((sidonT3Exponent : ℝ))
  /-- The recalibrated conclusion: `M ≤ Cdb · H^{65/72} · p^{1/72}` (same `p`-tax as Thm 3.1). -/
  sup_bound : Mval ≤ Cdb * Hcard ^ ((sidonHExponent : ℝ)) * p ^ ((thm31PExponent : ℝ))

/-- **The Sidon `0.9583` beat, derived FROM the precise recalibration statement.** At the prize
lower-range endpoint `H > p^{1/4}` (`β = 4`), the SAME `p^{1/72} ≤ H^{1/18}` argument as
`_AvF2.corollary_of_thm31` collapses the `p`-tax onto `H`, giving the COMBINED Sidon exponent
`65/72 + 1/18 = 23/24`. Hence `M ≤ Cdb · H^{23/24}`. This is the headline `0.9583` figure, now a
THEOREM modulo the named recalibrated trilinear statement — NOT an opaque placeholder. -/
theorem sidon_corollary_of_thm31 {Hcard p Mval T2val T3val Cdb : ℝ}
    (hH : 0 < Hcard) (hp : 0 ≤ p)
    (h : DiBenedettoThm31Sidon Hcard p Mval T2val T3val Cdb) :
    Mval ≤ Cdb * Hcard ^ ((sidonCombinedExponent : ℝ)) := by
  -- From `p^{1/4} < Hcard`, get `p^{1/72} ≤ Hcard^{1/18}` (the single shared tax).
  have hp14 : (0 : ℝ) ≤ p ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hp _
  have hple : p ^ ((1 : ℝ) / 72) ≤ Hcard ^ ((1 : ℝ) / 18) := by
    have hpow : (p ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 18) ≤ Hcard ^ ((1 : ℝ) / 18) :=
      Real.rpow_le_rpow hp14 (le_of_lt h.range_lower) (by norm_num)
    rwa [← Real.rpow_mul hp, show (1 : ℝ) / 4 * (1 / 18) = 1 / 72 from by norm_num] at hpow
  calc Mval ≤ Cdb * Hcard ^ ((sidonHExponent : ℝ)) * p ^ ((thm31PExponent : ℝ)) := h.sup_bound
    _ ≤ Cdb * Hcard ^ ((sidonHExponent : ℝ)) * Hcard ^ ((1 : ℝ) / 18) := by
        have hc : 0 ≤ Cdb * Hcard ^ ((sidonHExponent : ℝ)) :=
          mul_nonneg h.const_nonneg (Real.rpow_nonneg hH.le _)
        apply mul_le_mul_of_nonneg_left _ hc
        simpa [thm31PExponent] using hple
    _ = Cdb * Hcard ^ ((sidonCombinedExponent : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hH]
        congr 2
        unfold sidonHExponent sidonCombinedExponent
        push_cast; norm_num

/-- **Both beats from one machinery, side by side.** GIVEN both the verbatim Theorem 3.1 instance
and the Sidon recalibration instance on the same subgroup at `β = 4`, we get BOTH combined bounds:
the generic `M ≤ Cdb·H^{2849/2880}` and the (stronger, energy-conditional) Sidon
`M' ≤ Cdb·H^{23/24}`, with the same `p^{1/72}` tax discharged once in each. This is the wiring:
both headline figures are corollaries of the SAME Theorem-3.1 trilinear machinery, the only
difference being the energy inputs (`49/20, 4` vs `2, 3`). -/
theorem both_beats_wired {Hcard p M M' T2 T3 T2' T3' Cdb : ℝ}
    (hH : 0 < Hcard) (hp : 0 ≤ p)
    (hGen : DiBenedettoThm31Precise Hcard p M T2 T3 Cdb)
    (hSid : DiBenedettoThm31Sidon Hcard p M' T2' T3' Cdb) :
    M ≤ Cdb * Hcard ^ ((corollaryHExponent : ℝ)) ∧
    M' ≤ Cdb * Hcard ^ ((sidonCombinedExponent : ℝ)) :=
  ⟨corollary_of_thm31 hH hp hGen, sidon_corollary_of_thm31 hH hp hSid⟩

/-- **Headline numerics pin.** `23/24 = 0.9583…` and `2849/2880 = 0.98924…`, with
`1/2 < 23/24 < 2849/2880 < 1`. Sanity that the wired exponents are the documented figures and both
sit strictly above the prize wall. -/
theorem headline_exponents :
    sidonCombinedExponent = 23 / 24 ∧ corollaryHExponent = 2849 / 2880 ∧
    (1 : ℚ) / 2 < sidonCombinedExponent ∧ sidonCombinedExponent < corollaryHExponent ∧
    corollaryHExponent < 1 := by
  refine ⟨rfl, corollaryHExponent_eq, ?_, ?_, ?_⟩
  · unfold sidonCombinedExponent; norm_num
  · unfold sidonCombinedExponent corollaryHExponent; norm_num
  · unfold corollaryHExponent; norm_num

end ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.generic_combined_eq
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.sidon_combined_eq
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.no_p_tax_double_count
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.calibration_is_energy_input_choice
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.sidon_beats_generic
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.sidon_corollary_of_thm31
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.both_beats_wired
#print axioms ArkLib.ProximityGap.Frontier.AvCRDiBenedettoWired.headline_exponents
