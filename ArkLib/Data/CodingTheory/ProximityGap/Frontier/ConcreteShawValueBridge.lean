/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteTrivialCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

/-!
# Wiring the Shaw-value capstone onto the CONCRETE worst period (#444)

`ShawValueCapstone` states the normalization equivalence `prize ⇔ Sh(n)=O(1)` and the floor/ceiling
rungs on an **abstract** raw worst-frequency size `M : ℝ`. `ConcreteTrivialCeiling` /
`ConcreteParsevalLower` prove the **concrete** floor `√(n(q−n)/(q−1)) ≤ M(μ_n)` and ceiling
`M(μ_n) ≤ |G|` over the real periods `η_b = ∑_{y∈G} ψ(b·y)`, with `M(μ_n) = worstPeriod ψ G hne`.

This file is the missing CONNECTIVE rung: it instantiates the abstract capstone bookkeeping with the
concrete `worstPeriod`, so the normalized Shaw value of the REAL character sum carries an in-tree
upper bound (and the concrete RMS floor), without any caller re-discharging the `M ≤ n` hypothesis.

> `shawValue_worstPeriod_le_of_card`  : `Sh(M(μ_n)) ≤ |G| / scale`, from the concrete ceiling `M ≤ |G|`,
> `shawValue_worstPeriod_rms_floor`   : `√(n(q−n)/(q−1)) / scale ≤ Sh(M(μ_n))`, from the concrete
>                                       Parseval/RMS floor,
> `shawValue_worstPeriod_bracket`     : the two together — the concrete normalized corridor for the
>                                       real worst period.

Here `Sh(M) = shawValue M (G.card) L = M / prizeScale (G.card) L`, `prizeScale n L = √(n·L)`, the
Shaw-value normalization. The HONEST floor uses the true RMS quantity `√(n(q−n)/(q−1))` (the
unconditional Parseval value), NOT the rounded `√n` — the capstone's clean-`√n` floor rung is a
slightly stronger hypothesis that the unconditional second-moment identity does not supply.

## Honesty (the prize is the GAP, untouched)

This is pure Lane-2 INSTANTIATION: it plugs the concrete real-period bounds into the abstract
normalization bookkeeping. It adds NO analytic content — no anti-concentration, no cancellation, no
completion, no moment, no capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` (equivalently
`Sh(M(μ_n)) = O(1)` at `L = log(p/n)`) stays OPEN; it lives strictly inside the proven normalized
`√((q−n)/(q−1)·L⁻¹) .. √(n/L)` corridor supplied here.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ProximityGap.Frontier.ConcreteTrivialCeiling

namespace ProximityGap.Frontier.ConcreteShawValueBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete normalized ceiling for the real worst period.** The Shaw value of the actual character
sum `M(μ_n) = max_{b≠0}‖η_b‖` is bounded by `|G| / scale`. Instantiates the abstract capstone rung
`shawValue_le_of_trivial_ceiling` with the concrete `M ≤ |G|` (`worstPeriod_le_card`). -/
theorem shawValue_worstPeriod_le_of_card {ψ : AddChar F ℂ} (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    shawValue (worstPeriod ψ G hne) (G.card : ℝ) L ≤ (G.card : ℝ) / prizeScale (G.card : ℝ) L :=
  shawValue_le_of_trivial_ceiling hs (worstPeriod_le_card ψ G hne)

/-- **Concrete normalized RMS floor for the real worst period.** The unconditional Parseval floor
`√(n(q−n)/(q−1)) ≤ M(μ_n)` (`worstPeriod_ge_sqrt_parseval`) passes through Shaw normalization:
`√(n(q−n)/(q−1)) / scale ≤ Sh(M(μ_n))`. Honest: uses the true RMS value, not a rounded `√n`. -/
theorem shawValue_worstPeriod_rms_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
        / prizeScale (G.card : ℝ) L
      ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right (worstPeriod_ge_sqrt_parseval hψ G hne hq1) (le_of_lt hs)

/-- **Concrete normalized corridor for the real worst period.** Both the RMS floor and the trivial
ceiling, normalized by the Shaw scale, around the Shaw value of the actual character sum
`M(μ_n) = max_{b≠0}‖η_b‖`. The prize target `Sh(M(μ_n)) = O(1)` (at `L = log(p/n)`) lives strictly
inside this proven corridor. -/
theorem shawValue_worstPeriod_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
          / prizeScale (G.card : ℝ) L
        ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ (G.card : ℝ) / prizeScale (G.card : ℝ) L :=
  ⟨shawValue_worstPeriod_rms_floor hψ G hne hq1 hs, shawValue_worstPeriod_le_of_card G hne hs⟩

/-- **The concrete prize ⇔ bounded-Shaw equivalence on the REAL worst period.** Instantiates the
abstract capstone equivalence `prizeBound_iff_shawValue_le` with `M := M(μ_n) = worstPeriod ψ G hne`:
for a positive prize scale, the prize-shaped core bound on the actual character-sum worst period is
exactly a bounded Shaw value. This is the headline `CORE ⇔ Sh(n)=O(1)` reduction stated over the real
`η`, not an abstract `M`. -/
theorem prizeBound_worstPeriod_iff_shawValue_le {ψ : AddChar F ℂ} (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {C L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    worstPeriod ψ G hne ≤ C * prizeScale (G.card : ℝ) L
      ↔ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L ≤ C :=
  prizeBound_iff_shawValue_le hs

/-- The same equivalence in expanded positivity hypotheses (`0 < n`, `0 < L`), so a caller need not
construct `prizeScale` positivity by hand. -/
theorem prizeBound_worstPeriod_iff_shawValue_le_of_pos {ψ : AddChar F ℂ} (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {C L : ℝ}
    (hn : 0 < (G.card : ℝ)) (hL : 0 < L) :
    worstPeriod ψ G hne ≤ C * prizeScale (G.card : ℝ) L
      ↔ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L ≤ C :=
  prizeBound_iff_shawValue_le_of_pos hn hL

/-- **Sharp prize-regime Shaw-value floor at the TRUE bracket endpoint.** In the prize regime
`n² ≤ q` (`q = n^β, β ≥ 2`), the sharp Parseval floor `√(n−1) ≤ M(μ_n)`
(`worstPeriod_ge_sqrt_card_pred_of_sq_le`) normalizes to
`√(1 − 1/n) / √L ≤ Sh(M(μ_n))`.

The lower endpoint of the abstract Shaw-value bracket is exactly `1/√L` (`floor_bracket_eq`). This
floor reaches it up to the factor `√(1−1/n) → 1`, i.e. on the REAL worst period the normalized Shaw
value is bounded below by essentially the FULL bracket endpoint `1/√L` — sharper than the generic RMS
floor and the `1/√(2L)` torsion floor, which only reach a constant fraction. The prize `Sh = O(1)` at
`L = log(q/n)` still lives strictly above this floor; the LOWER side is pinned, the UPPER gap is the
open prize. -/
theorem shawValue_worstPeriod_sharp_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (1 - 1 / (G.card : ℝ)) / Real.sqrt L
      ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hs : 0 < prizeScale (G.card : ℝ) L := prizeScale_pos hnpos hL
  -- normalized sharp floor: √(n−1)/scale ≤ Sh(M)
  have hfloor : Real.sqrt ((G.card : ℝ) - 1) / prizeScale (G.card : ℝ) L
      ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
    unfold shawValue
    exact div_le_div_of_nonneg_right
      (worstPeriod_ge_sqrt_card_pred_of_sq_le hψ G hne hq1 hG1 hsq) (le_of_lt hs)
  -- closed form: √(n−1)/√(nL) = √(1−1/n)/√L, via √(n−1)=√n·√(1−1/n) and √(nL)=√n·√L
  have hsn : (0 : ℝ) < Real.sqrt (G.card : ℝ) := Real.sqrt_pos.2 hnpos
  have hnum : Real.sqrt ((G.card : ℝ) - 1)
      = Real.sqrt (G.card : ℝ) * Real.sqrt (1 - 1 / (G.card : ℝ)) := by
    rw [← Real.sqrt_mul (le_of_lt hnpos)]
    congr 1
    field_simp
  have hden : prizeScale (G.card : ℝ) L = Real.sqrt (G.card : ℝ) * Real.sqrt L := by
    unfold prizeScale
    rw [Real.sqrt_mul (le_of_lt hnpos) L]
  have hendpoint : Real.sqrt ((G.card : ℝ) - 1) / prizeScale (G.card : ℝ) L
      = Real.sqrt (1 - 1 / (G.card : ℝ)) / Real.sqrt L := by
    rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt hsn)]
  rw [hendpoint] at hfloor
  exact hfloor

/-- **The sharp prize-regime Shaw-value bracket on the REAL worst period (citable capstone).**
In the prize regime `n² ≤ q` (`q = n^β, β ≥ 2`), the normalized Shaw value of the actual character
sum is sandwiched in CLOSED FORM:
`√(1 − 1/n) / √L  ≤  Sh(M(μ_n))  ≤  √(n / L)`.
The lower endpoint is the sharp floor at the true bracket value `1/√L` (up to `√(1−1/n) → 1`); the
upper endpoint is the trivial ceiling `n` normalized to `√(n/L)` (`ceiling_bracket_eq`). This is the
clean two-sided statement of everything proven unconditionally about `Sh(M(μ_n))` in the prize regime.
The prize `Sh(M(μ_n)) = O(1)` at `L = log(q/n)` is exactly the demand to collapse this corridor's
upper endpoint from `√(n/L)` to an absolute constant; the lower endpoint is already pinned at the
true `1/√L`. No CORE/cancellation/completion/anti-concentration/capacity claim. -/
theorem shawValue_worstPeriod_sharp_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (1 - 1 / (G.card : ℝ)) / Real.sqrt L
        ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) := by
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hs : 0 < prizeScale (G.card : ℝ) L := prizeScale_pos hnpos hL
  refine ⟨shawValue_worstPeriod_sharp_floor hψ G hne hq1 hG1 hsq hL, ?_⟩
  have hceil := shawValue_worstPeriod_le_of_card (ψ := ψ) G hne hs
  rwa [ceiling_bracket_eq hnpos hL] at hceil

/-- **Concrete Shaw-value capstone on the REAL worst period.**  In the quadratic thin regime
`n² ≤ q`, the raw prize-shaped bound on the actual period supremum `M(μ_n)` is equivalent to a
Shaw-value bound with the same constant, and the same normalized object lies in the sharp closed
corridor `√(1-1/n)/√L ≤ Sh(M(μ_n)) ≤ √(n/L)`.  This bundles the Lane-2 reduction and the
sharp unconditional bracket into one citable statement.  The theorem is pure normalization plus
previously proven floor/ceiling rungs: it does not prove the missing `O(1)` upper bound. -/
theorem concrete_worstPeriod_shawValue_capstone {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) {C L : ℝ} (hL : 0 < L) :
    (worstPeriod ψ G hne ≤ C * prizeScale (G.card : ℝ) L
        ↔ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L ≤ C)
      ∧ Real.sqrt (1 - 1 / (G.card : ℝ)) / Real.sqrt L
          ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) := by
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by linarith
  exact ⟨prizeBound_worstPeriod_iff_shawValue_le_of_pos G hne hnpos hL,
    shawValue_worstPeriod_sharp_bracket hψ G hne hq1 hG1 hsq hL⟩

end ProximityGap.Frontier.ConcreteShawValueBridge

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteShawValueBridge.shawValue_worstPeriod_sharp_floor
#print axioms ProximityGap.Frontier.ConcreteShawValueBridge.shawValue_worstPeriod_sharp_bracket
#print axioms ProximityGap.Frontier.ConcreteShawValueBridge.concrete_worstPeriod_shawValue_capstone
