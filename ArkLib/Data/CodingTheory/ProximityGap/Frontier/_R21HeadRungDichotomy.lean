/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19RungRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18PlateauLaw

/-!
# LANE HEADRUNG (#466 round 21): the head-rung dichotomy — sub-Wick monotonicity
  `L_r ≤ 1` is EXACTLY as phase-deep as the away-sup at rungs `r < (Λ−1)/2`,
  and automatic above

The object: `L_r := S_{r+1}^D / ((2r+1)·Σ·S_r^D)` (the per-rung sub-Wick multiplier of
R19/R20; `S_r^D = rungMoment`, `Σ = ∑_{b∈H}‖η_b‖²`, `Λ = M²_away/Σ` the r19 sup ratio).
Sub-Wick monotonicity (`L_r ≤ 1` at every rung, zero violations in 16+ probed cells,
r ≤ 10) survived round 20 as an independent live conjecture. This lane pins WHERE its
content lives.

## PROBE VERDICT (`probe_r21_headrung.py` — scratchpad; exact FFT; 12 stabilized cells
   `μ_n ⊆ H`, n ∈ {8,16}, m ∈ {2,4}, p ≤ 65537; + spike-phase adversary, 5 cells)

* **(A) The exact free-measure maximum is `L_r = Λ/(2r+1)`, attained.** Over ALL
  magnitude configurations (nonneg values `x_s ≤ M²` with any first-moment budget) the
  ratio `S_{r+1}/S_r` has supremum exactly `M²` — the flat/spike configuration attains it
  (`freeMeasure_step_eq` below), and the pointwise cap gives the matching upper bound
  (`freeMeasure_step_le`). Random search (2000 restarts × 4 shapes) never beats the spike.
* **(B) True cells: `L_r ≤ 1` always (L₁ ∈ [0.31, 0.85]), while the free-measure max
  `Λ/3` exceeds 1 in 9 of 12 cells (up to 4.14 at Λ = 12.43).** So at rung 1 the
  conjecture is NOT magnitude-provable in any cell with `Λ > 3`.
* **(D) The no-go is REALIZED inside the fixed-magnitude class**: keeping the TRUE
  `|η_b|` multiset on `H` and aligning all phases at one away offset
  (`w_b = |η_b|·e^{−2πi b s*/p}`) breaks `L₁ ≤ 1` in EVERY probed cell — L₁ = 38.7
  (p=1009), 423.0 (p=12289, the cell hill-climbing alone had not broken), 2367.1
  (p=65537). Hill-climb from random phases confirms (L₁ up to 8.41). **Sub-Wick
  monotonicity at head rungs is PHASE-DEEP: it is a property of the Gauss-period phases,
  false for generic/adversarial phases with the same magnitudes.**
* **(C) Direction correction (the lane brief guessed the reverse):** `L₁ ≤ 1` is
  STRICTLY STRONGER than the constant-3 r=2 rung, not weaker. Via the r18 depletion
  identity `S₁^D = qΣ − ‖I(0)‖² − Σ²/n`, `L₁ ≤ 1 ⟺ S₂^D ≤ 3qΣ²·(1 − depl/qΣ)` with
  measured `depl/qΣ ∈ [0.24, 0.51]` — so closing rung-1 head from the r=2 chain needs a
  depleted constant `C ≤ 3(1 − depl/qΣ) ≈ 1.5–2.3`, i.e. exactly the `DepletedWickR2`
  object that round 19 refuted per-instance. **The head rung does NOT close
  Stepanov-conditionally through the constant-3 rung.** The true implication runs the
  other way (`constant3_of_headRung1` below).

## What THIS file proves (all axiom-clean; no Weil, no analysis)

* `headRung_of_awaySupBound` — the automatic side of the dichotomy: `AwaySupBound C`
  with `C ≤ 2r+1` gives the rung-r sub-Wick step `S_{r+1}^D ≤ (2r+1)·Σ·S_r^D`
  (i.e. `L_r ≤ 1`). So at rungs `r ≥ (Λ−1)/2` monotonicity is FREE given the sup.
* `freeMeasure_step_le` / `freeMeasure_step_eq` — the exact free-measure maximum:
  `∑ x^{r+1} ≤ M²·∑ x^r` for `x ≤ M²` pointwise, with EQUALITY at the flat spike —
  the magnitude-only sup of `S_{r+1}/S_r` is exactly `M²`, hence of `L_r` exactly
  `Λ/(2r+1)`.
* `magnitudeOnly_headRung_no_go` — for every `r` and every `Λ > 2r+1` an explicit
  nonneg configuration with `∑x^{r+1} > (2r+1)·Σ·∑x^r`: no magnitude-only argument can
  prove `L_r ≤ 1` below the threshold rung `(Λ−1)/2`.
* `rungMoment_one_le_parseval` + `constant3_of_headRung1` — the (C) direction, sound
  half: `S₁^D ≤ qΣ` (from the R18 all-offset Parseval, primitive `ψ`), hence
  `L₁ ≤ 1 ⟹ S₂^D ≤ 3qΣ²` (the constant-3 rung). The converse is FALSE-in-content
  (needs the refuted depleted constant — probe (C) above).

## The dichotomy (the lane's deliverable, honest form)

For every rung `r`: `L_r ≤ 1` is magnitude-provable **iff** `2r+1 ≥ Λ` — i.e. iff the
away-sup bound at constant `C = 2r+1` already holds. Below that threshold it is
phase-deep (explicit adversary in the fixed-magnitude class), above it is a corollary of
the sup. **Sub-Wick monotonicity at head rungs carries NO content independent of
`AwaySupBound`: it is the wall's shadow, not a separate lever.** The standalone-algebra
hope of the round-20 correction is hereby closed. Issue #466, round 21, LANE HEADRUNG.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R19RungRecursion

namespace ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The automatic side: `AwaySupBound C`, `C ≤ 2r+1` ⟹ the rung-r sub-Wick step. -/

/-- **Head rungs are free given the sup.** If `sup_{s∉D}‖I‖² ≤ C·Σ` with `C ≤ 2r+1`, then
`S_{r+1}^D ≤ (2r+1)·Σ·S_r^D` — sub-Wick monotonicity at rung `r` (`L_r ≤ 1`). -/
theorem headRung_of_awaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ} (r : ℕ)
    (hCr : C ≤ (2 * r + 1 : ℝ)) (h : AwaySupBound ψ G H D C) :
    rungMoment ψ G H D (r + 1)
      ≤ ((2 * r + 1 : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  refine sup_split_recursion ψ G H D _ (fun s hs => ?_) r
  calc ‖incidenceSum ψ G H s‖ ^ 2
      ≤ C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := h s hs
    _ ≤ (2 * r + 1 : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCr hSig

/-! ### (2) The exact free-measure maximum of the rung step. -/

/-- **Free-measure upper bound**: if every value is capped by `M2`, then
`∑ x^{r+1} ≤ M2·∑ x^r`. (The `L_r ≤ Λ/(2r+1)` upper half of the exact maximum.) -/
theorem freeMeasure_step_le {α : Type*} (s : Finset α) (x : α → ℝ) (M2 : ℝ) (r : ℕ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hxM : ∀ i ∈ s, x i ≤ M2) :
    (∑ i ∈ s, x i ^ (r + 1)) ≤ M2 * ∑ i ∈ s, x i ^ r := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc x i ^ (r + 1) = x i * x i ^ r := by rw [pow_succ']
    _ ≤ M2 * x i ^ r :=
        mul_le_mul_of_nonneg_right (hxM i hi) (pow_nonneg (hx0 i hi) r)

/-- **Free-measure saturation**: the flat spike `x ≡ M2` attains the cap with EQUALITY:
`∑ x^{r+1} = M2·∑ x^r`. Together with `freeMeasure_step_le`, the magnitude-only supremum
of the rung step `S_{r+1}/S_r` is EXACTLY `M2`, hence of `L_r` exactly `Λ/(2r+1)`. -/
theorem freeMeasure_step_eq {α : Type*} (s : Finset α) (M2 : ℝ) (r : ℕ) :
    (∑ _i ∈ s, M2 ^ (r + 1)) = M2 * ∑ _i ∈ s, M2 ^ r := by
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, pow_succ']
  ring

/-- **The magnitude-only no-go.** For every rung `r`, whenever the sup ratio exceeds the
Wick budget (`M2 > (2r+1)·Σ`, i.e. `Λ > 2r+1`), the flat-spike configuration on any
nonempty index set VIOLATES the sub-Wick step: `∑x^{r+1} > (2r+1)·Σ·∑x^r`. No
magnitude-only argument (any function of the value multiset respecting the cap) can prove
`L_r ≤ 1` at rungs `r < (Λ−1)/2`. Probe (D): this adversary is REALIZED with the true
`|η_b|` multiset by phase alignment — the no-go is not an artifact of the abstraction. -/
theorem magnitudeOnly_headRung_no_go {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {M2 Sig : ℝ} (r : ℕ) (hM2 : 0 < M2) (hΛ : (2 * r + 1 : ℝ) * Sig < M2) :
    ((2 * r + 1 : ℝ) * Sig) * (∑ _i ∈ s, M2 ^ r) < ∑ _i ∈ s, M2 ^ (r + 1) := by
  rw [freeMeasure_step_eq s M2 r]
  have hpow : (0 : ℝ) < ∑ _i ∈ s, M2 ^ r := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast Finset.card_pos.mpr hs) (pow_pos hM2 r)
  exact mul_lt_mul_of_pos_right hΛ hpow

/-! ### (3) The (C) direction, sound half: `L₁ ≤ 1` IMPLIES the constant-3 rung
(not the reverse — the lane brief's guess is corrected in the header). -/

/-- `S₁^D ≤ q·Σ`: the away first moment is dominated by the all-offset Parseval total
(R18 `incidenceSum_sq_sum_offsets`, primitive `ψ`; the deleted diagonal only helps). -/
theorem rungMoment_one_le_parseval (G H D : Finset F) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    rungMoment ψ G H D 1
      ≤ (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  have hbridge : ∀ s : F,
      ArkLib.ProximityGap.Frontier.R18PlateauLaw.incidenceSum ψ G H s
        = incidenceSum ψ G H s := fun _ => rfl
  have htot := ArkLib.ProximityGap.Frontier.R18PlateauLaw.incidenceSum_sq_sum_offsets
    hψ G H
  simp only [hbridge] at htot
  calc rungMoment ψ G H D 1
      = ∑ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ (2 * 1) := rfl
    _ ≤ ∑ s : F, ‖incidenceSum ψ G H s‖ ^ (2 * 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun i _ _ => pow_nonneg (norm_nonneg _) _)
    _ = (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
        simpa using htot

/-- **`L₁ ≤ 1` ⟹ the constant-3 r=2 rung**: `S₂^D ≤ 3·Σ·S₁^D ≤ 3qΣ²`. The converse
FAILS in content: by the depletion identity it would require the per-instance-refuted
depleted constant `C ≤ 3(1 − depl/qΣ)` (probe (C); r19 `DepletedWickR2` refutation).
So the rung-1 head case does NOT close conditionally through the Stepanov r=2 chain. -/
theorem constant3_of_headRung1 (G H D : Finset F) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive)
    (hL1 : rungMoment ψ G H D 2
      ≤ (3 : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D 1) :
    rungMoment ψ G H D 2
      ≤ (3 : ℝ) * (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  have hS1 := rungMoment_one_le_parseval G H D hψ (ψ := ψ)
  calc rungMoment ψ G H D 2
      ≤ (3 : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D 1 := hL1
    _ ≤ (3 : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * ((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left hS1 ?_
        positivity
    _ = (3 : ℝ) * (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by ring

/-! ### (4) The named residual: sub-Wick monotonicity, now correctly located. -/

/-- **The head-rung sub-Wick Prop** (the round-20 independent conjecture, named).
By this file's dichotomy: at rungs `r` with `2r+1 ≥ Λ` it FOLLOWS from `AwaySupBound`
(`headRung_of_awaySupBound`); at rungs `r` with `2r+1 < Λ` it is phase-deep
(`magnitudeOnly_headRung_no_go` + the realized spike-phase adversary) — i.e. it carries
no content independent of the wall. Kept as a named Prop for downstream wiring. -/
def HeadRungSubWick (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) : Prop :=
  rungMoment ψ G H D (r + 1)
    ≤ ((2 * r + 1 : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * rungMoment ψ G H D r

/-- Restatement: the automatic side, in the named form. -/
theorem headRungSubWick_of_awaySupBound (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ}
    (r : ℕ) (hCr : C ≤ (2 * r + 1 : ℝ)) (h : AwaySupBound ψ G H D C) :
    HeadRungSubWick ψ G H D r :=
  headRung_of_awaySupBound ψ G H D r hCr h

end ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.headRung_of_awaySupBound
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.freeMeasure_step_le
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.freeMeasure_step_eq
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.magnitudeOnly_headRung_no_go
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.rungMoment_one_le_parseval
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.constant3_of_headRung1
#print axioms ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy.headRungSubWick_of_awaySupBound
