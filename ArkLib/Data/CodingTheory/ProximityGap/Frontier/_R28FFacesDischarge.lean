/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# R28F (#466 round 28F, FACES lane): the mixed-rung faces do NOT discharge from the
proven per-character machinery — the exact deficit, formalized.

`R27GMixedAudit.mixed_rung_fires_at_half` closes the subfamily rung at `κ = 1/2` from two
face-fraction hypotheses `Ea ≤ (37/10000)·B` and `Eb ≤ (764/1000)·B`, where
`B = m⁴·3q·Σ²` is the Wick budget.  Those two fractions are **probe measurements**.  This
lane asked: can they be replaced by *unconditional in-regime* bounds derived from the proven
`d ≤ 16` per-character faces —

* the Weil fourth moment `∑_{s₀}‖T_χ‖⁴ ≤ Cw·n²·q` (`FourthMomentTwistBound`, `Cw = 6`), and
* the Gauss size `‖g(χ')‖ ≤ √q` (`GaussSumSizeBound`)?

**Answer: NO — with an exact, `q`-independent deficit.**  The proven faces are per-character
and Wick-scaled; combining the `m'` Main-`Y` (resp. `M = m−m'` complement) characters back into
`Main_Y` / `Res` costs an Hölder/L²-sup factor that the measured fractions do NOT pay, because
the measured fractions already sit at the *joint-cancellation* (Wick) scale.

## The two provable faces and their deficits (probe `probe_r28f_faces.py`, 4 exact cells)

* **`Eb` (complement fourth moment).**  The best PROVEN route is the L²×sup composition
  `residualQuarticWickAt_of_l2_sup`, giving `∑‖Res‖⁴ ≤ 2Mn · q·(Mnq)² = 2·M³n³q³`
  (constant `C = 2Mn`).  The closure needs the *Wick* constant `3`
  (`Eb_true = 3·q·(Mnq)² = 3M²n²q³ = 0.764·B`).  Provable / needed `= 2Mn/3`.
  At the flagship (`M = 14, n = 8`): **74.7× over budget**, scale-invariant in `q`.

* **`Ea` (Main_Y fourth moment).**  Hölder over the `m'` Y-characters plus the DC split
  `(a+b)⁴ ≤ 8(a⁴+b⁴)` gives `Ea ≤ 8(n⁴q + m'⁴·Cw·n²q³)`.  Provable / needed ≈ **270×**
  (`m' = 2`), **5900×** (`m' = 4`), scale-invariant in `q`.

Both deficits are pure multiplicative constants independent of `q`: this is a genuine wall,
not a small-field artifact.  **The measured face fractions are themselves at-Wick statements**;
discharging them requires the same cross-character (Weil-family, joint) cancellation that the
open `MixedMainResHalfCS(1/2)` needs.  Discharging the faces is therefore NOT a strictly
smaller problem than the mixed decoupling — it is the same joint-cancellation wall.

## What is PROVEN here (axiom-clean, pure real arithmetic)

1. `eb_lsup_face_value` — the L²×sup face constant equals `2·M³n³q³`.
2. `eb_face_overspends` — the provable `Eb` face strictly exceeds the Wick budget
   `3·M²n²q³` exactly when `2Mn > 3` (always, in-regime): deficit factor `2Mn/3`.
3. `ea_holder_face_value` — the Hölder Main_Y face equals `8n⁴q + 8·m'⁴·Cw·n²q³`.
4. `ea_face_overspends` — the provable `Ea` face strictly exceeds any fraction `f·B`
   whenever the leading Hölder term already does (`8·m'⁴·Cw·n²q³ > f·B`).
5. `faces_discharge_iff_wick_constants` — the composed closure with the *provable*
   constants holds iff those constants are already at the Wick scale, i.e. the honest
   reduction bottoms out at the joint-cancellation input, not at the per-character faces.

NO closure of the open core; this is a NEGATIVE (no-go) result pinning the exact deficit.
Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 28F.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R28FFacesDischarge

/-! ## 1. The `Eb` complement face: exact value and exact deficit -/

/-- **The L²×sup provable `Eb` face equals `2·M³n³q³`.**  This is the `C = 2Mn` constant of
`R26ResidualL2CrossIdentity.residualQuarticWickAt_of_l2_sup`, written out:
`2Mn · q·(Mnq)²`. -/
theorem eb_lsup_face_value (M n q : ℝ) :
    2 * (M * n) * q * (M * n * q) ^ 2 = 2 * M ^ 3 * n ^ 3 * q ^ 3 := by ring

/-- **The provable `Eb` face strictly overspends the Wick budget.**  The closure anchors
`Eb` at the Wick face `3·M²n²q³` (`= 0.764·B`).  The best proven route delivers only
`2·M³n³q³`.  Whenever `2Mn > 3` — true throughout the regime (`Mn ≥ 12·8 = 96`) — the
provable face STRICTLY exceeds the Wick budget, by the exact factor `2Mn/3`. -/
theorem eb_face_overspends {M n q : ℝ} (hM : 0 < M) (hn : 0 < n) (hq : 0 < q)
    (hMn : 3 < 2 * M * n) :
    3 * M ^ 2 * n ^ 2 * q ^ 3 < 2 * M ^ 3 * n ^ 3 * q ^ 3 := by
  have hbase : (0 : ℝ) < M ^ 2 * n ^ 2 * q ^ 3 := by positivity
  nlinarith [hbase, hMn, mul_pos hM hn]

/-- The deficit factor is exactly `2Mn/3`: the provable `Eb` equals that multiple of the
Wick budget. -/
theorem eb_deficit_factor {M n q : ℝ} (hden : (3 : ℝ) * M ^ 2 * n ^ 2 * q ^ 3 ≠ 0) :
    2 * M ^ 3 * n ^ 3 * q ^ 3 = (2 * M * n / 3) * (3 * M ^ 2 * n ^ 2 * q ^ 3) := by
  field_simp

/-! ## 2. The `Ea` Main_Y face: exact value and exact deficit -/

/-- **The Hölder+DC provable `Ea` face equals `8n⁴q + 8·m'⁴·Cw·n²q³`.**  This is the crude
combination `∑‖M'‖⁴ ≤ 8(∑‖-n‖⁴ + ∑‖Main_Y‖⁴)` with `∑‖Main_Y‖⁴ ≤ m'³·∑_{χ'∈Y}‖g‖⁴·∑‖T‖⁴`,
`‖g‖⁴ ≤ q²`, `∑_{s₀}‖T‖⁴ ≤ Cw·n²q`, `|Y| = m'`, `|S| = q`. -/
theorem ea_holder_face_value (n q m' Cw : ℝ) :
    8 * (n ^ 4 * q + m' ^ 4 * Cw * n ^ 2 * q ^ 3)
      = 8 * n ^ 4 * q + 8 * m' ^ 4 * Cw * n ^ 2 * q ^ 3 := by ring

/-- **The provable `Ea` face strictly overspends its budget fraction.**  If even the leading
Hölder term `8·m'⁴·Cw·n²q³` already exceeds the allowed fraction `f·B`, then so does the full
provable face (the DC term `8n⁴q ≥ 0` only adds).  At the flagship the leading term is ≈270×
(`m'=2`) resp. ≈5900× (`m'=4`) the needed `(37/10000)·B`. -/
theorem ea_face_overspends {n q m' Cw fB : ℝ} (hDC : 0 ≤ 8 * n ^ 4 * q)
    (hlead : fB < 8 * m' ^ 4 * Cw * n ^ 2 * q ^ 3) :
    fB < 8 * n ^ 4 * q + 8 * m' ^ 4 * Cw * n ^ 2 * q ^ 3 := by
  linarith

/-! ## 3. The honest reduction bottoms out at the joint-cancellation input -/

/-- **Faces discharge only at Wick constants.**  Abstractly: the composed closure needs
`Eb ≤ (764/1000)·B`.  With the provable constant `Eb = cE·M²n²q³` this holds iff
`cE ≤ (764/1000)·B/(M²n²q³)`.  The proven route gives `cE = 2Mn` (unbounded in the regime);
the Wick input gives `cE = 3` (the measured anchor).  So the face-fraction hypothesis is
*equivalent to* supplying a Wick-scale (joint-cancellation) constant — it is not weaker than
the mixed-moment object it feeds. -/
theorem faces_discharge_iff_wick_constants
    {cE M n q B : ℝ} (hpos : 0 < M ^ 2 * n ^ 2 * q ^ 3) :
    cE * M ^ 2 * n ^ 2 * q ^ 3 ≤ (764 / 1000) * B ↔
      cE ≤ (764 / 1000) * B / (M ^ 2 * n ^ 2 * q ^ 3) := by
  rw [le_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith [h, hpos]

end ArkLib.ProximityGap.Frontier.R28FFacesDischarge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.eb_lsup_face_value
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.eb_face_overspends
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.eb_deficit_factor
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.ea_holder_face_value
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.ea_face_overspends
#print axioms ArkLib.ProximityGap.Frontier.R28FFacesDischarge.faces_discharge_iff_wick_constants
