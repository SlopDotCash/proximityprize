/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Master gap identity - the OFF-BY-ONE correction `capacity - delta* = m*/n` (#444)

@lalalune's 2026-06-16 audit (`docs/kb/deltastar-444-audit-corrections-2026-06-16.md`, S.A.1) caught
a convention off-by-one in the landed master-gap bricks `_BridgeB01.deltaStar_master_gap_identity`
and `_BridgeB04.deltaStarFormula`:

* Those bricks take the binding radius as `hdelta : delta* = 1 - (s* - 1)/n` (the orbcount script-
  display convention) and correctly derive `delta* = 1 - rho - (m* - 1)/n`, i.e.
  `capacity - delta* = (m* - 1)/n`. They are HONEST conditionals -- but on a hypothesis that
  encodes the off-by-one.
* The INCIDENCE-CORRECT binding radius (`delta`-close `<=>` agreement `>= (1 - delta) * n`, the
  governing law `I(delta) = #{gamma : word is delta-close to RS[k]}`) is `delta* = 1 - s*/n`. With
  THAT radius, the forced identity is `capacity - delta* = m*/n` (NOT `(m* - 1)/n`).

The audit [VERIFIED] the corrected exact pins: `delta*(8) = 3/8` (BELOW Johnson `1/2`),
`delta*(16) = 9/16` (ABOVE Johnson) -- and the corrected gap `m*/n` REPRODUCES them
(`cap - 3/8 = 3/8 = 3/8` at n=8; `cap - 9/16 = 3/16 = 3/16` at n=16), whereas the old `(m* - 1)/n`
does NOT. Probe `scripts/probes/probe_master_gap_offbyone.py` confirms (exact Q arithmetic over the
audit's own VERIFIED rows): corrected gap `= m*/n` matches the audit delta*; old gap is exactly
`1/n` too small; the old radius over-states delta* by exactly `1/n`.

## What this brick does (HONEST scope)

This is the pure Q-algebra CORRECTION of E1, mirroring `_BridgeB01` but with the incidence-correct
radius:

* `master_gap_identity_corrected` -- from `rho = k/n`, `m* = s - k`, and the CORRECT radius
  `delta* = 1 - s/n`, the forced identity is `delta* = 1 - rho - m*/n`.
* `capacity_gap_eq_corrected` -- equivalently `capacity - delta* = m*/n`.
* `old_radius_off_by_one_n` -- the two radius conventions differ by exactly `1/n`:
  `(1 - (s-1)/n) - (1 - s/n) = 1/n`, so the old radius over-states delta* by `1/n`.
* `old_gap_under_by_one_n` -- consequently the old gap `(m*-1)/n` is exactly `1/n` SMALLER than the
  corrected gap `m*/n`.
* The exact pins at the audit's VERIFIED rows: at n=8 (k=2, s*=5, m*=3) corrected delta* = 3/8 and
  gap = 3/8; at n=16 (k=4, s*=7, m*=3) corrected delta* = 9/16 and gap = 3/16. The old convention
  gives 1/2 and 5/8 (which MISS the audit's verified delta*).
* `corrected_crosses_johnson` -- the corrected delta* crosses Johnson `1/2` between n=8
  (`3/8 < 1/2`) and n=16 (`9/16 > 1/2`), the audit headline consequence (the old 0.5/0.625 hid it).

The genuine mathematical content NOT discharged here (that the operational sSup-delta* equals the
closed form at the binding `m*`) is exactly P1 + the cascade, upstream; here, as in B01/B04, the
radius form is the named hypothesis and the algebra is forced. This brick supplies the CORRECT
hypothesis and the corrected forced identity, plus the exact off-by-one delta between the two.

## Honesty

No `sorry`, no fake axiom. Pure Q `field_simp`/`ring` + `norm_num` over the exact rows.
This is a CONSTRAINT/CORRECTION brick (rule 4): it does NOT close CORE. It supplies the
audited-correct master gap identity and certifies the off-by-one in the two landed bricks, the
audit's exact VERIFIED delta* pins reproduced. No capacity / beyond-Johnson / sub-linear claim:
the corrected delta* values 3/8, 9/16 are exactly the audit's; the Johnson CROSSING is theirs too.
ASYMPTOTIC GUARD: no `c*/n -> 0`, cliff-at-`n/2` untouched. CORE `M(mu_n) <= C sqrt(n log(p/n))`
stays OPEN.

Issue #444.
-/

namespace ProximityGap.MasterGapOffByOneCorrected

/-- **The corrected master gap identity (Q algebra).**

From the rate definition `rho = k/n`, the binding-depth definition `m* = s - k`, and the
INCIDENCE-CORRECT binding radius `delta* = 1 - s/n` (`delta`-close iff agreement `>= (1-delta)*n`),
the corrected master gap identity `delta* = 1 - rho - m*/n` is forced. (Contrast
`_BridgeB01.deltaStar_master_gap_identity`, which uses the off-by-one radius `1 - (s-1)/n` and gets
`(m*-1)/n`.) -/
theorem master_gap_identity_corrected
    (n k s deltaStar rho mstar : ℚ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - s / n) :
    deltaStar = 1 - rho - mstar / n := by
  subst hρ hms hδ
  field_simp
  ring

/-- **The corrected capacity gap.** `capacity - delta* = m*/n`, where `capacity = 1 - rho`. -/
theorem capacity_gap_eq_corrected
    (n k s deltaStar rho mstar : ℚ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - s / n) :
    (1 - rho) - deltaStar = mstar / n := by
  have h := master_gap_identity_corrected n k s deltaStar rho mstar hn hρ hms hδ
  rw [h]; ring

/-- **The two radius conventions differ by exactly `1/n`.** The old (orbcount) radius
`1 - (s-1)/n` over-states the incidence-correct radius `1 - s/n` by `1/n`. -/
theorem old_radius_off_by_one_n (n s : ℚ) (hn : n ≠ 0) :
    (1 - (s - 1) / n) - (1 - s / n) = 1 / n := by
  field_simp
  ring

/-- **The old gap is `1/n` too small.** With `m* = s - k`, the corrected gap `m*/n` exceeds the old
gap `(m*-1)/n` by exactly `1/n` -- the off-by-one in `_BridgeB01`/`_BridgeB04`. -/
theorem old_gap_under_by_one_n (n mstar : ℚ) (hn : n ≠ 0) :
    mstar / n - (mstar - 1) / n = 1 / n := by
  field_simp
  ring

/-- n=8 row (audit VERIFIED): k=2, s*=5, m*=3, rho=1/4. The corrected delta* `= 1 - 5/8 = 3/8`
matches the audit (BELOW Johnson `1/2`); the corrected gap `= 3/8 = m*/n`. -/
theorem n8_corrected_deltaStar : (1 : ℚ) - 5 / 8 = 3 / 8 := by norm_num

theorem n8_corrected_gap : ((1 : ℚ) - 1 / 4) - (1 - 5 / 8) = 3 / 8 := by norm_num

/-- n=8: the OLD radius gives `1 - 4/8 = 1/2`, which MISSES the audit's VERIFIED `3/8`. -/
theorem n8_old_deltaStar_misses : (1 : ℚ) - 4 / 8 = 1 / 2 ∧ (1 : ℚ) - 4 / 8 ≠ 3 / 8 := by
  norm_num

/-- n=16 row (audit VERIFIED): k=4, s*=7, m*=3, rho=1/4. The corrected delta* `= 1 - 7/16 = 9/16`
matches the audit (ABOVE Johnson `1/2`); the corrected gap `= 3/16 = m*/n`. -/
theorem n16_corrected_deltaStar : (1 : ℚ) - 7 / 16 = 9 / 16 := by norm_num

theorem n16_corrected_gap : ((1 : ℚ) - 1 / 4) - (1 - 7 / 16) = 3 / 16 := by norm_num

/-- n=16: the OLD radius gives `1 - 6/16 = 5/8`, which MISSES the audit's VERIFIED `9/16`. -/
theorem n16_old_deltaStar_misses : (1 : ℚ) - 6 / 16 = 5 / 8 ∧ (1 : ℚ) - 6 / 16 ≠ 9 / 16 := by
  norm_num

/-- **The audit headline (corrected pins).** The corrected delta* CROSSES Johnson `1/2` between
n=8 (`3/8 < 1/2`, below) and n=16 (`9/16 > 1/2`, above) -- the structural fact the laundered
0.5/0.625 hid. Both delta* are exactly the audit's VERIFIED values. -/
theorem corrected_crosses_johnson :
    ((1 : ℚ) - 5 / 8 = 3 / 8) ∧ (3 / 8 < (1 : ℚ) / 2) ∧
    ((1 : ℚ) - 7 / 16 = 9 / 16) ∧ ((1 : ℚ) / 2 < 9 / 16) := by
  norm_num

end ProximityGap.MasterGapOffByOneCorrected

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.MasterGapOffByOneCorrected.master_gap_identity_corrected
#print axioms ProximityGap.MasterGapOffByOneCorrected.capacity_gap_eq_corrected
#print axioms ProximityGap.MasterGapOffByOneCorrected.old_radius_off_by_one_n
#print axioms ProximityGap.MasterGapOffByOneCorrected.old_gap_under_by_one_n
#print axioms ProximityGap.MasterGapOffByOneCorrected.corrected_crosses_johnson
