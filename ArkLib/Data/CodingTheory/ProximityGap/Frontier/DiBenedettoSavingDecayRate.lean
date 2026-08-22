/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DiBenedettoSavingTendsto

/-!
# di Benedetto near-Sidon saving: the EXACT `Theta(1/log n)` decay rate (#444, constant-factor lane)

`DiBenedettoSavingTendsto.lean` proved the realised dyadic saving `-> 1/24` (the supremum is the
limit), and `DiBenedettoFiniteNSavingBelow.lean` proved it stays `< 1/24` strictly at every finite
`n`. Both files note (as PROSE, never a theorem) that the convergence is SLOW, `O(1/log n)`. This file
lands the EXACT first-order decay rate: the shortfall `1/24 - saving` times `log n` converges to a
nonzero constant, so the shortfall is `Theta(1/log n)` with an explicit constant.

## The exact constant

Writing `gap(n) := 1/24 - diBenedettoSaving (t2 n) (t3 n)` with the realised exponents
`t_k(n) = logb n (E_k n)`, the saving formula gives
`gap(n) = (2*(t3(n) - 3) + (t2(n) - 2)/2) / 72`, and `(t_k(n) - k)*log n = log(E_k n) - k*log n`
is precisely the quantity that `DiBenedettoSavingTendsto`'s `energy{Two,Three}_logDiff_tendsto`
shows converges to `log c_k` (`c_2 = 3`, `c_3 = 15`). Hence

  `gap(n) * log n = (2*(log(E3 n) - 3 log n) + (log(E2 n) - 2 log n)/2)/72`
                `-> (2*log 15 + (log 3)/2) / 72 =: decayConst`.

So `(1/24 - saving) ~ decayConst / log n`, a precise `Theta(1/log n)` law (the constant is positive:
`2 log 15 + (log 3)/2 > 0`), confirming the energy route reaches its `1/24` ceiling only at the
logarithmically-slow rate the prose claimed.

## Probe (`/tmp/probe_dib_decay_const.py`, char-0 closed forms, `n = 2^10..2^100`)
`gap(n)*ln n -> 0.0828528687...` matching `(2 ln 15 + (ln 3)/2)/72` to `< 1e-16` at `n = 2^30+`. The
shortfall is `Theta(1/log n)` with this exact constant. 0 fails.

## HONESTY (rules 1, 3, 6 + ASYMPTOTIC GUARD)
NOT a CORE closure. A QUANTITATIVE refinement of the proven saving-limit: the energy method's saving
approaches its `1/24` ceiling at the exact rate `decayConst/log n`. A NEGATIVE / boundary result on a
route `12x` short of the prize cancellation exponent `1/2`; makes NO capacity / beyond-Johnson /
growth-law claim. Pure `R`/`logb` real-analysis on the proven exact-value char-0 energies;
FIELD-UNIVERSAL (the saving formula is thickness-blind). Touches NEITHER `delta*` NOR the cliff-at-`n/2`
incidence object. EXTEND-proven, it reuses `DiBenedettoSavingTendsto`'s `logDiff` limits VERBATIM (no
new analytic input). The char-`p` transfer at `p = n^4` is a separate open input. ONE sweep, ONE commit.
CORE `M(mu_n) <= C*sqrt(n*log(p/n))` UNCHANGED / OPEN. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Filter Topology Real

namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- **The exact first-order decay constant** of the di Benedetto near-Sidon saving shortfall:
`decayConst = (2*log 15 + (log 3)/2)/72`. The shortfall `1/24 - saving(n)` is asymptotic to
`decayConst / log n`. -/
noncomputable def decayConst : ℝ := (2 * Real.log 15 + Real.log 3 / 2) / 72

/-- `decayConst > 0` (both `log 15` and `log 3` are positive), so the shortfall is genuinely
`Theta(1/log n)`, not `o(1/log n)`. -/
theorem decayConst_pos : 0 < decayConst := by
  have h15 : 0 < Real.log 15 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold decayConst; positivity

/-- **HEADLINE, the exact `Theta(1/log n)` decay rate.** The realised saving shortfall against the
near-Sidon ceiling `1/24`, scaled by `log n`, converges to the positive constant
`decayConst = (2*log 15 + (log 3)/2)/72`:

  `(1/24 - diBenedettoSaving (t2 n) (t3 n)) * log n  ->  decayConst`.

Mechanism: `gap(n)*log n = (2*(log(E3 n) - 3 log n) + (log(E2 n) - 2 log n)/2)/72`, whose two inner
differences are EXACTLY the convergent quantities of `energy{Two,Three}_logDiff_tendsto`
(`-> log 3`, `-> log 15`). So the energy method's saving meets its `1/24` ceiling only at the
logarithmically-slow rate `decayConst/log n`. -/
theorem realisedSaving_shortfall_mul_log_tendsto :
    Tendsto (fun n => (1 / 24 - diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n))
      * Real.log n) atTop (nhds decayConst) := by
  -- the two convergent log-differences (reused verbatim from the limit file)
  have h2 := energyTwo_logDiff_tendsto       -- log(E2 n) - 2 log n -> log 3
  have h3 := energyThree_logDiff_tendsto     -- log(E3 n) - 3 log n -> log 15
  -- target combination tends to decayConst
  have hcomb : Tendsto (fun n =>
      (2 * (Real.log (energyThree n) - 3 * Real.log n)
        + (Real.log (energyTwo n) - 2 * Real.log n) / 2) / 72) atTop (nhds decayConst) := by
    have : Tendsto (fun n =>
        (2 * (Real.log (energyThree n) - 3 * Real.log n)
          + (Real.log (energyTwo n) - 2 * Real.log n) / 2) / 72) atTop
        (nhds ((2 * Real.log 15 + Real.log 3 / 2) / 72)) :=
      (((h3.const_mul 2).add (h2.div_const 2)).div_const 72)
    simpa [decayConst] using this
  -- the scaled shortfall EQUALS that combination, eventually (where log n != 0, i.e. n >= 2)
  have hev : (fun n => (1 / 24 - diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n))
      * Real.log n)
      =ᶠ[atTop] (fun n =>
        (2 * (Real.log (energyThree n) - 3 * Real.log n)
          + (Real.log (energyTwo n) - 2 * Real.log n) / 2) / 72) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
    have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
    have hne : Real.log n ≠ 0 := ne_of_gt hlogpos
    -- expand saving + realisedExp = logb n (E n) = log(E n)/log n, then clear log n
    unfold diBenedettoSaving realisedExp Real.logb
    field_simp
    ring
  exact hcomb.congr' hev.symm

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.decayConst_pos
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedSaving_shortfall_mul_log_tendsto
