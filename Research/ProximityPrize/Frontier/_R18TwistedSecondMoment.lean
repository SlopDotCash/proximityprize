/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._R18SigmaEquidistribution

/-!
# Round 18: twisted second-moment core for Σ-equidistribution (compatibility re-export)

This file originally extracted the first analytic component of `_R18SigmaEquidistribution`:

* exact expansion of the `χ`-twisted second moment of the period weights into Gauss sums;
* the triangle/Gauss-sum bound
  `‖∑_b χ(b)‖η_b‖²‖ ≤ |G|(|G|-1)√q`.

**Deduplicated (2026-10-29 audit CW-B10-06).**  Every theorem here had the same statement
and proof skeleton as its namesake in `_R18SigmaEquidistribution` (and `hSig_of_gchi` is
`R18SigmaEquidistribution.hSig_of_regime`).  The canonical proofs now live only in
`_R18SigmaEquidistribution`; the names below are aliases kept for backward compatibility.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment

alias twisted_secondMoment_eq_gaussSums :=
  R18SigmaEquidistribution.twisted_secondMoment_eq_gaussSums
alias norm_twisted_secondMoment_le := R18SigmaEquidistribution.norm_twisted_secondMoment_le
alias sigma_indicator_decomp := R18SigmaEquidistribution.sigma_indicator_decomp
alias eta_zero := R18SigmaEquidistribution.eta_zero
alias trivial_term_eq := R18SigmaEquidistribution.trivial_term_eq
alias sigma_lower_bound := R18SigmaEquidistribution.sigma_lower_bound
alias sigmaLowerEnvelope_of_gchi := R18SigmaEquidistribution.sigmaLowerEnvelope_of_gchi
/-- Compact-core `hSig` corollary (alias of `R18SigmaEquidistribution.hSig_of_regime`). -/
alias hSig_of_gchi := R18SigmaEquidistribution.hSig_of_regime
alias wickAwayAtWithConstant_two_of_gchi_quarticWeil :=
  R18SigmaEquidistribution.wickAwayAtWithConstant_two_of_gchi_quarticWeil

end ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.twisted_secondMoment_eq_gaussSums
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.norm_twisted_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigma_indicator_decomp
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.eta_zero
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.trivial_term_eq
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigma_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.sigmaLowerEnvelope_of_gchi
#print axioms ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.hSig_of_gchi
#print axioms
  ArkLib.ProximityGap.Frontier.R18TwistedSecondMoment.wickAwayAtWithConstant_two_of_gchi_quarticWeil
