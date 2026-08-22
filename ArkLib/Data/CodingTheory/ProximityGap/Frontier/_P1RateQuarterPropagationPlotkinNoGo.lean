/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# P1 propagation cannot be forced from secant-core cardinality alone

The pencil-propagation brick identifies two degree-`<K` pencils once their two-label data agree on
`K` domain points.  The forced-secant matching supplies cores of size at least `K`.  It is tempting
to apply the constant-weight Plotkin bound a second time to force two such cores to overlap in
`K` points, then consolidate their pencils.

At the exact P1 parameters this second Plotkin step is arithmetically impossible.  Its denominator
`K^2 - N*(K-1)` is nonpositive.  Even the elementary inclusion-exclusion floor is zero because
`2K ≤ N`.  Therefore the propagation theorem is a valid gluing consumer, but extracting its
overlap requires polynomial geometry or a support-dependent determinant invariant; core sizes
alone cannot provide it.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPropagationPlotkinNoGo

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension and forced-secant core weight. -/
abbrev K : Nat := 2 ^ 28

/-- The second-stage Plotkin denominator for weight-`K` secant cores and overlap cap `K-1` is
nonpositive at `N=2^30`, `K=2^28`. -/
theorem secantCore_plotkin_denominator_nonpositive :
    K ^ 2 ≤ N * (K - 1) := by
  norm_num [N, K]

/-- There is no positive inclusion-exclusion overlap floor for two `K`-subsets of the P1 domain. -/
theorem two_secantCore_weights_fit_in_domain :
    2 * K ≤ N := by
  norm_num [N, K]

/-- Exact slack in the elementary obstruction: two disjoint `K`-cores leave half the domain
unused. -/
theorem domain_sub_two_secantCore_weights :
    N - 2 * K = 2 ^ 29 := by
  norm_num [N, K]

end ArkLib.ProximityGap.Frontier.P1RateQuarterPropagationPlotkinNoGo

open ArkLib.ProximityGap.Frontier.P1RateQuarterPropagationPlotkinNoGo

#print axioms secantCore_plotkin_denominator_nonpositive
#print axioms two_secantCore_weights_fit_in_domain
#print axioms domain_sub_two_secantCore_weights
