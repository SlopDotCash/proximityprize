/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Rate-quarter many-line common-factor ownership barrier

This file records the kernel-cheap arithmetic certificate needed for five
primitive-cluster lines.  Let `M` be the total baseline maximum-component core
mass, `G` the mass turned into new all-line common roots, and `H` the hole mass.
If the scalar budget is at least the coordinate budget, then

```text
G <= (L-1) H.
```

If every core has size at least `z`, total core incidence gives

```text
L z + H <= M + (L-1) G.
```

For `L = 5`, with common-factor budget `G<=m`, eliminating `H` yields

```text
20z <= 4M + 15m.
```

For five pairwise split-cubic quotient lines on `mu_16`, the ten pair
differences contribute only `3*C(5,2)=30` pair-equality incidences.  If `s_e`
is the largest value-component size at quotient coordinate `e`, the elementary
pointwise inequality

```text
2 s_e <= C(s_e,2)+3
```

gives `sum_e s_e <= 39`.  Therefore `M<=39m`.  With `D<=m`, every five-line
common-factor amplifier satisfies

```text
20z <= 171m,
6z < 53m.
```

Thus no five-line universal split-cubic clique can beat the saturated
three-line threshold `53m/6`.  This is an architecture-local upper bound, not
a global rate-quarter list-decoding lower bound.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.RateQuarterManyLineOwnershipBarrier

/-- After summing the pointwise inequalities over the sixteen quotient
coordinates, pair-equality cost at most `30` forces maximum-component mass at
most `39`.  Keeping the summation outside this lemma avoids expensive finite
sum elaboration in this frontier certificate. -/
theorem maxComponentMass_le_thirtyNine_of_aggregate
    {componentMass pairCost : Nat}
    (hpointSum : 2 * componentMass ≤ pairCost + 48)
    (hpair : pairCost ≤ 30) :
    componentMass ≤ 39 := by
  omega

/-- The sharper division-free five-line endpoint used by the preceding
strict comparison. -/
theorem fiveLine_twenty_mul_core_le_171_mul
    {z m M H G : Nat}
    (hbase : M ≤ 39 * m)
    (hlabels : G ≤ 4 * H)
    (hcore : 5 * z + H ≤ M + 4 * G)
    (hcommon : G ≤ m) :
    20 * z ≤ 171 * m := by
  omega

/-- Five lines with baseline maximum-component mass at most `39m` and common
factor degree at most `m` cannot reach the saturated three-line core density
`53m/6`. -/
theorem fiveLine_core_lt_threeLine_saturated
    {z m M H G : Nat}
    (hm : 0 < m)
    (hbase : M ≤ 39 * m)
    (hlabels : G ≤ 4 * H)
    (hcore : 5 * z + H ≤ M + 4 * G)
    (hcommon : G ≤ m) :
    6 * z < 53 * m := by
  have htwenty := fiveLine_twenty_mul_core_le_171_mul
    hbase hlabels hcore hcommon
  omega

end ArkLib.ProximityGap.Frontier.RateQuarterManyLineOwnershipBarrier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterManyLineOwnershipBarrier
#print axioms maxComponentMass_le_thirtyNine_of_aggregate
#print axioms fiveLine_twenty_mul_core_le_171_mul
#print axioms fiveLine_core_lt_threeLine_saturated
