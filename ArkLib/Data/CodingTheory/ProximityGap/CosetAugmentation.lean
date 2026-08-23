/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BalancedFiveLaw

/-!
# The coset augmentation law: adjoining an order-4 coset preserves balance

Campaign #357. The depth-1 census table shows **dualities across rows** — at `n = 16` the
`a = 8` census set-equals the `a = 4` census and the `a = 13` census set-equals the
`a = 5` census. This file proves the mechanism behind the upward half:

> **`balanced_pairSums_coset_augment`** — adjoining a coset `x + {0, q, h, q+h}` of the
> order-4 subgroup to ANY multiset preserves antipodal balance of the pair sums, in both
> directions: `Balanced (pairSums (coset + A)) ↔ Balanced (pairSums A)`.

Mechanism: the coset's six internal sums form three antipodal fibers
(`{2x, 2x+h} + 2·{2x+q, 2x+q+h}` — the same cancellation as the five-set law), and the
cross sums against any `u` split as two antipodal pairs (`u+x` with `u+x+h`, `u+x+q` with
`u+x+q+h`) — the new sums are balanced *unconditionally*, so balance of the total is
balance of the old part (`balanced_add` / `balanced_residual`).

Census consequence (with `e₁(coset) = g^x(1+g^q)(1+g^h) = 0` in the field — the
`A5CensusValue` cancellation): a qualifying `a`-set with a disjoint coset available
augments to a qualifying `(a+4)`-set with the **same census value** — so
`census(a) ⊆ census(a+4)` whenever free cosets exist (e.g. `a = 4 → 8` for `m ≥ 4`, since
a structured 4-set occupies at most 3 of the `≥ 4` cosets). This is the proven half of the
measured `census(8) = census(4) = (n/2−1)²` duality; the reverse inclusion is the named
open follow-up.

## References

* Probe `probe_a58_census_table.py` (the duality data); issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.WindowTwoLayer

open Multiset

variable {R : Type*} [CommRing R] [DecidableEq R]

section Augment

variable {h q : R} (hh2 : h + h = 0)

include hh2

/-- A map and its `+h` translate are jointly balanced over any index multiset. -/
theorem balanced_map_pair (A : Multiset R) (f : R → R) :
    Balanced h (A.map f + A.map (fun u => f u + h)) := by
  intro t
  simp only [Multiset.count_add, Multiset.count_map]
  have e1 : Multiset.card (Multiset.filter (fun u => t + h = f u) A)
      = Multiset.card (Multiset.filter (fun u => t = f u + h) A) := by
    congr 1
    refine Multiset.filter_congr fun u _ => ?_
    constructor
    · intro hc
      linear_combination hc - hh2
    · intro hc
      linear_combination hc + hh2
  have e2 : Multiset.card (Multiset.filter (fun u => t + h = f u + h) A)
      = Multiset.card (Multiset.filter (fun u => t = f u) A) := by
    congr 1
    refine Multiset.filter_congr fun u _ => ?_
    constructor
    · intro hc
      linear_combination hc
    · intro hc
      linear_combination hc
  omega

/-- **The coset augmentation law**: adjoining an order-4 coset preserves balance of the
pair sums, in both directions. -/
theorem balanced_pairSums_coset_augment (hq : q + q = h) (x : R) (A : Multiset R) :
    Balanced h (pairSums (x ::ₘ (x + q) ::ₘ (x + h) ::ₘ (x + q + h) ::ₘ A))
      ↔ Balanced h (pairSums A) := by
  have e1 : (x + q) + (x + q + h) = x + x := by linear_combination hq + hh2
  have e2 : (x + h) + (x + q + h) = (x + x) + q := by linear_combination hh2
  have e3 : x + (x + q + h) = ((x + x) + q) + h := by ring
  have e4 : (x + q) + (x + h) = ((x + x) + q) + h := by ring
  have e5 : x + (x + h) = (x + x) + h := by ring
  have e6 : x + (x + q) = (x + x) + q := by ring
  have m1 : A.map (fun u => (x + h) + u) = A.map (fun u => (x + u) + h) :=
    Multiset.map_congr rfl fun u _ => by ring
  have m2 : A.map (fun u => (x + q + h) + u) = A.map (fun u => ((x + q) + u) + h) :=
    Multiset.map_congr rfl fun u _ => by ring
  have htotal : pairSums (x ::ₘ (x + q) ::ₘ (x + h) ::ₘ (x + q + h) ::ₘ A)
      = pairSums A + ((({x + x, (x + x) + h} : Multiset R)
          + ({(x + x) + q, ((x + x) + q) + h} + {(x + x) + q, ((x + x) + q) + h}))
        + ((A.map (fun u => x + u) + A.map (fun u => (x + u) + h))
          + (A.map (fun u => (x + q) + u)
            + A.map (fun u => ((x + q) + u) + h)))) := by
    rw [pairSums_cons, pairSums_cons, pairSums_cons, pairSums_cons]
    simp only [Multiset.map_cons]
    rw [e1, e2, e3, e4, e5, e6, m1, m2]
    ext t
    simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_map,
      Multiset.insert_eq_cons, Multiset.count_singleton]
    ring
  have hextra : Balanced h ((({x + x, (x + x) + h} : Multiset R)
      + ({(x + x) + q, ((x + x) + q) + h} + {(x + x) + q, ((x + x) + q) + h}))
      + ((A.map (fun u => x + u) + A.map (fun u => (x + u) + h))
        + (A.map (fun u => (x + q) + u) + A.map (fun u => ((x + q) + u) + h)))) :=
    balanced_add (balanced_add (balanced_antipodal_pair hh2 _)
      (balanced_add (balanced_antipodal_pair hh2 _) (balanced_antipodal_pair hh2 _)))
      (balanced_add (balanced_map_pair hh2 A (fun u => x + u))
        (balanced_map_pair hh2 A (fun u => (x + q) + u)))
  rw [htotal]
  constructor
  · intro htot
    rw [add_comm] at htot
    exact balanced_residual hextra htot
  · intro hA
    exact balanced_add hA hextra

end Augment

/-! ## Source audit -/

#print axioms balanced_map_pair
#print axioms balanced_pairSums_coset_augment

end ArkLib.ProximityGap.WindowTwoLayer
