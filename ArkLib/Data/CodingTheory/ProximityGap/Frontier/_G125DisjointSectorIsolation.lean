/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G124MomentLPDepthConstraints

/-!
# G125: disjoint-sector isolation — the energy recursion with kernel constants

The near-diagonal rows of the G124 moment LP give per-fiber bounds that are sharp exactly
where the G97 shallow-oriented envelope is lossy.  Specializing row `m = r − s` and dropping
the other (nonnegative) terms:

```text
(r−s)! · depthFiber A r s ≤ (r)_{r−s}² · #A^{r−s} · E_s(A)      (every s ≤ r)
```

— e.g. `fiber_{r−1} ≤ r² · #A · E_{r−1}` (one shared value, `r²` positions), the natural
sharp count, now a theorem.  Summing over all depths below `r` isolates the fully-disjoint
sector from the whole energy:

```text
E_r(A) ≤ depthFiber A r r + Σ_{s<r} (r)_{r−s}² · #A^{r−s} · E_s(A).
```

**Every part of the `2r`-th-moment object except the fully-disjoint sector is bounded,
unconditionally, by lower-rung energies with explicit kernel constants.**  Combined with
G96's weld, `DCEnergyBound` at any prime reduces (up to these explicit descent terms) to
bounding the fully-disjoint equal-sum census `depthFiber A r r` — the formal counterpart of
"the wall is disjoint-support cancellation".

**Honest scope.**  The recursion constants are crude (`(r)_{r−s}²` without the `(r−s)!`
saving in the summed form); the disjoint sector itself is untouched (the wall).  CORE remains
OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints

variable {α : Type*} [DecidableEq α] [AddCancelCommMonoid α]

/-- **Near-diagonal fiber bound.**  Row `m = r − s` of the moment LP, restricted to its
diagonal term: the depth-`s` fiber pays `(r−s)!` against the rung-`s` energy. -/
theorem factorial_mul_depthFiber_le (A : Finset α) {r s : ℕ} (hs : s ≤ r) :
    (r - s).factorial * depthFiber A r s
      ≤ (r.descFactorial (r - s)) ^ 2 * (A.card ^ (r - s) * Finset.addREnergy s A) := by
  have hrow := moment_LP_row A (m := r - s) (Nat.sub_le r s)
  have hterm : (r - s).factorial * depthFiber A r s
      ≤ ∑ t ∈ Finset.range (r + 1),
          (r - t).descFactorial (r - s) * depthFiber A r t := by
    have hmem : s ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hs)
    have hsingle := Finset.single_le_sum
      (f := fun t => (r - t).descFactorial (r - s) * depthFiber A r t)
      (fun t _ => Nat.zero_le _) hmem
    calc
      (r - s).factorial * depthFiber A r s
          = (r - s).descFactorial (r - s) * depthFiber A r s := by
        rw [Nat.descFactorial_self]
      _ ≤ ∑ t ∈ Finset.range (r + 1),
            (r - t).descFactorial (r - s) * depthFiber A r t := hsingle
  have hsub : r - (r - s) = s := Nat.sub_sub_self hs
  calc
    (r - s).factorial * depthFiber A r s
        ≤ ∑ t ∈ Finset.range (r + 1),
            (r - t).descFactorial (r - s) * depthFiber A r t := hterm
    _ ≤ (r.descFactorial (r - s)) ^ 2 *
          (A.card ^ (r - s) * Finset.addREnergy (r - (r - s)) A) := hrow
    _ = (r.descFactorial (r - s)) ^ 2 *
          (A.card ^ (r - s) * Finset.addREnergy s A) := by rw [hsub]

/-- Fiber bound with the factorial dropped (crude form for summation). -/
theorem depthFiber_le_energy_bound (A : Finset α) {r s : ℕ} (hs : s ≤ r) :
    depthFiber A r s
      ≤ (r.descFactorial (r - s)) ^ 2 * (A.card ^ (r - s) * Finset.addREnergy s A) := by
  have h := factorial_mul_depthFiber_le A hs
  have hfac : 1 ≤ (r - s).factorial := Nat.one_le_iff_ne_zero.mpr (r - s).factorial_ne_zero
  calc
    depthFiber A r s = 1 * depthFiber A r s := (one_mul _).symm
    _ ≤ (r - s).factorial * depthFiber A r s := Nat.mul_le_mul_right _ hfac
    _ ≤ _ := h

/-- **Disjoint-sector isolation.**  The whole `2r`-th-moment object is the fully-disjoint
census plus terms bounded by lower-rung energies with explicit kernel constants. -/
theorem addREnergy_le_disjoint_add_descent (A : Finset α) (r : ℕ) :
    Finset.addREnergy r A
      ≤ depthFiber A r r
        + ∑ s ∈ Finset.range r,
            (r.descFactorial (r - s)) ^ 2 * (A.card ^ (r - s) * Finset.addREnergy s A) := by
  have hdecomp := addREnergy_eq_sum_depthFiber A r
  have hsplit : ∑ s ∈ Finset.range (r + 1), depthFiber A r s
      = (∑ s ∈ Finset.range r, depthFiber A r s) + depthFiber A r r := by
    rw [Finset.sum_range_succ]
  rw [hdecomp, hsplit, add_comm]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum (fun s hsmem =>
    depthFiber_le_energy_bound A (le_of_lt (Finset.mem_range.mp hsmem)))

end ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation.factorial_mul_depthFiber_le
#print axioms
  ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation.depthFiber_le_energy_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G125DisjointSectorIsolation.addREnergy_le_disjoint_add_descent
