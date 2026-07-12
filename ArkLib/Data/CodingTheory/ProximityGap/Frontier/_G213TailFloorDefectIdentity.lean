/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G210TailFloorEqualityRigidity

/-!
# G213: exact defect identity for the dyadic depth-two tail floor (#466)

G209 proves the sharp pure-`ℕ` floor for a positive multiplicity partition
`ks` of `n - 1`, with `n = 2*m` and `ks.card ≤ m`:

```text
Σ k² ≥ 4*m - 3 = 2*n - 3.
```

G210 identifies the zero-defect equality case: the cap is saturated and every part is `1` or `2`,
forcing the unique histogram `{1,2,...,2}`.

This file records the exact arithmetic invariant between those two results.  For any positive
partition `ks` of `2*m - 1`, the floor excess decomposes as

```text
Σ k² - (4*m - 3)
  = Σ_k (k - 1)(k - 2)       +       2*(m - #ks).
      local collision defect         unused dyadic class slots
```

under the class-count cap `#ks ≤ m`.  Thus every failure of the depth-two flat floor has only two
sources:

* a class of multiplicity at least `3` (local collision/amalgamation defect); or
* unsaturated use of the dyadic `d ↦ n-d` class cap.

This is thinness-essential bookkeeping: the `m` available slots are exactly the dyadic half-set
from G206, and the floor is the G209/G210 dyadic depth-two floor.  It does not bound the signed
`r = 5, 6` covariance and does not close the prize; it only makes the excess above the floor a
canonical nonnegative budget instead of an opaque `Σk²` surplus.

The concrete large-prime G210 exception shape `[4,3,2,...,2]` at `n=32` has excess
`73 - 61 = 12`, decomposing as `8` local defect plus `4` unused-slot defect.  This matches the
exact probe witnesses `n=32, p∈{50177,51137,65537}` without importing any field-specific data.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G213

open Multiset
open ArkLib.ProximityGap.Frontier.G210

/-- Integer square of a natural multiplicity.  Keeping this named avoids parser ambiguity around
casts inside `Multiset.map`. -/
def sqZ (k : ℕ) : ℤ := (k : ℤ) ^ 2

/-- Local excess of a positive part over the G209 pointwise engine.  For `k ≥ 1`, this is
nonnegative and vanishes exactly at the floor-compatible parts `k = 1, 2`. -/
def localDefect (k : ℕ) : ℤ := ((k : ℤ) - 1) * ((k : ℤ) - 2)

/-- Sum of local defects expands to the difference between `Σk² + 2*#ks` and `3*Σk`.
This is the algebra behind the G209 pointwise engine `3k ≤ k²+2`. -/
theorem sum_localDefect_eq (ks : Multiset ℕ) :
    (ks.map localDefect).sum =
      (ks.map sqZ).sum - 3 * (ks.sum : ℤ) + 2 * (ks.card : ℤ) := by
  induction ks using Multiset.induction with
  | empty => simp [localDefect, sqZ]
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      rw [ih]
      simp [localDefect, sqZ]
      ring

/-- **Exact tail-floor defect identity.**
For a partition of `2*m - 1`, the excess over the G209 floor `4*m - 3` is exactly the sum of the
local multiplicity defects `(k-1)(k-2)` plus two units for every unused dyadic class slot. -/
theorem tail_floor_defect_identity
    (m : ℕ) (ks : Multiset ℕ) (hm : 1 ≤ m) (hsum : ks.sum = 2 * m - 1) :
    ((ks.map sqZ).sum - (4 * (m : ℤ) - 3)) =
      (ks.map localDefect).sum + 2 * ((m : ℤ) - (ks.card : ℤ)) := by
  have hdef := sum_localDefect_eq ks
  have hsumz0 : (ks.sum : ℤ) = (2 * m - 1 : ℕ) := by exact_mod_cast hsum
  have hsumz : (ks.sum : ℤ) = 2 * (m : ℤ) - 1 := by omega
  rw [hdef]
  omega

/-- A positive multiplicity part has nonnegative local defect. -/
theorem localDefect_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ localDefect k := by
  unfold localDefect
  by_cases h1 : k = 1
  · subst k
    norm_num
  · have hk2 : 2 ≤ k := by omega
    have hA : (0 : ℤ) ≤ (k : ℤ) - 1 := by omega
    have hB : (0 : ℤ) ≤ (k : ℤ) - 2 := by omega
    exact mul_nonneg hA hB

/-- Under positivity and the dyadic class-count cap, the G209 floor excess is nonnegative by the
exact two-term decomposition, rather than only by an inequality chain. -/
theorem tail_floor_excess_nonneg
    (m : ℕ) (ks : Multiset ℕ)
    (hm : 1 ≤ m)
    (hpos : ∀ k ∈ ks, 1 ≤ k)
    (hsum : ks.sum = 2 * m - 1)
    (hcard : ks.card ≤ m) :
    (0 : ℤ) ≤ ((ks.map sqZ).sum - (4 * (m : ℤ) - 3)) := by
  rw [tail_floor_defect_identity m ks hm hsum]
  have hlocal : (0 : ℤ) ≤ (ks.map localDefect).sum := by
    refine Multiset.sum_nonneg ?_
    intro x hx
    simp only [Multiset.mem_map] at hx
    rcases hx with ⟨k, hk, rfl⟩
    exact localDefect_nonneg (hpos k hk)
  have hunused : (0 : ℤ) ≤ 2 * ((m : ℤ) - (ks.card : ℤ)) := by omega
  omega

/-- The G210 large-exception histogram `[4,3,2,...,2]` at `n=32` has total floor excess
`73 - 61 = 12`, decomposed as `8` local multiplicity defect plus `4` unused dyadic slots. -/
theorem g210_n32_exception_defect :
    let ks : Multiset ℕ := {4, 3} + Multiset.replicate 12 2
    ((ks.map sqZ).sum - 61 = 12) ∧
      (ks.map localDefect).sum = 8 ∧ 2 * ((16 : ℤ) - (ks.card : ℤ)) = 4 := by
  norm_num [localDefect, sqZ]

#print axioms sum_localDefect_eq
#print axioms tail_floor_defect_identity
#print axioms localDefect_nonneg
#print axioms tail_floor_excess_nonneg
#print axioms g210_n32_exception_defect

end ArkLib.ProximityGap.Frontier.G213
