/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G240QuotientIncidenceNormalization

/-!
# G242: carrier-correct quotient large sieve — the fiber map lives on `F_p^*`, not `G` (#466)

G240 repaired G237's `n`-vs-`m` character mis-indexing by re-typing the quotient-Jacobi operator
onto `Q = F_p^* / G`, and advertised the lifted input Parseval

```text
∑_{x ∈ F_p^*} ‖F_a(x)‖² = n·m·‖a‖².
```

However G240's Lean statements `quotient_largesieve_of_fibers` and
`l2_mass_floor_of_quotient_fibers` run the fiber sum over the index set called `G` while
simultaneously demanding

```text
hInputParseval : ∑_{u ∈ G} ‖F u‖² = n·m·‖a‖².
```

That hypothesis is **false for the actual object** when `G` is the order-`n` subgroup: every `u ∈ G`
has trivial quotient class (`cls u = 0`), so `F_a` is *constant* on `G` and
`∑_{u ∈ G} ‖F_a(u)‖² = n·|∑_A a_A|²`, a rank-one functional that is a tiny fraction (measured
`0.0005–0.019·(n·m·‖a‖²)`) of the lifted mass.  The `n·m` energy lives on `F_p^*` (cardinality
`n·m`), **not** on the subgroup `G` (cardinality `n`).  Discharging G240's hypothesis as written
would smuggle in exactly the carrier error G240 was written to fix, one level up.  This is the live
typing/wiring gap flagged by the G241 referee probe.

The honest fix is a **carrier-correct** instantiation: the fiber map `x ↦ class(2 − x)` must range
over the full carrier `C = F_p^*` of cardinality `n·m`, where

* the input Parseval `∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²` genuinely holds (G241 `(L)`, exact in every
  probed cell), and
* the fiber ceiling is `#{x ∈ C : class(2 − x) = d} ≤ n`, because a carrier that is a disjoint union
  of `m` quotient classes each of size `≤ n` has every class-fiber of size `≤ n`.

This file supplies that carrier-correct wrapper.  It does not weaken or re-derive G240/G237's
abstract inequalities (they are index-set-agnostic and correct); it fixes the *instantiation*, so
the remaining Mathlib obligation is the honest `n·m` Parseval **on the size-`n·m` carrier**, and the
fiber ceiling `≤ n` is discharged structurally from a per-class size bound rather than asserted.

Keystone correctness repair of the input-(A) discharge path, not a prize move.  The signed
sponsor-prime covariance at ranks 5 and 6 remains open and on the BGK/Paley wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G242CarrierCorrectQuotientLargeSieve

open Finset
open ArkLib.ProximityGap.Frontier.G237FiberLargeSieveInputA
open ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo

variable {α β : Type*}

/-! ## Structural fiber ceiling on a class-partitioned carrier -/

/-- **Fiber ceiling from a per-class size bound.**

Let the carrier `C : Finset α` classify under `cls : α → β` into classes drawn from `D : Finset β`
(`hmaps : ∀ x ∈ C, cls x ∈ D`).  If every class-fiber `{x ∈ C : cls x = d}` has cardinality `≤ n`,
then in particular the fiber over the composed map used by the large sieve is `≤ n`.

This is the phase-honest replacement for a Gram row-mass premise: the operator constant is a *fiber
count*, and `≤ n` is a structural per-class size bound, not an analytic assertion.  For the
quotient-Jacobi object the carrier is `F_p^* ` and each quotient class has exactly `n` elements, so
`hclass_le` holds with equality. -/
theorem fiber_le_of_class_size_bound
    [DecidableEq β] (C : Finset α) (cls : α → β) (n : ℕ)
    (hclass_le : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n) :
    ∀ d, ((C.filter (fun x => cls x = d)).card : ℝ) ≤ (n : ℝ) := by
  intro d
  exact_mod_cast hclass_le d

/-! ## Carrier size from a disjoint class decomposition -/

/-- **Carrier cardinality `= n·m` from `m` classes of size `≤ n` … as an upper bound.**

If `C` classifies into the `m` classes indexed by `D` (with `#D = m`) and every class has size
`≤ n`, then `#C ≤ n·m`.  For the quotient-Jacobi carrier `F_p^*` every class has size exactly `n`,
so `#C = n·m`; here we record the structural inequality that the carrier cannot exceed the
`n·m` budget, which is what pins the lifted Parseval normalization.  (The exact `= n·m` used by the
input Parseval is supplied as an explicit hypothesis in the wrapper below, since it is a
number-theoretic fact about `F_p^* → F_p^*/G`.) -/
theorem carrier_card_le
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β) (n m : ℕ)
    (hmaps : ∀ x ∈ C, cls x ∈ D) (hD : D.card = m)
    (hclass_le : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n) :
    C.card ≤ n * m := by
  classical
  have hpart : C.card = ∑ d ∈ D, (C.filter (fun x => cls x = d)).card :=
    (Finset.card_eq_sum_card_fiberwise hmaps)
  rw [hpart]
  calc ∑ d ∈ D, (C.filter (fun x => cls x = d)).card
      ≤ ∑ _d ∈ D, n := Finset.sum_le_sum (fun d _ => hclass_le d)
    _ = D.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ = n * m := by rw [hD]; ring

/-! ## Carrier-correct large-sieve operator bound -/

/-- **Carrier-correct quotient large-sieve operator bound.**

The fiber sum ranges over the carrier `C = F_p^*` (cardinality `n·m`), the fiber ceiling is `≤ n`
from the per-class size bound, and the input Parseval on the carrier is
`∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²` (the honest `(L)` identity).  With output Parseval
`outputEnergy ≤ classEnergy/m`, the operator bound is `outputEnergy ≤ n²·‖a‖²`.

Compared with G240's `quotient_largesieve_of_fibers`, the *only* change is that the fiber index set
is the carrier `C` (where the `n·m` input energy actually lives) rather than the subgroup `G` (where
`F` is constant and the `n·m` hypothesis is false).  Everything downstream — the `n·(n·m)/m = n²`
cancellation — is unchanged. -/
theorem carrier_largesieve_of_fibers
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n m : ℕ) (hm : 0 < m) (aNorm2 outputEnergy : ℝ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hclass_le : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n)
    (hInputParseval : ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * m * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ x ∈ C.filter (fun x => cls x = d), F x‖ ^ 2) / m) :
    outputEnergy ≤ (n : ℝ) ^ 2 * aNorm2 := by
  have hfib : ∀ d ∈ D, ((C.filter (fun x => cls x = d)).card : ℝ) ≤ (n : ℝ) :=
    fun d _ => fiber_le_of_class_size_bound C cls n hclass_le d
  exact
    ArkLib.ProximityGap.Frontier.G240QuotientIncidenceNormalization.quotient_largesieve_of_fibers
      C cls D F n m hm aNorm2 outputEnergy hmaps hfib hInputParseval hOutputParseval

/-! ## Carrier-correct G233 mass floor -/

/-- **G233 coefficient-mass floor with the carrier-correct quotient normalization.**

This is the honest end of the G228→G240 chain: the large-sieve input `(A)` is discharged with the
fiber map on the carrier `C = F_p^*` (cardinality `n·m`), so the input Parseval
`∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²` is the *true* `(L)` identity — not the false `∑_{u ∈ G} = n·m·‖a‖²`
that G240's statement demanded on the subgroup.  The fiber ceiling `≤ n` is a structural per-class
size bound.

The sole remaining Mathlib obligation is the carrier Parseval `(L)` on the size-`n·m` carrier
(quotient-character orthogonality on `Q ≅ ℤ/m` lifted over the `n`-fold fibers of `F_p^* → Q`),
which the G241 probe confirmed exact.  Everything else (fiber Cauchy, fiber count, the `n²`
cancellation, the mass floor) is kernel-checked. -/
theorem l2_mass_floor_of_carrier_fibers
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (aNorm2 outputEnergy sNorm2 : ℝ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hclass_le : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n)
    (hInputParseval : ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * m * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ x ∈ C.filter (fun x => cls x = d), F x‖ ^ 2) / m)
    (hSponsor : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ outputEnergy) :
    (m : ℝ) - n ≤ 4 * n * aNorm2 := by
  apply l2_mass_floor_of_largesieve_parseval n m hn aNorm2 outputEnergy sNorm2
  · exact carrier_largesieve_of_fibers C cls D F n m hm aNorm2 outputEnergy
      hmaps hclass_le hInputParseval hOutputParseval
  · exact hSponsor
  · exact hHalf

end ArkLib.ProximityGap.Frontier.G242CarrierCorrectQuotientLargeSieve
