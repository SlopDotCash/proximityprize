/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Bridge B05/B35 — the antipodal odd-vanishing mechanism (toward E6, #444)

The empirical EXACT FFT-graded recursion (E6) has two halves:
`#bad_{2n}(k, 2m') = #bad_n(k/2, m')` (even) and **`#bad_{2n}(k, m) = 0` for odd `m`**.

This file proves, axiom-clean, the algebraic CORE of the odd half: any weight that is
**anti-invariant** under a fixed-point-free involution sums to zero over an involution-closed
finite set. Instantiated at the antipodal involution `x ↦ −x` on `μ_{2n}` (the order-2 element
`−1 ∈ μ_{2n}`, present precisely because the subgroup has even order `2n`), an **odd-graded**
frequency weight `w` satisfies `w(−x) = −w(x)`, so its sum over `μ_{2n}` vanishes — the mechanism
that forces the odd graded obstruction count to `0`.

**Honest scope (LANDED core, named reduction).** This is the abstract vanishing core. The full E6
odd half additionally needs the `fhat` graded-frequency weight formalized so that
"odd graded ⟹ anti-invariant under `x ↦ −x`" becomes a theorem feeding `hanti`. That connection
is the explicit remaining obligation, described in the docstring — it is NOT discharged by a hidden
hypothesis inside any proof here.
-/

open Finset

namespace ArkLib.ProximityGap.Bridge05

variable {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommGroup M]

/-- **Antipodal odd-vanishing (abstract core).** If `σ` is an involution mapping the finite set `T`
into itself with no fixed points on `T`, and the weight `f` is anti-invariant
(`f (σ x) = - f x`), then `∑_{x ∈ T} f x = 0`. Pair each `x` with `σ x`: the two contributions
`f x + f (σ x) = f x + (-f x) = 0` cancel. This is exactly the mechanism behind E6's odd half. -/
theorem sum_eq_zero_of_antiInvariant
    (T : Finset ι) (σ : ι → ι)
    (hmap : ∀ x ∈ T, σ x ∈ T)
    (hinv : ∀ x ∈ T, σ (σ x) = x)
    (hnofix : ∀ x ∈ T, σ x ≠ x)
    (f : ι → M) (hanti : ∀ x ∈ T, f (σ x) = - f x) :
    ∑ x ∈ T, f x = 0 := by
  refine Finset.sum_involution (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx; rw [hanti x hx, add_neg_cancel]
  · intro x hx _; exact hnofix x hx
  · intro x hx; exact hmap x hx
  · intro x hx; exact hinv x hx

/-- **Sanity instance.** On `T = {0,1,2,3} ⊆ ZMod 4` with the antipodal involution `x ↦ x + 2`
(fixed-point-free since `2 ≠ 0` in `ZMod 4`) and the signed weight
`f x = if x = 0 ∨ x = 1 then (1 : ℤ) else -1`, the sum cancels to `0`. -/
example :
    ∑ x ∈ ({0, 1, 2, 3} : Finset (ZMod 4)),
      (if x = 0 ∨ x = 1 then (1 : ℤ) else -1) = 0 := by decide

end ArkLib.ProximityGap.Bridge05

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Bridge05.sum_eq_zero_of_antiInvariant
