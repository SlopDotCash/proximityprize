/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The pseudocyclic defect of the cyclotomic scheme on `μ_n` sums to `−n(n−1)` (#444, lever F9)

In a **pseudocyclic** association scheme every nontrivial eigenvalue satisfies `‖η_b‖² = n`
exactly (the Ramanujan / prize value `√v`). The cyclotomic scheme on the root-of-unity subgroup
`μ_n ⊆ F_q*` is only *almost* pseudocyclic, and the open-directions census (lever **F9**,
van Dam–Muzychuk) asks to **quantify the defect** `δ_b := ‖η_b‖² − n`.

This file supplies the exact closed form for the **total defect** over the nonzero frequencies,
as a thin frontier-extension of the already-proven Parseval second-moment identity
`GaussPeriodParsevalFloor.sum_sq_erase_zero` (`∑_{b≠0} ‖η_b‖² = q·n − n²`):

> **`sum_pseudocyclic_defect`** :
>   `∑_{b≠0} (‖η_b‖² − n) = − n·(n − 1)`     (where `n = #G`).

Arithmetic: `∑_{b≠0}(‖η_b‖² − n) = (q·n − n²) − (q − 1)·n = n − n² = −n(n−1)`, using that there
are exactly `q − 1` nonzero frequencies.

## Why this is the right "defect" statement (and what it is NOT)

The total defect is **negative and `q`-independent** (`= −n(n−1)`), so the average defect is
`−n(n−1)/(q−1) < 0`: the scheme is **sub-pseudocyclic in the mean**, the periods average
*strictly below* the pseudocyclic value `n`. Consequently the pseudocyclic ideal `‖η_b‖² = n`
for all `b` is reachable **only** if every defect vanishes identically; since the total is a fixed
negative `−n(n−1) ≠ 0` for `n ≥ 2`, the scheme is **never pseudocyclic** for a proper nontrivial
subgroup. Hence the prize sup-norm bound `M(n)² ≤ C·n·log(q/n)` cannot be obtained "for free" from
an amorphic/pseudocyclic-scheme argument: the average already fails the `‖η‖² = n` equality from
below, so any positive defect at the worst frequency (the BGK wall) is *compensated* by
small/vanishing periods elsewhere, exactly the cancellation structure the wall is about.

**Scope (honesty contract, rules 1/3/6 + ASYMPTOTIC GUARD).** This is an EXACT, field-universal,
NON-MOMENT structural identity (pure Parseval bookkeeping). By rule 3 a field-universal identity
**cannot** prove the thinness-essential prize, and this one does not pretend to: it makes **no**
capacity / beyond-Johnson / growth-law claim and does not touch the cliff-at-`n/2`. Its value is
**cartography**: it formalizes the never-formalized F9 "quantify the defect" lever and pins the
defect total to a closed form, ruling out the pseudocyclic/amorphic route as a free pass to the
prize. The open wall (the worst-case *positive* defect `max_b δ_b`) is entirely untouched.

Probe (`scripts/probes/probe_pseudocyclic_parseval.py`, PROPER thin `μ_n`, `p ≫ n³`, never the full
group): the Parseval identity holds to `relerr ≤ 2·10⁻¹⁶`, the average is `< n` at every instance,
and the scheme is pseudocyclic at **none** (max-defect `> 0` always).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.GaussPeriodParsevalFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The total pseudocyclic defect over the nonzero frequencies is `−n(n−1)`.**
`∑_{b≠0} (‖η_b‖² − n) = −n·(n−1)` with `n = #G`. A thin frontier-extension of
`sum_sq_erase_zero` (`∑_{b≠0} ‖η_b‖² = q·n − n²`): subtract the constant `n` from each of the
`q − 1` nonzero-frequency terms. The result is negative and `q`-independent, so the cyclotomic
scheme on `μ_n` is sub-pseudocyclic in the mean (never pseudocyclic for `n ≥ 2`). -/
theorem sum_pseudocyclic_defect {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 1 ≤ Fintype.card F) :
    ∑ b ∈ Finset.univ.erase (0 : F), (‖eta ψ G b‖ ^ 2 - (G.card : ℝ))
      = - (G.card : ℝ) * ((G.card : ℝ) - 1) := by
  classical
  -- Split the sum of (‖η_b‖² − n) into ∑‖η_b‖² − (#nonzero)·n.
  rw [Finset.sum_sub_distrib, sum_sq_erase_zero hψ G, Finset.sum_const, nsmul_eq_mul]
  -- The erase-zero index set has exactly q − 1 elements.
  have hcard : (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [hcard]
  have hcast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    push_cast [Nat.cast_sub hq]; ring
  rw [hcast]
  ring

end ArkLib.ProximityGap.GaussPeriodParsevalFloor

#print axioms ArkLib.ProximityGap.GaussPeriodParsevalFloor.sum_pseudocyclic_defect
