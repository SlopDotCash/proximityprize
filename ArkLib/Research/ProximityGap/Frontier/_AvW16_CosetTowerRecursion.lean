/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The additive tower recursion and the frequency-migration obstruction (#444)

The self-similarity attack (`_AvW15`, squaring) has a *linear* complement: the dyadic coset
decomposition `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` (`ζ` a primitive `n`-th root, `ζ ∉ μ_{n/2}`) gives, for the
Gauss period `η_b(G) = Σ_{x∈G} f_b(x)` with `f_b(x) = e_p(b x)`,

> `η_b(μ_n) = η_b(μ_{n/2}) + η_{ζ b}(μ_{n/2})`.

This file formalizes that exact recursion (axiom-clean), and records the precise reason it does NOT
prove the Paley bound — the **frequency-migration obstruction**.

## The recursion and the obstruction
Taking absolute values and maximizing, the triangle inequality gives only
`M(μ_n) ≤ 2·M(μ_{n/2})` (factor **2**), which iterates to the trivial `M ≤ n`. A per-level ratio
of `√2` would give `M ≈ √n` (the conjecture); the `√2`-vs-`2` gap compounded over the `μ` dyadic
levels is the open half-power gap `n^{1-o(1)}` vs `√n`.

**Scope (audit R-083/R-054 extension, 2026-10-28).**  The statements below prove only the disjoint
coset sum, a conditional abstract frequency-migration split, and the triangle factor `2`.  The
sentences in this section about the "actual recursion ≈ √2" and phase alignment are **sampled
probe observations, not proved recurrences**: no theorem here bounds the per-level ratio below `2`
or proves phase alignment at the worst frequency.  A strict universal `√2` per-level descent is
not established, and later probe work in this cone (e.g. `_DoorIVWorstBPerLevelGrowthFloor.lean`
reports per-level ratios `1.75, 1.57, 1.47` above `√2`) argues against it.

The improvement from `2` toward `√2` would follow if, at the worst frequency `b*` for `μ_n`, the two
half-periods `η_{b*}(μ_{n/2})` and `η_{ζ b*}(μ_{n/2})` were not *both* near-maximal. In the probes
they do not look independently controllable: the worst `b*` for `μ_n` was observed to **migrate**
away from the argmax of `μ_{n/2}` (an L²-vs-L∞ phenomenon), and the two half-periods were observed
to align in phase at `b*` (the cross-term `2 Re(η_{b*} \overline{η_{ζ b*}})` measured positive,
≈50% of the total — sampled, not proved). So the recursion's saving is governed by the **joint
distribution of `(η_b, η_{ζb})` over `b`** — a 2-dimensional instance of the same Gauss-period
problem; the single-level recursion does not close without control of that joint object.

## Results (axiom-clean)
* `sum_coset_tower` — `Σ_{x∈H ⊔ gH} f x = Σ_{x∈H} f x + Σ_{x∈H} f (g·x)` (disjoint coset split).
* `period_tower_recursion` — the period form: with `f_b` the period summand, the period over the
  doubled subgroup splits as the period over `H` at `b` plus the period over `H` at the migrated
  frequency. (Stated abstractly via the summand `e_b`.)
* `sup_le_two_mul_sup` — the triangle consequence `M(μ_n) ≤ 2·M(μ_{n/2})` (factor 2, the lossy bound
  whose per-level `√2` slack is the half-power gap).

NOT prize closure — it pins the recursion and localizes the obstruction to the joint two-frequency
distribution.
-/

namespace ArkLib.ProximityGap.Frontier.AvW16

open Finset

/-- **Disjoint coset-tower sum (proven).** If `s = H ∪ (H.image (g • ·))` is a disjoint union and
`(g • ·)` is injective on `H`, then `Σ_{x∈s} f x = Σ_{x∈H} f x + Σ_{x∈H} f (g • x)`. The instance is
`μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}`. -/
theorem sum_coset_tower {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (H : Finset α) (g : α → α) (f : α → M)
    (hinj : ∀ x ∈ H, ∀ y ∈ H, g x = g y → x = y)
    (hdisj : Disjoint H (H.image g)) :
    ∑ x ∈ (H ∪ H.image g), f x = ∑ x ∈ H, f x + ∑ x ∈ H, f (g x) := by
  rw [Finset.sum_union hdisj, Finset.sum_image hinj]

/-- **Period tower recursion (proven, abstract).** For a period-like summand `e : β → α → M`
(think `e b x = e_p(b·x)`) and the doubled subgroup `μ_n = H ∪ ζ·H`, the period at frequency `b`
splits as the period over `H` at `b` plus the period over `H` evaluated through the coset shift —
which, when `e b (ζ·x) = e (ζ•b) x` (period homogeneity), is the period at the **migrated**
frequency `ζ•b`. Stated with the migration as the hypothesis `hmig`. -/
theorem period_tower_recursion {α β M : Type*} [AddCommMonoid M] [DecidableEq α]
    (H : Finset α) (ζ : α → α) (e : β → α → M) (b : β) (mig : β → β)
    (hinj : ∀ x ∈ H, ∀ y ∈ H, ζ x = ζ y → x = y)
    (hdisj : Disjoint H (H.image ζ))
    (hmig : ∀ x ∈ H, e b (ζ x) = e (mig b) x) :
    ∑ x ∈ (H ∪ H.image ζ), e b x = ∑ x ∈ H, e b x + ∑ x ∈ H, e (mig b) x := by
  rw [sum_coset_tower H ζ (e b) hinj hdisj]
  congr 1
  exact Finset.sum_congr rfl hmig

/-- **The lossy triangle consequence (proven).** If `‖η_b(μ_n)‖ = ‖η_b(μ_{n/2}) + η_{ζb}(μ_{n/2})‖`
and both half-period norms are `≤ Mhalf`, then `‖η_b(μ_n)‖ ≤ 2·Mhalf`. This is the factor-2 bound;
its per-level slack relative to a hypothetical `√2` recursion (not proved) compounds to the open
half-power gap. -/
theorem sup_le_two_mul_sup {M : Type*} [NormedAddCommGroup M]
    (etaFull etaLo etaHi : M) (Mhalf : ℝ)
    (hsplit : etaFull = etaLo + etaHi) (hlo : ‖etaLo‖ ≤ Mhalf) (hhi : ‖etaHi‖ ≤ Mhalf) :
    ‖etaFull‖ ≤ 2 * Mhalf := by
  rw [hsplit]
  calc ‖etaLo + etaHi‖ ≤ ‖etaLo‖ + ‖etaHi‖ := norm_add_le _ _
    _ ≤ Mhalf + Mhalf := add_le_add hlo hhi
    _ = 2 * Mhalf := by ring

end ArkLib.ProximityGap.Frontier.AvW16

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW16.sum_coset_tower
#print axioms ArkLib.ProximityGap.Frontier.AvW16.period_tower_recursion
#print axioms ArkLib.ProximityGap.Frontier.AvW16.sup_le_two_mul_sup
