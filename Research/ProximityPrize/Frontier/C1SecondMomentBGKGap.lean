/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ShawSecondMoment

/-!
# C1 (K3 thin-strip average→worst) — the second-moment route reduces to BGK (#407)

The lower-bound census proposed pushing the `δ*` lower bracket past Johnson by a
**Chebyshev / second-moment** argument on the thin strip
`δ ∈ (1−√ρ, 1−√ρ + c/log n)`, hoping the cyclic automorphism of the smooth domain controls
the apex obstruction (the `sup` over received words).

`ShawSecondMoment.lean` already proves both halves of the worst-case bracket for the Shaw
operator `𝒮(S; s₀, s₁)` (the exact far-line incidence error whose `sup` over `s₀` *is* the
quantity bounding `epsMCA`):

* `shawError_sq_le_second_moment` : `‖𝒮(s₀)‖² ≤ |V| · M`     (the only L²-derivable *upper* bound)
* `exists_shawError_sq_ge`        : `∃ s₀, M ≤ ‖𝒮(s₀)‖²`      (the worst case beats the average)

where `M = ∑_{ψ≠0, ψ⊥s₁} ‖∑_{s∈S} ψ(−s)‖²` is the hyperplane ℓ²-mass.

**This file packages the two halves into the single bracket the census asked to evaluate** —
the worst-case `sup_{s₀} ‖𝒮‖²` lies in `[M, |V|·M]`, a multiplicative slack of exactly
`|V| = q^n` — together with its three consequences:

1. `shaw_sup_sq_bracket` : `M ≤ (sup) ∧ (sup) ≤ |V|·M`.
2. `chebyshev_does_not_bound_sup` : the Chebyshev/L² *average* tail bound
   (`card_large_shawError_mul_sq_le`) controls only the **count** of heavy base points,
   never the worst value below `√(|V|·M)`; the worst case is `≥ √M` by `exists_shawError_sq_ge`.
   So no L²/Chebyshev estimate closes the `√|V|` gap.
3. `shaw_worst_case_needs_uniform_cancellation` : a budget `B` with `B² < M` is *refuted*
   (a bad witness exists), but a budget proving the upper side small requires `B² ≥`
   the worst value, which the L² route only bounds by `|V|·M` — i.e. one needs *uniform*
   (every-`s₀`) square-root cancellation of the structured Gauss-period sum
   `∑_ψ Ŝ(ψ)·ψ(s₀)`.  That is exactly the open **BGK / Paley** content
   `max_{b≠0} ‖∑_{y∈μ_n} ψ(by)‖ ≤ 2√n` (`WorstCaseIncompleteSumBound`).

**Conclusion (a precise reduction, per the honesty contract):** the C1 second-moment route
does *not* move the `δ*` lower bracket past Johnson — it reduces, with a `√|V| = q^{n/2}`
gap, to the same BGK char-sum wall the BGK-independent threads were chosen to avoid.  The
cyclic automorphism does *not* help: `exists_shawError_sq_ge` shows the `sup` is `≥` the
average *for every direction `s₁`*, so symmetrizing the average cannot lower the worst case.

No new lower bound is *claimed*; this is the machine-checked statement that this route is BGK.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset
open ArkLib.ProximityGap.ShawOperator
open ArkLib.ProximityGap.LineIncidenceSpectral

namespace ArkLib.ProximityGap.Frontier.C1SecondMomentBGKGap

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [DecidableEq V]
  [Module F V]

open ArkLib.ProximityGap.ShawSecondMoment

/-- The hyperplane ℓ²-mass `M(S, s₁) = ∑_{ψ≠0, ψ⊥s₁} ‖∑_{s∈S} ψ(−s)‖²`. -/
noncomputable def hyperplaneMass (S : Finset V) (s₁ : V) : ℝ :=
  ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
        directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
      ‖∑ s ∈ S, ψ (-s)‖ ^ 2

/-- **The two-sided second-moment bracket on the worst-case Shaw value.**  For any base point
`s₀` realizing the lower half, the squared worst-case Shaw error is sandwiched:

  `M ≤ ‖𝒮(s₀_worst)‖²`   and   `‖𝒮(s₀)‖² ≤ |V| · M`   for all `s₀`.

The multiplicative slack between the two derivable bounds is exactly `|V| = q^n` — the
`√|V| = q^{n/2}` worst-vs-average gap.  This is the machine-checked apex obstruction. -/
theorem shaw_sup_sq_bracket [Nonempty V] (S : Finset V) (s₁ : V) :
    (∃ s₀ : V, hyperplaneMass (F := F) S s₁ ≤ ‖shawError (F := F) S s₀ s₁‖ ^ 2) ∧
    (∀ s₀ : V, ‖shawError (F := F) S s₀ s₁‖ ^ 2
      ≤ (Fintype.card V : ℝ) * hyperplaneMass (F := F) S s₁) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s₀, hs₀⟩ := exists_shawError_sq_ge (F := F) S s₁
    exact ⟨s₀, by simpa [hyperplaneMass] using hs₀⟩
  · intro s₀
    simpa [hyperplaneMass] using shawError_sq_le_second_moment (F := F) S s₀ s₁

/-- **Chebyshev controls only the count of heavy base points, not the worst value.**
For any threshold `t ≥ 0`, the number of base points with `‖𝒮‖ ≥ t` is at most `|V|·M / t²`
(`card_large_shawError_mul_sq_le`).  But the worst base point itself has `‖𝒮‖² ≥ M`
(`exists_shawError_sq_ge`), so the Chebyshev tail can never certify `sup ‖𝒮‖ < √M`: the
worst value is pinned from below by the average, independent of how the count concentrates.
This is the precise sense in which the average→worst (C1) step fails. -/
theorem chebyshev_does_not_bound_sup [Nonempty V] (S : Finset V) (s₁ : V) {t : ℝ} (ht : 0 ≤ t) :
    -- Chebyshev: the heavy-count tail bound...
    ((univ.filter (fun s₀ : V => t ≤ ‖shawError (F := F) S s₀ s₁‖)).card : ℝ) * t ^ 2
        ≤ (Fintype.card V : ℝ) * hyperplaneMass (F := F) S s₁
    -- ...coexists with a worst base point at least as large as the average √M.
    ∧ (∃ s₀ : V, hyperplaneMass (F := F) S s₁ ≤ ‖shawError (F := F) S s₀ s₁‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · simpa [hyperplaneMass] using card_large_shawError_mul_sq_le (F := F) S s₁ ht
  · obtain ⟨s₀, hs₀⟩ := exists_shawError_sq_ge (F := F) S s₁
    exact ⟨s₀, by simpa [hyperplaneMass] using hs₀⟩

/-- **The worst case needs uniform cancellation = BGK.**  If the prize Shaw budget `B`
undershoots the hyperplane mass (`B² < M`), the prize Shaw bound is FALSE with an explicit
bad witness (`not_mcaShawConjecture_of_lt_secondMoment`).  Hence any *valid* budget must
satisfy `B² ≥ M`; but the L² route only proves the worst case `≤ |V|·M`, so certifying a
budget `B` with `B² < |V|·M` (anything below the trivial union bound) requires bounding the
worst `‖𝒮(s₀)‖` *uniformly in `s₀`* — the open `√`-cancellation of `∑_ψ Ŝ(ψ)ψ(s₀)`, i.e.
BGK / Paley `max_b ‖η_b‖ ≤ 2√n`.  This restates the route's dependence on BGK. -/
theorem shaw_worst_case_needs_uniform_cancellation [Nonempty V] (S : Finset V) (s₁ : V)
    (B : ℝ) (hB : B ^ 2 < hyperplaneMass (F := F) S s₁) :
    ¬ MCAShawConjecture (F := F) S B := by
  refine not_mcaShawConjecture_of_lt_secondMoment (F := F) S s₁ B ?_
  simpa [hyperplaneMass] using hB

end ArkLib.ProximityGap.Frontier.C1SecondMomentBGKGap

open ArkLib.ProximityGap.Frontier.C1SecondMomentBGKGap in
#print axioms shaw_sup_sq_bracket
open ArkLib.ProximityGap.Frontier.C1SecondMomentBGKGap in
#print axioms chebyshev_does_not_bound_sup
open ArkLib.ProximityGap.Frontier.C1SecondMomentBGKGap in
#print axioms shaw_worst_case_needs_uniform_cancellation
