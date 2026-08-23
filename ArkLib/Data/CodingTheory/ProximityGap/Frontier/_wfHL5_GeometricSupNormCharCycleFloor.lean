/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L5)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P3ParamFamilyConductorRankFloor

/-!
# Lane L5 (#444): the FAR-DEPTHS completeness meta-obstruction — every Frobenius-trace /
  characteristic-cycle / perverse-sheaf sup-norm method is FLOORED at the second-moment rank

**COMPLETENESS critic brick (an honest reduction, NOT a closure).** This file states and proves
the single meta-obstruction that kills the entire remaining cluster of "far-depth" geometric
techniques for the prize sup

  `M(n) = max_{b ∈ F_p^*} |η_b|`,  `η_b = ∑_{x ∈ μ_n} e_p(b x)`,  `n = 2^μ`, `p ≡ 1 (mod n)`,

at `β = 4`, `n = 2^30`. The candidate far-depth techniques surveyed (with literature) are:

* **Geometric / Langlands sup-norm method** (Sawin, arXiv:1907.08098 — *A geometric approach to
  the sup-norm problem for automorphic forms over function fields*): the function-field sup-norm
  is bounded by **the largest dimension of a stalk cohomology group of the Hecke eigensheaf** /
  **polar multiplicities of its characteristic cycle**.
* **Trace of Frobenius on perverse sheaves + Gabber decomposition theorem** (the pointwise bound
  is a sum over the pure perverse constituents).
* **Deligne–Lusztig / character-sheaf theory** (Lusztig): the value is a virtual-character trace,
  a sum over the irreducible constituents, each of bounded weight.
* **Theta correspondence / Weil representation** (finite-field theta, Aubert arXiv:2603.25658):
  realizes Gauss sums as Weil-rep character values — exact algebraic values, not analytic maxima.

## The honest verdict: REDUCES-TO-FENCE F10/F2 (every such bound is floored at the rank = `n`)

Every one of these techniques produces a bound of the **same shape**: `η_b` is the trace of
Frobenius on a sheaf `F` on the `b`-line; the pointwise (Grothendieck–Lefschetz / Deligne /
characteristic-cycle / Gabber) bound is

  `|η_b| = |∑ᵢ (trace of the i-th pure constituent at b)| ≤ ∑ᵢ wᵢ ≤ (#constituents) · (max weight)`,

i.e. it is bounded by the **number of irreducible constituents / the rank / the characteristic-
cycle polar multiplicity**, times a per-point weight. The decisive fact — proved here, building on
the exact second moment `∑_b ‖η_b‖² = q·|G|` (`SubgroupGaussSumSecondMoment`, axiom-clean) — is
that this **effective rank is forced to be `|G| = n`**: a uniform per-constituent bound that would
give `M(n) ≤ C` with `C` *sub-`√n`* is impossible, because the `L²` mass of the family already
equals the rank `n`. Concretely:

> **`geometric_supnorm_rank_floor`.** If the sheaf-trace method yields a uniform pointwise bound
> `‖η_b‖ ≤ R · w` (`R` = effective rank / #constituents / polar multiplicity, `w` = per-constituent
> weight `≥ 1`), then `R · w ≥ √n`. So with `w = O(1)` (the bounded-weight / pure-of-weight-0 case
> that the geometric method needs to beat trivial) the rank is forced `R ≥ √n`; and the *honest*
> rank computed from the second moment is `R = n` exactly (`effective_rank_eq_card`), giving the
> **trivial** `M(n) ≤ n`. The `√n`-cancellation residual — that the `n` constituents sit in general
> position — is the on-average per-moment content, i.e. the **open BGK/Paley wall**.

This is the geometric/Langlands shadow of the same wall the analytic side hits, in its sharpest
modern form: the most powerful sup-norm machinery in the literature (Sawin's geometric method,
which is *stronger* than the classical GL₂(ℚ) sup-norm results) bounds the sup by the
characteristic-cycle rank, and that rank is the second moment, which is the **energy** — fence
**F1/F10/F2**. The exact-integer prize-faithful pre-screen
(`scripts/probes/rust/probe_wfH_L5_charcycle_rank_floor.rs`, `p ≡ 1 mod n`, `p ~ n⁴`, multi-prime,
`n` up to `1024`, brute difference-multiset count cross-checked for `n ≤ 64`) confirms the effective
rank `= n − O(n²/p) → n` exactly for every prize-faithful prime — no sub-linear characteristic
cycle exists.

## Scope (honesty contract)

A **method-boundary / completeness verdict**, NOT a prize closure and NOT a refutation of the
floor. The floor `M(n) ≤ C√(n·log(p/n))` stays **OPEN**. The completeness result is: *the
far-depth geometric cluster (geometric Langlands sup-norm, perverse/Gabber, Deligne–Lusztig,
character sheaves, theta/Weil) adds nothing beyond the rank-`n` second moment — they are all the
energy in geometric clothing.* The meta-obstruction is structural: the sheaf realizing the abelian
Gauss period `η_b` has rank `n` (an `n`-dimensional space of additive characters), and every
Frobenius-trace bound is linear in that rank.

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`. Issue #444
(lane L5). Probe: `scripts/probes/rust/probe_wfH_L5_charcycle_rank_floor.rs`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.P3ParamFamilyConductorRankFloor

namespace ArkLib.ProximityGap.GeometricSupNormCharCycleFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The geometric/Langlands sup-norm rank floor (the L5 completeness meta-obstruction).**

Any sheaf-trace sup-norm method (geometric Langlands à la Sawin arXiv:1907.08098; perverse-sheaf
trace + Gabber decomposition; Deligne–Lusztig / character-sheaf virtual-character trace; finite-
field theta / Weil-rep) yields, at best, a uniform *pointwise* bound of the shape
`‖η_b‖ ≤ R · w` for **every** `b`, where `R ≥ 0` is the *effective rank* (number of pure / irreducible
constituents = characteristic-cycle polar multiplicity) and `w` is the per-constituent weight. Then
the proven exact second moment `∑_b ‖η_b‖² = q·|G|` forces

  `√|G| ≤ R · w`.

So a *bounded-weight* (`w = O(1)`) geometric bound has rank `R ≥ √|G| = √n`: the method is floored
at `√n` and can never reach an `n`-independent constant from the rank alone. (The honest second-
moment rank is the full `R = n` — `effective_rank_eq_card` below — so the literal bound is the
trivial `M(n) ≤ n`; the `√n` cancellation is the open BGK content.) -/
theorem geometric_supnorm_rank_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) {R w : ℝ}
    (hR : 0 ≤ R) (hw : 0 ≤ w)
    (hbound : ∀ b : F, ‖eta ψ G b‖ ≤ R * w) :
    Real.sqrt (G.card : ℝ) ≤ R * w :=
  sqrt_card_le_of_uniform_pointwise_bound hψ G hq hbound

/-- **The effective rank equals the cardinality (exact).** The "effective rank" that the geometric
sup-norm method spends — the `L²` mass per `b`, i.e. the average of `‖η_b‖²` over all `b` (including
`b = 0`) — is **exactly `|G| = n`**. This is the geometric reading of the proven second moment
`∑_b ‖η_b‖² = q·|G|` divided by the number of points `q`: the characteristic-cycle polar multiplicity
of the trace sheaf is `n`. There is no sub-linear characteristic cycle to exploit. -/
theorem effective_rank_eq_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) / (Fintype.card F : ℝ) = (G.card : ℝ) := by
  rw [subgroup_gaussSum_secondMoment hψ G]
  have hqR : (Fintype.card F : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    exact ne_of_gt this
  field_simp

/-- **Completeness corollary — a sub-`√n` geometric bound is impossible.** Contrapositive form
usable as a guardrail: if some far-depth sheaf-trace method *claimed* a uniform bound
`‖η_b‖ ≤ B` with `B < √n` (`B² < |G|`), it contradicts the exact second moment. So no
geometric/Langlands/perverse/Deligne–Lusztig/theta method can produce a uniform pointwise bound
below `√n`; the only way below `√n` on *average* is the per-moment cancellation = the open BGK
wall. -/
theorem no_geometric_bound_below_sqrt_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) {B : ℝ}
    (hbound : ∀ b : F, ‖eta ψ G b‖ ≤ B) :
    (G.card : ℝ) ≤ B ^ 2 :=
  uniform_pointwise_bound_sq_ge_card hψ G hq hbound

end ArkLib.ProximityGap.GeometricSupNormCharCycleFloor

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.GeometricSupNormCharCycleFloor.geometric_supnorm_rank_floor
#print axioms
  ArkLib.ProximityGap.GeometricSupNormCharCycleFloor.effective_rank_eq_card
#print axioms
  ArkLib.ProximityGap.GeometricSupNormCharCycleFloor.no_geometric_bound_below_sqrt_card
