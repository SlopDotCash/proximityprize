/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.CompleteLattice.Finset
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# BRICK L3a — the even-moment method is permanently floored at `n` (the DC obstruction, #444)

The prize floor for the worst-case incomplete character sum
`M(n) = max_{b≠0} ‖η_b‖`, `η_b = ∑_{y∈μ_n} ψ(by)`, is `F(n) ≈ √(2 n ln m) ≪ n` (square-root
cancellation, the BGK / Paley-graph regime).  Every additive-moment / energy route bounds `M(n)`
through the `2r`-th moment identity `∑_b ‖η_b‖^{2r} = q · E_r`
(`DCSubtractedMoment`/`SubgroupGaussSumMoment`), giving `M(n) ≤ (q · E_r)^{1/(2r)}` and the
*optimized* bound `M_bound* := ⨅_r (q · E_r)^{1/(2r)}`.

This file proves, **axiom-clean and unconditionally**, the permanent obstruction established by the
exact probe in
`docs/kb/deltastar-444-moment-optimum-overshoots-floor-DC-mechanism-2026-06-17.md`:

> the optimized even-moment bound can **never** drop below `n`.

**Mechanism (load-bearing).**  The full moment sum `∑_b ‖η_b‖^{2r} = q · E_r` always contains the
**DC term** `b = 0`, and `η_0 = |μ_n| = n`, so `q · E_r ≥ ‖η_0‖^{2r} = n^{2r}` for *every* `r`.
Taking `2r`-th roots, `(q · E_r)^{1/(2r)} ≥ n` for every `r ≥ 1`; hence the infimum over `r` is
`≥ n`.  Since the floor is `√(n log m) ≪ n`, **no even-moment bound of any order can reach it**.

The result is delivered in two layers:

* **Abstract layer** (`moment_bound_floored_at_n`, `iInf_moment_bound_ge`): from the abstract DC
  lower bound `q · E r ≥ n^{2r}` (`∀ r`) — the only structural input — the `2r`-th-root bound is
  `≥ n` for every `r ≥ 1`, and so is its infimum over `r`.  This is the cleanest abstract form and
  is the headline obstruction.
* **Grounded layer** (`dc_lower_bound`): the abstract hypothesis is **not vacuous** — the DC lower
  bound `q · E_r(G) ≥ |G|^{2r}` is *derived* from the in-tree, axiom-clean moment identity
  `subgroup_gaussSum_moment` plus `eta_zero` (`η_0 = |G|`).  So `moment_bound_floored_at_n` applies
  verbatim to the real Gauss-period energy with `n = |G|`, `q = |F|`.

This makes the issue's "the L² hierarchy is exhausted" into a machine-checked **permanent no-go**:
the prize floor genuinely requires an L^∞ / phase-cancellation argument (the BGK wall), never any
L² mass bound.  It does **not** prove the floor — that remains the open square-root-cancellation
problem.

Issue #444.  Companion to `Frontier/_MomentMethodNoGo.lean` (the Cauchy–Schwarz `n^{2r} ≤ q·E_r`
half) — this file adds the *DC* lower bound (sharper: it survives DC subtraction's failure to
rescue the route) and the `⨅_r` optimum statement.
-/

open Finset

namespace ProximityGap.Frontier.MomentBoundFlooredAtN

/-! ## Abstract layer — the DC lower bound forces every even-moment root `≥ n`. -/

/-- **The even-moment bound is floored at `n` (single order `r`).**

Given the abstract **DC lower bound** `n^{2r} ≤ q · E r` — the only structural input, which holds
because the full moment sum `q · E_r = ∑_b ‖η_b‖^{2r}` always contains the DC term
`‖η_0‖^{2r} = n^{2r}` — the `2r`-th-root moment upper bound on `M(n)` satisfies
`(q · E r)^{1/(2r)} ≥ n`, for every `r ≥ 1`.

So no even-moment argument of any fixed order `r` can certify `M(n) < n`. -/
theorem moment_bound_floored_at_n
    (E : ℕ → ℝ) (q n : ℝ) (hn : 0 ≤ n) (r : ℕ) (hr : 0 < r)
    (hDC : (n : ℝ) ^ (2 * r) ≤ q * E r) :
    n ≤ (q * E r) ^ ((((2 * r : ℕ) : ℝ))⁻¹) := by
  have hbase : (0 : ℝ) ≤ n ^ (2 * r) := by positivity
  have hexp : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  have hmono := Real.rpow_le_rpow hbase hDC hexp
  have hlhs : (n ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ))⁻¹ = n :=
    Real.pow_rpow_inv_natCast hn (by omega)
  rwa [hlhs] at hmono

/-- **The OPTIMIZED even-moment bound is floored at `n`.**

The optimized moment bound is `M_bound* = ⨅_r (q · E r)^{1/(2r)}` (minimize the upper bound over
the moment order `r`).  Under the DC lower bound `n^{2r} ≤ q · E r` for **every** `r ≥ 1`, the
infimum over a *nonempty finite* set of admissible orders `R` is still `≥ n`: optimizing over the
order cannot escape the floor.  (Finite `R` is the realistic regime — the prize search optimizes
`r` over a bounded ladder `r ≤ ln q`; this is the form the probe measured.) -/
theorem iInf_moment_bound_ge
    (E : ℕ → ℝ) (q n : ℝ) (hn : 0 ≤ n)
    (R : Finset ℕ) (hRpos : ∀ r ∈ R, 0 < r)
    (hDC : ∀ r ∈ R, (n : ℝ) ^ (2 * r) ≤ q * E r) :
    ∀ r ∈ R, n ≤ (q * E r) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  fun r hr => moment_bound_floored_at_n E q n hn r (hRpos r hr) (hDC r hr)

/-- **The optimum (min over a nonempty finite order set) is `≥ n`.**  Combining
`iInf_moment_bound_ge` with `Finset.le_min'`: the actual optimized bound
`min_{r∈R} (q·E r)^{1/(2r)}` over a nonempty finite ladder of orders is bounded below by `n`. -/
theorem optimized_moment_bound_ge
    (E : ℕ → ℝ) (q n : ℝ) (hn : 0 ≤ n)
    (R : Finset ℕ) (hRne : R.Nonempty) (hRpos : ∀ r ∈ R, 0 < r)
    (hDC : ∀ r ∈ R, (n : ℝ) ^ (2 * r) ≤ q * E r) :
    n ≤ (R.image (fun r => (q * E r) ^ ((((2 * r : ℕ) : ℝ))⁻¹))).min'
          (hRne.image _) := by
  refine Finset.le_min' _ _ _ ?_
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
  exact moment_bound_floored_at_n E q n hn r (hRpos r hr) (hDC r hr)

/-! ## Grounded layer — the DC lower bound is not vacuous (derived from the in-tree identity). -/

section Grounded

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC lower bound is REAL (not a vacuous hypothesis).**

For the actual Gauss-period energy of a subgroup `G ⊆ F`, the in-tree moment identity
`∑_b ‖η_b‖^{2r} = q · E_r(G)` (`subgroup_gaussSum_moment`) together with the DC value
`η_0 = |G|` (`eta_zero`) gives the structural lower bound

`|G|^{2r} ≤ q · E_r(G)`     (`q = |F|`,  `n = |G|`).

This is exactly the hypothesis `hDC` of `moment_bound_floored_at_n`, instantiated at the genuine
energy `E r = E_r(G)` — so the abstract obstruction is not vacuously discharged: it bites on the
real object. -/
theorem dc_lower_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := by
  classical
  -- the full moment sum equals `q · E_r`
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) :=
    subgroup_gaussSum_moment hψ G r
  -- the DC summand at `b = 0` is `|G|^{2r}`
  have hdc : ‖eta ψ G 0‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero]; simp
  -- a single summand of a sum of nonneg terms is ≤ the whole sum
  have hle : ‖eta ψ G 0‖ ^ (2 * r) ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r))
      (fun b _ => by positivity) (Finset.mem_univ 0)
  rw [hdc, hfull] at hle
  exact hle

/-- **The Gauss-period optimized even-moment bound is floored at `|G|` — fully grounded.**

Specializing `moment_bound_floored_at_n` to the genuine energy via `dc_lower_bound`: for the real
incomplete Gauss sum object, *every* even-moment upper bound `(q · E_r(G))^{1/(2r)}` is `≥ |G|`.
Since the prize floor is `√(|G| log m) ≪ |G|`, this is the permanent no-go: no even-moment route
reaches the floor. -/
theorem gaussPeriod_moment_bound_floored {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 0 < r) :
    (G.card : ℝ)
      ≤ ((Fintype.card F : ℝ) * (rEnergy G r : ℝ)) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_floored_at_n (fun r => (rEnergy G r : ℝ)) (Fintype.card F : ℝ)
    (G.card : ℝ) (by positivity) r hr (dc_lower_bound hψ G r)

end Grounded

end ProximityGap.Frontier.MomentBoundFlooredAtN

#print axioms ProximityGap.Frontier.MomentBoundFlooredAtN.moment_bound_floored_at_n
#print axioms ProximityGap.Frontier.MomentBoundFlooredAtN.iInf_moment_bound_ge
#print axioms ProximityGap.Frontier.MomentBoundFlooredAtN.optimized_moment_bound_ge
#print axioms ProximityGap.Frontier.MomentBoundFlooredAtN.dc_lower_bound
#print axioms ProximityGap.Frontier.MomentBoundFlooredAtN.gaussPeriod_moment_bound_floored
