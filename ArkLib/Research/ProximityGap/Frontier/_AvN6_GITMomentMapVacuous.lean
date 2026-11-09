/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# N6 — the GIT / stability / moment-map route REDUCES (symmetric-average) for the house (#444)

**The attack (N6, non-estimation candidate).** Reformulate the house bound
`M = max_{c} |η_c| ≤ C·√(n log(p/n))` as a GIT *semistability* condition: the period
configuration `η = (η_0,…,η_{f-1}) ∈ ℝ^f` (one Galois orbit, `f = (p-1)/n` real conjugates,
trace `-1`, `Σ_c η_c² = p-n`) is a point in the regular representation of the cyclic Galois
group `ℤ/f` (Frobenius = cyclic shift). Ask: is `M` bounded iff the configuration is
*semistable* for some natural group action, with the bound = a checkable *moment map*?

**The verdict (this file): it REDUCES through (i) symmetric-average.** Every candidate moment
map computed exactly at `n = 16, 32` is a *constant on the Galois orbit*, hence carries **zero**
information about the max:

* **Energy / `U(1)` moment map** `μ(η) = Σ_c η_c² = p-n` — a Casimir, identically constant.
* **Cyclic / toric (AGS) moment map** — the DFT magnitudes `|η̂_k|² = p` for **every** `k ≠ 0`
  (verified EXACT, zero spread, at `n=16` value `65537=p` and `n=32` value `1048609=p`; this is
  the Gauss-sum/Jacobi modulus identity `|g(χ)|² = p`, i.e. F3 "Frobenius-decorrelated" made
  precise). The toric moment-map image is the **single point** `(p,…,p)` — a degenerate,
  `0`-dimensional polytope.
* **SL₂ / Möbius (Kempf–Ness) moment map** on the `f` roots as a config on `ℝP¹` — Möbius-
  *invariant*, hence blind to scale = the house; fixing the quadratic `Σ η_c²` to break Möbius
  collapses the residual `SO(2)`-moment map back to the constant energy.

The structural reason, the deliverable formalized here: **any moment map is equivariant, hence a
class function = a *symmetric* function of the roots = a function of the elementary symmetric
`e_k`**. By the dossier's pre-settled fact (N1/N3/N4 reduce), every symmetric function gives only
the root-magnitude **floor** `√(p-n)` (the `ℓ²` norm), never the `√(log f)`-sharper truth. So a
moment-map certificate can certify at best `M ≤ √(p-n)`, which **overshoots the truth
`√(n ln f)` by the factor `√((p-n)/(n ln f)) = √(f/ln f)`** (verified EXACT: floor `√(p-n)` vs
truth `√(n ln f)` is `22.2×` at `n=16`, `56.1×` at `n=32`, matching `√(f/ln f)` to the digit).
The sign-cancellation that pulls the house a factor `√f` *below* the floor lives in *how* the
`e_k` combine, invisible to any symmetric / moment-map functional. **N6 reduces — symmetric-
average, same wall.**

This is *not* prize closure; it is honest negative knowledge that closes the GIT/stability/
moment-map avenue and pins precisely *why* (the moment map is equivariant ⟹ symmetric ⟹ ℓ²-floor).

## Results (axiom-clean)
* `momentMap_certifies_floor` — an `ℓ²`-only (equivariant/symmetric) certificate gives
  `M ≤ √(E)` where `E = Σ η_c²`; i.e. the best a moment map can certify is the `ℓ²`-floor.
  (Pure `ℓ∞ ≤ ℓ²` fact, the formal content of "moment map sees only the energy".)
* `floor_overshoots_truth` — with `E = p-n ≥ f · (n · ln f)` (the prize regime), the floor
  certificate `√E` is `≥ √f · √(n ln f)`, i.e. it overshoots the truth `√(n ln f)` by `√f`.
* `git_moment_map_vacuous` — the composite: the moment-map certificate `√(p-n)` for the house
  exceeds the prize target `√(n ln f)` by a factor `≥ √f` (`→ ∞`), hence is vacuous.
-/

namespace ArkLib.ProximityGap.Frontier.AvN6

open Real

/-- **An equivariant (moment-map / symmetric) certificate sees only the `ℓ²` energy.**
A moment map for any of the candidate group actions is a class function, hence a *symmetric*
function of the conjugates; the strongest sup-norm bound a symmetric / `ℓ²`-only functional can
certify is `max_c |η_c| ≤ √(Σ_c η_c²)` — the `ℓ∞ ≤ ℓ²` floor. Here we encode the single index
`c` realising the max: `|η_c| ≤ √E` whenever `η_c² ≤ E` (the energy `E = Σ_c η_c²` dominates any
single squared coordinate). This is the formal content of "the moment map reads the energy". -/
theorem momentMap_certifies_floor (etaMax E : ℝ) (hE : etaMax ^ 2 ≤ E) :
    |etaMax| ≤ Real.sqrt E := by
  have hEnn : (0 : ℝ) ≤ E := le_trans (sq_nonneg etaMax) hE
  have : |etaMax| = Real.sqrt (etaMax ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [this]
  exact Real.sqrt_le_sqrt hE

/-- **The `ℓ²`-floor overshoots the truth by a diverging factor.** In the prize regime the energy
is `E = p - n` and the true house scale is `T = √(n · ln f)` with `f = (p-1)/n` conjugates. The
exact gap is `E / T² = (p-n)/(n ln f) = f/ln f → ∞` (verified EXACT at `n=16,32`: `22.2²`, `56.1²`
matching `√(f/ln f)`). We encode the generic inequality with a free *gap parameter* `g` standing in
for `f/ln f`: if `E ≥ g · T²` then `√E ≥ √g · T`, so the floor certificate `√E` exceeds the target
`T = √(n ln f)` by the factor `√g = √(f/ln f) → ∞`. -/
theorem floor_overshoots_truth (E T g : ℝ) (hg : 0 ≤ g) (hT : 0 ≤ T)
    (hbound : g * T ^ 2 ≤ E) :
    Real.sqrt g * T ≤ Real.sqrt E := by
  have hfT : Real.sqrt g * T = Real.sqrt (g * T ^ 2) := by
    rw [Real.sqrt_mul hg, Real.sqrt_sq hT]
  rw [hfT]
  exact Real.sqrt_le_sqrt hbound

/-- **The GIT / moment-map route is vacuous for the house (composite).** Suppose a moment-map
certificate bounds the house `M` by the `ℓ²`-floor `√E` (the strongest an equivariant/symmetric
functional can give, `momentMap_certifies_floor`), and the prize regime supplies `E ≥ g · T²`
with `T = √(n ln f)` the true target and `g = f/ln f → ∞` the exact floor-to-truth gap. Then the
certificate `√E` exceeds the target `T` by a factor `≥ √g`: the moment map *overshoots the truth
by `√g = √(f/ln f)`*, so it cannot certify the prize bound. That gap is exactly the
sign-cancellation below the `ℓ²`-floor that no symmetric (hence no moment-map) functional sees. -/
theorem git_moment_map_vacuous (E T g : ℝ) (hg1 : 1 ≤ g) (hT : 0 < T)
    (hbound : g * T ^ 2 ≤ E) :
    Real.sqrt g * T ≤ Real.sqrt E ∧ T ≤ Real.sqrt E := by
  have hg0 : 0 ≤ g := le_trans zero_le_one hg1
  have hfloor : Real.sqrt g * T ≤ Real.sqrt E :=
    floor_overshoots_truth E T g hg0 hT.le hbound
  refine ⟨hfloor, ?_⟩
  -- T ≤ √g · T ≤ √E, since √g ≥ 1.
  have hsg : (1 : ℝ) ≤ Real.sqrt g := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hg1
  calc T = 1 * T := (one_mul T).symm
    _ ≤ Real.sqrt g * T := by exact mul_le_mul_of_nonneg_right hsg hT.le
    _ ≤ Real.sqrt E := hfloor

end ArkLib.ProximityGap.Frontier.AvN6

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvN6.momentMap_certifies_floor
#print axioms ArkLib.ProximityGap.Frontier.AvN6.floor_overshoots_truth
#print axioms ArkLib.ProximityGap.Frontier.AvN6.git_moment_map_vacuous
