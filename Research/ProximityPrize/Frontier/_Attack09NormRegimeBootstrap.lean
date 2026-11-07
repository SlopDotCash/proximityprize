/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Tactic

/-!
# Attack #09 — bootstrap the small-`n` / norm-regime BGK up the 2-adic tower (#464/#407)

The dyadic split `μ_{2^μ} = μ_{2^{μ-1}} ⊔ ω·μ_{2^{μ-1}}` gives the EXACT period recursion

> `η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}`.

This file records, axiom-clean, exactly what the recursion buys for the worst-case spectrum
`M(2^μ) = max_{b≠0}‖η_b^{(μ)}‖`, and the precise wall it hits:

* `eta_tower_recursion` — the exact split of the level-`μ` period into two level-`(μ−1)` periods
  (a thin re-export of `sum_tower_split` instantiated at `f = ψ(b·•)`).
* `eta_tower_triangle` — the ONLY unconditional consequence: `‖η_b^{(μ)}‖ ≤ ‖a‖ + ‖bω‖`.
* `M_doubling` — hence `M(2^μ) ≤ 2·M(2^{μ-1})`, i.e. the lift only gives `M ≤ n` (TRIVIAL).

**Evidence against the lift (numerics, probe_attack09; not a proof):** at the sampled worst-case
frequency `b*` the two sub-period halves `a = η_{b*}^{(μ-1)}` and `bω = η_{b*ω}^{(μ-1)}` were
observed to align in phase — the triangle inequality was tight in the sample (`ratio_to_tri = 1.000`
for μ ≤ 6 at p=257). So no `√2`-decorrelation factor per level is proved here; a sub-`2×` lift would
need a phase non-alignment statement at the maximizer.  Sampled alignment at small `p` does **not**
prove that every factor below `2` is impossible (audit R-083/R-054 extension).

The parallelogram law conserves the SECOND MOMENT (`‖η‖²+‖η̃‖²=2(‖a‖²+‖b‖²)`).  The twisted sum
`η̃ = a − b` is in general a **character-weighted** sum over `μ_{2^μ}` (weight `+1` on `H`, `−1` on
`ωH`), **not** an ordinary Gauss period at another frequency: e.g. on `μ_2 ⊂ F₅` with `b = 1` it is
`ζ₅ − ζ₅^{-1}`, which has nonzero imaginary part, while every ordinary `μ_2` period is real.  So
`η̃` is outside the original unweighted frequency family, and the identity gives no bound on `M`.

Verdict: the recursion alone yields only the trivial doubling law, landed here; the lift beyond it
needs control of the joint/weighted two-frequency object.
-/

open Finset

namespace ArkLib.ProximityGap.Attack09

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact tower recursion for the period.** If the level-`μ` subgroup `G` dyadically splits as
`G = H ⊔ ω·H` (with `H = μ_{2^{μ-1}}`, `ω` a primitive `2^μ`-th root, `ω ≠ 0`), then the period at
frequency `b` is the sum of two level-`(μ−1)` periods:
`η_b(G) = η_b(H) + η_{bω}(H)`. -/
theorem eta_tower_recursion (ψ : AddChar F ℂ) {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hsplit : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) :
    eta ψ G b = eta ψ H b + eta ψ H (b * ω) := by
  classical
  have hinj : ∀ x ∈ H, ∀ y ∈ H, ω * x = ω * y → x = y :=
    fun a _ c _ h => mul_left_cancel₀ hω h
  unfold eta
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

/-- **The only unconditional bound the recursion yields: triangle.**
`‖η_b(G)‖ ≤ ‖η_b(H)‖ + ‖η_{bω}(H)‖`. -/
theorem eta_tower_triangle (ψ : AddChar F ℂ) {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hsplit : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) (b : F) :
    ‖eta ψ G b‖ ≤ ‖eta ψ H b‖ + ‖eta ψ H (b * ω)‖ := by
  rw [eta_tower_recursion ψ hω hsplit hdisj b]
  exact norm_add_le _ _

/-- **Trivial doubling of the worst-case spectrum.** If `Mprev` bounds the level-`(μ−1)` spectrum at
BOTH relevant frequencies `b` and `bω`, the recursion only propagates `M(2^μ) ≤ 2·Mprev` — in the
probe the triangle inequality was tight at the sampled maximizer, so no sub-`2×` factor is proved
here (nor is one proved impossible). Iterated from the proven base, this gives only `M ≤ n`, far
above the prize target `√(n log m)`. -/
theorem M_doubling (ψ : AddChar F ℂ) {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hsplit : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) {Mprev : ℝ} (b : F)
    (hb : ‖eta ψ H b‖ ≤ Mprev) (hbw : ‖eta ψ H (b * ω)‖ ≤ Mprev) :
    ‖eta ψ G b‖ ≤ 2 * Mprev := by
  have := eta_tower_triangle ψ hω hsplit hdisj b
  linarith

/-- **Second-moment conservation (parallelogram).** For the period `η = a + b` and its twist
`η̃ = a − b`, `‖η‖² + ‖η̃‖² = 2(‖a‖² + ‖b‖²)`. This conserves the TOTAL second moment across the
period and its twist, but `η̃` is a character-weighted sum (not an ordinary period of the same
family) — it gives no worst-case `M` bound. -/
theorem period_parallelogram (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
  parallelogram_law_with_norm ℂ a b

end ArkLib.ProximityGap.Attack09

#print axioms ArkLib.ProximityGap.Attack09.eta_tower_recursion
#print axioms ArkLib.ProximityGap.Attack09.eta_tower_triangle
#print axioms ArkLib.ProximityGap.Attack09.M_doubling
#print axioms ArkLib.ProximityGap.Attack09.period_parallelogram
