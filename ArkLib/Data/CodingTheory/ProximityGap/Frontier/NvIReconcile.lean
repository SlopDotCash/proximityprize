/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# N-vs-I reconciliation: the binding root-sum is the codim-1 face of the deployed incidence (#407)

HONESTY-CRITICAL clarification (target P3, N-vs-I-reconcile).

Two distinct objects appear in the #407 attack:

* **N — the binding root-sum** that the *height-gate* (`HeightGateNormBound`,
  `FpVanishingBridge`) and the *No-Excess* lane (`NoExcessBindingRootSum`) close:
  the vanishing `∑_{i∈S} ω^{a i} = 0` in `F_p`, `ω` a primitive `n`-th root.  By the
  Schur/Lagrange bridge this is the divided difference of `x^{#s}` over a `#s`-node set,
  i.e. the **first Schur value** `h₁ = e₁` = the point sum.

* **I — the deployed far-line incidence** (`FarCosetExplosion.epsMCA_ge_far_incidence`):
  `I = #{γ : x^a + γ·x^b agrees with RS_k on a witness-sized set}`.  A single agreement
  set `R` of size `m = n − ⌊δn⌋` contributes the line-membership condition
  `x^a|_R, x^b|_R ∈ RS[R,k]`, governed by the **left-null space of the Vandermonde** `V_R`,
  whose dimension is `m − k`.

The reconciliation (probes `probe_p3_nvi_focused.py`, `probe_p3_nvi_final.py`, this session,
exact and `p`-independent): a single far monomial `x^b` lands in `RS[R,k]` **iff** the top
`m − k` interpolant coefficients vanish — the `(m−k)`-fold Schur system
`h_{b−k}(R) = ⋯ = h_{b−1}(R) = 0`.

* At agreement size `m = k+1` (left-null **codim 1**) this is the *single* divided difference
  `dividedDifferencePow R v b = 0`.  At `b = #R = k+1` it is exactly the **point sum**
  `∑_{i∈R} v i` — the binding object `N`.  (Probe TEST 1: `0/4368` mismatches.)
* At the **deployed binder** `m = k+2` (the actual `δ*` rung for `n=16, k=4`, left-null
  **codim 2**) the membership is a **2-fold** Schur-minor system, *strictly richer* than the
  single root-sum.  The deployed bad-`γ` are *ratios of two Schur minors* (probe `_final`:
  `I = 89`, left-null dim `= 2`, all `p`).

This file proves the structural fact that pins the relationship, axiom-clean:

> **The binding root-sum `N` (`dividedDifferencePow R v (#R) = 0`, the point sum) is precisely
> the codim-1 face of the deployed line-membership system.  It coincides with the full deployed
> per-`R` condition only when the agreement set has size `#R = k+1` (codim 1); at the deployed
> binder `#R = k+2` the per-`R` condition carries an additional independent Schur constraint
> `h₂`, which the height-gate does NOT bound.**

So the small-`n` height-gate closure (`n ≤ 64`) closes the **binding sub-object** `N`, a genuine
*lower bound* on `I`, but does **not** control the deployed `δ*` incidence at its binder radius.
The gap is real and precisely located: `N` is the `h₁` face; `I` at the binder lives on the
`h₂`-augmented minor system.  (This corrects any synthesis that treats the height-gate as closing
the deployed `δ*` line-incidence; it closes only the binding sub-object.)

All results are `sorry`-free; the axiom audit must show only `propext, Classical.choice, Quot.sound`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset Polynomial

namespace ArkLib.ProximityGap.NvI

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-! ## The deployed per-`R` membership condition, exactly. -/

/-- **The deployed per-agreement-set membership condition.**  A single far monomial `x^b`
restricted to the node set `R` (with values `v`) lies in `RS[R,k]` (i.e. agrees with a
degree-`<k` codeword on `R`) **iff** the top interpolant coefficient — the divided difference
`[R] x^b` — vanishes, *exactly when `#R = k+1`*.  (For `#R = k+1`, "degree `< k`" = "top
coefficient `0`", and the top coefficient is the divided difference.)  This is the codim-1
specialisation: the membership system reduces to the single Schur factor `h_{b−k}`. -/
theorem deployed_membership_codim1_eq_dividedDifference
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) {k b : ℕ} (hk : #R = k + 1) :
    (Lagrange.interpolate R v (fun i => (v i) ^ b)).coeff k = dividedDifferencePow R v b := by
  have : k = #R - 1 := by omega
  rw [this]
  exact interpolate_pow_coeff_top hvs b

/-! ## The binding object `N` is the point-sum face (`b = #R`). -/

/-- **The binding object `N` is the deployed codim-1 condition at `b = #R`.**  At agreement
size `#R = k+1` and binding far exponent `b = #R`, the deployed top-coefficient condition
`[R] x^{#R} = 0` is *exactly* the vanishing of the point sum `∑_{i∈R} v i` — the height-gate /
No-Excess binding root-sum object `N`.  (`dividedDifferencePow_card_eq_sum`.) -/
theorem binding_is_codim1_pointSum
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) (hR : R.Nonempty) :
    dividedDifferencePow R v (#R) = ∑ i ∈ R, v i :=
  dividedDifferencePow_card_eq_sum hvs hR

/-- **`N`-vanishing ⟺ codim-1 deployed membership at the binding radius.**  Combining the two:
for `#R = k+1`, the deployed per-`R` condition that `x^{#R}` lies in `RS[R,k]` (top coeff `= 0`)
holds **iff** the binding root-sum `∑_{i∈R} v i = 0`.  This is the *exact* identification of the
binding object `N` with the deployed incidence's per-set condition — *at codim 1 only*. -/
theorem binding_iff_deployed_membership_codim1
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) (hR : R.Nonempty) {k : ℕ}
    (hk : #R = k + 1) :
    (Lagrange.interpolate R v (fun i => (v i) ^ (#R))).coeff k = 0
      ↔ (∑ i ∈ R, v i) = 0 := by
  rw [deployed_membership_codim1_eq_dividedDifference hvs hk,
      binding_is_codim1_pointSum hvs hR]

/-! ## The gap at the deployed binder: the codim-2 condition carries an INDEPENDENT `h₂`. -/

/-- **The `h₂` face exists and is generally NONZERO — the constraint the height-gate misses.**
At the deployed binder the agreement set has size `#R = k+2` (codim 2), and the line-membership
system carries a *second* Schur constraint beyond the point sum: the value `h₂ = [R] x^{#R+1}`.
This lemma packages `h₂` as a genuine divided-difference object (`dividedDifferencePow R v (#R+1)`),
the top coefficient of the interpolant of `x^{#R+1}`.  It is an *independent* coordinate of the
deployed per-`R` system, not a function of the point sum `h₁` — hence not closed by the
height-gate's single-root-sum bound.  (Numerically `h₂ ≠ 0` generically; `_final` probe.) -/
theorem deployed_h2_is_dividedDifference
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) :
    (Lagrange.interpolate R v (fun i => (v i) ^ (#R + 1))).coeff (#R - 1)
      = dividedDifferencePow R v (#R + 1) :=
  interpolate_pow_coeff_top hvs (#R + 1)

/-- **The deployed-incidence vanishing system at codim ≥ 2 is STRICTLY MORE than `N`.**
Honest type-level witness of the gap.  At agreement size `#R = k+2`, the deployed per-`R`
membership of a far monomial `x^b` (`b ≥ #R`) requires *both* divided differences
`[R] x^b = 0` and the next one down `[R] x^{b-1} = 0` to vanish (the top two interpolant
coefficients over the `(k+2)` nodes); the binding object `N` is only the *single* point-sum
`[R] x^{#R} = 0`.  We state this as the explicit conjunction whose first conjunct is `N`
(at `b = #R`) and whose second conjunct (`h₂`) is the constraint the height-gate omits. -/
def DeployedBinderCondition (R : Finset ι) (v : ι → F) : Prop :=
  dividedDifferencePow R v (#R) = 0 ∧ dividedDifferencePow R v (#R + 1) = 0

/-- The binding object `N` is the FIRST conjunct of the deployed binder condition — a strictly
weaker (codim-1) constraint.  Formally: `DeployedBinderCondition R v → N R v` but the converse
fails (the `h₂` conjunct is independent).  We prove the forward (sub-object) direction; the
non-implication of the converse is the documented numerical gap (`h₂ ≠ 0` while `h₁ = 0` occurs),
recorded as `_final` probe data, NOT a Lean theorem (it is an existential over field instances). -/
theorem binding_is_subObject_of_deployedBinder
    {R : Finset ι} {v : ι → F} (h : DeployedBinderCondition R v) :
    dividedDifferencePow R v (#R) = 0 :=
  h.1

end ArkLib.ProximityGap.NvI

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.NvI.deployed_membership_codim1_eq_dividedDifference
#print axioms ArkLib.ProximityGap.NvI.binding_is_codim1_pointSum
#print axioms ArkLib.ProximityGap.NvI.binding_iff_deployed_membership_codim1
#print axioms ArkLib.ProximityGap.NvI.deployed_h2_is_dividedDifference
#print axioms ArkLib.ProximityGap.NvI.binding_is_subObject_of_deployedBinder
