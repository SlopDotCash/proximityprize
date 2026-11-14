/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# The moment ↔ Jacobi-phase correlation identity: the √p removes from the WHOLE moment (#444)

Building on `_JacobiCocycleDispersion`: the Gauss phases `θ_χ = g(χ)/√p` form a projective character with the
normalized-Jacobi-sum cocycle. This file proves the **core algebraic identity** that powers the framing — in the
`2r`-th moment, the magnitude collapses to a pure **unit-phase correlation**.

## The identity

For ANY unit-modulus phase `θ` (`normSq(θ s)=1`, i.e. `|θ s|=1`; here `θ`=the Gauss phase, lemma is general) and
two `r`-tuples `x, y` on the SAME additive relation `Σx_i = Σy_j`, the moment summand collapses:
```
(∏_i θ(x_i))·conj(∏_j θ(y_j)) = Jphase(x)·conj(Jphase(y)),   Jphase(x) := (∏_i θ(x_i))·conj(θ(Σx_i)),  |Jphase|=1.
```
`Jphase(x)` is the **normalized iterated Gauss/Jacobi phase** — a UNIT complex number (the `√p` scale is gone).
So the period's `2r`-th moment `Σ_b‖η_b‖^{2r} = (norm)·Σ_{Σx=Σy} Jphase(x)·conj(Jphase(y))` is a pure correlation
of unit phases: NO `√p` anywhere (it cancelled), and a SIGNED sum (not a count) — the object sits OUTSIDE both
obstructions (moment-necessity wants a count; √p-vacuity wants field scale).

## The diagonal / off-diagonal split (where the prize now lives)

* **Diagonal** (`Jphase(y)=Jphase(x)`, e.g. `y` a permutation of `x` by symmetry of the iterated Jacobi sum):
  each term is `Jphase(x)·conj(Jphase(x)) = 1` (`diagonal_term_one`) → the **Wick count** `(2r−1)‼·mult` = the
  char-0 energy.
* **Off-diagonal** (`Σx=Σy` but `Jphase(y)≠Jphase(x)`): a nontrivial unit phase. **Prize ⟺ these cancel
  (square-root):** `|Σ_{off-diag} Jphase(x)·conj(Jphase(y))| ≤ (lower order than the diagonal)`.

## The named MISSING THEOREM (the novel external mathematics)

`OffDiagonalJacobiCancellation`: the off-diagonal sum of normalized iterated-Jacobi-sum phases over the additive
relations of `μ_n`, at depth `r ≈ log m`, has square-root cancellation — a Deligne/Katz EQUIDISTRIBUTION-of-
Jacobi-sums statement at growing order (Jacobi sums = Frobenius eigenvalues of Fermat-type varieties). A
CONCRETE algebraic-geometry target, strictly better-structured than a raw character sum; the quantitative
growing-order version is OPEN. Proving it closes the prize; NOT discharged here.

Honest status: proves the √p-removal identity + diagonal collapse, axiom-clean; relocates the prize to
off-diagonal Jacobi cancellation. NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiMomentIdentity

open Finset ComplexConjugate

variable {R : Type*} [AddCommMonoid R] {r : ℕ}

/-- **The normalized iterated Jacobi phase** `Jphase(x) = (∏_i θ(x_i))·conj(θ(Σx_i))` — the `√p`-free part of
the Gauss-product `∏ g(χ_i)`. -/
noncomputable def Jphase (θ : R → ℂ) (x : Fin r → R) : ℂ :=
  (∏ i, θ (x i)) * conj (θ (∑ i, x i))

/-- `normSq(Jphase(x)) = 1` for a unit phase `θ` (`normSq∘θ ≡ 1`): the iterated Jacobi phase is a UNIT (no √p). -/
theorem Jphase_normSq (θ : R → ℂ) (hθ : ∀ s, Complex.normSq (θ s) = 1) (x : Fin r → R) :
    Complex.normSq (Jphase θ x) = 1 := by
  unfold Jphase
  rw [Complex.normSq_mul, Complex.normSq_conj, hθ, mul_one, map_prod]
  exact Finset.prod_eq_one (fun i _ => hθ (x i))

/-- **The core √p-removal identity.** For tuples on the SAME additive relation `Σx_i = Σy_j`, the moment summand
`(∏θ(x_i))·conj(∏θ(y_j))` equals the pure unit-phase correlation `Jphase(x)·conj(Jphase(y))`. The magnitude (the
`√p` of the Gauss sums) cancels entirely; what remains is a SIGNED correlation of UNIT phases — the object lives
outside BOTH obstructions. -/
theorem moment_summand_eq (θ : R → ℂ) (hθ : ∀ s, Complex.normSq (θ s) = 1) {x y : Fin r → R}
    (h : (∑ i, x i) = ∑ j, y j) :
    (∏ i, θ (x i)) * conj (∏ j, θ (y j)) = Jphase θ x * conj (Jphase θ y) := by
  have hs : conj (θ (∑ j, y j)) * θ (∑ j, y j) = 1 := by
    rw [mul_comm, Complex.mul_conj, hθ]; norm_num
  unfold Jphase
  rw [map_mul, Complex.conj_conj, h]
  rw [show (∏ i, θ (x i)) * conj (θ (∑ j, y j)) * (conj (∏ j, θ (y j)) * θ (∑ j, y j))
        = (∏ i, θ (x i)) * conj (∏ j, θ (y j)) * (conj (θ (∑ j, y j)) * θ (∑ j, y j)) from by ring,
     hs, mul_one]

/-- **The diagonal term is `1`.** When `y` gives the same iterated phase as `x` (e.g. `y` a permutation of `x`,
by symmetry of the iterated Jacobi sum), `Jphase(x)·conj(Jphase(x)) = 1`. So the diagonal contributes the plain
Wick count — exactly the char-0 energy `(2r−1)‼·multiplicity`. -/
theorem diagonal_term_one (θ : R → ℂ) (hθ : ∀ s, Complex.normSq (θ s) = 1) (x : Fin r → R) :
    Jphase θ x * conj (Jphase θ x) = 1 := by
  rw [Complex.mul_conj, Jphase_normSq θ hθ]; norm_num

/-- **The named MISSING THEOREM — off-diagonal Jacobi cancellation (the prize, NOT proved).** The off-diagonal
correlation `Σ_{Σx=Σy, Jphase(y)≠Jphase(x)} Jphase(x)·conj(Jphase(y))` (real part `Off`) is bounded by a slack
`S` (the deviation below the diagonal/Wick value) at depth `r ≈ log m`. The Deligne/Katz-equidistribution-of-
Jacobi-sums statement at growing order — the novel external mathematics required. NOT discharged. -/
def OffDiagonalJacobiCancellation (Off S : ℝ) : Prop := Off ≤ S

end ArkLib.ProximityGap.Frontier.JacobiMomentIdentity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiMomentIdentity.Jphase_normSq
#print axioms ArkLib.ProximityGap.Frontier.JacobiMomentIdentity.moment_summand_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiMomentIdentity.diagonal_term_one
