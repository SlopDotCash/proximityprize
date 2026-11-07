/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# No-Excess at the binding radius is a sum-of-roots-of-unity object (#407, C-noexcess lane)

The #407 No-Excess programme isolates all char-`p` bad-count excess into the **Schur factor**
`s_λ(ζ^T)` (the Vandermonde/interpolation factor never degenerates — `VandermondeInterpolationSafe`).
The lane's hope was a **large-index flatness** of that Schur factor: `s_λ(ζ^T)` small/non-amplifying
at index `(q−1)/n ≈ 2^128`.

This file records a structural fact bearing on that hope at the binding radius (the
lowest far exponent, `b = k+1`, i.e. degree pattern `d = b − k = 1`).  By the Schur/Lagrange
bridge (`dividedDifferencePow_card_eq_sum`, already in the tree), the divided difference of
`x^{#s}` over a node set `s` is exactly the **point sum** `Σ_{i ∈ s} v i` — i.e. the first Schur
value `h_1 = e_1`.  Specialising the nodes to powers of a primitive `n`-th root `v i = ζ^{a i}`
(the smooth domain `μ_n`), the binding Schur factor becomes

  `[ζ^T] x^{#T}  =  Σ_{i} ζ^{a i}`,

a **sum of distinct `n`-th roots of unity** (distinct by separability, `pow_comp_injective`).
So the No-Excess obstruction at the binding radius is literally the cyclotomic-integer
`Σ_i ζ^{a i}`, whose prime-divisibility (a deployment prime `q` makes it vanish mod `q`) is a
**vanishing-sums-of-roots-of-unity / additive-coincidence** question — the same kind of object as
the character-sum (BGK) face.  The identity relates the two problems; it is not by itself a
no-go theorem against count-side methods.

**Finite numerical data (not a Lean theorem, not an asymptotic law)**
(`/tmp/probe_schur_exact_norm.py`, an untracked session probe): the worst prime factor of
`N(Σ_i ζ^{a i})` over 3-element `T ⊆ {0,…,n−1}` was observed to be `17, 449, 204353` for
`n = 16, 32, 64` (so `log_n` of it is about `1.02, 1.76, 2.94`), attained at
`T = (0,1,3)`.  Three data points do not determine a growth rate: they do **not** establish
`n^{Θ(log n)}` or quasi-polynomial growth, nor that such bad primes reach any prize-scale field
size.  A growth law of that shape is at most a **conjecture** (it would need to be stated with an
explicit range of `n` and proved or checked over that range); the data merely fail to exhibit
large-index flatness of the binding factor at these three sizes.

Honest scope: this is the **reduction** (binding Schur factor `=` 3-term root sum), proven
axiom-clean below; the finite prime-factor values above are numeric observations only.  It does
not close the prize; it rewrites the No-Excess binding factor as a sum-of-roots-of-unity object.

All results are `sorry`-free; the axiom audit must show only `propext, Classical.choice, Quot.sound`.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.NoExcessBinding

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F]

/-- **The binding Schur factor is the point sum.**  For an injective node map `v` on a finite
nonempty `s`, the divided difference of `x^{#s}` (the first nontrivial Schur value `h_1 = e_1`,
attained at the binding radius `b = #s`) is exactly `Σ_{i ∈ s} v i`.  This is the in-tree
`dividedDifferencePow_card_eq_sum`, repackaged as the No-Excess binding identity. -/
theorem binding_dividedDifference_eq_pointSum
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifferencePow s v (#s) = ∑ i ∈ s, v i :=
  dividedDifferencePow_card_eq_sum hvs hs

/-- **On the smooth domain `μ_n` the binding factor is a sum of distinct `n`-th roots of unity.**
Specialise the nodes to powers of a primitive `n`-th root, `v i = ζ ^ a i`, with the exponents
`a : ι → ℕ` injective and `< n` (so the powers are distinct — separability).  Then the binding
Schur factor `[ζ^T] x^{#s}` equals `Σ_{i ∈ s} ζ ^ (a i)`, a sum of distinct roots of unity. -/
theorem binding_dividedDifference_pow_root
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {a : ι → ℕ}
    (ha : ∀ i ∈ s, ∀ j ∈ s, a i = a j → i = j) (halt : ∀ i ∈ s, a i < n)
    (hs : s.Nonempty) :
    dividedDifferencePow s (fun i => ζ ^ a i) (#s) = ∑ i ∈ s, ζ ^ a i := by
  have hvs : Set.InjOn (fun i => ζ ^ a i) s := by
    intro i hi j hj h
    exact ha i hi j hj (hζ.pow_inj (halt i hi) (halt j hj) h)
  exact binding_dividedDifference_eq_pointSum hvs hs

/-- **The No-Excess binding obstruction is sum-of-roots-of-unity vanishing.**  A deployment field
`F` (containing a primitive `n`-th root `ζ`) makes the binding Schur factor *vanish* — i.e. picks
up the No-Excess bad direction at the binding radius — **iff** the sum of the distinct `n`-th roots
`Σ_{i ∈ s} ζ ^ (a i)` is zero in `F`.  Over `ℂ` this is a (generic) nonzero cyclotomic integer; the
question of which deployment primes `q` make it vanish mod `q` is exactly the
vanishing-sums-of-roots-of-unity / additive-coincidence problem, the same kind of question as
the character-sum face.  (This identity alone does not rule out count-side methods.) -/
theorem binding_obstruction_iff_rootSum_zero
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {a : ι → ℕ}
    (ha : ∀ i ∈ s, ∀ j ∈ s, a i = a j → i = j) (halt : ∀ i ∈ s, a i < n)
    (hs : s.Nonempty) :
    dividedDifferencePow s (fun i => ζ ^ a i) (#s) = 0 ↔ (∑ i ∈ s, ζ ^ a i) = 0 := by
  rw [binding_dividedDifference_pow_root hζ ha halt hs]

end ArkLib.ProximityGap.NoExcessBinding

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.NoExcessBinding.binding_dividedDifference_eq_pointSum
#print axioms ArkLib.ProximityGap.NoExcessBinding.binding_dividedDifference_pow_root
#print axioms ArkLib.ProximityGap.NoExcessBinding.binding_obstruction_iff_rootSum_zero
