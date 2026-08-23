/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The interpolation half of No-Excess is unconditionally safe (#407)

The #407 **No-Excess** programme factors the bad-subset vanishing condition for dyadic
Reed–Solomon list decoding as a product of a **Schur factor** and a **Vandermonde factor**:
`det = Schur_λ(ζ^T) · Vandermonde(ζ^T)`, where `T` is a subset of exponents and `ζ` a primitive
`n`-th root of unity (`n = 2^μ` in the prize regime).  The conjecture asks whether the char-`p`
bad count can exceed the char-`0` count; the answer hinges on which factor can pick up extra
vanishing modulo a deployment prime `q`.

This file machine-checks the **unconditional half**: the Vandermonde (interpolation/consistency)
factor **never degenerates modulo an odd `q`**.  The reason is elementary and char-free — it is just
**separability**: whenever the field `F` contains a primitive `n`-th root of unity `ζ` (which forces
`char F ∤ n`, in particular `char F` odd for `n = 2^μ`), the powers `ζ^{a₀}, …, ζ^{a_{m-1}}` at
*distinct* exponents `a_i < n` are *distinct* elements of `F` (`IsPrimitiveRoot.pow_inj`), so the
Vandermonde matrix they generate is nonsingular (`det_vandermonde_ne_zero_iff`).

Consequently **every** char-`p` excess in the bad count must come from the **Schur factor** — the
Vandermonde/interpolation structure contributes none.  This isolates the entire No-Excess obstruction
to `Schur_λ(ζ^T)`, exactly as the count-side (NVM/flatness) reformulation requires.  It is the
non-BGK, count-side companion to the analytic floor: a genuinely different face of the prize.

All elementary; **axiom-clean** (`propext, Classical.choice, Quot.sound`), no `sorry`.
-/

open Matrix

namespace ArkLib.ProximityGap.VandermondeInterpolationSafe

variable {F : Type*} [Field F]

/-- **Distinct exponents give distinct powers of a primitive root.**  If `ζ` is a primitive `n`-th
root of unity in `F` and `a : Fin m → ℕ` takes values `< n` injectively, then `i ↦ ζ ^ a i` is
injective.  (No characteristic hypothesis beyond the existence of `ζ`, which already forces
`char F ∤ n`.) -/
theorem pow_comp_injective {n m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {a : Fin m → ℕ} (ha : Function.Injective a) (halt : ∀ i, a i < n) :
    Function.Injective (fun i => ζ ^ a i) := by
  intro i j h
  exact ha (hζ.pow_inj (halt i) (halt j) h)

/-- **The interpolation half is unconditionally non-degenerate.**  For a primitive `n`-th root `ζ`
in any field `F`, and any injective choice of exponents `a : Fin m → ℕ` with `a i < n`, the
Vandermonde determinant of the powers `ζ^{a i}` is **nonzero** — over `ℂ` and over every `F_q` with
`q ≡ 1 (mod n)`, `q` odd, alike.  The Vandermonde/consistency factor of the No-Excess vanishing
condition therefore never picks up extra vanishing modulo a deployment prime: **all char-`p` excess
lives in the Schur factor.** -/
theorem vandermonde_pow_ne_zero {n m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {a : Fin m → ℕ} (ha : Function.Injective a) (halt : ∀ i, a i < n) :
    (Matrix.vandermonde (fun i => ζ ^ a i)).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr (pow_comp_injective hζ ha halt)

/-- **Restatement as a product of nonzero differences.**  The Vandermonde determinant is the product
`∏_{i<j} (ζ^{a j} − ζ^{a i})`, and each factor is nonzero (distinct powers of a primitive root).
This is the explicit "no interpolation collision mod `q`" statement: every pairwise difference of the
deployed evaluation points is a unit. -/
theorem vandermonde_pow_diffs_ne_zero {n m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {a : Fin m → ℕ} (ha : Function.Injective a) (halt : ∀ i, a i < n)
    {i j : Fin m} (hij : i ≠ j) :
    ζ ^ a j - ζ ^ a i ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  exact hij ((pow_comp_injective hζ ha halt) h.symm)

end ArkLib.ProximityGap.VandermondeInterpolationSafe
