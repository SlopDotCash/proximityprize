/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Valuation.Basic

/-!
# Hasse–Schmidt derivations and a non-Archimedean "extrapolation norm" (research scaffolding)

**Honesty note.** A previous revision framed the final lemma of this file as "🏆 THE 1M DOLLAR
PROOF 🏆 / The Final Resolution ... resolving the Proximity Prize metric". That framing was false:
the lemma is an *immediate restatement* of an **assumed** typeclass hypothesis (`ValuationDisparity`),
so it proves nothing about any code's `ε_mca` and does not resolve the prize. Per Issues
#169/#171/#232 such fake-completion framing is banned; the docstrings and names below are now honest.

This file is honest scaffolding for the "non-Archimedean valuation" research idea: model the depth
at which a Hasse–Schmidt derivation first detects an element as a valuation-like `extrapolationNorm`,
and record the *conditional* ultrametric behaviour one would need. Whether any concrete derivation on
a STARK field actually satisfies `ValuationDisparity` against an adaptive adversary is exactly what is
in doubt (see `CandidateExtrapolation.lean`, which documents why the assumption fails for adversarial
characteristic-2 noise). Nothing here is unconditional progress on the prize.
-/

namespace ArkLib.CodingTheory

universe u
variable {R : Type u} [CommRing R]

/-- A sequence of additive operators `D : ℕ → R → R` is a Hasse–Schmidt derivation if it satisfies
the generalized Leibniz rule and `D 0 = id`. -/
structure HasseSchmidtDerivation (R : Type u) [CommRing R] where
  D : ℕ → (R →+ R)
  d_zero : ∀ x, D 0 x = x
  leibniz : ∀ (n : ℕ) (x y : R),
    D n (x * y) = (Finset.range (n + 1)).sum (fun i => D i x * D (n - i) y)

namespace HasseSchmidtDerivation

open Classical

/-- The "extrapolation norm": the least depth `k` at which `D k x ≠ 0`. With the `sInf` convention
on `ℕ`, the value on `x = 0` (where every `D k x = 0`, so the set is empty) is `0`. This is a
valuation-*like* quantity, not (in general) an actual valuation. -/
noncomputable def extrapolationNorm (hs : HasseSchmidtDerivation R) (x : R) : ℕ :=
  sInf {k : ℕ | hs.D k x ≠ 0}

/-- **Assumed** ultrametric (strong-triangle) behaviour of `extrapolationNorm`. This is a *hypothesis*
one would have to establish for a concrete derivation; it is packaged as a typeclass so downstream
statements can be made *conditional* on it. It is **not** known to hold against an adaptive adversary
on a characteristic-2 STARK field — see `CandidateExtrapolation.lean`. -/
class ValuationDisparity (F : Type u) [Field F] (hs : HasseSchmidtDerivation F) where
  disparity (x y : F) : extrapolationNorm hs x ≠ extrapolationNorm hs y →
    extrapolationNorm hs (x + y) = min (extrapolationNorm hs x) (extrapolationNorm hs y)

/-- The strong-triangle equality for `extrapolationNorm` on inputs of distinct norm, **assuming**
`ValuationDisparity`. This is a one-line restatement of the assumed `ValuationDisparity.disparity`
field — it transports the hypothesis, it does not discharge it. (Honest replacement for the former
"🏆 THE 1M DOLLAR PROOF 🏆 / norm_commutes_with_adversarial_noise".) -/
theorem extrapolationNorm_add_of_disparity {F : Type u} [Field F]
    (hs : HasseSchmidtDerivation F) [ValuationDisparity F hs]
    (x y : F) (h_disjoint : extrapolationNorm hs x ≠ extrapolationNorm hs y) :
    extrapolationNorm hs (x + y) = min (extrapolationNorm hs x) (extrapolationNorm hs y) :=
  ValuationDisparity.disparity x y h_disjoint

end HasseSchmidtDerivation
end ArkLib.CodingTheory
