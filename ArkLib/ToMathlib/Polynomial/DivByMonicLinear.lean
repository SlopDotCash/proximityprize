/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Linearity of division by a monic polynomial

Mathlib proves that `· %ₘ q` (remainder on division by a monic polynomial) is `R`-linear
(`Polynomial.add_modByMonic`, `Polynomial.smul_modByMonic`, bundled as
`Polynomial.modByMonicHom`), but the corresponding statements for the *quotient* `· /ₘ q`
are absent.  This file supplies them, in the same generality (a commutative ring `R`,
no `Monic` hypothesis — the non-monic case is degenerate since `p /ₘ q = 0` there), by the
same uniqueness argument (`Polynomial.div_modByMonic_unique`).

## Main results

* `Polynomial.add_divByMonic` : `(p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q`
* `Polynomial.smul_divByMonic` : `(c • p) /ₘ q = c • (p /ₘ q)`
* `Polynomial.neg_divByMonic`, `Polynomial.sub_divByMonic`
* `Polynomial.divByMonicHom` : `· /ₘ q` bundled as an `R`-linear map `R[X] →ₗ[R] R[X]`

## Mathlib upstreaming target

`Mathlib/Algebra/Polynomial/Div.lean` (next to `add_modByMonic`) for the `add`/`neg`/`sub`
lemmas, and `Mathlib/Algebra/Polynomial/RingDivision.lean` (next to `smul_modByMonic` /
`modByMonicHom`) for `smul_divByMonic` / `divByMonicHom`.  This is PR-1 of the #466 r24
upstream plan.
-/

namespace Polynomial

variable {R : Type*} [CommRing R] {q : R[X]}

/-- Division by a monic polynomial is additive:
`(p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q`.

(The companion of `Polynomial.add_modByMonic`; no `Monic` hypothesis is needed because in
the non-monic case both sides are `0`.) -/
theorem add_divByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
        (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) (p₁ %ₘ q + p₂ %ₘ q) hq
            ⟨by
              rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div, ← add_assoc,
                add_comm (q * _), modByMonic_add_div],
              (degree_add_le _ _).trans_lt
                (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).1
  · simp only [divByMonic_eq_of_not_monic _ hq, add_zero]

/-- Division by a monic polynomial commutes with negation: `(-p) /ₘ q = -(p /ₘ q)`.

(The companion of `Polynomial.neg_modByMonic`.) -/
theorem neg_divByMonic (p : R[X]) : (-p) /ₘ q = -(p /ₘ q) := by
  rw [eq_neg_iff_add_eq_zero, ← add_divByMonic, neg_add_cancel, zero_divByMonic]

/-- Division by a monic polynomial is subtractive:
`(p₁ - p₂) /ₘ q = p₁ /ₘ q - p₂ /ₘ q`.

(The companion of `Polynomial.sub_modByMonic`.) -/
theorem sub_divByMonic (p₁ p₂ : R[X]) : (p₁ - p₂) /ₘ q = p₁ /ₘ q - p₂ /ₘ q := by
  simp only [sub_eq_add_neg, add_divByMonic, neg_divByMonic]

/-- Division by a monic polynomial commutes with scalar multiplication:
`(c • p) /ₘ q = c • (p /ₘ q)`.

(The companion of `Polynomial.smul_modByMonic`.) -/
theorem smul_divByMonic (c : R) (p : R[X]) : (c • p) /ₘ q = c • (p /ₘ q) := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
        (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
            ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
              (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).1
  · simp only [divByMonic_eq_of_not_monic _ hq, smul_zero]

/-- `· /ₘ q` as an `R`-linear map.

(The companion of `Polynomial.modByMonicHom`.) -/
@[simps]
noncomputable def divByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p /ₘ q
  map_add' := add_divByMonic
  map_smul' := smul_divByMonic

end Polynomial
