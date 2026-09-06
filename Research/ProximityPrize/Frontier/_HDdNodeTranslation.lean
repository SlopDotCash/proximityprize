/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import Research.ProximityPrize.Frontier._HDdInterpolationCore

/-!
# HDd — node translation: the contact substitution at `(α, y)` factors through the origin

`contactSubstD d α y = contactSubstD d 0 0 ∘ σ_{α,y}` where `σ_{α,y}` is the algebra
automorphism `X ↦ X + C α`, `Y₀ ↦ Y₀ + C y`, `Y_{j+1} ↦ Y_{j+1}` (`translateD`).  Hence the
node map at `(α, y)` equals the origin node map composed with `σ_{α,y}`
(`nodeMapD_translate`), and on any subspace stable under `σ` — in particular the span of a
cap-monomial family that is downward closed in the `(a, b₀)` exponents, as every probe cap
space is (`wdeg` decreases when `a` or `b₀` decreases with `bs` fixed) — the restricted
ranks at every node agree with the origin ranks.  This is the first half of the formal link
between the integer counting certificates and `exists_interpolant_d`; the second half is the
`(g₁, g₂)` bigrading of the origin substitution feeding
`finrank_span_range_le_sum_min` (`_HDdCountingBound.lean`).
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Polynomial

variable {F : Type*} [CommRing F]

/-- The translation `X ↦ X + C α`, `Y₀ ↦ Y₀ + C y`, `Y_{j+1} ↦ Y_{j+1}`. -/
noncomputable def translateD (d : ℕ) (α y : F) :
    MvPolynomial (Fin (d + 2)) F →ₐ[F] MvPolynomial (Fin (d + 2)) F :=
  MvPolynomial.aeval
    (Fin.cons (MvPolynomial.X 0 + MvPolynomial.C α)
      (Fin.cons (MvPolynomial.X 1 + MvPolynomial.C y)
        (fun j : Fin d => MvPolynomial.X j.succ.succ)))

/-- **Node translation.**  The contact substitution at `(α, y)` is the origin substitution
after translating the interpolant. -/
theorem contactSubstD_translate (d : ℕ) (α y : F) (Q : MvPolynomial (Fin (d + 2)) F) :
    contactSubstD d α y Q = contactSubstD d 0 0 (translateD d α y Q) := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · -- X: α + T  vs  subst₀(X + C α) = T + C α
    simp only [contactSubstD, translateD, MvPolynomial.aeval_X, Fin.cons_zero, map_add,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, map_zero]
    ring
  · -- Y₀
    have h1 : (1 : Fin (d + 2)) = Fin.succ 0 := by ext; simp
    simp only [contactSubstD, translateD, h1, MvPolynomial.aeval_X, Fin.cons_succ,
      Fin.cons_zero, map_add, MvPolynomial.aeval_C]
    rw [MvPolynomial.algebraMap_eq]
    simp only [map_zero, zero_add]
    ring
  · -- Y_{j+1}
    simp only [contactSubstD, translateD, MvPolynomial.aeval_X, Fin.cons_succ]

/-- The node constraint transports along the translation. -/
theorem contactConstraintD_translate (d : ℕ) (α y : F) (m : ℕ)
    (Q : MvPolynomial (Fin (d + 2)) F) :
    ContactConstraintD d α y m Q ↔ ContactConstraintD d 0 0 m (translateD d α y Q) := by
  unfold ContactConstraintD
  rw [contactSubstD_translate]

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.contactSubstD_translate
