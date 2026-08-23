/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots

/-!
# The Guruswami–Sudan list-size bound

The classical output of the Guruswami–Sudan list-decoder: every candidate codeword `f` that the
interpolation polynomial `Q(X, Y)` annihilates (i.e. `Q(X, f(X)) = 0`) is a *root of `Q` viewed
as a univariate polynomial in `Y` over `F[X]`*. Since `Q` has `Y`-degree `≤ deg_Y` and `F[X]` is
an integral domain, there are at most `deg_Y` such codewords.

This is the list-size half of Guruswami–Sudan list decoding (the interpolation half is
`gkl24_interpolation_existence`; the multiplicity half is `rootMultiplicity_aeval_ge` in
`SubstitutionMultiplicity`). The key device is the `F`-algebra isomorphism
`psi : F[X₀, X₁] ≅ (F[X])[Y]` sending `X₀ ↦ C X` and `X₁ ↦ Y`, under which the substitution
`Q(X, f(X))` becomes the evaluation `(psi Q).eval f`.
-/

open MvPolynomial

namespace CodingTheory.Bounds

variable {F : Type} [Field F]

/-- The `F`-algebra map `F[X₀, X₁] → (F[X])[Y]` sending `X₀ ↦ C X` and `X₁ ↦ Y`. -/
noncomputable def psi : MvPolynomial (Fin 2) F →ₐ[F] Polynomial (Polynomial F) :=
  aeval ![Polynomial.C Polynomial.X, Polynomial.X]

/-- Evaluating `psi Q` at `f ∈ F[X]` recovers the bivariate substitution `Q(X, f(X))`. -/
theorem psi_eval (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) :
    (psi Q).eval f
      = MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q := by
  have h : (Polynomial.evalRingHom f).comp (psi : MvPolynomial (Fin 2) F →ₐ[F] _).toRingHom
      = (MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) :
          MvPolynomial (Fin 2) F →ₐ[F] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [psi]
    · intro i; fin_cases i <;> simp [psi]
  exact congrFun (congrArg DFunLike.coe h) Q

/-- Explicit `F`-algebra retraction of `psi`, sending `Y ↦ X₁` and coefficients `g(X) ↦ g(X₀)`. -/
noncomputable def phi : Polynomial (Polynomial F) →ₐ[F] MvPolynomial (Fin 2) F :=
  Polynomial.aevalTower (Polynomial.aeval (MvPolynomial.X (0 : Fin 2))) (MvPolynomial.X 1)

theorem psi_injective : Function.Injective (psi : MvPolynomial (Fin 2) F →ₐ[F] _) := by
  have hinv : (phi.comp psi : MvPolynomial (Fin 2) F →ₐ[F] _) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [phi, psi]
  exact Function.LeftInverse.injective (g := phi)
    (fun x => congrFun (congrArg DFunLike.coe hinv) x)

set_option maxHeartbeats 800000 in
/-- The `Y`-degree of `psi Q` is bounded by the `X₁`-degree of `Q`. -/
theorem natDegree_psi_le (Q : MvPolynomial (Fin 2) F) (deg_Y : ℕ)
    (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y) :
    (psi Q).natDegree ≤ deg_Y := by
  classical
  have hsum : psi Q
      = ∑ m ∈ Q.support, psi (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
  rw [hsum]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le ?_
  intro m hm
  simp only [Function.comp_apply]
  have hmono : psi (MvPolynomial.monomial m (MvPolynomial.coeff m Q))
      = Polynomial.C (Polynomial.C (MvPolynomial.coeff m Q) * Polynomial.X ^ m 0)
          * Polynomial.X ^ m 1 := by
    rw [psi, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp),
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [show (algebraMap F (Polynomial (Polynomial F))) (MvPolynomial.coeff m Q)
          = Polynomial.C (Polynomial.C (MvPolynomial.coeff m Q)) from rfl,
      Polynomial.C_mul, Polynomial.C_pow]
    ring
  rw [hmono]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  exact le_trans (MvPolynomial.monomial_le_degreeOf 1 hm) hY

/-- **Guruswami–Sudan list-size bound.** If `Q ≠ 0` has `Y`-degree `≤ deg_Y`, then the set of
candidate codewords `f` annihilated by `Q` (`Q(X, f(X)) = 0`) has size at most `deg_Y`. -/
theorem gs_list_size_bound
    (Q : MvPolynomial (Fin 2) F) (hQ : Q ≠ 0) (deg_Y : ℕ)
    (hdegY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (S : Finset (Polynomial F))
    (hS : ∀ f ∈ S, MvPolynomial.aeval
      (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q = 0) :
    S.card ≤ deg_Y := by
  classical
  have hpsi : psi Q ≠ 0 := fun h => hQ (psi_injective (by rw [h, map_zero]))
  have hsub : S ⊆ (psi Q).roots.toFinset := by
    intro f hf
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpsi, Polynomial.IsRoot, psi_eval]
    exact hS f hf
  calc S.card ≤ (psi Q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (psi Q).roots := Multiset.toFinset_card_le _
    _ ≤ (psi Q).natDegree := Polynomial.card_roots' _
    _ ≤ deg_Y := natDegree_psi_le Q deg_Y hdegY

end CodingTheory.Bounds
