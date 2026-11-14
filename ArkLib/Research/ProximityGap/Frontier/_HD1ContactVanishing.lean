/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# HD1 — the hidden-derivative contact vanishing lemma (TR26-164 Lemma 3.1, order `d = 1`)

The list-decoding interpolants of ECCC TR26-164 (Brakensiek–Chen–Putterman–Zhang–Zheng,
2026-09-04) and of better.codes PR #122 (nasqret, 2026-08-27) are polynomials
`Q(X, Y₀, Y₁)` in which `Y₁` stands for the *unknown* derivative of the message polynomial.
At a received node `(α, y)` one imposes the **formal contact constraint**: after the
substitution

    X ↦ α + T,   Y₀ ↦ y + T·(Y₁ + E),   Y₁ ↦ Y₁

(`T`, `E`, `Y₁` fresh variables), every monomial `T^i E^b Y₁^e` of the result has
`i + b ≥ m`.  The lemma says that this purely formal condition forces multiplicity `≥ m`
of `Q(X, P, P')` at `α` for **every** polynomial `P` through `(α, y)` — no derivative data
is needed at the node.  The point is that the Taylor identity
`P(α + T) = y + T·(P'(α + T) + E_P(T))` with `E_P ≡ 0 (mod T)` is the only relation used;
`scripts/probes/hd_true_rank.py` shows numerically that this formal system has exactly the
rank of the true condition, so nothing is lost.

This file is Mathlib-only and axiom-clean.  Companion probes:
`scripts/probes/hd1_interpolation_threshold.py` (exact ranks and thresholds),
`scripts/probes/hd1_line_ledger.py`; KB note
`docs/kb/deltastar-hd1-hidden-derivative-interpolation-2026-09-05.md`.

Two forms are proved:

* `contact_vanishing` — the list-decoding form `Q(X, Y₀, Y₁)`;
* `contact_vanishing_line` — the affine-line form `Q(X, Y, R, Z)` of PR #122, where the
  node value is `u₀ + Z·u₁` and the conclusion holds for every scalar `γ` and every `P`
  with `P(α) = u₀ + γ u₁`.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Polynomial

variable {F : Type*} [CommRing F]

/-! ## Transport of divisibility along the Taylor shift -/

/-- The Taylor shift `f ↦ f.comp (X + C α)` as an algebra hom. -/
noncomputable abbrev shift (α : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (X + C α)

theorem shift_apply (α : F) (f : F[X]) : shift α f = f.comp (X + C α) := rfl

/-- If `X^m` divides the Taylor shift of `g` at `α`, then `(X - C α)^m` divides `g`. -/
theorem X_sub_C_pow_dvd_of_X_pow_dvd_shift (α : F) (m : ℕ) (g : F[X])
    (h : X ^ m ∣ shift α g) : (X - C α) ^ m ∣ g := by
  obtain ⟨c, hc⟩ := h
  have hcomp : (g.comp (X + C α)).comp (X - C α) = g := by
    rw [comp_assoc]
    have : (X + C α).comp (X - C α) = X := by
      rw [add_comp, X_comp, C_comp]; ring
    rw [this, comp_X]
  refine ⟨c.comp (X - C α), ?_⟩
  have hc' : g.comp (X + C α) = X ^ m * c := hc
  calc g = (g.comp (X + C α)).comp (X - C α) := hcomp.symm
    _ = (X ^ m * c).comp (X - C α) := by rw [hc']
    _ = (X - C α) ^ m * c.comp (X - C α) := by rw [mul_comp, pow_comp, X_comp]

/-! ## The order-one Taylor identity at a node -/

/-- Any polynomial through `(α, y)` has Taylor shift `y + X·U` for a unique `U`. -/
theorem exists_taylor_tail (α y : F) (P : F[X]) (hP : P.eval α = y) :
    ∃ U : F[X], shift α P = C y + X * U := by
  have h0 : (shift α P).coeff 0 = y := by
    rw [shift_apply, ← taylor_apply, taylor_coeff_zero, hP]
  have hdvd : X ∣ shift α P - C y := by
    rw [X_dvd_iff, coeff_sub, h0, coeff_C_zero, sub_self]
  obtain ⟨U, hU⟩ := hdvd
  exact ⟨U, by rw [← sub_add_cancel (shift α P) (C y), hU, add_comm]⟩

/-- The shifted derivative is the derivative of the shift (chain rule with unit slope). -/
theorem shift_derivative (α : F) (P : F[X]) :
    shift α (derivative P) = derivative (shift α P) := by
  rw [shift_apply, shift_apply, derivative_comp, derivative_X_add_C, one_mul]

/-! ## The list-decoding form -/

/-- Node substitution `X ↦ C α + T`, `Y₀ ↦ C y + T·(Y₁ + E)`, `Y₁ ↦ Y₁`; output
variables `0 = T`, `1 = E`, `2 = Y₁`. -/
noncomputable def contactSubst (α y : F) :
    MvPolynomial (Fin 3) F →ₐ[F] MvPolynomial (Fin 3) F :=
  MvPolynomial.aeval
    ![MvPolynomial.C α + MvPolynomial.X 0,
      MvPolynomial.C y + MvPolynomial.X 0 * (MvPolynomial.X 2 + MvPolynomial.X 1),
      MvPolynomial.X 2]

/-- The formal contact constraint of order `m` at the node `(α, y)`: every monomial of the
substituted interpolant has `T`-degree plus `E`-degree at least `m`.  This is TR26-164 (15)
with `d = 1` (equivalently the PR #122 "vanishing below contact weight `m`" with weights
`1` for `T` and `2` for `S = T·E`). -/
def ContactConstraint (α y : F) (m : ℕ) (Q : MvPolynomial (Fin 3) F) : Prop :=
  ∀ μ ∈ (contactSubst α y Q).support, m ≤ μ 0 + μ 1

/-- `Q(X, P, P')`. -/
noncomputable def specialize (Q : MvPolynomial (Fin 3) F) (P : F[X]) : F[X] :=
  MvPolynomial.aeval ![X, P, derivative P] Q

/-- Evaluating the substituted interpolant at `T ↦ X`, `E ↦ X * E'`, `Y₁ ↦ Y₁` lands in
`(X^m)` whenever the contact constraint holds. -/
theorem X_pow_dvd_aeval_of_contact (α y : F) (m : ℕ) (Q : MvPolynomial (Fin 3) F)
    (hQ : ContactConstraint α y m Q) (E' Y₁ : F[X]) :
    X ^ m ∣ MvPolynomial.aeval ![X, X * E', Y₁] (contactSubst α y Q) := by
  set S := contactSubst α y Q with hS
  rw [MvPolynomial.as_sum S, map_sum]
  refine Finset.dvd_sum fun μ hμ => ?_
  rw [MvPolynomial.aeval_monomial]
  have hμ' : m ≤ μ 0 + μ 1 := hQ μ hμ
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  refine Dvd.dvd.mul_left ?_ _
  refine Dvd.dvd.mul_right ?_ _
  rw [mul_pow, ← mul_assoc, ← pow_add]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ hμ') _

/-- **Contact vanishing (TR26-164 Lemma 3.1, `d = 1`).**  If `Q` satisfies the formal contact
constraint of order `m` at `(α, y)`, then `(X - C α)^m` divides `Q(X, P, P')` for every
polynomial `P` with `P(α) = y`. -/
theorem contact_vanishing (α y : F) (m : ℕ) (Q : MvPolynomial (Fin 3) F)
    (hQ : ContactConstraint α y m Q) (P : F[X]) (hP : P.eval α = y) :
    (X - C α) ^ m ∣ specialize Q P := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_shift
  obtain ⟨U, hU⟩ := exists_taylor_tail α y P hP
  -- the shifted derivative
  have hD : shift α (derivative P) = U + X * derivative U := by
    rw [shift_derivative, hU, derivative_add, derivative_C, zero_add, derivative_mul,
      derivative_X, one_mul]
  -- push the shift through the specialization
  have hspec : shift α (specialize Q P) =
      MvPolynomial.aeval ![X + C α, C y + X * U, U + X * derivative U] Q := by
    unfold specialize
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    fin_cases i
    · show shift α X = X + C α
      rw [shift_apply, X_comp]
    · exact hU
    · exact hD
  rw [hspec]
  -- rewrite as the evaluation of the substituted interpolant
  have hkey : MvPolynomial.aeval ![X + C α, C y + X * U, U + X * derivative U] Q =
      MvPolynomial.aeval ![X, X * (-derivative U), U + X * derivative U] (contactSubst α y Q) := by
    unfold contactSubst
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  rw [hkey]
  exact X_pow_dvd_aeval_of_contact α y m Q hQ _ _

/-! ## The affine-line form of PR #122 -/

/-- Node substitution for `Q(X, Y, R, Z)` at a node with values `(u₀, u₁)`:
`X ↦ C α + T`, `Y ↦ C u₀ + C u₁ · Z + T·(R + E)`, `R ↦ R`, `Z ↦ Z`; output variables
`0 = T`, `1 = E`, `2 = R`, `3 = Z`. -/
noncomputable def lineSubst (α u₀ u₁ : F) :
    MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 4) F :=
  MvPolynomial.aeval
    ![MvPolynomial.C α + MvPolynomial.X 0,
      MvPolynomial.C u₀ + MvPolynomial.C u₁ * MvPolynomial.X 3 +
        MvPolynomial.X 0 * (MvPolynomial.X 2 + MvPolynomial.X 1),
      MvPolynomial.X 2, MvPolynomial.X 3]

/-- Line contact constraint: every monomial of the substituted interpolant has
`T`-degree plus `E`-degree at least `m` (any `R`, `Z` degrees). -/
def LineContactConstraint (α u₀ u₁ : F) (m : ℕ) (Q : MvPolynomial (Fin 4) F) : Prop :=
  ∀ μ ∈ (lineSubst α u₀ u₁ Q).support, m ≤ μ 0 + μ 1

/-- `Q(X, P, P', γ)`. -/
noncomputable def specializeLine (Q : MvPolynomial (Fin 4) F) (P : F[X]) (γ : F) : F[X] :=
  MvPolynomial.aeval ![X, P, derivative P, C γ] Q

theorem X_pow_dvd_aeval_of_lineContact (α u₀ u₁ : F) (m : ℕ) (Q : MvPolynomial (Fin 4) F)
    (hQ : LineContactConstraint α u₀ u₁ m Q) (E' R Z : F[X]) :
    X ^ m ∣ MvPolynomial.aeval ![X, X * E', R, Z] (lineSubst α u₀ u₁ Q) := by
  set S := lineSubst α u₀ u₁ Q with hS
  rw [MvPolynomial.as_sum S, map_sum]
  refine Finset.dvd_sum fun μ hμ => ?_
  rw [MvPolynomial.aeval_monomial]
  have hμ' : m ≤ μ 0 + μ 1 := hQ μ hμ
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  refine Dvd.dvd.mul_left ?_ _
  refine Dvd.dvd.mul_right ?_ _
  refine Dvd.dvd.mul_right ?_ _
  rw [mul_pow, ← mul_assoc, ← pow_add]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ hμ') _

/-- **Line contact vanishing.**  If `Q(X, Y, R, Z)` satisfies the line contact constraint of
order `m` at a node `(α; u₀, u₁)`, then for every scalar `γ` and every polynomial `P` with
`P(α) = u₀ + γ u₁`, `(X - C α)^m` divides `Q(X, P, P', γ)`. -/
theorem contact_vanishing_line (α u₀ u₁ : F) (m : ℕ) (Q : MvPolynomial (Fin 4) F)
    (hQ : LineContactConstraint α u₀ u₁ m Q) (γ : F) (P : F[X])
    (hP : P.eval α = u₀ + γ * u₁) :
    (X - C α) ^ m ∣ specializeLine Q P γ := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_shift
  obtain ⟨U, hU⟩ := exists_taylor_tail α (u₀ + γ * u₁) P hP
  have hD : shift α (derivative P) = U + X * derivative U := by
    rw [shift_derivative, hU, derivative_add, derivative_C, zero_add, derivative_mul,
      derivative_X, one_mul]
  have hspec : shift α (specializeLine Q P γ) =
      MvPolynomial.aeval
        ![X + C α, C (u₀ + γ * u₁) + X * U, U + X * derivative U, C γ] Q := by
    unfold specializeLine
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    fin_cases i
    · show shift α X = X + C α
      rw [shift_apply, X_comp]
    · exact hU
    · exact hD
    · show shift α (C γ) = C γ
      rw [shift_apply, C_comp]
  rw [hspec]
  have hkey : MvPolynomial.aeval
        ![X + C α, C (u₀ + γ * u₁) + X * U, U + X * derivative U, C γ] Q =
      MvPolynomial.aeval ![X, X * (-derivative U), U + X * derivative U, C γ]
        (lineSubst α u₀ u₁ Q) := by
    unfold lineSubst
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp [C_add, C_mul] <;> ring
  rw [hkey]
  exact X_pow_dvd_aeval_of_lineContact α u₀ u₁ m Q hQ _ _ _

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.contact_vanishing
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.contact_vanishing_line
