/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HD1ContactVanishing
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# HD1 — the interpolation core of TR26-164 Proposition 3.13 (order `d = 1`)

Everything in the hidden-derivative list-decoding argument except the *counting* of
independent node constraints is proved here, Mathlib-only:

* `natDegree_specialize_lt` — if every monomial `X^a Y₀^{b₀} Y₁^{b₁}` of `Q` has weighted
  degree `a + w b₀ + (w−1) b₁ < D`, then `Q(X, P, P')` has degree `< D` for every `deg P ≤ w`;
* `specialize_eq_zero_of_agreement` — if `Q` meets the order-`m` contact constraint at every
  node of a set `T` on which `P` agrees with the received word and `D ≤ |T|·m`, then
  `Q(X, P, P') = 0` (coprime powers `(X − α)^m`, `α ∈ T`, all divide it);
* `nodeMap` — the node constraint as a linear map whose kernel is the contact constraint;
* `finrank_le_finrank_iInf_ker_add_sum` — codimension of a finite intersection of kernels is
  at most the sum of the ranks;
* `exists_interpolant` — **if the sum over nodes of the ranks of the node maps on the
  interpolation space is smaller than its dimension**, a nonzero interpolant exists that kills
  every polynomial of degree `≤ w` with at least `A` agreements, whenever `D ≤ A·m`.

The rank inequality is exactly what `scripts/probes/hd1_interpolation_threshold.py` and
`scripts/probes/hd_general_rank.py` compute (exactly), so the theorem plus the probe is the full
interpolation step; the list/seed count is a separate ledger.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Polynomial Module

variable {F : Type*} [Field F]

/-! ## Weighted degree -/

/-- Weighted degree of the exponent vector of `X^a Y₀^{b₀} Y₁^{b₁}` with weights
`(1, w, w−1)`. -/
def wdeg (w : ℕ) (μ : Fin 3 →₀ ℕ) : ℕ := μ 0 + w * μ 1 + (w - 1) * μ 2

theorem natDegree_monomial_specialize_le (w : ℕ) (P : F[X]) (hP : P.natDegree ≤ w)
    (c : F) (μ : Fin 3 →₀ ℕ) :
    (MvPolynomial.aeval ![X, P, derivative P] (MvPolynomial.monomial μ c)).natDegree ≤
      wdeg w μ := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Polynomial.algebraMap_eq]
  have h1 : (X ^ μ 0 : F[X]).natDegree ≤ μ 0 := natDegree_X_pow_le _
  have h2 : (P ^ μ 1).natDegree ≤ μ 1 * w :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ hP)
  have h3 : (derivative P ^ μ 2).natDegree ≤ μ 2 * (w - 1) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _
      ((natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)))
  calc (C c * (X ^ μ 0 * P ^ μ 1 * derivative P ^ μ 2)).natDegree
      ≤ (X ^ μ 0 * P ^ μ 1 * derivative P ^ μ 2).natDegree := natDegree_C_mul_le _ _
    _ ≤ (X ^ μ 0 * P ^ μ 1).natDegree + (derivative P ^ μ 2).natDegree := natDegree_mul_le
    _ ≤ ((X ^ μ 0).natDegree + (P ^ μ 1).natDegree) + (derivative P ^ μ 2).natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
    _ ≤ (μ 0 + μ 1 * w) + μ 2 * (w - 1) := by omega
    _ = wdeg w μ := by unfold wdeg; ring

/-- The specialization of a weighted-degree-`< D` interpolant has degree `< D`. -/
theorem natDegree_specialize_lt (w D : ℕ) (hD : 0 < D) (Q : MvPolynomial (Fin 3) F)
    (hQ : ∀ μ ∈ Q.support, wdeg w μ < D) (P : F[X]) (hP : P.natDegree ≤ w) :
    (specialize Q P).natDegree < D := by
  unfold specialize
  rw [MvPolynomial.as_sum Q, map_sum]
  have : (∑ μ ∈ Q.support, MvPolynomial.aeval ![X, P, derivative P]
      (MvPolynomial.monomial μ (MvPolynomial.coeff μ Q))).natDegree ≤ D - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun μ hμ => ?_
    exact (natDegree_monomial_specialize_le w P hP _ μ).trans (by have := hQ μ hμ; omega)
  omega

/-! ## Vanishing from many contact nodes -/

/-- **Vanishing.**  If `Q` satisfies the contact constraint of order `m` at every node `α ∈ T`
with value `y α`, `P` (of degree `≤ w`) passes through all those nodes, and `D ≤ |T|·m`, then
`Q(X, P, P') = 0`. -/
theorem specialize_eq_zero_of_agreement (w D m : ℕ) (hD : 0 < D) (Q : MvPolynomial (Fin 3) F)
    (hQ : ∀ μ ∈ Q.support, wdeg w μ < D) (T : Finset F) (y : F → F)
    (hcon : ∀ α ∈ T, ContactConstraint α (y α) m Q) (P : F[X]) (hP : P.natDegree ≤ w)
    (hagree : ∀ α ∈ T, P.eval α = y α) (hcount : D ≤ T.card * m) :
    specialize Q P = 0 := by
  by_contra hne
  have hdvd : (∏ α ∈ T, (X - C α) ^ m) ∣ specialize Q P := by
    refine Finset.prod_dvd_of_coprime ?_
      (fun α hα => contact_vanishing α (y α) m Q (hcon α hα) P (hagree α hα))
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  have hdeg := natDegree_le_of_dvd hdvd hne
  rw [natDegree_prod_of_monic _ _ (fun α _ => (monic_X_sub_C α).pow m)] at hdeg
  simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const,
    smul_eq_mul] at hdeg
  have hlt := natDegree_specialize_lt w D hD Q hQ P hP
  exact absurd (lt_of_le_of_lt (hcount.trans hdeg) hlt) (lt_irrefl _)

/-! ## The node constraint as a linear map -/

/-- Low-order exponent vectors: `T`-degree plus `E`-degree below `m`. -/
abbrev LowIdx (m : ℕ) : Type := {μ : Fin 3 →₀ ℕ // μ 0 + μ 1 < m}

/-- The linear functional `Q ↦ coeff μ (contactSubst α y Q)`. -/
noncomputable def contactCoeff (α y : F) (μ : Fin 3 →₀ ℕ) :
    MvPolynomial (Fin 3) F →ₗ[F] F where
  toFun Q := MvPolynomial.coeff μ (contactSubst α y Q)
  map_add' Q₁ Q₂ := by simp [map_add, MvPolynomial.coeff_add]
  map_smul' c Q := by simp [map_smul, MvPolynomial.coeff_smul]

/-- The node constraint map: all low-order coefficients of the substituted interpolant. -/
noncomputable def nodeMap (α y : F) (m : ℕ) :
    MvPolynomial (Fin 3) F →ₗ[F] (LowIdx m → F) :=
  LinearMap.pi fun μ => contactCoeff α y μ.1

theorem nodeMap_eq_zero_iff (α y : F) (m : ℕ) (Q : MvPolynomial (Fin 3) F) :
    nodeMap α y m Q = 0 ↔ ContactConstraint α y m Q := by
  constructor
  · intro h μ hμ
    by_contra hlt
    have hlt' : μ 0 + μ 1 < m := not_le.mp hlt
    have := congrFun h ⟨μ, hlt'⟩
    simp only [nodeMap, LinearMap.pi_apply, contactCoeff, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply] at this
    exact (MvPolynomial.mem_support_iff.mp hμ) this
  · intro h
    funext μ
    simp only [nodeMap, LinearMap.pi_apply, contactCoeff, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply]
    by_contra hne
    have hmem : μ.1 ∈ (contactSubst α y Q).support := MvPolynomial.mem_support_iff.mpr hne
    exact absurd (h μ.1 hmem) (not_le.mpr μ.2)

/-! ## Linear algebra: codimension of an intersection of kernels -/

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem finrank_le_finrank_ker_add_finrank_range {W : Type*} [AddCommGroup W] [Module F W]
    (Φ : V →ₗ[F] W) :
    finrank F V ≤ finrank F (LinearMap.ker Φ) + finrank F (LinearMap.range Φ) := by
  have := LinearMap.finrank_range_add_finrank_ker Φ
  omega

/-- Codimension subadditivity:
`finrank V ≤ finrank (⨅ i ∈ S, ker Φᵢ) + Σ_{i ∈ S} rank Φᵢ`. -/
theorem finrank_le_finrank_iInf_ker_add_sum {ι W : Type*} [AddCommGroup W] [Module F W]
    [DecidableEq ι] (S : Finset ι) (Φ : ι → V →ₗ[F] W) :
    finrank F V ≤ finrank F ↥(⨅ i ∈ S, LinearMap.ker (Φ i)) +
      ∑ i ∈ S, finrank F (LinearMap.range (Φ i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h : (⨅ i ∈ (∅ : Finset ι), LinearMap.ker (Φ i)) = ⊤ := by simp
    rw [h]
    simp
  | insert a S ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha]
    set K := ⨅ i ∈ S, LinearMap.ker (Φ i) with hK
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (Φ a)) K
    have h2 : finrank F ↥(LinearMap.ker (Φ a) ⊔ K) ≤ finrank F V := Submodule.finrank_le _
    have h3 := finrank_le_finrank_ker_add_finrank_range (Φ a)
    omega

/-- A nonzero vector in a finite intersection of kernels exists once the ranks sum to less
than the dimension. -/
theorem exists_ne_zero_mem_iInf_ker {ι W : Type*} [AddCommGroup W] [Module F W]
    [DecidableEq ι] (S : Finset ι) (Φ : ι → V →ₗ[F] W)
    (h : ∑ i ∈ S, finrank F (LinearMap.range (Φ i)) < finrank F V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i ∈ S, Φ i v = 0 := by
  classical
  have hle := finrank_le_finrank_iInf_ker_add_sum S Φ
  have hpos : (⨅ i ∈ S, LinearMap.ker (Φ i)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hle
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hpos
  refine ⟨v, hv0, fun i hi => ?_⟩
  have := (Submodule.mem_iInf _).mp hv i
  have := (Submodule.mem_iInf _).mp this hi
  exact LinearMap.mem_ker.mp this

end LinearAlgebra

/-! ## The interpolation theorem -/

open scoped Classical in
/-- **Interpolation (TR26-164 Proposition 3.13, `d = 1`, counting left explicit).**
Let `Qs` be a finite-dimensional space of interpolants of weighted degree `< D`, `S` a finite set
of nodes with values `y`, and suppose the ranks of the node maps on `Qs` sum to less than
`dim Qs`.  Then some nonzero `Q ∈ Qs` satisfies `Q(X, P, P') = 0` for every `P` of degree `≤ w`
agreeing with `y` on at least `A` nodes, provided `D ≤ A·m`. -/
theorem exists_interpolant (w D m A : ℕ) (hD : 0 < D) (hA : D ≤ A * m)
    (Qs : Submodule F (MvPolynomial (Fin 3) F)) [FiniteDimensional F Qs]
    (hQs : ∀ Q ∈ Qs, ∀ μ ∈ Q.support, wdeg w μ < D)
    (S : Finset F) (y : F → F)
    (hrank : ∑ α ∈ S, finrank F (LinearMap.range ((nodeMap α (y α) m).domRestrict Qs)) <
      finrank F Qs) :
    ∃ Q ∈ Qs, Q ≠ 0 ∧ ∀ P : F[X], P.natDegree ≤ w →
      A ≤ (S.filter fun α => P.eval α = y α).card → specialize Q P = 0 := by
  classical
  obtain ⟨q, hq0, hq⟩ := exists_ne_zero_mem_iInf_ker S
    (fun α => (nodeMap α (y α) m).domRestrict Qs) hrank
  refine ⟨q, q.2, fun h => hq0 (Subtype.ext h), fun P hP hagree => ?_⟩
  refine specialize_eq_zero_of_agreement w D m hD q (hQs q q.2)
    (S.filter fun α => P.eval α = y α) y ?_ P hP ?_ ?_
  · intro α hα
    have hαS : α ∈ S := (Finset.mem_filter.mp hα).1
    exact (nodeMap_eq_zero_iff α (y α) m q).mp (hq α hαS)
  · intro α hα
    exact (Finset.mem_filter.mp hα).2
  · exact hA.trans (Nat.mul_le_mul_right m hagree)

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.exists_interpolant
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.specialize_eq_zero_of_agreement
