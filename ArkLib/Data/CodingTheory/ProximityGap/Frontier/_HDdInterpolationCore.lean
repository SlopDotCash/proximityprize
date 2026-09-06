/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HDdContactVanishing
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HD1InterpolationCore

/-!
# HDd — the interpolation core of TR26-164 Proposition 3.13 at every order `d`

Generalizes `_HD1InterpolationCore.lean` from one hidden derivative to `d` hidden Hasse
derivatives, on top of `contact_vanishing_d`:

* `wdegD` — weighted degree with weights `(1, w, w−1, …, w−d)`;
* `natDegree_specializeD_lt` — weighted degree `< D` forces `deg Q(X, P, P^{[1]}, …, P^{[d]}) < D`
  for every `deg P ≤ w`;
* `specializeD_eq_zero_of_agreement` — order-`m` contact at every node of `T` with `D ≤ |T|·m`
  forces `Q(X, P, …) = 0`;
* `nodeMapD` with `nodeMapD_eq_zero_iff` — the node constraint as a linear map;
* `exists_interpolant_d` — **if the per-node constraint ranks on the interpolation space sum to
  less than its dimension**, a nonzero interpolant kills every degree-`≤ w` polynomial with at
  least `A` agreements, whenever `D ≤ A·m`.

The rank sum is exactly what `scripts/probes/hd_general_rank.py` computes exactly and
`scripts/probes/hd_fast_bound.py` / `hdinf_cap_search.py` soundly bound, at every `d`; the
theorem plus a probe run is the full interpolation step at that order.  The linear-algebra
kernel lemmas are inherited from the `d = 1` file (they are dimension-generic).
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Polynomial Module

variable {F : Type*} [Field F]

/-! ## Weighted degree and the specialization vector -/

/-- Weighted degree of `X^{μ₀} Y₀^{μ₁} Y₁^{μ₂} ⋯ Y_d^{μ_{d+1}}` with weights
`(1, w, w−1, …, w−d)`. -/
def wdegD (w d : ℕ) (μ : Fin (d + 2) →₀ ℕ) : ℕ :=
  μ 0 + ∑ i : Fin (d + 1), (w - (i : ℕ)) * μ i.succ

/-- The substitution vector `(X, P, P^{[1]}, …, P^{[d]})`. -/
noncomputable def specVec (d : ℕ) (P : F[X]) : Fin (d + 2) → F[X] :=
  Fin.cons X (Fin.cons P (fun j : Fin d => hasseDeriv ((j : ℕ) + 1) P))

theorem specializeD_eq_aeval_specVec (d : ℕ) (Q : MvPolynomial (Fin (d + 2)) F) (P : F[X]) :
    specializeD d Q P = MvPolynomial.aeval (specVec d P) Q := rfl

theorem natDegree_specVec_succ_le (d w : ℕ) (P : F[X]) (hP : P.natDegree ≤ w)
    (i : Fin (d + 1)) : (specVec d P i.succ).natDegree ≤ w - (i : ℕ) := by
  unfold specVec
  rw [Fin.cons_succ]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hP
  · rw [Fin.cons_succ]
    simp only [Fin.val_succ]
    exact (natDegree_hasseDeriv_le P ((j : ℕ) + 1)).trans
      (Nat.sub_le_sub_right hP ((j : ℕ) + 1))

theorem natDegree_monomial_specializeD_le (d w : ℕ) (P : F[X]) (hP : P.natDegree ≤ w)
    (c : F) (μ : Fin (d + 2) →₀ ℕ) :
    (MvPolynomial.aeval (specVec d P) (MvPolynomial.monomial μ c)).natDegree ≤ wdegD w d μ := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  calc (algebraMap F F[X] c * ∏ i, specVec d P i ^ μ i).natDegree
      ≤ (∏ i, specVec d P i ^ μ i).natDegree := by
        rw [Polynomial.algebraMap_eq]; exact natDegree_C_mul_le _ _
    _ ≤ ∑ i, (specVec d P i ^ μ i).natDegree := natDegree_prod_le _ _
    _ ≤ wdegD w d μ := by
        rw [Fin.sum_univ_succ]
        unfold wdegD
        refine Nat.add_le_add ?_ ?_
        · exact (natDegree_pow_le).trans (by
            simp only [specVec, Fin.cons_zero, natDegree_X]; omega)
        · refine Finset.sum_le_sum fun i _ => ?_
          exact (natDegree_pow_le).trans (by
            have := natDegree_specVec_succ_le d w P hP i
            calc μ i.succ * (specVec d P i.succ).natDegree
                ≤ μ i.succ * (w - (i : ℕ)) := Nat.mul_le_mul_left _ this
              _ = (w - (i : ℕ)) * μ i.succ := Nat.mul_comm _ _)

/-- The specialization of a weighted-degree-`< D` interpolant has degree `< D`. -/
theorem natDegree_specializeD_lt (d w D : ℕ) (hD : 0 < D) (Q : MvPolynomial (Fin (d + 2)) F)
    (hQ : ∀ μ ∈ Q.support, wdegD w d μ < D) (P : F[X]) (hP : P.natDegree ≤ w) :
    (specializeD d Q P).natDegree < D := by
  rw [specializeD_eq_aeval_specVec]
  rw [MvPolynomial.as_sum Q, map_sum]
  have : (∑ μ ∈ Q.support, MvPolynomial.aeval (specVec d P)
      (MvPolynomial.monomial μ (MvPolynomial.coeff μ Q))).natDegree ≤ D - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun μ hμ => ?_
    exact (natDegree_monomial_specializeD_le d w P hP _ μ).trans (by have := hQ μ hμ; omega)
  omega

/-! ## Vanishing from many contact nodes -/

/-- **Vanishing.**  If `Q` satisfies the order-`m`, order-`d` contact constraint at every node
`α ∈ T` with value `y α`, `P` (of degree `≤ w`) passes through all those nodes, and
`D ≤ |T|·m`, then `Q(X, P, P^{[1]}, …, P^{[d]}) = 0`. -/
theorem specializeD_eq_zero_of_agreement (d w D m : ℕ) (hD : 0 < D)
    (Q : MvPolynomial (Fin (d + 2)) F) (hQ : ∀ μ ∈ Q.support, wdegD w d μ < D)
    (T : Finset F) (y : F → F) (hcon : ∀ α ∈ T, ContactConstraintD d α (y α) m Q)
    (P : F[X]) (hP : P.natDegree ≤ w) (hagree : ∀ α ∈ T, P.eval α = y α)
    (hcount : D ≤ T.card * m) : specializeD d Q P = 0 := by
  by_contra hne
  have hdvd : (∏ α ∈ T, (X - C α) ^ m) ∣ specializeD d Q P := by
    refine Finset.prod_dvd_of_coprime ?_
      (fun α hα => contact_vanishing_d d α (y α) m Q (hcon α hα) P (hagree α hα))
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  have hdeg := natDegree_le_of_dvd hdvd hne
  rw [natDegree_prod_of_monic _ _ (fun α _ => (monic_X_sub_C α).pow m)] at hdeg
  simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const,
    smul_eq_mul] at hdeg
  have hlt := natDegree_specializeD_lt d w D hD Q hQ P hP
  exact absurd (lt_of_le_of_lt (hcount.trans hdeg) hlt) (lt_irrefl _)

/-! ## The node constraint as a linear map -/

/-- Low-order exponent vectors: `T`-degree plus `E`-degree below `m`. -/
abbrev LowIdxD (d m : ℕ) : Type := {μ : Fin (d + 2) →₀ ℕ // μ 0 + μ 1 < m}

/-- The linear functional `Q ↦ coeff μ (contactSubstD d α y Q)`. -/
noncomputable def contactCoeffD (d : ℕ) (α y : F) (μ : Fin (d + 2) →₀ ℕ) :
    MvPolynomial (Fin (d + 2)) F →ₗ[F] F where
  toFun Q := MvPolynomial.coeff μ (contactSubstD d α y Q)
  map_add' Q₁ Q₂ := by simp [map_add, MvPolynomial.coeff_add]
  map_smul' c Q := by simp [map_smul, MvPolynomial.coeff_smul]

/-- The node constraint map: all low-order coefficients of the substituted interpolant. -/
noncomputable def nodeMapD (d : ℕ) (α y : F) (m : ℕ) :
    MvPolynomial (Fin (d + 2)) F →ₗ[F] (LowIdxD d m → F) :=
  LinearMap.pi fun μ => contactCoeffD d α y μ.1

theorem nodeMapD_eq_zero_iff (d : ℕ) (α y : F) (m : ℕ) (Q : MvPolynomial (Fin (d + 2)) F) :
    nodeMapD d α y m Q = 0 ↔ ContactConstraintD d α y m Q := by
  constructor
  · intro h μ hμ
    by_contra hlt
    have hlt' : μ 0 + μ 1 < m := not_le.mp hlt
    have := congrFun h ⟨μ, hlt'⟩
    simp only [nodeMapD, LinearMap.pi_apply, contactCoeffD, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply] at this
    exact (MvPolynomial.mem_support_iff.mp hμ) this
  · intro h
    funext μ
    simp only [nodeMapD, LinearMap.pi_apply, contactCoeffD, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply]
    by_contra hne
    have hmem : μ.1 ∈ (contactSubstD d α y Q).support := MvPolynomial.mem_support_iff.mpr hne
    exact absurd (h μ.1 hmem) (not_le.mpr μ.2)

/-! ## The interpolation theorem -/

open scoped Classical in
/-- **Interpolation (TR26-164 Proposition 3.13, every order `d`, counting left explicit).**
Let `Qs` be a finite-dimensional space of interpolants of weighted degree `< D`, `S` a finite
set of nodes with values `y`, and suppose the ranks of the node maps on `Qs` sum to less than
`dim Qs`.  Then some nonzero `Q ∈ Qs` satisfies `Q(X, P, P^{[1]}, …, P^{[d]}) = 0` for every
`P` of degree `≤ w` agreeing with `y` on at least `A` nodes, provided `D ≤ A·m`. -/
theorem exists_interpolant_d (d w D m A : ℕ) (hD : 0 < D) (hA : D ≤ A * m)
    (Qs : Submodule F (MvPolynomial (Fin (d + 2)) F)) [FiniteDimensional F Qs]
    (hQs : ∀ Q ∈ Qs, ∀ μ ∈ Q.support, wdegD w d μ < D)
    (S : Finset F) (y : F → F)
    (hrank : ∑ α ∈ S, finrank F (LinearMap.range ((nodeMapD d α (y α) m).domRestrict Qs)) <
      finrank F Qs) :
    ∃ Q ∈ Qs, Q ≠ 0 ∧ ∀ P : F[X], P.natDegree ≤ w →
      A ≤ (S.filter fun α => P.eval α = y α).card → specializeD d Q P = 0 := by
  classical
  obtain ⟨q, hq0, hq⟩ := exists_ne_zero_mem_iInf_ker S
    (fun α => (nodeMapD d α (y α) m).domRestrict Qs) hrank
  refine ⟨q, q.2, fun h => hq0 (Subtype.ext h), fun P hP hagree => ?_⟩
  refine specializeD_eq_zero_of_agreement d w D m hD q (hQs q q.2)
    (S.filter fun α => P.eval α = y α) y ?_ P hP ?_ ?_
  · intro α hα
    have hαS : α ∈ S := (Finset.mem_filter.mp hα).1
    exact (nodeMapD_eq_zero_iff d α (y α) m q).mp (hq α hαS)
  · intro α hα
    exact (Finset.mem_filter.mp hα).2
  · exact hA.trans (Nat.mul_le_mul_right m hagree)

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.exists_interpolant_d
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.specializeD_eq_zero_of_agreement
