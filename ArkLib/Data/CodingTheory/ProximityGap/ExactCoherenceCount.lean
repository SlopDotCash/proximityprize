/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureUnconditional

/-!
# Exact coherence counts (#389): surjectivity by interpolation

The second-moment programme needs EXACT fiber counts, not just the one-sided
multi-kernel bound.  This file builds the engine:

* `coeffFamily` — the standard coefficient-transparent stack family
  `c ↦ Σ_j c_j·X^j`, extracted as a definition with its coefficient,
  degree, subtraction, and reconstruction laws.
* `card_zeroFiber_eq_of_surjective` — a SURJECTIVE subtraction-linear map
  `F^M → F^r` has all fibers of size exactly `q^{M−r}`.
* `coreInterp_of_degree_lt` — a polynomial of degree `< |T|` is its own core
  interpolant.
* `coherence_surjective` / `card_coherent_eq` — per-core surjectivity is free
  (`Q := Σ t_j·X^{k+j}` hits any prescribed coherence coordinates), hence
  **`#{c : T coherent for coeffFamily c} · q^m = q^M` EXACTLY** — the
  witness-mass inequality upgraded to an equality.

The merge-interpolation pair surjectivity (exact same-value pair counts)
builds on this next.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The coefficient-transparent stack family. -/
noncomputable def coeffFamily (M : ℕ) (c : Fin M → F) : F[X] :=
  ∑ j : Fin M, C (c j) * X ^ (j : ℕ)

omit [Fintype F] [NeZero n] in
theorem coeffFamily_coeff_nat (M : ℕ) (c : Fin M → F) (jj : ℕ) :
    (coeffFamily M c).coeff jj = if h : jj < M then c ⟨jj, h⟩ else 0 := by
  rw [coeffFamily, Polynomial.finset_sum_coeff]
  by_cases h : jj < M
  · rw [dif_pos h]
    calc ∑ i : Fin M, (C (c i) * X ^ (i : ℕ)).coeff jj
        = ∑ i : Fin M, (if i = (⟨jj, h⟩ : Fin M) then c i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coeff_C_mul, coeff_X_pow]
          by_cases h2 : i = (⟨jj, h⟩ : Fin M)
          · subst h2
            simp
          · rw [if_neg (by
              intro hji
              exact h2 (Fin.ext (by simpa using hji.symm))), if_neg h2,
              mul_zero]
      _ = c ⟨jj, h⟩ := by
          rw [Finset.sum_ite_eq' Finset.univ (⟨jj, h⟩ : Fin M)
            (fun i => c i)]
          simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_C_mul, coeff_X_pow, if_neg (by
      intro hji
      exact h (hji ▸ i.2)), mul_zero]

omit [Fintype F] [NeZero n] in
theorem coeffFamily_coeff (M : ℕ) (c : Fin M → F) (j : Fin M) :
    (coeffFamily M c).coeff (j : ℕ) = c j := by
  rw [coeffFamily_coeff_nat, dif_pos j.2]

omit [Fintype F] [NeZero n] in
theorem coeffFamily_natDegree_le (M : ℕ) (c : Fin M → F) :
    (coeffFamily M c).natDegree ≤ M - 1 := by
  rw [coeffFamily]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  calc (C (c j) * X ^ (j : ℕ)).natDegree
      ≤ (C (c j)).natDegree + (X ^ (j : ℕ) : F[X]).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ M - 1 := by
        rw [natDegree_C, natDegree_X_pow]
        have := j.2
        omega

omit [Fintype F] [NeZero n] in
theorem coeffFamily_sub (M : ℕ) (x y : Fin M → F) :
    coeffFamily M (x - y) = coeffFamily M x - coeffFamily M y := by
  rw [coeffFamily, coeffFamily, coeffFamily, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C (x j - y j) * X ^ (j : ℕ) = _
  rw [C_sub]
  ring

omit [Fintype F] [NeZero n] in
/-- The family reconstructs every polynomial of degree `< M`. -/
theorem coeffFamily_reconstruct (M : ℕ) {Q : F[X]} (hdeg : Q.natDegree < M) :
    coeffFamily M (fun j => Q.coeff (j : ℕ)) = Q := by
  ext jj
  rw [coeffFamily_coeff_nat]
  by_cases h : jj < M
  · rw [dif_pos h]
  · rw [dif_neg h]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

open Classical in
/-- **Exact fiber count**: a surjective subtraction-linear map `F^M → F^r`
has zero fiber of size exactly `q^{M−r}` (multiplicative form). -/
theorem card_zeroFiber_eq_of_surjective {M r : ℕ}
    (φ : (Fin M → F) → (Fin r → F))
    (hsub : ∀ x y, φ (x - y) = φ x - φ y)
    (hsurj : Function.Surjective φ) :
    (Finset.univ.filter
        (fun c : Fin M → F => φ c = 0)).card * (Fintype.card F) ^ r
      = (Fintype.card F) ^ M := by
  have hfib : ∀ v : Fin r → F, (Finset.univ.filter
      (fun c : Fin M → F => φ c = v)).card
      = (Finset.univ.filter (fun c : Fin M → F => φ c = 0)).card := by
    intro v
    obtain ⟨δv, hδv⟩ := hsurj v
    refine Finset.card_bij' (fun c _ => c - δv) (fun c _ => c + δv)
      ?_ ?_ ?_ ?_
    · intro c hc
      have hcval := (Finset.mem_filter.mp hc).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hsub, hcval, hδv, sub_self]
    · intro c hc
      have hcval := (Finset.mem_filter.mp hc).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := hsub (c + δv) δv
      rw [add_sub_cancel_right] at h
      have h2 : φ (c + δv) - φ δv = φ c := h.symm
      rw [hcval, hδv] at h2
      have h3 : φ (c + δv) - v = 0 := h2
      have h4 : φ (c + δv) = v := by
        have := sub_eq_zero.mp h3
        exact this
      exact h4
    · intro c _
      simp
    · intro c _
      simp
  have hpart : (Fintype.card F) ^ M
      = ∑ v : Fin r → F, (Finset.univ.filter
        (fun c : Fin M → F => φ c = v)).card := by
    calc (Fintype.card F) ^ M
        = Fintype.card (Fin M → F) := by
          rw [Fintype.card_fun, Fintype.card_fin]
      _ = (Finset.univ : Finset (Fin M → F)).card := Finset.card_univ.symm
      _ = ∑ v ∈ Finset.univ, (Finset.univ.filter
          (fun c : Fin M → F => φ c = v)).card :=
          Finset.card_eq_sum_card_fiberwise fun c _ => Finset.mem_univ (φ c)
  rw [Finset.sum_congr rfl (fun v _ => hfib v), Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    smul_eq_mul] at hpart
  rw [mul_comm] at hpart
  exact hpart.symm

open Classical in
/-- A polynomial of degree `< |T|` is its own core interpolant. -/
theorem coreInterp_of_degree_lt (dom : Fin n ↪ F) {T : Finset (Fin n)}
    {Q : F[X]} (hdeg : Q.degree < (T.card : ℕ)) :
    coreInterp dom T Q = Q := by
  have hvs : Set.InjOn dom T := fun a _ b _ h => dom.injective h
  rw [coreInterp]
  exact (Lagrange.eq_interpolate hvs hdeg).symm

open Classical in
/-- **The exact per-core coherence count**: surjectivity is free, so the
coherent fraction is exactly `q^{−m}`. -/
theorem card_coherent_eq (dom : Fin n ↪ F) {k m : ℕ} {T : Finset (Fin n)}
    (hT : T.card = k + m + 1) {M : ℕ} (hM : k + m + 1 ≤ M) :
    (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (coeffFamily M c))).card
      * (Fintype.card F) ^ m = (Fintype.card F) ^ M := by
  set φ : (Fin M → F) → (Fin m → F) :=
    fun c => fun j => (coreInterp dom T (coeffFamily M c)).coeff (k + 1 + j)
    with hφ
  have hsub : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y
    funext j
    show (coreInterp dom T (coeffFamily M (x - y))).coeff (k + 1 + (j : ℕ))
      = _ - _
    rw [coeffFamily_sub]
    have hI : coreInterp dom T (coeffFamily M x - coeffFamily M y)
        = coreInterp dom T (coeffFamily M x)
          - coreInterp dom T (coeffFamily M y) := by
      rw [coreInterp, coreInterp, coreInterp]
      have hvals : (fun i => (coeffFamily M x - coeffFamily M y).eval (dom i))
          = (fun i => (coeffFamily M x).eval (dom i))
            - (fun i => (coeffFamily M y).eval (dom i)) := by
        funext i
        simp [eval_sub]
      rw [hvals, map_sub]
    rw [hI, coeff_sub]
  have hsurj : Function.Surjective φ := by
    intro t
    set Q : F[X] := ∑ j : Fin m, C (t j) * X ^ (k + 1 + (j : ℕ)) with hQ
    have hQdeg : Q.natDegree ≤ k + m := by
      rw [hQ]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      calc (C (t j) * X ^ (k + 1 + (j : ℕ))).natDegree
          ≤ (C (t j)).natDegree
              + (X ^ (k + 1 + (j : ℕ)) : F[X]).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ k + m := by
            rw [natDegree_C, natDegree_X_pow]
            have := j.2
            omega
    have hQdeg' : Q.natDegree < M := by omega
    refine ⟨fun j => Q.coeff (j : ℕ), ?_⟩
    funext j
    show (coreInterp dom T
      (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff (k + 1 + (j : ℕ)) = t j
    rw [coeffFamily_reconstruct M hQdeg']
    rw [coreInterp_of_degree_lt dom (by
      rw [hT]
      calc Q.degree ≤ (Q.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ < ((k + m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast by omega)]
    -- the coefficient of the shifted monomial sum
    rw [hQ, Polynomial.finset_sum_coeff]
    calc ∑ i : Fin m, (C (t i) * X ^ (k + 1 + (i : ℕ))).coeff (k + 1 + (j : ℕ))
        = ∑ i : Fin m, (if i = j then t i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coeff_C_mul, coeff_X_pow]
          by_cases h2 : i = j
          · subst h2
            simp
          · rw [if_neg (by
              intro hji
              exact h2 (Fin.ext (by omega))), if_neg h2, mul_zero]
      _ = t j := by
          rw [Finset.sum_ite_eq' Finset.univ j (fun i => t i)]
          simp
  have h := card_zeroFiber_eq_of_surjective φ hsub hsurj
  have hfeq : (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (coeffFamily M c)))
      = (Finset.univ.filter (fun c : Fin M → F => φ c = 0)) := by
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · intro hcoh
      funext j
      exact hcoh j
    · intro hzero j
      exact congrFun hzero j
  rw [hfeq]
  exact h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.card_zeroFiber_eq_of_surjective
#print axioms ProximityGap.Ownership.card_coherent_eq
