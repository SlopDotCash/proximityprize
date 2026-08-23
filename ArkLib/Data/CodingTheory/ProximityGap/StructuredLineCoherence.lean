/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The structured-line coherence forcing: the line-list IS the coherent core (generated case)

Issue #389, the unification of the two attack routes. The line-list reduction
(`LineListReduction.lean`) bounds the bad scalars by the affine-line list size `Λ`. This file
proves that for a **structured** direction-row setup — `u₀` a polynomial evaluation of degree
`≤ k+m`, `u₁ = xᵏ` — the codewords contributing to `Λ` are **forced** to be coherent:

> **`structured_line_forces_identity`** — if a degree-`< k` codeword `Pc` agrees with
> `Q.eval + γ·xᵏ` (`deg Q ≤ k+m`) on `≥ k+m+1` domain points, then the polynomial identity
> `Pc = Q + C γ · Xᵏ` holds *exactly*.

The mechanism is a single degree count: `Pc − Q − C γ·Xᵏ` has degree `≤ k+m` and vanishes on
`≥ k+m+1` distinct points, hence is the zero polynomial. Two corollaries extract the structure:

> **`structured_line_forces_coeff_zero`** — the middle coefficients vanish:
> `Q.coeff j = 0` for `k < j ≤ k+m` (the **coherence** condition), and
> **`structured_line_forces_scalar`** — the scalar is pinned: `γ = −Q.coeff k`.

So in the generated case the affine-line list `Λ` is exactly the set of coherent cores with
their pinned scalars — the same object the failure-side second-moment machine
(`DeepBandSecondMoment.lean`) counts. The positive (line-list) and failure (second-moment)
routes are therefore two views of one object, and the open residual is confined to the
*unstructured* `u₀` regime. This is the machine-checked converse of `coherent_explains_line`.

## References

* Issue #389; `LineListReduction.lean`, `DeepBandCoherence.lean` (`coherent_explains_line`),
  `JohnsonSplitSupply.lean` (the degree/roots pattern).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The structured-line identity forcing.** A degree-`< k` codeword that agrees with the
structured line word `Q.eval + γ·xᵏ` (`deg Q ≤ k+m`) on at least `k+m+1` domain points must
equal it as a polynomial. -/
theorem structured_line_forces_identity (dom : Fin n ↪ F) {k m : ℕ}
    {Pc Q : F[X]} (hPc : Pc.natDegree < k) (hQ : Q.natDegree ≤ k + m)
    {γ : F} {T : Finset (Fin n)} (hT : k + m + 1 ≤ T.card)
    (hagree : ∀ i ∈ T, Pc.eval (dom i) = Q.eval (dom i) + γ * (dom i) ^ k) :
    Pc = Q + Polynomial.C γ * Polynomial.X ^ k := by
  classical
  set P : F[X] := Pc - (Q + Polynomial.C γ * Polynomial.X ^ k) with hP
  -- it suffices to show P = 0
  suffices hP0 : P = 0 by
    have := sub_eq_zero.mp (by rw [← hP]; exact hP0)
    exact this
  by_contra hPne
  -- degree of P is ≤ k+m
  have hdeg : P.natDegree ≤ k + m := by
    have h1 : (Polynomial.C γ * Polynomial.X ^ k).natDegree ≤ k := by
      calc (Polynomial.C γ * Polynomial.X ^ k).natDegree
          ≤ (Polynomial.C γ).natDegree + (Polynomial.X ^ k).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 0 + k := by
            gcongr
            · exact (Polynomial.natDegree_C γ).le
            · rw [Polynomial.natDegree_X_pow]
        _ = k := by ring
    have h2 : (Q + Polynomial.C γ * Polynomial.X ^ k).natDegree ≤ k + m := by
      calc (Q + Polynomial.C γ * Polynomial.X ^ k).natDegree
          ≤ max Q.natDegree (Polynomial.C γ * Polynomial.X ^ k).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ k + m := by omega
    calc P.natDegree ≤ max Pc.natDegree (Q + Polynomial.C γ * Polynomial.X ^ k).natDegree := by
          rw [hP]; exact Polynomial.natDegree_sub_le _ _
      _ ≤ k + m := by omega
  -- P vanishes on the injective image of T, which has ≥ k+m+1 points
  have hroots : (T.image (fun i => dom i)) ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    show P.eval (dom i) = 0
    rw [hP, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hagree i hiT]
    ring
  have hcardT : (T.image (fun i => dom i)).card = T.card :=
    Finset.card_image_of_injective _ dom.injective
  have hle : T.card ≤ P.natDegree := by
    calc T.card = (T.image (fun i => dom i)).card := hcardT.symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' _
  omega

/-- **Coherence forcing**: the middle coefficients of the structured row vanish. -/
theorem structured_line_forces_coeff_zero (dom : Fin n ↪ F) {k m : ℕ}
    {Pc Q : F[X]} (hPc : Pc.natDegree < k) (hQ : Q.natDegree ≤ k + m)
    {γ : F} {T : Finset (Fin n)} (hT : k + m + 1 ≤ T.card)
    (hagree : ∀ i ∈ T, Pc.eval (dom i) = Q.eval (dom i) + γ * (dom i) ^ k)
    {j : ℕ} (hj1 : k < j) (hj2 : j ≤ k + m) :
    Q.coeff j = 0 := by
  have hid := structured_line_forces_identity dom hPc hQ hT hagree
  have hPcj : Pc.coeff j = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hxk : (Polynomial.C γ * Polynomial.X ^ k).coeff j = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have := congrArg (fun p => Polynomial.coeff p j) hid
  simp only [Polynomial.coeff_add, hPcj, hxk, add_zero] at this
  exact this.symm

/-- **Scalar pinning**: the line scalar is determined by the degree-`k` coefficient. -/
theorem structured_line_forces_scalar (dom : Fin n ↪ F) {k m : ℕ}
    {Pc Q : F[X]} (hPc : Pc.natDegree < k) (hQ : Q.natDegree ≤ k + m)
    {γ : F} {T : Finset (Fin n)} (hT : k + m + 1 ≤ T.card)
    (hagree : ∀ i ∈ T, Pc.eval (dom i) = Q.eval (dom i) + γ * (dom i) ^ k) :
    γ = -Q.coeff k := by
  have hid := structured_line_forces_identity dom hPc hQ hT hagree
  have hPck : Pc.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hPc
  have hxk : (Polynomial.C γ * Polynomial.X ^ k).coeff k = γ := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hcoeff := congrArg (fun p => Polynomial.coeff p k) hid
  simp only [Polynomial.coeff_add, hPck, hxk] at hcoeff
  linear_combination -hcoeff

/-! ## Source audit -/

#print axioms structured_line_forces_identity
#print axioms structured_line_forces_coeff_zero
#print axioms structured_line_forces_scalar

end ProximityGap.Ownership
