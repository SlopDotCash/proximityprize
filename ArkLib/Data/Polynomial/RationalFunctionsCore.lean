/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Definitions and Theorems about Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

## Main Definitions

-/

set_option linter.style.longFile 3100

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [Field F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

section FieldIrreducibility

variable {F : Type} [Field F]

private lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  letI : Invertible a := invertibleOfNonzero ha
  let e : K[X] ≃ₐ[K] K[X] := Polynomial.algEquivCMulXAddC a 0
  have hp : e p = p.comp (Polynomial.C a * Polynomial.X) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← hp]
  exact MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p)

private lemma irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0)
    (hH : Irreducible H) :
    Irreducible (H.map (univPolyHom (F := F))) := by
  have hprim : H.IsPrimitive := Irreducible.isPrimitive hH hdeg
  simpa [ToRatFunc.univPolyHom] using
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F) hprim).mp hH

/-- Corrected irreducibility statement for `H_tilde`: the paper assumes positive `Y`-degree.
Without this hypothesis, a constant irreducible in `F[Z][Y]` can become a unit in `F(Z)[T]`. -/
lemma irreducibleHTildeOfIrreducible_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde H) := by
  classical
  let d : ℕ := H.natDegree
  let a : RatFunc F := univPolyHom (F := F) H.leadingCoeff
  let W : Polynomial (RatFunc F) := Polynomial.C a
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  have hlead_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hlead_ne (univPolyHom_injective (by simpa [a] using ha))
  have hmap_irreducible : Irreducible (H.map (univPolyHom (F := F))) :=
    irreducible_map_univPolyHom_of_irreducible (Nat.ne_of_gt hdeg) hH
  have hsub :
      Polynomial.X / W = Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)) := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := rfl
      _ = Polynomial.X * Polynomial.C a⁻¹ := Polynomial.div_C
      _ = Polynomial.C a⁻¹ * Polynomial.X := by rw [mul_comm]
  have hcomp_irreducible :
      Irreducible
        ((H.map (univPolyHom (F := F))).comp
          (Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)))) := by
    exact (irreducible_comp_C_mul_X_iff (a := a⁻¹) (inv_ne_zero ha_ne)
      (H.map (univPolyHom (F := F)))).mpr hmap_irreducible
  have heval :
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := univPolyHom (F := F))
        (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
        (x := Polynomial.X / W)).symm
  have heval_irreducible :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
          H) := by
    rw [heval, hsub]
    exact hcomp_irreducible
  have hunitW : IsUnit (W ^ (d - 1)) := by
    exact (isUnit_C.mpr (Ne.isUnit ha_ne)).pow (d - 1)
  rcases hunitW with ⟨u, hu⟩
  have htilde :
      H_tilde H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible

end FieldIrreducibility

/-- The monisized version `H_tilde` is irreducible if the original polynomial `H` is irreducible
and has positive degree in `Y`, as assumed in Appendix A.1 of [BCIKS20]. -/
lemma irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (H_tilde H) :=
  irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg

abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw
    [
      ← Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH

/-- The function field `𝕃 ` is indeed a field when the generator of the ideal we quotient by is
irreducible and has positive degree in `Y`. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ← Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible hHdeg h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i

lemma H_tilde'_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (H_tilde' H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

lemma evalEval_H_tilde' (H : F[X][Y]) (hH : 0 < H.natDegree) (z y : F) :
    Polynomial.evalEval z ((H.coeff H.natDegree).eval z * y) (H_tilde' H) =
      ((H.coeff H.natDegree).eval z) ^ (H.natDegree - 1) * Polynomial.evalEval z y H := by
  classical
  set d := H.natDegree with hd
  set W : F[X] := H.coeff d with hW
  set w : F := W.eval z with hw
  have hdne : d ≠ 0 := by omega
  have hwd : Polynomial.eval z (H.coeff d) = w := by rw [← hW, hw]
  have hEvalH : Polynomial.evalEval z y H =
      ∑ i ∈ Finset.range (H.natDegree + 1), (H.coeff i).eval z * y ^ i := by
    rw [Polynomial.evalEval]
    rw [show Polynomial.eval (Polynomial.C y) H =
        ∑ i ∈ Finset.range (H.natDegree + 1), H.coeff i * (Polynomial.C y) ^ i by
      exact Polynomial.eval_eq_sum_range (x := Polynomial.C y)]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C]
  rw [H_tilde', if_neg (by simpa [hd] using hdne)]
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_pow, Polynomial.evalEval_X,
    Polynomial.evalEval_finset_sum, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    Polynomial.eval_mul, Polynomial.eval_pow]
  rw [hEvalH]
  simp only [hd]
  rw [Finset.sum_range_succ]
  simp only [← hd]
  rw [mul_add]
  have hsum_lower :
      (∑ x ∈ Finset.range d, Polynomial.eval z (H.coeff x) *
          Polynomial.eval z (H.coeff d) ^ (d - 1 - x) * (w * y) ^ x) =
        w ^ (d - 1) * ∑ x ∈ Finset.range d, Polynomial.eval z (H.coeff x) * y ^ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hid : d - 1 - i + i = d - 1 := by
      have : i < d := Finset.mem_range.mp hi
      omega
    rw [hwd, mul_pow]
    calc
      Polynomial.eval z (H.coeff i) * w ^ (d - 1 - i) * (w ^ i * y ^ i)
          = Polynomial.eval z (H.coeff i) * ((w ^ (d - 1 - i) * w ^ i) * y ^ i) := by ring
      _ = Polynomial.eval z (H.coeff i) * (w ^ (d - 1) * y ^ i) := by rw [← pow_add, hid]
      _ = w ^ (d - 1) * (Polynomial.eval z (H.coeff i) * y ^ i) := by ring
  have hlead : (w * y) ^ d = w ^ (d - 1) * (Polynomial.eval z (H.coeff d) * y ^ d) := by
    rw [hwd, mul_pow]
    have hpow : w ^ d = w ^ (d - 1) * w := by
      have hds : d = (d - 1) + 1 := by omega
      calc
        w ^ d = w ^ ((d - 1) + 1) := congrArg (fun n : ℕ => w ^ n) hds
        _ = w ^ (d - 1) * w := by rw [pow_succ]
    rw [hpow]; ring
  rw [hsum_lower, hlead, add_comm]

lemma evalEval_H_tilde'_eq_zero_of_evalEval_eq_zero (H : F[X][Y]) (hH : 0 < H.natDegree)
    {z y : F} (hroot : Polynomial.evalEval z y H = 0) :
    Polynomial.evalEval z ((H.coeff H.natDegree).eval z * y) (H_tilde' H) = 0 := by
  rw [evalEval_H_tilde' H hH z y, hroot, mul_zero]

lemma eval_evalX_eq_evalEval (H : F[X][Y]) (z y : F) :
    (Polynomial.Bivariate.evalX z H).eval y = Polynomial.evalEval z y H := by
  rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.map_evalRingHom_eval]

lemma evalEval_H_tilde'_eq_zero_of_evalX_eq_zero (H : F[X][Y]) (hH : 0 < H.natDegree)
    {z y : F} (hroot : (Polynomial.Bivariate.evalX z H).eval y = 0) :
    Polynomial.evalEval z ((H.coeff H.natDegree).eval z * y) (H_tilde' H) = 0 := by
  apply evalEval_H_tilde'_eq_zero_of_evalEval_eq_zero H hH
  rwa [← eval_evalX_eq_evalEval H z y]

private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]

private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. -/
lemma H_tilde_equiv_H_tilde' (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [H_tilde', hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, H_tilde]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [H_tilde', hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [H_tilde, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. This is the forward-named alias used by later Appendix A proofs. -/
lemma map_H_tilde'_eq_H_tilde (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H :=
  H_tilde_equiv_H_tilde' H

section FieldIrreducibility

variable {F : Type} [Field F]

/-- The integral monicized polynomial `H_tilde'` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducibleHTilde'OfIrreducible {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde' H) := by
  have hmap : Irreducible ((H_tilde' H).map (univPolyHom (F := F))) := by
    simpa [H_tilde_equiv_H_tilde'] using
      irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH
  exact (H_tilde'_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end FieldIrreducibility

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        bivPolyHom (by
          rw [Ideal.span_le]
          intro x hx
          rw [Set.mem_singleton_iff] at hx; subst hx
          change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
          rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
              H_tilde_equiv_H_tilde']
          exact Ideal.subset_span rfl)

section FieldEmbedding

variable {F : Type} [Field F]

private lemma H_tilde'_dvd_of_map_dvd_H_tilde {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : H_tilde H ∣ p.map (univPolyHom (F := F))) :
    H_tilde' H ∣ p := by
  let q : F[X][Y] := H_tilde' H
  have hqmonic : q.Monic := H_tilde'_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, H_tilde_equiv_H_tilde'] using hp
  have hqmap_dvd_rem :
      q.map (univPolyHom (F := F)) ∣
        (p %ₘ q).map (univPolyHom (F := F)) := by
    have hrem :
        (p %ₘ q).map (univPolyHom (F := F)) =
          p.map (univPolyHom (F := F)) -
            q.map (univPolyHom (F := F)) * (p /ₘ q).map (univPolyHom (F := F)) := by
      have h := congrArg (fun r : F[X][Y] => r.map (univPolyHom (F := F)))
        (Polynomial.modByMonic_add_div p q)
      simp only [Polynomial.map_add, Polynomial.map_mul] at h
      rw [← h]
      ring
    rw [hrem]
    exact dvd_sub hqmap_dvd_p (dvd_mul_right _ _)
  have hdegree :
      ((p %ₘ q).map (univPolyHom (F := F))).degree <
        (q.map (univPolyHom (F := F))).degree := by
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    exact Polynomial.degree_modByMonic_lt p hqmonic
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hqmap_dvd_rem hdegree

private lemma mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {H_tilde H}) :
    p ∈ Ideal.span {H_tilde' H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact H_tilde'_dvd_of_map_dvd_H_tilde hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)

/-- The regular quotient embeds injectively into the function-field quotient when `H` has positive
degree in `Y`. -/
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde hHdeg hp

end FieldEmbedding

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElms_set_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElms_set H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElms_set_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElms_set H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElms_set_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a + b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElms_set_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) : -a ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElms_set_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a - b ∈ regularElms_set H := by
  simpa [sub_eq_add_neg] using regularElms_set_add ha (regularElms_set_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElms_set_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a * b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElms_set_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) (n : ℕ) : a ^ n ∈ regularElms_set H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElms_set_mul ih ha

/-- The regular elements are closed under finite sums. -/
lemma regularElms_set_sum {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElms_set H) :
    (∑ i ∈ s, f i) ∈ regularElms_set H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact regularElms_set_add
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := H_tilde'_monic H hH
  Polynomial.modByMonic β.out (H_tilde' H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (H_tilde' H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (H_tilde'_monic H hH)

/-- The canonical representative has natural degree bounded by the defining relation. -/
lemma canonicalRepOf𝒪_natDegree_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree ≤ (H_tilde' H).natDegree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.natDegree_modByMonic_le _ (H_tilde'_monic H hH)

/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {H_tilde' H}
  let q : F[X][Y] := H_tilde' H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]

/-- Canonical representatives of quotient constructors are computed by `modByMonic`. -/
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      p %ₘ H_tilde' H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p := rfl

/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 hp

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_Λ_zero (H : F[X][Y]) (D : ℕ) :
    weight_Λ (0 : F[X][Y]) H D = ⊥ := by
  simp [weight_Λ]

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight_Λ (canonicalRepOf𝒪 hH f) H D

/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma weight_Λ_over_𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ := by
  simp [weight_Λ_over_𝒪]

/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma weight_Λ_over_𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ (p %ₘ H_tilde' H) H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ p H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-! ### Λ-weight calculus

Algebraic identities for the bivariate `Λ`-weight from Appendix A.2 of [BCIKS20]. The weight
`m := D + 1 − natDegreeY H` is the per-Y-power contribution; constants in `F[X]` contribute their
`natDegree`. -/

/-- A monomial `n` in `f`'s support contributes a lower bound on `Λ(f)`. -/
lemma le_weight_Λ_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight_Λ f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn

/-- Characterization: `Λ(f) ≤ b` iff every monomial in `f`'s support contributes at most `b`. -/
lemma weight_Λ_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_Λ_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)

/-- `Λ(C c) ≤ c.natDegree`. -/
lemma weight_Λ_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight_Λ (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]

/-- `Λ(Y^k) ≤ k · m`. -/
lemma weight_Λ_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight_Λ ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]

/-- `Λ(C c · Y^k) ≤ k · m + c.natDegree`. -/
lemma weight_Λ_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c * Polynomial.X ^ k : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- The `Λ`-weight is invariant under negation. -/
@[simp]
lemma weight_Λ_neg (f H : F[X][Y]) (D : ℕ) : weight_Λ (-f) H D = weight_Λ f H D := by
  classical
  unfold weight_Λ
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]

/-- `Λ(f + g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f + g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  -- The contribution at `n` to weight_Λ (f + g) is bounded by f's or g's contribution.
  have hcoeff : (f + g).coeff n = f.coeff n + g.coeff n := Polynomial.coeff_add _ _ _
  have hsum_ne : f.coeff n + g.coeff n ≠ 0 := by
    rw [← hcoeff]; exact Polynomial.mem_support_iff.mp hn
  by_cases hf : f.coeff n = 0
  · -- f.coeff n = 0, so g.coeff n ≠ 0
    have hg : g.coeff n ≠ 0 := by simpa [hf] using hsum_ne
    have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
    have heq : (f + g).coeff n = g.coeff n := by simp [hcoeff, hf]
    change (WithBot.some _ : WithBot ℕ) ≤ _
    rw [heq]
    exact (le_weight_Λ_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_Λ_of_mem_support hnf).trans (le_max_left _ _)
    · have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
      have hdeg : ((f + g).coeff n).natDegree ≤
          max (f.coeff n).natDegree (g.coeff n).natDegree := by
        rw [hcoeff]; exact Polynomial.natDegree_add_le _ _
      rcases le_total (f.coeff n).natDegree (g.coeff n).natDegree with h | h
      · -- bound by g's contribution
        have hbound : ((f + g).coeff n).natDegree ≤ (g.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_right h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ g H D := le_weight_Λ_of_mem_support hng
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_right _ _
      · have hbound : ((f + g).coeff n).natDegree ≤ (f.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_left h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ f H D := le_weight_Λ_of_mem_support hnf
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_left _ _

/-- `Λ(f − g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f - g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_Λ_add_le f (-g) H D).trans_eq (by rw [weight_Λ_neg])

/-- `Λ` of a finite sum is bounded by the max of the summands' weights. -/
lemma weight_Λ_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight_Λ (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight_Λ (f i) H D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_add_le _ _ _ _).trans (max_le_max le_rfl ih)

/-- For a monomial `n` in the support of `f * g`, there is a splitting `n = i + j` with both
coefficients nonzero and `((f * g).coeff n).natDegree ≤ (f.coeff i).natDegree +
(g.coeff j).natDegree`. -/
lemma exists_split_natDegree_coeff_mul_le {f g : F[X][Y]} {n : ℕ}
    (hn : n ∈ (f * g).support) :
    ∃ i j : ℕ, i + j = n ∧ f.coeff i ≠ 0 ∧ g.coeff j ≠ 0 ∧
      ((f * g).coeff n).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
  classical
  -- The support of nonzero product terms over the antidiagonal of `n`.
  set s : Finset (ℕ × ℕ) :=
    (Finset.antidiagonal n).filter (fun p => f.coeff p.1 * g.coeff p.2 ≠ 0) with hs_def
  have hcoeff : (f * g).coeff n = ∑ p ∈ s, f.coeff p.1 * g.coeff p.2 := by
    rw [Polynomial.coeff_mul]
    rw [hs_def, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : f.coeff p.1 * g.coeff p.2 = 0 <;> simp [hp]
  have hne : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hcoeff, h, Finset.sum_empty] at hne
    exact hne rfl
  -- Pick the pair maximizing the product's `natDegree`.
  obtain ⟨p, hp_mem, hp_eq⟩ :=
    Finset.exists_mem_eq_sup s hs_nonempty
      (fun p => (f.coeff p.1 * g.coeff p.2).natDegree)
  have hp_filter := Finset.mem_filter.mp hp_mem
  have hp_anti : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp_filter.1
  have hp_prod_ne : f.coeff p.1 * g.coeff p.2 ≠ 0 := hp_filter.2
  have hf_ne : f.coeff p.1 ≠ 0 := fun h => hp_prod_ne (by rw [h, zero_mul])
  have hg_ne : g.coeff p.2 ≠ 0 := fun h => hp_prod_ne (by rw [h, mul_zero])
  refine ⟨p.1, p.2, hp_anti, hf_ne, hg_ne, ?_⟩
  -- The sum's `natDegree` is at most the maximal term's, which is at most the factors' sum.
  have hsum_le : ((f * g).coeff n).natDegree ≤
      (f.coeff p.1 * g.coeff p.2).natDegree := by
    rw [hcoeff]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (n := (f.coeff p.1 * g.coeff p.2).natDegree)
      (s := s) (fun q : ℕ × ℕ => f.coeff q.1 * g.coeff q.2) (fun q hq => ?_)
    exact (Finset.le_sup (f := fun q : ℕ × ℕ => (f.coeff q.1 * g.coeff q.2).natDegree) hq).trans_eq
      hp_eq
  exact hsum_le.trans Polynomial.natDegree_mul_le

/-- Sub-multiplicativity of the bivariate `Λ`-weight: `Λ(f · g) ≤ Λ(f) + Λ(g)`. The per-`Y`-power
weight `m` is additive across the product, and coefficient `natDegree`s are sub-additive. -/
lemma weight_Λ_mul_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f * g) H D ≤ weight_Λ f H D + weight_Λ g H D := by
  classical
  set m : ℕ := D + 1 - Bivariate.natDegreeY H with hm_def
  refine Finset.sup_le (fun n hn => ?_)
  obtain ⟨i, j, hij, hf_ne, hg_ne, hdeg⟩ := exists_split_natDegree_coeff_mul_le hn
  have hi_mem : i ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
  have hj_mem : j ∈ g.support := Polynomial.mem_support_iff.mpr hg_ne
  have hf_le : (WithBot.some (i * m + (f.coeff i).natDegree) : WithBot ℕ) ≤ weight_Λ f H D :=
    le_weight_Λ_of_mem_support hi_mem
  have hg_le : (WithBot.some (j * m + (g.coeff j).natDegree) : WithBot ℕ) ≤ weight_Λ g H D :=
    le_weight_Λ_of_mem_support hj_mem
  have hnum : n * m + ((f * g).coeff n).natDegree ≤
      (i * m + (f.coeff i).natDegree) + (j * m + (g.coeff j).natDegree) := by
    have hnm : n * m = i * m + j * m := by rw [← hij, Nat.add_mul]
    omega
  calc (WithBot.some (n * m + ((f * g).coeff n).natDegree) : WithBot ℕ)
      ≤ WithBot.some ((i * m + (f.coeff i).natDegree) +
          (j * m + (g.coeff j).natDegree)) := by exact_mod_cast hnum
    _ = WithBot.some (i * m + (f.coeff i).natDegree) +
          WithBot.some (j * m + (g.coeff j).natDegree) := by rw [WithBot.coe_add]
    _ ≤ weight_Λ f H D + weight_Λ g H D := add_le_add hf_le hg_le

/-- Bound on the `X`-degree of a coefficient of `H` from a `totalDegree` bound. -/
lemma natDegree_coeff_le_of_totalDegree_le (f : F[X][Y]) {D : ℕ}
    (hD : Bivariate.totalDegree f ≤ D) (i : ℕ) :
    (f.coeff i).natDegree ≤ D - i := by
  classical
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hi_in : i ∈ f.support := Polynomial.mem_support_iff.mpr hi
    have h1 : (f.coeff i).natDegree + i ≤ Bivariate.totalDegree f :=
      Bivariate.coeff_totalDegree_le f hi_in
    omega

/-- Sub-additivity for `C c · Y^k · f`: given `Λ(f) ≤ b`, multiplying by `C c · Y^k` adds
`k · m + c.natDegree` to the weight. -/
lemma weight_Λ_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  rw [weight_Λ_le_iff] at hf
  intro n hn
  have hcoeff_ne : (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeff_eq :
      (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n =
        (if k ≤ n then c * f.coeff (n - k) else 0) := by
    rw [show (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]) =
           Polynomial.C c * (f * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  by_cases hkn : k ≤ n
  · rw [hcoeff_eq, if_pos hkn] at hcoeff_ne
    have hf_ne : f.coeff (n - k) ≠ 0 := by
      intro h0
      apply hcoeff_ne
      rw [h0, mul_zero]
    have hn_k_in : n - k ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
    have hf_bound := hf (n - k) hn_k_in
    rw [hcoeff_eq, if_pos hkn]
    have hdeg : (c * f.coeff (n - k)).natDegree ≤ c.natDegree + (f.coeff (n - k)).natDegree :=
      Polynomial.natDegree_mul_le
    have hsplit : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hgoal :
        n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
          k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b := by
      have h1 :
          n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) :=
        Nat.add_le_add_left hdeg _
      have h2 :
          n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) =
            k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree +
              ((n - k) * (D + 1 - Bivariate.natDegreeY H) +
                (f.coeff (n - k)).natDegree) := by
        have hnk : k + (n - k) = n := Nat.add_sub_cancel' hkn
        conv_lhs => rw [hsplit, Nat.add_mul]
        rw [show k + (n - k) - k = n - k from by omega]
        ring
      rw [h2] at h1
      exact h1.trans (Nat.add_le_add_left hf_bound _)
    exact hgoal
  · rw [hcoeff_eq, if_neg hkn] at hcoeff_ne
    exact (hcoeff_ne rfl).elim

/-- The `natDegree` of `H_tilde' H` matches that of `H` when `0 < H.natDegree`. -/
lemma natDegree_H_tilde' {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde' H).natDegree = H.natDegree := by
  classical
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  have hsum_deg :
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]).degree < (H.natDegree : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr <| by
        intro i hi
        exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  rw [show (Polynomial.X ^ H.natDegree +
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]) =
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i) + Polynomial.X ^ H.natDegree by ring]
  have hX_deg : (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_right_of_degree_lt (hsum_deg.trans_eq hX_deg.symm), hX_deg]

/-- The `Λ`-weight of `H_tilde' H` is bounded by `d_H · m`, where `d_H = H.natDegree`. -/
lemma weight_Λ_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ (H_tilde' H) H D ≤
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hd_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  refine (weight_Λ_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · -- weight_Λ Y^d ≤ d · m
    refine (weight_Λ_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  · -- weight_Λ (∑ ... · Y^i) ≤ d · m
    refine (weight_Λ_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_Λ_C_mul_X_pow_le H D _ _).trans ?_
    -- Goal: WithBot.some (i·m + (H.coeff i · W^(d-1-i)).natDegree) ≤ WithBot.some (d·m)
    rw [WithBot.coe_le_coe]
    rw [hbY]
    have hcoeff_natDeg :
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) := by
      have h1 :
          (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 :
          (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree :=
        Polynomial.natDegree_pow_le
      have hi_deg : (H.coeff i).natDegree ≤ D - i :=
        natDegree_coeff_le_of_totalDegree_le H hD i
      have hd_deg : (H.coeff H.natDegree).natDegree ≤ D - H.natDegree :=
        natDegree_coeff_le_of_totalDegree_le H hD H.natDegree
      calc (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree
          ≤ (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree := h1
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree := by
            exact Nat.add_le_add hi_deg h2
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hd_deg) _
    -- numeric bound: i·m + (D-i) + (d-1-i)(D-d) = d·m
    have hadd : i * (D + 1 - H.natDegree) +
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          i * (D + 1 - H.natDegree) +
            ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) :=
      Nat.add_le_add_left hcoeff_natDeg _
    refine hadd.trans ?_
    -- Numeric identity: i*(D+1-d) + (D-i) + (d-1-i)(D-d) = d*(D+1-d)
    have hkey : i * (D + 1 - H.natDegree) +
        ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) =
        H.natDegree * (D + 1 - H.natDegree) := by
      have hi_le : i ≤ H.natDegree - 1 := by omega
      have hi_le_D : i ≤ D := by omega
      have hd_le_D1 : H.natDegree ≤ 1 + D := by omega
      have hd_le_D' : H.natDegree ≤ D + 1 := by omega
      zify [hd_le_D, hd_le_D', hi_le, hi_le_D, hH]
      ring
    omega

/-- One reduction step in `modByMonic` does not increase `Λ`-weight: subtracting
`C(p.leadingCoeff) · Y^(p.natDegree - d_H) · H_tilde' H` from `p` keeps the weight bounded by
`Λ(p)`. -/
lemma weight_Λ_sub_leadingCoeff_mul_H_tilde'_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight_Λ (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * H_tilde' H) H D ≤
      weight_Λ p H D := by
  classical
  refine (weight_Λ_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_Λ_C_mul_X_pow_mul_le (weight_Λ_H_tilde'_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_Λ_of_mem_support hp_in)
    rw [WithBot.coe_le_coe]
    change (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
        (p.coeff p.natDegree).natDegree + H.natDegree * (D + 1 - Bivariate.natDegreeY H) ≤
        p.natDegree * (D + 1 - Bivariate.natDegreeY H) + (p.coeff p.natDegree).natDegree
    have hsum : (p.natDegree - H.natDegree) + H.natDegree = p.natDegree := by omega
    have hadd_mul :
        (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
            H.natDegree * (D + 1 - Bivariate.natDegreeY H) =
          p.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
      rw [← Nat.add_mul, hsum]
    linarith [hadd_mul]

/-- Complete reduction modulo `H_tilde' H` never increases the `Λ`-weight (Appendix A.2 of
[BCIKS20]): `Λ(p %ₘ H_tilde' H) ≤ Λ(p)`. Proved by well-founded recursion mirroring the
`modByMonic` reduction, using `weight_Λ_sub_leadingCoeff_mul_H_tilde'_le` for the single step. -/
lemma weight_Λ_modByMonic_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight_Λ (p %ₘ H_tilde' H) H D ≤ weight_Λ p H D
  | p => by
    classical
    set q : F[X][Y] := H_tilde' H with hq_def
    have hqmonic : q.Monic := H_tilde'_monic H hH
    have hq_natDeg : q.natDegree = H.natDegree := natDegree_H_tilde' hH
    by_cases hstep : H.natDegree ≤ p.natDegree ∧ p ≠ 0
    · -- A reduction step happens: `p %ₘ q = (p - C(lc) * X^(deg) * q) %ₘ q`.
      obtain ⟨hp_deg, hp_ne⟩ := hstep
      set z : F[X][Y] :=
        Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - H.natDegree) with hz_def
      -- The reduced polynomial has strictly smaller degree (well-founded recursion).
      have hdeg_lt : (p - q * z).degree < p.degree := by
        have hcond : q.degree ≤ p.degree ∧ p ≠ 0 := by
          refine ⟨?_, hp_ne⟩
          rw [Polynomial.degree_eq_natDegree hqmonic.ne_zero,
              Polynomial.degree_eq_natDegree hp_ne, Nat.cast_le, hq_natDeg]
          exact hp_deg
        have := Polynomial.div_wf_lemma hcond hqmonic
        rwa [hq_natDeg, ← hz_def] at this
      have hmod_eq : p %ₘ q = (p - q * z) %ₘ q := by
        rw [Polynomial.sub_modByMonic, Polynomial.self_mul_modByMonic hqmonic, sub_zero]
      have hcomm : q * z = Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - H.natDegree) * q := by rw [hz_def]; ring
      have ih := weight_Λ_modByMonic_le hD hH (p - q * z)
      calc weight_Λ (p %ₘ q) H D
          = weight_Λ ((p - q * z) %ₘ q) H D := by rw [hmod_eq]
        _ ≤ weight_Λ (p - q * z) H D := ih
        _ = weight_Λ (p - Polynomial.C p.leadingCoeff *
              Polynomial.X ^ (p.natDegree - H.natDegree) * q) H D := by rw [hcomm]
        _ ≤ weight_Λ p H D := by
              rw [hq_def]; exact weight_Λ_sub_leadingCoeff_mul_H_tilde'_le hD hH hp_deg
    · -- No reduction: `p %ₘ q = p`.
      rw [not_and_or, not_le, not_not] at hstep
      have hself : p %ₘ q = p := by
        rcases hstep with hlt | hp0
        · rw [Polynomial.modByMonic_eq_self_iff hqmonic]
          rcases eq_or_ne p 0 with rfl | hp_ne
          · rw [Polynomial.degree_zero]
            exact Ne.bot_lt fun h =>
              hqmonic.ne_zero (Polynomial.degree_eq_bot.mp h)
          · rw [Polynomial.degree_eq_natDegree hp_ne,
                Polynomial.degree_eq_natDegree hqmonic.ne_zero, Nat.cast_lt, hq_natDeg]
            exact hlt
        · rw [hp0, Polynomial.zero_modByMonic]
      rw [hself]
  termination_by p => p.degree
  decreasing_by exact hdeg_lt

/-- Any polynomial representative bounds the `𝒪`-weight of the element it represents: if
`⟦r⟧ = a` then `weight_Λ_over_𝒪 hH a D ≤ weight_Λ r H D`. This combines the canonical-representative
identity with `weight_Λ_modByMonic_le`, and is the workhorse for bounding weights of regular
elements by any convenient (non-reduced) representative. -/
lemma weight_Λ_over_𝒪_le_of_mk_eq {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {r : F[X][Y]} {a : 𝒪 H}
    (hr : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) r : 𝒪 H) = a) :
    weight_Λ_over_𝒪 hH a D ≤ weight_Λ r H D := by
  rw [← hr, weight_Λ_over_𝒪_mk]
  exact weight_Λ_modByMonic_le hD hH r

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

section LemmaA1

variable {F : Type} [Field F]

/-- Applying the specialization `π_z` to a quotient constructor evaluates the representative at the
point `(z, t_z)`. -/
lemma π_z_mk {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) (p : F[X][Y]) :
    π_z z root (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p) =
      Polynomial.evalEval z root.1 p := by
  rw [π_z, Ideal.Quotient.lift_mk]
  rfl

/-- The bivariate polynomial `p` evaluated at `(z, y)` agrees with the univariate specialization
`p.map (evalRingHom z)` evaluated at `y`. -/
lemma evalEval_eq_eval_map (z y : F) (p : F[X][Y]) :
    Polynomial.evalEval z y p = (p.map (Polynomial.evalRingHom z)).eval y := by
  rw [Polynomial.map_evalRingHom_eval]

/-- The monicized polynomial `H_tilde H` is monic, as the image of the monic `H_tilde' H`. -/
lemma H_tilde_monic {H : F[X][Y]} (hH : 0 < H.natDegree) : (H_tilde H).Monic := by
  have h := (H_tilde'_monic H hH).map (univPolyHom (F := F))
  rwa [H_tilde_equiv_H_tilde' H] at h

/-- The resultant (in `Y`) of the canonical representative of a nonzero regular element `β` and the
defining relation `H_tilde' H` is a nonzero element of `F[X]`. This is the algebraic heart of the
"not coprime forces `β = 0`" step: since `H_tilde H` is irreducible over `F(X)` and the
representative has strictly smaller `Y`-degree, they are coprime, so the resultant is nonzero. -/
lemma resultant_canonicalRep_H_tilde'_ne_zero {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {β : 𝒪 H} (hβ : β ≠ 0) :
    Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) H.natDegree H.natDegree ≠ 0 := by
  classical
  set r := canonicalRepOf𝒪 hH β with hr_def
  -- The canonical representative is nonzero.
  have hr_ne : r ≠ 0 := by
    intro h0
    apply hβ
    have := mk_canonicalRepOf𝒪 hH β
    rw [hr_def] at h0
    rw [h0] at this
    simpa using this.symm
  -- Degrees: `H_tilde' H` is monic of degree `d`, the representative has `Y`-degree `< d`.
  have hd : (H_tilde' H).natDegree = H.natDegree := natDegree_H_tilde' hH
  have hr_deg : r.natDegree < H.natDegree := by
    have hlt := canonicalRepOf𝒪_degree_lt hH β
    rw [← hr_def] at hlt
    have : r.degree < (H_tilde' H).degree := hlt
    rw [Polynomial.degree_eq_natDegree hr_ne,
        Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero] at this
    rw [hd] at this
    exact_mod_cast this
  -- Map everything to the field `RatFunc F` via `univPolyHom`.
  have hinj : Function.Injective (univPolyHom (F := F)) := univPolyHom_injective
  -- Work with the explicit image `Ht := (H_tilde' H).map univPolyHom` to avoid unfolding `H_tilde`.
  set Ht : Polynomial (RatFunc F) := (H_tilde' H).map univPolyHom with hHt_def
  set rmap : Polynomial (RatFunc F) := r.map univPolyHom with hrmap_def
  have hmap_eq : Ht = H_tilde H := H_tilde_equiv_H_tilde' H
  have hHt_irr : Irreducible Ht := by
    rw [hmap_eq]; exact irreducibleHTildeOfIrreducible_of_natDegree_pos hH Fact.out
  have hHt_monic : Ht.Monic := (H_tilde'_monic H hH).map _
  -- `natDegree` facts proved via the (injective, degree-preserving) map; no `H_tilde` unfolding.
  have hHt_natDeg : Ht.natDegree = H.natDegree := by
    rw [hHt_def, Polynomial.natDegree_map_eq_of_injective hinj, hd]
  have hrmap_natDeg : rmap.natDegree = r.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj r
  -- The image of the representative is nonzero with `Y`-degree `< d`.
  have hrmap_ne : rmap ≠ 0 :=
    fun h => hr_ne (Polynomial.map_eq_zero_iff hinj |>.1 h)
  have hrmap_deg : rmap.natDegree < Ht.natDegree := by
    rw [hrmap_natDeg, hHt_natDeg]; exact hr_deg
  -- Coprimality over the field: an irreducible polynomial is coprime to anything of strictly
  -- smaller degree (which it cannot divide).
  have hcoprime : IsCoprime Ht rmap :=
    hHt_irr.coprime_iff_not_dvd.2 (hHt_monic.not_dvd_of_natDegree_lt hrmap_ne hrmap_deg)
  -- Hence the resultant over the field, using the natural degrees, is nonzero.
  have hres_field :
      Polynomial.resultant rmap Ht r.natDegree H.natDegree ≠ 0 := by
    have h := Polynomial.resultant_ne_zero rmap Ht hcoprime.symm
    rwa [hrmap_natDeg, hHt_natDeg] at h
  -- Transport along `univPolyHom` (injective): the resultant over `F[X]` with the same degrees
  -- `(r.natDegree, H.natDegree)` is nonzero.
  have hres_base :
      Polynomial.resultant r (H_tilde' H) r.natDegree H.natDegree ≠ 0 := by
    intro hzero
    apply hres_field
    have hmap_res :
        Polynomial.resultant rmap Ht r.natDegree H.natDegree
          = univPolyHom (Polynomial.resultant r (H_tilde' H) r.natDegree H.natDegree) := by
      rw [hHt_def, hrmap_def]
      exact Polynomial.resultant_map_map r (H_tilde' H) r.natDegree H.natDegree univPolyHom
    rw [hmap_res, hzero, map_zero]
  -- Pad the first-argument degree from `r.natDegree` up to `H.natDegree`; since `H_tilde' H` is
  -- monic the padding factor is a sign (`±1`), hence does not affect nonvanishing.
  intro hzero
  apply hres_base
  have hk : r.natDegree + (H.natDegree - r.natDegree) = H.natDegree := by omega
  have hpad := Polynomial.resultant_add_left_deg r (H_tilde' H) r.natDegree
    H.natDegree (H.natDegree - r.natDegree) (le_refl r.natDegree)
  rw [hk] at hpad
  -- `(H_tilde' H).coeff H.natDegree = leadingCoeff = 1`.
  have hlead : (H_tilde' H).coeff H.natDegree = 1 := by
    have := (H_tilde'_monic H hH)
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hd] at this
    exact this
  rw [hlead, one_pow, mul_one] at hpad
  -- `resultant r H̃' d d = (-1)^(d·k) · resultant r H̃' r.natDeg d`.
  have : Polynomial.resultant r (H_tilde' H) r.natDegree H.natDegree = 0 := by
    have hsign : ((-1 : F[X]) ^ (H.natDegree * (H.natDegree - r.natDegree))) ≠ 0 := by
      exact pow_ne_zero _ (by simp)
    have hzero' :
        (-1 : F[X]) ^ (H.natDegree * (H.natDegree - r.natDegree)) *
          Polynomial.resultant r (H_tilde' H) r.natDegree H.natDegree = 0 := by
      rw [← hpad]; exact hzero
    exact (mul_eq_zero.1 hzero').resolve_left hsign
  exact this

/-- Padded resultant vanishing from a shared root: if `b` is monic of degree `d`, `a` has degree
`≤ d`, and `a`, `b` have a common root, then the (degree-`d`) resultant `resultant a b d d`
is `0`. -/
lemma resultant_eq_zero_of_common_root {K : Type} [Field K] {a b : K[X]} {t : K} {d : ℕ}
    (hb : b.Monic) (hbd : b.natDegree = d) (had : a.natDegree ≤ d)
    (hat : a.IsRoot t) (hbt : b.IsRoot t) :
    Polynomial.resultant a b d d = 0 := by
  -- `a, b` are not coprime: both divisible by the non-unit `X - C t`.
  have hb_ne : b ≠ 0 := hb.ne_zero
  have hdvd_a : (Polynomial.X - Polynomial.C t) ∣ a := Polynomial.dvd_iff_isRoot.2 hat
  have hdvd_b : (Polynomial.X - Polynomial.C t) ∣ b := Polynomial.dvd_iff_isRoot.2 hbt
  have hncop : ¬ IsCoprime a b := fun hco => by
    have := hco.isUnit_of_dvd' hdvd_a hdvd_b
    exact (Polynomial.not_isUnit_X_sub_C t) this
  -- Natural-degree resultant is `0` over the field.
  have hnat : Polynomial.resultant a b = 0 :=
    Polynomial.resultant_eq_zero_iff.2 ⟨Or.inr hb_ne, hncop⟩
  -- Pad both arguments up to `d` and conclude (`b.coeff d = 1`, `a.coeff (natDeg a)` may be killed
  -- — but the natural resultant is already `0`).
  -- Pad the second argument from `natDegree b = d` (no padding) and the first from `natDegree a`.
  have hpad_a := Polynomial.resultant_add_left_deg a b a.natDegree b.natDegree
    (d - a.natDegree) (le_refl a.natDegree)
  -- Normalise `b.natDegree` to `d` everywhere, then collapse the padded `LHS` exponent.
  rw [hbd, show a.natDegree + (d - a.natDegree) = d by omega] at hpad_a
  -- `hpad_a : resultant a b d d = (unit) * resultant a b a.natDegree d`.
  -- The last factor equals the natural-degree resultant `a.resultant b` (since `natDegree b = d`).
  rw [hpad_a, show Polynomial.resultant a b a.natDegree d
        = Polynomial.resultant a b a.natDegree b.natDegree by rw [hbd], hnat, mul_zero]

/-- Every specialization point in `S_β` is a root of the resultant `Res_Y(r, H̃')` viewed as a
univariate polynomial in `Z = X`: the common rational root `t_z` is a shared root of the two
`Z = z` specializations. -/
lemma eval_resultant_eq_zero_of_mem_S_β {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H)
    {z : F} (hz : z ∈ S_β β) :
    (Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) H.natDegree H.natDegree).eval z
      = 0 := by
  classical
  set r := canonicalRepOf𝒪 hH β with hr_def
  obtain ⟨root, hroot⟩ := hz
  set t := root.1 with ht_def
  -- `β = ⟦r⟧`, so `π_z z root β = evalEval z t r`.
  have hβ_eq : β = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) r := (mk_canonicalRepOf𝒪 hH β).symm
  have hr_root : Polynomial.evalEval z t r = 0 := by
    have := hroot
    rw [hβ_eq, π_z_mk] at this
    exact this
  -- `t` is a rational root of `H_tilde' H`.
  have hHt_root : Polynomial.evalEval z t (H_tilde' H) = 0 := root.2
  -- Specialize at `Z = z`: the two univariate polynomials share the root `t`.
  set a : F[X] := r.map (Polynomial.evalRingHom z) with ha_def
  set b : F[X] := (H_tilde' H).map (Polynomial.evalRingHom z) with hb_def
  have hat : a.IsRoot t := by
    rw [ha_def, Polynomial.IsRoot, ← evalEval_eq_eval_map]; exact hr_root
  have hbt : b.IsRoot t := by
    rw [hb_def, Polynomial.IsRoot, ← evalEval_eq_eval_map]; exact hHt_root
  -- `b` is monic of degree `d`, `a` has degree `≤ d`.
  have hb_monic : b.Monic := (H_tilde'_monic H hH).map _
  have hbd : b.natDegree = H.natDegree := by
    rw [hb_def, (H_tilde'_monic H hH).natDegree_map (Polynomial.evalRingHom z),
        natDegree_H_tilde' hH]
  have had : a.natDegree ≤ H.natDegree := by
    have h1 : a.natDegree ≤ r.natDegree := by
      rw [ha_def]; exact Polynomial.natDegree_map_le
    have h2 : r.natDegree ≤ (H_tilde' H).natDegree := by
      rw [hr_def]; exact canonicalRepOf𝒪_natDegree_le hH β
    rw [natDegree_H_tilde' hH] at h2
    omega
  -- The specialized resultant vanishes (common root `t`); transport back via `resultant_map_map`.
  have hspec :
      Polynomial.resultant a b H.natDegree H.natDegree = 0 :=
    resultant_eq_zero_of_common_root hb_monic hbd had hat hbt
  have hmap_res :
      Polynomial.resultant a b H.natDegree H.natDegree
        = (Polynomial.evalRingHom z) (Polynomial.resultant r (H_tilde' H)
            H.natDegree H.natDegree) := by
    rw [ha_def, hb_def]
    exact Polynomial.resultant_map_map r (H_tilde' H) H.natDegree H.natDegree
      (Polynomial.evalRingHom z)
  rw [hmap_res] at hspec
  simpa [Polynomial.coe_evalRingHom] using hspec

end LemmaA1

section LemmaA1Final

variable {F : Type} [Field F]

/-- A nonzero polynomial has at most `natDegree`-many roots, as a `Set.ncard` bound. -/
private lemma ncard_setOf_isRoot_le {K : Type} [Field K] {R : K[X]} (hR : R ≠ 0) :
    {z : K | R.IsRoot z}.ncard ≤ R.natDegree := by
  classical
  calc {z : K | R.IsRoot z}.ncard
      = (R.roots.toFinset : Set K).ncard := by
        congr 1; ext x; simp only [Set.mem_setOf_eq, Multiset.mem_toFinset,
          Polynomial.mem_roots, hR, ne_eq, not_false_eq_true, Finset.mem_coe]
    _ = R.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card R.roots := R.roots.toFinset_card_le
    _ ≤ R.natDegree := Polynomial.card_roots' R

/-- A `Finset.sup` of `WithBot.some` values over a nonempty finset is itself `some`. -/
private lemma sup_some_eq_some {ι : Type} {s : Finset ι} (hs : s.Nonempty) (g : ι → ℕ) :
    ∃ W : ℕ, (s.sup fun i => (WithBot.some (g i) : WithBot ℕ)) = (W : WithBot ℕ) := by
  classical
  induction s using Finset.induction with
  | empty => exact absurd hs (by simp)
  | insert a t ha ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨g a, by simp only [Finset.sup_insert, Finset.sup_empty]; rfl⟩
    · obtain ⟨W, hW⟩ := ih ht
      exact ⟨max (g a) W, by rw [Finset.sup_insert, hW]; rfl⟩

/-- For a nonzero bivariate polynomial `r`, its `Λ`-weight is a finite value `W`, and every
coefficient obeys the weighted bound `k · κ + (r.coeff k).natDegree ≤ W` (where `κ = D + 1 - d_H`).
We package both facts together. -/
private lemma exists_weight_bound {r H : F[X][Y]} {D : ℕ} (hr : r ≠ 0) :
    ∃ W : ℕ, weight_Λ r H D = (W : WithBot ℕ) ∧
      ∀ k, k ∈ r.support →
        k * (D + 1 - Bivariate.natDegreeY H) + (r.coeff k).natDegree ≤ W := by
  classical
  have hsupp : r.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h => hr (Polynomial.support_eq_empty.1 h)
  obtain ⟨W, hW⟩ := sup_some_eq_some hsupp
    (fun deg => deg * (D + 1 - Bivariate.natDegreeY H) + (r.coeff deg).natDegree)
  refine ⟨W, hW, fun k hk => ?_⟩
  have hle : (WithBot.some
        (k * (D + 1 - Bivariate.natDegreeY H) + (r.coeff k).natDegree) : WithBot ℕ)
      ≤ (r.support.sup fun deg =>
          (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (r.coeff deg).natDegree)
            : WithBot ℕ)) :=
    Finset.le_sup (f := fun deg =>
      (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (r.coeff deg).natDegree)
        : WithBot ℕ)) hk
  rw [hW] at hle
  exact WithBot.coe_le_coe.1 hle

/-- `∑_{k<2d} k = d² + 2·∑_{k<d} k`. The key index identity underlying the exact cancellation in the
weighted Sylvester-determinant degree count. -/
private lemma range_two_mul_sum (d : ℕ) :
    ∑ k ∈ Finset.range (2 * d), k = d ^ 2 + 2 * ∑ k ∈ Finset.range d, k := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n) + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Weighted Sylvester-determinant degree count (combinatorial core).** Given per-column
additive weighted-degree bounds on the entries of a `(d+d)×(d+d)` matrix permutation term -- the
left `d` columns ("`H̃'` columns") capped at `d·κ + j·κ` and the right `d` columns ("`r` columns")
capped at `W + j·κ` -- the total degree of any permutation term is at most `d·W`. The exact
cancellation of the weight terms `κ` is `∑(σ i) = ∑ i` together with `∑_{k<2d} = d² + 2∑_{k<d}`. -/
private lemma sum_entry_natDegree_le (d κ W : ℕ) (σ : Equiv.Perm (Fin (d + d)))
    (e : Fin (d + d) → ℕ)
    (hleft : ∀ j : Fin d,
      e (Fin.castAdd d j) + (σ (Fin.castAdd d j)).val * κ ≤ d * κ + (j : ℕ) * κ)
    (hright : ∀ j : Fin d,
      e (Fin.natAdd d j) + (σ (Fin.natAdd d j)).val * κ ≤ W + (j : ℕ) * κ) :
    ∑ i, e i ≤ d * W := by
  have hL : ∑ j : Fin d, (e (Fin.castAdd d j) + (σ (Fin.castAdd d j)).val * κ)
      ≤ ∑ j : Fin d, (d * κ + (j : ℕ) * κ) := Finset.sum_le_sum (fun j _ => hleft j)
  have hR : ∑ j : Fin d, (e (Fin.natAdd d j) + (σ (Fin.natAdd d j)).val * κ)
      ≤ ∑ j : Fin d, (W + (j : ℕ) * κ) := Finset.sum_le_sum (fun j _ => hright j)
  have hadd := Nat.add_le_add hL hR
  have hLHS : (∑ j : Fin d, (e (Fin.castAdd d j) + (σ (Fin.castAdd d j)).val * κ))
            + (∑ j : Fin d, (e (Fin.natAdd d j) + (σ (Fin.natAdd d j)).val * κ))
      = (∑ i, e i) + (∑ i : Fin (d + d), (σ i).val) * κ := by
    rw [← Fin.sum_univ_add (fun i => e i + (σ i).val * κ), Finset.sum_add_distrib, Finset.sum_mul]
  have hperm : (∑ i : Fin (d + d), (σ i).val) = ∑ i : Fin (d + d), (i.val) :=
    Equiv.sum_comp σ (fun i => (i : ℕ))
  have hRHS : (∑ j : Fin d, (d * κ + (j : ℕ) * κ)) + (∑ j : Fin d, (W + (j : ℕ) * κ))
      = d * (d * κ) + d * W + 2 * ((∑ j : Fin d, (j : ℕ)) * κ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hsum2d : (∑ i : Fin (d + d), (i.val)) = d ^ 2 + 2 * (∑ j : Fin d, (j : ℕ)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k) (d + d), Fin.sum_univ_eq_sum_range (fun k => k) d,
        show d + d = 2 * d by ring, range_two_mul_sum]
  rw [hLHS, hperm, hRHS, hsum2d] at hadd
  nlinarith [hadd]

/-- Reduce a determinant `natDegree` bound to a uniform bound on every permutation term. -/
private lemma natDegree_det_le_of_forall_perm {K : Type} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K[X]) (B : ℕ)
    (hσ : ∀ σ : Equiv.Perm (Fin n), (∏ i, M (σ i) i).natDegree ≤ B) :
    M.det.natDegree ≤ B := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
  simp only [Function.comp_apply]
  calc (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree
      = (∏ i, M (σ i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
        · rw [h]; simp [Units.neg_smul]
    _ ≤ B := hσ σ

/-- The H̃'-coefficient weighted bound (Claim A.2 packaging), valid on the support. -/
private lemma natDegree_H_tilde'_coeff_weighted_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {k : ℕ}
    (hk : (H_tilde' H).coeff k ≠ 0) :
    ((H_tilde' H).coeff k).natDegree + k * (D + 1 - Bivariate.natDegreeY H)
      ≤ H.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
  classical
  have hksupp : k ∈ (H_tilde' H).support := Polynomial.mem_support_iff.2 hk
  have hle : (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)
        + ((H_tilde' H).coeff k).natDegree) : WithBot ℕ)
      ≤ weight_Λ (H_tilde' H) H D := by
    unfold weight_Λ
    exact Finset.le_sup (f := fun deg =>
      (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H)
        + ((H_tilde' H).coeff deg).natDegree) : WithBot ℕ)) hksupp
  have := WithBot.coe_le_coe.1 (le_trans hle (weight_Λ_H_tilde'_le hD hH))
  omega

/-- **Lemma A.1** of [BCIKS20], Appendix A.3 (resultant / specialization-point counting).

The `Z`-degree bound on the resultant `Res_Y(r, H̃')` of the canonical representative `r` of the
regular element `β` and the defining relation `H̃'`. This is the analytic heart of the lemma: a
weighted-degree count on the Sylvester determinant. The proof bounds the `Z`-degree of the
Sylvester determinant `Res_Y(r, H̃') = det (sylvester r H̃' d d)` by a weighted-degree count over
permutations (`sum_entry_natDegree_le`): for each permutation either the term vanishes, or every
entry is a nonzero coefficient whose `Λ`-weight obeys the Claim A.2 bounds. -/
lemma natDegree_resultant_canonicalRep_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {β : 𝒪 H} (hβ : β ≠ 0) :
    (↑(Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) H.natDegree H.natDegree).natDegree
        : WithBot ℕ)
      ≤ weight_Λ_over_𝒪 hH β D * H.natDegree := by
  classical
  set r := canonicalRepOf𝒪 hH β with hr_def
  set κ := D + 1 - Bivariate.natDegreeY H with hκ_def
  -- `r ≠ 0`.
  have hr_ne : r ≠ 0 := by
    intro h0
    apply hβ
    have := mk_canonicalRepOf𝒪 hH β
    rw [hr_def] at h0
    rw [h0] at this
    simpa using this.symm
  -- Extract the finite weight `W` and the per-coefficient bound for `r`.
  obtain ⟨W, hWeq, hWbound⟩ := exists_weight_bound (H := H) (D := D) hr_ne
  -- Per-coefficient weighted bounds for the Sylvester entries.
  have hg : ∀ k, (H_tilde' H).coeff k ≠ 0 →
      ((H_tilde' H).coeff k).natDegree + k * κ ≤ H.natDegree * κ := by
    intro k hk; exact natDegree_H_tilde'_coeff_weighted_le hD hH hk
  have hr : ∀ k, r.coeff k ≠ 0 → (r.coeff k).natDegree + k * κ ≤ W := by
    intro k hk
    have := hWbound k (Polynomial.mem_support_iff.2 hk)
    rw [hκ_def]; omega
  -- The resultant is the Sylvester determinant; bound its `natDegree` by `d · W`.
  have hdet : (Polynomial.resultant r (H_tilde' H) H.natDegree H.natDegree).natDegree
      ≤ H.natDegree * W := by
    rw [Polynomial.resultant]
    refine natDegree_det_le_of_forall_perm _ _ (fun σ => ?_)
    -- Per-permutation bound via the combinatorial core.
    by_cases hzero : ∃ i, Polynomial.sylvester r (H_tilde' H) H.natDegree H.natDegree (σ i) i = 0
    · obtain ⟨i, hi⟩ := hzero
      have : (∏ i, Polynomial.sylvester r (H_tilde' H) H.natDegree H.natDegree (σ i) i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [this, Polynomial.natDegree_zero]; exact Nat.zero_le _
    · simp only [not_exists] at hzero
      -- All entries nonzero: bound `natDegree (∏) ≤ ∑ natDegree` and apply the weighted core.
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine sum_entry_natDegree_le H.natDegree κ W σ
        (fun i => (Polynomial.sylvester r (H_tilde' H)
          H.natDegree H.natDegree (σ i) i).natDegree) ?_ ?_
      · -- left columns: `H̃'` coefficients.
        intro j
        have hentry :
            Polynomial.sylvester r (H_tilde' H) H.natDegree H.natDegree
                (σ (Fin.castAdd H.natDegree j)) (Fin.castAdd H.natDegree j)
              = (if ((σ (Fin.castAdd H.natDegree j) : Fin _) : ℕ)
                    ∈ Set.Icc (j : ℕ) ((j : ℕ) + H.natDegree)
                  then (H_tilde' H).coeff
                    (((σ (Fin.castAdd H.natDegree j) : Fin _) : ℕ) - (j : ℕ)) else 0) := by
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        have hne := hzero (Fin.castAdd H.natDegree j)
        simp only [hentry] at hne ⊢
        split_ifs at hne ⊢ with hicc
        · set s := ((σ (Fin.castAdd H.natDegree j) : Fin _) : ℕ)
          have hjs : (j : ℕ) ≤ s := hicc.1
          have hgk := hg (s - (j : ℕ)) hne
          have hsplit : (s - (j : ℕ)) * κ + (j : ℕ) * κ = s * κ := by
            rw [← add_mul]; congr 1; omega
          omega
        · exact absurd rfl hne
      · -- right columns: `r` coefficients.
        intro j
        have hentry :
            Polynomial.sylvester r (H_tilde' H) H.natDegree H.natDegree
                (σ (Fin.natAdd H.natDegree j)) (Fin.natAdd H.natDegree j)
              = (if ((σ (Fin.natAdd H.natDegree j) : Fin _) : ℕ)
                    ∈ Set.Icc (j : ℕ) ((j : ℕ) + H.natDegree)
                  then r.coeff
                    (((σ (Fin.natAdd H.natDegree j) : Fin _) : ℕ) - (j : ℕ)) else 0) := by
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        have hne := hzero (Fin.natAdd H.natDegree j)
        simp only [hentry] at hne ⊢
        split_ifs at hne ⊢ with hicc
        · set s := ((σ (Fin.natAdd H.natDegree j) : Fin _) : ℕ)
          have hjs : (j : ℕ) ≤ s := hicc.1
          have hrk := hr (s - (j : ℕ)) hne
          have hsplit : (s - (j : ℕ)) * κ + (j : ℕ) * κ = s * κ := by
            rw [← add_mul]; congr 1; omega
          omega
        · exact absurd rfl hne
  -- Lift the `ℕ` bound to the `WithBot ℕ` statement.
  have hweight_eq : weight_Λ_over_𝒪 hH β D = (W : WithBot ℕ) := by
    rw [weight_Λ_over_𝒪, ← hr_def, hWeq]
  rw [hweight_eq]
  rw [show ((W : WithBot ℕ) * (H.natDegree : WithBot ℕ)) = ((W * H.natDegree : ℕ) : WithBot ℕ) by
    push_cast; ring]
  refine WithBot.coe_le_coe.2 ?_
  calc (Polynomial.resultant r (H_tilde' H) H.natDegree H.natDegree).natDegree
      ≤ H.natDegree * W := hdet
    _ = W * H.natDegree := by ring

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  -- The embedding is injective, so it suffices to prove `β = 0`.
  rw [show (0 : 𝕃 H) = embeddingOf𝒪Into𝕃 H 0 by simp]
  rw [(embeddingOf𝒪Into𝕃_injective hH).eq_iff]
  by_contra hβ
  -- Set up the canonical representative `r` and the resultant `R`.
  set r := canonicalRepOf𝒪 hH β with hr_def
  set R := Polynomial.resultant r (H_tilde' H) H.natDegree H.natDegree with hR_def
  -- `R ≠ 0` by the coprimality step.
  have hR_ne : R ≠ 0 := resultant_canonicalRep_H_tilde'_ne_zero hH hβ
  -- `S_β β` is contained in the (finite) root set of `R`.
  have hsubset : S_β β ⊆ {z : F | R.IsRoot z} := by
    intro z hz
    have := eval_resultant_eq_zero_of_mem_S_β hH β hz
    rw [← hr_def, ← hR_def] at this
    exact this
  have hfin : {z : F | R.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hR_ne
  -- Counting: `|S_β β| ≤ #roots(R) ≤ deg R ≤ Λ(β)·d`.
  have hcard_le : Set.ncard (S_β β) ≤ R.natDegree :=
    (Set.ncard_le_ncard hsubset hfin).trans (ncard_setOf_isRoot_le hR_ne)
  have hdeg_bound :
      (↑R.natDegree : WithBot ℕ) ≤ weight_Λ_over_𝒪 hH β D * H.natDegree := by
    rw [hR_def, hr_def]
    exact natDegree_resultant_canonicalRep_le hD hH hβ
  -- Chain the inequalities in `WithBot ℕ` to contradict the hypothesis.
  have h1 : (↑(Set.ncard (S_β β)) : WithBot ℕ) ≤ ↑R.natDegree := by
    exact_mod_cast hcard_le
  have h2 : (↑(Set.ncard (S_β β)) : WithBot ℕ) ≤ weight_Λ_over_𝒪 hH β D * H.natDegree :=
    h1.trans hdeg_bound
  exact absurd S_β_card (not_lt.2 h2)

end LemmaA1Final

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElms_set_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElms_set H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElms_set_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.C p)

/-- Nonzero coefficient polynomials remain nonzero after embedding into the function field. -/
lemma liftToFunctionField_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro hzero
  have hmem : coeffAsRatFunc p ∈ Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))) := by
    simpa [liftToFunctionField] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [Ideal.mem_span_singleton] at hmem
  have hp_map : univPolyHom (F := F) p ≠ 0 := by
    intro hp_zero
    exact hp (univPolyHom_injective (F := F) (by simpa using hp_zero))
  have hunit : IsUnit (coeffAsRatFunc p) := by
    have hunitC : IsUnit (Polynomial.C (univPolyHom (F := F) p) :
        Polynomial (RatFunc F)) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hp_map)
    simpa only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C] using hunitC
  exact (irreducibleHTildeOfIrreducible_of_natDegree_pos H_natDegree_pos.out
    H_irreducible.out).not_dvd_isUnit hunit hmem

/-- The leading coefficient `W` of a positive-`Y`-degree `H` is nonzero in the function field. -/
lemma liftToFunctionField_leadingCoeff_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := by
  exact liftToFunctionField_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))

/-- The coefficient embedding into the function field is the bivariate lift of the constant. -/
lemma coeffAsRatFunc_eq_C {F : Type} [Field F] (c : F[X]) :
    coeffAsRatFunc c = Polynomial.C (univPolyHom (F := F) c) := by
  simp only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
    Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- The image of the rational substitution `X / W` under the quotient map is `T / W`. -/
lemma mk_X_div_eq_functionFieldT_div_W {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    (Ideal.Quotient.mk (Ideal.span {H_tilde H})
        (Polynomial.X / Polynomial.C (univPolyHom (F := F) H.leadingCoeff))) =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
  have hW_ne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  set W_rat : Polynomial (RatFunc F) :=
    Polynomial.C (univPolyHom (F := F) H.leadingCoeff) with hW_rat_def
  have hmk_W : Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat =
      liftToFunctionField (H := H) H.leadingCoeff := by
    rw [hW_rat_def, ← coeffAsRatFunc_eq_C]; rfl
  have hmk_X : Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.X : Polynomial (RatFunc F)) =
      functionFieldT (H := H) := rfl
  have ha_ne : univPolyHom (F := F) H.leadingCoeff ≠ 0 := by
    intro h
    exact (Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
      (univPolyHom_injective (F := F) (by simpa using h))
  -- In `(RatFunc F)[X]`, division by the constant `W_rat = C a` is `X * C a⁻¹`.
  have hmul : (Polynomial.X / W_rat) * W_rat = (Polynomial.X : Polynomial (RatFunc F)) := by
    rw [hW_rat_def, Polynomial.div_C, mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ ha_ne, Polynomial.C_1, mul_one]
  rw [eq_div_iff hW_ne, ← hmk_W, ← map_mul, hmul, hmk_X]

/-- The element `α₀ = T / W` is a root of `H` in the function field: evaluating `H` at `T / W`
via the coefficient embedding gives `0`. This is the algebraic heart of the Hensel lift in
Appendix A.4 of [BCIKS20]: `H̃` is the monicization of `H` at the root `α₀`, and `H̃(T) = 0`
in `𝕃`. -/
lemma eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H = 0 := by
  let W_rat : Polynomial (RatFunc F) := Polynomial.C (univPolyHom (F := F) H.leadingCoeff)
  -- `H_tilde H = W_rat^(d-1) * eval₂ (C∘univ) (X / W_rat) H`.
  have hHt : H_tilde H =
      W_rat ^ (H.natDegree - 1) *
        Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W_rat)
          H := rfl
  -- `mk (H_tilde H) = 0` since the generator lies in the ideal.
  have hmk_zero : Ideal.Quotient.mk (Ideal.span {H_tilde H}) (H_tilde H) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  -- Push `mk` through the eval₂ via `hom_eval₂`.
  have hcomp_eq :
      RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H}))
          (RingHom.comp Polynomial.C (univPolyHom (F := F))) =
        (liftToFunctionField (H := H) : F[X] →+* 𝕃 H) := by
    refine RingHom.ext (fun c => ?_)
    simp only [RingHom.comp_apply]
    rw [show (Polynomial.C (univPolyHom (F := F) c)) = coeffAsRatFunc c from
      (coeffAsRatFunc_eq_C c).symm]
    rfl
  have hpush :
      Ideal.Quotient.mk (Ideal.span {H_tilde H})
          (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
            (Polynomial.X / W_rat) H) =
        Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
    rw [Polynomial.hom_eval₂, hcomp_eq, mk_X_div_eq_functionFieldT_div_W (H := H)]
  -- `mk (W_rat) = W ≠ 0`, so the eval₂ factor must vanish.
  have hmk_W_ne : Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat ≠ 0 := by
    change Ideal.Quotient.mk (Ideal.span {H_tilde H})
        (Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) ≠ 0
    rw [show Polynomial.C (univPolyHom (F := F) H.leadingCoeff) =
        coeffAsRatFunc H.leadingCoeff from (coeffAsRatFunc_eq_C _).symm]
    exact liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hmk_factored : Ideal.Quotient.mk (Ideal.span {H_tilde H}) (H_tilde H) =
      Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat ^ (H.natDegree - 1) *
        Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
    calc Ideal.Quotient.mk (Ideal.span {H_tilde H}) (H_tilde H)
        = Ideal.Quotient.mk (Ideal.span {H_tilde H})
            (W_rat ^ (H.natDegree - 1) *
              Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
                (Polynomial.X / W_rat) H) :=
          congrArg (Ideal.Quotient.mk (Ideal.span {H_tilde H})) hHt
      _ = Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat ^ (H.natDegree - 1) *
            Polynomial.eval₂ liftToFunctionField
              (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
          rw [map_mul, map_pow, hpush]
  have hzero_factored :
      (0 : 𝕃 H) =
        Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat ^ (H.natDegree - 1) *
          Polynomial.eval₂ liftToFunctionField
            (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H :=
    hmk_zero.symm.trans hmk_factored
  have hpow_ne : Ideal.Quotient.mk (Ideal.span {H_tilde H}) W_rat ^ (H.natDegree - 1) ≠ 0 :=
    pow_ne_zero _ hmk_W_ne
  exact (mul_eq_zero.mp hzero_factored.symm).resolve_left hpow_ne

/-- If `q ∣ p` in `F[X]`, then `p / q` is regular after embedding into `𝕃`. -/
lemma regularElms_set_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElms_set H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElms_set_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElms_set_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElms_set H := by
  exact regularElms_set_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

private lemma mul_pow_mul_div_pow_eq_lower {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) {k i : ℕ} (hi : i ≤ k) :
    W ^ k * (a * (T / W) ^ i) = a * (T ^ i * W ^ (k - i)) := by
  rw [div_pow]
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  calc
    W ^ k * (a * (T ^ i / W ^ i)) = a * (T ^ i * (W ^ k / W ^ i)) := by
      ring
    _ = a * (T ^ i * W ^ (k - i)) := by
      rw [hk, pow_add]
      field_simp [hW]
      have hsub : k - i + i - i = k - i := by omega
      rw [hsub]

private lemma mul_pow_mul_div_pow_succ_eq_top {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) (k : ℕ) :
    W ^ k * (a * (T / W) ^ (k + 1)) = (a / W) * T ^ (k + 1) := by
  rw [div_pow, pow_succ]
  field_simp [hW]
  ring

/-- Clearing denominators in `W^k · P(T/W)` as an explicit sum: if `P.natDegree ≤ k + 1`, then
`W^k * eval₂ lift (T/W) P` decomposes into a low-degree polynomial sum plus a single
`(P.coeff(k+1)/W) · T^(k+1)` term. The divisibility `W ∣ P.coeff(k+1)` is not needed here -
the formula holds in `𝕃 H` directly via field division. -/
lemma W_pow_mul_eval₂_div_eq_sum {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P =
      (∑ i ∈ Finset.range (k + 1),
          liftToFunctionField (H := H) (P.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (k - i))) +
        (liftToFunctionField (H := H) (P.coeff (k + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ (k + 1) := by
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW_def
  set T : 𝕃 H := functionFieldT (H := H) with hT_def
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le : i ≤ k := by
      have := Finset.mem_range.mp hi; omega
    exact mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le
  · exact mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElms_set_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElms_set_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElms_set H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElms_set_add
    (regularElms_set_mul
      (regularElms_set_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElms_set_functionFieldT H))
    (regularElms_set_liftToFunctionField H (P.coeff 0))

/-- Clearing denominators in `P(T / W)`: if `P` has degree at most `k + 1` and its top
coefficient is divisible by `W = H.leadingCoeff`, then `W^k * P(T/W)` is regular. -/
lemma regularElms_set_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd
    {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1)
    (hdiv : H.leadingCoeff ∣ P.coeff (k + 1)) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElms_set H := by
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  change W ^ k * Polynomial.eval₂ liftToFunctionField (T / W) P ∈ regularElms_set H
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  refine regularElms_set_add ?_ ?_
  · refine regularElms_set_sum (Finset.range (k + 1)) ?_
    intro i hi
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ k := by omega
    rw [mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le]
    exact regularElms_set_mul
      (regularElms_set_liftToFunctionField H (P.coeff i))
      (regularElms_set_mul
        (by simpa [T] using regularElms_set_pow (regularElms_set_functionFieldT H) i)
        (by
          simpa [W] using
            regularElms_set_pow (regularElms_set_liftToFunctionField H H.leadingCoeff) (k - i)))
  · rw [mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k]
    exact regularElms_set_mul
      (by
        simpa [W] using
          regularElms_set_liftToFunctionField_div_leadingCoeff_of_dvd (H := H) hdiv)
      (by simpa [T] using regularElms_set_pow (regularElms_set_functionFieldT H) (k + 1))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- Constructing power series over the function field `𝕃 H` out of a polynomial. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)

@[simp]
lemma coeff_polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) (n : ℕ) :
    PowerSeries.coeff n (polyToPowerSeries𝕃 H P) = liftToFunctionField (P.coeff n) :=
  PowerSeries.coeff_mk n _

/-! ### The `X`-elimination polynomial of Lemma A.1 (recovered)

The following block (`elimPoly` and its three lemmas, together with the helper lemmas
`degree_H_tilde_eq`, `π_z_eq_evalEval_canonicalRep`, `exists_common_root_of_mem_S_β` they depend
on) was wrongly excised by a reconciliation merge. It is restored verbatim from commit `71ab8cc57`
(pre-excision `ce4e2497a^`). The §5 BCIKS20 list-decoding chain (`Extraction → Agreement`)
references `BCIKS20AppendixA.elimPoly`, `elimPoly_ne_zero`, `elimPoly_eval_eq_zero_of_mem_S_β` at
the namespace top level. -/

/-- The degree of `H_tilde H` (over `RatFunc F`) equals the degree of `H_tilde' H` (over `F[X]`). -/
lemma degree_H_tilde_eq {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde H).degree = (H_tilde' H).degree := by
  rw [← H_tilde_equiv_H_tilde', (H_tilde'_monic H hH).degree_map univPolyHom]

/-- The substitution `π_z` evaluated on `β` agrees with evaluating the canonical representative
of `β` at `(z, t_z)`. -/
lemma π_z_eq_evalEval_canonicalRep {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) β = Polynomial.evalEval z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rw [π_z, Ideal.Quotient.lift_mk]
  rfl

/-- Membership in `S_β` extracts, for the canonical representative `P` of `β`, a common root
`(z, t_z)` of `H_tilde' H` and `P` over `F`. -/
lemma exists_common_root_of_mem_S_β {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) {z : F}
    (hz : z ∈ S_β β) :
    ∃ t : F, Polynomial.evalEval z t (H_tilde' H) = 0 ∧
      Polynomial.evalEval z t (canonicalRepOf𝒪 hH β) = 0 := by
  obtain ⟨root, hroot⟩ := hz
  refine ⟨root.1, root.2, ?_⟩
  rw [← π_z_eq_evalEval_canonicalRep hH β z root]
  exact hroot

/-- The `X`-elimination polynomial of Lemma A.1: the `Y`-resultant of `H_tilde' H` with the
canonical representative of `β`, an element of `F[X]`. Its roots contain `S_β`. -/
noncomputable def elimPoly {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X] :=
  Polynomial.resultant (H_tilde' H) (canonicalRepOf𝒪 hH β)
    (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree

/-- Specializing `X := z` commutes with the resultant: `(elimPoly β).eval z` is the resultant over
`F` of the two specialized univariate polynomials in `Y`. -/
lemma eval_elimPoly {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (z : F) :
    (elimPoly hH β).eval z =
      Polynomial.resultant (Polynomial.Bivariate.evalX z (H_tilde' H))
        (Polynomial.Bivariate.evalX z (canonicalRepOf𝒪 hH β))
        (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree := by
  rw [elimPoly, Polynomial.Bivariate.evalX_eq_map, Polynomial.Bivariate.evalX_eq_map,
      Polynomial.resultant_map_map]
  rfl

/-- For `z ∈ S_β`, the elimination polynomial vanishes at `z`. -/
lemma elimPoly_eval_eq_zero_of_mem_S_β {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) {z : F}
    (hz : z ∈ S_β β) :
    (elimPoly hH β).eval z = 0 := by
  classical
  obtain ⟨t, hHt, hPt⟩ := exists_common_root_of_mem_S_β hH β hz
  rw [eval_elimPoly]
  set f := Polynomial.Bivariate.evalX z (H_tilde' H) with hf_def
  set g := Polynomial.Bivariate.evalX z (canonicalRepOf𝒪 hH β) with hg_def
  -- Both specialized polynomials have `t` as a root, so `X - C t` divides each.
  have hf_root : f.IsRoot t := by
    rw [hf_def, Polynomial.Bivariate.evalX_eq_map, Polynomial.IsRoot,
        Polynomial.map_evalRingHom_eval]; exact hHt
  have hg_root : g.IsRoot t := by
    rw [hg_def, Polynomial.Bivariate.evalX_eq_map, Polynomial.IsRoot,
        Polynomial.map_evalRingHom_eval]; exact hPt
  have hdvd_f : (Polynomial.X - Polynomial.C t) ∣ f := Polynomial.dvd_iff_isRoot.mpr hf_root
  have hdvd_g : (Polynomial.X - Polynomial.C t) ∣ g := Polynomial.dvd_iff_isRoot.mpr hg_root
  -- The degree arguments dominate the actual degrees of `f` and `g`.
  have hfle : f.natDegree ≤ (H_tilde' H).natDegree := by
    rw [hf_def, Polynomial.Bivariate.evalX_eq_map]; exact Polynomial.natDegree_map_le
  have hgle : g.natDegree ≤ (canonicalRepOf𝒪 hH β).natDegree := by
    rw [hg_def, Polynomial.Bivariate.evalX_eq_map]; exact Polynomial.natDegree_map_le
  have hmn : (H_tilde' H).natDegree ≠ 0 ∨ (canonicalRepOf𝒪 hH β).natDegree ≠ 0 :=
    Or.inl (by rw [natDegree_H_tilde' hH]; exact Nat.ne_of_gt hH)
  -- By contradiction: if the resultant is nonzero, `X - C t` would divide a nonzero constant.
  by_contra hres
  obtain ⟨p, q, _, _, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hfle hgle hmn
  have hdvd_C : (Polynomial.X - Polynomial.C t) ∣
      Polynomial.C (Polynomial.resultant f g (H_tilde' H).natDegree
        (canonicalRepOf𝒪 hH β).natDegree) := by
    rw [← hpq]; exact dvd_add (hdvd_f.mul_right p) (hdvd_g.mul_right q)
  have hC_ne : Polynomial.C (Polynomial.resultant f g (H_tilde' H).natDegree
      (canonicalRepOf𝒪 hH β).natDegree) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using hres
  have hdeg_le := Polynomial.degree_le_of_dvd hdvd_C hC_ne
  rw [Polynomial.degree_X_sub_C, Polynomial.degree_C
      (by simpa [Polynomial.C_eq_zero] using hres)] at hdeg_le
  exact absurd hdeg_le (by decide)

/-- The elimination polynomial is nonzero. This is where `[Fact (Irreducible H)]` is used: over
`RatFunc F`, `H_tilde H` is irreducible and the (mapped) canonical representative has strictly
smaller `Y`-degree, hence cannot be divisible by `H_tilde H`, so the two are coprime and their
resultant — the image of `elimPoly` under `univPolyHom` — is nonzero. -/
lemma elimPoly_ne_zero {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (β : 𝒪 H) (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    elimPoly hH β ≠ 0 := by
  have hinj : Function.Injective (univPolyHom : F[X] →+* RatFunc F) := by
    rw [univPolyHom]; exact IsFractionRing.injective _ _
  -- Map the resultant down to `RatFunc F`.
  have hmap : univPolyHom (elimPoly hH β) =
      Polynomial.resultant (H_tilde H) ((canonicalRepOf𝒪 hH β).map univPolyHom)
        (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree := by
    rw [elimPoly, ← Polynomial.resultant_map_map, H_tilde_equiv_H_tilde']
  -- The mapped canonical representative is nonzero with `Y`-degree `< H_tilde H`.
  set P' := (canonicalRepOf𝒪 hH β).map univPolyHom with hP'_def
  have hP'_ne : P' ≠ 0 := by
    rw [hP'_def]
    intro hzero
    exact hP (by
      have hmi : Function.Injective (Polynomial.map (univPolyHom : F[X] →+* RatFunc F)) :=
        Polynomial.map_injective _ hinj
      exact hmi (by simpa using hzero))
  have hHt_irr : Irreducible (H_tilde H) := irreducibleHTildeOfIrreducible hH (Fact.out)
  have hdeg_lt : P'.degree < (H_tilde H).degree := by
    rw [hP'_def]
    refine lt_of_le_of_lt Polynomial.degree_map_le ?_
    rw [degree_H_tilde_eq hH]
    exact canonicalRepOf𝒪_degree_lt hH β
  -- `H_tilde H` does not divide `P'` (degree), so they are coprime.
  have hnotdvd : ¬ (H_tilde H ∣ P') := fun hdvd =>
    absurd (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg_lt) hP'_ne
  have hcop : IsCoprime (H_tilde H) P' :=
    (dvd_or_isCoprime _ _ hHt_irr).resolve_left hnotdvd
  have hres_ne : Polynomial.resultant (H_tilde H) P'
      (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree ≠ 0 := by
    have hcop' : IsCoprime (H_tilde H) P' := hcop
    -- `resultant_ne_zero` uses default degrees; rewrite to the right degree arguments.
    -- (`natDegree_H_tilde` was excised; derive the natDegree equality from `degree_H_tilde_eq`.)
    have hHd : (H_tilde H).natDegree = (H_tilde' H).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (degree_H_tilde_eq hH)
    have hPd : P'.natDegree = (canonicalRepOf𝒪 hH β).natDegree := by
      rw [hP'_def, Polynomial.natDegree_map_eq_of_injective hinj]
    have := Polynomial.resultant_ne_zero (H_tilde H) P' hcop'
    rwa [hHd, hPd] at this
  intro hzero
  apply hres_ne
  rw [← hmap, hzero, map_zero]

end


noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (0 < H.natDegree)]

/-- The algebraic hypotheses for Claim A.2 from Appendix A.4 of [BCIKS20], after specializing
`R` at `X = x₀`. -/
structure Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : Prop where
  dvd_evalX : H ∣ Bivariate.evalX (Polynomial.C x₀) R
  separable_evalX : (Bivariate.evalX (Polynomial.C x₀) R).Separable

private lemma evalX_natDegree_le {K : Type} [CommSemiring K] (x : K) (P : K[X][Y]) :
    (Bivariate.evalX x P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hcoeff : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]

/-- The leading coefficient `W` of `H` divides the leading coefficient of `R(x₀,Y,Z)`. -/
lemma leadingCoeff_dvd_evalX_leadingCoeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := by
  rcases hHyp.dvd_evalX with ⟨q, hq⟩
  refine ⟨q.leadingCoeff, ?_⟩
  calc
    (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = (H * q).leadingCoeff := by rw [hq]
    _ = H.leadingCoeff * q.leadingCoeff := Polynomial.leadingCoeff_mul H q

/-- The leading coefficient `W` of `H` divides the coefficient of `Y ^ R.natDegree` in
`R(x₀,Y,Z)`. If specialization lowers the `Y`-degree, that coefficient is zero. -/
lemma leadingCoeff_dvd_evalX_coeff_natDegree {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  have hdeg : P.natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
  by_cases hEq : P.natDegree = R.natDegree
  · simpa [P, hEq.symm] using leadingCoeff_dvd_evalX_leadingCoeff hHyp
  · have hlt : P.natDegree < R.natDegree := lt_of_le_of_ne hdeg hEq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact dvd_zero H.leadingCoeff

/-- The leading coefficient `W` of `H` divides the top possible coefficient of
`∂R/∂Y(x₀,Y,Z)`. This is the coefficient that remains after multiplying `ζ` by `W^(d-2)`. -/
lemma leadingCoeff_dvd_evalX_derivative_coeff_pred {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) := by
  by_cases hR : R.natDegree = 0
  · have hderiv : R.derivative = 0 := Polynomial.derivative_of_natDegree_zero hR
    rw [hderiv]
    exact ⟨0, by simp [Bivariate.evalX_eq_map]⟩
  · have hsucc : R.natDegree - 1 + 1 = R.natDegree :=
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hR)
    have hsucc_cast : (((R.natDegree - 1 : ℕ) : F[X][X]) + 1) =
        (R.natDegree : F[X][X]) := by
      rw [← Nat.cast_one (R := F[X][X])]
      rw [← Nat.cast_add, hsucc]
    have hcoeff :
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
      calc
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
            ((R.derivative).coeff (R.natDegree - 1)).eval (Polynomial.C x₀) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        _ = (R.coeff R.natDegree * (R.natDegree : F[X][X])).eval (Polynomial.C x₀) := by
          rw [Polynomial.coeff_derivative, hsucc, hsucc_cast]
        _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
    refine ⟨q * (R.natDegree : F[X]), ?_⟩
    rw [hcoeff, hq]
    ring

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := functionFieldT (H := H);
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- The `X`-specialization commutes with the `Y`-derivative. -/
lemma evalX_derivative_comm (x₀ : F) (p : F[X][X][Y]) :
    Bivariate.evalX (Polynomial.C x₀) p.derivative =
      (Bivariate.evalX (Polynomial.C x₀) p).derivative := by
  rw [Bivariate.evalX_eq_map, Bivariate.evalX_eq_map, Polynomial.derivative_map]

/-- The coefficient of `Y^n` in `∂R/∂Y(x₀,Z)` is `(n+1) · (R(x₀,Z)).coeff (n+1)`, so its
`X`-degree is bounded by `D - (n+1)` when `D` bounds the total degree of `R(x₀,Z)`. -/
lemma natDegree_evalX_derivative_coeff_le {x₀ : F} {R : F[X][X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) (n : ℕ) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff n).natDegree ≤ D - (n + 1) := by
  have hcoeff :
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff n =
        ((n + 1 : ℕ) : F[X]) * (Bivariate.evalX (Polynomial.C x₀) R).coeff (n + 1) := by
    rw [evalX_derivative_comm, Polynomial.coeff_derivative]
    push_cast
    ring
  rw [hcoeff]
  calc (((n + 1 : ℕ) : F[X]) * (Bivariate.evalX (Polynomial.C x₀) R).coeff (n + 1)).natDegree
      ≤ ((Bivariate.evalX (Polynomial.C x₀) R).coeff (n + 1)).natDegree := by
        rw [← nsmul_eq_mul]
        exact Polynomial.natDegree_smul_le _ _
    _ ≤ D - (n + 1) := natDegree_coeff_le_of_totalDegree_le _ hD (n + 1)

/-- The product-rule factorization of `ζ` at the root `α₀ = T/W`: writing `Q = R(x₀,·) = H · g`
with `g` the cofactor of the factor `H`, the Y-derivative product rule evaluated at `α₀` gives
`ζ = H'_Y(α₀) · g(α₀)`, since the `H(α₀) · g'_Y(α₀)` term vanishes (`H(α₀) = 0`).
This is the structural identity of Claim A.2 in Appendix A.4 of [BCIKS20]. -/
lemma ζ_eq_evalα₀_derivative_mul (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {g : F[X][Y]} (hg : Bivariate.evalX (Polynomial.C x₀) R = H * g) :
    ζ R x₀ H =
      Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H.derivative *
        Polynomial.eval₂ liftToFunctionField
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) g := by
  set α₀ : 𝕃 H := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff with hα₀
  -- `eval₂` at `α₀` is the ring hom `evalα₀`.
  let evalα₀ : F[X][Y] →+* 𝕃 H := Polynomial.eval₂RingHom liftToFunctionField α₀
  have heval (p : F[X][Y]) : Polynomial.eval₂ liftToFunctionField α₀ p = evalα₀ p := rfl
  -- `ζ = evalα₀ (Q.derivative)` with `Q = H * g`.
  have hζ : ζ R x₀ H = evalα₀ (Bivariate.evalX (Polynomial.C x₀) R).derivative := by
    rw [ζ, ← evalX_derivative_comm, ← hα₀, heval]
  rw [hζ, hg, Polynomial.derivative_mul, map_add, map_mul, map_mul]
  -- The `H(α₀)` factor vanishes by the root lemma.
  have hH0 : evalα₀ H = 0 := by
    rw [← heval, hα₀]
    exact eval₂_liftToFunctionField_div_leadingCoeff_H_eq_zero (H := H)
  rw [hH0, zero_mul, add_zero, heval, heval]

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElms_set H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElms_set_liftToFunctionField H p

/-- If `R` has `Y`-degree at most one, then the specialized derivative is constant. -/
lemma derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (hR : R.natDegree ≤ 1) :
    ∃ p : F[X], Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  refine ⟨P.coeff 0, ?_⟩
  have hderiv : R.derivative.natDegree ≤ 0 := by
    calc
      R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 0 := by omega
  have hP : P.natDegree ≤ 0 :=
    (evalX_natDegree_le (Polynomial.C x₀) R.derivative).trans hderiv
  exact Polynomial.eq_C_of_natDegree_le_zero hP

/-- In the constant-derivative, low-`Y`-degree case, the `ξ` regularity witness is explicit. -/
lemma ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p)
    (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases ζ_regular_of_derivative_evalX_eq_C x₀ R H hp with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- If `R` has `Y`-degree at most one, the regularity statement for `ξ` follows from the
constant-derivative case. -/
lemma ξ_regular_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hR with ⟨p, hp⟩
  exact ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one x₀ R H hp hR

/-- In the quadratic case, `ξ = ζ` is regular by clearing the single denominator with the
divisibility of the top derivative coefficient. -/
lemma ξ_regular_of_natDegree_eq_two
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hR : R.natDegree = 2) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  have hP : P.natDegree ≤ 1 := by
    calc
      P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le (Polynomial.C x₀) R.derivative
      _ ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 1 := by omega
  have hdiv : H.leadingCoeff ∣ P.coeff 1 := by
    simpa [P, hR] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hreg : ζ R x₀ H ∈ regularElms_set H := by
    simpa [ζ, P] using regularElms_set_eval₂_linear_of_coeff_one_dvd (H := H) hP hdiv
  rcases hreg with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- Explicit polynomial representative for the regular element `ξ = W^(d-2) · ζ` of Claim A.2.
For `2 ≤ R.natDegree`, this is the polynomial obtained by clearing the single denominator that
appears in `W^(d-2) · ζ`; the divisibility `W ∣ R'(x₀, Z)_{d-1}` is captured implicitly by
Euclidean division in `F[X]`. For `R.natDegree ≤ 1`, the derivative specialization is constant
in `Y`, so we take it as the representative. -/
noncomputable def ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  if 2 ≤ d then
    (∑ i ∈ Finset.range (d - 1),
        Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i) +
      Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)
  else
    P

/-- The image of `⟦ξ_pre⟧` in the function field equals `W^(d-2) · ζ`, matching Claim A.2's
algebraic identity. -/
lemma embeddingOf𝒪Into𝕃_mk_ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (ξ_pre x₀ R H) : 𝒪 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H := by
  rw [embeddingOf𝒪Into𝕃_mk]
  by_cases hRle : R.natDegree ≤ 1
  · -- d ≤ 1: ξ_pre = R'(x₀, Z), constant in Y; ζ is the lift of that constant.
    rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hRle with ⟨p, hp⟩
    have hd2 : R.natDegree - 2 = 0 := by omega
    have hbranch : ¬ 2 ≤ R.natDegree := by omega
    have hξ_pre : ξ_pre x₀ R H = Polynomial.C p := by
      simp [ξ_pre, hbranch, hp]
    rw [hξ_pre, hd2, pow_zero, one_mul, liftBivariate_C]
    change liftToFunctionField (H := H) p =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Bivariate.evalX (Polynomial.C x₀) R.derivative)
    rw [hp, Polynomial.eval₂_C]
  · have hd2 : 2 ≤ R.natDegree := by omega
    set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hP_def
    set W_poly : F[X] := H.leadingCoeff with hW_poly_def
    have hkk : R.natDegree - 1 = R.natDegree - 2 + 1 := by omega
    have hP_le : P.natDegree ≤ R.natDegree - 2 + 1 := by
      have h1 : P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le _ R.derivative
      have h2 : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      omega
    have hdiv : W_poly ∣ P.coeff (R.natDegree - 2 + 1) := by
      have h := leadingCoeff_dvd_evalX_derivative_coeff_pred (H := H) hHyp
      rwa [hkk] at h
    have hW_poly_ne : W_poly ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    have hW_ne : (liftToFunctionField (H := H) W_poly : 𝕃 H) ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hξ_pre_eq : ξ_pre x₀ R H =
        (∑ i ∈ Finset.range (R.natDegree - 2 + 1),
            Polynomial.C (P.coeff i * W_poly ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) +
          Polynomial.C (P.coeff (R.natDegree - 2 + 1) / W_poly) *
            Polynomial.X ^ (R.natDegree - 2 + 1) := by
      simp only [ξ_pre, hd2, ↓reduceIte, ← hP_def, ← hW_poly_def, hkk]
    rw [hξ_pre_eq]
    rw [show (ζ R x₀ H : 𝕃 H) =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) W_poly) P from rfl]
    rw [W_pow_mul_eval₂_div_eq_sum (H := H) (P := P) (k := R.natDegree - 2) hP_le]
    have hlift_div :
        liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1) / W_poly) =
          liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1)) /
            liftToFunctionField (H := H) W_poly := by
      rw [eq_div_iff hW_ne, ← map_mul, mul_comm,
          EuclideanDomain.mul_div_cancel' hW_poly_ne hdiv]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C, liftBivariate_X, hlift_div]
    refine congr_arg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H :=
  ⟨Ideal.Quotient.mk _ (ξ_pre x₀ R H),
    by simpa using embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp⟩

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20].
The `Fact` and `Hypotheses` arguments are kept for API compatibility with downstream callers
(`α`, `γ`); they are needed for the embedding equation in `embeddingOf𝒪Into𝕃_ξ`. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [_φ : Fact (Irreducible H)]
    [_H_natDegree_pos : Fact (0 < H.natDegree)] (_hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  Ideal.Quotient.mk _ (ξ_pre x₀ R H)

/-- The defining equation `embedding ξ = W^(d-2) · ζ`, the specialization of
`embeddingOf𝒪Into𝕃_mk_ξ_pre` to `ξ`. -/
lemma embeddingOf𝒪Into𝕃_ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H :=
  embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp

/-! ### Coefficient structure for `weight_ξ_bound`

Helper lemmas establishing the explicit coefficients of `H_tilde' H` and `ξ_pre`, used in the
proof of `weight_ξ_bound`. -/

/-- For `i < H.natDegree`, the `i`-th coefficient of `H_tilde' H` is
`H.coeff i * H.leadingCoeff ^ (d_H - 1 - i)`. -/
lemma H_tilde'_coeff_of_lt {H : F[X][Y]} (hH : 0 < H.natDegree) {i : ℕ}
    (hi : i < H.natDegree) :
    (H_tilde' H).coeff i = H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i) := by
  classical
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  rw [Polynomial.coeff_add]
  have hXpow : (Polynomial.X ^ H.natDegree : F[X][Y]).coeff i = 0 := by
    rw [Polynomial.coeff_X_pow]
    rw [if_neg (by omega)]
  rw [hXpow, zero_add]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    rfl
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
  · intro hi_mem
    exact absurd (Finset.mem_range.mpr hi) hi_mem

/-- For `i < H.natDegree`, the `natDegree` of the `i`-th coefficient of `H_tilde' H` is bounded by
`(totalDegree H - i) + (d_H - 1 - i) · natDegree W`, where `W = H.leadingCoeff`. -/
lemma natDegree_H_tilde'_coeff_le {H : F[X][Y]} (hH : 0 < H.natDegree) {i : ℕ}
    (hi : i < H.natDegree) :
    ((H_tilde' H).coeff i).natDegree ≤
      (Bivariate.totalDegree H - i) +
        (H.natDegree - 1 - i) * (H.leadingCoeff).natDegree := by
  rw [H_tilde'_coeff_of_lt hH hi]
  calc (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i)).natDegree
      ≤ (H.coeff i).natDegree + (H.leadingCoeff ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (Bivariate.totalDegree H - i) + (H.natDegree - 1 - i) * (H.leadingCoeff).natDegree := by
        refine Nat.add_le_add (natDegree_coeff_le_of_totalDegree_le H le_rfl i) ?_
        exact Polynomial.natDegree_pow_le

/-- The specialized polynomial `Q = R(x₀, ·)` is nonzero, since it is separable (and `0` is not
separable: `derivative 0 = 0` is not coprime to `0` in a nontrivial ring). -/
lemma evalX_ne_zero_of_hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := by
  intro h0
  have hsep := hHyp.separable_evalX
  rw [h0] at hsep
  -- `(0 : F[X][Y]).Separable` is `IsCoprime 0 0`, impossible in a nontrivial comm ring.
  rw [Polynomial.Separable, derivative_zero] at hsep
  exact not_isCoprime_zero_zero hsep

/-- In the `2 ≤ d` regime, the explicit coefficients of `ξ_pre`. For `i < d - 1` the coefficient
is `P.coeff i * W^(d-2-i)`; at `i = d - 1` it is `P.coeff (d-1) / W`; for `i ≥ d` it vanishes. Here
`P = R'(x₀, ·)` and `W = H.leadingCoeff`. -/
lemma ξ_pre_coeff_of_lt {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} (hd : 2 ≤ R.natDegree) {i : ℕ}
    (hi : i < R.natDegree - 1) :
    (ξ_pre x₀ R H).coeff i =
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
        H.leadingCoeff ^ (R.natDegree - 2 - i) := by
  classical
  rw [ξ_pre]
  simp only [hd, ↓reduceIte]
  rw [Polynomial.coeff_add]
  have htop : (Polynomial.C
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
        H.leadingCoeff) * Polynomial.X ^ (R.natDegree - 1) : F[X][Y]).coeff i = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  rw [htop, add_zero]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
  · intro hi_mem
    exact absurd (Finset.mem_range.mpr hi) hi_mem

/-- The top coefficient of `ξ_pre` (at index `d - 1`) in the `2 ≤ d` regime. -/
lemma ξ_pre_coeff_top {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} (hd : 2 ≤ R.natDegree) :
    (ξ_pre x₀ R H).coeff (R.natDegree - 1) =
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
        H.leadingCoeff := by
  classical
  rw [ξ_pre]
  simp only [hd, ↓reduceIte]
  rw [Polynomial.coeff_add]
  have hsum : (∑ i ∈ Finset.range (R.natDegree - 1),
      Polynomial.C ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
        H.leadingCoeff ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i :
        F[X][Y]).coeff (R.natDegree - 1) = 0 := by
    rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by
      have := Finset.mem_range.mp hb; omega), mul_zero]
  rw [hsum, zero_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]

/-- In the `2 ≤ d` regime, `ξ_pre` has `Y`-degree at most `d - 1`. -/
lemma natDegree_ξ_pre_le {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} (hd : 2 ≤ R.natDegree) :
    (ξ_pre x₀ R H).natDegree ≤ R.natDegree - 1 := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hn1 : n = R.natDegree - 1
  · subst hn1; omega
  · by_cases hn_lt : n < R.natDegree - 1
    · omega
    · -- n > R.natDegree - 1 and n ≠ R.natDegree - 1: coeff vanishes
      rw [ξ_pre]
      simp only [hd, ↓reduceIte]
      rw [Polynomial.coeff_add, Polynomial.finset_sum_coeff]
      rw [Finset.sum_eq_zero (fun b hb => ?_), zero_add,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_neg (by have := Finset.mem_range.mp hb; omega), mul_zero]

/-- The cofactor degree bound that powers `weight_ξ_bound`'s tight top-coefficient analysis:
writing `Q = R(x₀,·) = H · g`, the `Y`-leading coefficient of `ξ_pre` (after clearing the single
denominator `W`) has `X`-degree bounded by the `X`-degree of `g`'s `Y`-leading coefficient.

Concretely `ξ_pre.coeff (d-1) = d · g.coeff (d - d_H)` up to the `Y^d` coefficient of `Q`, so its
`X`-degree is at most `(g.coeff (d - d_H)).natDegree`. -/
lemma natDegree_ξ_pre_coeff_top_le {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hd : 2 ≤ R.natDegree)
    {g : F[X][Y]} (hg : Bivariate.evalX (Polynomial.C x₀) R = H * g) :
    ((ξ_pre x₀ R H).coeff (R.natDegree - 1)).natDegree ≤
      (g.coeff (R.natDegree - H.natDegree)).natDegree := by
  classical
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hQ_def
  set W : F[X] := H.leadingCoeff with hW_def
  have hQ_ne : Q ≠ 0 := evalX_ne_zero_of_hypotheses hHyp
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out
  have hg_ne : g ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hg; exact hQ_ne hg
  have hW_ne : W ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  -- Top coefficient of ξ_pre.
  rw [ξ_pre_coeff_top hd]
  -- `W ∣ P.coeff (d-1)`, and `P.coeff (d-1) = Q.coeff d * d`.
  have hPcoeff : (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
      Q.coeff R.natDegree * (R.natDegree : F[X]) := by
    have hsucc : R.natDegree - 1 + 1 = R.natDegree := by omega
    rw [evalX_derivative_comm, Polynomial.coeff_derivative, ← hQ_def]
    rw [show ((R.natDegree - 1 : ℕ) : F[X]) + 1 = (R.natDegree : F[X]) by
          rw [← Nat.cast_one (R := F[X]), ← Nat.cast_add, hsucc]]
    rw [hsucc]
  -- `Q.coeff d`: if `d > natDegree Q` it's 0; else it's the leading coefficient.
  by_cases hdeg : R.natDegree ≤ Q.natDegree
  · -- `natDegree Q = d` (since `natDegree Q ≤ natDegree R = d`).
    have hQdeg_le : Q.natDegree ≤ R.natDegree := by
      rw [hQ_def]; exact evalX_natDegree_le (Polynomial.C x₀) R
    have hQdeg : Q.natDegree = R.natDegree := le_antisymm hQdeg_le hdeg
    -- `Q.coeff d = leadingCoeff Q = W · g.leadingCoeff`.
    have hlead : Q.coeff R.natDegree = W * g.leadingCoeff := by
      rw [← hQdeg, ← Polynomial.leadingCoeff, hg, Polynomial.leadingCoeff_mul, hW_def]
    -- `g.leadingCoeff = g.coeff (d - d_H)`.
    have hdg : g.natDegree = R.natDegree - H.natDegree := by
      have hmul : Q.natDegree = H.natDegree + g.natDegree := by
        rw [hg, Polynomial.natDegree_mul hH_ne hg_ne]
      omega
    -- `ξ_pre.coeff (d-1) = P.coeff (d-1) / W = (Q.coeff d · d) / W = g.leadingCoeff · d`.
    have hquot : (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) / W =
        g.leadingCoeff * (R.natDegree : F[X]) := by
      rw [hPcoeff, hlead]
      rw [show W * g.leadingCoeff * (R.natDegree : F[X]) =
            g.leadingCoeff * (R.natDegree : F[X]) * W by ring]
      exact mul_div_cancel_right₀ _ hW_ne
    rw [hquot, Polynomial.leadingCoeff, hdg]
    exact (Polynomial.natDegree_mul_le).trans (by
      rw [Polynomial.natDegree_natCast]; omega)
  · -- `d > natDegree Q`, so `Q.coeff d = 0`, hence ξ_pre.coeff (d-1) = 0.
    rw [not_le] at hdeg
    have hQc : Q.coeff R.natDegree = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    have h0 : (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) / W = 0 := by
      rw [hPcoeff, hQc]; simp
    rw [h0, Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- In the degenerate regime `d_H = d` (cofactor `g` constant in `Y`), separability of
`Q = R(x₀,·)` forces the cofactor's constant term to be a unit of `F[X]`, so the `Y`-leading
coefficient of `ξ_pre` is itself a constant (`natDegree` zero). This is the structural fact that
keeps the tight `d_H = d` case of `weight_ξ_bound` within budget. -/
lemma natDegree_ξ_pre_coeff_top_eq_zero_of_natDegree_eq {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hd : 2 ≤ R.natDegree)
    {g : F[X][Y]} (hg : Bivariate.evalX (Polynomial.C x₀) R = H * g)
    (hdH : H.natDegree = R.natDegree) :
    ((ξ_pre x₀ R H).coeff (R.natDegree - 1)).natDegree = 0 := by
  classical
  have hbound := natDegree_ξ_pre_coeff_top_le hHyp hd hg
  rw [hdH, Nat.sub_self] at hbound
  -- It remains to show `(g.coeff 0).natDegree = 0`, i.e. `g.coeff 0` is a unit.
  -- `g.natDegree = 0`, so `g` is constant in `Y`: `g = C (g.coeff 0)`.
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hQ_def
  have hQ_ne : Q ≠ 0 := evalX_ne_zero_of_hypotheses hHyp
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out
  have hg_ne : g ≠ 0 := by intro h0; rw [h0, mul_zero] at hg; exact hQ_ne hg
  have hg_natDeg : g.natDegree = 0 := by
    have hQdeg_le : Q.natDegree ≤ R.natDegree := by
      rw [hQ_def]; exact evalX_natDegree_le (Polynomial.C x₀) R
    have hmul : Q.natDegree = H.natDegree + g.natDegree := by
      rw [hg, Polynomial.natDegree_mul hH_ne hg_ne]
    omega
  -- `C g₀ ∣ Q` and `C g₀ ∣ Q'`, so it divides 1 by coprimality.
  set g₀ : F[X] := g.coeff 0 with hg₀_def
  have hg_eq : g = Polynomial.C g₀ := Polynomial.eq_C_of_natDegree_eq_zero hg_natDeg
  have hQ_eq : Q = H * Polynomial.C g₀ := by rw [hg, hg_eq]
  have hsep : Q.Separable := hHyp.separable_evalX
  rw [Polynomial.Separable] at hsep
  have hdvd_Q : Polynomial.C g₀ ∣ Q := by
    rw [hQ_eq]; exact Dvd.intro_left H rfl
  have hdvd_Q' : Polynomial.C g₀ ∣ Q.derivative := by
    rw [hQ_eq, Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero]
    exact Dvd.intro_left H.derivative rfl
  have hunit : IsUnit (Polynomial.C g₀) := hsep.isUnit_of_dvd' hdvd_Q hdvd_Q'
  have hunit_g0 : IsUnit g₀ := Polynomial.isUnit_C.mp hunit
  have hg0 : g₀.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit_g0
  omega

/-- The per-monomial budget bound for the lower coefficients of `ξ_pre` (indices `< d - 1`):
`n · m + (ξ_pre.coeff n).natDegree ≤ (d - 1) · m`, where `m = D + 1 - d_H`. The margin is
`d - d_H ≥ 0`, which holds because `H ∣ R(x₀,·)` forces `d_H ≤ d`. -/
lemma ξ_pre_lower_budget {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} {D : ℕ}
    (hd : 2 ≤ R.natDegree) (hH : 0 < H.natDegree) (hdH_le : H.natDegree ≤ R.natDegree)
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    {n : ℕ} (hn : n < R.natDegree - 1) :
    n * (D + 1 - H.natDegree) + ((ξ_pre x₀ R H).coeff n).natDegree ≤
      (R.natDegree - 1) * (D + 1 - H.natDegree) := by
  -- ξ_pre.coeff n = P.coeff n * W^(d-2-n)
  rw [ξ_pre_coeff_of_lt hd hn]
  set d := R.natDegree with hd_def
  set dH := H.natDegree with hdH_def
  set w := (H.leadingCoeff).natDegree with hw_def
  have hPbound : ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff n).natDegree ≤
      D - (n + 1) := natDegree_evalX_derivative_coeff_le hD_Rx0 n
  have hdH_le_D : dH ≤ D := by
    have hH_in : dH ∈ H.support :=
      Polynomial.mem_support_iff.mpr
        (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hH))
    have := Bivariate.coeff_totalDegree_le H hH_in
    omega
  have hWbound : w ≤ D - dH := by
    have h1 : (H.coeff dH).natDegree ≤ Bivariate.totalDegree H - dH :=
      natDegree_coeff_le_of_totalDegree_le H le_rfl dH
    have h2 : (H.coeff dH).natDegree = w := by rw [hw_def, Polynomial.leadingCoeff, ← hdH_def]
    omega
  -- natDeg(P.coeff n · W^(d-2-n)) ≤ (D-(n+1)) + (d-2-n)·w
  have hcoeff_bound :
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff n *
        H.leadingCoeff ^ (d - 2 - n)).natDegree ≤ (D - (n + 1)) + (d - 2 - n) * w := by
    refine Polynomial.natDegree_mul_le.trans ?_
    exact Nat.add_le_add hPbound (Polynomial.natDegree_pow_le.trans (by rw [hw_def]))
  refine (Nat.add_le_add_left hcoeff_bound _).trans ?_
  -- numeric inequality: n·m + (D-(n+1)) + (d-2-n)·w ≤ (d-1)·m, m = D+1-dH.
  -- Substitution off = d-1-n ≥ 1; m = e+1 with e = D-dH; w ≤ e.  Margin = d - dH ≥ 0.
  obtain ⟨off, hoff⟩ : ∃ off, d - 1 = n + 1 + off := ⟨d - 2 - n, by omega⟩
  have hdne : d - 2 - n = off := by omega
  rw [hdne] at hcoeff_bound ⊢
  rw [hoff]
  -- Goal: n*(D+1-dH) + ((D-(n+1)) + off*w) ≤ (n+1+off)*(D+1-dH)
  set e := D - dH with he_def
  have hmw : w ≤ e := by omega
  have hme : D + 1 - dH = e + 1 := by omega
  rw [hme]
  have hDsub : D - (n + 1) ≤ e + 1 + off := by omega
  have hprod : off * w ≤ off * e := Nat.mul_le_mul_left _ hmw
  have hexp : (n + 1 + off) * (e + 1) = n * (e + 1) + (e + 1) + (off * e + off) := by ring
  rw [hexp]
  omega

/-- The pure-arithmetic core of `sub_term_budget`: with `w ≤ D - d_H`, `t_H + t_g ≤ D`,
`w + d_H ≤ t_H` (the leading-coefficient degree bound), `i < d_H`, `d_H < d` and
`n = i + (d-1-d_H)`, one has `n·m + ((t_g - (d-d_H)) + ((t_H - i) + (d_H-1-i)·w)) ≤ (d-1)·m`
for `m = D + 1 - d_H`. The margin is `d - d_H ≥ 1`. -/
lemma numeric_sub_budget (D d dH i n w tH tg : ℕ)
    (hwH : w + dH ≤ tH) (hwD : w ≤ D - dH) (htot : tH + tg ≤ D) (htH : tH ≤ D)
    (hi_lt : i < dH) (hdH_lt : dH < d) (hn_eq : n = i + (d - 1 - dH)) (hdH_le_D : dH ≤ D) :
    n * (D + 1 - dH) + ((tg - (d - dH)) + ((tH - i) + (dH - 1 - i) * w)) ≤
      (d - 1) * (D + 1 - dH) := by
  -- off = dH - i ≥ 1, and d - 1 - n = off; m = D+1-dH.
  obtain ⟨off, hoff⟩ : ∃ off, dH = i + 1 + off := ⟨dH - 1 - i, by omega⟩
  have hd1n : d - 1 = n + (off + 1) := by omega
  have hwe : (dH - 1 - i) = off := by omega
  rw [hwe]
  rw [show (d - 1) * (D + 1 - dH) = (n + (off + 1)) * (D + 1 - dH) by rw [hd1n]]
  rw [show (n + (off + 1)) * (D + 1 - dH) =
        n * (D + 1 - dH) + (off + 1) * (D + 1 - dH) by ring]
  -- need: (tg-(d-dH)) + ((tH-i) + off*w) ≤ (off+1)*(D+1-dH)
  refine Nat.add_le_add_left ?_ _
  -- bound each: tg-(d-dH) ≤ D - tH - (d-dH) ... use htot; tH - i ≤ D - i;
  -- off*w ≤ off*(D-dH). (off+1)*(D+1-dH) = (off+1)*(D-dH) + (off+1).
  have hprodw : off * w ≤ off * (D - dH) := Nat.mul_le_mul_left _ hwD
  have hexp : (off + 1) * (D + 1 - dH) = off * (D - dH) + (D - dH) + (off + 1) := by
    rw [show D + 1 - dH = (D - dH) + 1 by omega]; ring
  rw [hexp]
  -- Bound `(tg-(d-dH)) + (tH-i) ≤ (D-dH) + 1 + off`, since `tg ≤ D - tH` and `i+1+off = dH`.
  have hkey : (tg - (d - dH)) + (tH - i) ≤ (D - dH) + (off + 1) := by omega
  omega

/-- The per-monomial budget bound for the subtracted correction term
`C(lc)·X^(d-1-d_H)·H_tilde' H` of the `weight_ξ_bound` representative
(`lc = ξ_pre.coeff (d-1)`).
For each `n < d - 1`, `n · m + (sub.coeff n).natDegree ≤ (d - 1) · m`. The cofactor identity
(`natDegree lc ≤ natDegree (g.coeff (d - d_H))`) is what keeps the cross terms in budget. -/
lemma sub_term_budget {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_natDegree_pos : Fact (0 < H.natDegree)] {D : ℕ}
    (hHyp : Hypotheses x₀ R H) (hd : 2 ≤ R.natDegree) (hH : 0 < H.natDegree)
    (hdH_lt : H.natDegree < R.natDegree)
    (hD_H : Bivariate.totalDegree H ≤ D)
    {g : F[X][Y]} (hg : Bivariate.evalX (Polynomial.C x₀) R = H * g)
    (htot : Bivariate.totalDegree H + Bivariate.totalDegree g ≤ D)
    {n : ℕ} (hn : n < R.natDegree - 1) :
    n * (D + 1 - H.natDegree) +
        ((Polynomial.C ((ξ_pre x₀ R H).coeff (R.natDegree - 1)) *
            Polynomial.X ^ (R.natDegree - 1 - H.natDegree) * H_tilde' H).coeff n).natDegree ≤
      (R.natDegree - 1) * (D + 1 - H.natDegree) := by
  classical
  set d := R.natDegree with hd_def
  set dH := H.natDegree with hdH_def
  set k := d - 1 - dH with hk_def
  set lc := (ξ_pre x₀ R H).coeff (d - 1) with hlc_def
  set w := (H.leadingCoeff).natDegree with hw_def
  set tH := Bivariate.totalDegree H with htH_def
  set tg := Bivariate.totalDegree g with htg_def
  -- The subtracted polynomial's coefficient at `n`.
  have hcoeff_eq :
      (Polynomial.C lc * Polynomial.X ^ k * H_tilde' H).coeff n =
        (if k ≤ n then lc * (H_tilde' H).coeff (n - k) else 0) := by
    rw [show (Polynomial.C lc * Polynomial.X ^ k * H_tilde' H : F[X][Y]) =
           Polynomial.C lc * (H_tilde' H * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  rw [hcoeff_eq]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    -- i = n - k < dH, so H_tilde'.coeff i = H.coeff i * W^(dH-1-i).
    set i := n - k with hi_def
    have hi_lt : i < dH := by omega
    -- natDeg(lc) ≤ natDeg(g.coeff (d - dH))
    have hlc_bound : lc.natDegree ≤ (g.coeff (d - dH)).natDegree :=
      natDegree_ξ_pre_coeff_top_le hHyp hd hg
    -- natDeg(g.coeff (d - dH)) ≤ tg - (d - dH)
    have hg_coeff : (g.coeff (d - dH)).natDegree ≤ tg - (d - dH) := by
      rw [htg_def]; exact natDegree_coeff_le_of_totalDegree_le g le_rfl (d - dH)
    -- natDeg(H_tilde'.coeff i) ≤ (tH - i) + (dH-1-i)*w
    have hHt_bound : ((H_tilde' H).coeff i).natDegree ≤ (tH - i) + (dH - 1 - i) * w := by
      rw [htH_def, hw_def, hdH_def]
      exact natDegree_H_tilde'_coeff_le hH hi_lt
    -- natDeg(lc * H_tilde'.coeff i) ≤ natDeg(lc) + natDeg(H_tilde'.coeff i)
    have hmul : (lc * (H_tilde' H).coeff i).natDegree ≤
        (tg - (d - dH)) + ((tH - i) + (dH - 1 - i) * w) := by
      refine Polynomial.natDegree_mul_le.trans ?_
      exact Nat.add_le_add (hlc_bound.trans hg_coeff) hHt_bound
    refine (Nat.add_le_add_left hmul _).trans ?_
    -- numeric: n*m + (tg-(d-dH)) + (tH-i) + (dH-1-i)*w ≤ (d-1)*m, m=D+1-dH.
    -- with i = n-k, k=d-1-dH, so n = i + (d-1-dH), d-1-n = dH - i.
    have hwH : w + dH ≤ tH := by
      have h1 : (H.coeff dH).natDegree + dH ≤ Bivariate.totalDegree H :=
        Bivariate.coeff_totalDegree_le H
          (Polynomial.mem_support_iff.mpr
            (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hH)))
      have h2 : (H.coeff dH).natDegree = w := by rw [hw_def, Polynomial.leadingCoeff, ← hdH_def]
      rw [htH_def]; omega
    have htH_le_D : tH ≤ D := hD_H
    have hdH_le_D : dH ≤ D := by omega
    have hwD : w ≤ D - dH := by omega
    have hn_eq : n = i + (d - 1 - dH) := by omega
    exact numeric_sub_budget D d dH i n w tH tg hwH hwD htot htH_le_D hi_lt hdH_lt hn_eq hdH_le_D
  · rw [if_neg hkn, Polynomial.natDegree_zero, add_zero]
    -- 0 contribution: n*m ≤ (d-1)*m since n < d-1.
    exact Nat.mul_le_mul_right _ (by omega)

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20].

The hypothesis `2 ≤ natDegreeY R` is required: the paper's `ξ = W^(d-2)·ζ` lives in the
regime `d ≥ 2`, and the statement is false at `d = 1` (e.g. `H = C(Z)·Y + 1` with
`R(x₀,·) = H` gives `ξ_pre = C(Z)` of weight `1`, while the claimed budget is `0`;
`Nat` truncated subtraction silently extends `W^(d-2)` to `d < 2` where the bound fails). -/
lemma weight_ξ_bound (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hd : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  classical
  -- `natDegreeY = natDegree`.
  have hdHY : Bivariate.natDegreeY H = H.natDegree := rfl
  rw [show Bivariate.natDegreeY R = R.natDegree from rfl,
      show Bivariate.natDegreeY H = H.natDegree from rfl]
  set d := R.natDegree with hd_def
  set dH := H.natDegree with hdH_def
  have hd2 : 2 ≤ d := hd
  -- Cofactor.
  obtain ⟨g, hg⟩ := hHyp.dvd_evalX
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hQ_def
  have hQ_ne : Q ≠ 0 := evalX_ne_zero_of_hypotheses hHyp
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hg_ne : g ≠ 0 := by intro h0; rw [h0, mul_zero] at hg; exact hQ_ne hg
  -- `dH ≤ d`.
  have hdH_le : dH ≤ d := by
    have hQdeg_le : Q.natDegree ≤ d := by rw [hQ_def]; exact evalX_natDegree_le (Polynomial.C x₀) R
    have hmul : Q.natDegree = dH + g.natDegree := by
      rw [hg, Polynomial.natDegree_mul hH_ne hg_ne]
    omega
  -- `dH ≤ D`.
  have hdH_le_D : dH ≤ D := by
    have hH_in : dH ∈ H.support :=
      Polynomial.mem_support_iff.mpr
        (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
    have := Bivariate.coeff_totalDegree_le H hH_in
    omega
  -- `totalDegree H + totalDegree g ≤ D`.
  have htot : Bivariate.totalDegree H + Bivariate.totalDegree g ≤ D := by
    have heq : Bivariate.totalDegree Q = Bivariate.totalDegree H + Bivariate.totalDegree g := by
      rw [hg, Bivariate.totalDegree_mul hH_ne hg_ne]
    omega
  -- The budget `(d-1)·m`, m = D + 1 - dH = D - dH + 1.
  set m := D + 1 - dH with hm_def
  have hm_eq : D - dH + 1 = m := by omega
  rw [hm_eq]
  -- Goal: weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ WithBot.some ((d-1)*m).
  change weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some ((d - 1) * m) : WithBot ℕ)
  rw [ξ]
  by_cases hbranch : dH < d
  · -- Branch 1: dH < d. Subtract a multiple of H_tilde' to cancel the top coefficient.
    set k := d - 1 - dH with hk_def
    set lc := (ξ_pre x₀ R H).coeff (d - 1) with hlc_def
    set sub : F[X][Y] := Polynomial.C lc * Polynomial.X ^ k * H_tilde' H with hsub_def
    set r : F[X][Y] := ξ_pre x₀ R H - sub with hr_def
    -- `mk r = mk ξ_pre` since `sub` is a multiple of `H_tilde'`.
    have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) r : 𝒪 H) =
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξ_pre x₀ R H) : 𝒪 H) := by
      rw [hr_def, map_sub, sub_eq_self]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hsub_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hD_H hH hmk) ?_
    -- Bound `weight_Λ r ≤ (d-1)*m`.
    rw [weight_Λ_le_iff]
    intro n hn
    rw [hdHY, ← hm_def]
    -- support of `r` lies in `{0, ..., d-2}`.
    -- The degree of `H_tilde' H` is `dH`, with leading coefficient `1`.
    have hHt_natDeg : (H_tilde' H).natDegree = dH := by rw [hdH_def]; exact natDegree_H_tilde' hH
    have hHt_lead : (H_tilde' H).coeff dH = 1 := by
      have hmon := (H_tilde'_monic H hH)
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hHt_natDeg] at hmon
      exact hmon
    -- `sub` has degree `≤ d - 1`.
    have hsub_natDeg : sub.natDegree ≤ d - 1 := by
      rw [hsub_def]
      refine Polynomial.natDegree_mul_le.trans ?_
      refine (Nat.add_le_add (Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le _)))
        hHt_natDeg.le).trans ?_
      omega
    have hn_le : n ≤ d - 2 := by
      by_contra hcontra
      rw [not_le] at hcontra
      have hrn : r.coeff n = 0 := by
        rcases Nat.lt_or_ge n d with hnd | hnd
        · -- n = d - 1: exact top cancellation.
          have hn1 : n = d - 1 := by omega
          subst hn1
          rw [hr_def, Polynomial.coeff_sub, hsub_def]
          have hsubc : (Polynomial.C lc * Polynomial.X ^ k * H_tilde' H).coeff (d - 1) = lc := by
            rw [show (Polynomial.C lc * Polynomial.X ^ k * H_tilde' H : F[X][Y]) =
                  Polynomial.C lc * (H_tilde' H * Polynomial.X ^ k) by ring]
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
            rw [if_pos (by omega)]
            rw [show d - 1 - k = dH by omega, hHt_lead, mul_one]
          rw [hsubc, hlc_def, sub_self]
        · -- n ≥ d: both summands vanish.
          rw [hr_def, Polynomial.coeff_sub]
          have hξ0 : (ξ_pre x₀ R H).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_ξ_pre_le hd2).trans_lt (by omega))
          have hsub0 : sub.coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (hsub_natDeg.trans_lt (by omega))
          rw [hξ0, hsub0, sub_zero]
      simp [hrn] at hn
    -- For `n ≤ d-2`: bound r.coeff n by max of the two summands.
    have hr_coeff : r.coeff n = (ξ_pre x₀ R H).coeff n - sub.coeff n := by
      rw [hr_def, Polynomial.coeff_sub]
    have hdeg_le : (r.coeff n).natDegree ≤
        max ((ξ_pre x₀ R H).coeff n).natDegree (sub.coeff n).natDegree := by
      rw [hr_coeff, sub_eq_add_neg]
      refine Polynomial.natDegree_add_le _ _ |>.trans ?_
      rw [Polynomial.natDegree_neg]
    rcases le_total ((ξ_pre x₀ R H).coeff n).natDegree (sub.coeff n).natDegree with h | h
    · -- bound by `sub`'s contribution
      have hsub_bound :=
        sub_term_budget hHyp hd2 hH hbranch hD_H hg htot (n := n) (by omega)
      rw [← hdH_def, ← hd_def, ← hsub_def, ← hm_def] at hsub_bound
      calc n * m + (r.coeff n).natDegree
          ≤ n * m + (sub.coeff n).natDegree :=
            Nat.add_le_add_left (hdeg_le.trans (max_le h le_rfl)) _
        _ ≤ (d - 1) * m := hsub_bound
    · -- bound by `ξ_pre`'s contribution
      have hξ_bound := ξ_pre_lower_budget hd2 hH hdH_le hD_H hD_Rx0 (n := n) (by omega)
      rw [← hdH_def, ← hd_def, ← hm_def] at hξ_bound
      calc n * m + (r.coeff n).natDegree
          ≤ n * m + ((ξ_pre x₀ R H).coeff n).natDegree :=
            Nat.add_le_add_left (hdeg_le.trans (max_le le_rfl h)) _
        _ ≤ (d - 1) * m := hξ_bound
  · -- Branch 2: dH = d. Use ξ_pre directly; the top coefficient is constant by separability.
    have hdH_eq : dH = d := by omega
    refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hD_H hH (r := ξ_pre x₀ R H) rfl) ?_
    rw [weight_Λ_le_iff]
    intro n hn
    rw [hdHY, ← hm_def]
    have hn_le : n ≤ d - 1 := (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hn)).trans (natDegree_ξ_pre_le hd2)
    rcases Nat.lt_or_ge n (d - 1) with hlt | hge
    · have hξ_bound := ξ_pre_lower_budget hd2 hH hdH_le hD_H hD_Rx0 (n := n) hlt
      rw [← hdH_def, ← hd_def, ← hm_def] at hξ_bound
      exact hξ_bound
    · -- n = d - 1: top coefficient is constant.
      have hn_eq : n = d - 1 := by omega
      subst hn_eq
      have htop : ((ξ_pre x₀ R H).coeff (d - 1)).natDegree = 0 :=
        natDegree_ξ_pre_coeff_top_eq_zero_of_natDegree_eq hHyp hd2 hg hdH_eq
      rw [htop, add_zero]

/-- A total degree for the trivariate polynomial `R`, represented as a polynomial in `Y` with
bivariate coefficients in the `Z` and `X` variables. -/
def trivariateTotalDegree (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun i => Bivariate.totalDegree (R.coeff i) + i)

/-- Each coefficient of `R` is bounded by `trivariateTotalDegree R`. -/
lemma coeff_totalDegree_add_index_le_trivariateTotalDegree (R : F[X][X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ trivariateTotalDegree R := by
  classical
  unfold trivariateTotalDegree
  exact Finset.le_sup (f := fun i => Bivariate.totalDegree (R.coeff i) + i) hi

/-- A canonical degree bound large enough for both `H` and all coefficients of `R`. -/
def defaultDegreeBound (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H) (trivariateTotalDegree R)

lemma defaultDegreeBound_ge_H (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ defaultDegreeBound R H :=
  le_max_left _ _

lemma defaultDegreeBound_ge_R_coeff (R : F[X][X][Y]) (H : F[X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ defaultDegreeBound R H :=
  (coeff_totalDegree_add_index_le_trivariateTotalDegree R hi).trans (le_max_right _ _)

end ClaimA2
end
end BCIKS20AppendixA
