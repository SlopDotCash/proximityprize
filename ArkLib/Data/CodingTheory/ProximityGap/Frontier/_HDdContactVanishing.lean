/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HD1ContactVanishing
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Sum

/-!
# HDd — the hidden-derivative contact vanishing lemma at every order `d` (TR26-164 Lemma 3.1)

Generalizes `_HD1ContactVanishing.lean` from one hidden derivative to `d` hidden Hasse
derivatives.  The interpolant lives in `MvPolynomial (Fin (d+2)) F` with variables
`0 = X`, `1 = Y₀`, `j+2 = Y_{j+1}` (`j < d`), the node substitution is

    X ↦ α + T,   Y₀ ↦ y + Σ_{j<d} (−1)^j T^{j+1} Y_{j+1} + T^d E,   Y_{j+1} ↦ Y_{j+1}

(output variables `0 = T`, `1 = E`, `j+2 = Y_{j+1}`; here `E` absorbs one power of `T`
relative to TR26-164 (25), exactly as in the `d = 1` file, so counting `T`-degree plus
`E`-degree here is the same constraint set as counting `T`-degree alone in the `T^{d+1} E`
normalization), and the constraint is again that every
monomial of the result has `T`-degree plus `E`-degree at least `m`.  The only new ingredient is
the truncated Möbius inversion (TR26-164 (13))

    f ≡ f(0) + Σ_{j<d} (−1)^j X^{j+1} · f^{[j+1]}   (mod X^{d+1}),

proved coefficientwise from the alternating binomial sum, together with the commutation of
Hasse derivatives with the Taylor shift.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Polynomial

variable {F : Type*} [CommRing F]

/-! ## Hasse derivatives commute with the Taylor shift -/

theorem shift_hasseDeriv (α : F) (j : ℕ) (P : F[X]) :
    shift α (hasseDeriv j P) = hasseDeriv j (shift α P) := by
  ext n
  rw [shift_apply, shift_apply, ← taylor_apply, ← taylor_apply, taylor_coeff, hasseDeriv_coeff,
    taylor_coeff]
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := F) n j) P
  rw [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, eval_smul, nsmul_eq_mul, Nat.choose_symm_add]

/-! ## The truncated Möbius identity -/

/-- `Σ_{j<i} (−1)^j C(i, j+1) = 1` for `i ≥ 1`, as an identity in any commutative ring. -/
theorem sum_neg_one_pow_choose_succ (i : ℕ) (hi : 0 < i) :
    ∑ j ∈ Finset.range i, ((-1 : F) ^ j * (i.choose (j + 1) : F)) = 1 := by
  have h := @Int.alternating_sum_range_choose i
  rw [if_neg hi.ne'] at h
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h
  have h' : ∑ j ∈ Finset.range i, ((-1 : ℤ) ^ j * (i.choose (j + 1) : ℤ)) = 1 := by
    have : ∑ j ∈ Finset.range i, ((-1 : ℤ) ^ (j + 1) * (i.choose (j + 1) : ℤ)) =
        -∑ j ∈ Finset.range i, ((-1 : ℤ) ^ j * (i.choose (j + 1) : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this] at h
    linarith
  have := congrArg (Int.cast : ℤ → F) h'
  push_cast at this
  exact this

/-- **Truncated Möbius inversion.**  `X^{d+1}` divides
`f − f(0) − Σ_{j<d} (−1)^j X^{j+1} f^{[j+1]}`. -/
theorem X_pow_dvd_mobius_tail (f : F[X]) (d : ℕ) :
    X ^ (d + 1) ∣ f - C (f.coeff 0) -
      ∑ j : Fin d, C ((-1 : F) ^ (j : ℕ)) * (X ^ ((j : ℕ) + 1) * hasseDeriv ((j : ℕ) + 1) f) := by
  rw [X_pow_dvd_iff]
  intro i hi
  rw [Fin.sum_univ_eq_sum_range (fun j => C ((-1 : F) ^ j) * (X ^ (j + 1) * hasseDeriv (j + 1) f)) d]
  simp only [coeff_sub, finset_sum_coeff, coeff_C_mul, coeff_X_pow_mul', hasseDeriv_coeff, coeff_C]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [if_neg hpos.ne']
    have hfilter : (Finset.range d).filter (fun j => j + 1 ≤ i) = Finset.range i := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    have hsum : ∑ j ∈ Finset.range d, ((-1 : F) ^ j *
        (if j + 1 ≤ i then (((i - (j + 1) + (j + 1)).choose (j + 1) : ℕ) : F) *
          f.coeff (i - (j + 1) + (j + 1)) else 0)) =
        f.coeff i * ∑ j ∈ Finset.range i, ((-1 : F) ^ j * (i.choose (j + 1) : F)) := by
      rw [Finset.mul_sum, ← hfilter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rw [Nat.sub_add_cancel hj]; ring
      · ring
    rw [hsum, sum_neg_one_pow_choose_succ i hpos]
    ring

/-! ## The order-`d` contact constraint -/

/-- Node substitution for `d` hidden derivatives (see the module docstring). -/
noncomputable def contactSubstD (d : ℕ) (α y : F) :
    MvPolynomial (Fin (d + 2)) F →ₐ[F] MvPolynomial (Fin (d + 2)) F :=
  MvPolynomial.aeval
    (Fin.cons (MvPolynomial.C α + MvPolynomial.X 0)
      (Fin.cons (MvPolynomial.C y +
          ∑ j : Fin d, MvPolynomial.C ((-1 : F) ^ (j : ℕ)) * MvPolynomial.X 0 ^ ((j : ℕ) + 1) *
            MvPolynomial.X j.succ.succ +
          MvPolynomial.X 0 ^ d * MvPolynomial.X 1)
        (fun j : Fin d => MvPolynomial.X j.succ.succ)))

/-- The formal order-`m` contact constraint at `(α, y)` for `d` hidden derivatives. -/
def ContactConstraintD (d : ℕ) (α y : F) (m : ℕ) (Q : MvPolynomial (Fin (d + 2)) F) : Prop :=
  ∀ μ ∈ (contactSubstD d α y Q).support, m ≤ μ 0 + μ 1

/-- `Q(X, P, P^{[1]}, …, P^{[d]})`. -/
noncomputable def specializeD (d : ℕ) (Q : MvPolynomial (Fin (d + 2)) F) (P : F[X]) : F[X] :=
  MvPolynomial.aeval (Fin.cons X (Fin.cons P (fun j : Fin d => hasseDeriv ((j : ℕ) + 1) P))) Q

theorem X_pow_dvd_aeval_of_contactD (d : ℕ) (α y : F) (m : ℕ) (Q : MvPolynomial (Fin (d + 2)) F)
    (hQ : ContactConstraintD d α y m Q) (E' : F[X]) (Y : Fin d → F[X]) :
    X ^ m ∣ MvPolynomial.aeval (Fin.cons X (Fin.cons (X * E') Y)) (contactSubstD d α y Q) := by
  set S := contactSubstD d α y Q with hS
  rw [MvPolynomial.as_sum S, map_sum]
  refine Finset.dvd_sum fun μ hμ => ?_
  rw [MvPolynomial.aeval_monomial]
  have hμ' : m ≤ μ 0 + μ 1 := hQ μ hμ
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine Dvd.dvd.mul_left ?_ _
  rw [← mul_assoc]
  refine Dvd.dvd.mul_right ?_ _
  rw [mul_pow, ← mul_assoc, ← pow_add]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (by simpa using hμ')) _

/-- **Contact vanishing at order `d`.**  If `Q` satisfies the order-`m` contact constraint at
`(α, y)` with `d` hidden derivatives, then `(X − C α)^m` divides `Q(X, P, P^{[1]}, …, P^{[d]})`
for every `P` with `P(α) = y`. -/
theorem contact_vanishing_d (d : ℕ) (α y : F) (m : ℕ) (Q : MvPolynomial (Fin (d + 2)) F)
    (hQ : ContactConstraintD d α y m Q) (P : F[X]) (hP : P.eval α = y) :
    (X - C α) ^ m ∣ specializeD d Q P := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_shift
  set f := shift α P with hf
  have hf0 : f.coeff 0 = y := by
    rw [hf, shift_apply, ← taylor_apply, taylor_coeff_zero, hP]
  obtain ⟨E, hE⟩ := X_pow_dvd_mobius_tail f d
  -- f = C y + Σ_j (−1)^j X^{j+1} f^{[j+1]} + X^{d+1} E
  have hfeq : f = C y + ∑ j : Fin d, C ((-1 : F) ^ (j : ℕ)) *
      (X ^ ((j : ℕ) + 1) * hasseDeriv ((j : ℕ) + 1) f) + X ^ (d + 1) * E := by
    rw [← hf0, ← hE]; ring
  have hspec : shift α (specializeD d Q P) =
      MvPolynomial.aeval (Fin.cons (X + C α) (Fin.cons f
        (fun j : Fin d => hasseDeriv ((j : ℕ) + 1) f))) Q := by
    unfold specializeD
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · show shift α X = X + C α
      rw [shift_apply, X_comp]
    · rfl
    · simp only [Fin.cons_succ]
      exact shift_hasseDeriv α _ P
  rw [hspec]
  have hkey : MvPolynomial.aeval (Fin.cons (X + C α) (Fin.cons f
        (fun j : Fin d => hasseDeriv ((j : ℕ) + 1) f))) Q =
      MvPolynomial.aeval (Fin.cons X (Fin.cons (X * E)
        (fun j : Fin d => hasseDeriv ((j : ℕ) + 1) f))) (contactSubstD d α y Q) := by
    unfold contactSubstD
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · simp [add_comm]
    · have h1 : (1 : Fin (d + 2)) = Fin.succ 0 := by
        ext; simp
      simp only [h1, Fin.cons_zero, Fin.cons_succ, map_add, map_sum, map_mul, map_pow,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      conv_lhs => rw [hfeq]
      simp only [← mul_assoc, pow_succ, map_pow]
    · simp only [Fin.cons_succ, MvPolynomial.aeval_X]
  rw [hkey]
  exact X_pow_dvd_aeval_of_contactD d α y m Q hQ _ _

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.contact_vanishing_d
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.X_pow_dvd_mobius_tail
