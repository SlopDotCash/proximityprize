/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83DeterminantCoverageFence

/-!
# G86: Hadamard's determinant inequality and the support-six census bound

G83 (`_G83DeterminantCoverageFence.lean`) proved the arithmetic handoff for the transversality
fence but left the field `hadamard_sq : determinant ^ 2 ≤ 6 ^ d` of
`SupportSixDeterminantCertificate` as an *assumed* certificate, naming "the Euclidean Hadamard
square bound for those rows" as an explicit open instantiation piece.

This file discharges that piece from scratch — Hadamard's determinant inequality is not in
Mathlib (as of this checkout's pin); we prove it here from
`InnerProductSpace.gramSchmidtOrthonormalBasis_det` and Cauchy–Schwarz, then specialize:

* `abs_basisFun_det_le_prod_norm` — **Hadamard's inequality**, family form: for any
  `f : Fin d → EuclideanSpace ℝ (Fin d)`, the determinant of `f` against the standard
  orthonormal basis satisfies `|det| ≤ ∏ i, ‖f i‖`. (Upstreaming candidate.)
* `abs_det_le_prod_sqrt_row_sq_sum` — matrix row form over `ℝ`:
  `|M.det| ≤ ∏ i, √(∑ j, M i j ^ 2)`.
* `sq_det_le_pow_of_row_sq_sum_le` — the integer consequence: if every row of an integer
  matrix has squared Euclidean norm `≤ B`, then `M.det ^ 2 ≤ B ^ d`.
* `row_sq_sum_le_of_support_le` — a `{−1,0,1}`-valued row with at most `c` nonzero entries has
  squared norm `≤ c` (the support-six hypothesis shape of the census rows).
* `supportSixDeterminantCertificate_of_rows` — **the weld**: any integer matrix with support-six
  `±1` rows, nonzero determinant, and coverage divisibility `p^s ∣ det` yields a
  `SupportSixDeterminantCertificate p s d`, so G83's fence
  (`coverage_log_le_half_height`, `no_certificate_above_half_height`) now consumes *matrices*,
  not asserted determinant certificates.

**Honest scope.** This closes exactly ONE of the three open instantiation pieces recorded by
G83 (the Hadamard square bound; now a theorem for arbitrary rows of squared norm ≤ 6). The two
remaining pieces are unchanged and still open: constructing a full-rank (nonzero-determinant)
matrix from the actual cyclotomic census rows, and proving that common prime-ideal coverage of
the census relations yields the divisibility `p^s ∣ det`. No bound on `M(μ_n)` is claimed;
CORE remains OPEN / ON-BGK. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G86HadamardSupportSix

open Finset InnerProductSpace
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Hadamard's determinant inequality**, family form: the determinant of a family
`f : Fin d → EuclideanSpace ℝ (Fin d)` with respect to the standard orthonormal basis is at
most the product of the Euclidean norms of the vectors. -/
theorem abs_basisFun_det_le_prod_norm (f : Fin d → EuclideanSpace ℝ (Fin d)) :
    |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det f| ≤ ∏ i, ‖f i‖ := by
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d) := by
    simp [finrank_euclideanSpace]
  set b := gramSchmidtOrthonormalBasis hcard f with hb
  have hdet : b.toBasis.det f = ∏ i, ⟪b i, f i⟫_ℝ :=
    gramSchmidtOrthonormalBasis_det hcard f
  -- change of orthonormal basis costs only a sign
  have hchange :
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det f
        = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det ⇑b.toBasis * b.toBasis.det f := by
    conv_lhs =>
      rw [AlternatingMap.eq_smul_basis_det b.toBasis
        ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det)]
    simp [AlternatingMap.smul_apply, smul_eq_mul]
  have hunit : |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det ⇑b.toBasis| = 1 := by
    rw [OrthonormalBasis.coe_toBasis, ← Real.norm_eq_abs]
    exact OrthonormalBasis.det_to_matrix_orthonormalBasis
      (EuclideanSpace.basisFun (Fin d) ℝ) b
  calc |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det f|
      = |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det ⇑b.toBasis| * |b.toBasis.det f| := by
        rw [hchange, abs_mul]
    _ = |b.toBasis.det f| := by rw [hunit, one_mul]
    _ = |∏ i, ⟪b i, f i⟫_ℝ| := by rw [hdet]
    _ = ∏ i, |⟪b i, f i⟫_ℝ| := Finset.abs_prod _ _
    _ ≤ ∏ i, ‖f i‖ := by
        refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
        have h1 := abs_real_inner_le_norm (b i) (f i)
        rwa [b.orthonormal.1 i, one_mul] at h1

/-- **Hadamard's determinant inequality**, matrix row form over `ℝ`:
`|det M| ≤ ∏ i, √(∑ j, M i j ^ 2)`. -/
theorem abs_det_le_prod_sqrt_row_sq_sum (M : Matrix (Fin d) (Fin d) ℝ) :
    |M.det| ≤ ∏ i, Real.sqrt (∑ j, M i j ^ 2) := by
  classical
  set f : Fin d → EuclideanSpace ℝ (Fin d) := fun i => WithLp.toLp 2 (M i) with hf
  have hdet : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det f = M.det := by
    rw [Module.Basis.det_apply]
    have hM : (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.toMatrix f = M.transpose := by
      ext i j
      rw [Module.Basis.toMatrix_apply]
      rfl
    rw [hM, Matrix.det_transpose]
  have hnorm : ∀ i, ‖f i‖ = Real.sqrt (∑ j, M i j ^ 2) := by
    intro i
    rw [EuclideanSpace.norm_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl (fun j _ => ?_))
    rw [Real.norm_eq_abs, sq_abs]
  calc |M.det| = |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det f| := by rw [hdet]
    _ ≤ ∏ i, ‖f i‖ := abs_basisFun_det_le_prod_norm f
    _ = ∏ i, Real.sqrt (∑ j, M i j ^ 2) := Finset.prod_congr rfl (fun i _ => hnorm i)

/-- Integer Hadamard bound: if every row of an integer matrix has squared Euclidean norm at
most `B`, then `det ^ 2 ≤ B ^ d`. -/
theorem sq_det_le_pow_of_row_sq_sum_le (M : Matrix (Fin d) (Fin d) ℤ) (B : ℕ)
    (h : ∀ i, (∑ j, M i j ^ 2) ≤ (B : ℤ)) :
    M.det ^ 2 ≤ (B : ℤ) ^ d := by
  classical
  set N : Matrix (Fin d) (Fin d) ℝ := M.map (Int.cast : ℤ → ℝ) with hN
  have hNdet : ((M.det : ℝ)) = N.det := by
    rw [hN]
    exact RingHom.map_det (Int.castRingHom ℝ) M
  have key : ((M.det : ℝ)) ^ 2 ≤ (B : ℝ) ^ d := by
    have h1 : |N.det| ≤ ∏ i, Real.sqrt (∑ j, N i j ^ 2) := abs_det_le_prod_sqrt_row_sq_sum N
    have h2 : ((M.det : ℝ)) ^ 2 ≤ ∏ i, (∑ j, N i j ^ 2) := by
      calc ((M.det : ℝ)) ^ 2 = |N.det| ^ 2 := by rw [hNdet]; exact (sq_abs _).symm
        _ ≤ (∏ i, Real.sqrt (∑ j, N i j ^ 2)) ^ 2 := by
            have h2 := mul_self_le_mul_self (abs_nonneg N.det) h1
            simpa [pow_two] using h2
        _ = ∏ i, (Real.sqrt (∑ j, N i j ^ 2)) ^ 2 := by rw [Finset.prod_pow]
        _ = ∏ i, (∑ j, N i j ^ 2) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h3 : ∏ i, (∑ j, N i j ^ 2) ≤ (B : ℝ) ^ d := by
      calc ∏ i, (∑ j, N i j ^ 2) ≤ ∏ _i : Fin d, (B : ℝ) := by
            refine Finset.prod_le_prod
              (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun i _ => ?_)
            have hi := h i
            have hc : ((∑ j, M i j ^ 2 : ℤ) : ℝ) ≤ ((B : ℤ) : ℝ) := by exact_mod_cast hi
            simpa [hN, Matrix.map_apply] using hc
        _ = (B : ℝ) ^ d := by simp [Finset.prod_const, Finset.card_univ]
    exact h2.trans h3
  exact_mod_cast key

/-- A `{−1,0,1}`-valued vector supported on at most `c` coordinates has squared Euclidean norm
at most `c`. This is the shape of the support-six census rows. -/
theorem row_sq_sum_le_of_support_le (v : Fin d → ℤ) (c : ℕ)
    (hval : ∀ j, v j = -1 ∨ v j = 0 ∨ v j = 1)
    (hsupp : ({j | v j ≠ 0} : Finset (Fin d)).card ≤ c) :
    (∑ j, v j ^ 2) ≤ (c : ℤ) := by
  classical
  have hsplit : (∑ j, v j ^ 2)
      = ∑ j ∈ ({j | v j ≠ 0} : Finset (Fin d)), v j ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)).symm
    have : v j = 0 := by
      by_contra hne
      exact hj (by simpa using hne)
    simp [this]
  have hterm : ∀ j ∈ ({j | v j ≠ 0} : Finset (Fin d)), v j ^ 2 ≤ 1 := by
    intro j _
    rcases hval j with h | h | h <;> simp [h]
  calc (∑ j, v j ^ 2)
      = ∑ j ∈ ({j | v j ≠ 0} : Finset (Fin d)), v j ^ 2 := hsplit
    _ ≤ ∑ _j ∈ ({j | v j ≠ 0} : Finset (Fin d)), (1 : ℤ) := Finset.sum_le_sum hterm
    _ = (({j | v j ≠ 0} : Finset (Fin d)).card : ℤ) := by simp
    _ ≤ (c : ℤ) := by exact_mod_cast hsupp

/-- **The weld into G83**: an integer census matrix with rows of squared norm at most `6`
(e.g. support-six `±1` rows), nonzero determinant, and coverage divisibility `p^s ∣ det`
produces the `SupportSixDeterminantCertificate` consumed by the G83 fence. The Hadamard field
is now a theorem, not an assumption. -/
theorem supportSixDeterminantCertificate_of_rows (p s : ℕ)
    (M : Matrix (Fin d) (Fin d) ℤ)
    (hne : M.det ≠ 0)
    (hdvd : (p : ℤ) ^ s ∣ M.det)
    (hrows : ∀ i, (∑ j, M i j ^ 2) ≤ (6 : ℤ)) :
    G83DeterminantCoverageFence.SupportSixDeterminantCertificate p s d M.det.natAbs := by
  refine ⟨Int.natAbs_pos.mpr hne, ?_, ?_⟩
  · have hd : ((p : ℤ) ^ s).natAbs ∣ M.det.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using hd
  · have hsq := sq_det_le_pow_of_row_sq_sum_le M 6 (by exact_mod_cast hrows)
    have habs : ((M.det.natAbs : ℤ)) ^ 2 = M.det ^ 2 := by
      rw [← Int.abs_eq_natAbs, sq_abs]
    have : ((M.det.natAbs : ℤ)) ^ 2 ≤ ((6 : ℕ) : ℤ) ^ d := by
      rw [habs]; exact_mod_cast hsq
    exact_mod_cast this

/-- End-to-end fence, matrix form: if coverage `s` satisfies
`(d/2)·log 6 < s·log p`, then NO full-rank support-six integer census matrix can carry the
divisibility `p^s ∣ det` — the concrete no-go the G82 fence direction consumes. -/
theorem no_census_matrix_above_half_height {p s : ℕ} (hp : 2 ≤ p)
    (hlarge : (d : ℝ) / 2 * Real.log 6 < (s : ℝ) * Real.log p)
    (M : Matrix (Fin d) (Fin d) ℤ)
    (hrows : ∀ i, (∑ j, M i j ^ 2) ≤ (6 : ℤ))
    (hdvd : (p : ℤ) ^ s ∣ M.det) :
    M.det = 0 := by
  by_contra hne
  exact G83DeterminantCoverageFence.no_certificate_above_half_height hp hlarge
    M.det.natAbs (supportSixDeterminantCertificate_of_rows p s M hne hdvd hrows)

end ArkLib.ProximityGap.Frontier.G86HadamardSupportSix

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.abs_basisFun_det_le_prod_norm
#print axioms ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.abs_det_le_prod_sqrt_row_sq_sum
#print axioms ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.sq_det_le_pow_of_row_sq_sum_le
#print axioms ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.row_sq_sum_le_of_support_le
#print axioms
  ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.supportSixDeterminantCertificate_of_rows
#print axioms ArkLib.ProximityGap.Frontier.G86HadamardSupportSix.no_census_matrix_above_half_height
