/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Stefano Rocca, Elias Judin
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Polynomial.Basic

import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries
import ProximityPrize.Extensions.Data.CodingTheory.GuruswamiSudan.Basic
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Interface

import CompPoly.Univariate.Lagrange

/-!
# Guruswami-Sudan Decoder

This module keeps the abstract Guruswami-Sudan specification decoder alongside
constructive candidate generation for Reed-Solomon codes.

The witness search is implemented by `computeGsWitness`, which solves a linearized
system of Hasse-derivative constraints with a normalization equation. Candidate
message polynomials are then filtered by a computable root check for
`$Q(X, p(X)) = 0$` using CompPoly arithmetic.

## References

* [Bafna, P., Chiesa, A., Ishai, Y., Khurana, D., and Spooner, N.,
    *On the Proximity Gap of Reed-Solomon Codes*][BCIKS20]
-/

namespace GuruswamiSudan

variable {F : Type} [Field F] [DecidableEq F]
variable {k : ℕ}
variable {n : ℕ}
variable {m : ℕ}
variable {ωs : Fin n ↪ F}
variable {f : Fin n → F}

open Finset Finsupp Polynomial Polynomial.Bivariate ReedSolomon

variable (k m) in
/-- Recover a polynomial from its first `k` coefficients when its degree is below `k`. -/
private lemma polynomial_of_coeffs_coeffs_of_polynomial_of_degree_lt
    {F : Type} [CommSemiring F] [DecidableEq F] {k : ℕ} {p : F[X]}
    (h : p.degree < (k : WithBot ℕ)) :
    polynomialOfCoeffs (coeffsOfPolynomial (deg := k) p) = p := by
  ext x
  simp only [coeff_polynomialOfCoeffs_eq_coeffs', coeffsOfPolynomial]
  split
  · rfl
  · symm
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le h (by exact_mod_cast Nat.le_of_not_lt ‹_›))

/-- Specification-level list decoder retained from the downstream development.

This finite-field contract enumerates all degree-`< k` polynomials and keeps exactly the
candidates within the requested distance bound. The canonical `decoder` supplies the
Guruswami-Sudan interpolant-root construction.
-/
noncomputable def specificationDecoder [Fintype F] (k _r _D e : ℕ)
    (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] :=
  ((polynomialsDegreeLt F k).filter fun p => decide (Δ₀(f, p.eval ∘ ωs) ≤ e)).toList

/-- Each decoded codeword has to be `e`-close to the received message. -/
theorem decoder_mem_impl_dist
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ specificationDecoder k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e := by
  have hmem : p ∈ polynomialsDegreeLt F k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
    simpa [specificationDecoder] using h_in
  exact hmem.2

/-- Alias for the specification decoder distance guarantee. -/
theorem decoder_output_dist_le
    [Fintype F]
    {k r D e : ℕ}
    (h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ specificationDecoder k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  decoder_mem_impl_dist (k := k) (r := r) (D := D) (e := e) h_e h_in

/-- If a degree-bounded codeword is `e`-close to the received message, it appears in the decoder
output.
Note: This completeness property is now trivial because `specificationDecoder` is defined as the pure
list-decoding specification (filtering `polynomialsDegreeLt`), rather than the algorithmic
Guruswami-Sudan output (`decoderCandidateSet`). -/
theorem decoder_dist_impl_mem
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_degree : p.degree < k)
    (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
    p ∈ specificationDecoder k r D e ωs f := by
  simp [specificationDecoder, mem_polynomials_degree_lt.mpr h_degree, h_dist]

/-! ### CompPoly-based interpolation candidate

The following private helpers use CompPoly's computable `CPolynomial.Raw` type to build a
Lagrange interpolation candidate from the first `min k n` evaluation points. The result is
converted back to Mathlib's `Polynomial F` via coefficient extraction (`polynomialOfCoeffs`),
which is fully computable.

The candidate is constructed with `rawToPolyBounded`, whose output has bounded degree by
construction (`degree_polynomialOfCoeffs_deg_lt_deg`). CompPoly's `Raw.toPoly` bridge is
noncomputable, so we validate the candidate by degree and distance checks before insertion.
-/

/-- Every element of `compPolyCandidateSet` satisfies the degree and distance bounds. -/
private lemma mem_comp_poly_candidate_set_imp [Fintype F] {k e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ compPolyCandidateSet k e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [compPolyCandidateSet] at hp
  split at hp
  · split at hp
    · rw [Finset.mem_singleton.mp hp]
      exact decide_eq_true_eq.mp ‹_›
    · simp at hp
  · simp at hp

/-! ### Hasse derivative evaluation for multiplicity checking

The Guruswami–Sudan multiplicity condition requires that for each interpolation
point `(ωᵢ, fᵢ)`, the bivariate polynomial `Q` vanishes with multiplicity `≥ r`.
Formally, this means every Hasse derivative `D^{(a,b)} Q` (for `a + b < r`)
evaluates to zero at `(ωᵢ, fᵢ)`.

For a bivariate polynomial `Q = ∑ cᵢⱼ X^i Y^j`, the `(a,b)`-Hasse derivative at
`(x₀, y₀)` is `∑ C(i,a) C(j,b) cᵢⱼ x₀^{i-a} y₀^{j-b}`, where `C(n,k)` denotes
the binomial coefficient.

The following functions compute this evaluation purely computably over coefficient
vectors, with no reliance on classical choice or nonconstructive root extraction.
-/

omit [DecidableEq F] in
/-- The `(0,0)`-Hasse derivative is ordinary evaluation: `Nat.choose i 0 = 1`,
    `Nat.choose j 0 = 1`, and shifting by zero leaves exponents unchanged, so
    `hasseDerivEvalAt k D 0 0 c x y = evalCoeffVecAt k D c x y`. -/
private lemma hasseDerivEvalAt_zero_zero (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) :
    hasseDerivEvalAt k D 0 0 c x y = evalCoeffVecAt k D c x y := by
  unfold hasseDerivEvalAt evalCoeffVecAt
  congr 1; funext j; funext a2; congr 1; funext i
  simp [Nat.choose_zero_right]

/-- If the multiplicity check passes, every individual Hasse derivative of order
    `< r` vanishes. This is the core unwinding of `hasseMultiplicityCheck`. -/
private lemma hasseMultiplicityCheck_imp_deriv_zero {k D r a b : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {x y : F}
    (hcheck : hasseMultiplicityCheck k D r c x y = true)
    (hab : a + b < r) :
    hasseDerivEvalAt k D a b c x y = 0 := by
  simp only [hasseMultiplicityCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    decide_eq_true_eq] at hcheck
  have h := hcheck ⟨a + b, hab⟩ ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩
  rwa [Nat.add_sub_cancel_left] at h

/-- When `r > 0`, the multiplicity check implies pointwise evaluation vanishes:
    `Q(x, y) = 0`. This is the `(a, b) = (0, 0)` specialization, combined with
    `hasseDerivEvalAt_zero_zero`. -/
private lemma hasseMultiplicityCheck_imp_eval_zero {k D r : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {x y : F}
    (hr : 0 < r)
    (hcheck : hasseMultiplicityCheck k D r c x y = true) :
    evalCoeffVecAt k D c x y = 0 := by
  rw [← hasseDerivEvalAt_zero_zero]
  exact hasseMultiplicityCheck_imp_deriv_zero hcheck (by omega)

/-- When `r > 0` and the witness predicate `isWitnessC` holds, the bivariate polynomial
    represented by `c` vanishes at every interpolation point `(ωs i, f i)`.

    This connects the computable Hasse-derivative multiplicity filter to the classical
    pointwise root condition `Q(ωᵢ, fᵢ) = 0` that the GS witness branch relies on. -/
private lemma is_witness_c_imp_eval_zero_at_points {k D r : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {c : Fin (D + 1) × Fin (D + 1) → F}
    (hr : 0 < r)
    (hw : isWitnessC k D r ωs f c = true) (i : Fin n) :
    evalCoeffVecAt k D c (ωs i) (f i) = 0 := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨_, hmult⟩ := hw
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left] at hmult
  exact hasseMultiplicityCheck_imp_eval_zero hr (hmult ⟨i.val, i.isLt⟩)

/-- Extract the nonzero-coefficient condition from `isWitnessC`: there exists at least one
    index pair `(i, j)` in the weighted-degree region `i + (k-1)·j ≤ D` where `c(i,j) ≠ 0`. -/
private lemma is_witness_c_nonzero {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) :
    ∃ i : Fin (D + 1), ∃ j : Fin (D + 1),
      i.val + (k - 1) * j.val ≤ D ∧ c (i, j) ≠ 0 := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨hne, _⟩ := hw
  simp only [List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at hne
  obtain ⟨j, i, hcond⟩ := hne
  exact ⟨i, j, hcond⟩

/-- Extract the per-point multiplicity check from `isWitnessC`: `hasseMultiplicityCheck`
    passes at every interpolation point `(ωs i, f i)`. -/
private lemma is_witness_c_multiplicity_at {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) (i : Fin n) :
    hasseMultiplicityCheck k D r c (ωs i) (f i) = true := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨_, hmult⟩ := hw
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left] at hmult
  exact hmult ⟨i.val, i.isLt⟩

/-- When `isWitnessC` holds, every Hasse derivative of order `< r` vanishes at every
    interpolation point. This combines `is_witness_c_multiplicity_at` with
    `hasseMultiplicityCheck_imp_deriv_zero`. -/
private lemma is_witness_c_hasse_deriv_vanishes {k D r a b : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true)
    (hab : a + b < r) (i : Fin n) :
    hasseDerivEvalAt k D a b c (ωs i) (f i) = 0 :=
  hasseMultiplicityCheck_imp_deriv_zero (is_witness_c_multiplicity_at hw i) hab

/-- `hasWitnessC = true` iff `computeGsWitness` returns an explicit witness package. -/
private lemma hasWitnessC_eq_true_iff_exists_output
    (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    hasWitnessC (n := n) k D r ωs f = true ↔
      ∃ w, computeGsWitness (n := n) k D r ωs f = some w := by
  unfold hasWitnessC
  simp [Option.isSome_iff_exists]

/-! ### Q-root extraction via CompPoly

Given a witness bivariate polynomial `Q = ∑ cᵢⱼ X^i Y^j` and a candidate
univariate polynomial `p(X)`, the Guruswami–Sudan root-extraction step checks
whether `Y - p(X)` divides `Q(X, Y)` in `F[X][Y]`. Equivalently, this reduces
to checking `Q(X, p(X)) = 0` in `F[X]`.

We compute the root filter `Q(X, p(X)) = ∑ cᵢⱼ X^i · p(X)^j` using CompPoly's
`CPolynomial.Raw` arithmetic and check whether the result is zero. The root filter
itself avoids nonconstructive root extraction; the upstream linear solver used to
produce `Q` is still noncomputable.
-/

/-- Characterization of `isQRootRaw`: it holds iff every element of the result array
    `evalQAtPRaw k D c pRaw` equals zero. This is a direct consequence of `Array.all`
    semantics and `BEq` on `F` being faithful (from `DecidableEq F`). -/
private lemma is_q_root_raw_iff_all_coeff_zero {k D : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {pRaw : CompPoly.CPolynomial.Raw F} :
    isQRootRaw k D c pRaw = true ↔
      ∀ idx : Fin (evalQAtPRaw k D c pRaw).size,
        (evalQAtPRaw k D c pRaw)[idx] = 0 := by
  simp only [isQRootRaw]
  rw [Array.all_iff_forall]
  constructor
  · intro h idx
    have hmem := h idx.val idx.isLt ⟨Nat.zero_le _, idx.isLt⟩
    simp only [beq_iff_eq] at hmem
    exact hmem
  · intro h i hi hrange
    simp only [beq_iff_eq]
    exact h ⟨i, hi⟩

/-- Every element of `witnessCandidateSet` has degree `< k` and distance `≤ e`. -/
private lemma mem_witness_candidate_set_imp [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ witnessCandidateSet k r D e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  unfold witnessCandidateSet at hp
  split at hp
  · rw [Finset.mem_filter] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨mem_polynomials_degree_lt.mp hp.1, hp.2.2⟩
  · simp at hp

/-- Strengthened witness soundness: when `r > 0`, every candidate in `witnessCandidateSet`
    is backed by a witness whose Hasse-derivative multiplicity conditions imply pointwise
    root vanishing at every interpolation point.

    Concretely, there exists a coefficient vector `c` satisfying:
    * `isWitnessC` (nonzero in the weighted-degree region and full multiplicity vanishing), and
    * `Q(X, p(X)) = 0` via CompPoly root extraction, and
    * `evalCoeffVecAt k D c (ωs i) (f i) = 0` for every `i : Fin n`.

    The last property is derived from `is_witness_c_imp_eval_zero_at_points`. -/
private lemma witness_candidate_set_witness_vanishes [Fintype F] {k r D e : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
    (hr : 0 < r)
    (hp : p ∈ witnessCandidateSet k r D e ωs f) :
    ∃ c : Fin (D + 1) × Fin (D + 1) → F,
      isWitnessC k D r ωs f c = true ∧
      isQRootRaw k D c (polyToRaw p k) = true ∧
      ∀ i : Fin n, evalCoeffVecAt k D c (ωs i) (f i) = 0 := by
  unfold witnessCandidateSet at hp
  cases hcw : computeGsWitness (n := n) k D r ωs f
  case none =>
      simp [hcw] at hp
  case some w =>
      rw [hcw] at hp
      rw [Finset.mem_filter] at hp
      obtain ⟨_, hcond⟩ := hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨w.1, w.2, hcond.1, fun i ↦ is_witness_c_imp_eval_zero_at_points hr w.2 i⟩

/--
Decoder candidate set inspired by Guruswami–Sudan.

**Definition.** The decoder returns the union of:
* a CompPoly interpolation fast-path candidate set, and
* a GS witness-filtered set computed from a linear-system witness search.

The implementation combines two candidate sources:

1. **CompPoly Lagrange candidate** (`compPolyCandidateSet`): A fast-path candidate
   constructed via CompPoly's computable Lagrange interpolation from the first
   `min k n` evaluation points. Included only if it passes degree and distance checks.

2. **GS witness-filtered candidates** (`witnessCandidateSet`): A concrete witness
   coefficient vector is computed by solving a linearized GS system with normalization.
   Candidates are filtered by `Q(X, p(X)) = 0` and the distance bound.

The fast-path and root checks are executable. The full candidate set is marked
`noncomputable` because the current `linsolve` abstraction used to obtain a witness is
noncomputable.
-/
noncomputable def decoderCandidateSet [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F)
    (f : Fin n → F) :
    Finset F[X] :=
  compPolyCandidateSet k e ωs f ∪ witnessCandidateSet k r D e ωs f

/-- Decoder soundness: every output polynomial has degree `< k` and distance `≤ e`. -/
private lemma mem_decoderCandidateSet_imp [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ decoderCandidateSet k r D e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [decoderCandidateSet, Finset.mem_union] at hp
  rcases hp with h | h
  · exact mem_comp_poly_candidate_set_imp h
  · exact mem_witness_candidate_set_imp h

/-- Each decoded codeword is within `e` Hamming distance of the received message. -/
theorem decoderCandidateSet_mem_impl_dist
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoderCandidateSet k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  (mem_decoderCandidateSet_imp h_in).2

/-- Alias for the candidate-set distance guarantee. -/
theorem decoderCandidateSet_output_dist_le
    [Fintype F]
    {k r D e : ℕ}
    (h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoderCandidateSet k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  decoderCandidateSet_mem_impl_dist (k := k) (r := r) (D := D) (e := e) h_e h_in

/-- A witness satisfying `isWitnessC` produces a nonzero Mathlib bivariate polynomial
    via `coeffVecToBivariate`. This follows from `is_witness_c_nonzero`: there is at
    least one nonzero coefficient in the weighted-degree region. -/
lemma coeff_vec_to_bivariate_ne_zero_of_is_witness_c
    {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) :
    coeffVecToBivariate k D c ≠ 0 := by
  obtain ⟨i, j, hwd, hne⟩ := is_witness_c_nonzero hw
  intro heq
  apply hne
  rw [← coeff_vec_to_bivariate_coeff k D c i j hwd, heq]
  simp

end GuruswamiSudan
