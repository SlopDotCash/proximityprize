/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ReedSolomon.Constrained

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov,
Mirco Richter, Chung Thai Nguyen
-/

import ArkLib.Data.Matrix.Vandermonde
import ProximityPrize.Extensions.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.Interface
import ArkLib.ToMathlib.Polynomial.DegreeLT
import CompPoly.Data.Polynomial.MonomialBasis
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Henselian
import Mathlib.Basic.NNReal.Defs
import Mathlib.Basic.NNReal.Basic -- for instFloorSemiring of ℝ≥0

/-!
# Reed-Solomon Codes

- The lemmas with suffix `'` (e.g. `dim_eq_deg_of_le'`, `minDist_eq'`, ...) are generalizations of
  their corresponding non-suffixed versions from `Fin m` index to arbitrary finite index type `ι`.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
-/

namespace ReedSolomon

open Polynomial NNReal

variable {F : Type*} {ι : Type*} (domain : ι ↪ F)

noncomputable def codewordToPoly
  [Fintype ι] [Field F] [DecidableEq ι]
  {deg : ℕ} {domain : ι ↪ F} (f : code domain deg) : F[X] :=
  Lagrange.interpolate Finset.univ domain.toFun f

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}
         {C : Set (ι → F)}

section

open Finset Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F]

end

section

variable {deg m n : ℕ} {α : Fin m → F}

section

variable [Semiring F] {p : F[X]}

end

open LinearCode

section

variable [Semiring F]

/-- Transport a Reed-Solomon codeword across an equivalence of evaluation domains.

The hypothesis `hα` says that the two evaluation embeddings select the same field point after
reindexing by `e`. -/
lemma codeword_equiv_of_eval_eq
    {F ι₁ ι₂ : Type*} [Semiring F]
    (e : ι₁ ≃ ι₂)
    {α₁ : ι₁ ↪ F} {α₂ : ι₂ ↪ F}
    (hα : ∀ x : ι₁, α₂ (e x) = α₁ x)
    {deg : ℕ} {v : ι₁ → F}
    (hv : v ∈ code α₁ deg) :
    (fun y : ι₂ => v (e.symm y)) ∈ code α₂ deg := by
  rw [mem_code_iff_exists_polynomial] at hv ⊢
  rcases hv with ⟨p, hp_deg, hv_eval⟩
  refine ⟨p, hp_deg, ?_⟩
  ext y
  have hy : α₂ y = α₁ (e.symm y) := by
    simpa using hα (e.symm y)
  simp [hv_eval, evalOnPoints, hy]

/-- **Reed-Solomon codeword transport across a domain reindexing.**

If two evaluation embeddings agree up to a coordinate equivalence `e`
(`domain₁ x = domain₂ (e x)`), then reindexing any `domain₁`-codeword along `e.symm` yields a
`domain₂`-codeword of the same degree bound.

A codeword is the evaluation vector of a fixed polynomial of degree `< n`; relabelling the
evaluation points by a bijection that matches the points pointwise leaves it the evaluation
vector of the *same* polynomial, hence still a codeword.  This supplies the Reed-Solomon-specific
`hC` hypothesis consumed by `Code.jointAgreement_equiv_of_codeword_transport`, which is the lift
of joint agreement from one evaluation domain to an equivalent one (e.g. from `ω.subdomain 0`
to `ω` in the FRI/STIR Claim 8.3 accounting). -/
theorem code_reindex_mem {ι₁ ι₂ : Type*} (e : ι₁ ≃ ι₂)
    {domain₁ : ι₁ ↪ F} {domain₂ : ι₂ ↪ F} {n : ℕ}
    (hdom : ∀ x, domain₁ x = domain₂ (e x))
    {f : ι₁ → F} (hf : f ∈ code domain₁ n) :
    (fun y => f (e.symm y)) ∈ code domain₂ n := by
  rw [mem_code_iff_exists_polynomial] at hf
  obtain ⟨p, hdeg, rfl⟩ := hf
  refine mem_code_of_polynomial_of_degree_lt_of_eval p hdeg (fun y => ?_)
  show evalOnPoints domain₁ p (e.symm y) = p.eval (domain₂ y)
  have hev : evalOnPoints domain₁ p (e.symm y) = p.eval (domain₁ (e.symm y)) := by
    simp [evalOnPoints]
  rw [hev, hdom (e.symm y), Equiv.apply_symm_apply]

end

section

open NNReal

variable [Field F]

/-- Generalized dimension formula for RS code with arbitrary finite index type `ι`. -/
lemma dim_eq_deg_of_le' {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    {n : ℕ} {α : ι ↪ F} (h : n ≤ Fintype.card ι) :
  LinearCode.dim (ReedSolomon.code α n) = n :=
  dim_eq_deg_of_le h

@[simp]
lemma length_eq_domain_size (inj : Function.Injective α) :
    length (ReedSolomon.code ⟨α, inj⟩ deg) = m := by
  simp [length]

@[simp]
lemma length_eq_domain_card' {ι : Type*} [Fintype ι] {F : Type*} [Field F] {deg : ℕ}
    {α : ι ↪ F} :
    length (ReedSolomon.code α deg) = Fintype.card ι := by
  simp [length]

/- The usual formula for the rate of an RS-code: the degree divided by
  the cardinality of the evaluation set. -/
lemma rateOfLinearCode_eq_div' {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    {n : ℕ} {α : ι ↪ F} (h : n ≤ Fintype.card ι) :
    rate (ReedSolomon.code α n) = n / Fintype.card ι :=
  rateOfLinearCode_eq_div h

end

section

variable [Semiring F] {x : F} [Fintype ι] {α : ι ↪ F}

end

open Finset in
/-- The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`. -/
theorem minDist_eq [Field F] [DecidableEq F]
    (inj : Function.Injective α) [NeZero n] (h : n ≤ m) :
    Code.minDist ((ReedSolomon.code ⟨α, inj⟩ n) : Set (Fin m → F)) = m - n + 1 :=
  by
    simpa only [Fintype.card_fin] using
      (minDist_of_le (α := ⟨α, inj⟩) (n := n) (by simpa only [Fintype.card_fin] using h))

/-- Generalized minimal code distance for RS code with arbitrary finite index type `ι`. -/
theorem minDist_eq' {ι : Type*} [Fintype ι] {F : Type*} [Field F] [DecidableEq F]
    {α : ι ↪ F} [NeZero n] (h : n ≤ Fintype.card ι) :
  Code.minDist ((ReedSolomon.code α n) : Set (ι → F)) = Fintype.card ι - n + 1 :=
  minDist_of_le h

/-- Generalized distance equality for RS code with arbitrary finite index type `ι`. -/
theorem dist_eq' {ι : Type*} [Fintype ι] {F : Type*} {n : ℕ} {α : ι ↪ F}
    [Field F] [DecidableEq F] [NeZero n] (h : n ≤ Fintype.card ι) :
    Code.dist (R := F) ((ReedSolomon.code α n) : Set (ι → F)) = Fintype.card ι - n + 1 :=
  dist_eq_of_le h

/-- Generalized unique decoding radius for RS code with arbitrary finite index type `ι`. -/
theorem uniqueDecodingRadius_RS_eq' {ι : Type*} [Fintype ι]
    {F : Type*} {n : ℕ} {α : ι ↪ F} [Field F] [DecidableEq F] [NeZero n]
    (h : n ≤ Fintype.card ι) :
    Code.uniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code α n) =
    (Fintype.card ι - n) / 2 :=
  uniqueDecodingRadius_RS_eq h

open NNReal in
/-- Generalized relative unique decoding radius for RS code with arbitrary finite index type `ι`. -/
theorem relativeUniqueDecodingRadius_RS_eq' {ι : Type*} [Fintype ι]
    {F : Type*} {n : ℕ} {α : ι ↪ F} [Field F] [DecidableEq F] [NeZero n]
    (h : n ≤ Fintype.card ι) :
    Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code α n) =
    ((1 : ℝ≥0) - n / Fintype.card ι) / 2 :=
  relativeUniqueDecodingRadius_RS_eq h

end

section

open LinearMap Finset Polynomial

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]
         {domain : ι ↪ F}
         {deg : ℕ}

/-- The linear map that maps a Reed-Solomon codeword to its associated polynomial. -/
noncomputable def decode : (ReedSolomon.code domain deg) →ₗ[F] F[X] :=
  toPolynomial

/-- Reed-Solomon codewords are decoded into degree smaller than `deg` polynomials. -/
lemma decoded_polynomial_lt_deg (c : ReedSolomon.code domain deg) :
    decode c ∈ (degreeLT F deg : Submodule F F[X]) :=
  toPolynomial_mem_lt_deg c

/-- The linear map that maps a Reed-Solomon codeword to its associated polynomial of degree less
than `deg`. -/
noncomputable def decodeLT : (ReedSolomon.code domain deg) →ₗ[F] (Polynomial.degreeLT F deg) :=
  toPolynomialLT

open LinearMvExtension

variable {F : Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

variable {F : Type*} [Field F] [DecidableEq F]
        {ι : Type*} [Fintype ι] [DecidableEq ι]
        {domain : ι ↪ F} [Smooth domain]
        {m : ℕ}

/-- Definition 4.2, WHIR[ACFY24]
Smooth Reed-Solomon codes are Reed-Solomon codes defined over smooth domains, such that their
decoded univariate polynomials are of degree less than `2ᵐ` for some `m ∈ ℕ`. -/
noncomputable def smoothCode
    (domain : ι ↪ F) [Smooth domain]
  (m : ℕ) : Submodule F (ι → F) := ReedSolomon.code domain (2^m)

/-- The linear map that maps smooth Reed-Solomon Code words to their decoded degreewise linear
`m`-variate polynomial. -/
noncomputable def mVdecode :
  (smoothCode domain m) →ₗ[F] MvPolynomial (Fin m) F :=
    linearMvExtensionLMap.comp decodeLT

/-- Decoded multilinear polynomials of smooth codewords are degreewise linear. -/
lemma mVdecode_mem_restrictDegree (u : smoothCode domain m) :
    mVdecode u ∈ MvPolynomial.restrictDegree (Fin m) F 1 := by
  rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
  intro i
  exact degreeOf_linearMvExtension_le (p := decodeLT u)

namespace Compatibility

/-- Assign the value coordinate and Boolean coordinates over a field in any universe. -/
noncomputable def toWeightAssignment
    (p : MvPolynomial (Fin m) F) (b : Fin m → Fin 2) : Fin (m + 1) → F :=
  let b' : Fin m → F := fun i => ↑(b i : ℕ)
  Fin.cases (MvPolynomial.eval b' p) (fun i => ↑(b i : ℕ))

/-- The weighted Boolean-cube sum constraint over a field in any universe. -/
def weightConstraint
    (p : MvPolynomial (Fin m) F)
    (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Prop :=
  ∑ b : Fin m → Fin 2, w.eval (toWeightAssignment p b) = σ

omit [DecidableEq F] in
/-- For a degreewise-linear polynomial `p`, the weight constraint with the out-of-domain
evaluation weight `Z · eq(r, X)` — value variable at index `0`, matching
`toWeightAssignment` — holds iff `p(r) = σ`: by the multilinear-extension identity,
`∑ b ∈ {0,1}^m, p(b) · eq(r, b) = p(r)`. -/
lemma weightConstraint_eqPolynomial_iff
    (p : MvPolynomial (Fin m) F) (hp : p ∈ MvPolynomial.restrictDegree (Fin m) F 1)
    (r : Fin m → F) (σ : F) :
    weightConstraint p
      (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (MvPolynomial.eqPolynomial r)) σ
      ↔ MvPolynomial.eval r p = σ := by
  unfold weightConstraint
  have hterm : ∀ b : Fin m → Fin 2,
      MvPolynomial.eval (toWeightAssignment p b)
        (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (MvPolynomial.eqPolynomial r))
      = MvPolynomial.eval ((b : Fin m → F)) p
          * MvPolynomial.eval r (MvPolynomial.eqPolynomial ((b : Fin m → F))) := by
    intro b
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename,
      MvPolynomial.eqPolynomial_symm]
    have h0 : toWeightAssignment p b 0 = MvPolynomial.eval ((b : Fin m → F)) p := by
      simp only [toWeightAssignment, Fin.cases_zero]
    have hsucc : toWeightAssignment p b ∘ Fin.succ = ((b : Fin m → F)) := by
      funext j
      simp only [Function.comp_apply, toWeightAssignment, Fin.cases_succ]
    rw [h0, hsucc]
  have hsum : (∑ b : Fin m → Fin 2,
      MvPolynomial.eval (toWeightAssignment p b)
        (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (MvPolynomial.eqPolynomial r)))
      = MvPolynomial.eval r p := by
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    conv_rhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp hp]
    rw [MvPolynomial.MLE, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, MvPolynomial.eval_C]
    unfold MvPolynomial.toEvalsZeroOne
    ring
  rw [hsum]

/-- The historical constrained-code API over an arbitrary smooth embedding. The canonical
API specializes the domain to a smooth FFT coset; this preserves the broader embedding surface. -/
def constrainedCode
    (domain : ι ↪ F) [Smooth domain] (m : ℕ)
    (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Set (ι → F) :=
  {f | ∃ (h : f ∈ smoothCode domain m),
    weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) w σ}

/-- Multiple canonical weight constraints on the generic smooth-embedding code. -/
def multiConstrainedCode
    (domain : ι ↪ F) [Smooth domain] (m t : ℕ)
    (w : Fin t → MvPolynomial (Fin (m + 1)) F)
    (σ : Fin t → F) : Set (ι → F) :=
  {f | ∃ (h : f ∈ smoothCode domain m),
    ∀ i : Fin t, weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) (w i) (σ i)}

end Compatibility

/-- The generic weighted sum agrees definitionally with the canonical small-universe API. -/
lemma Compatibility.weightConstraint_iff_canonical
    {F : Type} [Field F] {m : ℕ}
    (p : MvPolynomial (Fin m) F) (w : MvPolynomial (Fin (m + 1)) F) (σ : F) :
    Compatibility.weightConstraint p w σ ↔ weightConstraint p w σ := Iff.rfl

/-- On a smooth FFT coset, the generic constrained-code interface is the canonical code. -/
lemma Compatibility.constrainedCode_eq_canonical
    {F : Type} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Domain.SmoothCosetFftDomain n F) [Smooth (domain : Fin (2 ^ n) ↪ F)]
    (m : ℕ) (w : MvPolynomial (Fin (m + 1)) F) (σ : F) :
    Compatibility.constrainedCode (domain : Fin (2 ^ n) ↪ F) m w σ =
      constrainedCode domain m w σ := rfl

/-- The generic multiple-constraint interface agrees with the canonical FFT-domain API. -/
lemma Compatibility.multiConstrainedCode_eq_canonical
    {F : Type} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Domain.SmoothCosetFftDomain n F) [Smooth (domain : Fin (2 ^ n) ↪ F)]
    (m t : ℕ) (w : Fin t → MvPolynomial (Fin (m + 1)) F) (σ : Fin t → F) :
    Compatibility.multiConstrainedCode (domain : Fin (2 ^ n) ↪ F) m t w σ =
      multiConstrainedCode domain m t w σ := rfl

/-- The canonical evaluation weight constraint is equivalent to evaluation of the polynomial. -/
lemma weightConstraint_eqPolynomial_iff
    {F : Type} [Field F] {m : ℕ}
    (p : MvPolynomial (Fin m) F) (hp : p ∈ MvPolynomial.restrictDegree (Fin m) F 1)
    (r : Fin m → F) (σ : F) :
    weightConstraint p
      (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (MvPolynomial.eqPolynomial r)) σ
      ↔ MvPolynomial.eval r p = σ :=
  (Compatibility.weightConstraint_iff_canonical p _ σ).symm.trans
    (Compatibility.weightConstraint_eqPolynomial_iff p hp r σ)

end
end ReedSolomon
