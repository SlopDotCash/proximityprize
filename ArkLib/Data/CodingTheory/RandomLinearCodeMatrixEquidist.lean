/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Joint equidistribution of several random-linear-code codewords (GLMRSW22 second-moment input)

`RandomLinearCodeEquidistribution.lean` proved the *per-message* uniform marginal: for a fixed
nonzero `m`, `G ↦ m ᵥ* G` pushes the uniform generator-matrix distribution to uniform on `ι → F`.

This file generalises that to a **block of messages** stacked as a matrix `M : Matrix (Fin r) (Fin k) F`
that admits a right inverse (`M * N = 1`, i.e. full row rank): the joint codeword map
`G ↦ M * G : Matrix (Fin r) ι F` pushes the uniform generator-matrix distribution to the uniform
distribution on `Matrix (Fin r) ι F`. For `r = 2` and two linearly independent messages this is the
**pairwise** uniformity feeding the GLMRSW22 / ABF26 T3.11 *second* moment (the variance term the
list-size lower bound still needs).

The proof mirrors the single-row file with the patch row replaced by the translate `N * D`.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `mul_add_rightInvTranslate`, `mul_rightInv` — the `M * N = 1` algebra.
* `blockVecMul_surjective` — `G ↦ M * G` is surjective when `M` has a right inverse.
* `blockFiberEquiv` / `card_block_fiber_eq` — all joint-codeword fibers are equinumerous.
* `card_mat_eq_block` — `|Matrix (Fin k) ι F| = |Matrix (Fin r) ι F| · |fiber|`.
* `map_mul_uniformOfFintype` — the uniform generator-matrix law pushes forward under `M * ·` to the
  uniform law on `Matrix (Fin r) ι F`.
* `mul_uniform_apply`, `mul_uniform_mem_prob` — pointwise `(qⁿ)^{-r}` and set `|S| / (qⁿ)^r` forms.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- With a right inverse `M * N = 1`, translating `G` by `N * D` shifts the joint codeword by `D`. -/
lemma mul_add_rightInvTranslate {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (G : Matrix (Fin k) ι F) (D : Matrix (Fin r) ι F) :
    M * (G + N * D) = M * G + D := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hMN, Matrix.one_mul]

/-- A right inverse realises any target joint codeword: `M * (N * D) = D`. -/
lemma mul_rightInv {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (D : Matrix (Fin r) ι F) :
    M * (N * D) = D := by
  rw [← Matrix.mul_assoc, hMN, Matrix.one_mul]

/-- If `M` has a right inverse then `G ↦ M * G` is surjective onto `Matrix (Fin r) ι F`. -/
lemma blockVecMul_surjective {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) :
    Function.Surjective (fun G : Matrix (Fin k) ι F => M * G) :=
  fun D => ⟨N * D, mul_rightInv hMN D⟩

/-- The joint-codeword fibers of `G ↦ M * G` are all in bijection (translate by `N * (D' - D)`). -/
def blockFiberEquiv {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (D D' : Matrix (Fin r) ι F) :
    {G : Matrix (Fin k) ι F // M * G = D} ≃ {G : Matrix (Fin k) ι F // M * G = D'} where
  toFun := fun ⟨G, hG⟩ => ⟨G + N * (D' - D), by rw [mul_add_rightInvTranslate hMN, hG]; abel⟩
  invFun := fun ⟨G, hG⟩ => ⟨G + N * (D - D'), by rw [mul_add_rightInvTranslate hMN, hG]; abel⟩
  left_inv := fun ⟨G, hG⟩ => by
    apply Subtype.ext
    show G + N * (D' - D) + N * (D - D') = G
    rw [add_assoc, ← Matrix.mul_add]
    have h0 : (D' - D) + (D - D') = 0 := by abel
    rw [h0, Matrix.mul_zero, add_zero]
  right_inv := fun ⟨G, hG⟩ => by
    apply Subtype.ext
    show G + N * (D - D') + N * (D' - D) = G
    rw [add_assoc, ← Matrix.mul_add]
    have h0 : (D - D') + (D' - D) = 0 := by abel
    rw [h0, Matrix.mul_zero, add_zero]

/-- All joint-codeword fibers have equal cardinality. -/
lemma card_block_fiber_eq {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (D D' : Matrix (Fin r) ι F) :
    Fintype.card {G : Matrix (Fin k) ι F // M * G = D}
      = Fintype.card {G : Matrix (Fin k) ι F // M * G = D'} :=
  Fintype.card_congr (blockFiberEquiv hMN D D')

/-- Equidistribution cardinality identity: every joint codeword has the same number of preimages,
`|Matrix (Fin k) ι F| = |Matrix (Fin r) ι F| · |fiber|`. -/
lemma card_mat_eq_block {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (D : Matrix (Fin r) ι F) :
    Fintype.card (Matrix (Fin k) ι F)
      = Fintype.card (Matrix (Fin r) ι F)
          * Fintype.card {G : Matrix (Fin k) ι F // M * G = D} := by
  classical
  have hpart :
      (Finset.univ : Finset (Matrix (Fin k) ι F)).card
        = ∑ D' : Matrix (Fin r) ι F, (Finset.univ.filter (fun G => M * G = D')).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hpart
  have hsub : ∀ D' : Matrix (Fin r) ι F,
      (Finset.univ.filter (fun G => M * G = D')).card
        = Fintype.card {G : Matrix (Fin k) ι F // M * G = D'} :=
    fun D' => by rw [Fintype.card_subtype]
  simp_rw [hsub] at hpart
  rw [hpart, Finset.sum_congr rfl (fun D' _ => card_block_fiber_eq hMN D' D),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Joint equidistribution.** If `M` has a right inverse, the uniform generator-matrix
distribution pushes forward under `G ↦ M * G` to the uniform distribution on `Matrix (Fin r) ι F`. -/
theorem map_mul_uniformOfFintype {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) :
    (PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)
      = PMF.uniformOfFintype (Matrix (Fin r) ι F) := by
  classical
  ext D
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilter :
      (Finset.univ.filter (fun G : Matrix (Fin k) ι F => D = M * G))
        = (Finset.univ.filter (fun G => M * G = D)) :=
    Finset.filter_congr (fun G _ => by exact eq_comm)
  rw [hfilter, ← Fintype.card_subtype (fun G : Matrix (Fin k) ι F => M * G = D)]
  set Nf : ℕ := Fintype.card {G : Matrix (Fin k) ι F // M * G = D} with hNf
  set B : ℕ := Fintype.card (Matrix (Fin r) ι F) with hB
  have hMat : Fintype.card (Matrix (Fin k) ι F) = B * Nf := card_mat_eq_block hMN D
  rw [hMat]
  have hNne : (Nf : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < Nf := by
      rw [hNf]
      apply Fintype.card_pos_iff.2
      obtain ⟨G, hG⟩ := blockVecMul_surjective hMN D
      exact ⟨⟨G, hG⟩⟩
    exact_mod_cast hpos.ne'
  have hBne : (B : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < B := by rw [hB]; exact Fintype.card_pos
    exact_mod_cast hpos.ne'
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hBne) (Or.inl (ENNReal.natCast_ne_top B)),
    ← mul_assoc, mul_comm (Nf : ℝ≥0∞) (B : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel hNne (ENNReal.natCast_ne_top Nf), mul_one]

/-- Pointwise form: a fixed full-row-rank block lands on any given joint codeword with probability
`(q^{n})^{-r} = |Matrix (Fin r) ι F|⁻¹`. -/
theorem mul_uniform_apply {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (D : Matrix (Fin r) ι F) :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)) D
      = (Fintype.card (Matrix (Fin r) ι F) : ℝ≥0∞)⁻¹ := by
  rw [map_mul_uniformOfFintype hMN, PMF.uniformOfFintype_apply]

/-- Set form: the joint codeword lands in a set `S` with probability `|S| / |Matrix (Fin r) ι F|`,
the GLMRSW22 second-moment summand for a full-row-rank block of messages. -/
theorem mul_uniform_mem_prob {M : Matrix (Fin r) (Fin k) F} {N : Matrix (Fin k) (Fin r) F}
    (hMN : M * N = 1) (S : Set (Matrix (Fin r) ι F)) [Fintype S] :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)).toOuterMeasure S
      = Fintype.card S / Fintype.card (Matrix (Fin r) ι F) := by
  rw [map_mul_uniformOfFintype hMN, PMF.toOuterMeasure_uniformOfFintype_apply]

end ArkLib.RandomLinearCode

-- Axiom audit.
#print axioms ArkLib.RandomLinearCode.blockVecMul_surjective
#print axioms ArkLib.RandomLinearCode.card_mat_eq_block
#print axioms ArkLib.RandomLinearCode.map_mul_uniformOfFintype
#print axioms ArkLib.RandomLinearCode.mul_uniform_apply
#print axioms ArkLib.RandomLinearCode.mul_uniform_mem_prob
