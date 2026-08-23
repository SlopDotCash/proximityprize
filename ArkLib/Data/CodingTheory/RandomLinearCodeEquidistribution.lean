/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Equidistribution of random-linear-code codewords (GLMRSW22 first-moment linchpin)

For a uniformly random generator matrix `G : Matrix (Fin k) ι F` over a finite field `F`, and a
**fixed nonzero** message `m : Fin k → F`, the codeword `m ᵥ* G` is *uniformly distributed* over
`ι → F`.

This is the foundational counting fact behind the GLMRSW22 / ABF26 T3.11 first-moment argument
for random linear codes (issue #79): the expected number of "bad" codewords of a random linear
code is `(q^k - 1) · |Bad| / q^n`, computed by summing, over each nonzero message `m`, the
probability `Pr[m ᵥ* G ∈ Bad] = |Bad| / q^n` — and that per-message probability is exactly the
uniformity proved here.

`ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean` defines `uniformRandomLinearGeneratorMatrix
F k ι` as `PMF.uniformOfFintype (Matrix (Fin k) ι F)` (definitionally), so the headline theorem
`map_vecMul_uniformOfFintype` applies to it directly after unfolding.

## Main results (all `sorry`-free, axiom-clean: only `propext, Classical.choice, Quot.sound`)

* `vecMul_surjective` — for `m ≠ 0`, `G ↦ m ᵥ* G` is surjective.
* `card_fiber_eq` — all fibers of `G ↦ m ᵥ* G` have equal cardinality (explicit bijection).
* `card_mat_eq` — `|Matrix| = |ι → F| · |fiber|`, i.e. every codeword has exactly
  `q^{(k-1)·n}` preimage matrices (equidistribution, as a pure cardinality identity).
* `map_vecMul_uniformOfFintype` — the uniform generator-matrix distribution pushes forward, under
  `G ↦ m ᵥ* G`, to the uniform distribution on `ι → F`.
* `vecMul_uniform_apply` — pointwise: `Pr[m ᵥ* G = v] = (q^n)⁻¹`.
* `vecMul_uniform_mem_prob` — set form: `Pr[m ᵥ* G ∈ S] = |S| / q^n` (the GLMRSW22 first-moment
  summand).
* `card_vecMul_mem_mul` — division-free `ℕ` count: `|{G : m ᵥ* G ∈ S}| · q^n = |S| · |Matrix|`.

## What this does *not* close

This is the *per-message uniform marginal* only. The GLMRSW22 list-size **lower** bound
(`0 < randomLinearLambdaLowerProbability`, the `randomLinearLambdaLowerFirstMomentResidual`) needs,
in addition, the first/second-moment combinatorics charging the number of close codewords; that
remains the deep residual. This file supplies the uniform-marginal ingredient those moments
multiply.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single-row "patch" matrix: row `j` carries `(m j)⁻¹ • w`, every other row is zero.
Under left-multiplication by `m` (with `m j ≠ 0`) it realises the codeword `w`. -/
def patch (m : Fin k → F) (j : Fin k) (w : ι → F) : Matrix (Fin k) ι F :=
  Matrix.of fun i l => if i = j then (m j)⁻¹ * w l else 0

@[simp] lemma patch_apply (m : Fin k → F) (j : Fin k) (w : ι → F) (i : Fin k) (l : ι) :
    patch m j w i l = if i = j then (m j)⁻¹ * w l else 0 := rfl

/-- `patch` is additive in the target codeword. -/
lemma patch_add (m : Fin k → F) (j : Fin k) (a b : ι → F) :
    patch m j (a + b) = patch m j a + patch m j b := by
  ext i l
  simp only [patch_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs with h
  · ring
  · ring

@[simp] lemma patch_zero (m : Fin k → F) (j : Fin k) : patch m j (0 : ι → F) = 0 := by
  ext i l
  simp only [patch_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero, ite_self]

/-- Left-multiplying the patch by `m` (with `m j ≠ 0`) returns the target codeword. -/
lemma vecMul_patch {m : Fin k → F} {j : Fin k} (hj : m j ≠ 0) (w : ι → F) :
    m ᵥ* patch m j w = w := by
  funext l
  show (∑ i, m i * patch m j w i l) = w l
  rw [Finset.sum_eq_single j]
  · rw [patch_apply, if_pos rfl, ← mul_assoc, mul_inv_cancel₀ hj, one_mul]
  · intro i _ hi
    rw [patch_apply, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `m ᵥ* (G + patch m j w) = m ᵥ* G + w`. -/
lemma vecMul_add_patch {m : Fin k → F} {j : Fin k} (hj : m j ≠ 0)
    (G : Matrix (Fin k) ι F) (w : ι → F) :
    m ᵥ* (G + patch m j w) = m ᵥ* G + w := by
  rw [Matrix.vecMul_add, vecMul_patch hj]

/-- For a fixed nonzero message `m`, the codeword map `G ↦ m ᵥ* G` is surjective. -/
lemma vecMul_surjective {m : Fin k → F} (hm : m ≠ 0) :
    Function.Surjective (fun G : Matrix (Fin k) ι F => m ᵥ* G) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hm
  have hj' : m j ≠ 0 := by simpa using hj
  intro v
  exact ⟨patch m j v, vecMul_patch hj' v⟩

/-- The codeword fibers of `G ↦ m ᵥ* G` are all in bijection (translate by a patch row). -/
def fiberEquiv {m : Fin k → F} {j : Fin k} (hj : m j ≠ 0) (v v' : ι → F) :
    {G : Matrix (Fin k) ι F // m ᵥ* G = v} ≃ {G : Matrix (Fin k) ι F // m ᵥ* G = v'} where
  toFun := fun ⟨G, hG⟩ => ⟨G + patch m j (v' - v), by
    rw [vecMul_add_patch hj, hG]; abel⟩
  invFun := fun ⟨G, hG⟩ => ⟨G + patch m j (v - v'), by
    rw [vecMul_add_patch hj, hG]; abel⟩
  left_inv := fun ⟨G, hG⟩ => by
    apply Subtype.ext
    show G + patch m j (v' - v) + patch m j (v - v') = G
    rw [add_assoc, ← patch_add]
    have h0 : (v' - v) + (v - v') = 0 := by abel
    rw [h0, patch_zero, add_zero]
  right_inv := fun ⟨G, hG⟩ => by
    apply Subtype.ext
    show G + patch m j (v - v') + patch m j (v' - v) = G
    rw [add_assoc, ← patch_add]
    have h0 : (v - v') + (v' - v) = 0 := by abel
    rw [h0, patch_zero, add_zero]

/-- All codeword fibers have equal cardinality. -/
lemma card_fiber_eq {m : Fin k → F} {j : Fin k} (hj : m j ≠ 0) (v v' : ι → F) :
    Fintype.card {G : Matrix (Fin k) ι F // m ᵥ* G = v}
      = Fintype.card {G : Matrix (Fin k) ι F // m ᵥ* G = v'} :=
  Fintype.card_congr (fiberEquiv hj v v')

/-- **Equidistribution as a cardinality identity.** Each codeword `v` is hit by exactly
`|Matrix| / |ι → F| = q^{(k-1)·n}` generator matrices: `|Matrix| = |ι → F| · |fiber v|`. -/
lemma card_mat_eq {m : Fin k → F} (hm : m ≠ 0) (v : ι → F) :
    Fintype.card (Matrix (Fin k) ι F)
      = Fintype.card (ι → F) * Fintype.card {G : Matrix (Fin k) ι F // m ᵥ* G = v} := by
  classical
  obtain ⟨j, hj0⟩ := Function.ne_iff.1 hm
  have hj : m j ≠ 0 := by simpa using hj0
  have hpart :
      (Finset.univ : Finset (Matrix (Fin k) ι F)).card
        = ∑ v' : (ι → F), (Finset.univ.filter (fun G => m ᵥ* G = v')).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hpart
  have hsub : ∀ v' : (ι → F),
      (Finset.univ.filter (fun G => m ᵥ* G = v')).card
        = Fintype.card {G : Matrix (Fin k) ι F // m ᵥ* G = v'} := by
    intro v'
    rw [Fintype.card_subtype]
  simp_rw [hsub] at hpart
  rw [hpart, Finset.sum_congr rfl (fun v' _ => card_fiber_eq hj v' v),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The first-moment linchpin.** For a fixed nonzero message `m`, the uniform distribution on
generator matrices pushes forward under `G ↦ m ᵥ* G` to the uniform distribution on codewords. -/
theorem map_vecMul_uniformOfFintype {m : Fin k → F} (hm : m ≠ 0) :
    (PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)
      = PMF.uniformOfFintype (ι → F) := by
  classical
  ext v
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  -- goal: ∑ G, (if v = m ᵥ* G then (card Matrix)⁻¹ else 0) = (card (ι → F))⁻¹
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilter :
      (Finset.univ.filter (fun G : Matrix (Fin k) ι F => v = m ᵥ* G))
        = (Finset.univ.filter (fun G => m ᵥ* G = v)) := by
    apply Finset.filter_congr
    intro G _
    exact eq_comm
  rw [hfilter, ← Fintype.card_subtype (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)]
  set N : ℕ := Fintype.card {G : Matrix (Fin k) ι F // m ᵥ* G = v} with hN
  set B : ℕ := Fintype.card (ι → F) with hB
  have hMat : Fintype.card (Matrix (Fin k) ι F) = B * N := card_mat_eq hm v
  rw [hMat]
  have hNne : (N : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < N := by
      rw [hN]
      apply Fintype.card_pos_iff.2
      obtain ⟨G, hG⟩ := vecMul_surjective hm v
      exact ⟨⟨G, hG⟩⟩
    exact_mod_cast hpos.ne'
  have hBne : (B : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < B := by rw [hB]; exact Fintype.card_pos
    exact_mod_cast hpos.ne'
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hBne) (Or.inl (ENNReal.natCast_ne_top B)),
    ← mul_assoc, mul_comm (N : ℝ≥0∞) (B : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel hNne (ENNReal.natCast_ne_top N), mul_one]

/-- Pointwise form: a fixed nonzero message lands on any given codeword with probability
`(q^n)⁻¹`. -/
theorem vecMul_uniform_apply {m : Fin k → F} (hm : m ≠ 0) (v : ι → F) :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)) v
      = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ := by
  rw [map_vecMul_uniformOfFintype hm, PMF.uniformOfFintype_apply]

/-- **The first-moment summand.** For a fixed nonzero message `m` and any target set `S` of
codewords, the random codeword `m ᵥ* G` lands in `S` with probability `|S| / q^n`. This is
exactly the per-message term the GLMRSW22 first moment sums over the `q^k − 1` nonzero
messages. -/
theorem vecMul_uniform_mem_prob {m : Fin k → F} (hm : m ≠ 0)
    (S : Set (ι → F)) [Fintype S] :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => m ᵥ* G)).toOuterMeasure S
      = Fintype.card S / Fintype.card (ι → F) := by
  rw [map_vecMul_uniformOfFintype hm, PMF.toOuterMeasure_uniformOfFintype_apply]

/-- **The first-moment count (division-free `ℕ` form).** For a fixed nonzero message `m` and any
finite set `S` of codewords, `|{G : m ᵥ* G ∈ S}| · |ι → F| = |S| · |Matrix|`: a fixed nonzero
message hits `S` from exactly a `|S| / q^n` fraction of all generator matrices. Summed over the
`q^k − 1` nonzero messages this is the GLMRSW22 first moment of the number of codewords in `S`. -/
theorem card_vecMul_mem_mul (S : Finset (ι → F)) {m : Fin k → F} (hm : m ≠ 0) :
    (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S)).card
        * Fintype.card (ι → F)
      = S.card * Fintype.card (Matrix (Fin k) ι F) := by
  -- each codeword `v` is hit from a fixed `|Matrix| / |ι → F|` slice of generator matrices
  have hcell : ∀ v : ι → F,
      (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)).card
          * Fintype.card (ι → F)
        = Fintype.card (Matrix (Fin k) ι F) := by
    intro v
    have h := card_mat_eq hm v
    rw [Fintype.card_subtype] at h
    rw [mul_comm]; exact h.symm
  -- partition `{G : m ᵥ* G ∈ S}` into the disjoint codeword fibers over `S`
  have hbiUnion :
      Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S)
        = S.biUnion (fun v => Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨m ᵥ* G, h, rfl⟩
    · rintro ⟨v, hv, hG⟩; rw [hG]; exact hv
  have hdisj : ∀ v₁ ∈ S, ∀ v₂ ∈ S, v₁ ≠ v₂ →
      Disjoint (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v₁))
        (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v₂)) := by
    intro v₁ _ v₂ _ hne
    apply Finset.disjoint_left.2
    intro G hG₁ hG₂
    rw [Finset.mem_filter] at hG₁ hG₂
    exact hne (hG₁.2.symm.trans hG₂.2)
  rw [hbiUnion, Finset.card_biUnion hdisj, Finset.sum_mul,
    Finset.sum_congr rfl (fun v _ => hcell v), Finset.sum_const, smul_eq_mul]

end ArkLib.RandomLinearCode

-- Axiom audit: every public result must reduce to the standard kernel axioms only.
#print axioms ArkLib.RandomLinearCode.vecMul_surjective
#print axioms ArkLib.RandomLinearCode.card_fiber_eq
#print axioms ArkLib.RandomLinearCode.card_mat_eq
#print axioms ArkLib.RandomLinearCode.map_vecMul_uniformOfFintype
#print axioms ArkLib.RandomLinearCode.vecMul_uniform_apply
#print axioms ArkLib.RandomLinearCode.vecMul_uniform_mem_prob
#print axioms ArkLib.RandomLinearCode.card_vecMul_mem_mul
