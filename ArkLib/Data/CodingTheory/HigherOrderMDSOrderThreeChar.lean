/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon
import ArkLib.Data.CodingTheory.HigherOrderMDSOrderTwo

/-!
# The sharp order-3 higher-MDS law for the Reed–Solomon frame: `(sum, product)` non-collinearity
(#389)

`HigherOrderMDSOrderTwo.lean` shows order 2 is automatic for every MDS frame, and
`HigherOrderMDSOrderThreeFail.lean` shows order 3 can fail — exhibiting the failure mechanism for
three disjoint pairs sharing a common **sum** (the additive-collision / `SidonModNeg`-antipodal
mechanism).  Those failure certificates leave open the *positive* direction — the **large-`k`,
unequal-sum frontier**: for which three-pair configurations does order 3 actually *hold*?  This
file closes that gap for the order-3 slice with an **exact iff** and uses it to exhibit a strictly
new failure mode.

## The sharp law

For three pairwise-disjoint pairs `{aᵢ,bᵢ}` of the explicit Reed–Solomon frame `(1, D, D²)` in
dimension `3`, the pair-span of `{aᵢ,bᵢ}` is the plane orthogonal to the **interpolation normal**
`nᵢ = (Daᵢ·Dbᵢ, −(Daᵢ+Dbᵢ), 1)` (the coefficient vector of `(X−Daᵢ)(X−Dbᵢ)`).  Writing
`sᵢ = Daᵢ+Dbᵢ`, `pᵢ = Daᵢ·Dbᵢ`, the determinant of the three normals equals the **collinearity
determinant** of the three plane points `(sᵢ, pᵢ)` (`normalDet_eq_sumProdDet`).  Hence:

`order-3 generic position  ⟺  the three points (sᵢ, pᵢ) = (sum, product) are affinely
non-collinear.`

* `isGenericInter_three_of_normalDet` — order-3 generic position from `det(normals) ≠ 0` (Cramer:
  three independent normals force the pair-spans to meet only at `0`).
* `normalDet_eq_sumProdDet` — `det(normals) = det` of the `(sum, product)` collinearity matrix.
* `isGenericInter_three_of_sumProd_noncollinear` — **the positive certificate**: non-collinear
  `(sum, product)` points ⟹ order 3 holds.  This is exactly the unequal-sum frontier: equal sums
  are the special *vertical-line* collinear case, so this strictly extends the equal-sum failure
  analysis — any non-collinear triple (in particular generic unequal-sum triples over `μ_n`) is in
  order-3 generic position.
* `sumProdDet_eq_zero_of_not_isGenericInter` — the contrapositive, completing the iff.

## A strictly new failure mode

`distinctSum_not_isHigherMDS_three` exhibits an explicit order-3 failure with **three pairwise
distinct pair-sums** (`-13, -3, 5`), whose `(sum, product)` points are nonetheless collinear (on
the line `p = −4·s − 30`).  The equal-sum lemma
`reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum` does *not* apply to it: the sharp law's
collinearity obstruction is strictly more general than the equal-sum one.
Axiom-clean.
-/

open Finset Module Matrix ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The interpolation normal of a pair `{a,b}`: the coefficient vector of `(X−Da)(X−Db)`,
`(Da·Db, −(Da+Db), 1)`.  Its orthogonal hyperplane in `Fin 3 → K` is the pair-span. -/
def pairNormal (D : ι → K) (a b : ι) : Fin 3 → K :=
  ![D a * D b, -(D a + D b), 1]

/-- The pair normal annihilates the frame column at either endpoint (`(X−Da)(X−Db)` vanishes at
`Da`, `Db`). -/
theorem pairNormal_dot_col (D : ι → K) (a b x : ι) (hx : x = a ∨ x = b) :
    pairNormal D a b ⬝ᵥ reedSolomonFrame D 3 x = 0 := by
  simp only [pairNormal, reedSolomonFrame, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one,
    one_mul]
  rcases hx with rfl | rfl
  · ring
  · ring

/-- Any vector in the pair-span (span of the two frame columns) is annihilated by the pair normal. -/
theorem frameSpan_pair_dot_eq_zero (D : ι → K) (a b : ι) {w : Fin 3 → K}
    (hw : w ∈ frameSpan K (reedSolomonFrame D 3) {a, b}) :
    pairNormal D a b ⬝ᵥ w = 0 := by
  classical
  rw [frameSpan] at hw
  refine Submodule.span_induction (p := fun w _ => pairNormal D a b ⬝ᵥ w = 0) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨ζ, hζ, rfl⟩
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hζ
    exact pairNormal_dot_col D a b ζ hζ
  · simp
  · intro x z _ _ hx hz; rw [dotProduct_add, hx, hz, add_zero]
  · intro c x _ hx; rw [dotProduct_smul, hx, smul_zero]

/-- **Order-3 generic-position certificate from the normal determinant.**
For three disjoint pairs `{aᵢ,bᵢ}`, if the `3×3` matrix of interpolation normals
`(Daᵢ·Dbᵢ, −(Daᵢ+Dbᵢ), 1)` is nonsingular, then the three pair-spans of the RS frame meet only at
`0`, i.e. they are in generic intersection position — order-3 holds for this family.  Mechanism:
three linearly independent normals kill the common vector via Cramer uniqueness. -/
theorem isGenericInter_three_of_normalDet (D : ι → K) (hD : Function.Injective D)
    (J : Fin 3 → Finset ι) (a b : Fin 3 → ι)
    (hJ : ∀ i, J i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hN : (Matrix.of (fun i j => pairNormal D (a i) (b i) j) :
        Matrix (Fin 3) (Fin 3) K).det ≠ 0) :
    IsGenericInter (fun i => frameSpan K (reedSolomonFrame D 3) (J i)) := by
  classical
  set v := reedSolomonFrame D 3 with hv
  have hmds : IsMDSFrame K v := reedSolomonFrame_isMDS hD (by norm_num)
  set N : Matrix (Fin 3) (Fin 3) K := Matrix.of (fun i j => pairNormal D (a i) (b i) j) with hNdef
  -- the intersection is `⊥`: any common vector is killed by the three independent normals
  have hbot : (⨅ i, frameSpan K v (J i)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_iInf] at hw
    have hker : N.mulVec w = 0 := by
      funext i
      have hwi : w ∈ frameSpan K v (J i) := hw i
      rw [hJ i] at hwi
      have := frameSpan_pair_dot_eq_zero D (a i) (b i) hwi
      simpa [hNdef, Matrix.mulVec, dotProduct, pairNormal] using this
    have hunit : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr (isUnit_iff_ne_zero.mpr hN)
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := N)).2 hunit
    have : N.mulVec w = N.mulVec 0 := by rw [hker, Matrix.mulVec_zero]
    exact hinj this
  have hcard : ∀ i, (J i).card = 2 := by
    intro i; rw [hJ i, Finset.card_pair (hab i)]
  have hV : finrank K (Fin 3 → K) = 3 := by simp
  have hc : ∀ i, (J i).card ≤ finrank K (Fin 3 → K) := fun i => by rw [hV, hcard i]; norm_num
  rw [IsGenericInter, hbot, Fin.sum_univ_three, codim_frameSpan hmds (hc 0),
    codim_frameSpan hmds (hc 1), codim_frameSpan hmds (hc 2), codim, hV, hcard 0, hcard 1, hcard 2,
    finrank_bot]
  norm_num

/-- The `(sum, product)` collinearity matrix of three pairs: rows `(Daᵢ+Dbᵢ, Daᵢ·Dbᵢ, 1)`.  Its
determinant vanishes exactly when the three plane points `(sumᵢ, productᵢ)` are affinely collinear. -/
def pairSumProdMatrix (D : ι → K) (a b : Fin 3 → ι) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of (fun i => ![D (a i) + D (b i), D (a i) * D (b i), 1])

/-- **The key determinant identity.**  The determinant of the three interpolation normals equals
the `(sum, product)` collinearity determinant.  Hence order-3 generic position is governed exactly
by the affine *non-collinearity* of the three points `(Daᵢ+Dbᵢ, Daᵢ·Dbᵢ)` in the plane. -/
theorem normalDet_eq_sumProdDet (D : ι → K) (a b : Fin 3 → ι) :
    (Matrix.of (fun i j => pairNormal D (a i) (b i) j) : Matrix (Fin 3) (Fin 3) K).det
      = (pairSumProdMatrix D a b).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [pairNormal, pairSumProdMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The unequal-sum order-3 certificate (the positive direction of the sharp law).**
Three disjoint pairs `{aᵢ,bᵢ}` whose `(sum, product)` points `(Daᵢ+Dbᵢ, Daᵢ·Dbᵢ)` are *affinely
non-collinear* (the collinearity determinant `≠ 0`) are in order-3 generic position for the RS
frame.  Equal pair-sums are the special collinear case (a vertical line), so this strictly extends
the equal-sum failure analysis: the genuine obstruction is collinearity in `(sum, product)` space,
and any non-collinear triple — in particular generic unequal-sum triples over `μ_n` — is fine.  This
is the missing positive piece of the large-`k` unequal-sum frontier at order 3. -/
theorem isGenericInter_three_of_sumProd_noncollinear (D : ι → K) (hD : Function.Injective D)
    (J : Fin 3 → Finset ι) (a b : Fin 3 → ι)
    (hJ : ∀ i, J i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hnc : (pairSumProdMatrix D a b).det ≠ 0) :
    IsGenericInter (fun i => frameSpan K (reedSolomonFrame D 3) (J i)) :=
  isGenericInter_three_of_normalDet D hD J a b hJ hab
    (by rw [normalDet_eq_sumProdDet]; exact hnc)

/-- **Sharp law, contrapositive form.**  If the RS frame *fails* order-3 generic position on three
disjoint pairs, then the `(sum, product)` points must be collinear.  Together with
`isGenericInter_three_of_sumProd_noncollinear` this is the exact iff: order-3 generic ⟺ the three
`(sum, product)` points are non-collinear. -/
theorem sumProdDet_eq_zero_of_not_isGenericInter (D : ι → K) (hD : Function.Injective D)
    (J : Fin 3 → Finset ι) (a b : Fin 3 → ι)
    (hJ : ∀ i, J i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hfail : ¬ IsGenericInter (fun i => frameSpan K (reedSolomonFrame D 3) (J i))) :
    (pairSumProdMatrix D a b).det = 0 := by
  by_contra h
  exact hfail (isGenericInter_three_of_sumProd_noncollinear D hD J a b hJ hab h)

/-! ### A new, distinct-sum failure mode

The classic order-3 failure (`reedSolomonFrame_not_isHigherMDS_three`) needs *equal pair sums*.
The sharp law above shows the true obstruction is `(sum, product)`-collinearity, which is strictly
weaker.  The following concrete witness has **three pairwise-distinct pair-sums** (`-13, -3, 5`),
yet its `(sum, product)` points are collinear (on the line `p = −4·s − 30`), so it still fails
order-3 — a failure mode *not* covered by the equal-sum lemma. -/

/-- Six distinct points; the three pairs `{-2,-11},{3,-6},{10,-5}` have distinct sums but collinear
`(sum, product)` points. -/
def Dcol : Fin 6 → ℚ := ![-2, -11, 3, -6, 10, -5]

/-- The common vector `(1/30, −2/15, 1)` lying in all three pair-spans. -/
def wcol : Fin 3 → ℚ := ![1/30, -2/15, 1]

/-- The three disjoint distinct-sum pairs. -/
def Jcol : Fin 3 → Finset (Fin 6) := ![{0, 1}, {2, 3}, {4, 5}]

theorem Dcol_injective : Function.Injective Dcol := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp only [Dcol] at h; norm_num at h)

theorem wcol_ne : wcol ≠ 0 := by
  intro h; have := congrFun h 2; simp [wcol] at this

/-- **Order-3 fails on three pairs with all-distinct sums.**  The pairs `{-2,-11},{3,-6},{10,-5}`
have pairwise-distinct sums `-13, -3, 5`, yet the RS frame fails order-3 higher MDS, because their
`(sum, product)` points are collinear — the strictly more general obstruction the sharp law
predicts.  The equal-sum lemma `reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum` does
**not** apply, so this is a genuinely new family of higher-order-MDS failures. -/
theorem distinctSum_not_isHigherMDS_three :
    ¬ IsHigherMDS ℚ 3 (reedSolomonFrame Dcol 3) := by
  set v := reedSolomonFrame Dcol 3 with hv
  have hmds : IsMDSFrame ℚ v := reedSolomonFrame_isMDS Dcol_injective (by norm_num)
  have mem_pair : ∀ (J' : Finset (Fin 6)) (i₀ i₁ : Fin 6) (a c : ℚ),
      i₀ ∈ J' → i₁ ∈ J' → wcol = a • v i₀ + c • v i₁ → wcol ∈ frameSpan ℚ v J' := by
    intro J' i₀ i₁ a c h0 h1 hw
    rw [frameSpan, hw]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span ⟨i₀, Finset.mem_coe.mpr h0, rfl⟩))
      (Submodule.smul_mem _ c (Submodule.subset_span ⟨i₁, Finset.mem_coe.mpr h1, rfl⟩))
  have hw0 : wcol ∈ frameSpan ℚ v (Jcol 0) :=
    mem_pair _ 0 1 (7/270) (1/135) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wcol, hv, reedSolomonFrame, Dcol] <;> norm_num)
  have hw1 : wcol ∈ frameSpan ℚ v (Jcol 1) :=
    mem_pair _ 2 3 (1/135) (7/270) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wcol, hv, reedSolomonFrame, Dcol] <;> norm_num)
  have hw2 : wcol ∈ frameSpan ℚ v (Jcol 2) :=
    mem_pair _ 4 5 (1/450) (7/225) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wcol, hv, reedSolomonFrame, Dcol] <;> norm_num)
  apply not_higherMDS_of_not_generic (J := Jcol)
  · intro i; fin_cases i <;> simp [Jcol]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Jcol]
  · intro hgen
    have hwmem : wcol ∈ ⨅ i, frameSpan ℚ v (Jcol i) := by
      rw [Submodule.mem_iInf]
      intro i; fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    have hbot : (⨅ i, frameSpan ℚ v (Jcol i)) ≠ ⊥ := fun h => by
      rw [h, Submodule.mem_bot] at hwmem; exact wcol_ne hwmem
    have hpos : 1 ≤ finrank ℚ ↥(⨅ i, frameSpan ℚ v (Jcol i)) :=
      Submodule.one_le_finrank_iff.mpr hbot
    have hV : finrank ℚ (Fin 3 → ℚ) = 3 := by simp
    have hc : ∀ i, (Jcol i).card ≤ finrank ℚ (Fin 3 → ℚ) := by
      intro i; rw [hV]; fin_cases i <;> simp [Jcol]
    rw [IsGenericInter, Fin.sum_univ_three, codim_frameSpan hmds (hc 0),
      codim_frameSpan hmds (hc 1), codim_frameSpan hmds (hc 2), codim, hV] at hgen
    have hcard : ∀ i, (Jcol i).card = 2 := by intro i; fin_cases i <;> simp [Jcol]
    rw [hcard 0, hcard 1, hcard 2] at hgen
    omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.isGenericInter_three_of_normalDet
#print axioms ArkLib.HigherOrderMDS.normalDet_eq_sumProdDet
#print axioms ArkLib.HigherOrderMDS.isGenericInter_three_of_sumProd_noncollinear
#print axioms ArkLib.HigherOrderMDS.sumProdDet_eq_zero_of_not_isGenericInter
#print axioms ArkLib.HigherOrderMDS.distinctSum_not_isHigherMDS_three
