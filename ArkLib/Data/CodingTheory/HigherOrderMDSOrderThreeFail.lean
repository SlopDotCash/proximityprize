/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon


/-!
# Order-2 higher MDS is sharp: an explicit MDS frame failing order 3 (#389)

Companion to `HigherOrderMDSOrderTwo.lean` (`isHigherMDS_two_of_isMDSFrame`, which shows order 2 is
automatic for every MDS frame).  Here is an *explicit Reed–Solomon (hence MDS) frame that is not
higher-order MDS of order 3*, proving the order-2 ceiling is sharp and that the genuine GM-MDS
difficulty really does begin at order 3.  `reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum`
states the general mechanism: any three disjoint pairs with a common sum force the failure — i.e.
an **additive collision** among the evaluation points, tying order-3 failure to the
additive-energy/Sidon structure of the domain.

The construction exposes the mechanism by which explicit/structured domains fail: take three
disjoint pairs of evaluation points sharing a common **sum** — here `{0,10}, {1,9}, {2,8}`, all
summing to `10`.  In dimension `k = 3` the span of a pair `{a,b}` is the plane orthogonal to the
interpolation normal `(X−a)(X−b) = X² − (a+b)X + ab`, i.e. to the point `(ab, −(a+b), 1)`.  Equal
sums make the three normals lie in a common plane (their `(sum, product)` points are collinear), so
they are linearly dependent and the three pair-spans share the unexpected common vector
`w = (0,1,10)` — even though generic position would force their intersection to be `{0}`.


`reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs` records the unconditional special case
`σ = 0` (antipodal pairs `{x, −x}`): this is the `a+b=0` relation that Sidon/`SidonModNeg` does NOT
forbid, so a negation-closed domain — `μ_n` for even `n` — fails order-3 higher MDS even in the
small-subgroup (Sidon) regime; `antipodal_example_not_isHigherMDS_three` is the concrete witness
`{±1,±2,±3}`.
Axiom-clean.
-/
open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

/-- The 6 explicit evaluation points: three pairs `{0,10},{1,9},{2,8}` all summing to `10`. -/
def Dfail : Fin 6 → ℚ := ![0, 10, 1, 9, 2, 8]

/-- The common vector `(0,1,10)` lying in all three pair-spans (generic intersection is `{0}`). -/
def wfail : Fin 3 → ℚ := ![0, 1, 10]

/-- The three disjoint pairs (by index). -/
def Jfail : Fin 3 → Finset (Fin 6) := ![{0, 1}, {2, 3}, {4, 5}]

theorem Dfail_injective : Function.Injective Dfail := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Dfail]

theorem wfail_ne : wfail ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [wfail] at this

/-- Order-3 higher MDS is **not** automatic: this explicit Reed–Solomon (hence MDS) frame fails it,
because the three pair-spans share the common vector `(0,1,10)` while generic intersection is `{0}`.
The mechanism: the pairs `{0,10},{1,9},{2,8}` share the sum `10`, so their interpolation normals
`(X−a)(X−b)` are linearly dependent (collinear `(sum,product)` points), forcing an unexpected
common vector.  Together with `isHigherMDS_two_of_isMDSFrame`, this pins the boundary: order 2
always holds, order 3 can fail. -/
theorem reedSolomonFrame_not_isHigherMDS_three :
    ¬ IsHigherMDS ℚ 3 (reedSolomonFrame Dfail 3) := by
  set v := reedSolomonFrame Dfail 3 with hv
  have hmds : IsMDSFrame ℚ v := reedSolomonFrame_isMDS Dfail_injective (by norm_num)
  -- membership helper
  have mem_pair : ∀ (J' : Finset (Fin 6)) (i₀ i₁ : Fin 6) (a b : ℚ),
      i₀ ∈ J' → i₁ ∈ J' → wfail = a • v i₀ + b • v i₁ → wfail ∈ frameSpan ℚ v J' := by
    intro J' i₀ i₁ a b h0 h1 hw
    rw [frameSpan, hw]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span ⟨i₀, Finset.mem_coe.mpr h0, rfl⟩))
      (Submodule.smul_mem _ b (Submodule.subset_span ⟨i₁, Finset.mem_coe.mpr h1, rfl⟩))
  have hw0 : wfail ∈ frameSpan ℚ v (Jfail 0) :=
    mem_pair _ 0 1 (-1/10) (1/10) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  have hw1 : wfail ∈ frameSpan ℚ v (Jfail 1) :=
    mem_pair _ 2 3 (-1/8) (1/8) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  have hw2 : wfail ∈ frameSpan ℚ v (Jfail 2) :=
    mem_pair _ 4 5 (-1/6) (1/6) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  apply not_higherMDS_of_not_generic (J := Jfail)
  · intro i; fin_cases i <;> simp [Jfail]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Jfail]
  · -- ¬ IsGenericInter: the intersection contains wfail ≠ 0, but generic codim would be 3
    intro hgen
    have hwmem : wfail ∈ ⨅ i, frameSpan ℚ v (Jfail i) := by
      rw [Submodule.mem_iInf]
      intro i; fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    have hbot : (⨅ i, frameSpan ℚ v (Jfail i)) ≠ ⊥ := fun h => by
      rw [h, Submodule.mem_bot] at hwmem; exact wfail_ne hwmem
    have hpos : 1 ≤ finrank ℚ ↥(⨅ i, frameSpan ℚ v (Jfail i)) :=
      Submodule.one_le_finrank_iff.mpr hbot
    have hV : finrank ℚ (Fin 3 → ℚ) = 3 := by simp
    have hc : ∀ i, (Jfail i).card ≤ finrank ℚ (Fin 3 → ℚ) := by
      intro i; rw [hV]; fin_cases i <;> simp [Jfail]
    rw [IsGenericInter, Fin.sum_univ_three, codim_frameSpan hmds (hc 0),
      codim_frameSpan hmds (hc 1), codim_frameSpan hmds (hc 2), codim, hV] at hgen
    have hcard : ∀ i, (Jfail i).card = 2 := by intro i; fin_cases i <;> simp [Jfail]
    rw [hcard 0, hcard 1, hcard 2] at hgen
    omega

/-- **Additive collision ⟹ order-3 higher-MDS failure (the lane bridge).**  If three pairwise
disjoint 2-element index sets share a common pair-sum `σ = ∑_{x∈Jᵢ} D x`, then the explicit
Reed–Solomon frame of dimension 3 on distinct points `D` is *not* order-3 higher MDS: the vector
`(0,1,σ)` lies in all three pair-spans (each `{a,b}` with `a+b=σ` has interpolation normal
`(ab,−σ,1)`, all sharing the orthogonal `(0,1,σ)`), while generic intersection is `{0}`.
For an evaluation domain this is exactly an additive collision among the points, so the
additive-energy/Sidon structure of the domain controls this family of higher-order-MDS failures. -/
theorem reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → K} (hD : Function.Injective D)
    {J : Fin 3 → Finset ι} (hcard : ∀ i, (J i).card = 2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (J i) (J j))
    {σ : K} (hsum : ∀ i, ∑ x ∈ J i, D x = σ) :
    ¬ IsHigherMDS K 3 (reedSolomonFrame D 3) := by
  set v := reedSolomonFrame D 3 with hvdef
  have hmds : IsMDSFrame K v := reedSolomonFrame_isMDS hD (by norm_num)
  set w : Fin 3 → K := ![0, 1, σ] with hwdef
  have hw_ne : w ≠ 0 := by
    intro h; have := congrFun h 1; simp [hwdef] at this
  -- the common vector lies in every pair-span
  have mem_w : ∀ i, w ∈ frameSpan K v (J i) := by
    intro i
    obtain ⟨a, b, hab, hJi⟩ := Finset.card_eq_two.mp (hcard i)
    have hsumab : D a + D b = σ := by
      have := hsum i; rw [hJi, Finset.sum_pair hab] at this; exact this
    have hDab : D b - D a ≠ 0 := sub_ne_zero.mpr (fun h => hab (hD h.symm))
    have hmem_a : v a ∈ frameSpan K v (J i) :=
      Submodule.subset_span ⟨a, by rw [hJi]; exact Finset.mem_coe.mpr (by simp), rfl⟩
    have hmem_b : v b ∈ frameSpan K v (J i) :=
      Submodule.subset_span ⟨b, by rw [hJi]; exact Finset.mem_coe.mpr (by simp), rfl⟩
    -- inverse-free scaling: `(D b − D a) • w = v b − v a`
    have hscaled : (D b - D a) • w = v b - v a := by
      funext j
      fin_cases j
      · simp [hwdef, hvdef, reedSolomonFrame]
      · simp [hwdef, hvdef, reedSolomonFrame]
      · simp only [hwdef, hvdef, reedSolomonFrame, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (D b - D a) * σ = D b ^ 2 - D a ^ 2
        rw [← hsumab]; ring
    have hmem_diff : v b - v a ∈ frameSpan K v (J i) := Submodule.sub_mem _ hmem_b hmem_a
    have hwsmul : w = (D b - D a)⁻¹ • ((D b - D a) • w) := by
      rw [smul_smul, inv_mul_cancel₀ hDab, one_smul]
    rw [hwsmul, hscaled]
    exact Submodule.smul_mem _ _ hmem_diff
  apply not_higherMDS_of_not_generic (J := J)
  · intro i; rw [hcard i]; exact (by norm_num : (2 : ℕ) ≤ finrank K (Fin 3 → K)).trans_eq (by simp)
  · exact hdisj
  · intro hgen
    have hwmem : w ∈ ⨅ i, frameSpan K v (J i) := Submodule.mem_iInf _ |>.mpr mem_w
    have hbot : (⨅ i, frameSpan K v (J i)) ≠ ⊥ := fun h => by
      rw [h, Submodule.mem_bot] at hwmem; exact hw_ne hwmem
    have hpos : 1 ≤ finrank K ↥(⨅ i, frameSpan K v (J i)) :=
      Submodule.one_le_finrank_iff.mpr hbot
    have hV : finrank K (Fin 3 → K) = 3 := by simp
    have hc : ∀ i, (J i).card ≤ finrank K (Fin 3 → K) := fun i => by rw [hV, hcard i]; norm_num
    rw [IsGenericInter, Fin.sum_univ_three, codim_frameSpan hmds (hc 0),
      codim_frameSpan hmds (hc 1), codim_frameSpan hmds (hc 2), codim, hV, hcard 0, hcard 1,
      hcard 2] at hgen
    omega

/-- **Antipodal (sum-zero) pairs force order-3 failure — unconditionally.**  Three pairwise disjoint
2-element sets each summing to `0` (antipodal pairs `{x, −x}`) make the RS frame fail order-3 higher
MDS.  This is the `σ = 0` case of `reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum`, and it
is exactly the `a+b=0` additive relation that the Sidon/`SidonModNeg` property *does not* forbid.
Hence any negation-closed domain — in particular `μ_n` for even `n`, which always contains the
antipodal pairs `{ζᵃ, −ζᵃ}` — fails order-3 higher MDS *even in the small-subgroup
(Sidon) regime*. -/
theorem reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → K} (hD : Function.Injective D)
    {J : Fin 3 → Finset ι} (hcard : ∀ i, (J i).card = 2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (J i) (J j)) (hzero : ∀ i, ∑ x ∈ J i, D x = 0) :
    ¬ IsHigherMDS K 3 (reedSolomonFrame D 3) :=
  reedSolomonFrame_not_isHigherMDS_three_of_commonPairSum hD hcard hdisj (σ := 0) hzero

/-- The negation-closed domain `{±1, ±2, ±3}` — the antipodal structure of `μ_n`. -/
def Danti : Fin 6 → ℚ := ![1, -1, 2, -2, 3, -3]

/-- Its three antipodal pairs. -/
def Janti : Fin 3 → Finset (Fin 6) := ![{0, 1}, {2, 3}, {4, 5}]

theorem Danti_injective : Function.Injective Danti := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (simp only [Danti] at h; norm_num at h)

/-- A concrete negation-closed domain whose RS frame of dimension 3 fails order-3 higher MDS. -/
theorem antipodal_example_not_isHigherMDS_three :
    ¬ IsHigherMDS ℚ 3 (reedSolomonFrame Danti 3) := by
  apply reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs Danti_injective (J := Janti)
  · intro i; fin_cases i <;> decide
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Janti]
  · intro i; fin_cases i <;> simp [Janti, Danti]

end ArkLib.HigherOrderMDS
