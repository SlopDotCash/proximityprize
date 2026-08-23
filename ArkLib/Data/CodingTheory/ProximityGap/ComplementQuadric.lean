/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.A4CensusValue

/-!
# The complement-quadric transform: top census rows are small-set quadric geometry

Campaign #357. The depth-1 census condition `e₂ = 0` transforms under complementation:
the full domain has vanishing first and second power sums, so `p₁` and `p₂` *negate* under
complement while `e₂ = (p₁² − p₂)/2` becomes `(p₁² + p₂)/2`:

> **`e2Folded_eq_zero_iff_complement_quadric`** — for `p` above the explicit threshold:
> a set `A` qualifies (`e2Folded m A = 0`) **iff** its complement `T` satisfies the
> quadric `(∑_{i∈T} g^i)² = −∑_{i∈T} g^(2i)`.

For the top rows `a = n − c` (small `c`) this converts the census into the `F_p`-point
geometry of an explicit quadric on `c`-subsets — e.g. the `a = n−3` row (fully
coset-decomposable by probe) is the point count of a 3-variable quadric, and the measured
orbit census there is the rational-point orbit. This is the same "arithmetic of the
evaluation domain governs the census" phenomenon the boundary-row analysis found from the
syndrome side.

Supporting bricks, each reusable: the pair-square identity
(`two_mul_pairPow_sum`: `2·∑_{i<j} g^(i+j) = S² − Q`), the full-domain power-sum
vanishing (`sum_pow_range_eq_zero`, `sum_pow_sq_range_eq_zero`), and the complement
negation (`sum_pow_compl`).

## References

* Probes `probe_a9_exceptional_family.py` (complement quadric check 32/32),
  `probe_coset_core_conjecture.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}

/-- **The pair-square identity**: twice the pair-power sum is the square of the power sum
minus the diagonal. -/
theorem two_mul_pairPow_sum (g : ZMod p) (A : Finset ℕ) :
    2 * ∑ q ∈ upperPairs A, g ^ (q.1 + q.2)
      = (∑ i ∈ A, g ^ i) ^ 2 - ∑ i ∈ A, g ^ (2 * i) := by
  classical
  have hsq : (∑ i ∈ A, g ^ i) ^ 2 = ∑ q ∈ A ×ˢ A, g ^ (q.1 + q.2) := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (pow_add g i j).symm
  have hsplit : A ×ˢ A = A.diag ∪ A.offDiag := (Finset.diag_union_offDiag A).symm
  have hdisj : Disjoint A.diag A.offDiag := Finset.disjoint_diag_offDiag A
  have hdiag : ∑ q ∈ A.diag, g ^ (q.1 + q.2) = ∑ i ∈ A, g ^ (2 * i) := by
    rw [Finset.sum_diag (f := fun q : ℕ × ℕ => g ^ (q.1 + q.2))]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  -- the off-diagonal is the doubled upper triangle
  have hoff : ∑ q ∈ A.offDiag, g ^ (q.1 + q.2)
      = 2 * ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) := by
    have hunion : A.offDiag
        = upperPairs A ∪ (A ×ˢ A).filter (fun q => q.2 < q.1) := by
      ext q
      simp only [Finset.mem_offDiag, upperPairs, Finset.mem_union, Finset.mem_filter,
        Finset.mem_product]
      constructor
      · rintro ⟨h1, h2, hne⟩
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨⟨h1, h2⟩, h⟩
        · exact Or.inr ⟨⟨h1, h2⟩, h⟩
      · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
        · exact ⟨h1, h2, by omega⟩
        · exact ⟨h1, h2, by omega⟩
    have hdisj2 : Disjoint (upperPairs A) ((A ×ˢ A).filter (fun q => q.2 < q.1)) := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      omega
    have hswap : ∑ q ∈ (A ×ˢ A).filter (fun q => q.2 < q.1), g ^ (q.1 + q.2)
        = ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) := by
      refine Finset.sum_nbij (fun q => (q.2, q.1)) ?_ ?_ ?_ ?_
      · intro q hq
        obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hq
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩
      · intro q _ q' _ hq
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hq
        exact Prod.ext h2 h1
      · intro q hq
        obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
        exact ⟨(q.2, q.1), Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt⟩), rfl⟩
      · intro q _
        rw [Nat.add_comm]
    rw [hunion, Finset.sum_union hdisj2, hswap]
    ring
  rw [hsq, hsplit, Finset.sum_union hdisj, hdiag, hoff]
  ring

/-- The full smooth domain's power sum vanishes. -/
theorem sum_pow_range_eq_zero (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m)) :
    ∑ i ∈ Finset.range (2 ^ m), g ^ i = 0 :=
  hg.geom_sum_eq_zero (by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)

/-- The full smooth domain's second power sum vanishes (for `m ≥ 2`). -/
theorem sum_pow_sq_range_eq_zero (hm : 2 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m)) :
    ∑ i ∈ Finset.range (2 ^ m), g ^ (2 * i) = 0 := by
  have h2 : ∀ i, g ^ (2 * i) = (g ^ 2) ^ i := fun i => by rw [← pow_mul]
  simp only [h2]
  -- g² is a primitive 2^(m−1)-th root; the range splits into two equal blocks
  have hsq : IsPrimitiveRoot (g ^ 2) (2 ^ (m - 1)) := by
    have := hg.pow (n := 2 ^ m) (by positivity)
      (show 2 ^ m = 2 * 2 ^ (m - 1) by
        rw [← pow_succ']
        congr 1
        omega)
    exact this
  have hsplit : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
    omega
  have hblock : ∑ i ∈ Finset.range (2 ^ (m - 1)), (g ^ 2) ^ i = 0 :=
    hsq.geom_sum_eq_zero (by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hper : (g ^ 2) ^ 2 ^ (m - 1) = 1 := by
    rw [← pow_mul]
    have : 2 * 2 ^ (m - 1) = 2 ^ m := by omega
    rw [this, hg.pow_eq_one]
  rw [hsplit, Finset.sum_range_add]
  have hshift : ∀ i, (g ^ 2) ^ (2 ^ (m - 1) + i) = (g ^ 2) ^ i := fun i => by
    rw [pow_add, hper, one_mul]
  rw [Finset.sum_congr rfl fun i _ => hshift i, hblock]
  simp

/-- Power sums negate under complement inside the smooth domain. -/
theorem sum_pow_compl (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m)) (c : ℕ)
    (hfull : ∑ i ∈ Finset.range (2 ^ m), g ^ (c * i) = 0) :
    ∑ i ∈ Finset.range (2 ^ m) \ A, g ^ (c * i) = -∑ i ∈ A, g ^ (c * i) := by
  have := Finset.sum_sdiff (f := fun i => g ^ (c * i)) hsub
  linear_combination this + hfull

/-- **The complement-quadric transform.** Above the explicit threshold, a set qualifies
**iff** its complement satisfies the quadric `S_T² = −Q_T`. -/
theorem e2Folded_eq_zero_iff_complement_quadric (hm : 2 ≤ m)
    (hg : IsPrimitiveRoot g (2 ^ m)) {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m))
    (hA : A.Nonempty)
    (hp : (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) < p) :
    e2Folded m A = 0 ↔
      (∑ i ∈ Finset.range (2 ^ m) \ A, g ^ i) ^ 2
        = -∑ i ∈ Finset.range (2 ^ m) \ A, g ^ (2 * i) := by
  have hm1 : 1 ≤ m := by omega
  -- p is odd (it exceeds the threshold, which is ≥ 4)
  have hp4 : 4 < p := by
    have h1 : (4 : ℕ) ≤ (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) := by
      have hc1 : 1 ≤ A.card := Finset.card_pos.mpr hA
      have hq2 : 2 ≤ 2 ^ (m - 1) := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ (m - 1) * (A.card * A.card)) ^ 2 := by
            have : 2 ≤ 2 ^ (m - 1) * (A.card * A.card) := by nlinarith
            nlinarith
        _ ≤ (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) := by
            apply Nat.pow_le_pow_right
            · nlinarith
            · calc 2 = 2 ^ 1 := rfl
                _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; ring,
      ZMod.natCast_eq_zero_iff] at hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  -- step 1: qualification ⟺ the pair sum vanishes mod p
  have step1 : e2Folded m A = 0 ↔ ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) = 0 := by
    constructor
    · intro h0
      rw [← e2Folded_eval hm1 hg A, h0]
      simp
    · intro hzero
      exact qualifying_implies_char0_vanishing hm1 hg A hp hzero
  -- step 2: the pair sum vanishes ⟺ S_A² = Q_A (2 is invertible)
  have step2 : (∑ q ∈ upperPairs A, g ^ (q.1 + q.2) = 0) ↔
      (∑ i ∈ A, g ^ i) ^ 2 = ∑ i ∈ A, g ^ (2 * i) := by
    have hid := two_mul_pairPow_sum g A
    constructor
    · intro h0
      rw [h0, mul_zero] at hid
      linear_combination -hid
    · intro hq
      have : 2 * ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) = 0 := by
        rw [hid, hq]
        ring
      exact (mul_eq_zero.mp this).resolve_left h2ne
  -- step 3: complement the power sums
  have hS := sum_pow_compl hm1 hg hsub 1 (by
    simpa using sum_pow_range_eq_zero hm1 hg)
  have hQ := sum_pow_compl hm1 hg hsub 2 (sum_pow_sq_range_eq_zero hm hg)
  simp only [one_mul] at hS
  rw [step1, step2]
  constructor
  · intro h
    rw [hS, hQ]
    linear_combination h
  · intro h
    rw [hS, hQ] at h
    linear_combination h

/-! ## Source audit -/

#print axioms two_mul_pairPow_sum
#print axioms sum_pow_range_eq_zero
#print axioms sum_pow_sq_range_eq_zero
#print axioms sum_pow_compl
#print axioms e2Folded_eq_zero_iff_complement_quadric

end ArkLib.ProximityGap.WindowTwoLayer
