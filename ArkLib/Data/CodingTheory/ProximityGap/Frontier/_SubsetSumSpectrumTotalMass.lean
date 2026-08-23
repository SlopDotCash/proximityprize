/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SubsetSumSpectrumClosedForm
import Mathlib.Tactic

/-!
# The total char-0 subset-sum spectrum mass of the 2-power subgroup: exact closed form (#444)

Extends the just-landed `_SubsetSumSpectrumClosedForm.spectrumCount` (the depth-`r` char-0
subset-sum cardinality `N_r(ℂ) = Σ_{k≡r(2), k≤min(r,2m−r)} C(m,k)·2^k`, `m = n/2`) to the **total
summed over all depths `r = 0 … 2m`** (the total number of distinct subset sums counted with their
depth multiplicity):

```
  T(m) := Σ_{r=0}^{2m} N_r  =  3^{m-1} · (m + 3).
```

**Mechanism (depth-multiplicity reindexing, NOT a moment/energy method).** In `N_r` a net-vector
class with `k` nonzero entries (contributing `C(m,k)·2^k`) is reachable at depth `r` iff
`k ≡ r (mod 2)` and `k ≤ r ≤ 2m − k`. The count of admissible `r ∈ {0,…,2m}` in that AP is
exactly `m − k + 1`. Hence

```
  T(m) = Σ_{k=0}^{m} (m − k + 1) · C(m,k) · 2^k
       = (m+1)·Σ_k C(m,k)2^k  −  Σ_k k·C(m,k)2^k
       = (m+1)·3^m − 2m·3^{m-1}            -- the two binomial GF sums
       = 3^{m-1}·(m + 3).
```

The two component GF identities are exact:
* `Σ_{k=0}^{m} C(m,k)·2^k = 3^m`            (binomial theorem `(1+2)^m`);
* `Σ_{k=0}^{m} k·C(m,k)·2^k = 2m·3^{m-1}`   (`k·C(m,k) = m·C(m−1,k−1)`, then `(1+2)^{m-1}`).

**HONESTY (rules 1,3,4,6 + ASYMPTOTIC GUARD).** This is an exact char-0 *count* identity extending a
proven in-tree theorem (extend-proven). It is a STRUCTURAL census fact about the deep-band
bad-scalar object (`N_r = #bad_r` via `DeepBandSubsetSumSpectrum.witness_pin`), giving the total
over all depths in closed form. It does NOT close CORE: the prize-binding object is the *per-depth*
growth `N_{ρn+1}` at the binding depth, not the total mass, and the char-0 to `F_p` bridge
`N_r(ℂ)=N_r(F_p)` holds only in the dilute `N_r ≪ p` regime (the binding depth is
collision-saturated = the BGK/BCHKS wall). NO capacity / beyond-Johnson / sub-linear / growth-law
claim; the ASYMPTOTIC-GUARD cliff-at-n/2 is untouched. CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED /
OPEN. 2-power-specific (the closed-form `spectrumCount` it builds on is verified to fail at
non-2-power `n`). Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.SubsetSumSpectrum

/-- **Total char-0 subset-sum spectrum mass**: `T(m) = Σ_{r=0}^{2m} N_r`. -/
def spectrumTotal (m : ℕ) : ℕ :=
  ∑ r ∈ range (2 * m + 1), spectrumCount m r

/-- The depth-multiplicity `k`-form: `Σ_{k=0}^{m} (m − k + 1) · C(m,k) · 2^k`. -/
def spectrumTotalKForm (m : ℕ) : ℕ :=
  ∑ k ∈ range (m + 1), (m - k + 1) * (m.choose k * 2 ^ k)

/-- **GF identity 1**: `Σ_{k=0}^{m} C(m,k)·2^k = 3^m` (binomial theorem at `1 + 2`). -/
theorem sum_choose_two_pow (m : ℕ) :
    ∑ k ∈ range (m + 1), m.choose k * 2 ^ k = 3 ^ m := by
  have h := (add_pow 2 1 m).symm
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [show (3 : ℕ) = 2 + 1 from rfl, ← h]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **GF identity 2**: `Σ_{k=0}^{m} k·C(m,k)·2^k = 2m·3^{m-1}` via `k·C(m,k)=m·C(m−1,k−1)` + GF1. -/
theorem sum_k_choose_two_pow (m : ℕ) :
    ∑ k ∈ range (m + 1), k * (m.choose k * 2 ^ k) = 2 * m * 3 ^ (m - 1) := by
  rcases m with _ | m
  · simp
  · -- shift index k = j+1
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul, Nat.choose_zero_right, Nat.pow_zero, Nat.mul_zero, Nat.add_zero,
      zero_mul, add_zero]
    -- term j+1: (j+1) * (C(m+1, j+1) * 2^(j+1))
    -- use (j+1)*C(m+1,j+1) = (m+1)*C(m,j)   [add_one_mul_choose_eq / succ_mul_choose_eq]
    have hkey : ∀ j ∈ range (m + 1),
        (j + 1) * ((m + 1).choose (j + 1) * 2 ^ (j + 1))
          = (m + 1) * (m.choose j * 2 ^ j) * 2 := by
      intro j _
      have hc : (m + 1) * m.choose j = (m + 1).choose (j + 1) * (j + 1) := by
        have := Nat.succ_mul_choose_eq m j
        simpa [Nat.succ_eq_add_one] using this
      have : (j + 1) * (m + 1).choose (j + 1) = (m + 1) * m.choose j := by
        rw [hc]; ring
      calc (j + 1) * ((m + 1).choose (j + 1) * 2 ^ (j + 1))
          = ((j + 1) * (m + 1).choose (j + 1)) * 2 ^ (j + 1) := by ring
        _ = ((m + 1) * m.choose j) * 2 ^ (j + 1) := by rw [this]
        _ = (m + 1) * (m.choose j * 2 ^ j) * 2 := by rw [pow_succ]; ring
    rw [Finset.sum_congr rfl hkey]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_choose_two_pow m]
    simp only [Nat.add_sub_cancel]
    ring

/-- **The k-form closed form**: `Σ_{k}(m−k+1)C(m,k)2^k = 3^{m-1}·(m+3)`, via GF1 + GF2. -/
theorem spectrumTotalKForm_closed (m : ℕ) (hm : 1 ≤ m) :
    spectrumTotalKForm m = 3 ^ (m - 1) * (m + 3) := by
  unfold spectrumTotalKForm
  -- (m-k+1) = (m+1) - k  on range (m+1)
  have hsplit : ∀ k ∈ range (m + 1),
      (m - k + 1) * (m.choose k * 2 ^ k)
        = (m + 1) * (m.choose k * 2 ^ k) - k * (m.choose k * 2 ^ k) := by
    intro k hk
    rw [mem_range] at hk
    have hkm : k ≤ m := by omega
    have : m - k + 1 = (m + 1) - k := by omega
    rw [this, Nat.sub_mul]
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_tsub_distrib]
  · rw [← Finset.mul_sum, sum_choose_two_pow, sum_k_choose_two_pow]
    -- (m+1)*3^m - 2*m*3^(m-1) = 3^(m-1)*(m+3)
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h3 : (3 : ℕ) ^ (m' + 1) = 3 * 3 ^ m' := by rw [pow_succ]; ring
    rw [h3]
    -- (m'+2)*(3*3^m') - 2*(m'+1)*3^m' = 3^m'*(m'+4)
    have expand : (m' + 1 + 1) * (3 * 3 ^ m') = 3 ^ m' * (3 * m' + 6) := by ring
    have expand2 : 2 * (m' + 1) * 3 ^ m' = 3 ^ m' * (2 * m' + 2) := by ring
    rw [expand, expand2, ← Nat.mul_sub]
    congr 1
    omega
  · -- pointwise k*(...) ≤ (m+1)*(...)
    intro k hk
    rw [mem_range] at hk
    have : k ≤ m + 1 := by omega
    exact Nat.mul_le_mul_right _ (by omega)

/-- The admissible-depth predicate: for a net-vector class with `k` nonzeros, the reachable depths
`r ∈ {0,…,2m}` are exactly those with `k ≤ r`, `r ≤ 2m − k`, and `r ≡ k (mod 2)`. -/
private def admDepth (m k r : ℕ) : Prop := k ≤ r ∧ r ≤ 2 * m - k ∧ r % 2 = k % 2

instance (m k r : ℕ) : Decidable (admDepth m k r) := by unfold admDepth; infer_instance

/-- For `k ≤ m`, the number of admissible depths `r ∈ {0,…,2m}` is exactly `m − k + 1`
(the AP `k, k+2, …, 2m−k`). -/
private theorem card_admDepth (m k : ℕ) (hk : k ≤ m) :
    ((range (2 * m + 1)).filter (admDepth m k)).card = m - k + 1 := by
  -- bijection r ↦ (r − k)/2 onto range (m − k + 1)
  rw [← Finset.card_range (m - k + 1)]
  apply Finset.card_bij' (fun r _ => (r - k) / 2) (fun j _ => k + 2 * j)
  · intro r hr
    simp only [mem_filter, mem_range, admDepth] at hr
    obtain ⟨_, ⟨hkr, hru, hpar⟩⟩ := hr
    rw [mem_range]
    omega
  · intro j hj
    rw [mem_range] at hj
    simp only [mem_filter, mem_range, admDepth]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · intro r hr
    simp only [mem_filter, mem_range, admDepth] at hr
    obtain ⟨_, ⟨hkr, hru, hpar⟩⟩ := hr
    omega
  · intro j hj
    rw [mem_range] at hj
    omega

/-- Rewrite `spectrumCount m r` (`r ≤ 2m`) as a filtered sum over the *full* `range(2m+1)` of `k`,
with the admissible-depth predicate, so the depths and the `k`-index live on comparable ranges. -/
private theorem spectrumCount_as_filter (m r : ℕ) (hr : r ≤ 2 * m) :
    spectrumCount m r
      = ∑ k ∈ (range (2 * m + 1)).filter (fun k => admDepth m k r),
          m.choose k * 2 ^ k := by
  unfold spectrumCount
  apply Finset.sum_congr
  · ext k
    simp only [mem_filter, mem_range, admDepth]
    omega
  · intro k _; rfl

/-- **The depth-multiplicity swap.** `Σ_{r=0}^{2m} N_r = Σ_{k=0}^{m} (m−k+1)·C(m,k)·2^k`. -/
theorem spectrumTotal_eq_kForm (m : ℕ) : spectrumTotal m = spectrumTotalKForm m := by
  unfold spectrumTotal spectrumTotalKForm
  -- rewrite each inner spectrumCount as a filtered sum over k ∈ range(2m+1)
  have hrw : ∀ r ∈ range (2 * m + 1),
      spectrumCount m r
        = ∑ k ∈ (range (2 * m + 1)).filter (fun k => admDepth m k r), m.choose k * 2 ^ k := by
    intro r hr; rw [mem_range] at hr; exact spectrumCount_as_filter m r (by omega)
  rw [Finset.sum_congr rfl hrw]
  -- turn filtered inner sums into indicator sums over the full k-range, then swap
  have hind : ∀ r ∈ range (2 * m + 1),
      (∑ k ∈ (range (2 * m + 1)).filter (fun k => admDepth m k r), m.choose k * 2 ^ k)
        = ∑ k ∈ range (2 * m + 1), (if admDepth m k r then m.choose k * 2 ^ k else 0) := by
    intro r _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hind, Finset.sum_comm]
  -- now: Σ_{k∈range(2m+1)} Σ_{r∈range(2m+1)} (if adm then C2^k else 0)
  -- = Σ_k C2^k * card{r : adm}
  have hk : ∀ k ∈ range (2 * m + 1),
      (∑ r ∈ range (2 * m + 1), (if admDepth m k r then m.choose k * 2 ^ k else 0))
        = (if k ≤ m then (m - k + 1) * (m.choose k * 2 ^ k) else 0) := by
    intro k hkmem
    rw [mem_range] at hkmem
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    by_cases hkm : k ≤ m
    · rw [card_admDepth m k hkm, if_pos hkm, smul_eq_mul]
    · rw [if_neg hkm]
      have hempty : (range (2 * m + 1)).filter (admDepth m k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r _
        simp only [admDepth, not_and]
        intro hkr hru
        -- k ≤ r ≤ 2m − k with k > m forces k ≤ 2m − k i.e. k ≤ m, contradiction
        omega
      rw [hempty]
      simp
  rw [Finset.sum_congr rfl hk]
  -- collapse range(2m+1) → range(m+1): the tail k∈[m+1,2m] all have if-false = 0
  have hsub : range (m + 1) ⊆ range (2 * m + 1) := by
    intro x hx; rw [mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro k hkmem
    rw [mem_range] at hkmem
    split
    · rfl
    · omega
  · intro k _ hknot
    rw [mem_range] at hknot
    split
    · omega
    · rfl

/-- **HEADLINE: the total char-0 subset-sum spectrum mass of `μ_n` (`m = n/2`):**
`Σ_{r=0}^{2m} N_r = 3^{m-1}·(m+3)`. Extends `_SubsetSumSpectrumClosedForm.spectrumCount` from the
per-depth count to the total over all depths, via the depth-multiplicity swap + the two binomial
GF sums. Axiom-clean; NOT a CORE closure (the prize binds the per-depth growth, not the total). -/
theorem spectrumTotal_closed (m : ℕ) (hm : 1 ≤ m) :
    spectrumTotal m = 3 ^ (m - 1) * (m + 3) := by
  rw [spectrumTotal_eq_kForm, spectrumTotalKForm_closed m hm]

/-- Verified small values of the total mass: `T(1)=4, T(2)=15, T(3)=54, T(4)=189` (`n=2,4,6,8`),
matching the probe `probe_spectrum_total`. -/
theorem spectrumTotal_values :
    spectrumTotal 1 = 4 ∧ spectrumTotal 2 = 15 ∧ spectrumTotal 3 = 54 ∧ spectrumTotal 4 = 189 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold spectrumTotal spectrumCount; decide)

/-- Cross-check: the closed form agrees with the direct definition at `n = 16` (`m = 8`):
`T(8) = 3^7·11 = 24057`. -/
theorem spectrumTotal_n16 : spectrumTotal 8 = 24057 := by
  rw [spectrumTotal_closed 8 (by norm_num)]; norm_num

end ProximityGap.Frontier.SubsetSumSpectrum

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumTotal_closed
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumTotal_eq_kForm
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumTotalKForm_closed
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.sum_choose_two_pow
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.sum_k_choose_two_pow
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumTotal_values
#print axioms ProximityGap.Frontier.SubsetSumSpectrum.spectrumTotal_n16
