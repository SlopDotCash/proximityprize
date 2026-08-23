/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SubsetSumSpectrumClosedForm

/-!
# The rising-half second-difference recurrence of the subset-sum spectrum (#444)

For the 2-power subgroup `μ_n` (`n = 2^μ`, `m = n/2`) the depth-`r` char-0 subset-sum spectrum
cardinality `N_r = spectrumCount m r` (the deep-band bad-scalar count `#bad_r`, via the in-tree
`_SubsetSumSpectrumClosedForm`) satisfies, on the **rising half** `2 ≤ r ≤ m`, the exact
two-step recurrence

```
N_r − N_{r−2}  =  C(m, r) · 2^r.
```

**Mechanism (NOT a moment method).** `spectrumCount m r` filters `k ∈ {0,…,min(r,2m−r)}` on the
parity class `k ≡ r (mod 2)`. On the rising half `min(r,2m−r)=r` and `min(r−2,2m−(r−2))=r−2`, and
the two parity classes coincide (`r` and `r−2` are congruent mod 2). So the two sums run over the
**same parity class** but `range (r+1)` vs `range (r−1)`. The only index added going from `r−2` to
`r` that survives the parity filter is `k = r` itself (`k = r−1` is the *wrong* parity), whose term
is `C(m,r)·2^r`. This is the **leading antipodal cross-polytope term** of `N_r`: the recurrence
says each two-step rise of the spectrum is *exactly* the top antipodal term, with no lower-order
mixing. It exposes `N_r = Σ_{j≥0} C(m, r−2j)·2^{r−2j}` (the parity-class partial sum) and pins the
dominant part `C(m,r)·2^r` of the deep-band census.

Probe `scripts/probes/probe_spectrum_rising_step.py` (exact big-int, thin tower m=8,16,32,64,
never n=q−1): `N_r − N_{r−2} = C(m,r)·2^r` for every `2 ≤ r ≤ m`, and `N_r = Σ_j C(m,r−2j)2^{r−2j}`,
VERDICT PASS.

**HONESTY.** This is the char-0 spectrum recurrence; it does NOT close CORE. At the binding depth
`r = ρn+1` the `F_p` count is collision-saturated and `p`-dependent (BGK/BCHKS wall), where this
char-0 identity no longer transfers. It is a structural census brick extending the in-tree
`spectrumCount`, NOT a moment/energy method and NOT a beyond-Johnson / capacity claim. Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.SubsetSumSpectrum

/-- On the **rising half** `r ≤ m`, the range bound collapses: `min r (2*m − r) = r`. -/
theorem min_eq_left_rising {m r : ℕ} (hrm : r ≤ m) : min r (2 * m - r) = r := by
  apply min_eq_left
  omega

/-- The parity classes of `r` and `r − 2` coincide (when `2 ≤ r`). -/
theorem parity_sub_two {r : ℕ} (hr : 2 ≤ r) : (r - 2) % 2 = r % 2 := by
  omega

/-- **The rising-half spectrum, unfolded.** For `2 ≤ r ≤ m`,
`spectrumCount m r = Σ_{k ∈ range (r+1), k ≡ r (2)} C(m,k)·2^k`. -/
theorem spectrumCount_rising (m r : ℕ) (hrm : r ≤ m) :
    spectrumCount m r =
      ∑ k ∈ (range (r + 1)).filter (fun k => k % 2 = r % 2), m.choose k * 2 ^ k := by
  unfold spectrumCount
  rw [min_eq_left_rising hrm]

/-- **HEADLINE: the rising-half second-difference recurrence.** For `2 ≤ r ≤ m`,
`spectrumCount m r = spectrumCount m (r - 2) + C(m, r) · 2 ^ r`. Each two-step rise of the deep-band
subset-sum census is *exactly* the leading antipodal term `C(m,r)·2^r`. -/
theorem spectrumCount_rising_step (m r : ℕ) (hr : 2 ≤ r) (hrm : r ≤ m) :
    spectrumCount m r = spectrumCount m (r - 2) + m.choose r * 2 ^ r := by
  have hrm2 : r - 2 ≤ m := by omega
  rw [spectrumCount_rising m r hrm, spectrumCount_rising m (r - 2) hrm2]
  rw [parity_sub_two hr]
  -- The two sums share the same parity predicate `fun k => k % 2 = r % 2`.
  -- range ((r-2)+1) = range (r-1); we split range (r+1) = range (r-1) ∪ {r-1, r}.
  -- Split the range: range (r+1) = range (r-1) ∪ Ioc (r-2) r, then filter by parity.
  have hrange : range (r + 1) = range (r - 2 + 1) ∪ Finset.Ioc (r - 2) r := by
    ext k
    simp only [mem_union, mem_range, mem_Ioc]
    omega
  have hsplit :
      (range (r + 1)).filter (fun k => k % 2 = r % 2)
        = (range (r - 2 + 1)).filter (fun k => k % 2 = r % 2)
            ∪ (Finset.Ioc (r - 2) r).filter (fun k => k % 2 = r % 2) := by
    rw [hrange, filter_union]
  rw [hsplit]
  rw [Finset.sum_union]
  · -- the upper piece (Ioc (r-2) r filtered by parity) is exactly {r}, summing to C(m,r)2^r.
    congr 1
    have hIoc : (Finset.Ioc (r - 2) r).filter (fun k => k % 2 = r % 2) = {r} := by
      ext k
      simp only [mem_filter, mem_Ioc, mem_singleton]
      constructor
      · rintro ⟨⟨_, _⟩, hpar⟩; omega
      · rintro rfl; exact ⟨⟨by omega, le_rfl⟩, rfl⟩
    rw [hIoc, Finset.sum_singleton]
  · -- disjointness of the two filtered index sets.
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro k hk hk2
    simp only [mem_range] at hk
    simp only [mem_Ioc] at hk2
    omega

/-- **The parity-class partial-sum form.** Iterating the rising step:
`spectrumCount m r = Σ_{j} C(m, r − 2j) · 2^{r − 2j}`, verified at the tower anchors. -/
theorem spectrumCount_rising_anchors :
    spectrumCount 8 2 = spectrumCount 8 0 + Nat.choose 8 2 * 2 ^ 2 ∧
    spectrumCount 16 2 = spectrumCount 16 0 + Nat.choose 16 2 * 2 ^ 2 ∧
    spectrumCount 16 4 = spectrumCount 16 2 + Nat.choose 16 4 * 2 ^ 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold spectrumCount; decide)

/-- Concrete anchor: `N_2 = N_0 + C(m,2)·4` at `m = 8`: `113 = 1 + 112`. -/
theorem spectrumCount_rising_n8_r2 : spectrumCount 8 2 = 113 ∧ spectrumCount 8 0 = 1 := by
  refine ⟨?_, ?_⟩ <;> (unfold spectrumCount; decide)

#print axioms spectrumCount_rising_step
#print axioms spectrumCount_rising
#print axioms spectrumCount_rising_anchors

end ProximityGap.Frontier.SubsetSumSpectrum
