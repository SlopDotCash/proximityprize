/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairSumsWiring

/-!
# The census doubling functor: qualification lifts along the 2-power tower

Campaign #357. The depth-1 census system has a **doubling functor**: the map
`exponent ↦ 2·exponent` sends scale-`2^m` configurations to scale-`2^(m+1)` configurations,
and it preserves census qualification **exactly**:

> **`e2Folded_double_iff`** — `e2Folded (m+1) (A.image (2·)) = 0 ↔ e2Folded m A = 0`.

Mechanism: doubled pair sums occupy only even residues (`(2s) % 2^(m+1) = 2·(s % 2^m)`),
odd fibers are empty on both sides of the antipodal pairing, and the even fibers biject
with the original fibers — so balance at the doubled scale **is** balance at the original
scale. This is the formal backbone of the probe-verified persistence of the `a = 9`
sporadic family (`probe_a9_exceptional_family.py` + the n = 32/64 doubling checks): every
scale's census embeds in the next, and "primitive vs lifted" is the right stratification
of the depth-1 system — the same dichotomy the census programme uses for its second-layer
families.

## References

* Probes `probe_a9_exceptional_family.py`, `probe_coset_core_conjecture.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.WindowTwoLayer

/-- Doubling identifies the ordered pairs of the doubled set with the original pairs. -/
theorem upperPairs_double (A : Finset ℕ) :
    upperPairs (A.image (2 * ·))
      = (upperPairs A).image (fun q => (2 * q.1, 2 * q.2)) := by
  ext q
  simp only [upperPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
    Prod.ext_iff]
  constructor
  · rintro ⟨⟨⟨i, hi, hqi⟩, ⟨j, hj, hqj⟩⟩, hlt⟩
    exact ⟨(i, j), ⟨⟨hi, hj⟩, by omega⟩, by omega, by omega⟩
  · rintro ⟨⟨i, j⟩, ⟨⟨hi, hj⟩, hlt⟩, h1, h2⟩
    simp only at h1 h2
    refine ⟨⟨⟨i, hi, by omega⟩, ⟨j, hj, by omega⟩⟩, by omega⟩

/-- The doubled fiber over an even residue is the original fiber over its half. -/
theorem double_fiber_card (A : Finset ℕ) (m : ℕ) (t : ℕ) :
    ((upperPairs (A.image (2 * ·))).filter
        (fun q => (q.1 + q.2) % 2 ^ (m + 1) = 2 * t)).card
      = ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card := by
  rw [upperPairs_double, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    refine Finset.filter_congr fun q _ => ?_
    have hmm : (2 * q.1 + 2 * q.2) % 2 ^ (m + 1) = 2 * ((q.1 + q.2) % 2 ^ m) := by
      rw [show 2 * q.1 + 2 * q.2 = 2 * (q.1 + q.2) from by ring, pow_succ',
        Nat.mul_mod_mul_left]
    rw [hmm]
    omega
  · intro q _ q' _ hq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hq
    simp only at h1 h2
    exact Prod.ext (by omega) (by omega)

/-- Odd fibers of a doubled set are empty. -/
theorem double_fiber_odd (A : Finset ℕ) (m : ℕ) {t : ℕ} (ht : t % 2 = 1) :
    ((upperPairs (A.image (2 * ·))).filter
        (fun q => (q.1 + q.2) % 2 ^ (m + 1) = t)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  rw [upperPairs_double] at hq
  obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hq
  intro hc
  simp only at hc
  have h2 : (2 * i + 2 * j) % 2 ^ (m + 1) % 2 = 0 := by
    have hdvd : (2 : ℕ) ∣ 2 ^ (m + 1) := dvd_pow_self 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ hdvd]
    omega
  omega

/-- **The doubling functor preserves census qualification exactly.** -/
theorem e2Folded_double_iff (m : ℕ) (hm : 1 ≤ m) (A : Finset ℕ) :
    e2Folded (m + 1) (A.image (2 * ·)) = 0 ↔ e2Folded m A = 0 := by
  rw [e2Folded_eq_foldedSum, e2Folded_eq_foldedSum, foldedSum_eq_zero_iff_balanced,
    foldedSum_eq_zero_iff_balanced]
  constructor
  · -- doubled balance restricts to the even fibers
    intro hbal t ht
    have h2 := hbal (2 * t) (by
      have : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega)
    rw [double_fiber_card, show 2 * t + 2 ^ (m + 1 - 1) = 2 * (t + 2 ^ (m - 1)) from by
      have : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega, double_fiber_card] at h2
    exact h2
  · -- original balance covers even fibers; odd fibers are empty on both sides
    intro hbal t ht
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · have hsm : s < 2 ^ (m - 1) := by
        have : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        omega
      rw [show t = 2 * s from by omega, double_fiber_card,
        show 2 * s + 2 ^ (m + 1 - 1) = 2 * (s + 2 ^ (m - 1)) from by
          have : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          omega, double_fiber_card]
      exact hbal s hsm
    · rw [double_fiber_odd A m (by omega), double_fiber_odd A m (by
        have h2d : (2 : ℕ) ∣ 2 ^ (m + 1 - 1) := dvd_pow_self 2 (by omega)
        omega)]

/-! ## Source audit -/

#print axioms upperPairs_double
#print axioms double_fiber_card
#print axioms double_fiber_odd
#print axioms e2Folded_double_iff

end ArkLib.ProximityGap.WindowTwoLayer
