/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-! # The deep-band subset-sum spectrum is complement-symmetric (#444)

`DeepBandSubsetSumSpectrum.lean` pins each deep-band bad scalar at depth `k+1` to a subset sum
`gamma_S = - sum_{z in S} z` (`witness_pin_eq_neg_sum`) and names the **exact spectrum
cardinality**

> `|{ sum_{z in S} z : S in powersetCard r mu }|`

as the remaining obstruction to the prize-critical growth law. The growth-law thread-pull on
`#444` records (disentanglement object (3)) the empirical symmetry `#bad_r = #bad_{n-r}`
("subset <-> complement, sum of all roots = 0", listed as *verified* but never a theorem).

This file lands that symmetry as an **unconditional, char-free structural identity** on the
spectrum image, for any finite ground set `mu` whose elements sum to zero (the negation-closed
subgroup `mu_n`, `n` even, satisfies `sum_{z in mu_n} z = 0`):

* `subsetSum_compl` : `sum_{z in mu \ S} z = - sum_{z in S} z` when `sum_{z in mu} z = 0`;
* `spectrum_compl_eq_neg_image` : the depth-`r` spectrum is the **negation** of the
  depth-`(|mu| - r)` spectrum;
* `card_subsetSumSpectrum_eq_compl` (HEADLINE) : `|spectrum r| = |spectrum (|mu| - r)|`.

This is a structural CONSTRAINT on the named obstruction (the spectrum cardinality is a
palindrome in `r`), not a bound on it: it does NOT compute `|spectrum r|` (that exact count is
the prize-critical open quantity = BCHKS 1.12). Field-universal finite combinatorics; thinness
enters only via WHICH `r` is the binding deep band. Makes NO capacity / beyond-Johnson /
growth-law claim; the cliff-at-n/2 is untouched. CORE `M(mu_n) <= C sqrt(n log(p/n))` UNCHANGED.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped Classical


namespace ArkLib.ProximityGap.SpectrumComplementSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- The depth-`r` subset-sum spectrum of a finite ground set `mu`: the set of subset sums over
size-`r` subsets, `{ sum_{z in S} z : S in powersetCard r mu }`. This is exactly the spectrum
named in `DeepBandSubsetSumSpectrum` (up to the harmless overall sign, which does not change the
cardinality). -/
noncomputable def subsetSumSpectrum (mu : Finset F) (r : ℕ) : Finset F :=
  (mu.powersetCard r).image (fun S => ∑ z ∈ S, z)

/-- **Complement subset sum.** If the whole ground set sums to zero, the sum over the complement
`mu \ S` is the negation of the sum over `S`. (For the negation-closed subgroup `mu_n` with
`n` even, `sum_{z in mu_n} z = 0`, so this applies to the deep-band spectrum.) -/
theorem subsetSum_compl {mu S : Finset F} (hS : S ⊆ mu) (htot : ∑ z ∈ mu, z = 0) :
    ∑ z ∈ mu \ S, z = -(∑ z ∈ S, z) := by
  rw [Finset.sum_sdiff_eq_sub hS, htot, zero_sub]

/-- Taking the complement within `mu` is a bijection from size-`r` subsets to size-`(|mu| - r)`
subsets. -/
theorem powersetCard_compl_bij {mu : Finset F} {r : ℕ} (hr : r ≤ mu.card) :
    (mu.powersetCard r).image (fun S => mu \ S) = mu.powersetCard (mu.card - r) := by
  ext T
  simp only [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨S, ⟨hSsub, hScard⟩, rfl⟩
    refine ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hSsub, hScard]
  · rintro ⟨hTsub, hTcard⟩
    refine ⟨mu \ T, ⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset hTsub, hTcard]
      omega
    · rw [Finset.sdiff_sdiff_eq_self hTsub]

/-- **The depth-`r` spectrum is the negation of the depth-`(|mu| - r)` spectrum** (when the whole
ground set sums to zero). The complement bijection `S |-> mu \ S` carries the size-`r` subsets to
the size-`(|mu| - r)` subsets, and `subsetSum_compl` negates each subset sum. -/
theorem spectrum_compl_eq_neg_image {mu : Finset F} {r : ℕ} (hr : r ≤ mu.card)
    (htot : ∑ z ∈ mu, z = 0) :
    subsetSumSpectrum mu (mu.card - r) = (subsetSumSpectrum mu r).image (fun x => -x) := by
  unfold subsetSumSpectrum
  rw [← powersetCard_compl_bij hr, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro S hS
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hS
  simp only [Function.comp]
  exact subsetSum_compl hS.1 htot

/-- **HEADLINE: the subset-sum spectrum cardinality is complement-symmetric**, i.e. a palindrome
in the depth `r`: `|spectrum r| = |spectrum (|mu| - r)|`. Negation is a bijection, so it preserves
cardinality, and the depth-`(|mu|-r)` spectrum is exactly the negated depth-`r` spectrum.

This is the structural constraint behind the empirical `#bad_r = #bad_{n-r}` on `#444`. It pins a
palindrome symmetry on the EXACT spectrum cardinality
`|{ sum_{z in S} z : S in powersetCard r mu_n }|`
named as the open growth-law obstruction in `DeepBandSubsetSumSpectrum`, WITHOUT computing it
(the exact count remains the prize-critical open quantity / BCHKS 1.12). -/
theorem card_subsetSumSpectrum_eq_compl {mu : Finset F} {r : ℕ} (hr : r ≤ mu.card)
    (htot : ∑ z ∈ mu, z = 0) :
    (subsetSumSpectrum mu (mu.card - r)).card = (subsetSumSpectrum mu r).card := by
  rw [spectrum_compl_eq_neg_image hr htot]
  rw [Finset.card_image_of_injective _ neg_injective]

/-- The empty subset gives the single spectrum value `0` at depth `0`, and (when `sum = 0`) the
full subset `mu` gives `0` at depth `|mu|`: the palindrome's endpoints both have cardinality `1`.
(A non-vacuity witness that the symmetry is not over an empty object.) -/
theorem spectrum_zero_card_one (mu : Finset F) :
    (subsetSumSpectrum mu 0).card = 1 := by
  unfold subsetSumSpectrum
  rw [Finset.powersetCard_zero]
  simp

#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.subsetSum_compl
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.spectrum_compl_eq_neg_image
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.card_subsetSumSpectrum_eq_compl
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.spectrum_zero_card_one

end ArkLib.ProximityGap.SpectrumComplementSymmetry
