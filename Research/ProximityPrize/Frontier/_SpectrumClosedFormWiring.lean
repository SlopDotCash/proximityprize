/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSpectrumUpper
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSubsetSumSpectrum

/-!
# Wiring the char-0 subset-sum-spectrum closed form into the deep-band consumer chain (#444)

`Frontier/_SubsetSumSpectrumClosedForm.lean` introduced the char-0 closed form
`spectrumCount m r = ∑_{k ≡ r (2), k ≤ min(r, 2m−r)} C(m,k)·2^k` for the depth-`r` subset-sum
spectrum cardinality of `μ_n` (`m = n/2`), but it was **standalone** (no in-tree consumer).

The in-tree deep-band consumer chain already bounds the genuine object by a `∑ C(|P|,ℓ)·2^ℓ`
ceiling, but with the index range `ℓ ∈ range(r+1)` (i.e. `0 ≤ ℓ ≤ r`, no upper `min`-cap):

* `SpectrumUpper.deepband_spectrum_card_le_choose_sum` — the antipodal-pairing ceiling
  `|spectrum_r| ≤ ∑_{ℓ ≤ r, ℓ ≡ r (2)} C(|P|,ℓ)·2^ℓ` (universal, from `P ⊔ (−P)` alone);
* `SinglePencilSharper.witness_badscalar_card_le_spectrum` — the deep-band bad-scalar count
  injects into that same spectrum `(μ.powersetCard (k+1)).image (fun S => −∑ ζ ∈ S, ζ)`.

This file supplies the missing identification: in the **dilute regime** `r ≤ m` (which is the
ENTIRE near-Johnson / low-depth band — `r = k+1`, `k ≪ n`, `m = n/2`) the `min(r, 2m−r)` cap in
`spectrumCount` is inert (`min r (2m−r) = r`), so the closed form `spectrumCount m r` is **exactly
equal** to the in-tree ceiling RHS. Hence the deep-band bad-scalar count is bounded by the
explicit closed form, with no residual `∑`.

## What this file proves (axiom-clean)

* `spectrumCount_eq_ceiling_of_dilute` — the bridge: `r ≤ m ⟹ spectrumCount m r = ceiling RHS`.
  (The two filtered range sums share index set: `min r (2m−r) = r`, same parity class.)
* `deepband_spectrum_card_le_spectrumCount` — the deep-band subset-sum spectrum cardinality is
  `≤ spectrumCount |P| r` (closed form), in the dilute regime, for `μ = P ⊔ (−P)`.
* `witness_badscalar_card_le_spectrumCount` — **the consumer landing**: the deep-band
  single-pencil bad-scalar count for `μ = P ⊔ (−P)` is `≤ spectrumCount |P| (k+1)`, an explicit
  closed-form ceiling (in the dilute regime `k+1 ≤ |P|`), replacing the generic `∑ C·2^ℓ` upper
  bracket of `DeepBandSubsetSumSpectrum` with the closed form whenever `k+1 ≤ |P|`.

## Honesty (the wall is untouched)

This is a **definitional welding of a closed form into the existing upper bracket**, NOT progress
on the open prize. The EXACT spectrum cardinality (vs this UPPER bound) and its growth law at
prize-binding depth `r = ρn+1 ≫ m` (where the dilute hypothesis FAILS, the `min`-cap engages, and
the `F_p` count is collision-saturated / `p`-dependent) remain the open core. What it buys: the
sharper upper bracket flagged by `DeepBandSubsetSumSpectrum` ("the remaining obstruction is the
EXACT spectrum cardinality") now has its char-0 ceiling expressed as the single closed form
`spectrumCount`, which exact-matches the `0xSolace` `spectsym` probe and carries the proven
palindrome `spectrumCount m r = spectrumCount m (2m−r)`. Issue #444.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.unusedSectionVars false

open Finset
open scoped Classical

namespace ProximityGap.Frontier.SpectrumClosedFormWiring

/-- **The char-0 subset-sum spectrum closed form** (copied from `_SubsetSumSpectrumClosedForm`):
`spectrumCount m r = ∑_{k ≡ r (2), k ≤ min(r, 2m−r)} C(m,k)·2^k`. -/
def spectrumCount (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2), m.choose k * 2 ^ k

/-- **The dilute-regime bridge.** For `r ≤ m`, the closed form `spectrumCount m r` equals the
in-tree antipodal ceiling RHS `∑_{ℓ ≤ r, ℓ ≡ r (2)} C(m,ℓ)·2^ℓ`: the `min(r, 2m−r)` cap is inert
(`min r (2m−r) = r` since `r ≤ m ≤ 2m−r`), so the two filtered ranges are the SAME index set. -/
theorem spectrumCount_eq_ceiling_of_dilute (m r : ℕ) (hr : r ≤ m) :
    spectrumCount m r
      = ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2), m.choose ℓ * 2 ^ ℓ := by
  unfold spectrumCount
  have hmin : min r (2 * m - r) = r := by omega
  rw [hmin]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The deep-band spectrum cardinality is bounded by the closed form** (dilute regime). For a
negation-closed domain `μ = P ⊔ (−P)` and depth `r ≤ |P|`, the `−∑`-spectrum cardinality is at
most `spectrumCount |P| r`. Chains the in-tree antipodal ceiling
`SpectrumUpper.deepband_spectrum_card_le_choose_sum` with the dilute bridge. -/
theorem deepband_spectrum_card_le_spectrumCount
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    (μ : Finset F) (hμ : μ = P ∪ P.image (fun p => -p)) (r : ℕ) (hr : r ≤ P.card) :
    ((μ.powersetCard r).image (fun S => -∑ a ∈ S, a)).card ≤ spectrumCount P.card r := by
  rw [spectrumCount_eq_ceiling_of_dilute P.card r hr]
  exact ArkLib.ProximityGap.SpectrumUpper.deepband_spectrum_card_le_choose_sum P hPneg μ hμ r

/-- **The consumer landing: deep-band single-pencil bad-scalar count `≤ spectrumCount` (closed
form).** For `μ = P ⊔ (−P)` negation-closed and depth `k + 1 ≤ |P|` (the dilute / near-Johnson
band), the number of bad scalars `γ` for the deep-band witness pencil `X^{k+1} + γ·X^k` on `μ` is
at most the explicit closed form `spectrumCount |P| (k+1)`.

Chains the in-tree `SinglePencilSharper.witness_badscalar_card_le_spectrum` (bad-count injects
into the spectrum) with `deepband_spectrum_card_le_spectrumCount` (spectrum ≤ closed form). This
replaces the generic `∑ C(|P|,ℓ)·2^ℓ` upper bracket with the single closed form `spectrumCount`
in the dilute regime — exact-matching the `spectsym` probe and carrying the proven palindrome. -/
theorem witness_badscalar_card_le_spectrumCount
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    (μ : Finset F) (hμ : μ = P ∪ P.image (fun p => -p)) (k : ℕ) (hk : k + 1 ≤ P.card) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : Polynomial F, W.natDegree < k ∧
          k + 1 ≤ (μ.filter (fun ζ =>
            (Polynomial.X ^ (k + 1) + Polynomial.C γ * Polynomial.X ^ k - W).eval ζ = 0)).card)).card
      ≤ spectrumCount P.card (k + 1) := by
  classical
  exact le_trans (ArkLib.ProximityGap.SinglePencilSharper.witness_badscalar_card_le_spectrum μ k)
    (deepband_spectrum_card_le_spectrumCount P hPneg μ hμ (k + 1) hk)

end ProximityGap.Frontier.SpectrumClosedFormWiring

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.SpectrumClosedFormWiring.spectrumCount_eq_ceiling_of_dilute
#print axioms ProximityGap.Frontier.SpectrumClosedFormWiring.deepband_spectrum_card_le_spectrumCount
#print axioms ProximityGap.Frontier.SpectrumClosedFormWiring.witness_badscalar_card_le_spectrumCount
