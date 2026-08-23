/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDonohoStark

/-!
# Fourier-sparse functions have few zeros — the LD-radius form of the uncertainty principle (#407)

The #407 c.349 reformulation: the far-line list-decoding radius over `μ_n ≅ Z_n` is `n − (min support
of a Fourier-sparse function)`, and the agreement polynomial `x^a+γx^b−c` (deg `< k`) restricts to a
function with DFT support `≤ k+2` (`_RThinSparseRealizability.agreementPoly_support_card_le`). So the
uncertainty principle directly bounds how many points such a function can vanish on.

This file lands that consequence of `_ZModDonohoStark.donoho_stark`:

> if `𝓕Φ` is `t`-Fourier-sparse (`|supp 𝓕Φ| ≤ t`) and `Φ ≠ 0`, then `|supp Φ| ≥ N/t`, i.e. `Φ`
> vanishes on at most `N − N/t = N(1 − 1/t)` of the `N` points.

For `t = k+2` on `Z_n` this is the Donoho–Stark list-decoding radius bound `≤ n(1 − 1/(k+2))`. (The
prime-`n` Tao bound `≤ k+1` = capacity is strictly stronger; the gap between Donoho–Stark (composite,
incl. `2^μ`) and Tao (prime) is exactly the [349] Johnson-vs-capacity dichotomy.) Axiom-clean. #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark

namespace ProximityGap.Frontier.FourierSparseZeros

variable {N : ℕ} [NeZero N]

/-- **Fourier-sparse ⟹ large support.** If `𝓕Φ` has support `≤ t` and `Φ ≠ 0`, then `N ≤ t·|supp Φ|`
(so `|supp Φ| ≥ N/t`). Immediate from Donoho–Stark `|supp Φ|·|supp 𝓕Φ| ≥ N` and `|supp 𝓕Φ| ≤ t`. -/
theorem card_supp_ge_of_dft_sparse (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) {t : ℕ}
    (ht : (supp (𝓕 Φ)).card ≤ t) :
    (N : ℝ) ≤ t * (supp Φ).card := by
  have hds : (N : ℝ) ≤ (supp Φ).card * (supp (𝓕 Φ)).card := donoho_stark Φ hΦ
  have htR : ((supp (𝓕 Φ)).card : ℝ) ≤ t := by exact_mod_cast ht
  calc (N : ℝ) ≤ (supp Φ).card * (supp (𝓕 Φ)).card := hds
    _ ≤ (supp Φ).card * t := by
        apply mul_le_mul_of_nonneg_left htR (by positivity)
    _ = t * (supp Φ).card := by ring

/-- **The list-decoding-radius form:** a `t`-Fourier-sparse `Φ ≠ 0` vanishes on at most `N − N/t`
points, i.e. the number of zeros `Z = N − |supp Φ|` satisfies `Z ≤ N·(1 − 1/t)` (`t ≥ 1`). This is the
uncertainty-principle bound on the far-line agreement/LD radius (`t = k+2` gives `≤ n(1 − 1/(k+2))`). -/
theorem zeros_le_of_dft_sparse (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : (supp (𝓕 Φ)).card ≤ t) :
    ((univ.filter (fun j => Φ j = 0)).card : ℝ) ≤ (N : ℝ) * (1 - 1 / t) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  -- |supp Φ| ≥ N/t
  have hsupp : (N : ℝ) / t ≤ (supp Φ).card := by
    rw [div_le_iff₀ htpos]
    have := card_supp_ge_of_dft_sparse Φ hΦ ht
    linarith [this]
  -- zeros = N − |supp Φ|
  have hcompl : (univ.filter (fun j => Φ j = 0)).card + (supp Φ).card = N := by
    rw [supp]
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (ZMod N)))
      (p := fun j => Φ j = 0)
    simpa [ZMod.card, eq_comm, Finset.filter_not] using this
  have hz : ((univ.filter (fun j => Φ j = 0)).card : ℝ) = (N : ℝ) - (supp Φ).card := by
    have : ((univ.filter (fun j => Φ j = 0)).card : ℝ) + (supp Φ).card = N := by exact_mod_cast hcompl
    linarith
  rw [hz]
  have : (N : ℝ) * (1 - 1 / t) = N - N / t := by ring
  rw [this]; linarith [hsupp]

end ProximityGap.Frontier.FourierSparseZeros

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.FourierSparseZeros.card_supp_ge_of_dft_sparse
#print axioms ProximityGap.Frontier.FourierSparseZeros.zeros_le_of_dft_sparse
