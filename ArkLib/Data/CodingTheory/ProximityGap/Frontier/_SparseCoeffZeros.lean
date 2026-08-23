/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FourierSparseZeros

/-!
# Sparse-coefficient signals have few zeros — the agreement-polynomial form (#407)

The #407 c.349 reformulation in its prize-facing direction: the far-line **agreement polynomial**
`x^a + γ·x^b − c` (deg `< k`) has SPARSE COEFFICIENTS — support `⊆ {0,…,k−1, a, b}`, ≤ `k+2` nonzero
coefficients (`_RThinSparseRealizability.agreementPoly_support_card_le`). Evaluated at the `n`-th
roots it is `𝓕(coeff-vector)` of a `(k+2)`-sparse vector on `Z_n`. This file converts "sparse
coefficients" into the far-line agreement / list-decoding radius bound, via `dft_dft` +
`_FourierSparseZeros`:

> if `c` is `t`-sparse (`|supp c| ≤ t`, `c ≠ 0`), then `𝓕 c` vanishes on at most `N·(1 − 1/t)` points.

For `t = k+2` on `Z_n` this is the char-0 far-line agreement-set bound `≤ n·(1 − 1/(k+2))` — the
Donoho–Stark list-decoding radius for the smooth (`2`-power) domain. (Combined with
`_ZModSubgroupSaturation`, which shows subgroups saturate the uncertainty principle, this is the
[349] picture: composite `n` gives only this Johnson-scale bound, prime `n` gives capacity.)
Axiom-clean. Issue #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.FourierSparseZeros

namespace ProximityGap.Frontier.SparseCoeffZeros

variable {N : ℕ} [NeZero N]

/-- The DFT of `𝓕 c` has the same support cardinality as `c` (via `dft_dft`: `𝓕(𝓕 c) = N·c(−·)`, and
`j ↦ −j` is a bijection). -/
theorem supp_dft_dft_card (c : ZMod N → ℂ) :
    (supp (𝓕 (𝓕 c))).card = (supp c).card := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have heq : supp (𝓕 (𝓕 c)) = (supp c).map (Equiv.neg (ZMod N)).toEmbedding := by
    ext j
    simp only [supp, Finset.mem_map, mem_filter, mem_univ, true_and, dft_dft, Pi.smul_apply,
      smul_eq_mul, mul_ne_zero_iff, Equiv.coe_toEmbedding, Equiv.neg_apply]
    constructor
    · intro h
      exact ⟨-j, h.2, neg_neg j⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨hNc, by rwa [neg_neg]⟩
  rw [heq, Finset.card_map]

/-- **Sparse-coefficient signals have few zeros.** If `c : ZMod N → ℂ` is `t`-sparse and nonzero, the
signal `𝓕 c` (its evaluation at the `N`-th roots) vanishes on at most `N·(1 − 1/t)` points — the
far-line list-decoding radius bound for a `(k+2)`-sparse agreement polynomial (`t = k+2`). -/
theorem sparse_coeff_zeros_le (c : ZMod N → ℂ) (hc : c ≠ 0) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : (supp c).card ≤ t) :
    ((univ.filter (fun j => (𝓕 c) j = 0)).card : ℝ) ≤ (N : ℝ) * (1 - 1 / t) := by
  have hFcne : 𝓕 c ≠ 0 := by
    intro h
    apply hc
    have : 𝓕 c = 𝓕 0 := by rw [h, map_zero]
    exact dft.injective this
  refine zeros_le_of_dft_sparse (𝓕 c) hFcne ht1 ?_
  rw [supp_dft_dft_card]
  exact ht

end ProximityGap.Frontier.SparseCoeffZeros

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SparseCoeffZeros.supp_dft_dft_card
#print axioms ProximityGap.Frontier.SparseCoeffZeros.sparse_coeff_zeros_le
