/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTLinftyFloor

/-!
# The sparse-DFT sharpened peak floor: `t`-Fourier-sparse ⟹ `max_k‖𝓕Φ k‖ ≥ √(N/t)·‖Φ‖₂` (#407)

`_ZModDFTLinftyFloor.exists_dft_peak_ge_l2norm` gives the plain `L^∞`–`L^2` floor
`max_k‖𝓕Φ k‖ ≥ ‖Φ‖₂` (one pigeonhole step off Parseval, dividing the `ℓ²`-mass among ALL `N`
frequencies).  When `𝓕Φ` is **`t`-Fourier-sparse** (`|supp 𝓕Φ| ≤ t`) the same `ℓ²`-mass is carried
by only `t` frequencies, so the pigeonhole sharpens by `√(N/t)`:

> `exists_dft_peak_ge_sqrt_sparse` :  `|supp 𝓕Φ| ≤ t`, `Φ ≠ 0`  ⟹
>   `∃ k₀, √((N/t)·∑_j‖Φ j‖²) ≤ ‖𝓕Φ k₀‖`.

Proof: `(max ‖𝓕Φ‖)²·t ≥ ∑_{k∈supp 𝓕Φ}‖𝓕Φ k‖² = ∑_k‖𝓕Φ k‖² = N·‖Φ‖₂²` (Parseval; off-support
terms are `0`), so `(max ‖𝓕Φ‖)² ≥ (N/t)·‖Φ‖₂²`.  At the trivial `t = N` this recovers the plain
floor `≥ ‖Φ‖₂`; for genuinely sparse spectra (`t = k+2 ≪ N`, the far-line agreement regime) the peak
is forced `√(N/t)`-times larger.

Scope: this is the FLOOR (easy/lower-bound) direction, sharpened by sparsity.  It quantifies how a
concentrated spectrum forces a tall peak — the dual face of "few zeros" (`_FourierSparseZeros`).  It
asserts nothing about the open CORE upper bound; no cancellation, completion, anti-concentration,
moment, or capacity claim.  Axiom-clean.  Issue #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.ZModDFTLinftyFloor

namespace ProximityGap.Frontier.ZModDFTSparsePeakFloor

variable {N : ℕ} [NeZero N]

/-- **Sparse-DFT sharpened peak floor (squared form).**  If `|supp 𝓕Φ| ≤ t` and `Φ ≠ 0` then the
squared peak `(max_k‖𝓕Φ k‖)²` is at least `(N/t)·∑_j‖Φ j‖²`.

The `ℓ²`-mass `∑_k‖𝓕Φ k‖² = N·‖Φ‖₂²` (Parseval) is carried by the `≤ t` support frequencies, each
`≤` the squared peak; dividing by `t` gives the bound. -/
theorem exists_dft_peak_sq_ge_sparse (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) {t : ℕ}
    (ht : (supp (𝓕 Φ)).card ≤ t) :
    ∃ k₀ : ZMod N,
      ((N : ℝ) / t) * (∑ j : ZMod N, ‖Φ j‖ ^ 2) ≤ ‖(𝓕 Φ) k₀‖ ^ 2 := by
  -- t > 0 since the support is nonempty (Φ ≠ 0 ⟹ 𝓕Φ ≠ 0 ⟹ supp nonempty)
  have hFne : 𝓕 Φ ≠ 0 := by
    intro h
    apply hΦ
    have hz : 𝓕 Φ = 𝓕 0 := by rw [h, map_zero]
    exact dft.injective hz
  have hsupp_pos : 0 < (supp (𝓕 Φ)).card := by
    rw [Finset.card_pos]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hFne
    exact ⟨k, by simp only [supp, mem_filter, mem_univ, true_and]; simpa using hk⟩
  have htpos : 0 < t := lt_of_lt_of_le hsupp_pos ht
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  -- the argmax over ZMod N
  obtain ⟨k₀, _, hk₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod N)) (fun k => ‖(𝓕 Φ) k‖ ^ 2)
      ⟨0, Finset.mem_univ 0⟩
  refine ⟨k₀, ?_⟩
  -- Parseval mass restricted to the support
  have hpars : (∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2) = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 :=
    ZModDFTParseval.dft_parseval Φ
  have hmass_supp : (∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖ ^ 2) = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
    rw [← hpars]
    refine Finset.sum_subset (Finset.subset_univ (supp (𝓕 Φ))) (fun k _ hk => ?_)
    simp only [supp, mem_filter, mem_univ, true_and, not_not] at hk
    rw [hk, norm_zero]; ring
  -- bound the support mass by |supp|·peak² ≤ t·peak²
  have hsum_le : (∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖ ^ 2) ≤ (t : ℝ) * ‖(𝓕 Φ) k₀‖ ^ 2 := by
    calc (∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖ ^ 2)
        ≤ ∑ _k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k₀‖ ^ 2 :=
          Finset.sum_le_sum (fun k _ => hk₀ k (Finset.mem_univ k))
      _ = ((supp (𝓕 Φ)).card : ℝ) * ‖(𝓕 Φ) k₀‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (t : ℝ) * ‖(𝓕 Φ) k₀‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast ht
  rw [hmass_supp] at hsum_le
  -- (N/t)·mass ≤ peak²  ⟺  N·mass ≤ t·peak²
  rw [div_mul_eq_mul_div, div_le_iff₀ htR]
  linarith [hsum_le]

/-- **Sparse-DFT sharpened peak floor (norm form).**  If `|supp 𝓕Φ| ≤ t` and `Φ ≠ 0`, there is a
frequency `k₀` with `‖𝓕Φ k₀‖ ≥ √((N/t)·∑_j‖Φ j‖²) = √(N/t)·‖Φ‖₂`.  At the trivial `t = N` this
recovers the plain `_ZModDFTLinftyFloor` floor `≥ ‖Φ‖₂`; a `t`-sparse spectrum forces a
`√(N/t)`-times taller peak. -/
theorem exists_dft_peak_ge_sqrt_sparse (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) {t : ℕ}
    (ht : (supp (𝓕 Φ)).card ≤ t) :
    ∃ k₀ : ZMod N,
      Real.sqrt (((N : ℝ) / t) * (∑ j : ZMod N, ‖Φ j‖ ^ 2)) ≤ ‖(𝓕 Φ) k₀‖ := by
  obtain ⟨k₀, hk₀⟩ := exists_dft_peak_sq_ge_sparse Φ hΦ ht
  refine ⟨k₀, ?_⟩
  have hnn : 0 ≤ ‖(𝓕 Φ) k₀‖ := norm_nonneg _
  rw [show ‖(𝓕 Φ) k₀‖ = Real.sqrt (‖(𝓕 Φ) k₀‖ ^ 2) from (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hk₀

end ProximityGap.Frontier.ZModDFTSparsePeakFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ZModDFTSparsePeakFloor.exists_dft_peak_sq_ge_sparse
#print axioms ProximityGap.Frontier.ZModDFTSparsePeakFloor.exists_dft_peak_ge_sqrt_sparse
