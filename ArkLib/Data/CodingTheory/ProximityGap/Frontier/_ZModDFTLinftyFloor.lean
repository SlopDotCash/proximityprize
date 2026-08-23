/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTParseval
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModSubgroupSaturation

/-!
# The `L^∞`–`L^2` Plancherel floor on the `ZMod N` DFT (#407 / #444 Shaw-chain rung)

The #407 DFT-uncertainty substrate already lands Parseval (`_ZModDFTParseval.dft_parseval`,
`∑_k ‖𝓕Φ k‖² = N·∑_j ‖Φ j‖²`) and the Donoho–Stark *support* uncertainty
(`_ZModDonohoStark.donoho_stark`, `|supp Φ|·|supp 𝓕Φ| ≥ N`).  What was *missing* on this
substrate is the elementary but load-bearing **`L^∞`–`L^2` floor**: a single pigeonhole step off
Parseval that turns the `ℓ²` mass of `𝓕Φ` into a pointwise lower bound on its peak.

> `(max_k ‖𝓕Φ k‖)² ≥ ∑_j ‖Φ j‖²`,  i.e.  `max_k ‖𝓕Φ k‖ ≥ ‖Φ‖₂`.

Proof: `N` terms each `≤ (max ‖𝓕Φ‖)²` sum to `∑_k ‖𝓕Φ k‖² = N·‖Φ‖₂²` (Parseval); divide by `N`.

This is the DFT-object form of the **Plancherel / RMS floor** `M(μ_n) ≥ √n` — the floor rung of
Shaw's reduction chain (#444 §5.0, the lower endpoint of the `√n`-wide Shaw bracket in
`ShawValueCapstone`).  Specialized to the order-`d` subgroup indicator `Φ = 1_{μ_d}` (whose
`ℓ²`-mass is `d` by `_ZModSubgroupSaturation`), it gives the clean thin-subgroup statement
`max_k ‖𝓕 1_{μ_d} k‖ ≥ √d` — the substrate-level Plancherel floor on the thin `2`-power subgroups
`μ_{2^μ}` that localize the prize.

NOTE on scope: this is a FLOOR (lower bound), i.e. the EASY direction.  It does NOT touch CORE
(the upper bound `M(μ_n) ≤ C√(n·log(p/n))` over the *off-DC* frequencies, the open prize wall).
For the indicator the floor is far from tight (the peak is the DC value `d ≫ √d`); the `√d` floor
is the honest `L^∞`–`L^2` content, the same content the Shaw bracket uses as its lower endpoint.
No cancellation, completion, anti-concentration, moment, or capacity claim.  Axiom-clean.
Issue #407/#444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.ZModDFTLinftyFloor

open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- **`L^∞`–`L^2` Plancherel floor (squared form).**  For any `Φ : ZMod N → ℂ` and any frequency
`k₀`, the squared peak `(max over k of ‖𝓕Φ k‖)²` is at least the `ℓ²`-mass `∑_j ‖Φ j‖²`.

We phrase the peak via an explicit maximizing `k₀` (which exists since `ZMod N` is a nonempty
fintype) so the statement is `‖𝓕Φ k₀‖² ≥ ∑_j ‖Φ j‖²` for the argmax `k₀`.  This is one pigeonhole
step off `dft_parseval`. -/
theorem exists_dft_peak_sq_ge_l2 (Φ : ZMod N → ℂ) :
    ∃ k₀ : ZMod N, (∑ j : ZMod N, ‖Φ j‖ ^ 2) ≤ ‖(𝓕 Φ) k₀‖ ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the argmax over the nonempty fintype `ZMod N`
  obtain ⟨k₀, _, hk₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod N)) (fun k => ‖(𝓕 Φ) k‖ ^ 2)
      ⟨0, Finset.mem_univ 0⟩
  refine ⟨k₀, ?_⟩
  -- bound the Parseval sum by `N · (peak)²`
  have hsum_le : (∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2) ≤ (N : ℝ) * ‖(𝓕 Φ) k₀‖ ^ 2 := by
    calc (∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2)
        ≤ ∑ _k : ZMod N, ‖(𝓕 Φ) k₀‖ ^ 2 :=
          Finset.sum_le_sum (fun k _ => hk₀ k (Finset.mem_univ k))
      _ = (N : ℝ) * ‖(𝓕 Φ) k₀‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hpars : (∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2) = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 :=
    ZModDFTParseval.dft_parseval Φ
  rw [hpars] at hsum_le
  -- cancel the positive `N`
  have := le_of_mul_le_mul_left hsum_le hNpos
  exact this

/-- **`L^∞`–`L^2` Plancherel floor (norm form).**  There is a frequency `k₀` whose DFT magnitude is
at least the `ℓ²`-norm of `Φ`:  `‖𝓕Φ k₀‖ ≥ √(∑_j ‖Φ j‖²)`.  Hence the peak of `‖𝓕Φ‖` dominates the
`L^2`-norm of `Φ`. -/
theorem exists_dft_peak_ge_l2norm (Φ : ZMod N → ℂ) :
    ∃ k₀ : ZMod N, Real.sqrt (∑ j : ZMod N, ‖Φ j‖ ^ 2) ≤ ‖(𝓕 Φ) k₀‖ := by
  obtain ⟨k₀, hk₀⟩ := exists_dft_peak_sq_ge_l2 Φ
  refine ⟨k₀, ?_⟩
  have hnn : 0 ≤ ‖(𝓕 Φ) k₀‖ := norm_nonneg _
  rw [show ‖(𝓕 Φ) k₀‖ = Real.sqrt (‖(𝓕 Φ) k₀‖ ^ 2) from (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hk₀

/-- **Substrate Plancherel floor at the thin subgroup `μ_d`.**  For `d ∣ N`, the order-`d` subgroup
indicator has peak DFT magnitude at least `√d`:
`∃ k₀, ‖𝓕 1_{μ_d} k₀‖ ≥ √d`.

The `ℓ²`-mass of the order-`d` indicator is exactly `d` (its support has `d` points, each of value
`1`, by `_ZModSubgroupSaturation.supp_subgroupIndicator_card`), so the general norm floor
specializes to `√d`.  This is the DFT-substrate realization of the Plancherel/RMS floor
`M(μ_d) ≥ √d` on the thin `2`-power subgroups `μ_{2^μ}` that localize the prize (the lower
endpoint of the Shaw bracket).  It is a FLOOR only; it asserts nothing about the off-DC peak
that the open CORE upper bound controls. -/
theorem subgroupIndicator_dft_peak_ge_sqrt {d : ℕ} (hd : d ∣ N) :
    ∃ k₀ : ZMod N,
      Real.sqrt (d : ℝ) ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := by
  -- the ℓ²-mass of the indicator equals its support cardinality = d
  have hmass : (∑ j : ZMod N, ‖(subgroupIndicator (N := N) d) j‖ ^ 2) = (d : ℝ) := by
    have hsupp : (∑ j : ZMod N, ‖(subgroupIndicator (N := N) d) j‖ ^ 2)
        = ∑ j ∈ supp (subgroupIndicator (N := N) d), ‖(subgroupIndicator (N := N) d) j‖ ^ 2 :=
      sum_sq_eq_supp _
    rw [hsupp]
    -- on the support the indicator is `1`, so each term is `1`
    have hone : ∀ j ∈ supp (subgroupIndicator (N := N) d),
        ‖(subgroupIndicator (N := N) d) j‖ ^ 2 = 1 := by
      intro j hj
      simp only [supp, mem_filter, mem_univ, true_and] at hj
      -- `subgroupIndicator` is `0/1`-valued; nonzero ⟹ value `1`
      have hval : (subgroupIndicator (N := N) d) j = 1 := by
        unfold subgroupIndicator at hj ⊢
        by_cases hk : (d : ZMod N) * j = 0
        · simp [hk]
        · simp [hk] at hj
      rw [hval, norm_one, one_pow]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      supp_subgroupIndicator_card hd]
  obtain ⟨k₀, hk₀⟩ := exists_dft_peak_ge_l2norm (subgroupIndicator (N := N) d)
  refine ⟨k₀, ?_⟩
  rwa [hmass] at hk₀

end ProximityGap.Frontier.ZModDFTLinftyFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ZModDFTLinftyFloor.exists_dft_peak_sq_ge_l2
#print axioms ProximityGap.Frontier.ZModDFTLinftyFloor.exists_dft_peak_ge_l2norm
#print axioms ProximityGap.Frontier.ZModDFTLinftyFloor.subgroupIndicator_dft_peak_ge_sqrt
