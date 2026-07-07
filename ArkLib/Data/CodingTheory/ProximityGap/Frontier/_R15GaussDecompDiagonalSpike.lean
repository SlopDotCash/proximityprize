/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# LANE B1 (#466 round 15): Gauss-sum decomposition of `I_H` — the diagonal spike is STRUCTURAL

Round 13 measured `worst_{s₀}‖I_H(s₀)‖ ≈ |H|`-scale (ratios `6.1 → 13.7 ∝ √|H|` over
`√|H|·M`) and concluded worst-case incidence is not a function of `M`.  Round 15 (this lane)
identifies the *exact structural source* of that measured peak via the multiplicative-character
(Gauss-sum) decomposition of `I_H`.  Numerically verified to `~1e-10` (float-limited at larger
`p`) at `n = 8/16/32`, window primes, `deg ∈ {2,4,8}`
(`scratchpad/b1_gauss_decomp.py`, `b1_refine.py`):

  `I_H(s₀) = (p·1_{s₀∈μ_n} − n)/deg + (1/deg)·∑_{χ≠χ₀, χ^deg=χ₀} g(χ)·T_χ(s₀)`,
  `T_χ(s₀) = ∑_{x∈μ_n, x≠s₀} χ̄(s₀−x)`.

The `χ₀` term produces a **diagonal spike** `≈ (p−n)/deg ≈ |H|` at every `s₀ ∈ μ_n` — and the
round-13 measured worst offsets are exactly this spike (`spike/(√|H|·M) = √|H|/M` = 6.1, 13.7 at
those scales).  **Off the diagonal** (`s₀ ∉ μ_n`) the measured ratio `‖I_H‖/(√|H|·M)` is `Θ(1)`
(0.61–1.61 across all probed scales, NO growth in `|H|`): Problem B is empirically TRUE off the
diagonal and structurally FALSE on it.

This file lands the `χ₀`-layer of the decomposition axiom-clean (no multiplicative characters
needed for this layer — it is a pure resummation):

* `incidenceSum_eq_period_resummation` — `I_H(s₀) = ∑_{x∈G} η^H(s₀ − x)` where
  `η^H(c) = ∑_{b∈H} ψ(c·b)` is the Gauss period of the *complementary* (thick) subgroup `H`.
  (Swap of summation + `conj ψ(a) = ψ(−a)`; exact, any `G`, `H`.)
* `eta_zero_eq_card` — `η^H(0) = |H|`: the diagonal term.
* `incidenceSum_diagonal_spike_lower` — for `s₀ ∈ G`:
  `‖I_H(s₀)‖ ≥ |H| − (|G|−1)·M_H` where `M_H = max_{c≠0}‖η^H(c)‖`.  Since `M_H = O(√p)` (Weil
  scale for the THICK subgroup, in-tree `SubgroupGaussSumWorstCase` machinery) while `|H| ≈ p/deg`,
  the spike dominates: at the prize (`|H| ≈ n⁴/deg`, `(n−1)·M_H ≈ n·n² = n³`, `√|H|·M ≈ n^{2.5}`)
  the diagonal offset provably exceeds the Problem-B budget.
* `problemB_fails_at_diagonal_offset` — the packaged refutation-shape: whenever
  `√|H|·M < |H| − (|G|−1)·M_H`, the worst-case Problem-B inequality `∀s₀, ‖I_H(s₀)‖ ≤ √|H|·M`
  is FALSE (witness: any `s₀ ∈ G`).

CONSEQUENCE (honest, no closure): **Problem B as stated over ALL offsets is false — it must be
stated for `s₀ ∉ μ_n` (or with the `χ₀`/diagonal term subtracted).**  The corrected off-diagonal
statement is the real BCHKS-1.12 content, empirically `Θ(1)`-true at all probed scales.  The
per-χ reduction of the corrected statement is `|T_χ(s₀)| ≲ M/√deg`-on-average-in-χ — a twisted
thin-subgroup character sum, same BGK/BCHKS wall (see findings report).  CORE OPEN.

Issue #466, lane B1 (round 15).
-/

set_option autoImplicit false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The signed incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)` — definitionally identical to
`R13HyperplaneSecondMoment.incidenceSum` (restated here to keep this lane file on warm oleans;
`_R13HyperplaneSecondMoment.lean` has no olean in the warm set). -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G : Finset F) (H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- **The resummation identity (the `χ₀`-layer of the Gauss-sum decomposition).**
`I_H(s₀) = ∑_{x∈G} η^H(s₀ − x)`: the signed incidence sum over the frequency set `H` is the sum,
over the thin evaluation set `G`, of the Gauss periods of `H` at the shifted points `s₀ − x`.
Pure summation swap + `conj ψ(a) = ψ(−a)`; exact for arbitrary finsets `G`, `H`. -/
theorem incidenceSum_eq_period_resummation (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    incidenceSum ψ G H s₀ = ∑ x ∈ G, eta ψ H (s₀ - x) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  unfold incidenceSum
  calc ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)
      = ∑ b ∈ H, ∑ x ∈ G, ψ (b * (s₀ - x)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        unfold eta
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hconj (b * x), ← AddChar.map_add_eq_mul]
        congr 1; ring
    _ = ∑ x ∈ G, ∑ b ∈ H, ψ ((s₀ - x) * b) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun b _ => by ring_nf))
    _ = ∑ x ∈ G, eta ψ H (s₀ - x) := rfl

/-- The Gauss period of any finset at frequency `0` is its cardinality: `η^H(0) = |H|`. -/
theorem eta_zero_eq_card (ψ : AddChar F ℂ) (H : Finset F) :
    eta ψ H 0 = (H.card : ℂ) := by
  unfold eta
  simp

/-- **Exact diagonal split.**  At a diagonal offset `s₀ ∈ G`, the signed incidence sum is the
cardinality spike `|H|` plus the off-diagonal shifted-period tail over `G \ {s₀}`. -/
theorem incidenceSum_eq_card_add_offdiag_of_mem (ψ : AddChar F ℂ) (G H : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) :
    incidenceSum ψ G H s₀ =
      (H.card : ℂ) + ∑ x ∈ G.erase s₀, eta ψ H (s₀ - x) := by
  classical
  rw [incidenceSum_eq_period_resummation ψ G H s₀]
  rw [← Finset.add_sum_erase G (fun x => eta ψ H (s₀ - x)) hs₀]
  rw [sub_self, eta_zero_eq_card]

/-- **After subtracting the diagonal spike, only the off-diagonal tail remains.**  If the nonzero
periods of the thick frequency set `H` are bounded by `M_H`, then at every diagonal offset
`s₀ ∈ G` the spike-subtracted incidence is bounded by `( |G| - 1 ) M_H`.  This is the corrected
object that a diagonal-subtracted version of Problem B should attack. -/
theorem diagonal_subtracted_incidence_norm_le (ψ : AddChar F ℂ) (G H : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) {MH : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    ‖incidenceSum ψ G H s₀ - (H.card : ℂ)‖ ≤ ((G.card : ℝ) - 1) * MH := by
  classical
  rw [incidenceSum_eq_card_add_offdiag_of_mem ψ G H hs₀]
  have htail : ‖∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖ ≤ ((G.card : ℝ) - 1) * MH := by
    calc ‖∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖
        ≤ ∑ x ∈ G.erase s₀, ‖eta ψ H (s₀ - x)‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ G.erase s₀, MH := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          have hne : s₀ - x ≠ 0 :=
            sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hx))
          exact hMH _ hne
      _ = ((G.erase s₀).card : ℝ) * MH := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((G.card : ℝ) - 1) * MH := by
          rw [Finset.card_erase_of_mem hs₀]
          have hpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨s₀, hs₀⟩
          push_cast [Nat.cast_sub hpos]
          ring
  simpa [add_sub_cancel_left] using htail

/-- **The diagonal spike (the measured round-13 worst case, now a theorem).**
For any offset `s₀ ∈ G`, if every *nonzero*-frequency Gauss period of `H` is bounded by `M_H`,
then `‖I_H(s₀)‖ ≥ |H| − (|G|−1)·M_H`.  The `η^H(0) = |H|` diagonal term survives with no
cancellation; only the `|G|−1` off-diagonal shifted periods can fight it.  With `M_H = O(√p)`
(thick-subgroup Weil scale) and `|H| ≈ p/deg ≫ n·√p`, the spike is of order `|H|` — provably
above the `√|H|·M` Problem-B budget. -/
theorem incidenceSum_diagonal_spike_lower (ψ : AddChar F ℂ) (G H : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) {MH : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    (H.card : ℝ) - ((G.card : ℝ) - 1) * MH ≤ ‖incidenceSum ψ G H s₀‖ := by
  classical
  rw [incidenceSum_eq_period_resummation ψ G H s₀]
  -- split off x = s₀
  rw [← Finset.add_sum_erase G _ hs₀]
  have hzero : eta ψ H (s₀ - s₀) = (H.card : ℂ) := by
    rw [sub_self, eta_zero_eq_card]
  rw [hzero]
  have htail : ‖∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖ ≤ ((G.card : ℝ) - 1) * MH := by
    calc ‖∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖
        ≤ ∑ x ∈ G.erase s₀, ‖eta ψ H (s₀ - x)‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ G.erase s₀, MH := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          have hne : s₀ - x ≠ 0 :=
            sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hx))
          exact hMH _ hne
      _ = ((G.erase s₀).card : ℝ) * MH := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((G.card : ℝ) - 1) * MH := by
          rw [Finset.card_erase_of_mem hs₀]
          have hpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨s₀, hs₀⟩
          push_cast [Nat.cast_sub hpos]
          ring
  have hkey : ‖((H.card : ℕ) : ℂ)‖ - ‖∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖
      ≤ ‖((H.card : ℕ) : ℂ) + ∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)‖ := by
    have h := norm_sub_norm_le ((H.card : ℕ) : ℂ)
      (-(∑ x ∈ G.erase s₀, eta ψ H (s₀ - x)))
    rw [sub_neg_eq_add, norm_neg] at h
    exact h
  have hnormcard : ‖((H.card : ℕ) : ℂ)‖ = (H.card : ℝ) := by simp
  rw [hnormcard] at hkey
  linarith

/-- **Problem B as stated (worst case over ALL offsets) is FALSE whenever the spike clears the
budget.**  If `√|H|·M < |H| − (|G|−1)·M_H`, then the Problem-B inequality
`∀ s₀, ‖I_H(s₀)‖ ≤ √|H|·M` fails — witnessed at any diagonal offset `s₀ ∈ G`.  (At the prize
scale: `|H| ≈ n⁴/deg` vs `(n−1)·M_H + √|H|·M ≈ n³ + n^{2.5}`, so the hypothesis holds with room.)
Problem B must therefore be stated off-diagonal (`s₀ ∉ μ_n`) or with the `χ₀` term subtracted. -/
theorem problemB_fails_at_diagonal_offset (ψ : AddChar F ℂ) (G H : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) {MH M : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH)
    (hgap : Real.sqrt (H.card : ℝ) * M < (H.card : ℝ) - ((G.card : ℝ) - 1) * MH) :
    ¬ (∀ s : F, ‖incidenceSum ψ G H s‖ ≤ Real.sqrt (H.card : ℝ) * M) := by
  intro hB
  have h1 := incidenceSum_diagonal_spike_lower ψ G H hs₀ hMH
  have h2 := hB s₀
  linarith

end ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.incidenceSum_eq_period_resummation
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.eta_zero_eq_card
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.incidenceSum_eq_card_add_offdiag_of_mem
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.diagonal_subtracted_incidence_norm_le
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.incidenceSum_diagonal_spike_lower
#print axioms
  ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.problemB_fails_at_diagonal_offset
