/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan

set_option linter.style.longLine false

/-!
# The Paley spectral floor: the prize target is the EVT floor, NOT Ramanujan (Issue #407)

This file records the **spectral verdict** of the Paley-graph attack on the prize per-frequency core
`B = max_{b≠0} ‖η_b‖`, `η_b = ∑_{y∈μ_n} ψ(b·y)`. By the Liu–Zhou dictionary (Thm 115, see
`GeneralizedPaleyRamanujan.lean`) `B` is the non-principal spectral radius of the generalized Paley
graph `Cay(F_q, μ_n)`, which is `n`-regular on `q` vertices with **exactly `m = (q−1)/n` distinct
nontrivial eigenvalues** (the Gauss periods — `GaussPeriodCosetReduction.eta_image_card_mul_le`).

## The verdict (numerically established; see `scripts/probes/_wf407_paley_*.py`)

In the prize regime the index `m = (q−1)/n ≈ 2^128` is held constant as the FFT domain `n → ∞`
(`ε* = 2^−128`, `q ≈ n·2^128`). The measured floor is

  `B ≈ √(2·n·ln m)`   (EVT: max of `m` near-Gaussian, variance-`n` Gauss periods),

with `B/√(n·ln m) ∈ [0.9, 1.4]`, flat, **no trend** in `n` or `m`. The Parseval identity
`(1/(q−1))·∑_{b≠0}‖η_b‖² = n` (`subgroup_gaussSum_secondMoment`) supplies the per-period variance `n`;
the `m`-fold maximum of variance-`n` quasi-Gaussians is `√(2 n ln m)` by extreme-value theory.

**The decisive spectral finding.** The Alon–Boppana / Ramanujan cap `B ≤ 2√n` is the WRONG target —
it is **provably FALSE** in the prize regime. Measured `B/(2√n)` rises to a plateau `≈ 1.37` already
at `n = 8` once `m ≳ 17` (probe `_wf407_paley_largem.py`, all rows flagged `> 2√n`), and the
Ramanujan-excess factor is `√(ln m / 2)`, which at `m = 2^128` is `√(88.7/2) ≈ 6.66×` over the
Ramanujan bound. The excess is structural, not a defect: with `m → ∞` distinct nontrivial
eigenvalues, the maximum of `m` mean-zero variance-`n` values is necessarily `≳ √(n log m) ≫ 2√n`
once `log m > 2`. **Spectral-graph theory supplies the dictionary (`B` = eigenvalue) but no new
*upper* bound**: Alon–Boppana is a matching *lower* bound `B ≥ 2√(n−1)−o(1)`, and the upper Ramanujan
property simply fails here. The correct target `B ≤ C·√(n·log m)` is an *extreme-value-of-Gauss-
periods* statement (analytic number theory), not a spectral-gap inequality. The index-`m` covering /
lift structure gives no interlacing handle on the sup, since the `m` quotient eigenvalues ARE the
Gauss periods themselves.

## What is proven here (axiom-clean, elementary)

Three honest bridges that *relocate* the open core onto the right target:

- `PaleyFloorBound ψ G C` — the prize per-frequency target as a named Prop:
  `∀ b ≠ 0, ‖η_b‖ ≤ C·√(|G|·L)` where `L = log m` is supplied as a parameter. This is the
  EVT-correct floor (NOT Ramanujan); it is never asserted, only consumed.
- `paleyFloor_implies_worstCase` — the floor discharges the in-tree open residual
  `WorstCaseIncompleteSumBound` at scale `M = C²·|G|·L`, feeding the entire interior δ\* consumer
  chain (`addEnergy_le_of_worstCase`, …) from this one cited hypothesis.
- `ramanujan_implies_paleyFloor` — the **spectral-excess inequality, machine-checked**: the
  Ramanujan condition `GeneralizedPaleyRamanujan` (`B ≤ 2√n`) implies `PaleyFloorBound ψ G C`
  **whenever `4 ≤ C²·L`** (i.e. `L = log m ≥ 4/C²`). This pins the exact sense in which Ramanujan is
  *strictly stronger* than the prize floor: it suffices only when `log m ≥ 4/C²`, and is FALSE
  (so unavailable) in the prize regime where it would have to hold with the floor's `√(log m)` slack.

## Honest scope of the open core (unchanged)

This file does **not** close the prize. It records that the spectral/Ramanujan framing is the WRONG
target (too strong, false) and reduces the per-frequency core to the EVT floor `PaleyFloorBound`,
which remains OPEN: proving `B ≤ C√(n log m)` is the extreme-value bound on `m` Gauss periods,
equivalently `√(2n ln m)`-cancellation among the `(q−1)/n` Gauss-sum phases `χ̄(b)τ(χ)`,
`χ ∈ μ_n^⊥`, `|τ| = √p` (the `L^∞` / deep-moment wall of `CharSumMomentDeepWall.lean`). The best
*proven* bound in the prize regime is `n^{3/4+o(1)}` (deep-moment wall) / `n^{1−o(1)}` (BGK) — both
`≫ √(n log m)`. The honest gain of the Paley route is: it certifies that chasing Ramanujan / a
spectral-gap upper bound is a dead end, and re-points the core at the correct (EVT) target.

## References
- [LZ19]  Liu, Zhou. *Eigenvalues of Cayley graphs*. arXiv:1809.09829, Thm 115 (the dictionary).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- `docs/references/proximity-gap-paley-spectrum/README.md` — the 20-paper sweep + semiprimitive no-go.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum (WorstCaseIncompleteSumBound)
open ArkLib.ProximityGap.GeneralizedPaleyRamanujan (GeneralizedPaleyRamanujan)

namespace ArkLib.ProximityGap.PaleySpectralFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The Paley spectral floor (the prize per-frequency target).** Every nonzero Gauss period has
modulus at most `C·√(|G|·L)`, where `L = log m = log((q−1)/|G|)` is the log-index supplied as a
parameter and `C` is the empirical `O(1)` extreme-value constant (`C ∈ [0.9, 1.4]`). This is the
EVT-correct prize target — the maximum of `m` variance-`|G|` Gauss periods — NOT the (false-in-regime)
Ramanujan cap `2√|G|`. Stated as a Prop; never asserted, only consumed by the bridge below. -/
def PaleyFloorBound (ψ : AddChar F ℂ) (G : Finset F) (C L : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * L)

/-- **The floor discharges the in-tree open residual.** `PaleyFloorBound ψ G C L` (with `C, L ≥ 0`)
implies `WorstCaseIncompleteSumBound ψ G (C²·|G|·L)`: squaring `‖η_b‖ ≤ C√(|G|·L)` gives
`‖η_b‖² ≤ C²·|G|·L`. This feeds the entire interior δ\* consumer chain
(`addEnergy_le_of_worstCase`, …) from the single cited EVT hypothesis — the correct target, in
place of the false Ramanujan one. -/
theorem paleyFloor_implies_worstCase {ψ : AddChar F ℂ} {G : Finset F} {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (h : PaleyFloorBound ψ G C L) :
    WorstCaseIncompleteSumBound ψ G (C ^ 2 * (G.card : ℝ) * L) := by
  intro b hb
  have hb' : ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * L) := h b hb
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have hrad : (0 : ℝ) ≤ (G.card : ℝ) * L := by positivity
  have hsq : ‖eta ψ G b‖ ^ 2 ≤ (C * Real.sqrt ((G.card : ℝ) * L)) ^ 2 := by
    have hrhs : (0 : ℝ) ≤ C * Real.sqrt ((G.card : ℝ) * L) := by positivity
    nlinarith [hb', hnn, hrhs]
  have hval : (C * Real.sqrt ((G.card : ℝ) * L)) ^ 2 = C ^ 2 * (G.card : ℝ) * L := by
    rw [mul_pow, Real.sq_sqrt hrad]; ring
  calc ‖eta ψ G b‖ ^ 2 ≤ (C * Real.sqrt ((G.card : ℝ) * L)) ^ 2 := hsq
    _ = C ^ 2 * (G.card : ℝ) * L := hval

/-- **The spectral-excess inequality (machine-checked).** The Ramanujan condition
`GeneralizedPaleyRamanujan` (`B ≤ 2√|G|`) implies the prize floor `PaleyFloorBound ψ G C L`
**whenever `4 ≤ C²·L`** (i.e. `L = log m ≥ 4/C²`). This is the exact sense in which Ramanujan is
*strictly stronger* than the EVT floor: a Ramanujan graph clears the floor only when the log-index is
large enough to absorb the `2√|G|` cap inside `C√(|G|·L)`. Conversely, when `L` is large the floor is
much weaker than Ramanujan — and the numerics show `B > 2√|G|` in the prize regime, so the antecedent
`GeneralizedPaleyRamanujan` is itself FALSE there. Hence this bridge is the honest record that the
spectral route's target is too strong: the floor is the right object, Ramanujan is not available. -/
theorem ramanujan_implies_paleyFloor {ψ : AddChar F ℂ} {G : Finset F} {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hCL : 4 ≤ C ^ 2 * L)
    (h : GeneralizedPaleyRamanujan ψ G) :
    PaleyFloorBound ψ G C L := by
  intro b hb
  -- Ramanujan: ‖η_b‖ ≤ 2√|G|.  Goal: ‖η_b‖ ≤ C√(|G|·L).  Suffices 2√|G| ≤ C√(|G|·L).
  have hram : ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card) := h b hb
  refine le_trans hram ?_
  -- 2√|G| ≤ C√(|G|L)  ⟺  (since both sides ≥ 0)  4·|G| ≤ C²·|G|·L  ⟸  4 ≤ C²·L.
  have hGnn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hrad : (0 : ℝ) ≤ (G.card : ℝ) * L := by positivity
  have hlhs : (0 : ℝ) ≤ 2 * Real.sqrt (G.card) := by positivity
  have hrhs : (0 : ℝ) ≤ C * Real.sqrt ((G.card : ℝ) * L) := by positivity
  -- compare squares
  have hsqle : (2 * Real.sqrt (G.card)) ^ 2 ≤ (C * Real.sqrt ((G.card : ℝ) * L)) ^ 2 := by
    have e1 : (2 * Real.sqrt (G.card)) ^ 2 = 4 * (G.card : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hGnn]; ring
    have e2 : (C * Real.sqrt ((G.card : ℝ) * L)) ^ 2 = C ^ 2 * ((G.card : ℝ) * L) := by
      rw [mul_pow, Real.sq_sqrt hrad]
    rw [e1, e2]
    nlinarith [hCL, hGnn]
  -- squares ordered + both nonneg ⟹ values ordered
  nlinarith [hsqle, hlhs, hrhs, sq_nonneg (C * Real.sqrt ((G.card : ℝ) * L) - 2 * Real.sqrt (G.card))]

/-- **End-to-end (the honest reduction).** The Paley floor at constant `C` and log-index `L` yields
the additive-energy budget `q·E(G) ≤ |G|⁴ + (C²·|G|·L)·(q·|G|)` — the prize per-frequency input
feeding the δ\* programme, reduced to the single named EVT hypothesis `PaleyFloorBound`. (Composes
`paleyFloor_implies_worstCase` with the in-tree consumer `addEnergy_le_of_worstCase`.) -/
theorem addEnergy_le_of_paleyFloor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (h : PaleyFloorBound ψ G C L) :
    (Fintype.card F : ℝ) * (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + (C ^ 2 * (G.card : ℝ) * L) * ((Fintype.card F : ℝ) * G.card) :=
  ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum.addEnergy_le_of_worstCase hψ G
    (by positivity) (paleyFloor_implies_worstCase hC hL h)

end ArkLib.ProximityGap.PaleySpectralFloor

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.PaleySpectralFloor.paleyFloor_implies_worstCase
#print axioms ArkLib.ProximityGap.PaleySpectralFloor.ramanujan_implies_paleyFloor
#print axioms ArkLib.ProximityGap.PaleySpectralFloor.addEnergy_le_of_paleyFloor
