/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Wiring the sub-Gaussian tail route to the real MCA prize object (#444 / Challenge A & B)

`_AvW5`/`_AvW6` proved, abstractly, that a uniform sub-Gaussian tail on a finite family `a : B → ℝ`
forces `max a ≤ √(n·(2 ln q + 1)/c)` (the Paley shape) via a tight union bound. This file
**instantiates that at the actual prize family** `a b = ‖eta ψ G b‖` and lands the conclusion as the
project's named open core `WorstCaseIncompleteSumBound ψ G M` — the *face #3* input that drives both
grand challenges:

* `WorstCaseIncompleteSumBound ψ G M` feeds `addEnergy_le_of_worstCase` → the additive-energy budget
  → the far-line incidence bound `epsMCA_ge_far_incidence` → the **MCA δ\*** (Challenge A), and
* the same `‖eta_b‖²` bound is the explicit-RS list-size driver for the **List Decoding** δ\*
  (Challenge B) through the Johnson/curve consumers.

So this brick connects the session's new tail machinery, end-to-end, to the genuine prize quantity
`ε_mca` (not just the abstract Paley face). The single remaining open input is the named tail
hypothesis `EtaSubGaussianTail` — empirically true (`c ≈ 0.6`, n-universal; see
`docs/kb/deltastar-444-SADDLE-K-DIAGNOSTIC-2026-06-19.md`), and *equal to* the open Paley/BGK
conjecture in distributional form. NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW7

open Finset
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero frequencies as a `Finset F`. -/
noncomputable def nzFreq (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.filter (fun b => b ≠ 0)

@[simp] theorem mem_nzFreq {b : F} : b ∈ nzFreq F ↔ b ≠ 0 := by
  simp [nzFreq]

/-- **The named open hypothesis at the real family.** The uniform sub-Gaussian tail of the
incomplete subgroup Gauss sums `‖eta ψ G b‖` at threshold `T`, sub-Gaussian constant `c`, scale
`n` (= `|G|`). Empirically true with `c ≈ 0.6`, n-independent; proving it = the open Paley/BGK
conjecture. -/
noncomputable def EtaSubGaussianTail (ψ : AddChar F ℂ) (G : Finset F) (n c T : ℝ) : Prop :=
  (((nzFreq F).filter (fun b => T < ‖eta ψ G b‖)).card : ℝ)
    ≤ ((nzFreq F).card : ℝ) * Real.exp (-((c / n) * T ^ 2))

/-- **Rate < 1 at the Paley threshold (proven).** Mirrors `_AvW6.rate_lt_one` for the `nzFreq`
family: with `(c/n)·T² = 2 ln(q−1) + 1`, the union-bound rate is `< 1`. -/
theorem rate_lt_one (ψ : AddChar F ℂ) (G : Finset F) (n c T : ℝ)
    (hN : 1 ≤ ((nzFreq F).card : ℝ)) (hcn : 0 < c / n)
    (hT : (c / n) * T ^ 2 = ((nzFreq F).card : ℝ).log + 1 + ((nzFreq F).card : ℝ).log) :
    ((nzFreq F).card : ℝ) * Real.exp (-((c / n) * T ^ 2)) < 1 := by
  set N : ℝ := ((nzFreq F).card : ℝ) with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  rw [hT]
  have hsplit : -(N.log + 1 + N.log) = -(2 * N.log) + (-1) := by ring
  rw [hsplit, Real.exp_add]
  have h2 : Real.exp (-(2 * N.log)) = (N ^ 2)⁻¹ := by
    rw [show (2:ℝ) * N.log = ((2:ℕ):ℝ) * N.log by norm_num,
        ← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h2]
  have hexp1 : Real.exp (-1) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  have key : N * ((N ^ 2)⁻¹ * Real.exp (-1)) ≤ Real.exp (-1) := by
    rw [← mul_assoc]
    have hle : N * (N ^ 2)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by positivity)]; nlinarith [hN]
    nlinarith [Real.exp_pos (-1 : ℝ), hle, Real.exp_nonneg (-1:ℝ)]
  calc N * ((N ^ 2)⁻¹ * Real.exp (-1)) ≤ Real.exp (-1) := key
    _ < 1 := hexp1

/-- **The bridge (PROVEN modulo the one named tail hypothesis).** The eta sub-Gaussian tail at the
Paley threshold `T` yields the project's open-core input `WorstCaseIncompleteSumBound ψ G (T²)` —
i.e. `∀ b ≠ 0, ‖eta_b‖² ≤ T²`, with `T² = n·(2 ln(q−1) + 1)/c` the Paley shape `Θ(n log q)`. This is
the entry point of the additive-energy → far-line incidence → MCA δ\* chain (Challenge A) and the
explicit-RS list-size chain (Challenge B). -/
theorem worstCaseIncompleteSumBound_of_etaTail (ψ : AddChar F ℂ) (G : Finset F) (n c T : ℝ)
    (hN : 1 ≤ ((nzFreq F).card : ℝ)) (hcn : 0 < c / n) (hTpos : 0 ≤ T)
    (hT : (c / n) * T ^ 2 = ((nzFreq F).card : ℝ).log + 1 + ((nzFreq F).card : ℝ).log)
    (htail : EtaSubGaussianTail ψ G n c T) :
    WorstCaseIncompleteSumBound ψ G (T ^ 2) := by
  -- exceedance count ≤ rate < 1 ⟹ count = 0 ⟹ every ‖eta_b‖ ≤ T ⟹ ‖eta_b‖² ≤ T²
  have hrate := rate_lt_one ψ G n c T hN hcn hT
  have hlt1 : (((nzFreq F).filter (fun b => T < ‖eta ψ G b‖)).card : ℝ) < 1 :=
    lt_of_le_of_lt htail hrate
  have hzero : ((nzFreq F).filter (fun b => T < ‖eta ψ G b‖)).card = 0 := by
    have : ((nzFreq F).filter (fun b => T < ‖eta ψ G b‖)).card < 1 := by exact_mod_cast hlt1
    omega
  intro b hb
  -- b ≠ 0, so b ∈ nzFreq; the exceedance set is empty, so ¬ (T < ‖eta_b‖), i.e. ‖eta_b‖ ≤ T
  have hbmem : b ∈ nzFreq F := mem_nzFreq.mpr hb
  have hle : ‖eta ψ G b‖ ≤ T := by
    by_contra h
    push_neg at h
    have hmem : b ∈ (nzFreq F).filter (fun b => T < ‖eta ψ G b‖) := mem_filter.mpr ⟨hbmem, h⟩
    rw [card_eq_zero] at hzero
    rw [hzero] at hmem
    simp at hmem
  -- square it: 0 ≤ ‖eta_b‖ ≤ T ⟹ ‖eta_b‖² ≤ T²
  have hnn : (0:ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  nlinarith [hle, hnn, hTpos]

/-- **End-to-end to the additive-energy budget (Challenge A entry).** Composing the bridge with the
in-tree `addEnergy_le_of_worstCase`: the eta tail hypothesis yields the energy budget
`q·E(G) ≤ |G|⁴ + T²·q·|G|` that drives the far-line incidence bound and hence the MCA δ\*. -/
theorem addEnergy_le_of_etaTail {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (n c T : ℝ) (hN : 1 ≤ ((nzFreq F).card : ℝ)) (hcn : 0 < c / n) (hTpos : 0 ≤ T)
    (hT : (c / n) * T ^ 2 = ((nzFreq F).card : ℝ).log + 1 + ((nzFreq F).card : ℝ).log)
    (htail : EtaSubGaussianTail ψ G n c T) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + (T ^ 2) * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_worstCase hψ G (sq_nonneg T)
    (worstCaseIncompleteSumBound_of_etaTail ψ G n c T hN hcn hTpos hT htail)

end ArkLib.ProximityGap.Frontier.AvW7

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW7.worstCaseIncompleteSumBound_of_etaTail
#print axioms ArkLib.ProximityGap.Frontier.AvW7.addEnergy_le_of_etaTail
