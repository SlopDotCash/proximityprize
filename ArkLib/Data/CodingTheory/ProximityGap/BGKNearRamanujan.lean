/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan
import ArkLib.Data.CodingTheory.ProximityGap.BGKBridge

/-!
# nearramanujan-formalize: the HONEST prize target (#407), correcting the BGKBridge δ=1/2
over-identification.

`BGKBridge.bgkBound_half_of_ramanujan` identifies `BGKBound 2 ψ G (1/2)` (the *constant-2*,
exponent-`1/2` BGK bound) with the in-tree strict-Ramanujan ceiling `‖η_b‖ ≤ 2√n`.  That is the
*strong* target.  But the LIVE energy/incidence consumer (`WorstCaseIncompleteSumBound` →
`addEnergy_le_of_worstCase` → the interior-δ\* chain) does **not** need strict Ramanujan; it needs
only the weaker near-Ramanujan-up-to-`√log` ceiling

> `NearRamanujanBound C ψ G` : `∀ b ≠ 0, ‖η_b‖² ≤ C · n · log(q/n)`   (`n = #G`, `q = #F`).

This is the honest prize-regime target.  This file:

1. **`worstCaseIncompleteSumBound_of_nearRamanujanBound`** — `NearRamanujanBound C` ⟹ the deployed
   consumer `WorstCaseIncompleteSumBound` at scale `M = C·n·log(q/n)` (thread the live chain;
   reuses the in-tree `GeneralizedPaleyNearRamanujan` bridge, no duplication).
   `addEnergy_le_of_nearRamanujanBound` then composes it into the additive-energy budget.

2. **`nearRamanujanBound_of_ramanujan`** — strict Ramanujan `‖η_b‖ ≤ 2√n` ⟹ `NearRamanujanBound C`
   *in the slack regime* `4 ≤ C·log(q/n)` (i.e. once `q/n ≥ e^{4/C}`).  So NearRamanujan is the
   WEAKER target.  At the ENVELOPE level the targets separate: `nearRamanujan_not_implies_ramanujan_envelope`
   exhibits a value strictly between the Ramanujan envelope `4n` and the NearRamanujan envelope
   `C·n·log(q/n)` — an honest bound-level separation (NOT a constructed Gauss-period field witness, so
   not a refutation of the implication between the Props themselves).  It shows the NearRamanujan envelope
   strictly contains the Ramanujan envelope, so the prize needs only the strictly-weaker (still-open)
   NearRamanujan target.

3. **`bgkBound_half_slack_of_nearRamanujanBound`** / **`nearRamanujanBound_of_bgkBound_half_slack`**
   — the honest BGK refinement: `NearRamanujanBound C` is *exactly* `BGKBound` at exponent `δ=1/2`
   but with the `√log`-SLACK constant `C' = √(C·log(q/n))`, NOT the constant `2` of strict
   Ramanujan.  This is the correction to `BGKBridge.bgkBound_half_of_ramanujan`: δ=1/2 is the right
   exponent, but the constant the prize consumer needs is the slowly-growing `√(C·log(q/n))`, not
   the fixed `2`.

ATTACK-SURFACE HONESTY: this brick lives on the per-frequency Gauss-period / energy lane (face #3,
the deployed `WorstCaseIncompleteSumBound`), NOT on the codim-1 sub-object `N = Σ_{i∈S}ω^i`.  It
states and weakens the *named open hypothesis* feeding the live consumer; it does NOT prove the
hypothesis.  No closure asserted.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GeneralizedPaleyRamanujan
open ArkLib.ProximityGap.BGKBridge

namespace ArkLib.ProximityGap.NearRamanujanFormalize

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The honest named target -/

/-- **The honest prize target: near-Ramanujan up to `√log`.**  `∀ b ≠ 0, ‖η_b‖² ≤ C·n·log(q/n)`,
with `n = #G`, `q = #F`.  This is definitionally the in-tree `GeneralizedPaleyNearRamanujan` — we
re-export it under the brick name to keep this file self-contained while reusing (not duplicating)
the substrate object.  It is the WEAKER-than-Ramanujan, still-open, named hypothesis that the live
energy/incidence consumer actually needs. -/
noncomputable def NearRamanujanBound (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  GeneralizedPaleyNearRamanujan C ψ G

/-- The brick target unfolds to the pointwise `√log` ceiling. -/
theorem nearRamanujanBound_iff (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) :
    NearRamanujanBound C ψ G ↔
      ∀ b : F, b ≠ 0 →
        ‖eta ψ G b‖ ^ 2
          ≤ C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) :=
  Iff.rfl

/-! ## (1) NearRamanujan ⟹ the deployed `WorstCaseIncompleteSumBound` consumer -/

/-- **(1) NearRamanujan ⟹ the deployed consumer at `M = C·n·log(q/n)`.**  Threads the honest target
into the live `WorstCaseIncompleteSumBound` (face #3, `prizeRadiusSq ≤ M`), which feeds
`addEnergy_le_of_worstCase` and the interior-δ\* incidence chain.  Reuses the in-tree
`worstCaseIncompleteSumBound_of_nearRamanujan`. -/
theorem worstCaseIncompleteSumBound_of_nearRamanujanBound {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (h : NearRamanujanBound C ψ G) :
    WorstCaseIncompleteSumBound ψ G
      (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :=
  worstCaseIncompleteSumBound_of_nearRamanujan h

/-- **(1') End-to-end energy budget from the honest target.**  Composes (1) with the in-tree
`addEnergy_le_of_worstCase` via the substrate `addEnergy_le_of_nearRamanujan`. -/
theorem addEnergy_le_of_nearRamanujanBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {C : ℝ} (hcard : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : NearRamanujanBound C ψ G) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
          * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_nearRamanujan hψ hcard hC h

/-! ## (2) NearRamanujan is STRICTLY WEAKER than strict Ramanujan -/

/-- **(2) Strict Ramanujan ⟹ NearRamanujan, in the slack regime.**  If `‖η_b‖ ≤ 2√n` (strict
Ramanujan) and the `√log` envelope is at least the Ramanujan envelope `4n` — i.e. `4 ≤ C·log(q/n)`,
which holds once `q/n ≥ e^{4/C}` (the prize regime, `q ≈ n·2^128`) — then `NearRamanujanBound C`
holds.  So strict Ramanujan is the STRONGER hypothesis; the prize asks only for the weaker one. -/
theorem nearRamanujanBound_of_ramanujan {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hslack : (4 : ℝ) ≤ C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (h : GeneralizedPaleyRamanujan ψ G) :
    NearRamanujanBound C ψ G := by
  intro b hb
  have hR : ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card) := h b hb
  -- ‖η_b‖² ≤ 4n
  have h4n : ‖eta ψ G b‖ ^ 2 ≤ 4 * (G.card : ℝ) := by
    have h0 : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    have hsq : Real.sqrt ((G.card : ℝ)) ^ 2 = (G.card : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [hR, h0, Real.sqrt_nonneg ((G.card : ℝ))]
  -- 4n ≤ C·n·log(q/n) because 4 ≤ C·log(q/n) and n ≥ 0
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have henv : (4 : ℝ) * (G.card : ℝ)
      ≤ C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hslack hn
    nlinarith [this]
  linarith [h4n, henv]

/-- **(2') Envelope separation (NOT a Prop-level countermodel).**  For any `n > 0` and any
`C·log(q/n)` strictly above `4` (the genuine prize slack regime), the NearRamanujan envelope
`C·n·log(q/n)` is STRICTLY larger than the strict-Ramanujan envelope `4n`, so there is a value
`v` (e.g. the midpoint) with `4n < v < C·n·log(q/n)`.  This is a bound-level separation showing the
NearRamanujan envelope strictly contains the Ramanujan one — it is NOT a refutation of the implication
`NearRamanujanBound ⇒ GeneralizedPaleyRamanujan` (no field/Gauss-period instance of squared-modulus `v`
is constructed). It witnesses only that the targets differ at the envelope level, so the prize needs
only the strictly-weaker NearRamanujan. -/
theorem nearRamanujan_not_implies_ramanujan_envelope
    {n L : ℝ} (hn : 0 < n) (hL : 4 < L) :
    ∃ v : ℝ, 4 * n < v ∧ v < n * L := by
  refine ⟨n * ((4 + L) / 2), ?_, ?_⟩
  · have : (4 : ℝ) * n = n * 4 := by ring
    rw [this]
    apply mul_lt_mul_of_pos_left _ hn
    linarith
  · apply mul_lt_mul_of_pos_left _ hn
    linarith

/-! ## (3) The BGK refinement: δ=1/2 with the `√log` SLACK constant (not the constant 2) -/

/-- **(3a) NearRamanujan ⟹ BGK at δ=1/2 with the slack constant.**  `NearRamanujanBound C` gives
`‖η_b‖ ≤ √(C·log(q/n)) · √n = √(C·log(q/n)) · n^{1-1/2}`, i.e. `BGKBound (√(C·log(q/n))) ψ G (1/2)`.
This is the HONEST BGK reading: exponent `δ = 1/2` (same as Ramanujan), but the constant is the
slowly-growing `√(C·log(q/n))`, NOT the fixed `2` of `BGKBridge.bgkBound_half_of_ramanujan`. -/
theorem bgkBound_half_slack_of_nearRamanujanBound {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hC : 0 ≤ C) (hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (h : NearRamanujanBound C ψ G) :
    BGKBound (Real.sqrt (C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))) ψ G (1 / 2) := by
  intro b hb
  -- from ‖η_b‖² ≤ C·n·log(q/n), take √: ‖η_b‖ ≤ √(C·log(q/n)) · √n
  have hsq : ‖eta ψ G b‖ ^ 2
      ≤ C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := h b hb
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) with hLdef
  have hCL : 0 ≤ C * L := mul_nonneg hC hlog
  -- RHS rewrite: (C·n·L) = (C·L)·n, and √((C·L)·n) = √(C·L)·√n = √(C·L)·n^{1-1/2}
  have hrw : C * (G.card : ℝ) * L = (C * L) * (G.card : ℝ) := by ring
  have hnorm_nn : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
  -- ‖η_b‖ ≤ √(C·n·L) = √(C·L)·√n
  have hle : ‖eta ψ G b‖ ≤ Real.sqrt ((C * L) * (G.card : ℝ)) := by
    have : ‖eta ψ G b‖ ≤ Real.sqrt (‖eta ψ G b‖ ^ 2) := by
      rw [Real.sqrt_sq hnorm_nn]
    calc ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) := by rw [Real.sqrt_sq hnorm_nn]
      _ ≤ Real.sqrt (C * (G.card : ℝ) * L) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((C * L) * (G.card : ℝ)) := by rw [hrw]
  -- √((C·L)·n) = √(C·L)·√n, and √n = n^{1-1/2}
  have hsplit : Real.sqrt ((C * L) * (G.card : ℝ))
      = Real.sqrt (C * L) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul hCL]
    congr 1
    rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow]
  rw [hsplit] at hle
  exact hle

/-- **(3b) BGK at δ=1/2 with the slack constant ⟹ NearRamanujan.**  Converse of (3a): a BGK bound
`‖η_b‖ ≤ √(C·log(q/n))·n^{1/2}` squares to `‖η_b‖² ≤ C·log(q/n)·n = C·n·log(q/n)`, i.e.
`NearRamanujanBound C`.  Together with (3a) this PINS NearRamanujan to the δ=1/2-with-slack BGK
lane — the correction to the over-strong constant-2 identification. -/
theorem nearRamanujanBound_of_bgkBound_half_slack {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hC : 0 ≤ C) (hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (h : BGKBound (Real.sqrt (C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))) ψ G (1 / 2)) :
    NearRamanujanBound C ψ G := by
  intro b hb
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) with hLdef
  have hCL : 0 ≤ C * L := mul_nonneg hC hlog
  have hb' : ‖eta ψ G b‖
      ≤ Real.sqrt (C * L) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ)) := h b hb
  -- square both sides
  have hbase_nn : 0 ≤ Real.sqrt (C * L) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ)) := by positivity
  have hsq : ‖eta ψ G b‖ ^ 2
      ≤ (Real.sqrt (C * L) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb' 2
  -- (√(C·L)·n^{1/2})² = (C·L)·n = C·n·L
  have hval : (Real.sqrt (C * L) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ))) ^ 2
      = C * (G.card : ℝ) * L := by
    rw [mul_pow, Real.sq_sqrt hCL]
    rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (G.card : ℝ))]
    ring
  rw [hval] at hsq
  exact hsq

/-- **(3c) Honest BGK dichotomy in one statement.**  The strict-Ramanujan BGK reading is
`BGKBound 2 ψ G (1/2)` (constant `2`); the NearRamanujan reading is the SAME exponent `δ=1/2` with
the slack constant `√(C·log(q/n))`.  In the prize regime `q ≈ n·2^128` with `C·log(q/n) > 4` the
slack constant strictly exceeds `2`, so the NearRamanujan BGK ceiling is strictly above (weaker
than) the strict-Ramanujan one — exactly the over-identification this brick corrects. -/
theorem nearRamanujan_bgk_constant_exceeds_two {C L : ℝ} (hCL : 4 < C * L) :
    (2 : ℝ) < Real.sqrt (C * L) := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc (2 : ℝ) = Real.sqrt 4 := h4.symm
    _ < Real.sqrt (C * L) := by
        apply Real.sqrt_lt_sqrt (by norm_num) hCL

end ArkLib.ProximityGap.NearRamanujanFormalize

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.nearRamanujanBound_iff
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.worstCaseIncompleteSumBound_of_nearRamanujanBound
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.addEnergy_le_of_nearRamanujanBound
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.nearRamanujanBound_of_ramanujan
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.nearRamanujan_not_implies_ramanujan_envelope
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.bgkBound_half_slack_of_nearRamanujanBound
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.nearRamanujanBound_of_bgkBound_half_slack
#print axioms ArkLib.ProximityGap.NearRamanujanFormalize.nearRamanujan_bgk_constant_exceeds_two
