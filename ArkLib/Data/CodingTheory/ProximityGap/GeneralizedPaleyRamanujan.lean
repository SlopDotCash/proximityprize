/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant

/-!
# The generalized-Paley spectral lane for the proximity-prize per-frequency core (#407)

**The dictionary (Liu–Zhou, *Eigenvalues of Cayley graphs*, arXiv:1809.09829, Thm 115).**
The in-tree per-frequency object `eta ψ G b = Σ_{y∈G} ψ(b·y)` (the incomplete subgroup Gauss
sum) is, for `G = μ_n` the smooth domain, the non-principal eigenvalue of the generalized Paley
graph `Cay(F_q, G)`. Its worst-case modulus `M(n) = max_{b≠0} ‖eta ψ G b‖` is the graph's
non-principal spectral radius. This is the surviving F2=F3 spectral identity in the #407 ledger.

The prize-regime target is **not** the literal Ramanujan threshold `2√|G|`. The live ceiling is
the near-Ramanujan-up-to-`√log` scale

> `‖eta ψ G b‖² ≤ C · |G| · log(|F|/|G|)` for every `b ≠ 0`,

equivalently `M(n) ≤ O(√(|G| log(q/n)))`. The second-moment law gives the matching Parseval
floor `M(n)² ≥ |G|(|F|-|G|)/(|F|-1)` on the nonzero spectrum; the thin-subgroup eigenvalue
ceiling above that floor is the named open BGK / Paley-graph / thin-subgroup-equidistribution wall.

This file therefore records two hypotheses:

* `GeneralizedPaleyNearRamanujan` — the current #407 lever at the `√log` loss.
* `GeneralizedPaleyRamanujan` — the older `2√|G|` ceiling, kept only as a backward-compatible,
  strictly stronger named residual. It is not claimed as the prize target.

The consumers below only bridge named hypotheses into the existing `WorstCaseIncompleteSumBound`
residual and additive-energy chain. No closure is asserted.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #389.
-/

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.PrizeStructuralConstant

namespace ArkLib.ProximityGap.GeneralizedPaleyRamanujan

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Near-Ramanujan up to `√log` for the generalized Paley graph.** This is the current #407
spectral ceiling: every nonzero Gauss period has squared modulus at most
`C · |G| · log(|F|/|G|)`. It is the honest prize-regime target, not a theorem here. The named open
content is exactly the thin-subgroup worst-case eigenvalue bound above the Parseval floor. -/
noncomputable def GeneralizedPaleyNearRamanujan
    (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ G b‖ ^ 2
      ≤ C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))

/-- A near-Ramanujan-up-to-`√log` generalized Paley graph is exactly the existing worst-case
incomplete-sum residual at the squared `√(|G| log(q/n))` scale. -/
theorem worstCaseIncompleteSumBound_of_nearRamanujan {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (h : GeneralizedPaleyNearRamanujan C ψ G) :
    WorstCaseIncompleteSumBound ψ G
      (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :=
  h

/-- **Near-Ramanujan-up-to-`√log` yields the additive-energy budget.** This is the live #407
consumer matching the legacy strict-Ramanujan bridge below, but at the correctly scaled
`C·|G|·log(q/|G|)` worst-case envelope. The hypothesis remains named-open; this theorem only
threads it through the already-proven `addEnergy_le_of_worstCase` bridge. -/
theorem addEnergy_le_of_nearRamanujan {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {C : ℝ} (hcard : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : GeneralizedPaleyNearRamanujan C ψ G) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
          * ((Fintype.card F : ℝ) * G.card) := by
  have hM0 :
      0 ≤ C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
    by_cases hG0 : G.card = 0
    · simp [hG0]
    · have hGposNat : 0 < G.card := Nat.pos_of_ne_zero hG0
      have hGpos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGposNat
      have hdiv : (1 : ℝ) ≤ (Fintype.card F : ℝ) / (G.card : ℝ) := by
        rw [le_div_iff₀ hGpos]
        simpa using hcard
      have hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) :=
        Real.log_nonneg hdiv
      positivity
  exact addEnergy_le_of_worstCase hψ G hM0
    (worstCaseIncompleteSumBound_of_nearRamanujan h)

/-! ### Bridge to the single structural constant `Λ` -/

/-- **The structural-constant face implies the Paley face.**  The open property
`DepthLogSubGaussian` is the one-object bound `Λ² ≤ 2|G| log |F|`.  Whenever the regime arithmetic
absorbs this into the near-Ramanujan envelope `C|G| log(|F|/|G|)`, it gives the generalized-Paley
near-Ramanujan hypothesis pointwise.  This is only a dictionary bridge: the log inequality and
`DepthLogSubGaussian` remain the actual inputs. -/
theorem nearRamanujan_of_depthLogSubGaussian {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hlog : 2 * Real.log (Fintype.card F : ℝ)
      ≤ C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (h : DepthLogSubGaussian ψ G) :
    GeneralizedPaleyNearRamanujan C ψ G := by
  intro b hb
  have hW :
      WorstCaseIncompleteSumBound ψ G
        (2 * (G.card : ℝ) * Real.log (Fintype.card F : ℝ)) :=
    (worstCaseIncompleteSumBound_iff_prizeRadiusSq_le ψ G
      (2 * (G.card : ℝ) * Real.log (Fintype.card F : ℝ))).mpr h
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ 2
      ≤ 2 * (G.card : ℝ) * Real.log (Fintype.card F : ℝ) := hW b hb
    _ = (G.card : ℝ) * (2 * Real.log (Fintype.card F : ℝ)) := by ring
    _ ≤ (G.card : ℝ) *
          (C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog hn
    _ = C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
        ring

/-- **The Paley face implies the structural-constant face under the reverse log comparison.**
This is the converse dictionary bridge to `nearRamanujan_of_depthLogSubGaussian`: if the chosen
near-Ramanujan envelope is no larger than `2|G| log |F|`, then it yields the one-object
`DepthLogSubGaussian` predicate. -/
theorem depthLogSubGaussian_of_nearRamanujan {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hlog : C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))
      ≤ 2 * Real.log (Fintype.card F : ℝ))
    (h : GeneralizedPaleyNearRamanujan C ψ G) :
    DepthLogSubGaussian ψ G := by
  have hW :
      WorstCaseIncompleteSumBound ψ G
        (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :=
    worstCaseIncompleteSumBound_of_nearRamanujan h
  have hΛ :
      prizeRadiusSq ψ G
        ≤ C * (G.card : ℝ) *
          Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) :=
    (worstCaseIncompleteSumBound_iff_prizeRadiusSq_le ψ G
      (C * (G.card : ℝ) *
        Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))).mp hW
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  have htarget :
      C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))
        ≤ 2 * (G.card : ℝ) * Real.log (Fintype.card F : ℝ) := by
    calc C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))
        = (G.card : ℝ) *
            (C * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) := by ring
      _ ≤ (G.card : ℝ) * (2 * Real.log (Fintype.card F : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog hn
      _ = 2 * (G.card : ℝ) * Real.log (Fintype.card F : ℝ) := by ring
  exact le_trans hΛ htarget

/-- **The historical strict Ramanujan ceiling.** Every nonzero Gauss period has modulus at most
`2·√|G|`. The #407 ledger treats this as a backward-compatible, over-strong named residual: it
implies the live consumers, but the prize route only asks for the weaker `√log` loss above the
Parseval floor. -/
def GeneralizedPaleyRamanujan (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card)

/-! ### Parseval floor for the nonzero spectrum -/

/-- **Nonzero spectral mass.** Splitting the landed second-moment law at `b = 0` gives
`Σ_{b≠0} ‖η_b‖² = |F|·|G| − |G|²`. This is the exact Parseval mass on the non-principal
spectrum of the generalized Paley graph. -/
theorem nonzero_spectral_mass {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have h2 := subgroup_gaussSum_secondMoment hψ G
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [eta, AddChar.map_zero_eq_one]
  have hn0sq : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [h0, Complex.norm_natCast]
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  rw [hsplit, hn0sq] at h2
  linarith [h2]

/-- **Parseval floor for the non-principal eigenvalue.** If the field has at least two elements,
then some nonzero frequency has

`|η_b|² ≥ |G| · (|F| - |G|) / (|F| - 1)`.

For a proper thin subgroup this is `≈ |G|`, the square of the `√|G|` floor. It is a lower bound
only: the matching near-Ramanujan-up-to-`√log` upper ceiling remains the named open thin-subgroup
eigenvalue problem. -/
theorem exists_nonzero_frequency_gaussSum_sq_ge_parseval {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (hq1 : 1 < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ))
          / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  classical
  let floor : ℝ :=
    (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ))
      / ((Fintype.card F : ℝ) - 1)
  by_contra h
  push Not at h
  have hcardErase :
      (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hEraseNonempty : (Finset.univ.erase (0 : F)).Nonempty := by
    rw [← Finset.card_pos, hcardErase]
    omega
  have hsumlt :
      ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
        < ∑ _b ∈ Finset.univ.erase (0 : F), floor :=
    Finset.sum_lt_sum_of_nonempty hEraseNonempty (fun b hb => h b (Finset.mem_erase.mp hb).1)
  have hmass := nonzero_spectral_mass hψ G
  have hcardEraseReal :
      ((Finset.univ.erase (0 : F)).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hcardErase, Nat.cast_sub (by omega)]
    norm_num
  have hden : (Fintype.card F : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq1
    linarith
  have hfloorSum :
      ∑ _b ∈ Finset.univ.erase (0 : F), floor
        = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardEraseReal]
    unfold floor
    field_simp [hden]
  rw [hmass, hfloorSum] at hsumlt
  exact (lt_irrefl _) hsumlt

/-- **The dictionary bridge.** A Ramanujan generalized Paley graph discharges the in-tree open
residual `WorstCaseIncompleteSumBound` at scale `M = 4·|G|`.
The implication is `‖eta‖ ≤ 2√|G| ⟹ ‖eta‖² ≤ 4|G|`, feeding the existing
interior δ\* consumer chain.
This is an over-strong legacy bridge; the live #407 spectral lane is
`worstCaseIncompleteSumBound_of_nearRamanujan`. -/
theorem worstCaseIncompleteSumBound_of_ramanujan {ψ : AddChar F ℂ} {G : Finset F}
    (h : GeneralizedPaleyRamanujan ψ G) :
    WorstCaseIncompleteSumBound ψ G (4 * G.card) := by
  intro b hb
  have hsq : ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card) := h b hb
  have hsqrt : Real.sqrt ((G.card : ℝ)) ^ 2 = (G.card : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hle : ‖eta ψ G b‖ ^ 2 ≤ (2 * Real.sqrt (G.card)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    nlinarith [hsq, h0, Real.sqrt_nonneg ((G.card : ℝ))]
  have hval : (2 * Real.sqrt ((G.card : ℝ))) ^ 2 = 4 * (G.card : ℝ) := by
    rw [mul_pow, hsqrt]; ring
  calc ‖eta ψ G b‖ ^ 2 ≤ (2 * Real.sqrt (G.card)) ^ 2 := hle
    _ = 4 * (G.card : ℝ) := hval

/-- **End-to-end legacy bridge:** a strict Ramanujan generalized Paley graph yields the
additive-energy budget
`q·E(G) ≤ |G|⁴ + 4|G|·(q·|G|)` (composing the dictionary bridge with the in-tree consumer
`addEnergy_le_of_worstCase`). This remains useful as a compatibility theorem, but the prize-regime
ceiling is the named open `√log` variant above, not literal Ramanujan. -/
theorem addEnergy_le_of_ramanujan {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h : GeneralizedPaleyRamanujan ψ G) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + (4 * G.card) * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_worstCase hψ G (by positivity) (worstCaseIncompleteSumBound_of_ramanujan h)

end ArkLib.ProximityGap.GeneralizedPaleyRamanujan

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms
  ArkLib.ProximityGap.GeneralizedPaleyRamanujan.worstCaseIncompleteSumBound_of_nearRamanujan
#print axioms
  ArkLib.ProximityGap.GeneralizedPaleyRamanujan.addEnergy_le_of_nearRamanujan
#print axioms
  ArkLib.ProximityGap.GeneralizedPaleyRamanujan.nearRamanujan_of_depthLogSubGaussian
#print axioms
  ArkLib.ProximityGap.GeneralizedPaleyRamanujan.depthLogSubGaussian_of_nearRamanujan
#print axioms ArkLib.ProximityGap.GeneralizedPaleyRamanujan.nonzero_spectral_mass
#print axioms
  ArkLib.ProximityGap.GeneralizedPaleyRamanujan.exists_nonzero_frequency_gaussSum_sq_ge_parseval
#print axioms ArkLib.ProximityGap.GeneralizedPaleyRamanujan.worstCaseIncompleteSumBound_of_ramanujan
#print axioms ArkLib.ProximityGap.GeneralizedPaleyRamanujan.addEnergy_le_of_ramanujan
