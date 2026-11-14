/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingBadScalarCount
import ArkLib.Research.ProximityGap.Lattice2

/-!
# Grand Challenge adapters for the double-cover / zero-error line-decoding surface

`LineDecodingCoverage.lean` proves the coverage-to-vanishing direction for ABF26 Theorem 4.21:
the explicit double-cover hypothesis gives `epsMCA = 0`.  This module repackages that as Grand MCA
Challenge lower witnesses, without using the refuted black-box
`lineDecodable_imp_epsMCA_le_target` surface.

## Honest scope — the prize-rate adapters are vacuous

Every hypothesis consumed here (`MCAForallDoubleCover`, per-bad-scalar double cover,
`mcaBadCount = 0`, `∀ γ, ¬ mcaEvent`, `epsMCA = 0`) implies `epsMCA C δ = 0`; by
`epsMCA_eq_zero_iff_MCAForallDoubleCover` they are all goal-equivalent restatements of a
**zero-error** target (see the circularity note in `LineDecodingT421Faithful.lean`).  For any
proper Reed–Solomon code that target is false: `one_div_card_le_epsMCA_of_succ_le_card` below
proves `1/|F| ≤ epsMCA(RS[k], δ)` at *every* radius `δ` whenever `k + 1 ≤ n` (one-spike plant),
and every ABF26 prize rate has `k = ⌊ρ_j n⌋ < n` (`prizeRateRS_floor_lt_card`).  Hence
`not_MCAForallDoubleCover_prizeRateRS`, `not_forall_badScalarDoubleCover_prizeRateRS`,
`not_forall_mcaBadCount_eq_zero_prizeRateRS`, `not_forall_not_mcaEvent_prizeRateRS` and
`epsMCA_prizeRateRS_ne_zero`: **every prize-rate RS adapter in this module and in the
downstream `LineDecodingSpec`, `LineDecodingResolvedSpec` and `LineDecodingSpecLowOutput`
cones has an unsatisfiable hypothesis, so its conclusion is vacuous.**  These declarations are
kept only as API shape; they are not a coverage theorem, a prize-facing endpoint or a replacement
path for any nonzero-budget MCA bound.  Consumers needing a genuine bound must route through a
nonzero-budget statement (e.g. `epsMCA_le_of_forall_gs_curve_cover`, or the GS list-size cap of
`LineDecodingT421Faithful.lean`).  The general-`C` `ofDoubleCover` constructors are satisfiable
only for degenerate codes (e.g. the full space), where they are restatements of `epsMCA = 0`.
-/

namespace ProximityGap

open scoped NNReal

set_option linter.unusedDecidableInType false

section PrizeRateVacuity

open scoped ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Zero-error MCA is impossible for a proper Reed–Solomon code.**  If `k + 1 ≤ n`, the one-spike
plant (`epsMCA_ge_spike` with `t = 1`) gives `1/|F| ≤ epsMCA(RS[k], δ)` at every radius `δ`. -/
theorem one_div_card_le_epsMCA_of_succ_le_card (domain : ι ↪ F) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι) (δ : ℝ≥0) :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ := by
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hδ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - 1 + 1 : ℕ) := by
    rw [Nat.sub_add_cancel hn]
    exact mul_le_of_le_one_left zero_le tsub_le_self
  simpa using epsMCA_ge_spike domain k 1 δ (by omega) hq hδ

omit [DecidableEq ι] in
/-- Every ABF26 prize degree is strictly below the block length: `⌊ρ_j n⌋ < n`. -/
theorem prizeRateRS_floor_lt_card (j : Fin 4) :
    ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ < Fintype.card ι := by
  have hn : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hρ : prizeRates j < 1 := by
    unfold prizeRates
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ one_lt_two (by omega)
  have hlt : prizeRates j * (Fintype.card ι : ℝ≥0) < Fintype.card ι := by
    simpa using mul_lt_mul_of_pos_right hρ hn
  exact (Nat.floor_lt zero_le).mpr hlt

/-- At every ABF26 prize rate and every radius, `epsMCA(RS, δ) ≥ 1/|F|`. -/
theorem one_div_card_le_epsMCA_prizeRateRS (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ :=
  one_div_card_le_epsMCA_of_succ_le_card domain (prizeRateRS_floor_lt_card j) δ

/-- At every ABF26 prize rate and every radius, `epsMCA(RS, δ) ≠ 0`: the zero-error target of the
double-cover adapters is false. -/
theorem epsMCA_prizeRateRS_ne_zero (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ ≠ 0 := by
  intro h0
  have h := one_div_card_le_epsMCA_prizeRateRS domain j δ
  rw [h0, nonpos_iff_eq_zero, ENNReal.div_eq_zero_iff] at h
  rcases h with h | h
  · exact one_ne_zero h
  · exact ENNReal.natCast_ne_top _ h

/-- The `MCAForallDoubleCover` hypothesis is unsatisfiable at every prize rate. -/
theorem not_MCAForallDoubleCover_prizeRateRS (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    ¬ MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ :=
  fun hcov => epsMCA_prizeRateRS_ne_zero domain j δ
    (epsMCA_eq_zero_of_forall_double_cover _ δ hcov)

/-- The per-bad-scalar double-cover hypothesis is unsatisfiable at every prize rate. -/
theorem not_forall_badScalarDoubleCover_prizeRateRS (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    ¬ ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ :=
  fun hcov => epsMCA_prizeRateRS_ne_zero domain j δ
    (epsMCA_eq_zero_of_badScalarDoubleCover _ δ hcov)

/-- The zero-bad-count hypothesis is unsatisfiable at every prize rate. -/
theorem not_forall_mcaBadCount_eq_zero_prizeRateRS (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    ¬ ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0 :=
  fun hzero => epsMCA_prizeRateRS_ne_zero domain j δ
    (epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (F := F) (A := F) _ δ hzero)

/-- The no-bad-event hypothesis is unsatisfiable at every prize rate. -/
theorem not_forall_not_mcaEvent_prizeRateRS (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0) :
    ¬ ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ :=
  fun hno => epsMCA_prizeRateRS_ne_zero domain j δ
    (epsMCA_eq_zero_of_forall_not_mcaEvent (F := F) (A := F) _ δ hno)

end PrizeRateVacuity

section LowerWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Grand-MCA lower witness from double-cover data.** Given the double-cover hypothesis
(goal-equivalent to `epsMCA = 0`), `epsMCA(C, δ) = 0`, hence any `ε_star` accepts radius `δ` as a
lower witness. -/
def GrandChallenges.MCALowerWitness.ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_double_cover C δ hcov]
    simp

/-- Grand-MCA lower witness from the named per-bad-scalar double-cover obligations. This is the
same double-cover path as `MCALowerWitness.ofDoubleCover`, but with the local GS extraction
target exposed directly. -/
def GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_badScalarDoubleCover C δ hcov]
    simp

/-- Grand-MCA lower witness from zero bad-scalar counts. This keeps the finite-count frontier as a
direct Grand Challenge lower-witness source, without assuming a double-cover package. -/
def GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_mcaBadCount_eq_zero (F := F) (A := F) C δ hzero]
    simp

/-- Grand-MCA lower witness from a direct no-bad-event frontier. -/
def GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ_le_one <| by
    rw [epsMCA_eq_zero_of_forall_not_mcaEvent (F := F) (A := F) C δ hno]
    simp

/-- Grand-MCA lower witness from a direct vanishing-`ε_mca` hypothesis: `ε_mca = 0` repacks as
the double-cover surface, then uses the existing lower-witness front door.  The hypothesis
`ε_mca = 0` is false for every proper Reed–Solomon code (`one_div_card_le_epsMCA_of_succ_le_card`),
so this is not a prize-facing endpoint. -/
def GrandChallenges.MCALowerWitness.of_epsMCA_eq_zero
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F) C δ = 0) :
    GrandChallenges.MCALowerWitness C ε_star :=
  GrandChallenges.MCALowerWitness.ofDoubleCover C δ ε_star hδ_le_one
    ((epsMCA_eq_zero_iff_MCAForallDoubleCover C δ).mp heps)

/-- Prize-rate specialization of double-cover data.  At any ABF26 prize rate, an
explicit `MCAForallDoubleCover` hypothesis for the corresponding Reed-Solomon code gives a
one-sided MCA lower witness at `epsStar`.  The hypothesis is unsatisfiable
(`not_MCAForallDoubleCover_prizeRateRS`), so the statement is vacuous. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.ofDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov, rfl⟩

/-- Prize-rate specialization of the named per-bad-scalar double-cover surface. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov, rfl⟩

/-- Prize-rate specialization of zero bad-scalar counts. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hzero, rfl⟩

/-- Prize-rate specialization of direct no-bad-event frontiers. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hno, rfl⟩

/-- Prize-rate specialization of direct vanishing `ε_mca`. -/
theorem GrandChallenges.exists_prize_mcaLowerWitness_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    ∃ w : GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_epsMCA_eq_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one heps, rfl⟩

end LowerWitness

namespace GrandChallengesLattice

open GrandChallenges

section LatticeWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A double-cover hypothesis makes the faithful MCA lattice threshold exist.  It avoids the
refuted black-box target, but the hypothesis is goal-equivalent to `epsMCA = 0`, which fails for
every proper Reed–Solomon code; it is not a usable replacement path. -/
theorem mcaThresholdExists_ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.ofDoubleCover C δ ε_star hδ_le_one hcov)

/-- The faithful MCA threshold created from double-cover data satisfies the MCA bound. -/
theorem mcaThreshold_spec_ofDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    let hne := mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov)

/-- Double-cover data gives the lattice lower bracket for the faithful MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_ofDoubleCover
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F) C δ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold C ε_star
        (mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov) := by
  simpa [GrandChallenges.MCALowerWitness.ofLe, mcaThresholdExists_ofDoubleCover, GrandChallenges.MCALowerWitness.ofDoubleCover]
    using MCALowerWitness_le_mcaThreshold C ε_star
      (mcaThresholdExists_ofDoubleCover C δ ε_star hδ_le_one hcov)
      (GrandChallenges.MCALowerWitness.ofDoubleCover C δ ε_star hδ_le_one hcov)

/-- A named per-bad-scalar double-cover target makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofBadScalarDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)

/-- The faithful MCA threshold created from named per-bad-scalar double-cover data satisfies the
MCA bound. -/
theorem mcaThreshold_spec_ofBadScalarDoubleCover (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    let hne := mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)

/-- Named per-bad-scalar double-cover data gives the lattice lower bracket for the faithful
MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_ofBadScalarDoubleCover
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F) C δ (u 0) (u 1) γ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold C ε_star
        (mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov) := by
  simpa [GrandChallenges.MCALowerWitness.ofLe, mcaThresholdExists_ofBadScalarDoubleCover,
    GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover]
    using MCALowerWitness_le_mcaThreshold C ε_star
      (mcaThresholdExists_ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)
      (GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover C δ ε_star hδ_le_one hcov)

/-- Zero bad-scalar counts make the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_mcaBadCount_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)

/-- The faithful MCA threshold created from zero bad-scalar counts satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_mcaBadCount_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    let hne := mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)

/-- Zero bad-scalar counts give the lattice lower bracket for the faithful MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_mcaBadCount_zero
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold C ε_star
        (mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero) := by
  simpa [GrandChallenges.MCALowerWitness.ofLe, mcaThresholdExists_of_mcaBadCount_zero,
    GrandChallenges.MCALowerWitness.of_mcaBadCount_zero]
    using MCALowerWitness_le_mcaThreshold C ε_star
      (mcaThresholdExists_of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)
      (GrandChallenges.MCALowerWitness.of_mcaBadCount_zero C δ ε_star hδ_le_one hzero)

/-- A direct no-bad-event frontier makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_forall_not_mcaEvent (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)

/-- The faithful MCA threshold created from a no-bad-event frontier satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_forall_not_mcaEvent (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    let hne := mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)

/-- A direct no-bad-event frontier gives the lattice lower bracket for the faithful MCA
threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_forall_not_mcaEvent
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F) C δ (u 0) (u 1) γ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold C ε_star
        (mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno) := by
  simpa [GrandChallenges.MCALowerWitness.ofLe, mcaThresholdExists_of_forall_not_mcaEvent,
    GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent]
    using MCALowerWitness_le_mcaThreshold C ε_star
      (mcaThresholdExists_of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)
      (GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent C δ ε_star hδ_le_one hno)

/-- A direct vanishing-`ε_mca` frontier makes the faithful MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_epsMCA_eq_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F) C δ = 0) :
    mcaThresholdExists C ε_star :=
  mcaThresholdExists_of_MCALowerWitness C ε_star
    (MCALowerWitness.of_epsMCA_eq_zero C δ ε_star hδ_le_one heps)

/-- The faithful MCA threshold created from a vanishing-`ε_mca` frontier satisfies the MCA
bound. -/
theorem mcaThreshold_spec_of_epsMCA_eq_zero (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F) C δ = 0) :
    let hne := mcaThresholdExists_of_epsMCA_eq_zero C δ ε_star hδ_le_one heps
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star
    (mcaThresholdExists_of_epsMCA_eq_zero C δ ε_star hδ_le_one heps)

/-- A direct vanishing-`ε_mca` frontier gives the lattice lower bracket for the faithful MCA
threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_epsMCA_eq_zero
    (C : Set (ι → F)) (δ ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F) C δ = 0) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold C ε_star
        (mcaThresholdExists_of_epsMCA_eq_zero C δ ε_star hδ_le_one heps) := by
  simpa [GrandChallenges.MCALowerWitness.ofLe, GrandChallenges.MCALowerWitness.ofDoubleCover,
    mcaThresholdExists_of_epsMCA_eq_zero,
    GrandChallenges.MCALowerWitness.of_epsMCA_eq_zero]
    using MCALowerWitness_le_mcaThreshold C ε_star
      (mcaThresholdExists_of_epsMCA_eq_zero C δ ε_star hδ_le_one heps)
      (GrandChallenges.MCALowerWitness.of_epsMCA_eq_zero C δ ε_star hδ_le_one heps)

/-- Prize-rate double-cover data makes the corresponding faithful MCA lattice threshold
exist. -/
theorem mcaThresholdExists_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar :=
  mcaThresholdExists_ofDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- The faithful MCA threshold selected from prize-rate double-cover data satisfies the
MCA bound. -/
theorem mcaThreshold_spec_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    let hne := mcaThresholdExists_ofDoubleCover C δ epsStar hδ_le_one hcov
    mcaSatisfies C epsStar (mcaThreshold C epsStar hne) :=
  mcaThreshold_spec_ofDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- Prize-rate named per-bad-scalar double-cover data makes the corresponding faithful MCA
lattice threshold exist. -/
theorem mcaThresholdExists_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar :=
  mcaThresholdExists_ofBadScalarDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- The faithful MCA threshold selected from prize-rate named per-bad-scalar double-cover data
satisfies the MCA bound. -/
theorem mcaThreshold_spec_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    let hne := mcaThresholdExists_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
    mcaSatisfies C epsStar (mcaThreshold C epsStar hne) :=
  mcaThreshold_spec_ofBadScalarDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- Prize-rate zero bad-scalar counts make the corresponding faithful MCA lattice threshold
exist. -/
theorem mcaThresholdExists_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar :=
  mcaThresholdExists_of_mcaBadCount_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hzero

/-- The faithful MCA threshold selected from prize-rate zero bad-scalar counts satisfies the MCA
bound. -/
theorem mcaThreshold_spec_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    let hne := mcaThresholdExists_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
    mcaSatisfies C epsStar (mcaThreshold C epsStar hne) :=
  mcaThreshold_spec_of_mcaBadCount_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hzero

/-- Prize-rate direct no-bad-event frontiers make the corresponding faithful MCA lattice threshold
exist. -/
theorem mcaThresholdExists_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar :=
  mcaThresholdExists_of_forall_not_mcaEvent
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hno

/-- The faithful MCA threshold selected from prize-rate no-bad-event frontiers satisfies the MCA
bound. -/
theorem mcaThreshold_spec_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    let hne := mcaThresholdExists_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
    mcaSatisfies C epsStar (mcaThreshold C epsStar hne) :=
  mcaThreshold_spec_of_forall_not_mcaEvent
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hno

/-- Prize-rate direct vanishing `ε_mca` makes the corresponding faithful MCA lattice threshold
exist. -/
theorem mcaThresholdExists_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    mcaThresholdExists
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar :=
  mcaThresholdExists_of_epsMCA_eq_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one heps

/-- The faithful MCA threshold selected from prize-rate vanishing `ε_mca` satisfies the MCA
bound. -/
theorem mcaThreshold_spec_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    let hne := mcaThresholdExists_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
    mcaSatisfies C epsStar (mcaThreshold C epsStar hne) :=
  mcaThreshold_spec_of_epsMCA_eq_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one heps

/-- Prize-rate double-cover data gives the lower bracket for the corresponding faithful
MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar
        (mcaThresholdExists_ofDoubleCover
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          δ epsStar hδ_le_one hcov) :=
  latticeIndexOf_le_mcaThreshold_ofDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- Prize-rate named per-bad-scalar double-cover data gives the lower bracket for the
corresponding faithful MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar
        (mcaThresholdExists_ofBadScalarDoubleCover
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          δ epsStar hδ_le_one hcov) :=
  latticeIndexOf_le_mcaThreshold_ofBadScalarDoubleCover
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hcov

/-- Prize-rate zero bad-scalar counts give the lower bracket for the corresponding faithful MCA
threshold. -/
theorem latticeIndexOf_le_mcaThreshold_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar
        (mcaThresholdExists_of_mcaBadCount_zero
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          δ epsStar hδ_le_one hzero) :=
  latticeIndexOf_le_mcaThreshold_of_mcaBadCount_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hzero

/-- Prize-rate direct no-bad-event frontiers give the lower bracket for the corresponding
faithful MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar
        (mcaThresholdExists_of_forall_not_mcaEvent
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          δ epsStar hδ_le_one hno) :=
  latticeIndexOf_le_mcaThreshold_of_forall_not_mcaEvent
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one hno

/-- Prize-rate direct vanishing `ε_mca` gives the lower bracket for the corresponding faithful
MCA threshold. -/
theorem latticeIndexOf_le_mcaThreshold_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar
        (mcaThresholdExists_of_epsMCA_eq_zero
          (ReedSolomon.code domain
            ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          δ epsStar hδ_le_one heps) :=
  latticeIndexOf_le_mcaThreshold_of_epsMCA_eq_zero
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    δ epsStar hδ_le_one heps

/-- Prize-rate double-cover data packages threshold existence, satisfaction, and the
lower lattice bracket for the selected faithful MCA threshold. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_ofDoubleCover C δ epsStar hδ_le_one hcov
  refine ⟨hne, ?_, ?_⟩
  · exact mcaThreshold_spec_ofDoubleCover C δ epsStar hδ_le_one hcov
  · exact latticeIndexOf_le_mcaThreshold_ofDoubleCover C δ epsStar hδ_le_one hcov

/-- Prize-rate named per-bad-scalar double-cover data packages threshold existence, satisfaction,
and the lower lattice bracket for the selected faithful MCA threshold. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
  refine ⟨hne, ?_, ?_⟩
  · exact mcaThreshold_spec_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
  · exact latticeIndexOf_le_mcaThreshold_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov

/-- Prize-rate zero bad-scalar counts package threshold existence, satisfaction, and the lower
lattice bracket for the selected faithful MCA threshold. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
  refine ⟨hne, ?_, ?_⟩
  · exact mcaThreshold_spec_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
  · exact latticeIndexOf_le_mcaThreshold_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero

/-- Prize-rate direct no-bad-event frontiers package threshold existence, satisfaction, and the
lower lattice bracket for the selected faithful MCA threshold. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
  refine ⟨hne, ?_, ?_⟩
  · exact mcaThreshold_spec_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
  · exact latticeIndexOf_le_mcaThreshold_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno

/-- Prize-rate direct vanishing `ε_mca` packages threshold existence, satisfaction, and the lower
lattice bracket for the selected faithful MCA threshold. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
  refine ⟨hne, ?_, ?_⟩
  · exact mcaThreshold_spec_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
  · exact latticeIndexOf_le_mcaThreshold_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps

/-- Prize-rate double-cover data, together with an explicit upper witness, packages the
selected faithful MCA threshold with its satisfy fact and both lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_ofDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) δ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_ofDoubleCover C δ epsStar hδ_le_one hcov
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact mcaThreshold_spec_ofDoubleCover C δ epsStar hδ_le_one hcov
  · exact latticeIndexOf_le_mcaThreshold_ofDoubleCover C δ epsStar hδ_le_one hcov
  · exact mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- Prize-rate named per-bad-scalar double-cover data, together with an explicit upper witness,
packages the selected faithful MCA threshold with its satisfy fact and both lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_ofBadScalarDoubleCover
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact mcaThreshold_spec_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
  · exact latticeIndexOf_le_mcaThreshold_ofBadScalarDoubleCover C δ epsStar hδ_le_one hcov
  · exact mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- Prize-rate zero bad-scalar counts, together with an explicit upper witness, package the
selected faithful MCA threshold with its satisfy fact and both lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_of_mcaBadCount_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hzero : ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) = 0)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact mcaThreshold_spec_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
  · exact latticeIndexOf_le_mcaThreshold_of_mcaBadCount_zero C δ epsStar hδ_le_one hzero
  · exact mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- Prize-rate direct no-bad-event frontiers, together with an explicit upper witness, package the
selected faithful MCA threshold with its satisfy fact and both lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_of_forall_not_mcaEvent
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hno : ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        δ (u 0) (u 1) γ)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact mcaThreshold_spec_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
  · exact latticeIndexOf_le_mcaThreshold_of_forall_not_mcaEvent C δ epsStar hδ_le_one hno
  · exact mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- Prize-rate direct vanishing `ε_mca`, together with an explicit upper witness, packages the
selected faithful MCA threshold with its satisfy fact and both lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_of_epsMCA_eq_zero
    (domain : ι ↪ F) (j : Fin 4) (δ : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (heps : epsMCA (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      δ = 0)
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar)
    (hδhi : whi.δ ≤ 1) :
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    ∃ hne : mcaThresholdExists C epsStar,
      mcaSatisfies C epsStar (mcaThreshold C epsStar hne) ∧
        latticeIndexOf (ι := ι) δ hδ_le_one ≤ mcaThreshold C epsStar hne ∧
          mcaThreshold C epsStar hne < latticeIndexOf (ι := ι) whi.δ hδhi := by
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne : mcaThresholdExists C epsStar :=
    mcaThresholdExists_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact mcaThreshold_spec_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
  · exact latticeIndexOf_le_mcaThreshold_of_epsMCA_eq_zero C δ epsStar hδ_le_one heps
  · exact mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- Per-rate double-cover data resolves the faithful MCA lattice prize existentially, through the
existing lower-witness lattice front door. **Vacuous for proper RS codes** (see the module's honest-scope note).  The hypothesis is unsatisfiable at
every prize rate (`not_MCAForallDoubleCover_prizeRateRS`). -/
theorem exists_mcaPrizeLatticeResolved_ofDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j)) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.ofDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate named per-bad-scalar double-cover obligations resolve the faithful MCA lattice prize
existentially. -/
theorem exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hcov j)

/-- Per-rate zero bad-scalar counts resolve the faithful MCA lattice prize existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_mcaBadCount_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hzero j)

/-- Per-rate direct no-bad-event frontiers resolve the faithful MCA lattice prize
existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_forall_not_mcaEvent
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j) epsStar (hδ_le_one j) (hno j)

/-- Per-rate direct vanishing `ε_mca` frontiers resolve the faithful MCA lattice prize
existentially. The proof explicitly routes through the indexed #140 exactness bridge to the
double-cover surface.  The hypothesis is unsatisfiable at every prize rate
(`epsMCA_prizeRateRS_ne_zero`). -/
theorem exists_mcaPrizeLatticeResolved_of_epsMCA_eq_zero
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_ofDoubleCover domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)

/-- Double-cover frontiers and explicit upper witnesses bracket all four faithful MCA
prize thresholds. -/
def mcaPrizeLattice_bracketed_ofDoubleCover_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_of_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.ofDoubleCover
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hcov j))
    whi hδhi

/-- Double-cover frontiers and adjacent explicit upper witnesses resolve the four-rate
MCA prize lattice at the double-cover lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_ofDoubleCover_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, MCAForallDoubleCover (F := F) (A := F)
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      (δ j))
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.ofDoubleCover
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hcov j))
    whi hδhi ?_
  intro j
  exact hadj j

/-- Named per-bad-scalar double-cover frontiers and explicit upper witnesses bracket all four
faithful MCA prize thresholds. -/
def mcaPrizeLattice_bracketed_ofBadScalarDoubleCover_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_of_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hcov j))
    whi hδhi

/-- Named per-bad-scalar double-cover frontiers and adjacent explicit upper witnesses resolve the
four-rate MCA prize lattice at the double-cover lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hcov : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := F)
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hcov j))
    whi hδhi ?_
  intro j
  exact hadj j

/-- Zero bad-scalar counts and explicit upper witnesses bracket all four faithful MCA prize
thresholds. -/
def mcaPrizeLattice_bracketed_of_mcaBadCount_zero_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_of_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hzero j))
    whi hδhi

/-- Zero bad-scalar counts and adjacent explicit upper witnesses resolve the four-rate MCA prize
lattice at the double-cover lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_of_mcaBadCount_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hzero : ∀ j : Fin 4, ∀ u : Code.WordStack F (Fin 2) ι,
      mcaBadCount (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hzero j))
    whi hδhi ?_
  intro j
  exact hadj j

/-- Direct no-bad-event frontiers and explicit upper witnesses bracket all four faithful MCA prize
thresholds. -/
def mcaPrizeLattice_bracketed_of_forall_not_mcaEvent_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_of_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hno j))
    whi hδhi

/-- Direct no-bad-event frontiers and adjacent explicit upper witnesses resolve the four-rate MCA
prize lattice at the double-cover lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (hno : ∀ j : Fin 4, ∀ (u : Code.WordStack F (Fin 2) ι) (γ : F),
      ¬ mcaEvent (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) (u 0) (u 1) γ)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) := by
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain
    (fun j =>
      GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) epsStar (hδ_le_one j) (hno j))
    whi hδhi ?_
  intro j
  exact hadj j

/-- Direct vanishing `ε_mca` frontiers and explicit upper witnesses bracket all four faithful MCA
prize thresholds. -/
def mcaPrizeLattice_bracketed_of_epsMCA_eq_zero_and_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :=
  mcaPrizeLattice_bracketed_ofDoubleCover_and_upperWitnesses domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)
    whi hδhi

/-- Direct vanishing `ε_mca` frontiers and adjacent explicit upper witnesses resolve the four-rate
MCA prize lattice at the double-cover lower-frontier lattice indices. -/
theorem mcaPrizeLatticeResolved_of_epsMCA_eq_zero_and_adjacent_upperWitnesses
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (heps : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        (δ j) = 0)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ j) (hδ_le_one j)) :=
  mcaPrizeLatticeResolved_ofDoubleCover_and_adjacent_upperWitnesses
    domain δ hδ_le_one
    (indexed_MCAForallDoubleCover_of_epsMCA_eq_zero
      (fun j : Fin 4 =>
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      δ heps)
    whi hδhi hadj

end LatticeWitness

end GrandChallengesLattice

#print axioms ProximityGap.GrandChallenges.MCALowerWitness.ofDoubleCover
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_ofDoubleCover
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallenges.exists_prize_mcaLowerWitness_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_ofDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_ofBadScalarDoubleCover
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_prize_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_prize_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_prize_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_prize_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_prize_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_prize_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_prize_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_lower_bracket_prize_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_and_bracket_prize_of_epsMCA_eq_zero
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_ofDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_ofBadScalarDoubleCover
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_mcaBadCount_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_forall_not_mcaEvent
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_epsMCA_eq_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_ofDoubleCover_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_ofDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_ofBadScalarDoubleCover_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_ofBadScalarDoubleCover_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_of_mcaBadCount_zero_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_mcaBadCount_zero_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_of_forall_not_mcaEvent_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_forall_not_mcaEvent_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLattice_bracketed_of_epsMCA_eq_zero_and_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_of_epsMCA_eq_zero_and_adjacent_upperWitnesses

end ProximityGap

/-! ## Axiom audit — prize-rate vacuity lemmas -/
#print axioms ProximityGap.one_div_card_le_epsMCA_of_succ_le_card
#print axioms ProximityGap.epsMCA_prizeRateRS_ne_zero
#print axioms ProximityGap.not_MCAForallDoubleCover_prizeRateRS
#print axioms ProximityGap.not_forall_badScalarDoubleCover_prizeRateRS
#print axioms ProximityGap.not_forall_mcaBadCount_eq_zero_prizeRateRS
#print axioms ProximityGap.not_forall_not_mcaEvent_prizeRateRS
