/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungEventInterface

/-!
# The rung threshold router (#371): one census bound covers the whole band

`IdentityCensusBound` is antitone in the witness threshold (`_mono`), and
the cardinality clause of `mcaEvent` at radius `δ` is the integer threshold
`⌈(1−δ)·n⌉₊`; so a census bound at the BINDING threshold `t₀` discharges
`ε_mca(domCode, δ) ≤ B/|F|` for every `δ` with `t₀ − 1 < (1−δ)·n`
(`epsMCA_le_of_identityCensusBound_of_lt`).  At the level-1 rung instance
(`n = 16`, `t₀ = 7`) the condition is exactly `δ < 5/8` — the full interior
band of the obligation `SubCeilingInteriorCeiling` routes through the single
Prop `IdentityCensusBound dom 2 7 31`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section ThresholdRouter

variable (dom : Fin n ↪ F)

open Classical in
/-- The census bound is antitone in the witness threshold: a bound at `t`
covers every larger threshold. -/
theorem identityCensusBound_mono {d t t' B : ℕ} (htt' : t ≤ t')
    (h : IdentityCensusBound dom d t B) :
    IdentityCensusBound dom d t' B := by
  intro u₀ u₁
  refine le_trans (Finset.card_le_card ?_) (h u₀ u₁)
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  obtain ⟨hu, S, hS, hrest⟩ := hγ
  exact ⟨hu, S, le_trans htt' hS, hrest⟩

open Classical in
/-- **The band router**: a census bound at the binding threshold `t₀`
discharges the `ε_mca` obligation at every radius `δ` with
`t₀ − 1 < (1−δ)·n`. -/
theorem epsMCA_le_of_identityCensusBound_of_lt {d t₀ B : ℕ} {δ : ℝ≥0}
    (hδ : ((t₀ - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (h : IdentityCensusBound dom d t₀ B) :
    epsMCA (F := F) (A := F) (domCode dom d) δ
      ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_identityCensusBound dom
    (t := ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (fun S => ProximityGap.MCAExactKit.card_clause_iff_ceil S) ?_
  refine identityCensusBound_mono dom ?_ h
  have := Nat.lt_ceil.mpr hδ
  omega

end ThresholdRouter

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.identityCensusBound_mono
#print axioms ProximityGap.WBPencil.epsMCA_le_of_identityCensusBound_of_lt
