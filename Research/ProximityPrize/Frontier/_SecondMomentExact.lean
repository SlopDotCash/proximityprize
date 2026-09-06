/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The exact DC-subtracted second moment (#407)

The `r = 1` base case of the moment ladder is exact and unconditional (no energy conjecture): the
first additive energy is `E_1(G) = |G|` (only the diagonal `x = y` contributes), so the DC-subtracted
second moment is

> **`sum_nonzero_sq`** — `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`.

Hence `A_1 = (1/q)∑_{b≠0}‖η_b‖² = |G| − |G|²/q < |G| = Wick(1)`, so the prize bound `A_r ≤ (2r−1)‼·|G|^r`
holds **exactly at `r = 1`** (the base case the moment method anchors on). The open content is `r ≥ 2`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ProximityGap.Frontier.SecondMomentExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **First additive energy is the cardinality.** `E_1(G) = |G|`: a `1`-tuple sum is its single entry,
so `∑ x = ∑ y` over `1`-tuples means `x = y`, contributing exactly `|G|` diagonal pairs. -/
theorem rEnergy_one (G : Finset F) : rEnergy G 1 = G.card := by
  classical
  unfold rEnergy
  simp only [Fin.sum_univ_one]
  -- For each `v`, exactly one `w` (the constant tuple at `v 0`) satisfies `v 0 = w 0`.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
      (∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G), (if v 0 = w 0 then 1 else 0)) = 1 := by
    intro v hv
    rw [Fintype.mem_piFinset] at hv
    -- the unique matching `w` is the constant tuple `![v 0]`
    rw [Finset.sum_eq_single (fun _ : Fin 1 => v 0)]
    · simp
    · intro w hw hne
      rw [if_neg]
      intro hvw
      apply hne
      funext i
      fin_cases i
      exact hvw.symm
    · intro hmem
      exact absurd (Fintype.mem_piFinset.2 (fun i => by fin_cases i; exact hv 0)) hmem
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Fintype.card_piFinset]
  simp

/-- **The exact `r = 1` DC-subtracted second moment.** Specializing `sum_nonzero_moment` at `r = 1`
with `E_1(G) = |G|` (`rEnergy_one`):

> `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`.

Exact and unconditional (no energy conjecture). Hence `A_1 = (1/q)∑_{b≠0}‖η_b‖² = |G| − |G|²/q < |G|`,
so the prize bound `A_r ≤ (2r−1)‼·|G|^r` holds **exactly at the base case** `r = 1`.
The open content is `r ≥ 2`. -/
theorem sum_nonzero_sq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := by
  have h := sum_nonzero_moment hψ G 1
  rw [rEnergy_one] at h
  simpa using h

/-- **The `r = 1` base case strictly beats the trivial value.** For nonempty `G`,
`∑_{b≠0}‖η_b‖² = q·|G| − |G|² < q·|G|`, i.e. `A_1 = |G| − |G|²/q < |G|`: the DC-subtracted
second moment is **strictly** below `q·|G|`, so the moment method's base case clears the
Wick value `Wick(1) = |G|` with room (the `−|G|²/q` deficit). -/
theorem base_case_strict {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : G.Nonempty) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 < (Fintype.card F : ℝ) * (G.card : ℝ) := by
  rw [sum_nonzero_sq hψ G]
  have hpos : (0 : ℝ) < (G.card : ℝ) ^ 2 := by
    have : 0 < G.card := Finset.card_pos.mpr hG
    positivity
  linarith

end ProximityGap.Frontier.SecondMomentExact

#print axioms ProximityGap.Frontier.SecondMomentExact.rEnergy_one
#print axioms ProximityGap.Frontier.SecondMomentExact.sum_nonzero_sq
#print axioms ProximityGap.Frontier.SecondMomentExact.base_case_strict
