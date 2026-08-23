/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AffineBlockKernels

/-!
# The A3 sharpness instance: definitions and subset kernels (issue #334, assembly stage 1)

The cancellation-pair instance whose Lemma-4.1 obstructions defeat every `UniformObstruction`
cover (the solved construction, issue #334 comment thread): positions `Option F × F`
(`q+1` blocks of size `q`), repetition base code, and per block `b` the stack pair

  `U_{b,1} = (j, val b · j)·𝟙_b`,  `U_{b,2} = (−j, −val b · j + 1)·𝟙_b`

(`val (some c) = c`, `val none = 0` with the first component zeroed — the vertical block),
whose seed-`b` combination is `(0, 1)·𝟙_b` (block-constant, nonzero — witness-forcing for
*every* seed) and whose `λ`-kernels carve exactly the `q+1` projective lines.

This stage: the instance definitions and the **subset constancy kernels** (the `|T| ≥ 2`
extensions of `AffineBlockKernels`' full-block lemmas — what `jointStackSubmodule` at a
single-block witness set actually consumes). The badness/forcing/escape legs are stage 2.
-/

namespace ProximityGap

variable {F : Type} [Field F] [DecidableEq F]

/-- Constancy of the affine combination on a subset: for any `T` with two distinct points,
`(λ₁ + c·λ₂)·j` is constant on `T` iff `λ₁ + c·λ₂ = 0`. (Subset version of
`affineBlockCombo_constant_iff`.) -/
theorem affineBlockCombo_constantOn_iff (c : F) (lam : Fin 2 → F)
    {T : Set F} {j₀ j₁ : F} (h0 : j₀ ∈ T) (h1 : j₁ ∈ T) (hne : j₀ ≠ j₁) :
    (∃ b : F, ∀ j ∈ T, affineBlockCombo c lam j = b) ↔ lam 0 + c * lam 1 = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have e0 := hb j₀ h0
    have e1 := hb j₁ h1
    have : (lam 0 + c * lam 1) * (j₀ - j₁) = 0 := by
      unfold affineBlockCombo at e0 e1
      linear_combination e0 - e1
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  · intro h
    refine ⟨0, fun j _ => ?_⟩
    calc affineBlockCombo c lam j = (lam 0 + c * lam 1) * j := by
          unfold affineBlockCombo; ring
    _ = 0 := by rw [h]; ring

/-- Subset constancy for the second pair-row pattern `−(λ₁ + c·λ₂)·j + λ₂`: same kernel. -/
theorem pairRowTwoCombo_constantOn_iff (c : F) (lam : Fin 2 → F)
    {T : Set F} {j₀ j₁ : F} (h0 : j₀ ∈ T) (h1 : j₁ ∈ T) (hne : j₀ ≠ j₁) :
    (∃ b : F, ∀ j ∈ T, lam 0 * (-j) + lam 1 * (-(c * j) + 1) = b)
      ↔ lam 0 + c * lam 1 = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have e0 := hb j₀ h0
    have e1 := hb j₁ h1
    have : (lam 0 + c * lam 1) * (j₀ - j₁) = 0 := by linear_combination e1 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  · intro h
    refine ⟨lam 1, fun j _ => ?_⟩
    have : (lam 0 + c * lam 1) * j = 0 := by rw [h]; ring
    linear_combination -this

/-! ## The instance data -/

variable (F) in
/-- Position space: `q+1` blocks (indexed by `Option F` — `some c` affine, `none` vertical),
each of size `q`. -/
abbrev A3Pos := Option F × F

/-- The block label's slope: `some c ↦ c`, `none ↦ 0` (the vertical block instead zeroes the
first row component). -/
def blockSlope : Option F → F
  | none => 0
  | some c => c

/-- First-component selector: `1` on affine blocks, `0` on the vertical block (which carves
`λ₂ = 0` through its second component instead). -/
def blockFirst : Option F → F
  | none => 0
  | some _ => 1

/-- **The stack** (`2(q+1)` rows, indexed by block × pair-position): row `(b, 0)` is
`(blockFirst b · j, blockSlope b · j)` on block `b` (zero elsewhere, as an interleaved
`Fin 2`-pair extended by the vertical second component `j` on the `none` block); row `(b, 1)`
is the cancellation partner `(−·, −· + 1)`. Stated as a single function. -/
def a3Stack : (Option F × Fin 2) → A3Pos F → Fin 2 → F :=
  fun br pos k =>
    let b := br.1; let r := br.2
    if pos.1 = b then
      let j := pos.2
      -- the underlying scalar pattern of component k at position j
      let first : F := if b = none then 0 else j     -- component 0 pattern
      let second : F := if b = none then j else blockSlope b * j  -- component 1 pattern
      if r = 0 then (if k = 0 then first else second)
      else (if k = 0 then -first else -second + 1)
    else 0

/-- The seed family: `Ω = Option F`; seed `b` selects block `b`'s cancellation pair with
coefficient `1` each. -/
def a3Gen : Option F → (Option F × Fin 2) → F :=
  fun b br => if br.1 = b then 1 else 0

/-- **The seed combination collapses to the block indicator**: `∑_r (a3Gen b) r • a3Stack r`
is `(0, 1)` on block `b` and `0` elsewhere — block-constant rows, nonzero on the block (the
witness-forcing currency). -/
theorem a3_combination [Fintype F] (b : Option F) (pos : A3Pos F) (k : Fin 2) :
    (∑ br : Option F × Fin 2, a3Gen b br • a3Stack (F := F) br pos k)
      = if pos.1 = b then (if k = 0 then 0 else 1) else 0 := by
  classical
  -- Only block-b rows contribute (a3Gen vanishes elsewhere).
  rw [show (∑ br : Option F × Fin 2, a3Gen b br • a3Stack (F := F) br pos k)
      = ∑ r : Fin 2, a3Stack (F := F) (b, r) pos k from by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · exact Finset.sum_congr rfl fun r _ => by simp [a3Gen]
    · intro b' _ hb'
      refine Finset.sum_eq_zero fun r _ => ?_
      simp [a3Gen, hb']
    · intro h
      exact absurd (Finset.mem_univ b) h]
  rw [Fin.sum_univ_two]
  unfold a3Stack
  by_cases hpos : pos.1 = b
  · rw [if_pos hpos, if_pos hpos, if_pos hpos]
    simp only [show ((0 : Fin 2) = 0) = True from by simp, if_true,
      show ((1 : Fin 2) = 0) = False from by simp, if_false]
    fin_cases k <;> by_cases hb : b = none <;> simp [hb] <;> ring
  · rw [if_neg hpos, if_neg hpos, if_neg hpos]
    simp

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.affineBlockCombo_constantOn_iff
#print axioms ProximityGap.pairRowTwoCombo_constantOn_iff
#print axioms ProximityGap.a3_combination
