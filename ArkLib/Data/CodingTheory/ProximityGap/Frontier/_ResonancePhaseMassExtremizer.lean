/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseMassFloor

/-!
# The constant vector MAXIMIZES the phase-mass floor (door-(iv), Lane 2/3 capstone)

The universal phase-mass floor (`resonanceMoment_ge_phaseMass_pow_div_card`) bounds the resonance
moment below by `‖S‖^{2r}/m`, `S = ∑_{a≠0} u a`.  This file closes the loop: among **unit-modulus**
phase vectors (`‖u a‖ = 1`, the Gauss-sum normalization), the phase mass is bounded `‖S‖ ≤ m-1` by the
triangle inequality, with the bound **attained exactly at the constant vector** `u ≡ 1` (`S = m-1`).

Consequently the phase-mass floor `‖S‖^{2r}/m` is *maximized at `u ≡ 1`*, value `(m-1)^{2r}/m`.  This is
the precise sense in which the DC-coherent vector is the extremizer of the entire phase-mass lower-bound
family — the unifying capstone over `_ResonanceConstantVectorCeiling` (ceiling order-attained at `u≡1`)
and `_ResonancePhaseMassFloor` (universal floor via `‖S‖`).  The structural message for door-(iv): the
ONLY way the phase-mass floor stays large is maximal phase coherence (all phases equal); genuine
multiplicative Gauss phases force `‖S‖ ≪ m-1`, and the prize regime lives in that cancellation gap which
the scalar phase mass cannot resolve.

Self-contained leaf over `_ResonancePhaseMassFloor`.  Axiom-clean (`{propext, Classical.choice,
Quot.sound}`).  No CORE / cancellation / completion / moment / anti-concentration / capacity claim.
Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The nonzero-residue index set is `(univ.filter (· ≠ 0))` and has card `m-1`.** -/
theorem card_nonzero_filter :
    ((Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card) = m - 1 := by
  classical
  rw [Finset.filter_ne']
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- **Unit-modulus ⟹ the phase mass is triangle-bounded by `m-1`.**
If `‖u a‖ = 1` for every nonzero `a`, then `‖S‖ = ‖∑_{a≠0} u a‖ ≤ m-1`. -/
theorem norm_phaseMass_le_of_unit (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, a ≠ 0 → ‖u a‖ = 1) :
    ‖phaseMass u‖ ≤ (m - 1 : ℕ) := by
  classical
  unfold phaseMass
  calc ‖∑ a ∈ (Finset.univ.filter (fun a : ZMod m => a ≠ 0)), u a‖
      ≤ ∑ a ∈ (Finset.univ.filter (fun a : ZMod m => a ≠ 0)), ‖u a‖ := norm_sum_le _ _
    _ = ∑ _a ∈ (Finset.univ.filter (fun a : ZMod m => a ≠ 0)), (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        exact hu a (by simpa using (Finset.mem_filter.mp ha).2)
    _ = ((Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (m - 1 : ℕ) := by rw [card_nonzero_filter]

/-- **The constant vector `u ≡ 1` attains the phase-mass triangle bound.**
`‖phaseMass (fun _ => 1)‖ = m-1`. -/
theorem norm_phaseMass_const_one :
    ‖phaseMass (fun _ : ZMod m => (1 : ℂ))‖ = (m - 1 : ℕ) := by
  classical
  unfold phaseMass
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_nonzero_filter, Complex.norm_natCast]

/-- **The phase-mass floor is MAXIMIZED at the constant vector (among unit-modulus phases).**
For unit-modulus `u`, the phase-mass lower bound `‖S‖^{2r}/m` never exceeds the constant-vector value
`(m-1)^{2r}/m`; equivalently `‖phaseMass u‖^{2r} ≤ ‖phaseMass (fun _ => 1)‖^{2r}`.  Combined with the
universal floor (`resonanceMoment_ge_phaseMass_pow_div_card`), this identifies `u ≡ 1` as the extremizer
of the entire phase-mass lower-bound family. -/
theorem phaseMass_pow_le_const_one_of_unit (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, a ≠ 0 → ‖u a‖ = 1) (r : ℕ) :
    ‖phaseMass u‖ ^ (2 * r) ≤ ‖phaseMass (fun _ : ZMod m => (1 : ℂ))‖ ^ (2 * r) := by
  have h1 : ‖phaseMass u‖ ≤ ‖phaseMass (fun _ : ZMod m => (1 : ℂ))‖ := by
    rw [norm_phaseMass_const_one]; exact norm_phaseMass_le_of_unit u hu
  exact pow_le_pow_left₀ (norm_nonneg _) h1 (2 * r)

/-- **Packaged extremizer capstone (door-(iv)).**  Among unit-modulus phase vectors the phase mass is
triangle-bounded by `m-1`, attained at `u ≡ 1`, so the universal phase-mass floor `‖S‖^{2r}/m` is
maximized exactly at the constant vector.  The phase-mass lower bound stays large ONLY under maximal
phase coherence; the prize √-cancellation regime lives in the gap `‖S‖ ≪ m-1` that the scalar phase mass
cannot resolve.  No CORE / cancellation / completion / moment / anti-concentration / capacity claim. -/
theorem const_one_maximizes_phaseMass_floor (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, a ≠ 0 → ‖u a‖ = 1) (r : ℕ) :
    ‖phaseMass u‖ ≤ (m - 1 : ℕ)
      ∧ ‖phaseMass (fun _ : ZMod m => (1 : ℂ))‖ = (m - 1 : ℕ)
      ∧ ‖phaseMass u‖ ^ (2 * r) ≤ ‖phaseMass (fun _ : ZMod m => (1 : ℂ))‖ ^ (2 * r) :=
  ⟨norm_phaseMass_le_of_unit u hu, norm_phaseMass_const_one,
    phaseMass_pow_le_const_one_of_unit u hu r⟩

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_phaseMass_le_of_unit
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.norm_phaseMass_const_one
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseMass_pow_le_const_one_of_unit
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.const_one_maximizes_phaseMass_floor
