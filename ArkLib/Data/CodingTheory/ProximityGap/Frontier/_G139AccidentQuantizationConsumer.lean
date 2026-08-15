/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136ProductionInstantiation

/-!
# G139: quantized rung-2 accidents collapse the G136 tolerance to zero

G136 proved that the production rung-2 anchor is equivalent to **at most three** normalized
accidents.  The fresh G139 fiber analysis isolates the missing arithmetic shape: after quotienting
by the inversion symmetry `t ~ t⁻¹`, every non-lawful value collision contributes accidents in
blocks of four.  Therefore the G136 tolerance `A ≤ 3` has no slack: under the quantization
hypothesis `4 ∣ A`, it is exactly `A = 0`.

This file formalizes the axiom-clean consumer, not the still-open certified-prime collision count.
It includes the orbit-fiber arithmetic responsible for the modulus-four phenomenon and then wires
that invariant into the already-landed G136 production capstone.

Honest scope: `4 ∣ #accidents` is an input here.  Proving it for the concrete map
`t ↦ (1+t)^(2^30)` on `μ_(2^30) \ {-1}` is the next G139 formal target.  CORE remains open.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false

namespace ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer

open Finset
open ArkLib.ProximityGap.Frontier.G136LawfulCount
open ArkLib.ProximityGap.Frontier.G136ProductionInstantiation

/-- A regular inversion fiber with `c` two-point classes contributes its excess in blocks of
four: `4c² - 4c = 4c(c-1)`.  This is the local arithmetic behind G139's accident
quantization. -/
def regularFiberExcess (c : ℕ) : ℕ := 4 * c * (c - 1)

/-- The distinguished fiber containing the singleton class `{1}` and `c` regular two-point
classes contributes `(1+2c)² - (1+4c) = 4c²`, again a multiple of four. -/
def distinguishedFiberExcess (c : ℕ) : ℕ := 4 * c ^ 2

/-- The G139 fiber ledger is automatically quantized: one distinguished fiber plus any finite
family of regular inversion fibers has total excess divisible by four. -/
theorem four_dvd_fiber_excess_sum {ι : Type*} [Fintype ι]
    (c0 : ℕ) (c : ι → ℕ) :
    4 ∣ distinguishedFiberExcess c0 + ∑ i, regularFiberExcess (c i) := by
  refine ⟨c0 ^ 2 + ∑ i, c i * (c i - 1), ?_⟩
  simp only [distinguishedFiberExcess, regularFiberExcess, Nat.mul_add,
    Finset.mul_sum]
  simp [Nat.mul_assoc]

/-- A modulus-four accident count has no positive values below four.  Hence G136's
`≤ 3` tolerance is equivalent to accident-freeness once the G139 quantization invariant is
available. -/
theorem le_three_iff_eq_zero_of_four_dvd {A : ℕ} (hA : 4 ∣ A) :
    A ≤ 3 ↔ A = 0 := by
  constructor
  · intro hle
    rcases hA with ⟨k, rfl⟩
    cases k with
    | zero => simp
    | succ k => omega
  · intro h
    rw [h]
    norm_num

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **G139 consumer, abstract subgroup form.**  If the normalized accident count is quantized
in blocks of four, then the G136 production rung-2 anchor is equivalent to zero accidents, not
merely at most three. -/
theorem rung2_anchor_iff_no_accidents_of_four_dvd (H : Finset F) {q : ℕ}
    (hq : 2 ^ 90 < q)
    (hcard : H.card = 2 ^ 30)
    (h1 : (1 : F) ∈ H) (hneg : ∀ x ∈ H, -x ∈ H) (h0 : (0 : F) ∉ H)
    (h2 : (2 : F) ≠ 0)
    (hmul : ∀ x ∈ H, ∀ u ∈ H, x * u ∈ H) (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (hquant : 4 ∣ (accidents H).card) :
    q * Finset.addREnergy 2 H ≤ 3 * q * (2 ^ 30) ^ 2 + (2 ^ 30) ^ 4
      ↔ (accidents H).card = 0 := by
  rw [rung2_anchor_iff_accidents H hq hcard h1 hneg h0 h2 hmul hinv]
  exact le_three_iff_eq_zero_of_four_dvd hquant

/-- **G139 consumer, concrete production roots-of-unity form.**  For the production subgroup
`μ_(2^30)`, a modulus-four accident theorem would sharpen the already-landed G136 equivalence
from `#accidents ≤ 3` to `#accidents = 0`. -/
theorem production_rung2_anchor_iff_no_accidents_of_four_dvd
    {ω : F} (hω : IsPrimitiveRoot ω (2 ^ 30))
    (hq : 2 ^ 90 < Fintype.card F) (h2 : (2 : F) ≠ 0)
    (hquant : 4 ∣ (accidents (rootsFinset ω (2 ^ 30))).card) :
    Fintype.card F * Finset.addREnergy 2 (rootsFinset ω (2 ^ 30))
        ≤ 3 * Fintype.card F * (2 ^ 30) ^ 2 + (2 ^ 30) ^ 4
      ↔ (accidents (rootsFinset ω (2 ^ 30))).card = 0 := by
  rw [production_rung2_anchor_iff_accidents hω hq h2]
  exact le_three_iff_eq_zero_of_four_dvd hquant

end ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer.four_dvd_fiber_excess_sum
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer.rung2_anchor_iff_no_accidents_of_four_dvd
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer.production_rung2_anchor_iff_no_accidents_of_four_dvd
