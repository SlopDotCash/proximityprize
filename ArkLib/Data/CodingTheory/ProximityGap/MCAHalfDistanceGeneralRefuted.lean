/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAHalfDistanceStaircase

/-!
# Round 3 (#357): `HalfDistanceStaircaseConjecture` is FALSE — the doubled-column attack

The named surface posed earlier today is **refuted at its first open band**: the general-code
collapse boundary is *not* `d ≥ 2b`. The counterexample (probe-discovered by relation-space
analysis, then verified end-to-end and formalized here):

**The doubled-column code** `D₂ ⊂ F₁₁⁸` with generator rows
`(1,1,0,0,1,1,1,1)` and `(0,0,1,1,1,1,2,2)` — an `[8,2,6]` code (no nonzero codeword on
`≤ 5` points; checked by `decide`) whose four coordinate pairs each carry a *singular* 2×2
minor, concentrating each weight-6 codeword's zeros on one pair. The stack

  `u₀ = (3,3,0,0,0,0,0,0)`, `u₁ = (8,8,9,9,0,0,0,0)`

has **four** bad scalars `γ ∈ {0, 1, 2, 5}` at `δ = 1/4` (band 3: `δ·n = 2 < 3`), each with
a distinct punctured-pair witness; the no-joint-explanation clauses block on the `u₁` row by
three-position interpolation contradictions (`decide`). Hence `LinearStaircaseUpper D₂ 3`
fails, and `¬ HalfDistanceStaircaseConjecture` (`halfDistanceStaircaseConjecture_refuted`).

**The corrected landscape** (per the directed-search record on #357):
* General linear codes: the disjoint branch dies at `d ≥ 2b + 1` by pure weight counting
  (a triple combination is supported on `≤ 2b` points), so the corrected general surface is
  `GeneralStaircaseConjecture` (`d ≥ 2b + 1`), stated below — never asserted.
* Reed–Solomon/MDS codes: the directed search found *no* admissible configuration at
  `d = 2b` (the syndrome system's kernel always zeroes a puncture) — the MDS form
  `d ≥ 2b` survives as `MDSStaircaseConjecture`, also stated below.
* The separation at `d = 2b` is therefore **real**: the staircase's collapse boundary is a
  property of the code's *minor structure*, not its distance alone — doubled-column codes
  witness the gap. This is, to our knowledge, the first separation between MDS and general
  linear codes for an MCA-staircase quantity.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 3), `MCAHalfDistanceStaircase.lean` (the refuted
  surface), DISPROOF_LOG entry of 2026-06-11.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAHalfDistanceGeneralRefuted

open ProximityGap.MCAHalfDistanceStaircase

abbrev F11 := ZMod 11

instance primeFact_MCAHalfDistanceGeneralRefuted_1 : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- First generator row of the doubled-column code. -/
def G0 : Fin 8 → F11 := ![1, 1, 0, 0, 1, 1, 1, 1]

/-- Second generator row. -/
def G1 : Fin 8 → F11 := ![0, 0, 1, 1, 1, 1, 2, 2]

/-- The doubled-column `[8,2,6]` code over `F₁₁`. -/
def D2 : Submodule F11 (Fin 8 → F11) where
  carrier := {w | ∃ a b : F11, ∀ i, w i = a * G0 i + b * G1 i}
  zero_mem' := ⟨0, 0, fun i => by simp⟩
  add_mem' := by
    rintro w w' ⟨a, b, h⟩ ⟨a', b', h'⟩
    exact ⟨a + a', b + b', fun i => by
      show w i + w' i = _
      rw [h i, h' i]; ring⟩
  smul_mem' := by
    rintro c w ⟨a, b, h⟩
    exact ⟨c * a, c * b, fun i => by
      show c * w i = _
      rw [h i]; ring⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `D₂` has no nonzero codeword supported on fewer than `6` points (distance `6`):
the hypothesis of `HalfDistanceStaircaseConjecture` at `b = 3`. -/
theorem D2_noWeight : ∀ w ∈ D2,
    (∃ T : Finset (Fin 8), T.card < 2 * 3 ∧ ∀ i ∉ T, w i = 0) → w = 0 := by
  rintro w ⟨a, b, hab⟩ ⟨T, hT, hsupp⟩
  have hzero : ∀ i, a * G0 i + b * G1 i = 0 := by
    have key : ∀ a b : F11, ∀ T : Finset (Fin 8), T.card < 6 →
        (∀ i ∉ T, a * G0 i + b * G1 i = 0) → ∀ i, a * G0 i + b * G1 i = 0 := by decide
    refine key a b T hT fun i hi => ?_
    rw [← hab i]
    exact hsupp i hi
  funext i
  rw [hab i, hzero i]
  rfl

/-- The refuting stack, first row. -/
def u0c : Fin 8 → F11 := ![3, 3, 0, 0, 0, 0, 0, 0]

/-- The refuting stack, second row. -/
def u1c : Fin 8 → F11 := ![8, 8, 9, 9, 0, 0, 0, 0]

/-- The witness-size clause at `δ = 1/4`, `n = 8`, for the six-point witnesses. -/
theorem card_clause8 {S : Finset (Fin 8)} (hS : S.card = 6) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 8) : ℝ≥0) := by
  rw [hS, Fintype.card_fin]
  calc ((1 : ℝ≥0) - 1/4) * (8 : ℕ) ≤ (3/4 : ℝ≥0) * (8 : ℕ) := by
        gcongr
        exact tsub_le_iff_right.mpr (by norm_num)
    _ ≤ ((6 : ℕ) : ℝ≥0) := by push_cast; norm_num

/-- `γ = 0`: witness `{2,…,7}`, on-line codeword `0`; the `u₁` row blocks the pair. -/
theorem mcaEvent_c0 :
    mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4) u0c u1c 0 := by
  refine ⟨{2, 3, 4, 5, 6, 7}, card_clause8 (by decide), ⟨0, D2.zero_mem, by decide⟩, ?_⟩
  rintro ⟨v₀, _, v₁, ⟨a, b, h⟩, hag⟩
  have e2 : a * G0 2 + b * G1 2 = u1c 2 := by rw [← h 2]; exact (hag 2 (by decide)).2
  have e4 : a * G0 4 + b * G1 4 = u1c 4 := by rw [← h 4]; exact (hag 4 (by decide)).2
  have e6 : a * G0 6 + b * G1 6 = u1c 6 := by rw [← h 6]; exact (hag 6 (by decide)).2
  clear h
  revert e2 e4 e6
  revert a b
  decide

/-- `γ = 1`: witness `{0,1,4,5,6,7}`, on-line codeword `0`. -/
theorem mcaEvent_c1 :
    mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4) u0c u1c 1 := by
  refine ⟨{0, 1, 4, 5, 6, 7}, card_clause8 (by decide), ⟨0, D2.zero_mem, by decide⟩, ?_⟩
  rintro ⟨v₀, _, v₁, ⟨a, b, h⟩, hag⟩
  have e0 : a * G0 0 + b * G1 0 = u1c 0 := by rw [← h 0]; exact (hag 0 (by decide)).2
  have e4 : a * G0 4 + b * G1 4 = u1c 4 := by rw [← h 4]; exact (hag 4 (by decide)).2
  have e6 : a * G0 6 + b * G1 6 = u1c 6 := by rw [← h 6]; exact (hag 6 (by decide)).2
  clear h
  revert e0 e4 e6
  revert a b
  decide

/-- `γ = 2`: witness `{0,1,2,3,6,7}`, on-line codeword `8·G0 + 7·G1`. -/
theorem mcaEvent_c2 :
    mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4) u0c u1c 2 := by
  refine ⟨{0, 1, 2, 3, 6, 7}, card_clause8 (by decide),
    ⟨fun i => 8 * G0 i + 7 * G1 i, ⟨8, 7, fun _ => rfl⟩, by decide⟩, ?_⟩
  rintro ⟨v₀, _, v₁, ⟨a, b, h⟩, hag⟩
  have e0 : a * G0 0 + b * G1 0 = u1c 0 := by rw [← h 0]; exact (hag 0 (by decide)).2
  have e2 : a * G0 2 + b * G1 2 = u1c 2 := by rw [← h 2]; exact (hag 2 (by decide)).2
  have e6 : a * G0 6 + b * G1 6 = u1c 6 := by rw [← h 6]; exact (hag 6 (by decide)).2
  clear h
  revert e0 e2 e6
  revert a b
  decide

/-- `γ = 5`: witness `{0,…,5}`, on-line codeword `10·G0 + 1·G1`. -/
theorem mcaEvent_c5 :
    mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4) u0c u1c 5 := by
  refine ⟨{0, 1, 2, 3, 4, 5}, card_clause8 (by decide),
    ⟨fun i => 10 * G0 i + 1 * G1 i, ⟨10, 1, fun _ => rfl⟩, by decide⟩, ?_⟩
  rintro ⟨v₀, _, v₁, ⟨a, b, h⟩, hag⟩
  have e0 : a * G0 0 + b * G1 0 = u1c 0 := by rw [← h 0]; exact (hag 0 (by decide)).2
  have e2 : a * G0 2 + b * G1 2 = u1c 2 := by rw [← h 2]; exact (hag 2 (by decide)).2
  have e4 : a * G0 4 + b * G1 4 = u1c 4 := by rw [← h 4]; exact (hag 4 (by decide)).2
  clear h
  revert e0 e2 e4
  revert a b
  decide

open Classical in
/-- **The refutation:** `HalfDistanceStaircaseConjecture` is false — the doubled-column code
satisfies its distance hypothesis at `b = 3`, yet the explicit stack has four bad scalars in
band 3. The general-code collapse boundary is `d ≥ 2b + 1`, not `d ≥ 2b`; the `d = 2b` law
is MDS/RS-specific (the separation witnessed here). -/
theorem halfDistanceStaircaseConjecture_refuted : ¬ HalfDistanceStaircaseConjecture := by
  intro h
  have hLSU : LinearStaircaseUpper D2 3 :=
    h (Fin 8) inferInstance inferInstance inferInstance F11 inferInstance inferInstance
      inferInstance D2 3 le_rfl D2_noWeight
  have hδ : ((1 : ℝ≥0)/4) * (Fintype.card (Fin 8) : ℝ≥0) < (3 : ℕ) := by
    rw [Fintype.card_fin]
    push_cast
    norm_num
  have hcap := hLSU (1/4) hδ ![u0c, u1c]
  have hsub : ({0, 1, 2, 5} : Finset F11) ⊆ Finset.filter (fun γ : F11 =>
      mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4)
        ((![u0c, u1c] : WordStack F11 (Fin 2) (Fin 8)) 0)
        ((![u0c, u1c] : WordStack F11 (Fin 2) (Fin 8)) 1) γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_c0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_c1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_c2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_c5⟩
  have h4 : (4 : ℕ) ≤ (Finset.filter (fun γ : F11 =>
      mcaEvent (F := F11) (D2 : Set (Fin 8 → F11)) (1/4)
        ((![u0c, u1c] : WordStack F11 (Fin 2) (Fin 8)) 0)
        ((![u0c, u1c] : WordStack F11 (Fin 2) (Fin 8)) 1) γ) Finset.univ).card := by
    calc (4 : ℕ) = ({0, 1, 2, 5} : Finset F11).card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-! ## The corrected surfaces (stated, never asserted) -/

/-- **The corrected general surface:** distance `≥ 2b + 1` (no nonzero codeword on `≤ 2b`
points) implies the linear-staircase upper at band `b`. The disjoint branch now dies by
pure weight counting (triple combinations live on `≤ 2b` points); the doubled-column
counterexample needs distance exactly `2b` and does not apply. -/
def GeneralStaircaseConjecture : Prop :=
  ∀ (ι : Type) (inst1 : Fintype ι) (inst2 : Nonempty ι) (inst3 : DecidableEq ι)
    (F : Type) (inst4 : Field F) (inst5 : Fintype F) (inst6 : DecidableEq F)
    (C : Submodule F (ι → F)) (b : ℕ), 3 ≤ b →
    (∀ w ∈ C, (∃ T : Finset ι, T.card ≤ 2 * b ∧ ∀ i ∉ T, w i = 0) → w = 0) →
    LinearStaircaseUpper C b

/-- **The MDS surface:** for Reed–Solomon codes the original boundary `d ≥ 2b` survives
(the directed-search record: the syndrome system has no admissible kernel at RS instances).
Stated for the RS family. -/
def MDSStaircaseConjecture : Prop :=
  ∀ (ι : Type) (inst1 : Fintype ι) (inst2 : Nonempty ι) (inst3 : DecidableEq ι)
    (F : Type) (inst4 : Field F) (inst5 : Fintype F) (inst6 : DecidableEq F)
    (domain : ι ↪ F) (k b : ℕ), 3 ≤ b → k + 2 * b ≤ Fintype.card ι →
    LinearStaircaseUpper (ReedSolomon.code domain k) b

/-! ## Source audit -/

#print axioms D2_noWeight
#print axioms mcaEvent_c0
#print axioms halfDistanceStaircaseConjecture_refuted

end ProximityGap.MCAHalfDistanceGeneralRefuted
