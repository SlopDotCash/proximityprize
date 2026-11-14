/-
  Local reconstruction for ArkLib #357.

  This is kept under `scripts/probes/lean/`: it is a compile-checkable witness
  for the DISPROOF_LOG F_101 boundary note, not yet integrated into ArkLib's tracked API.
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAHalfDistanceStaircase
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace NubsResearch.F101Band3BoundaryWitness

abbrev F101 := ZMod 101

instance : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Eight distinct evaluation points, normalized as `0,1,...,7`. -/
def dom : Fin 8 → F101 := ![0, 1, 2, 3, 4, 5, 6, 7]

/-- The concrete degree-`<4` Reed-Solomon code on `dom`. -/
def C101 : Submodule F101 (Fin 8 → F101) where
  carrier := {w | ∃ a0 a1 a2 a3 : F101,
    ∀ i, w i = a0 + a1 * dom i + a2 * dom i ^ 2 + a3 * dom i ^ 3}
  zero_mem' := ⟨0, 0, 0, 0, by simp⟩
  add_mem' := by
    rintro w w' ⟨a0, a1, a2, a3, hw⟩ ⟨b0, b1, b2, b3, hw'⟩
    refine ⟨a0 + b0, a1 + b1, a2 + b2, a3 + b3, ?_⟩
    intro i
    show w i + w' i =
      a0 + b0 + (a1 + b1) * dom i + (a2 + b2) * dom i ^ 2 +
        (a3 + b3) * dom i ^ 3
    rw [hw i, hw' i]
    ring
  smul_mem' := by
    rintro c w ⟨a0, a1, a2, a3, hw⟩
    refine ⟨c * a0, c * a1, c * a2, c * a3, ?_⟩
    intro i
    show c * w i = c * a0 + c * a1 * dom i + c * a2 * dom i ^ 2 +
      c * a3 * dom i ^ 3
    rw [hw i]
    ring

/-- Degree-3 membership helper. -/
theorem deg3_mem (a0 a1 a2 a3 : F101) :
    (fun i => a0 + a1 * dom i + a2 * dom i ^ 2 + a3 * dom i ^ 3) ∈ C101 :=
  ⟨a0, a1, a2, a3, fun _ => rfl⟩

/-- First row of the reconstructed stack. -/
def u0 : Fin 8 → F101 := ![0, 0, 0, 0, 58, 71, 37, 55]

/-- Second row of the reconstructed stack. -/
def u1 : Fin 8 → F101 := ![0, 0, 0, 0, 87, 56, 32, 23]

/-- The witness-size clause at `δ = 1/4`, `n = 8`. -/
theorem card_clause6 {S : Finset (Fin 8)} (hS : S.card = 6) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 8) : ℝ≥0) := by
  rw [hS, Fintype.card_fin]
  calc ((1 : ℝ≥0) - 1/4) * (8 : ℕ) ≤ (3/4 : ℝ≥0) * (8 : ℕ) := by
        gcongr
        exact tsub_le_iff_right.mpr (by norm_num)
    _ ≤ ((6 : ℕ) : ℝ≥0) := by push_cast; norm_num

/-! ## No-joint-explanation certificates -/

theorem no_joint0 :
    ¬ pairJointAgreesOn (C101 : Set (Fin 8 → F101)) {2, 3, 4, 5, 6, 7} u0 u1 := by
  rintro ⟨_, _, v1, ⟨a0, a1, a2, a3, hv1⟩, hag⟩
  have e2 : a0 + a1 * dom 2 + a2 * dom 2 ^ 2 + a3 * dom 2 ^ 3 = u1 2 := by
    rw [← hv1 2]; exact (hag 2 (by decide)).2
  have e3 : a0 + a1 * dom 3 + a2 * dom 3 ^ 2 + a3 * dom 3 ^ 3 = u1 3 := by
    rw [← hv1 3]; exact (hag 3 (by decide)).2
  have e4 : a0 + a1 * dom 4 + a2 * dom 4 ^ 2 + a3 * dom 4 ^ 3 = u1 4 := by
    rw [← hv1 4]; exact (hag 4 (by decide)).2
  have e5 : a0 + a1 * dom 5 + a2 * dom 5 ^ 2 + a3 * dom 5 ^ 3 = u1 5 := by
    rw [← hv1 5]; exact (hag 5 (by decide)).2
  have e6 : a0 + a1 * dom 6 + a2 * dom 6 ^ 2 + a3 * dom 6 ^ 3 = u1 6 := by
    rw [← hv1 6]; exact (hag 6 (by decide)).2
  have e2n : a0 + a1 * (2 : F101) + a2 * (2 : F101) ^ 2 + a3 * (2 : F101) ^ 3 = 0 := by
    simpa [dom, u1] using e2
  have e3n : a0 + a1 * (3 : F101) + a2 * (3 : F101) ^ 2 + a3 * (3 : F101) ^ 3 = 0 := by
    simpa [dom, u1] using e3
  have e4n : a0 + a1 * (4 : F101) + a2 * (4 : F101) ^ 2 + a3 * (4 : F101) ^ 3 = 87 := by
    simpa [dom, u1] using e4
  have e5n : a0 + a1 * (5 : F101) + a2 * (5 : F101) ^ 2 + a3 * (5 : F101) ^ 3 = 56 := by
    simpa [dom, u1] using e5
  have e6n : a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3 = 32 := by
    simpa [dom, u1] using e6
  clear hv1 hag
  have bad : (0 : F101) = 27 := by
    let L2 : F101 := a0 + a1 * (2 : F101) + a2 * (2 : F101) ^ 2 + a3 * (2 : F101) ^ 3
    let L3 : F101 := a0 + a1 * (3 : F101) + a2 * (3 : F101) ^ 2 + a3 * (3 : F101) ^ 3
    let L4 : F101 := a0 + a1 * (4 : F101) + a2 * (4 : F101) ^ 2 + a3 * (4 : F101) ^ 3
    let L5 : F101 := a0 + a1 * (5 : F101) + a2 * (5 : F101) ^ 2 + a3 * (5 : F101) ^ 3
    let L6 : F101 := a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3
    have hzero : L2 - 4 * L3 + 6 * L4 - 4 * L5 + L6 = 0 := by
      dsimp [L2, L3, L4, L5, L6]
      ring
    have hrhs : L2 - 4 * L3 + 6 * L4 - 4 * L5 + L6 = 27 := by
      dsimp [L2, L3, L4, L5, L6]
      rw [e2n, e3n, e4n, e5n, e6n]
      decide
    rw [← hzero]
    exact hrhs
  exact (by decide : ¬ ((0 : F101) = 27)) bad

theorem no_joint1 :
    ¬ pairJointAgreesOn (C101 : Set (Fin 8 → F101)) {0, 1, 4, 5, 6, 7} u0 u1 := by
  rintro ⟨v0, ⟨a0, a1, a2, a3, hv0⟩, _, _, hag⟩
  have e0 : a0 + a1 * dom 0 + a2 * dom 0 ^ 2 + a3 * dom 0 ^ 3 = u0 0 := by
    rw [← hv0 0]; exact (hag 0 (by decide)).1
  have e1 : a0 + a1 * dom 1 + a2 * dom 1 ^ 2 + a3 * dom 1 ^ 3 = u0 1 := by
    rw [← hv0 1]; exact (hag 1 (by decide)).1
  have e4 : a0 + a1 * dom 4 + a2 * dom 4 ^ 2 + a3 * dom 4 ^ 3 = u0 4 := by
    rw [← hv0 4]; exact (hag 4 (by decide)).1
  have e5 : a0 + a1 * dom 5 + a2 * dom 5 ^ 2 + a3 * dom 5 ^ 3 = u0 5 := by
    rw [← hv0 5]; exact (hag 5 (by decide)).1
  have e6 : a0 + a1 * dom 6 + a2 * dom 6 ^ 2 + a3 * dom 6 ^ 3 = u0 6 := by
    rw [← hv0 6]; exact (hag 6 (by decide)).1
  have e0n : a0 + a1 * (0 : F101) + a2 * (0 : F101) ^ 2 + a3 * (0 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e0
  have e1n : a0 + a1 * (1 : F101) + a2 * (1 : F101) ^ 2 + a3 * (1 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e1
  have e4n : a0 + a1 * (4 : F101) + a2 * (4 : F101) ^ 2 + a3 * (4 : F101) ^ 3 = 58 := by
    simpa [dom, u0] using e4
  have e5n : a0 + a1 * (5 : F101) + a2 * (5 : F101) ^ 2 + a3 * (5 : F101) ^ 3 = 71 := by
    simpa [dom, u0] using e5
  have e6n : a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3 = 37 := by
    simpa [dom, u0] using e6
  clear v0 hv0 hag
  have bad : (0 : F101) = 70 := by
    let L0 : F101 := a0 + a1 * (0 : F101) + a2 * (0 : F101) ^ 2 + a3 * (0 : F101) ^ 3
    let L1 : F101 := a0 + a1 * (1 : F101) + a2 * (1 : F101) ^ 2 + a3 * (1 : F101) ^ 3
    let L4 : F101 := a0 + a1 * (4 : F101) + a2 * (4 : F101) ^ 2 + a3 * (4 : F101) ^ 3
    let L5 : F101 := a0 + a1 * (5 : F101) + a2 * (5 : F101) ^ 2 + a3 * (5 : F101) ^ 3
    let L6 : F101 := a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3
    have hzero : 51 * L0 - L1 + 53 * L4 - 3 * L5 + L6 = 0 := by
      dsimp [L0, L1, L4, L5, L6]
      ring_nf
      simp [show (101 : F101) = 0 by decide,
        show (202 : F101) = 0 by decide,
        show (808 : F101) = 0 by decide,
        show (3232 : F101) = 0 by decide]
    have hrhs : 51 * L0 - L1 + 53 * L4 - 3 * L5 + L6 = 70 := by
      dsimp [L0, L1, L4, L5, L6]
      rw [e0n, e1n, e4n, e5n, e6n]
      decide
    rw [← hzero]
    exact hrhs
  exact (by decide : ¬ ((0 : F101) = 70)) bad

theorem no_joint2 :
    ¬ pairJointAgreesOn (C101 : Set (Fin 8 → F101)) {0, 1, 2, 3, 6, 7} u0 u1 := by
  rintro ⟨v0, ⟨a0, a1, a2, a3, hv0⟩, _, _, hag⟩
  have e0 : a0 + a1 * dom 0 + a2 * dom 0 ^ 2 + a3 * dom 0 ^ 3 = u0 0 := by
    rw [← hv0 0]; exact (hag 0 (by decide)).1
  have e1 : a0 + a1 * dom 1 + a2 * dom 1 ^ 2 + a3 * dom 1 ^ 3 = u0 1 := by
    rw [← hv0 1]; exact (hag 1 (by decide)).1
  have e2 : a0 + a1 * dom 2 + a2 * dom 2 ^ 2 + a3 * dom 2 ^ 3 = u0 2 := by
    rw [← hv0 2]; exact (hag 2 (by decide)).1
  have e3 : a0 + a1 * dom 3 + a2 * dom 3 ^ 2 + a3 * dom 3 ^ 3 = u0 3 := by
    rw [← hv0 3]; exact (hag 3 (by decide)).1
  have e6 : a0 + a1 * dom 6 + a2 * dom 6 ^ 2 + a3 * dom 6 ^ 3 = u0 6 := by
    rw [← hv0 6]; exact (hag 6 (by decide)).1
  have e0n : a0 + a1 * (0 : F101) + a2 * (0 : F101) ^ 2 + a3 * (0 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e0
  have e1n : a0 + a1 * (1 : F101) + a2 * (1 : F101) ^ 2 + a3 * (1 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e1
  have e2n : a0 + a1 * (2 : F101) + a2 * (2 : F101) ^ 2 + a3 * (2 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e2
  have e3n : a0 + a1 * (3 : F101) + a2 * (3 : F101) ^ 2 + a3 * (3 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e3
  have e6n : a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3 = 37 := by
    simpa [dom, u0] using e6
  clear v0 hv0 hag
  have bad : (0 : F101) = 37 := by
    let L0 : F101 := a0 + a1 * (0 : F101) + a2 * (0 : F101) ^ 2 + a3 * (0 : F101) ^ 3
    let L1 : F101 := a0 + a1 * (1 : F101) + a2 * (1 : F101) ^ 2 + a3 * (1 : F101) ^ 3
    let L2 : F101 := a0 + a1 * (2 : F101) + a2 * (2 : F101) ^ 2 + a3 * (2 : F101) ^ 3
    let L3 : F101 := a0 + a1 * (3 : F101) + a2 * (3 : F101) ^ 2 + a3 * (3 : F101) ^ 3
    let L6 : F101 := a0 + a1 * (6 : F101) + a2 * (6 : F101) ^ 2 + a3 * (6 : F101) ^ 3
    have hzero : 10 * L0 + 65 * L1 + 45 * L2 + 81 * L3 + L6 = 0 := by
      dsimp [L0, L1, L2, L3, L6]
      ring_nf
      simp [show (202 : F101) = 0 by decide,
        show (404 : F101) = 0 by decide,
        show (1010 : F101) = 0 by decide,
        show (2828 : F101) = 0 by decide]
    have hrhs : 10 * L0 + 65 * L1 + 45 * L2 + 81 * L3 + L6 = 37 := by
      dsimp [L0, L1, L2, L3, L6]
      rw [e0n, e1n, e2n, e3n, e6n]
      decide
    rw [← hzero]
    exact hrhs
  exact (by decide : ¬ ((0 : F101) = 37)) bad

theorem no_joint33 :
    ¬ pairJointAgreesOn (C101 : Set (Fin 8 → F101)) {0, 1, 2, 3, 4, 5} u0 u1 := by
  rintro ⟨v0, ⟨a0, a1, a2, a3, hv0⟩, _, _, hag⟩
  have e0 : a0 + a1 * dom 0 + a2 * dom 0 ^ 2 + a3 * dom 0 ^ 3 = u0 0 := by
    rw [← hv0 0]; exact (hag 0 (by decide)).1
  have e1 : a0 + a1 * dom 1 + a2 * dom 1 ^ 2 + a3 * dom 1 ^ 3 = u0 1 := by
    rw [← hv0 1]; exact (hag 1 (by decide)).1
  have e2 : a0 + a1 * dom 2 + a2 * dom 2 ^ 2 + a3 * dom 2 ^ 3 = u0 2 := by
    rw [← hv0 2]; exact (hag 2 (by decide)).1
  have e3 : a0 + a1 * dom 3 + a2 * dom 3 ^ 2 + a3 * dom 3 ^ 3 = u0 3 := by
    rw [← hv0 3]; exact (hag 3 (by decide)).1
  have e4 : a0 + a1 * dom 4 + a2 * dom 4 ^ 2 + a3 * dom 4 ^ 3 = u0 4 := by
    rw [← hv0 4]; exact (hag 4 (by decide)).1
  have e0n : a0 + a1 * (0 : F101) + a2 * (0 : F101) ^ 2 + a3 * (0 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e0
  have e1n : a0 + a1 * (1 : F101) + a2 * (1 : F101) ^ 2 + a3 * (1 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e1
  have e2n : a0 + a1 * (2 : F101) + a2 * (2 : F101) ^ 2 + a3 * (2 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e2
  have e3n : a0 + a1 * (3 : F101) + a2 * (3 : F101) ^ 2 + a3 * (3 : F101) ^ 3 = 0 := by
    simpa [dom, u0] using e3
  have e4n : a0 + a1 * (4 : F101) + a2 * (4 : F101) ^ 2 + a3 * (4 : F101) ^ 3 = 58 := by
    simpa [dom, u0] using e4
  clear v0 hv0 hag
  have bad : (0 : F101) = 58 := by
    linear_combination e0n - 4 * e1n + 6 * e2n - 4 * e3n + e4n
  exact (by decide : ¬ ((0 : F101) = 58)) bad

/-! ## The four bad-scalar certificates -/

theorem cert0 : mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 0 := by
  refine ⟨{2, 3, 4, 5, 6, 7}, card_clause6 (by decide),
    ⟨fun i => 81 + 82 * dom i + 32 * dom i ^ 2 + 67 * dom i ^ 3,
      deg3_mem 81 82 32 67, by decide⟩, no_joint0⟩

theorem cert1 : mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 1 := by
  refine ⟨{0, 1, 4, 5, 6, 7}, card_clause6 (by decide),
    ⟨fun i => 0 + 34 * dom i + 66 * dom i ^ 2 + 1 * dom i ^ 3,
      deg3_mem 0 34 66 1, by decide⟩, no_joint1⟩

theorem cert2 : mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 2 := by
  refine ⟨{0, 1, 2, 3, 6, 7}, card_clause6 (by decide),
    ⟨0, C101.zero_mem, by decide⟩, no_joint2⟩

theorem cert33 : mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 33 := by
  refine ⟨{0, 1, 2, 3, 4, 5}, card_clause6 (by decide),
    ⟨0, C101.zero_mem, by decide⟩, no_joint33⟩

/-- The normalized F_101 boundary stack has four explicitly certified bad scalars. -/
theorem four_bad_scalars :
    ∃ Γ : Finset F101, Γ.card = 4 ∧
      ∀ γ ∈ Γ, mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 γ := by
  refine ⟨{0, 1, 2, 33}, by decide, ?_⟩
  intro γ hγ
  fin_cases hγ
  · exact cert0
  · exact cert1
  · exact cert2
  · exact cert33

open Classical in
/-- Filter-count form of `four_bad_scalars`, convenient for staircase consumers. -/
theorem four_bad_scalars_filter :
    4 ≤ (Finset.filter (fun γ : F101 =>
      mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 γ) Finset.univ).card := by
  have hsub : ({0, 1, 2, 33} : Finset F101) ⊆ Finset.filter (fun γ : F101 =>
      mcaEvent (F := F101) (C101 : Set (Fin 8 → F101)) (1/4) u0 u1 γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert33⟩
  calc
    4 = ({0, 1, 2, 33} : Finset F101).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Source audit -/

#print axioms cert0
#print axioms cert1
#print axioms cert2
#print axioms cert33
#print axioms four_bad_scalars
#print axioms four_bad_scalars_filter

end NubsResearch.F101Band3BoundaryWitness
