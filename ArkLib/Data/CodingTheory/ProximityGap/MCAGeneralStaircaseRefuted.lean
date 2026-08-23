/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAHalfDistanceGeneralRefuted

/-!
# Round 4 (#357): `GeneralStaircaseConjecture` is FALSE — the tripled-column attack at `b = 4`

The corrected surface (`d ≥ 2b + 1`) posed after the doubled-column refutation falls at its
first separating instance. The pre-registered decision experiment between the threshold laws
`f(b) = 3b − 2` and `2b + 1` (which **coincide at `b = 3`**, both `= 7`) is decided at
`b = 4` (`10` vs `9`):

**The tripled-column code** `T3 ⊂ F₁₁¹⁵` — three moment-curve generator rows, each column
`(1, t, t²)` repeated three times for `t ∈ {0,…,4}` — is a `[15, 3, 9]` code (no nonzero
codeword on `≤ 8` points: a vanishing position kills a whole direction, at most two of the
five pairwise-independent directions can vanish, so `≥ 3·3` positions survive). The stack

  `u₀ = (10,10,10, 0,…,0)`, `u₁ = (1,1,1, 3,3,3, 0,…,0)`

has **five** bad scalars `γ ∈ {0,1,2,3,4}` at `δ = 1/5` (band 4: `δ·n = 3 < 4`), each with
its punctured-triple witness; the explaining second row is trapped on three directions and
dies on the remaining two (`decide`). Hence `LinearStaircaseUpper T3 4` fails while the
`b = 4` hypothesis of the conjecture (distance `> 8`) holds:
`generalStaircaseConjecture_refuted`.

**The unified law** (every datum across `b = 2, 3, 4` now coheres): general-code band-`b`
collapse to the spike value holds iff `d ≥ 3b − 2`; the `(b−1)`-tupled-column codes explode
at `d = 3b − 3`. The landed `b = 2, 3` theorems are exactly the first instances
(`4 = 3·2−2`, `7 = 3·3−2`); the corrected surface `TheGeneralStaircaseLaw` (stated below,
never asserted) carries the `b ≥ 4` instances. The explosion witnesses are maximally
non-MDS — parallel matroid classes of size `b − 1` — so the gap to the RS/MDS threshold
(`d ≥ 2b`, directed-search-supported) is exactly parallel-class capacity: the staircase
below half-distance is a **matroid-sensitive** quantity.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAGeneralStaircaseRefuted

open ProximityGap.MCAHalfDistanceStaircase ProximityGap.MCAHalfDistanceGeneralRefuted

/-- Moment-curve generator rows, columns tripled. -/
def T0 : Fin 15 → F11 := ![1,1,1, 1,1,1, 1,1,1, 1,1,1, 1,1,1]

def T1 : Fin 15 → F11 := ![0,0,0, 1,1,1, 2,2,2, 3,3,3, 4,4,4]

def T2 : Fin 15 → F11 := ![0,0,0, 1,1,1, 4,4,4, 9,9,9, 5,5,5]

/-- The tripled-column `[15, 3, 9]` code over `F₁₁`. -/
def T3 : Submodule F11 (Fin 15 → F11) where
  carrier := {w | ∃ x0 x1 x2 : F11, ∀ i, w i = x0 * T0 i + x1 * T1 i + x2 * T2 i}
  zero_mem' := ⟨0, 0, 0, fun i => by simp⟩
  add_mem' := by
    rintro w w' ⟨a, b, c, h⟩ ⟨a', b', c', h'⟩
    exact ⟨a + a', b + b', c + c', fun i => by
      show w i + w' i = _
      rw [h i, h' i]; ring⟩
  smul_mem' := by
    rintro s w ⟨a, b, c, h⟩
    exact ⟨s * a, s * b, s * c, fun i => by
      show s * w i = _
      rw [h i]; ring⟩

/-- The direction (triple index) of a position. -/
def dir : Fin 15 → Fin 5 := ![0,0,0, 1,1,1, 2,2,2, 3,3,3, 4,4,4]

/-- The inner-product value of coefficient `x` against direction `a`. -/
def ip (x0 x1 x2 : F11) (a : Fin 5) : F11 :=
  x0 + x1 * (![0,1,2,3,4] a) + x2 * (![0,1,4,9,5] a)

/-- Codeword values factor through directions. -/
theorem val_eq_ip : ∀ (x0 x1 x2 : F11) (i : Fin 15),
    x0 * T0 i + x1 * T1 i + x2 * T2 i = ip x0 x1 x2 (dir i) := by decide

/-- The three positions of a direction. -/
def posSet : Fin 5 → Finset (Fin 15) := ![{0,1,2}, {3,4,5}, {6,7,8}, {9,10,11}, {12,13,14}]

theorem posSet_dir : ∀ (a : Fin 5) (i : Fin 15), i ∈ posSet a → dir i = a := by decide

theorem posSet_card : ∀ a : Fin 5, (posSet a).card = 3 := by decide

theorem posSet_disj : ∀ a b : Fin 5, a ≠ b → Disjoint (posSet a) (posSet b) := by decide

/-- Any three distinct directions kill the coefficients (moment-curve independence). -/
theorem three_dirs_kill : ∀ (a b c : Fin 5), a ≠ b → a ≠ c → b ≠ c →
    ∀ x0 x1 x2 : F11, ip x0 x1 x2 a = 0 → ip x0 x1 x2 b = 0 → ip x0 x1 x2 c = 0 →
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by decide

open Classical in
/-- **`T3` has no nonzero codeword on `≤ 8` points** (distance `9`): the `b = 4`
hypothesis of `GeneralStaircaseConjecture`. -/
theorem T3_noWeight : ∀ w ∈ T3,
    (∃ T : Finset (Fin 15), T.card ≤ 2 * 4 ∧ ∀ i ∉ T, w i = 0) → w = 0 := by
  rintro w ⟨x0, x1, x2, hw⟩ ⟨T, hT, hsupp⟩
  -- live directions have their whole triple inside T
  set B : Finset (Fin 5) := Finset.univ.filter (fun a => ip x0 x1 x2 a ≠ 0) with hB
  have hsub : B.biUnion posSet ⊆ T := by
    intro i hi
    obtain ⟨a, haB, hia⟩ := Finset.mem_biUnion.mp hi
    by_contra hiT
    have hz := hsupp i hiT
    rw [hw i, val_eq_ip x0 x1 x2 i, posSet_dir a i hia] at hz
    exact (Finset.mem_filter.mp haB).2 hz
  have hcardB : (B.biUnion posSet).card = 3 * B.card := by
    rw [Finset.card_biUnion (fun a _ b _ hab => posSet_disj a b hab)]
    rw [Finset.sum_congr rfl (fun a _ => posSet_card a)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hBle : B.card ≤ 2 := by
    have h := Finset.card_le_card hsub
    rw [hcardB] at h
    omega
  -- so at least three directions vanish
  have hcompl : 2 < (Finset.univ.filter (fun a : Fin 5 => ip x0 x1 x2 a = 0)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5))) (p := fun a => ip x0 x1 x2 a = 0)
    have huniv : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
    have hBeq : (Finset.univ.filter (fun a : Fin 5 => ¬ ip x0 x1 x2 a = 0)).card
        = B.card := rfl
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcompl
  obtain ⟨h0, h1, h2⟩ := three_dirs_kill a b c hab hac hbc x0 x1 x2
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
  funext i
  rw [hw i, h0, h1, h2]
  show (0 : F11) * T0 i + 0 * T1 i + 0 * T2 i = 0
  ring

/-- The refuting stack. -/
def v0 : Fin 15 → F11 := ![10,10,10, 0,0,0, 0,0,0, 0,0,0, 0,0,0]

def v1 : Fin 15 → F11 := ![1,1,1, 3,3,3, 0,0,0, 0,0,0, 0,0,0]

/-- Witness sets: the doubly... triply-punctured universes (one triple removed). -/
def Sof : Fin 5 → Finset (Fin 15) :=
  ![{3,4,5,6,7,8,9,10,11,12,13,14}, {0,1,2,6,7,8,9,10,11,12,13,14},
    {0,1,2,3,4,5,9,10,11,12,13,14}, {0,1,2,3,4,5,6,7,8,12,13,14},
    {0,1,2,3,4,5,6,7,8,9,10,11}]

/-- The witness-size clause at `δ = 1/5`, `n = 15`: twelve points suffice. -/
theorem card_clause15 {S : Finset (Fin 15)} (hS : S.card = 12) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/5) * (Fintype.card (Fin 15) : ℝ≥0) := by
  rw [hS, Fintype.card_fin]
  calc ((1 : ℝ≥0) - 1/5) * (15 : ℕ) ≤ (4/5 : ℝ≥0) * (15 : ℕ) := by
        gcongr
        exact tsub_le_iff_right.mpr (by norm_num)
    _ ≤ ((12 : ℕ) : ℝ≥0) := by push_cast; norm_num

/-- The five on-line codewords (`w_γ = u₀ + γ·u₁ + e_γ`), as coefficient triples:
checked by `decide` inside each event. -/
def wcoef : Fin 5 → F11 × F11 × F11 :=
  ![(0, 0, 0), (0, 0, 0), (1, 4, 1), (2, 4, 3), (3, 3, 6)]

open Classical in
/-- The five bad events, uniformly: scalar `g ∈ {0,…,4}` is bad with witness `Sof g`. -/
theorem mcaEvent_t (g : Fin 5) :
    mcaEvent (F := F11) (T3 : Set (Fin 15 → F11)) (1/5) v0 v1 (![0,1,2,3,4] g) := by
  refine ⟨Sof g, card_clause15 (by fin_cases g <;> decide), ?_, ?_⟩
  · -- the on-line codeword
    refine ⟨fun i => (wcoef g).1 * T0 i + (wcoef g).2.1 * T1 i + (wcoef g).2.2 * T2 i,
      ⟨(wcoef g).1, (wcoef g).2.1, (wcoef g).2.2, fun _ => rfl⟩, ?_⟩
    fin_cases g <;> decide
  · -- no joint explanation: the second row is blocked
    rintro ⟨vv₀, _, vv₁, ⟨a, b, c, h⟩, hag⟩
    -- four probe positions covering the four surviving directions
    have key : ∀ a b c : F11,
        (∀ i ∈ Sof g, a * T0 i + b * T1 i + c * T2 i = v1 i) → False := by
      fin_cases g <;> decide
    refine key a b c fun i hi => ?_
    rw [← h i]
    exact (hag i hi).2

open Classical in
/-- **The refutation:** `GeneralStaircaseConjecture` is false — `T3` satisfies the `b = 4`
distance hypothesis, yet the tripled-column stack has five bad scalars in band 4. The
general-code collapse threshold is `3b − 2`, not `2b + 1`. -/
theorem generalStaircaseConjecture_refuted : ¬ GeneralStaircaseConjecture := by
  intro h
  have hLSU : LinearStaircaseUpper T3 4 :=
    h (Fin 15) inferInstance inferInstance inferInstance F11 inferInstance inferInstance
      inferInstance T3 4 (by omega) T3_noWeight
  have hδ : ((1 : ℝ≥0)/5) * (Fintype.card (Fin 15) : ℝ≥0) < (4 : ℕ) := by
    rw [Fintype.card_fin]
    push_cast
    norm_num
  have hcap := hLSU (1/5) hδ ![v0, v1]
  have hsub : ({0, 1, 2, 3, 4} : Finset F11) ⊆ Finset.filter (fun γ : F11 =>
      mcaEvent (F := F11) (T3 : Set (Fin 15 → F11)) (1/5)
        ((![v0, v1] : WordStack F11 (Fin 2) (Fin 15)) 0)
        ((![v0, v1] : WordStack F11 (Fin 2) (Fin 15)) 1) γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_t 0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_t 1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_t 2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_t 3⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_t 4⟩
  have h5 : (5 : ℕ) ≤ (Finset.filter (fun γ : F11 =>
      mcaEvent (F := F11) (T3 : Set (Fin 15 → F11)) (1/5)
        ((![v0, v1] : WordStack F11 (Fin 2) (Fin 15)) 0)
        ((![v0, v1] : WordStack F11 (Fin 2) (Fin 15)) 1) γ) Finset.univ).card := by
    calc (5 : ℕ) = ({0, 1, 2, 3, 4} : Finset F11).card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- **The unified general-code surface** (`d ≥ 3b − 2`; stated, never asserted): the landed
`b = 2, 3` collapse theorems are exactly its first instances, and the `(b−1)`-tupled-column
codes witness sharpness at `d = 3b − 3` for `b = 2, 3, 4`. -/
def TheGeneralStaircaseLaw : Prop :=
  ∀ (ι : Type) (inst1 : Fintype ι) (inst2 : Nonempty ι) (inst3 : DecidableEq ι)
    (F : Type) (inst4 : Field F) (inst5 : Fintype F) (inst6 : DecidableEq F)
    (C : Submodule F (ι → F)) (b : ℕ), 4 ≤ b →
    (∀ w ∈ C, (∃ T : Finset ι, T.card ≤ 3 * b - 3 ∧ ∀ i ∉ T, w i = 0) → w = 0) →
    LinearStaircaseUpper C b

/-! ## Source audit -/

#print axioms T3_noWeight
#print axioms mcaEvent_t
#print axioms generalStaircaseConjecture_refuted

end ProximityGap.MCAGeneralStaircaseRefuted
