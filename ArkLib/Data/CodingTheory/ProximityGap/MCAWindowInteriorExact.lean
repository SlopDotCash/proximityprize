/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALYMCeiling
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The first exact window-interior `ε_mca` value (#357 round 4)

The open core of the Proximity Prize lives in the window between the Johnson radius and
capacity. This file produces the **first machine-checked exact `ε_mca` value strictly
inside that window**, at the cell the round-3 probes mapped:

  `C = RS[F₁₁, (1,2,3,4,5), 2]` (rate `2/5`), `δ = 2/5` — with
  Johnson `= 1 − √(2/5) ≈ 0.368 < 0.4 = δ < 0.6 = 1 − ρ` (capacity):

  **`ε_mca(C, 2/5) = 10/11 = C(5,3)/q`  exactly** (`epsMCA_window_eq`).

* **Upper bound:** the LYM ceiling (`epsMCA_le_choose_div`, landed): the witnesses of
  distinct bad scalars form an antichain of `≥ 3`-sets in a 5-point universe, so at most
  `C(5,3) = 10` bad scalars — for *every* stack.
* **Lower bound:** the probe-discovered extremal stack `u₀ = (0,0,0,1,4)`,
  `u₁ = (0,0,1,5,10)`. Its second row is *uninterpolable on every 3-set* (`u1_far`, kernel
  check), so no witness is ever jointly explained; and **every one of the ten 3-subsets
  fires its own interpolation scalar** — the bad scalars are `{0,1,2,4,5,6,7,8,9,10}`
  (all of `F₁₁` except `3`), in bijection with the full `C(5,3)` layer. The antichain
  ceiling is attained by a complete layer.

Interiorness is recorded in integer form (`window_interior`): `k < t ∧ t² < k·n` with
`t = 3` the agreement floor — i.e. `δ` strictly between Johnson and capacity.

Honest scope: this is one toy-scale cell (`n = 5`), where "inside the window" is a fact
about this instance's parameters, not an asymptotic statement; small fields (`F₇`)
degenerate to full breakdown, and `q ∈ {11, 13}` both sit exactly at the census `10`.
What it contributes: the staircase programme now provably *reaches the window* — the
question "where is `δ*`" has become "at which floor does the attained census detach from
`C(n,t)`", with this cell as the first fully pinned interior datum.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
`native_decide`.

## References

- Issue #357 (round-3/4 window-cell probe + anatomy comments); `MCALYMCeiling.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCALYMCeiling

namespace ProximityGap.MCAWindowInteriorExact

instance primeFact_MCAWindowInteriorExact_1 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The base field `F₁₁`. -/
abbrev F11 : Type := ZMod 11

/-- The evaluation domain `(1, 2, 3, 4, 5)`. -/
def dom : Fin 5 → F11 := ![1, 2, 3, 4, 5]

theorem dom_injective : Function.Injective dom := by decide

/-- The domain embedding. -/
def domain5 : Fin 5 ↪ F11 := ⟨dom, dom_injective⟩

/-- The probe-discovered extremal stack, first row. -/
def u0 : Fin 5 → F11 := ![0, 0, 0, 1, 4]

/-- The extremal stack, second row — uninterpolable on every 3-set. -/
def u1 : Fin 5 → F11 := ![0, 0, 1, 5, 10]

/-- Membership in `RS[F₁₁, dom, 2]`: affine evaluations. -/
theorem mem_rs_iff {v : Fin 5 → F11} :
    v ∈ ReedSolomon.code domain5 2 ↔ ∃ a b : F11, ∀ i, v i = a + b * dom i := by
  constructor
  · intro hv
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hv
    obtain ⟨p, hdeg, rfl⟩ := hv
    obtain ⟨c, d, rfl⟩ :=
      Polynomial.exists_eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hdeg)
    refine ⟨d, c, fun i => ?_⟩
    simp [ReedSolomon.evalOnPoints, domain5]
    ring
  · rintro ⟨a, b, hv⟩
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    refine ⟨Polynomial.C b * Polynomial.X + Polynomial.C a, ?_, ?_⟩
    · have h1 : (Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
        le_trans (Polynomial.natDegree_C_mul_le b Polynomial.X) Polynomial.natDegree_X_le
      have h2 : (Polynomial.C a : Polynomial F11).natDegree = 0 := Polynomial.natDegree_C a
      have h3 := Polynomial.natDegree_add_le (Polynomial.C b * Polynomial.X)
        (Polynomial.C a : Polynomial F11)
      omega
    · funext i
      rw [hv i]
      simp [ReedSolomon.evalOnPoints, domain5]
      ring

/-- **`u₁` is uninterpolable on every 3-set** — no affine polynomial agrees with it on any
three of the five domain points (kernel check, `11² × 32` cases). -/
theorem u1_far : ∀ a b : F11, ∀ S : Finset (Fin 5), 3 ≤ S.card →
    ¬ (∀ i ∈ S, a + b * dom i = u1 i) := by decide

/-- No witness set of size `≥ 3` is ever jointly explained for this stack. -/
theorem not_pairJoint (S : Finset (Fin 5)) (hS : 3 ≤ S.card) :
    ¬ pairJointAgreesOn (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) S u0 u1 := by
  rintro ⟨v₀, _hv₀, v₁, hv₁, hag⟩
  obtain ⟨a, b, hab⟩ := mem_rs_iff.mp hv₁
  exact u1_far a b S hS (fun i hi => by rw [← hab i]; exact (hag i hi).2)

/-- The witness-size clause at `δ = 2/5`, `n = 5`: a 3-set qualifies. -/
theorem card_clause {S : Finset (Fin 5)} (hS : 3 ≤ S.card) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 2/5) * (Fintype.card (Fin 5) : ℝ≥0) := by
  have hsub : ((1 : ℝ≥0) - 2/5) ≤ 3/5 := tsub_le_iff_right.mpr (by norm_num)
  calc ((1 : ℝ≥0) - 2/5) * (Fintype.card (Fin 5) : ℝ≥0)
      ≤ (3/5) * (Fintype.card (Fin 5) : ℝ≥0) :=
        mul_le_mul_of_nonneg_right hsub (zero_le _)
    _ = 3 := by rw [Fintype.card_fin]; norm_num
    _ ≤ (S.card : ℝ≥0) := by exact_mod_cast hS

/-- The per-scalar witness table (probe-discovered): witness 3-set and codeword `(a, b)`
for each bad scalar. -/
def witTable : F11 → (Finset (Fin 5)) × F11 × F11 := fun γ =>
  if γ = 0 then ({0, 1, 2}, 0, 0)
  else if γ = 1 then ({1, 2, 4}, 9, 1)
  else if γ = 2 then ({0, 1, 3}, 0, 0)
  else if γ = 4 then ({0, 1, 4}, 0, 0)
  else if γ = 5 then ({0, 2, 4}, 3, 8)
  else if γ = 6 then ({0, 2, 3}, 8, 3)
  else if γ = 7 then ({1, 2, 3}, 8, 7)
  else if γ = 8 then ({0, 3, 4}, 1, 10)
  else if γ = 9 then ({2, 3, 4}, 8, 4)
  else ({1, 3, 4}, 4, 9)

/-- The ten bad scalars: all of `F₁₁` except `3`. -/
def badG : Finset F11 := {0, 1, 2, 4, 5, 6, 7, 8, 9, 10}

theorem badG_card : badG.card = 10 := by decide

/-- The table data verifies: for each `γ ∈ badG`, the witness has 3 elements and the
codeword agrees with the line on it (kernel check). -/
theorem table_checks : ∀ γ ∈ badG,
    3 ≤ (witTable γ).1.card ∧
    ∀ i ∈ (witTable γ).1,
      (witTable γ).2.1 + (witTable γ).2.2 * dom i = u0 i + γ * u1 i := by decide

/-- **Every scalar in `badG` fires `mcaEvent`** at `δ = 2/5`. -/
theorem mcaEvent_badG : ∀ γ ∈ badG,
    mcaEvent (F := F11) (ReedSolomon.code domain5 2 : Set (Fin 5 → F11))
      (2/5) u0 u1 γ := by
  intro γ hγ
  obtain ⟨hcard, hagree⟩ := table_checks γ hγ
  refine ⟨(witTable γ).1, card_clause hcard,
    ⟨fun i => (witTable γ).2.1 + (witTable γ).2.2 * dom i,
      mem_rs_iff.mpr ⟨(witTable γ).2.1, (witTable γ).2.2, fun _ => rfl⟩,
      fun i hi => ?_⟩,
    not_pairJoint _ hcard⟩
  show (witTable γ).2.1 + (witTable γ).2.2 * dom i = u0 i + γ • u1 i
  have hsh : u0 i + γ • u1 i = u0 i + γ * u1 i := by simp [smul_eq_mul]
  rw [hsh]
  exact hagree i hi

/-- The stack as a `WordStack`. -/
def stack : WordStack F11 (Fin 2) (Fin 5) := fun j => if j = 0 then u0 else u1

/-- **THE FIRST EXACT WINDOW-INTERIOR `ε_mca` VALUE.**

  `ε_mca(RS[F₁₁, (1..5), 2], 2/5) = 10/11 = C(5,3)/q`  exactly,

with `δ = 2/5` strictly between Johnson and capacity (`window_interior`). Lower: the ten
explicit bad scalars (full `C(5,3)` layer attained); upper: the LYM ceiling. -/
theorem epsMCA_window_eq :
    epsMCA (F := F11) (A := F11)
        (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) (2/5)
      = (10 : ℝ≥0∞) / 11 := by
  apply le_antisymm
  · -- LYM ceiling: C(5,3) = 10
    have h := epsMCA_le_choose_div (F := F11) (A := F11)
      (ReedSolomon.code domain5 2) (2/5) (t := 3)
      (by
        rw [Fintype.card_fin]
        have hsub : (3/5 : ℝ≥0) ≤ 1 - 2/5 := by
          rw [le_tsub_iff_right (by
            rw [div_le_one (by norm_num : (0 : ℝ≥0) < 5)]
            norm_num)]
          norm_num
        calc ((3 : ℕ) : ℝ≥0) = (3/5) * 5 := by norm_num
          _ ≤ (1 - 2/5) * 5 := mul_le_mul_of_nonneg_right hsub (zero_le _)
          _ = (1 - 2/5) * ((5 : ℕ) : ℝ≥0) := by norm_num)
      (by rw [Fintype.card_fin]; norm_num)
    have hc : (Fintype.card (Fin 5)).choose 3 = 10 := by decide
    have hF : Fintype.card F11 = 11 := ZMod.card 11
    rw [hc, hF] at h
    simpa using h
  · -- the ten-scalar lower bound
    have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F11) (A := F11)
      (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) (2/5) stack badG (by
        intro γ hγ
        have h0 : stack 0 = u0 := rfl
        have h1 : stack 1 = u1 := by
          show (if (1 : Fin 2) = 0 then u0 else u1) = u1
          norm_num
        rw [h0, h1]
        exact mcaEvent_badG γ hγ)
    have hG : badG.card = 10 := badG_card
    have hF : Fintype.card F11 = 11 := ZMod.card 11
    rw [hG, hF] at h
    simpa using h

/-- **Interiorness**: with agreement floor `t = 3`, the cell satisfies `k < t` (above
unique decoding territory: `δ` past the half-distance) and `t² < k·n` (above Johnson:
`(1−δ) < √ρ`), i.e. `δ = 2/5` is strictly inside `(1−√ρ, 1−ρ)` for `ρ = 2/5`. -/
theorem window_interior : 2 < 3 ∧ 3 ^ 2 < 2 * 5 := by
  norm_num

/-! ## Source audit -/

#print axioms u1_far
#print axioms mcaEvent_badG
#print axioms epsMCA_window_eq
#print axioms window_interior

end ProximityGap.MCAWindowInteriorExact
