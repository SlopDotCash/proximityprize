/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdBudgetMono
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# An exact `δ*` point strictly above the Johnson radius: `mcaDeltaStar(RS[F₁₁, H₅, 2], 1/2) = 2/5`

The existing concrete exact pins (`DeltaStarExactPinF5` at `δ* = 1/4`, the `F17` second pins) all
land `δ*` at or below the unique-decoding radius.  This file produces a machine-checked exact
`δ*` value that sits **strictly above the Johnson list-decoding radius** for an explicit smooth-
domain Reed–Solomon code — the qualitative phenomenon the Proximity Prize is about.

The code is `C = RS[F₁₁, H₅, 2]`: degree-`< 2` polynomials evaluated on the order-`5`
multiplicative subgroup `H₅ = ⟨4⟩ = {4⁰,…,4⁴} = (1, 4, 5, 9, 3) ⊂ F₁₁*` (a genuinely smooth
domain of size `n = 5`).  Rate `ρ = 2/5`, so:

  * unique-decoding radius `(1−ρ)/2 = 3/10 = 0.3`,
  * Johnson radius `1 − √ρ = 1 − √(2/5) ≈ 0.368`,
  * capacity `1 − ρ = 3/5 = 0.6`.

With threshold `ε* = 1/2` we pin

  `mcaDeltaStar (C : Set (Fin 5 → F₁₁)) (1/2) = 2/5 = 0.4`,

so `0.368 ≈ Johnson < δ* = 0.4 < 0.6 = capacity`: an exact `δ*` **above Johnson**.

The exact ground truth (probe `scripts/probes/probe_exact_epsmca_ladder.py`, exact arithmetic):
`ε_mca(C, δ)` is the step function `1/11 → 2/11 → 10/11` with jumps at `δ = 1/5` and `δ = 2/5`.
At `ε* = 1/2` the supremum of good radii sits exactly at the second jump `2/5`.

## Proof architecture

* **Good side (substrate, no enumeration).**  For every `δ < 2/5` the witness-cardinality clause
  forces each legal `mcaEvent` witness set to have size `≥ n − 1 = 4`, so the forced-codimension-one
  barrier `MCAWitnessSpread.epsMCA_le_card_div_of_forced_pred` gives `ε_mca(C, δ) ≤ n/|F| = 5/11`,
  and `5/11 ≤ 1/2`.
* **Bad side (explicit stacks).**  The first probe-extracted stack `u₀ = (0,0,0,0,1)`,
  `u₁ = (8,3,4,5,9)` has `6` of `11` scalars bad at `δ = 2/5`, already enough for the headline
  `ε* = 1/2` pin.  A sharper stack `u₀ = (7,4,3,0,0)`, `u₁ = (3,9,1,0,0)` has `10` of `11`
  scalars bad, matching the exact second jump.  Each badness certificate is an
  explicit `3`-element witness set, an explicit interpolating codeword, and a `decide`d
  non-explainability of the row `u₁`.  Hence `ε_mca(C, 2/5) ≥ 10/11`.
* **Assembly.**  The two `MCAThresholdLedger` bracket lemmas plus density of `ℝ≥0` pin the `sSup`.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3: `mcaEvent`/`epsMCA`.)
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.DeltaStarPinF11H5

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code
open Polynomial

/-! ## The concrete code `RS[F₁₁, H₅, 2]` -/

/-- The field `F₁₁`. -/
abbrev F11 := ZMod 11

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- `(2/5 : ℝ≥0) ≤ 1`, the recurring radius-sanity fact. -/
theorem twoFifth_le_one : (2/5 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num : (0 : ℝ≥0) < 5)]; norm_num

/-- The smooth evaluation domain `H₅ = ⟨4⟩ = (4⁰, 4¹, 4², 4³, 4⁴) = (1, 4, 5, 9, 3)`, the unique
order-`5` multiplicative subgroup of `F₁₁*`. -/
def dom : Fin 5 → F11 := ![1, 4, 5, 9, 3]

/-- The same domain packaged as an injection, for the generic Reed–Solomon ladder. -/
def domEmb : Fin 5 ↪ F11 := ⟨dom, by decide⟩

/-- The codeword of the polynomial `a + b·X`, evaluated on `dom`. -/
def lineEval (a b : F11) : Fin 5 → F11 := fun i => a + b * dom i

/-- `RS[F₁₁, H₅, 2]` — evaluations of degree-`< 2` polynomials on `dom` — as a submodule. -/
def C : Submodule F11 (Fin 5 → F11) where
  carrier := {w | ∃ a b : F11, w = lineEval a b}
  add_mem' := by
    rintro w w' ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a + a', b + b', ?_⟩
    funext i
    change lineEval a b i + lineEval a' b' i = lineEval (a + a') (b + b') i
    simp only [lineEval]; ring
  zero_mem' := ⟨0, 0, by funext i; simp [lineEval]⟩
  smul_mem' := by
    rintro c w ⟨a, b, rfl⟩
    refine ⟨c * a, c * b, ?_⟩
    funext i
    change c • lineEval a b i = lineEval (c * a) (c * b) i
    simp only [lineEval, smul_eq_mul]; ring

theorem lineEval_mem (a b : F11) : lineEval a b ∈ (C : Set (Fin 5 → F11)) := ⟨a, b, rfl⟩

/-- Affine words are exactly degree-`< 2` Reed–Solomon evaluations on `dom`. -/
theorem lineEval_mem_rsCode (a b : F11) :
    lineEval a b ∈
      (ProximityGap.SpikeFloor.rsCode domEmb 2 : Submodule F11 (Fin 5 → F11)) := by
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X, ?_, ?_⟩
  · have h1 : (Polynomial.C a + Polynomial.C b * Polynomial.X).degree ≤ 1 := by
      refine le_trans (Polynomial.degree_add_le _ _) ?_
      refine max_le (le_trans Polynomial.degree_C_le (by norm_num)) ?_
      refine le_trans (Polynomial.degree_mul_le _ _) ?_
      refine le_trans (add_le_add Polynomial.degree_C_le Polynomial.degree_X_le) ?_
      norm_num
    exact lt_of_le_of_lt h1 (by norm_num)
  · funext i
    simp [lineEval, domEmb, dom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]

/-- A degree-`< 2` polynomial evaluation is one of the affine words defining `C`. -/
theorem rsEval_mem_C_of_degree_lt_two (P : Polynomial F11) (hP : P.degree < (2 : ℕ)) :
    (fun i : Fin 5 => P.eval (domEmb i)) ∈ (C : Set (Fin 5 → F11)) := by
  have hle : P.degree ≤ (1 : WithBot ℕ) := by
    by_cases h0 : P = 0
    · rw [h0]
      exact bot_le
    · have hnat : P.natDegree < 2 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hP
      exact Polynomial.degree_le_of_natDegree_le (Nat.le_of_lt_succ hnat)
  refine ⟨P.coeff 0, P.coeff 1, ?_⟩
  funext i
  rw [Polynomial.eq_X_add_C_of_degree_le_one hle]
  simp [lineEval, domEmb, dom, eval_add, eval_mul, eval_C, eval_X]
  ring

/-- The hand-written affine code `C` is the generic `rsCode domEmb 2`. -/
theorem C_eq_rsCode_two :
    C = ProximityGap.SpikeFloor.rsCode domEmb 2 := by
  ext w
  constructor
  · rintro ⟨a, b, rfl⟩
    exact lineEval_mem_rsCode a b
  · rintro ⟨P, hP, rfl⟩
    exact rsEval_mem_C_of_degree_lt_two P hP

/-- Explainability of a single row on a coordinate set (decidable finite search). -/
def ExplainableOn (S : Finset (Fin 5)) (w : Fin 5 → F11) : Prop :=
  ∃ a b : F11, ∀ i ∈ S, lineEval a b i = w i

instance (S : Finset (Fin 5)) (w : Fin 5 → F11) : Decidable (ExplainableOn S w) := by
  unfold ExplainableOn; infer_instance

theorem explainableOn_iff (S : Finset (Fin 5)) (w : Fin 5 → F11) :
    (∃ v ∈ (C : Set (Fin 5 → F11)), ∀ i ∈ S, v i = w i) ↔ ExplainableOn S w := by
  constructor
  · rintro ⟨v, ⟨a, b, rfl⟩, h⟩; exact ⟨a, b, h⟩
  · rintro ⟨a, b, h⟩; exact ⟨lineEval a b, lineEval_mem a b, h⟩

/-- To refute the joint-pair clause it suffices that the second row is not explainable. -/
theorem not_pairJointAgreesOn_of_row1 {S : Finset (Fin 5)} {u₀ u₁ : Fin 5 → F11}
    (h : ¬ ExplainableOn S u₁) :
    ¬ pairJointAgreesOn (C : Set (Fin 5 → F11)) S u₀ u₁ := by
  rw [MCAWitnessSpread.pairJointAgreesOn_iff_split]
  rintro ⟨_, h₁⟩
  exact h ((explainableOn_iff S u₁).mp h₁)

/-! ## The bad stack at `δ = 2/5` (probe-extracted, 6 of 11 scalars bad) -/

def u₀ : Fin 5 → F11 := ![0, 0, 0, 0, 1]
def u₁ : Fin 5 → F11 := ![8, 3, 4, 5, 9]

/-- The bad stack as a `WordStack`. -/
def ubad : WordStack F11 (Fin 2) (Fin 5) := ![u₀, u₁]

@[simp] theorem ubad_zero : ubad 0 = u₀ := rfl
@[simp] theorem ubad_one : ubad 1 = u₁ := rfl

/-- The witness-cardinality clause of `mcaEvent` at `δ = 2/5`, `n = 5`, for a 3-element set. -/
theorem card_cond {S : Finset (Fin 5)} (h : S.card = 3) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - (2/5 : ℝ≥0)) * (Fintype.card (Fin 5) : ℝ≥0) := by
  have h35 : ((1 : ℝ≥0) - (2/5 : ℝ≥0)) * (Fintype.card (Fin 5) : ℝ≥0) = 3 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub twoFifth_le_one]
    push_cast [Fintype.card_fin]
    norm_num
  rw [ge_iff_le, h35, h]; norm_num

/-- `γ = 0` is bad: witness set `{0,1,2}`, interpolating codeword `0`. -/
theorem mcaEvent_g0 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (0 : F11) := by
  refine ⟨{0, 1, 2}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 1` is bad: witness set `{0,3,4}`, interpolating codeword `7 + X`. -/
theorem mcaEvent_g1 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (1 : F11) := by
  refine ⟨{0, 3, 4}, card_cond (by decide), ⟨lineEval 7 1, lineEval_mem 7 1, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 3` is bad: witness set `{1,2,4}`, interpolating codeword `8 + 3X`. -/
theorem mcaEvent_g3 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (3 : F11) := by
  refine ⟨{1, 2, 4}, card_cond (by decide), ⟨lineEval 8 3, lineEval_mem 8 3, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 4` is bad: witness set `{0,1,4}`, interpolating codeword `2 + 8X`. -/
theorem mcaEvent_g4 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (4 : F11) := by
  refine ⟨{0, 1, 4}, card_cond (by decide), ⟨lineEval 2 8, lineEval_mem 2 8, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 5` is bad: witness set `{1,3,4}`, interpolating codeword `7 + 2X`. -/
theorem mcaEvent_g5 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (5 : F11) := by
  refine ⟨{1, 3, 4}, card_cond (by decide), ⟨lineEval 7 2, lineEval_mem 7 2, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 7` is bad: witness set `{0,2,4}`, interpolating codeword `8 + 4X`. -/
theorem mcaEvent_g7 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀ u₁ (7 : F11) := by
  refine ⟨{0, 2, 4}, card_cond (by decide), ⟨lineEval 8 4, lineEval_mem 8 4, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The bad-scalar set: 6 of the 11 scalars. -/
def Gbad : Finset F11 := {0, 1, 3, 4, 5, 7}

theorem mcaEvent_of_mem_Gbad :
    ∀ γ ∈ Gbad, mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) (ubad 0) (ubad 1) γ := by
  intro γ hγ
  rw [ubad_zero, ubad_one]
  simp only [Gbad, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mcaEvent_g0
  · exact mcaEvent_g1
  · exact mcaEvent_g3
  · exact mcaEvent_g4
  · exact mcaEvent_g5
  · exact mcaEvent_g7

/-- **Bad side:** `ε_mca(C, 2/5) ≥ 6/11`. -/
theorem epsMCA_twoFifth_ge :
    (6 : ℝ≥0∞) / 11 ≤ epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) (2/5) := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (Fin 5 → F11)) (2/5) ubad Gbad mcaEvent_of_mem_Gbad
  have hG : (Gbad.card : ℝ≥0∞) = 6 := by rw [show Gbad.card = 6 from by decide]; norm_num
  have hF : ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 := by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num
  rwa [hG, hF] at h

/-! ## The sharp bad side at `δ = 2/5` (10 of 11 scalars bad) -/

def u₀Top : Fin 5 → F11 := ![7, 4, 3, 0, 0]
def u₁Top : Fin 5 → F11 := ![3, 9, 1, 0, 0]

/-- The sharp second-jump bad stack. -/
def ubadTop : WordStack F11 (Fin 2) (Fin 5) := ![u₀Top, u₁Top]

@[simp] theorem ubadTop_zero : ubadTop 0 = u₀Top := rfl
@[simp] theorem ubadTop_one : ubadTop 1 = u₁Top := rfl

/-- `γ = 0` is bad for the sharp stack. -/
theorem mcaEventTop_g0 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (0 : F11) := by
  refine ⟨{0, 1, 2}, card_cond (by decide), ⟨lineEval 8 10, lineEval_mem 8 10, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 1` is bad for the sharp stack. -/
theorem mcaEventTop_g1 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (1 : F11) := by
  refine ⟨{1, 2, 4}, card_cond (by decide), ⟨lineEval 5 2, lineEval_mem 5 2, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 2` is bad for the sharp stack. -/
theorem mcaEventTop_g2 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (2 : F11) := by
  refine ⟨{1, 3, 4}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 3` is bad for the sharp stack. -/
theorem mcaEventTop_g3 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (3 : F11) := by
  refine ⟨{0, 2, 4}, card_cond (by decide), ⟨lineEval 2 3, lineEval_mem 2 3, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 4` is bad for the sharp stack. -/
theorem mcaEventTop_g4 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (4 : F11) := by
  refine ⟨{0, 1, 4}, card_cond (by decide), ⟨lineEval 1 7, lineEval_mem 1 7, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 5` is bad for the sharp stack. -/
theorem mcaEventTop_g5 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (5 : F11) := by
  refine ⟨{0, 3, 4}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 6` is bad for the sharp stack. -/
theorem mcaEventTop_g6 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (6 : F11) := by
  refine ⟨{1, 2, 3}, card_cond (by decide), ⟨lineEval 1 6, lineEval_mem 1 6, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 7` is bad for the sharp stack. -/
theorem mcaEventTop_g7 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (7 : F11) := by
  refine ⟨{0, 1, 3}, card_cond (by decide), ⟨lineEval 4 2, lineEval_mem 4 2, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 8` is bad for the sharp stack. -/
theorem mcaEventTop_g8 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (8 : F11) := by
  refine ⟨{2, 3, 4}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 10` is bad for the sharp stack. -/
theorem mcaEventTop_g10 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) u₀Top u₁Top (10 : F11) := by
  refine ⟨{0, 2, 3}, card_cond (by decide), ⟨lineEval 10 5, lineEval_mem 10 5, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The sharp second-jump bad-scalar set: 10 of the 11 scalars. -/
def GbadTop : Finset F11 := {0, 1, 2, 3, 4, 5, 6, 7, 8, 10}

theorem mcaEventTop_of_mem_GbadTop :
    ∀ γ ∈ GbadTop,
      mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (2/5) (ubadTop 0) (ubadTop 1) γ := by
  intro γ hγ
  rw [ubadTop_zero, ubadTop_one]
  simp only [GbadTop, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mcaEventTop_g0
  · exact mcaEventTop_g1
  · exact mcaEventTop_g2
  · exact mcaEventTop_g3
  · exact mcaEventTop_g4
  · exact mcaEventTop_g5
  · exact mcaEventTop_g6
  · exact mcaEventTop_g7
  · exact mcaEventTop_g8
  · exact mcaEventTop_g10

/-- **Sharp bad side:** `ε_mca(C, 2/5) ≥ 10/11`. -/
theorem epsMCA_twoFifth_ge_ten :
    (10 : ℝ≥0∞) / 11 ≤ epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) (2/5) := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (Fin 5 → F11)) (2/5) ubadTop GbadTop mcaEventTop_of_mem_GbadTop
  have hG : (GbadTop.card : ℝ≥0∞) = 10 := by rw [show GbadTop.card = 10 from by decide]; norm_num
  have hF : ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 := by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num
  rwa [hG, hF] at h

/-! ## The good side on `[0, 2/5)` -/

/-- Below `δ = 2/5` every legal witness set has size at least `n − 1 = 4`. -/
theorem forced_pred_of_lt_twoFifth {δ : ℝ≥0} (hδ : δ < 2 / 5) :
    ∀ T : Finset (Fin 5),
      ((1 : ℝ≥0) - δ) * (Fintype.card (Fin 5) : ℝ≥0) ≤ (T.card : ℝ≥0) →
        Fintype.card (Fin 5) - 1 ≤ T.card := by
  intro T hT
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ twoFifth_le_one)
  have hδR : (δ : ℝ) < 2/5 := by exact_mod_cast hδ
  have hT' : ((1 : ℝ) - (δ : ℝ)) * 5 ≤ (T.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hT
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one,
      show ((Fintype.card (Fin 5) : ℝ≥0) : ℝ) = 5 by norm_num [Fintype.card_fin]] at h
  have h3 : (3 : ℝ) < (T.card : ℝ) := by nlinarith
  have h4 : 4 ≤ T.card := by
    have : 3 < T.card := by exact_mod_cast h3
    omega
  simp only [Fintype.card_fin]; omega

/-- **Good side:** `ε_mca(C, δ) ≤ 5/11` for every `δ < 2/5`. -/
theorem epsMCA_le_of_lt_twoFifth {δ : ℝ≥0} (hδ : δ < 2 / 5) :
    epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) δ ≤ 5 / 11 := by
  have h := MCAWitnessSpread.epsMCA_le_card_div_of_forced_pred C δ
    (forced_pred_of_lt_twoFifth hδ)
  have hι : ((Fintype.card (Fin 5) : ℕ) : ℝ≥0∞) = 5 := by
    rw [Fintype.card_fin]; norm_num
  have hF : ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 := by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num
  rwa [hι, hF] at h

/-! ## The pin -/

/-- `1/2 < 6/11` in `ℝ≥0∞`. -/
theorem half_lt_sixEleven : (1 / 2 : ℝ≥0∞) < 6 / 11 := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- `5/11 ≤ 1/2` in `ℝ≥0∞`. -/
theorem fiveEleven_le_half : (5 / 11 : ℝ≥0∞) ≤ 1 / 2 := by
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- **Bad-side bracket input:** `ε* = 1/2 < ε_mca(C, 2/5)`. -/
theorem epsMCA_twoFifth_gt :
    (1 / 2 : ℝ≥0∞) < epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) (2/5) :=
  lt_of_lt_of_le half_lt_sixEleven epsMCA_twoFifth_ge

/-- **Good-radius membership, interval form:** every `δ < 2/5` is a good radius for any threshold
`ε* ≥ 5/11`. -/
theorem mem_goodRadii_of_lt_twoFifth_of_fiveEleven_le {δ : ℝ≥0} (hδ : δ < 2 / 5)
    {εstar : ℝ≥0∞} (hε : (5 / 11 : ℝ≥0∞) ≤ εstar) :
    δ ∈ MCAThresholdLedger.mcaGoodRadii (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar := by
  refine ⟨le_of_lt (lt_of_lt_of_le hδ twoFifth_le_one), ?_⟩
  exact le_trans (epsMCA_le_of_lt_twoFifth hδ) hε

/-- **Good-radius membership:** every `δ < 2/5` is a good radius at `ε* = 1/2`. -/
theorem mem_goodRadii_of_lt_twoFifth {δ : ℝ≥0} (hδ : δ < 2 / 5) :
    δ ∈ MCAThresholdLedger.mcaGoodRadii (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) (1/2 : ℝ≥0∞) :=
  mem_goodRadii_of_lt_twoFifth_of_fiveEleven_le hδ fiveEleven_le_half

/-- **Interval pin:** the exact value persists for every threshold in the whole bracket
`5/11 ≤ ε* < 6/11`. -/
theorem mcaDeltaStar_eq_twoFifth_of_fiveEleven_le_of_lt_sixEleven {εstar : ℝ≥0∞}
    (hlo : (5 / 11 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 6 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 2/5 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi epsMCA_twoFifth_ge))
    ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hmem := mem_goodRadii_of_lt_twoFifth_of_fiveEleven_le hc2 hlo
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F11) (A := F11)
    (C : Set (Fin 5 → F11)) εstar hmem.1 hmem.2
  exact absurd hle (not_le.mpr hc1)

/-- **THE PIN — an exact `δ*` value strictly above the Johnson radius.**

For `C = RS[F₁₁, H₅, 2]` (smooth domain of size `5`, rate `2/5`) at `ε* = 1/2`:

  `mcaDeltaStar C (1/2) = 2/5`.

Upper bracket: `δ = 2/5` is bad (`ε_mca ≥ 6/11 > 1/2`, explicit 6-scalar stack). Lower bracket:
every `δ < 2/5` is good (`ε_mca ≤ 5/11 ≤ 1/2`, forced-codimension-one barrier), and `ℝ≥0` is
densely ordered, so the supremum reaches `2/5`.  Since `Johnson = 1 − √(2/5) ≈ 0.368 < 0.4 = δ*`,
this is an exact `δ*` above the Johnson list-decoding radius. -/
theorem mcaDeltaStar_eq_twoFifth :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) (1/2 : ℝ≥0∞) = 2/5 :=
  mcaDeltaStar_eq_twoFifth_of_fiveEleven_le_of_lt_sixEleven
    fiveEleven_le_half half_lt_sixEleven

/-! ## The bottom band: `mcaDeltaStar(C, ε*) = 0` for `ε* < 1/11` -/

/-- The zero-band bad stack: first row is the zero codeword, second row is a non-codeword. -/
def ubadZero : WordStack F11 (Fin 2) (Fin 5) := ![lineEval 0 0, u₁]

@[simp] theorem ubadZero_zero : ubadZero 0 = lineEval 0 0 := rfl
@[simp] theorem ubadZero_one : ubadZero 1 = u₁ := rfl

/-- The witness-cardinality clause at `δ = 0`, `n = 5`, for the full domain. -/
theorem card_cond_zero :
    (((Finset.univ : Finset (Fin 5)).card : ℝ≥0) ≥
      ((1 : ℝ≥0) - 0) * (Fintype.card (Fin 5) : ℝ≥0)) := by
  norm_num [Fintype.card_fin]

/-- `γ = 0` is already bad at `δ = 0`: the first row is the zero codeword on the full domain,
while the second row is not explainable by any degree-`< 2` codeword. -/
theorem mcaEvent_zero_g0 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) 0 (lineEval 0 0) u₁ (0 : F11) := by
  refine ⟨Finset.univ, card_cond_zero, ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The zero-band bad-scalar set: one scalar out of eleven. -/
def GbadZero : Finset F11 := {0}

theorem mcaEvent_zero_of_mem_GbadZero :
    ∀ γ ∈ GbadZero,
      mcaEvent (F := F11) (C : Set (Fin 5 → F11)) 0 (ubadZero 0) (ubadZero 1) γ := by
  intro γ hγ
  rw [ubadZero_zero, ubadZero_one]
  simp only [GbadZero, Finset.mem_singleton] at hγ
  rw [hγ]
  exact mcaEvent_zero_g0

/-- **Bad side (zero band):** `ε_mca(C, 0) ≥ 1/11`. -/
theorem epsMCA_zero_ge :
    (1 : ℝ≥0∞) / 11 ≤ epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) 0 := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (Fin 5 → F11)) 0 ubadZero GbadZero mcaEvent_zero_of_mem_GbadZero
  have hG : (GbadZero.card : ℝ≥0∞) = 1 := by
    rw [show GbadZero.card = 1 from by decide]; norm_num
  have hF : ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 := by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num
  rwa [hG, hF] at h

/-- **Interval pin (bottom band):** if the threshold is below the unavoidable one-scalar event,
then no positive radius is good and `mcaDeltaStar(C, ε*) = 0`. -/
theorem mcaDeltaStar_eq_zero_of_lt_oneEleven {εstar : ℝ≥0∞}
    (hhi : εstar < 1 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 0 := by
  refine le_antisymm ?_ (zero_le _)
  exact MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hhi epsMCA_zero_ge)

/-! ## The lower jump: `mcaDeltaStar(C, ε*) = 1/5` for `ε* ∈ [1/11, 2/11)`

Completing the threshold characterization of `C`: the step function `ε_mca(C, ·)` has its first
jump at `δ = 1/5` (from `1/11` to `2/11`).  So for thresholds in the first band the exact `δ*`
sits at `1/5` (below the unique-decoding radius `0.3`), the complement of the above-Johnson pin. -/

/-- `(1/5 : ℝ≥0) ≤ 1`. -/
theorem fifth_le_one : (1/5 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num : (0 : ℝ≥0) < 5)]; norm_num

/-- Second row of the first-jump bad stack (the line row `u₀ = (0,0,0,0,1)` is shared). -/
def u₁' : Fin 5 → F11 := ![2, 4, 8, 3, 10]

/-- The first-jump bad stack. -/
def ubad' : WordStack F11 (Fin 2) (Fin 5) := ![u₀, u₁']

@[simp] theorem ubad'_zero : ubad' 0 = u₀ := rfl
@[simp] theorem ubad'_one : ubad' 1 = u₁' := rfl

/-- Witness-cardinality clause at `δ = 1/5`, `n = 5`, for a 4-element set. -/
theorem card_cond' {S : Finset (Fin 5)} (h : S.card = 4) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - (1/5 : ℝ≥0)) * (Fintype.card (Fin 5) : ℝ≥0) := by
  have h45 : ((1 : ℝ≥0) - (1/5 : ℝ≥0)) * (Fintype.card (Fin 5) : ℝ≥0) = 4 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub fifth_le_one]
    push_cast [Fintype.card_fin]; norm_num
  rw [ge_iff_le, h45, h]; norm_num

/-- `γ = 0` is bad at `δ = 1/5`: witness set `{0,1,2,3}`, interpolating codeword `0`. -/
theorem mcaEvent'_g0 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (1/5) u₀ u₁' (0 : F11) := by
  refine ⟨{0, 1, 2, 3}, card_cond' (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 2` is bad at `δ = 1/5`: witness set `{0,2,3,4}`, interpolating codeword `1 + 3X`. -/
theorem mcaEvent'_g2 :
    mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (1/5) u₀ u₁' (2 : F11) := by
  refine ⟨{0, 2, 3, 4}, card_cond' (by decide), ⟨lineEval 1 3, lineEval_mem 1 3, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The first-jump bad-scalar set: 2 of the 11 scalars. -/
def Gbad' : Finset F11 := {0, 2}

theorem mcaEvent'_of_mem_Gbad' :
    ∀ γ ∈ Gbad', mcaEvent (F := F11) (C : Set (Fin 5 → F11)) (1/5) (ubad' 0) (ubad' 1) γ := by
  intro γ hγ
  rw [ubad'_zero, ubad'_one]
  simp only [Gbad', Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl
  · exact mcaEvent'_g0
  · exact mcaEvent'_g2

/-- **Bad side (first jump):** `ε_mca(C, 1/5) ≥ 2/11`. -/
theorem epsMCA_fifth_ge :
    (2 : ℝ≥0∞) / 11 ≤ epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) (1/5) := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (Fin 5 → F11)) (1/5) ubad' Gbad' mcaEvent'_of_mem_Gbad'
  have hG : (Gbad'.card : ℝ≥0∞) = 2 := by rw [show Gbad'.card = 2 from by decide]; norm_num
  have hF : ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 := by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num
  rwa [hG, hF] at h

/-- Below `δ = 1/5` the witness set is forced to be all of `Fin 5`. -/
theorem forced_univ_of_lt_fifth {δ : ℝ≥0} (hδ : δ < 1 / 5) :
    ∀ T : Finset (Fin 5),
      ((1 : ℝ≥0) - δ) * (Fintype.card (Fin 5) : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ := by
  intro T hT
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ fifth_le_one)
  have hδR : (δ : ℝ) < 1/5 := by exact_mod_cast hδ
  have hT' : ((1 : ℝ) - (δ : ℝ)) * 5 ≤ (T.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hT
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one,
      show ((Fintype.card (Fin 5) : ℝ≥0) : ℝ) = 5 by norm_num [Fintype.card_fin]] at h
  have h4 : (4 : ℝ) < (T.card : ℝ) := by nlinarith
  have h5 : 5 ≤ T.card := by
    have : 4 < T.card := by exact_mod_cast h4
    omega
  apply Finset.eq_univ_of_card
  have hle : T.card ≤ 5 := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ T
  simp only [Fintype.card_fin]; omega

/-- **Good side (first band):** `ε_mca(C, δ) ≤ 1/11` for every `δ < 1/5`. -/
theorem epsMCA_le_of_lt_fifth {δ : ℝ≥0} (hδ : δ < 1 / 5) :
    epsMCA (F := F11) (A := F11) (C : Set (Fin 5 → F11)) δ ≤ 1 / 11 := by
  have h := MCAWitnessSpread.epsMCA_le_inv_card_of_forced_univ C δ (forced_univ_of_lt_fifth hδ)
  rwa [show ((Fintype.card F11 : ℕ) : ℝ≥0∞) = 11 from by
    rw [show Fintype.card F11 = 11 from by simp [ZMod.card]]; norm_num] at h

/-- `1/11 < 2/11` in `ℝ≥0∞`. -/
theorem oneEleven_lt_twoEleven : (1 / 11 : ℝ≥0∞) < 2 / 11 := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- `2/11 < 3/11` in `ℝ≥0∞`. -/
theorem twoEleven_lt_threeEleven : (2 / 11 : ℝ≥0∞) < 3 / 11 := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- `2/11 ≤ 1/2` in `ℝ≥0∞`. -/
theorem twoEleven_le_half : (2 / 11 : ℝ≥0∞) ≤ 1 / 2 := by
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- `6/11 < 10/11` in `ℝ≥0∞`. -/
theorem sixEleven_lt_tenEleven : (6 / 11 : ℝ≥0∞) < 10 / 11 := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- **Interval pin (first jump):** `mcaDeltaStar(C, ε*) = 1/5` for every `ε* ∈ [1/11, 2/11)`. -/
theorem mcaDeltaStar_eq_fifth_of_oneEleven_le_of_lt_twoEleven {εstar : ℝ≥0∞}
    (hlo : (1 / 11 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 2 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 1/5 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi epsMCA_fifth_ge)) ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hmem : c ∈ MCAThresholdLedger.mcaGoodRadii (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar := by
    refine ⟨le_of_lt (lt_of_lt_of_le hc2 fifth_le_one), ?_⟩
    exact le_trans (epsMCA_le_of_lt_fifth hc2) hlo
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F11) (A := F11)
    (C : Set (Fin 5 → F11)) εstar hmem.1 hmem.2
  exact absurd hle (not_le.mpr hc1)

/-! ## The first middle granularity band: `mcaDeltaStar(C, ε*) = 2/5` for
`ε* ∈ [2/11, 3/11)`

The generic Reed–Solomon granularity ladder applies to the concrete affine presentation of `C`
after the local equality `C_eq_rsCode_two`.  This discharges the first missing middle band without
adding a new scalar enumeration. -/

/-- **Interval pin (granularity band):** `mcaDeltaStar(C, ε*) = 2/5` for every
`ε* ∈ [2/11, 3/11)`. -/
theorem mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_threeEleven {εstar : ℝ≥0∞}
    (hlo : (2 / 11 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 3 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 2/5 := by
  have hlo' : ((2 : ℕ) : ℝ≥0∞) / (Fintype.card F11 : ℝ≥0∞) ≤ εstar := by
    simpa [F11, ZMod.card] using hlo
  have hhi' :
      εstar < (((2 + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F11 : ℝ≥0∞)) := by
    simpa [F11, ZMod.card] using hhi
  rw [C_eq_rsCode_two]
  simpa [Fintype.card_fin] using
    (ProximityGap.SpikeFloor.mcaDeltaStar_rs_eq_granularity
      (F := F11) (n := 5) (dom := domEmb) (k := 2) (j := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo' hhi')

/-! ## The closed middle band: `mcaDeltaStar(C, ε*) = 2/5` for `ε* ∈ [2/11, 6/11)`

The ladder pin at the left endpoint `ε* = 2/11` lower-bounds every looser budget by threshold
monotonicity.  The existing explicit six-scalar bad stack at radius `2/5` upper-bounds every budget
below `6/11`. -/

/-- **Interval pin (closed middle band):** `mcaDeltaStar(C, ε*) = 2/5` for every
`ε* ∈ [2/11, 6/11)`. -/
theorem mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_sixEleven {εstar : ℝ≥0∞}
    (hlo : (2 / 11 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 6 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 2/5 := by
  have hpin :
      MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
        (C : Set (Fin 5 → F11)) (2 / 11 : ℝ≥0∞) = 2/5 :=
    mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_threeEleven
      (εstar := (2 / 11 : ℝ≥0∞)) le_rfl twoEleven_lt_threeEleven
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi epsMCA_twoFifth_ge)) ?_
  rw [← hpin]
  exact MCAThresholdLedger.mcaDeltaStar_mono (F := F11) (A := F11)
    (C := (C : Set (Fin 5 → F11))) hlo

/-- The above-Johnson point pin also follows from the closed middle band. -/
theorem mcaDeltaStar_eq_twoFifth_via_middle_band :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) (1/2 : ℝ≥0∞) = 2/5 :=
  mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_sixEleven
    twoEleven_le_half half_lt_sixEleven

/-! ## The sharp second-jump band: `mcaDeltaStar(C, ε*) = 2/5` for `ε* ∈ [2/11, 10/11)`

Replacing the six-scalar bad stack with `ubadTop` upgrades the upper bracket to the exact
second-jump value from the exhaustive profile.  The lower bracket is still the same
budget-monotonicity transport from the `ε* = 2/11` ladder pin. -/

/-- **Interval pin (sharp second-jump band):** `mcaDeltaStar(C, ε*) = 2/5` for every
`ε* ∈ [2/11, 10/11)`. -/
theorem mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_tenEleven {εstar : ℝ≥0∞}
    (hlo : (2 / 11 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 10 / 11) :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) εstar = 2/5 := by
  have hpin :
      MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
        (C : Set (Fin 5 → F11)) (2 / 11 : ℝ≥0∞) = 2/5 :=
    mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_threeEleven
      (εstar := (2 / 11 : ℝ≥0∞)) le_rfl twoEleven_lt_threeEleven
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi epsMCA_twoFifth_ge_ten))
    ?_
  rw [← hpin]
  exact MCAThresholdLedger.mcaDeltaStar_mono (F := F11) (A := F11)
    (C := (C : Set (Fin 5 → F11))) hlo

/-- The above-Johnson point pin via the sharp second-jump band. -/
theorem mcaDeltaStar_eq_twoFifth_via_sharp_band :
    MCAThresholdLedger.mcaDeltaStar (F := F11) (A := F11)
      (C : Set (Fin 5 → F11)) (1/2 : ℝ≥0∞) = 2/5 :=
  mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_tenEleven
    twoEleven_le_half (lt_trans half_lt_sixEleven sixEleven_lt_tenEleven)

/-! ## Source audit -/

#print axioms epsMCA_twoFifth_ge
#print axioms epsMCA_twoFifth_ge_ten
#print axioms epsMCA_le_of_lt_twoFifth
#print axioms mcaDeltaStar_eq_twoFifth_of_fiveEleven_le_of_lt_sixEleven
#print axioms mcaDeltaStar_eq_twoFifth
#print axioms epsMCA_zero_ge
#print axioms mcaDeltaStar_eq_zero_of_lt_oneEleven
#print axioms epsMCA_fifth_ge
#print axioms mcaDeltaStar_eq_fifth_of_oneEleven_le_of_lt_twoEleven
#print axioms C_eq_rsCode_two
#print axioms mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_threeEleven
#print axioms mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_sixEleven
#print axioms mcaDeltaStar_eq_twoFifth_via_middle_band
#print axioms mcaDeltaStar_eq_twoFifth_of_twoEleven_le_of_lt_tenEleven
#print axioms mcaDeltaStar_eq_twoFifth_via_sharp_band

end ProximityGap.DeltaStarPinF11H5
