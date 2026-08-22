/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# An exact `δ*` point for `RS[F₁₃, ⟨5⟩, 2]`, and an honest above-Johnson **no-go**

Lane `L3-F13-order4`.  The code is `C = RS[F₁₃, H₄, 2]`: degree-`< 2` polynomials evaluated on
the order-`4` multiplicative subgroup `H₄ = ⟨5⟩ = (5⁰, 5¹, 5², 5³) = (1, 5, 12, 8) ⊂ F₁₃*`
(a smooth domain of size `n = 4 = 2²`).  Rate `ρ = 2/4 = 1/2`, so:

  * unique-decoding radius `(1−ρ)/2 = 1/4 = 0.25`,
  * Johnson radius `1 − √ρ = 1 − √(1/2) ≈ 0.293`,
  * capacity `1 − ρ = 1/2 = 0.5`.

## The exact ground truth (probe `scripts/probes/probe_deltastar_f13_order4.py`, exact arithmetic)

The MCA error `ε_mca(C, ·)` is a **two-step** function:

  `ε_mca(C, δ) = 1/13` for `δ ∈ [0, 1/4)`,  and  `= 4/13` for `δ ∈ [1/4, 1]`.

The *only* nondegenerate jump is at `δ = 1/4`, from `1/13` to `4/13`, and the maximum value
`4/13 ≈ 0.308` is attained for **all** `δ ≥ 1/4` (the bad-scalar count tops out at `n = 4`,
so `ε_mca ≤ n/q = 4/13`).

## ⚠ Honest above-Johnson no-go (the assigned target is impossible for this code)

The lane goal was a window-interior `δ*` strictly **above** Johnson at the threshold `ε* = 1/2`.
For this code that is **mathematically impossible**: since `ε_mca(C, δ) ≤ 4/13 < 1/2` for every
`δ ∈ [0, 1]`, the threshold `1/2` is never crossed, so

  `mcaDeltaStar (C : Set (Fin 4 → F₁₃)) (1/2) = 1`  (degenerate, top of the radius interval),

which is **not** a window-interior pin.  The unique nondegenerate jump sits at `δ* = 1/4 = UDR`,
*below* the Johnson radius `0.293`.  Concretely there is **no** threshold `ε*` for which this
code's exact `δ*` lands strictly above Johnson: for `ε* ∈ [1/13, 4/13)` the pin is `δ* = 1/4`
(below Johnson), and for `ε* ∈ [4/13, 1]` it is the degenerate `δ* = 1`.  The reason is the tiny
`n/q = 4/13` ceiling: with `n = 4` the worst stack has at most `n = 4` bad scalars, and `4/13`
never reaches the `> ε*` regime in the above-Johnson radius band.  (Contrast the `F₁₁` pin, where
`n = 5`, `q = 11` give a `6/11 > 1/2` bad count at `δ = 2/5` above Johnson.)

This is a *valid finding*, reported per the lane instructions: a code whose `δ*` is **not** above
Johnson.

## What IS proven here (exact, axiom-clean): the `δ = 1/4` jump pin

We machine-check the genuine exact threshold value at the (sub-Johnson) jump:

  `mcaDeltaStar (C : Set (Fin 4 → F₁₃)) ε* = 1/4`  for every `ε* ∈ [1/13, 4/13)`.

* **Bad side (one explicit stack).** The probe-extracted stack `u₀ = (7,8,0,0)`,
  `u₁ = (12,12,0,0)` has `4` of `13` scalars bad at `δ = 1/4`; each badness certificate is an
  explicit `3`-element witness set, an explicit interpolating codeword, and a `decide`d
  non-explainability of the row `u₁`.  Hence `ε_mca(C, 1/4) ≥ 4/13 > ε*`.
* **Good side (substrate, no enumeration).** For every `δ < 1/4` the witness-cardinality clause
  forces each legal `mcaEvent` witness set to be all of `Fin 4`, so the forced-universal-witness
  barrier `MCAWitnessSpread.epsMCA_le_inv_card_of_forced_univ` gives `ε_mca(C, δ) ≤ 1/13 ≤ ε*`.
* **Assembly.** The two `MCAThresholdLedger` bracket lemmas plus density of `ℝ≥0` pin the `sSup`.

These are exact small-code pins; they do **not** close the Proximity Prize — the prize regime is
`n = 2^30` at `ε* = 2^-128`, the open BGK / Paley wall.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3: `mcaEvent`/`epsMCA`.)
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ProximityGap.DeltaStarPinF13Order4

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

/-! ## The concrete code `RS[F₁₃, H₄, 2]` -/

/-- The field `F₁₃`. -/
abbrev F13 := ZMod 13

instance primeFact_DeltaStarPinF13Order4Deg2_1 : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- `(1/4 : ℝ≥0) ≤ 1`, the recurring radius-sanity fact. -/
theorem quarter_le_one : (1/4 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]; norm_num

/-- The smooth evaluation domain `H₄ = ⟨5⟩ = (5⁰, 5¹, 5², 5³) = (1, 5, 12, 8)`, the unique
order-`4` multiplicative subgroup of `F₁₃*`. -/
def dom : Fin 4 → F13 := ![1, 5, 12, 8]

/-- The codeword of the polynomial `a + b·X`, evaluated on `dom`. -/
def lineEval (a b : F13) : Fin 4 → F13 := fun i => a + b * dom i

/-- `RS[F₁₃, H₄, 2]` — evaluations of degree-`< 2` polynomials on `dom` — as a submodule. -/
def C : Submodule F13 (Fin 4 → F13) where
  carrier := {w | ∃ a b : F13, w = lineEval a b}
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

theorem lineEval_mem (a b : F13) : lineEval a b ∈ (C : Set (Fin 4 → F13)) := ⟨a, b, rfl⟩

/-- Explainability of a single row on a coordinate set (decidable finite search). -/
def ExplainableOn (S : Finset (Fin 4)) (w : Fin 4 → F13) : Prop :=
  ∃ a b : F13, ∀ i ∈ S, lineEval a b i = w i

instance (S : Finset (Fin 4)) (w : Fin 4 → F13) : Decidable (ExplainableOn S w) := by
  unfold ExplainableOn; infer_instance

theorem explainableOn_iff (S : Finset (Fin 4)) (w : Fin 4 → F13) :
    (∃ v ∈ (C : Set (Fin 4 → F13)), ∀ i ∈ S, v i = w i) ↔ ExplainableOn S w := by
  constructor
  · rintro ⟨v, ⟨a, b, rfl⟩, h⟩; exact ⟨a, b, h⟩
  · rintro ⟨a, b, h⟩; exact ⟨lineEval a b, lineEval_mem a b, h⟩

/-- To refute the joint-pair clause it suffices that the second row is not explainable. -/
theorem not_pairJointAgreesOn_of_row1 {S : Finset (Fin 4)} {u₀ u₁ : Fin 4 → F13}
    (h : ¬ ExplainableOn S u₁) :
    ¬ pairJointAgreesOn (C : Set (Fin 4 → F13)) S u₀ u₁ := by
  rw [MCAWitnessSpread.pairJointAgreesOn_iff_split]
  rintro ⟨_, h₁⟩
  exact h ((explainableOn_iff S u₁).mp h₁)

/-! ## The bad stack at `δ = 1/4` (probe-extracted, 4 of 13 scalars bad) -/

def u₀ : Fin 4 → F13 := ![7, 8, 0, 0]
def u₁ : Fin 4 → F13 := ![12, 12, 0, 0]

/-- The bad stack as a `WordStack`. -/
def ubad : WordStack F13 (Fin 2) (Fin 4) := ![u₀, u₁]

@[simp] theorem ubad_zero : ubad 0 = u₀ := rfl
@[simp] theorem ubad_one : ubad 1 = u₁ := rfl

/-- The witness-cardinality clause of `mcaEvent` at `δ = 1/4`, `n = 4`, for a 3-element set. -/
theorem card_cond {S : Finset (Fin 4)} (h : S.card = 3) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - (1/4 : ℝ≥0)) * (Fintype.card (Fin 4) : ℝ≥0) := by
  have h34 : ((1 : ℝ≥0) - (1/4 : ℝ≥0)) * (Fintype.card (Fin 4) : ℝ≥0) = 3 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub quarter_le_one]
    push_cast [Fintype.card_fin]
    norm_num
  rw [ge_iff_le, h34, h]; norm_num

/-- `γ = 0` is bad: witness set `{0,1,2}`, interpolating codeword `10 + 10·X`. -/
theorem mcaEvent_g0 :
    mcaEvent (F := F13) (C : Set (Fin 4 → F13)) (1/4) u₀ u₁ (0 : F13) := by
  refine ⟨{0, 1, 2}, card_cond (by decide), ⟨lineEval 10 10, lineEval_mem 10 10, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 7` is bad: witness set `{0,2,3}`, interpolating codeword `0`. -/
theorem mcaEvent_g7 :
    mcaEvent (F := F13) (C : Set (Fin 4 → F13)) (1/4) u₀ u₁ (7 : F13) := by
  refine ⟨{0, 2, 3}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 8` is bad: witness set `{1,2,3}`, interpolating codeword `0`. -/
theorem mcaEvent_g8 :
    mcaEvent (F := F13) (C : Set (Fin 4 → F13)) (1/4) u₀ u₁ (8 : F13) := by
  refine ⟨{1, 2, 3}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 12` is bad: witness set `{0,1,3}`, interpolating codeword `11 + 10·X`. -/
theorem mcaEvent_g12 :
    mcaEvent (F := F13) (C : Set (Fin 4 → F13)) (1/4) u₀ u₁ (12 : F13) := by
  refine ⟨{0, 1, 3}, card_cond (by decide), ⟨lineEval 11 10, lineEval_mem 11 10, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The bad-scalar set: 4 of the 13 scalars. -/
def Gbad : Finset F13 := {0, 7, 8, 12}

theorem mcaEvent_of_mem_Gbad :
    ∀ γ ∈ Gbad, mcaEvent (F := F13) (C : Set (Fin 4 → F13)) (1/4) (ubad 0) (ubad 1) γ := by
  intro γ hγ
  rw [ubad_zero, ubad_one]
  simp only [Gbad, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · exact mcaEvent_g0
  · exact mcaEvent_g7
  · exact mcaEvent_g8
  · exact mcaEvent_g12

/-- **Bad side:** `ε_mca(C, 1/4) ≥ 4/13`. -/
theorem epsMCA_quarter_ge :
    (4 : ℝ≥0∞) / 13 ≤ epsMCA (F := F13) (A := F13) (C : Set (Fin 4 → F13)) (1/4) := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (Fin 4 → F13)) (1/4) ubad Gbad mcaEvent_of_mem_Gbad
  have hG : (Gbad.card : ℝ≥0∞) = 4 := by rw [show Gbad.card = 4 from by decide]; norm_num
  have hF : ((Fintype.card F13 : ℕ) : ℝ≥0∞) = 13 := by
    rw [show Fintype.card F13 = 13 from by simp [ZMod.card]]; norm_num
  rwa [hG, hF] at h

/-! ## The good side on `[0, 1/4)` -/

/-- Below `δ = 1/4` the witness set is forced to be all of `Fin 4`. -/
theorem forced_univ_of_lt_quarter {δ : ℝ≥0} (hδ : δ < 1 / 4) :
    ∀ T : Finset (Fin 4),
      ((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ := by
  intro T hT
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ quarter_le_one)
  have hδR : (δ : ℝ) < 1/4 := by exact_mod_cast hδ
  have hT' : ((1 : ℝ) - (δ : ℝ)) * 4 ≤ (T.card : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hT
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one,
      show ((Fintype.card (Fin 4) : ℝ≥0) : ℝ) = 4 by norm_num [Fintype.card_fin]] at h
  have h3 : (3 : ℝ) < (T.card : ℝ) := by nlinarith
  have h4 : 4 ≤ T.card := by
    have : 3 < T.card := by exact_mod_cast h3
    omega
  apply Finset.eq_univ_of_card
  have hle : T.card ≤ 4 := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ T
  simp only [Fintype.card_fin]; omega

/-- **Good side:** `ε_mca(C, δ) ≤ 1/13` for every `δ < 1/4`. -/
theorem epsMCA_le_of_lt_quarter {δ : ℝ≥0} (hδ : δ < 1 / 4) :
    epsMCA (F := F13) (A := F13) (C : Set (Fin 4 → F13)) δ ≤ 1 / 13 := by
  have h := MCAWitnessSpread.epsMCA_le_inv_card_of_forced_univ C δ (forced_univ_of_lt_quarter hδ)
  rwa [show ((Fintype.card F13 : ℕ) : ℝ≥0∞) = 13 from by
    rw [show Fintype.card F13 = 13 from by simp [ZMod.card]]; norm_num] at h

/-! ## The pin (sub-Johnson jump at `δ = 1/4`) -/

/-- `1/13 ≤ 4/13` in `ℝ≥0∞`. -/
theorem oneThirteen_le_fourThirteen : (1 / 13 : ℝ≥0∞) ≤ 4 / 13 := by
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp))
        (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- **Interval pin:** the exact value `δ* = 1/4` persists for every threshold in the whole bracket
`1/13 ≤ ε* < 4/13`. -/
theorem mcaDeltaStar_eq_quarter_of_oneThirteen_le_of_lt_fourThirteen {εstar : ℝ≥0∞}
    (hlo : (1 / 13 : ℝ≥0∞) ≤ εstar) (hhi : εstar < 4 / 13) :
    MCAThresholdLedger.mcaDeltaStar (F := F13) (A := F13)
      (C : Set (Fin 4 → F13)) εstar = 1/4 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi epsMCA_quarter_ge))
    ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hmem : c ∈ MCAThresholdLedger.mcaGoodRadii (F := F13) (A := F13)
      (C : Set (Fin 4 → F13)) εstar := by
    refine ⟨le_of_lt (lt_of_lt_of_le hc2 quarter_le_one), ?_⟩
    exact le_trans (epsMCA_le_of_lt_quarter hc2) hlo
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F13) (A := F13)
    (C : Set (Fin 4 → F13)) εstar hmem.1 hmem.2
  exact absurd hle (not_le.mpr hc1)

/-- **THE PIN — the exact `δ*` value at the (sub-Johnson) jump of `RS[F₁₃, H₄, 2]`.**

For `C = RS[F₁₃, H₄, 2]` (smooth domain of size `4 = 2²`, rate `1/2`) at `ε* = 1/13`:

  `mcaDeltaStar C (1/13) = 1/4`.

Upper bracket: `δ = 1/4` is bad (`ε_mca ≥ 4/13 > 1/13`, explicit 4-scalar stack). Lower bracket:
every `δ < 1/4` is good (`ε_mca ≤ 1/13`, forced-universal-witness barrier), and `ℝ≥0` is densely
ordered, so the supremum reaches `1/4`.  Here `δ* = 1/4 = (1−ρ)/2` is the **unique-decoding
radius**, which lies *below* the Johnson radius `1 − √(1/2) ≈ 0.293`: an honest sub-Johnson pin.
See the file header for the above-Johnson **no-go** at `ε* = 1/2` (`mcaDeltaStar C (1/2) = 1`,
degenerate). -/
theorem mcaDeltaStar_eq_quarter :
    MCAThresholdLedger.mcaDeltaStar (F := F13) (A := F13)
      (C : Set (Fin 4 → F13)) (1/13 : ℝ≥0∞) = 1/4 :=
  mcaDeltaStar_eq_quarter_of_oneThirteen_le_of_lt_fourThirteen
    le_rfl (by
      rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp))
            (ENNReal.div_ne_top (by simp) (by simp))]
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
      norm_num)

/-! ## Source audit -/

#print axioms epsMCA_quarter_ge
#print axioms epsMCA_le_of_lt_quarter
#print axioms mcaDeltaStar_eq_quarter_of_oneThirteen_le_of_lt_fourThirteen
#print axioms mcaDeltaStar_eq_quarter

end ProximityGap.DeltaStarPinF13Order4
