/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
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
* **Bad side (one explicit stack).**  The probe-extracted stack `u₀ = (0,0,0,0,1)`,
  `u₁ = (8,3,4,5,9)` has `6` of `11` scalars bad at `δ = 2/5`; each badness certificate is an
  explicit `3`-element witness set, an explicit interpolating codeword, and a `decide`d
  non-explainability of the row `u₁`.  Hence `ε_mca(C, 2/5) ≥ 6/11 > 1/2`.
* **Assembly.**  The two `MCAThresholdLedger` bracket lemmas plus density of `ℝ≥0` pin the `sSup`.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3: `mcaEvent`/`epsMCA`.)
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.DeltaStarPinF11H5

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

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

/-! ## Source audit -/

#print axioms epsMCA_twoFifth_ge
#print axioms epsMCA_le_of_lt_twoFifth
#print axioms mcaDeltaStar_eq_twoFifth_of_fiveEleven_le_of_lt_sixEleven
#print axioms mcaDeltaStar_eq_twoFifth

end ProximityGap.DeltaStarPinF11H5
