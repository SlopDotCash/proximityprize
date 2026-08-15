/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The first machine-checked exact `δ*` point: `mcaDeltaStar(RS[F₅, F₅*, 2], 2/5) = 1/4`

The Grand MCA Challenge (#357, predecessors #232/#334) asks for the exact MCA threshold
`δ* = sup {δ | ε_mca(C, δ) ≤ ε*}` of explicit smooth-domain Reed–Solomon codes. The literature
only ever *bounds* `ε_mca`; no exact value of the **MCA threshold** `mcaDeltaStar` has been
certified for any code, by any group, in any proof format (the in-tree F17 pins —
`DeltaStarConcretePinF17`, `DeltaStarExactCrossoverF17` — are *list-size* brackets/crossovers,
a different quantity). This file produces the first one, at the smallest genuinely smooth
instance: `C = RS[F₅, F₅*, 2]` — evaluations of polynomials of degree `< 2` on the full
multiplicative group `F₅* = {2⁰, 2¹, 2², 2³} = (1,2,4,3)`, a smooth domain of size `n = 4 = 2²`,
rate `ρ = 1/2`. With threshold `ε* = 2/5` (i.e. `2/|F|`):

  `mcaDeltaStar (C : Set (Fin 4 → F₅)) (2/5) = 1/4`.

The exact ground truth (probe `scripts/probes/probe_exact_epsmca_ladder.py`, exact arithmetic,
syndrome-reduced engine cross-validated against the naive engine): `ε_mca(C, δ) = 1/5` for
`δ ∈ [0, 1/4)` and `= 4/5` for `δ ∈ [1/4, 1]` — a pure step function, so `δ*` sits **exactly at
the jump** `1/4` and the supremum is not attained. Note `1/4 = (1−ρ)/2` — at this toy scale and
this `ε*`, `δ*` is the unique-decoding radius.

## Proof architecture (no orbit enumeration needed)

* **Good side, pure algebra** (`badScalar_card_le_one_of_forced_univ`): for radii `δ` with
  `(1−δ)·n > n−1` the `mcaEvent` witness set is forced to be all of `ι`; *all* bad scalars then
  share the single witness set `univ`, and `MCAWitnessSpread.unique_bad_gamma_common_witness`
  (the structural obstruction lemma) collapses them to at most one. Hence
  `ε_mca(C, δ) ≤ 1/|F|` for **every** submodule code — no computation, generalizing the
  `ZMod 2`/zero-code-specific bounds of `MCALowerBound`/`MCAZeroCodeExact`.
* **Bad side, one explicit stack** (`mcaEvent` × 4 + `epsMCA_ge_card_div_of_mcaEvent_set`):
  the probe-extracted stack `u₀ = (0,0,0,1)`, `u₁ = (0,0,1,1)` has 4 of 5 scalars bad at
  `δ = 1/4`; each badness certificate is an explicit witness set, an explicit interpolating
  codeword (kernel-checked), and a `decide`d non-explainability of the row `u₁`.
* **Assembly**: the two `MCAThresholdLedger` bracket lemmas plus density of `ℝ≥0` pin the
  `sSup` exactly.

Also recorded: the exact value `ε_mca(C, δ) = 1/5` on the whole interval `[0, 1/4)`
(`epsMCA_C542_eq_inv_card_of_lt_quarter`), and the general `pairJointAgreesOn` split
(`pairJointAgreesOn_iff_split`): the joint-pair clause always decouples into two independent
per-row explainability clauses.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3: `mcaEvent`/`epsMCA`.)
* Issue #357 (δ* tracker), hypothesis R1 of the 2026-06-11 nine-hypothesis dossier
  (`docs/wiki/deltastar-357-nine-hypotheses-2026-06.md`).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.DeltaStarExactPin

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

/-! ## The concrete code `RS[F₅, F₅*, 2]` -/

/-- The field `F₅`. -/
abbrev F5 := ZMod 5

instance primeFact_DeltaStarExactPinF5_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- `(1/4 : ℝ≥0) ≤ 1`, the recurring radius-sanity fact. -/
theorem quarter_le_one : (1/4 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
  norm_num

/-- The smooth evaluation domain: `F₅* = ⟨2⟩` enumerated as successive powers of the
generator `2`, i.e. `(2⁰, 2¹, 2², 2³) = (1, 2, 4, 3)`. A multiplicative subgroup of size
`4 = 2²` — the smallest genuinely smooth RS domain. -/
def dom : Fin 4 → F5 := ![1, 2, 4, 3]

/-- The codeword of the polynomial `a + b·X`, evaluated on `dom`. -/
def lineEval (a b : F5) : Fin 4 → F5 := fun i => a + b * dom i

/-- `RS[F₅, F₅*, 2]` — evaluations of degree-`< 2` polynomials on `dom` — as a submodule of
`Fin 4 → F₅`. Rate `ρ = 2/4 = 1/2`; unique-decoding radius `(1−ρ)/2 = 1/4`; Johnson radius
`1 − √ρ ≈ 0.293`; capacity `1 − ρ = 1/2`. -/
def C542 : Submodule F5 (Fin 4 → F5) where
  carrier := {w | ∃ a b : F5, w = lineEval a b}
  add_mem' := by
    rintro w w' ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a + a', b + b', ?_⟩
    funext i
    change lineEval a b i + lineEval a' b' i = lineEval (a + a') (b + b') i
    simp only [lineEval]
    ring
  zero_mem' := ⟨0, 0, by funext i; simp [lineEval]⟩
  smul_mem' := by
    rintro c w ⟨a, b, rfl⟩
    refine ⟨c * a, c * b, ?_⟩
    funext i
    change c • lineEval a b i = lineEval (c * a) (c * b) i
    simp only [lineEval, smul_eq_mul]
    ring

theorem lineEval_mem (a b : F5) : lineEval a b ∈ (C542 : Set (Fin 4 → F5)) :=
  ⟨a, b, rfl⟩

theorem mem_C542_iff (w : Fin 4 → F5) :
    w ∈ (C542 : Set (Fin 4 → F5)) ↔ ∃ a b : F5, w = lineEval a b :=
  Iff.rfl

/-- Explainability of a single row on a coordinate set: some codeword agrees with `w`
everywhere on `S`. Decidable (a finite search over the 25 codewords). -/
def ExplainableOn (S : Finset (Fin 4)) (w : Fin 4 → F5) : Prop :=
  ∃ a b : F5, ∀ i ∈ S, lineEval a b i = w i

instance (S : Finset (Fin 4)) (w : Fin 4 → F5) : Decidable (ExplainableOn S w) := by
  unfold ExplainableOn; infer_instance

theorem explainableOn_iff (S : Finset (Fin 4)) (w : Fin 4 → F5) :
    (∃ v ∈ (C542 : Set (Fin 4 → F5)), ∀ i ∈ S, v i = w i) ↔ ExplainableOn S w := by
  constructor
  · rintro ⟨v, ⟨a, b, rfl⟩, h⟩
    exact ⟨a, b, h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨lineEval a b, lineEval_mem a b, h⟩

/-- To refute the joint-pair clause it suffices that the second row is not explainable. -/
theorem not_pairJointAgreesOn_of_row1 {S : Finset (Fin 4)} {u₀ u₁ : Fin 4 → F5}
    (h : ¬ ExplainableOn S u₁) :
    ¬ pairJointAgreesOn (C542 : Set (Fin 4 → F5)) S u₀ u₁ := by
  rw [MCAWitnessSpread.pairJointAgreesOn_iff_split]
  rintro ⟨_, h₁⟩
  exact h ((explainableOn_iff S u₁).mp h₁)

/-! ## The bad stack at `δ = 1/4` (probe-extracted, 4 of 5 scalars bad) -/

/-- First row of the bad stack. Not a codeword (it vanishes at `1, 2, 4` but not `3`). -/
def u₀ : Fin 4 → F5 := ![0, 0, 0, 1]

/-- Second row of the bad stack. -/
def u₁ : Fin 4 → F5 := ![0, 0, 1, 1]

/-- The bad stack as a `WordStack`. -/
def ubad : WordStack F5 (Fin 2) (Fin 4) := ![u₀, u₁]

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
  rw [ge_iff_le, h34, h]
  norm_num

/-- `γ = 0` is bad: the line is `u₀` itself, which agrees with the zero codeword on
`S = {0,1,2}`, while `u₁` is not explainable on `S`. -/
theorem mcaEvent_g0 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) u₀ u₁ (0 : F5) := by
  refine ⟨{0, 1, 2}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 2` is bad, witness set `{0,2,3}`, interpolating codeword `1 + 4X`. -/
theorem mcaEvent_g2 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) u₀ u₁ (2 : F5) := by
  refine ⟨{0, 2, 3}, card_cond (by decide), ⟨lineEval 1 4, lineEval_mem 1 4, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 3` is bad, witness set `{1,2,3}`, interpolating codeword `2 + 4X`. -/
theorem mcaEvent_g3 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) u₀ u₁ (3 : F5) := by
  refine ⟨{1, 2, 3}, card_cond (by decide), ⟨lineEval 2 4, lineEval_mem 2 4, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- `γ = 4` is bad, witness set `{0,1,3}`, interpolating codeword `0`. -/
theorem mcaEvent_g4 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) u₀ u₁ (4 : F5) := by
  refine ⟨{0, 1, 3}, card_cond (by decide), ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- The bad-scalar set: 4 of the 5 scalars. -/
def Gbad : Finset F5 := {0, 2, 3, 4}

theorem mcaEvent_of_mem_Gbad :
    ∀ γ ∈ Gbad, mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) (ubad 0) (ubad 1) γ := by
  intro γ hγ
  rw [ubad_zero, ubad_one]
  simp only [Gbad, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · exact mcaEvent_g0
  · exact mcaEvent_g2
  · exact mcaEvent_g3
  · exact mcaEvent_g4

/-- **Bad side:** `ε_mca(C, 1/4) ≥ 4/5`. (The probe says this is in fact an equality; only the
`≥` direction is needed for the pin.) -/
theorem epsMCA_C542_quarter_ge :
    (4 : ℝ≥0∞) / 5 ≤ epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) (1/4) := by
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C542 : Set (Fin 4 → F5)) (1/4) ubad Gbad mcaEvent_of_mem_Gbad
  have hG : (Gbad.card : ℝ≥0∞) = 4 := by
    rw [show Gbad.card = 4 from by decide]; norm_num
  have hF : ((Fintype.card F5 : ℕ) : ℝ≥0∞) = 5 := by
    rw [show Fintype.card F5 = 5 from by simp [ZMod.card]]; norm_num
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
    have h34 : 3 < T.card := by exact_mod_cast h3
    omega
  apply Finset.eq_univ_of_card
  have hle : T.card ≤ 4 := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ T
  simp only [Fintype.card_fin]
  omega

/-- **Good side:** `ε_mca(C, δ) ≤ 1/5` for every `δ < 1/4`. -/
theorem epsMCA_C542_le_of_lt_quarter {δ : ℝ≥0} (hδ : δ < 1 / 4) :
    epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) δ ≤ 1 / 5 := by
  have h := MCAWitnessSpread.epsMCA_le_inv_card_of_forced_univ C542 δ
    (forced_univ_of_lt_quarter hδ)
  rwa [show ((Fintype.card F5 : ℕ) : ℝ≥0∞) = 5 from by
    rw [show Fintype.card F5 = 5 from by simp [ZMod.card]]; norm_num] at h

/-! ## Exact value on `[0, 1/4)` (bonus: the full profile below the jump) -/

/-- A firing stack valid at every radius: `(0, u₀)` with `u₀ ∉ C` fires at `γ = 0` with
witness set `univ` (the line is the zero codeword; the second row is not explainable). -/
theorem mcaEvent_floor (δ : ℝ≥0) :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) δ (0 : Fin 4 → F5) u₀ (0 : F5) := by
  refine ⟨Finset.univ, ?_, ⟨lineEval 0 0, lineEval_mem 0 0, by decide⟩, ?_⟩
  · have : ((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0) ≤ (Fintype.card (Fin 4) : ℝ≥0) := by
      have h1 : (1 : ℝ≥0) - δ ≤ 1 := tsub_le_self
      calc ((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0)
          ≤ 1 * (Fintype.card (Fin 4) : ℝ≥0) := by gcongr
        _ = (Fintype.card (Fin 4) : ℝ≥0) := one_mul _
    simp only [ge_iff_le, Finset.card_univ]
    exact this
  · refine not_pairJointAgreesOn_of_row1 ?_
    decide

/-- **Exact value below the jump:** `ε_mca(C, δ) = 1/5` for every `δ < 1/4`. Together with
`epsMCA_C542_quarter_ge` this exhibits the step profile `1/5 ↗ 4/5` at `δ = 1/4`. -/
theorem epsMCA_C542_eq_inv_card_of_lt_quarter {δ : ℝ≥0} (hδ : δ < 1 / 4) :
    epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) δ = 1 / 5 := by
  refine le_antisymm (epsMCA_C542_le_of_lt_quarter hδ) ?_
  have h := epsMCA_ge_inv_card_of_mcaEvent (F := F5) (A := F5)
    (C542 : Set (Fin 4 → F5)) δ ![0, u₀] 0 (by simpa using mcaEvent_floor δ)
  rwa [show ((Fintype.card F5 : ℕ) : ℝ≥0∞) = 5 from by
    rw [show Fintype.card F5 = 5 from by simp [ZMod.card]]; norm_num] at h

/-! ## The pin -/

/-- `2/5 < 4/5` in `ℝ≥0∞`. -/
theorem two_fifth_lt_four_fifth : (2 / 5 : ℝ≥0∞) < 4 / 5 := by
  have h5 : ((5 : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have h5' : ((5 : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), mul_comm (4 : ℝ≥0∞)]
  exact ENNReal.mul_lt_mul_right h5 h5' (by norm_num)

/-- **Bad-side bracket input:** `ε* = 2/5 < ε_mca(C, 1/4)`. -/
theorem epsMCA_C542_quarter_gt :
    (2 / 5 : ℝ≥0∞) < epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) (1/4) :=
  lt_of_lt_of_le two_fifth_lt_four_fifth epsMCA_C542_quarter_ge

/-- **Good-radius membership:** every `δ < 1/4` is a good radius at `ε* = 2/5`. -/
theorem mem_goodRadii_of_lt_quarter {δ : ℝ≥0} (hδ : δ < 1 / 4) :
    δ ∈ MCAThresholdLedger.mcaGoodRadii (F := F5) (A := F5)
      (C542 : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) := by
  refine ⟨le_of_lt (lt_of_lt_of_le hδ quarter_le_one), ?_⟩
  refine le_trans (epsMCA_C542_le_of_lt_quarter hδ) ?_
  gcongr
  norm_num

/-- **THE PIN — the first machine-checked exact `δ*` value for any code.**

For `C = RS[F₅, F₅*, 2]` (smooth domain of size `4 = 2²`, rate `1/2`) at `ε* = 2/5`:

  `mcaDeltaStar C (2/5) = 1/4`.

Upper bracket: `δ = 1/4` is bad (`ε_mca = 4/5 > 2/5`, explicit 4-scalar stack). Lower bracket:
every `δ < 1/4` is good (`ε_mca = 1/5 ≤ 2/5`, forced-universal-witness algebra), and `ℝ≥0` is
densely ordered, so the supremum reaches `1/4`. The supremum is **not attained** — `δ*` sits
exactly at the jump of the step function `ε_mca(C, ·)`. -/
theorem mcaDeltaStar_C542_eq_quarter :
    MCAThresholdLedger.mcaDeltaStar (F := F5) (A := F5)
      (C542 : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) = 1/4 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ epsMCA_C542_quarter_gt) ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hmem := mem_goodRadii_of_lt_quarter hc2
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F5) (A := F5)
    (C542 : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) hmem.1 hmem.2
  exact absurd hle (not_le.mpr hc1)

/-! ## Source audit -/

#print axioms ProximityGap.MCAWitnessSpread.pairJointAgreesOn_iff_split
#print axioms ProximityGap.MCAWitnessSpread.badScalar_card_le_one_of_forced_univ
#print axioms ProximityGap.MCAWitnessSpread.epsMCA_le_inv_card_of_forced_univ
#print axioms epsMCA_C542_quarter_ge
#print axioms epsMCA_C542_eq_inv_card_of_lt_quarter
#print axioms mcaDeltaStar_C542_eq_quarter

end ProximityGap.DeltaStarExactPin
