/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint

/-!
# The census-conditional δ* pin: δ* as the crossing radius of the constrained subset-sum census

The O137/O138/O139 probe arc (issue #357) produced the *corrected extremality conjecture*:
for smooth-domain RS codes, `ε_mca(C, 1 − a/n) · |F|` equals the size of the **constrained
subset-sum census** `{−e₁(A) : A an a-subset of the domain, e₂(A) = ⋯ = e_{a−k}(A) = 0}`,
attained on the twisted-monomial orbit of the adjacent-exponent pair — verified exactly at
every rung where exact computation exists ((5,4,2), (13,4,2), (17,4,2), (12,6)×3 fields), with
the census measured *inside the window* at (16,4) and (8,4) including an empty-census death
radius. If this holds at production scales, the in-window upper bracket of δ* is the
asymptotics of one additive-combinatorics object.

This file welds that programme into the `mcaDeltaStar` ledger:

* `constrainedCensus` — the census, formal (first formalization of the probe object).
* `agreeOf` + `mcaEvent_agree_iff` + `epsMCA_eq_grid` — **the radius-quantization theorem**:
  `ε_mca` depends on `δ` only through the agreement threshold `⌈(1−δ)n⌉`, so it is a step
  function constant between grid radii `1 − a/n`. This retroactively certifies every
  grid-sampled probe and lets grid hypotheses control all radii.
* `CensusUpperExtremal` — the **named open hypothesis** (the conjecture's upper half: above
  the crossing agreement no stack beats the census). The lower half — the census scalars are
  genuinely bad for the explicit monomial stack — is the per-instance provable half
  (`badScalar_iff_subsetSum` / the O138 census law).
* `mcaDeltaStar_eq_of_censusCrossing` — **the conditional pin**: census-upper extremality +
  census numerics (good above the crossing, bad at it) ⟹ `mcaDeltaStar = 1 − a_c/n` exactly.
  "Pin δ*" for these codes is thereby *equivalent, given extremality, to locating the census
  crossing* — a finite, per-scale additive-combinatorics computation.
* `mcaDeltaStar_F5_via_census` — **non-vacuity, end-to-end**: at RS[F₅, F₅*, 2] the census
  route is fully instantiated (census(3) = {1,2,3,4} of size 4 — kernel-checked — crossing
  ε* = 2/5 at a_c = 3; census(4) = {0} matching `ε_mca = 1/5` at δ = 0), recovering
  `δ* = 1/4` purely through the census engine, in agreement with the direct pin
  (`mcaDeltaStar_rs_F5_eq_quarter`). The extremality inputs at this scale are *theorems*,
  not hypotheses.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (O137/O138/O139/O140 census arc; the round-2 architecture).
- `KKH26CensusLaw.lean` (`badScalar_iff_subsetSum` — the lower half's engine),
  `MCAListBracketInterpolation.lean` (the jump-pin), `MCADeltaStarExactPoint.lean`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.CensusConditionalPin

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.MCAListBracketInterpolation

/-! ## The constrained subset-sum census -/

section Census

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The O138 census object:** scalars `−e₁(A)` over `a`-subsets `A ⊆ H` whose elementary
symmetric functions `e₂, …, e_{a−k}` all vanish. For the adjacent-exponent monomial stack
over a smooth domain `H`, these are exactly the MCA-bad scalars (the census law / O138). -/
def constrainedCensus (H : Finset F) (k a : ℕ) : Finset F :=
  ((H.powersetCard a).filter
    (fun A => ∀ j ∈ Finset.Icc 2 (a - k), A.val.esymm j = 0)).image
    (fun A => - A.val.esymm 1)

end Census

/-! ## The radius-quantization theorem -/

section Quantization

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The effective agreement threshold of radius `δ` on `n` coordinates. -/
noncomputable def agreeOf (n : ℕ) (δ : ℝ≥0) : ℕ := ⌈(1 - δ) * (n : ℝ≥0)⌉₊

/-- The MCA bad event sees `δ` only through `agreeOf`. -/
theorem mcaEvent_agree_iff (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (A := A) C δ u₀ u₁ γ ↔
      ∃ S : Finset ι, agreeOf (Fintype.card ι) δ ≤ S.card ∧
        (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn C S u₀ u₁ := by
  unfold mcaEvent agreeOf
  constructor
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, Nat.ceil_le.mpr h1, h2, h3⟩
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, le_trans (Nat.le_ceil _) (by exact_mod_cast h1), h2, h3⟩

open Classical in
/-- Radii with equal agreement thresholds have equal MCA errors. -/
theorem epsMCA_eq_of_agreeOf_eq (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (h : agreeOf (Fintype.card ι) δ = agreeOf (Fintype.card ι) δ') :
    epsMCA (F := F) (A := A) C δ = epsMCA (F := F) (A := A) C δ' := by
  unfold epsMCA
  refine iSup_congr fun u => le_antisymm ?_ ?_
  · refine Pr_le_Pr_of_implies _ _ _ fun γ hev => ?_
    have hx := (mcaEvent_agree_iff C δ (u 0) (u 1) γ).mp hev
    rw [h] at hx
    exact (mcaEvent_agree_iff C δ' (u 0) (u 1) γ).mpr hx
  · refine Pr_le_Pr_of_implies _ _ _ fun γ hev => ?_
    have hx := (mcaEvent_agree_iff C δ' (u 0) (u 1) γ).mp hev
    rw [← h] at hx
    exact (mcaEvent_agree_iff C δ (u 0) (u 1) γ).mpr hx

/-- The agreement threshold never exceeds `n`. -/
theorem agreeOf_le (n : ℕ) (δ : ℝ≥0) : agreeOf n δ ≤ n := by
  unfold agreeOf
  rw [Nat.ceil_le]
  calc (1 - δ) * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) := by gcongr; exact tsub_le_self
    _ = (n : ℝ≥0) := one_mul _

/-- The agreement threshold of the grid radius `1 − a/n` is `a` itself. -/
theorem agreeOf_grid {n a : ℕ} (hn : n ≠ 0) (ha : a ≤ n) :
    agreeOf n (1 - (a : ℝ≥0) / (n : ℝ≥0)) = a := by
  unfold agreeOf
  have hn' : ((n : ℝ≥0)) ≠ 0 := by exact_mod_cast hn
  have hle : (a : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
    rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn'))]
    exact_mod_cast ha
  rw [tsub_tsub_cancel_of_le hle, div_mul_cancel₀ _ hn']
  exact Nat.ceil_natCast a

/-- **The radius-quantization theorem:** `ε_mca` is the step function of its grid value —
every radius `δ` has the same MCA error as the grid radius `1 − agreeOf(δ)/n`. This is the
exact sense in which grid-sampled probes (and grid-stated hypotheses) determine the whole
`ε_mca` curve. -/
theorem epsMCA_eq_grid (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ
      = epsMCA (F := F) (A := A) C
          (1 - (agreeOf (Fintype.card ι) δ : ℝ≥0) / (Fintype.card ι : ℝ≥0)) := by
  refine epsMCA_eq_of_agreeOf_eq C ?_
  rw [agreeOf_grid (Fintype.card_ne_zero) (agreeOf_le _ δ)]

end Quantization

/-! ## The named hypothesis and the conditional pin -/

section Pin

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The named open hypothesis (O138 extremality, upper half):** above the crossing
agreement `ac`, no stack's MCA error beats the constrained subset-sum census fraction.
The lower half (census scalars are genuinely bad) is per-instance provable via the census
law; this upper half is the genuine conjecture — proven below only at toy scale. -/
def CensusUpperExtremal (C : Set (ι → A)) (H : Finset F) (k ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ Fintype.card ι →
    epsMCA (F := F) (A := A) C (1 - (a : ℝ≥0) / (Fintype.card ι : ℝ≥0))
      ≤ ((constrainedCensus H k a).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

/-- **The census-conditional δ\* pin.** If (i) the census-upper extremality holds above the
crossing agreement `ac`, (ii) the census clears `ε*` at every agreement above `ac`, and
(iii) the MCA error at the crossing radius itself exceeds `ε*` (the per-instance provable
lower half), then `mcaDeltaStar = 1 − ac/n` **exactly**. Pinning δ* for such codes is
thereby reduced, given extremality, to locating the census crossing — a finite
additive-combinatorics computation per scale. -/
theorem mcaDeltaStar_eq_of_censusCrossing
    (C : Set (ι → A)) (H : Finset F) (k : ℕ) (εstar : ℝ≥0∞) {ac : ℕ}
    (hupper : CensusUpperExtremal (F := F) (A := A) C H k ac)
    (hcensus : ∀ a : ℕ, ac < a → a ≤ Fintype.card ι →
      ((constrainedCensus H k a).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hlower : εstar < epsMCA (F := F) (A := A) C
      (1 - (ac : ℝ≥0) / (Fintype.card ι : ℝ≥0))) :
    mcaDeltaStar (F := F) (A := A) C εstar
      = 1 - (ac : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  refine mcaDeltaStar_eq_of_jump C εstar tsub_le_self ?_ hlower
  intro δ hδ
  set n := Fintype.card ι with hn
  -- quantize δ to its grid agreement a = agreeOf n δ
  rw [epsMCA_eq_grid C δ]
  set a := agreeOf n δ with ha
  -- δ below the crossing radius forces the agreement strictly above ac
  have hac_lt : ac < a := by
    have h1 : δ + (ac : ℝ≥0) / (n : ℝ≥0) < 1 := by
      have := hδ
      rwa [lt_tsub_iff_right] at this
    have h2 : (ac : ℝ≥0) / (n : ℝ≥0) < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (ac : ℝ≥0) / (n : ℝ≥0) + δ = δ + (ac : ℝ≥0) / (n : ℝ≥0) := add_comm _ _
        _ < 1 := h1
    have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by
      exact_mod_cast Fintype.card_pos
    have h3 : (ac : ℝ≥0) < (1 - δ) * (n : ℝ≥0) := by
      have := mul_lt_mul_of_pos_right h2 hn0
      rwa [div_mul_cancel₀ _ (ne_of_gt hn0)] at this
    rw [ha]
    unfold agreeOf
    exact Nat.lt_ceil.mpr h3
  exact le_trans (hupper a hac_lt (agreeOf_le n δ)) (hcensus a hac_lt (agreeOf_le n δ))

end Pin

/-! ## Non-vacuity: the F₅ exact point through the census engine -/

section F5Instance

open ProximityGap.MCADeltaStarExactPoint

/-- The smooth domain `F₅* = {1, 2, 4, 3}` as a Finset. -/
def domF5 : Finset F5 := {1, 2, 4, 3}

/-- The census at agreement 3 (no constraints: `a − k = 1`): all four 3-subset sums,
negated — the full nonzero scalar set. Kernel-checked. -/
theorem census_F5_a3 : constrainedCensus domF5 2 3 = {1, 2, 3, 4} := by decide

/-- The census at agreement 4: the single 4-subset `H` qualifies (`e₂(H) = 0` over `F₅`!),
contributing `−e₁(H) = 0`. Kernel-checked. -/
theorem census_F5_a4 : constrainedCensus domF5 2 4 = {0} := by decide

/-- The grid radius at agreement 4 is `0`. -/
theorem grid_radius_a4 :
    (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0) = 0 := by
  rw [Fintype.card_fin]
  have h4 : ((4 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) = 1 := by
    rw [div_self]
    norm_num
  rw [h4, tsub_self]

/-- The grid radius at agreement 3 is `1/4`. -/
theorem grid_radius_a3 :
    (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0) = 1/4 := by
  rw [Fintype.card_fin]
  have h34 : ((3 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < ((4 : ℕ) : ℝ≥0))]
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  apply NNReal.coe_injective
  rw [NNReal.coe_sub h34]
  push_cast
  norm_num

/-- **Census-upper extremality is a theorem at the F₅ scale**: the only in-range agreement
above the crossing is `a = 4`, where `ε_mca(C, 0) = 1/5 = census(4)/|F₅|` exactly (the
sub-granularity regime meets the census). -/
theorem censusUpperExtremal_F5 :
    CensusUpperExtremal (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) domF5 2 3 := by
  intro a ha3 ha4
  rw [Fintype.card_fin] at ha4
  interval_cases a
  -- a = 4
  rw [grid_radius_a4, census_F5_a4, Finset.card_singleton]
  have hsmall : (0 : ℝ≥0) * (Fintype.card (Fin 4) : ℝ≥0) < 1 := by
    rw [zero_mul]; norm_num
  rw [epsMCA_eq_inv_card_of_small_radius rsC hsmall]
  · simp
  · exact rsC_proper

/-- The census numerics at F₅: above the crossing, the census fraction clears `ε* = 2/5`. -/
theorem censusGood_F5 : ∀ a : ℕ, 3 < a → a ≤ Fintype.card (Fin 4) →
    ((constrainedCensus domF5 2 a).card : ℝ≥0∞) / (Fintype.card F5 : ℝ≥0∞)
      ≤ (2/5 : ℝ≥0∞) := by
  intro a ha3 ha4
  rw [Fintype.card_fin] at ha4
  interval_cases a
  rw [census_F5_a4, Finset.card_singleton, ZMod.card]
  simp only [Nat.cast_ofNat, Nat.cast_one]
  gcongr
  norm_num

/-- The crossing is bad: `ε_mca(C, 1 − 3/4) = ε_mca(C, 1/4) ≥ 4/5 > 2/5`. -/
theorem censusBad_F5 :
    (2/5 : ℝ≥0∞) < epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5))
      (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 4) : ℝ≥0)) := by
  rw [grid_radius_a3]
  refine lt_of_lt_of_le ?_ epsMCA_rs_quarter_ge
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- **The F₅ exact point, recovered end-to-end through the census engine** — the first
machine-checked instance of "δ\* = the census crossing radius", with every hypothesis of
the conditional pin discharged as a theorem. Agrees with the direct pin
(`mcaDeltaStar_rs_F5_eq_quarter`). -/
theorem mcaDeltaStar_F5_via_census :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) = 1/4 := by
  have h := mcaDeltaStar_eq_of_censusCrossing (F := F5) (A := F5)
    (rsC : Set (Fin 4 → F5)) domF5 2 (2/5 : ℝ≥0∞)
    censusUpperExtremal_F5 censusGood_F5 censusBad_F5
  rw [grid_radius_a3] at h
  exact h

end F5Instance

/-! ## Source audit -/

#print axioms epsMCA_eq_grid
#print axioms mcaDeltaStar_eq_of_censusCrossing
#print axioms mcaDeltaStar_F5_via_census

end ProximityGap.CensusConditionalPin
