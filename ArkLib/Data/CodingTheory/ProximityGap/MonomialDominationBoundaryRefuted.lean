/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarSecondPinF17
import ArkLib.Data.CodingTheory.ProximityGap.MonomialDominationPin

/-!
# The boundary-row triangle stack: `MonomialDomination` fails off the monomial family (#357)

At the boundary row `d = 2b − 1` (band `b = 3`, `δ = 1/4`, agreement `a = 6`) of the
second-pin code `C84 = RS[F₁₇, ⟨2⟩, 4]`, the **two-triangle incidence stack**

  `u₀ = (0, 8, 16, 0, …, 0)`, `u₁ = (10, 15, 5, 0, …, 0)`

(the affine line in the 2-dimensional intersection of the column spans of the exponent
triangles `{0,1,2}` and `{3,4,6}`) carries **seven** `mcaEvent`-bad scalars
`{0, 4, 7, 9, 10, 12, 13}` — machine-checked below via seven explicit certificates
(`tri_cert*`), each killed by the four-point interpolant-forcing engine `interp_kill`.

The probe `probe_boundary_triangle_stratum.py` measures `monomialEps` at this radius to
be exactly `4/17` (exhaustive over all 64 monomial pairs, end-to-end `mcaEvent`
verification): every monomial pair has at most 4 bad scalars while this non-monomial
stack has 7.  Consequently `MonomialDomination dom C ac` (which demands
`ε_mca ≤ monomialEps` at **every** agreement above the crossing) is **false** at this
instance for every crossing `ac ≤ 5` — formalized here as the conditional refutation
`monomialDomination_refuted_of_monomial_bound` whose only input is the probe-measured
monomial bound, packaged as the named numeric surface `MonomialBoundaryBound`.

Production relevance: 2-power smooth domains always have `3 ∤ n`, so the boundary-row
defect case (triangles strictly beating monomials; at `3 ∣ n` the excess pair
`(X^{n−2}, X^{n−3})` is itself coset-triangle-structured and ties) is the *generic*
production shape.  The surviving v4 surface restricts domination to rows with
`d ≥ 2b` (off the boundary rows), where the monomial family has survived every
falsifier run to date.

Issue #357 (the boundary-row incidence arc).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MonomialDominationBoundaryRefuted

open ProximityGap.DeltaStarSecondPin (F17 dom C84 codeword_eq_zero_of_vanishing cubic_mem)

/-! ## The triangle stack -/

/-- First row: supported on the exponent triangle `{0, 1, 2}`-side of the line. -/
def v₀ : Fin 8 → F17 := ![0, 8, 16, 0, 0, 0, 0, 0]

/-- Second row (the direction word). -/
def v₁ : Fin 8 → F17 := ![10, 15, 5, 0, 0, 0, 0, 0]

/-! ## The interpolant-forcing kill engine -/

/-- **The four-point interpolant kill.**  If the explicit cubic `q₀ + q₁x + q₂x² + q₃x³`
matches `v₁` at four witness positions with distinct domain values but conflicts with
`v₁` at a fifth witness position, no codeword pair jointly explains `(v₀, v₁)` on the
witness: the would-be explanation of `v₁` agrees with the cubic at four points, so
their difference (a codeword) vanishes there and is zero, forcing the explanation to
*be* the cubic — contradicting the conflict. -/
theorem interp_kill (T : Finset (Fin 8)) (q₀ q₁ q₂ q₃ : F17)
    (i1 i2 i3 i4 : Fin 8)
    (hfit : q₀ + q₁ * dom i1 + q₂ * dom i1 ^ 2 + q₃ * dom i1 ^ 3 = v₁ i1 ∧
            q₀ + q₁ * dom i2 + q₂ * dom i2 ^ 2 + q₃ * dom i2 ^ 3 = v₁ i2 ∧
            q₀ + q₁ * dom i3 + q₂ * dom i3 ^ 2 + q₃ * dom i3 ^ 3 = v₁ i3 ∧
            q₀ + q₁ * dom i4 + q₂ * dom i4 ^ 2 + q₃ * dom i4 ^ 3 = v₁ i4)
    (hmem : i1 ∈ T ∧ i2 ∈ T ∧ i3 ∈ T ∧ i4 ∈ T)
    (hcard : ({dom i1, dom i2, dom i3, dom i4} : Finset F17).card = 4)
    (c : Fin 8) (hcT : c ∈ T)
    (hconf : q₀ + q₁ * dom c + q₂ * dom c ^ 2 + q₃ * dom c ^ 3 ≠ v₁ c) :
    ¬ pairJointAgreesOn (C84 : Set (Fin 8 → F17)) T v₀ v₁ := by
  rintro ⟨w₀, _, w₁, hw₁, hag⟩
  set q : Fin 8 → F17 :=
    fun i => q₀ + q₁ * dom i + q₂ * dom i ^ 2 + q₃ * dom i ^ 3 with hq
  have hqmem : q ∈ C84 := cubic_mem q₀ q₁ q₂ q₃
  have hdiff : w₁ - q = 0 := by
    refine codeword_eq_zero_of_vanishing _ (Submodule.sub_mem _ hw₁ hqmem)
      {dom i1, dom i2, dom i3, dom i4} (le_of_eq hcard.symm) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨i1, rfl, by
        rw [Pi.sub_apply, (hag i1 hmem.1).2, hq]
        simp only []
        rw [hfit.1, sub_self]⟩
    · exact ⟨i2, rfl, by
        rw [Pi.sub_apply, (hag i2 hmem.2.1).2, hq]
        simp only []
        rw [hfit.2.1, sub_self]⟩
    · exact ⟨i3, rfl, by
        rw [Pi.sub_apply, (hag i3 hmem.2.2.1).2, hq]
        simp only []
        rw [hfit.2.2.1, sub_self]⟩
    · exact ⟨i4, rfl, by
        rw [Pi.sub_apply, (hag i4 hmem.2.2.2).2, hq]
        simp only []
        rw [hfit.2.2.2, sub_self]⟩
  have hwq : w₁ c = q c := by
    have := congrFun hdiff c
    rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  have : q c = v₁ c := by rw [← hwq, (hag c hcT).2]
  exact hconf (by rw [hq] at this; exact this)

/-- The size clause at `δ = 1/4`, `n = 8` (6-point witnesses), reused. -/
private theorem card6 {T : Finset (Fin 8)} (hT : T.card = 6) :
    (T.card : ℝ≥0) ≥ (1 - (1/4 : ℝ≥0)) * (Fintype.card (Fin 8) : ℝ≥0) :=
  ProximityGap.DeltaStarSecondPin.card_clause hT

/-! ## The seven certificates -/

/-- γ = 0: witness `{0,3,4,5,6,7}`, line codeword 0 (the line vanishes there). -/
theorem tri_cert0 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 0 := by
  refine ⟨{0, 3, 4, 5, 6, 7}, card6 (by decide), ⟨0, C84.zero_mem, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 3 2 2 3 0 3 4 5 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 6 (by decide) (by decide)

/-- γ = 4: witness `{1,3,4,5,6,7}`, line codeword 0. -/
theorem tri_cert4 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 4 := by
  refine ⟨{1, 3, 4, 5, 6, 7}, card6 (by decide), ⟨0, C84.zero_mem, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 9 6 6 9 1 3 4 5 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 6 (by decide) (by decide)

/-- γ = 7: witness `{2,3,4,5,6,7}`, line codeword 0. -/
theorem tri_cert7 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 7 := by
  refine ⟨{2, 3, 4, 5, 6, 7}, card6 (by decide), ⟨0, C84.zero_mem, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 12 8 8 12 2 3 4 5 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 6 (by decide) (by decide)

/-- γ = 9: witness `{0,1,2,5,6,7}`, line codeword `3 + 9x + 15x² + 12x³`. -/
theorem tri_cert9 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 9 := by
  refine ⟨{0, 1, 2, 5, 6, 7}, card6 (by decide), ⟨_, cubic_mem 3 9 15 12, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 9 2 6 10 0 1 2 5 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 6 (by decide) (by decide)

/-- γ = 10: witness `{0,1,2,4,5,7}`, line codeword `12 + 11x + 4x² + 5x³`. -/
theorem tri_cert10 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 10 := by
  refine ⟨{0, 1, 2, 4, 5, 7}, card6 (by decide), ⟨_, cubic_mem 12 11 4 5, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 15 0 7 5 0 1 2 4 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 5 (by decide) (by decide)

/-- γ = 12: witness `{0,1,2,3,5,7}`, line codeword `13 + 15x + 16x² + 8x³`. -/
theorem tri_cert12 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 12 := by
  refine ⟨{0, 1, 2, 3, 5, 7}, card6 (by decide), ⟨_, cubic_mem 13 15 16 8, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 10 13 9 12 0 1 2 3 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 5 (by decide) (by decide)

/-- γ = 13: witness `{0,1,2,3,4,6}`, line codeword `6 + 11x + 8x² + 3x³`. -/
theorem tri_cert13 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 13 := by
  refine ⟨{0, 1, 2, 3, 4, 6}, card6 (by decide), ⟨_, cubic_mem 6 11 8 3, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact interp_kill _ 10 13 9 12 0 1 2 3 ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩ (by decide) 4 (by decide) (by decide)

/-! ## The lower bound and the conditional refutation -/

/-- **The triangle stack carries seven bad scalars:** `ε_mca(C84, 1/4) ≥ 7/17`. -/
theorem epsMCA_quarter_ge_seven :
    (7 / 17 : ℝ≥0∞) ≤ epsMCA (F := F17) (A := F17) (C84 : Set (Fin 8 → F17)) (1/4) := by
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C84 : Set (Fin 8 → F17)) (1/4) ![v₀, v₁] ({0, 4, 7, 9, 10, 12, 13} : Finset F17) ?_
  · have hcard : ({0, 4, 7, 9, 10, 12, 13} : Finset F17).card = 7 := by decide
    have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by
      rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
      norm_num
    rwa [hcard, hF] at h
  · intro γ hγ
    fin_cases hγ
    · simpa using tri_cert0
    · simpa using tri_cert4
    · simpa using tri_cert7
    · simpa using tri_cert9
    · simpa using tri_cert10
    · simpa using tri_cert12
    · simpa using tri_cert13

/-- The probe-measured monomial census at the boundary row (the named numeric surface):
every monomial pair of `C84` has bad-scalar mass at most `4/17` at `δ = 1/4`.
Measured exhaustively (64 pairs, end-to-end `mcaEvent` scans) by
`probe_boundary_triangle_stratum.py`; maximum 4, attained at `(X⁶, X⁴)`. -/
def MonomialBoundaryBound : Prop :=
  ProximityGap.MonomialDominationPin.monomialEps dom (C84 : Set (Fin 8 → F17)) (1/4)
    ≤ 4 / 17

/-- The boundary radius `1/4` is the grid radius of agreement `a = 6` at `n = 8`. -/
private theorem quarter_eq_grid :
    (1 - ((6 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) = (1/4 : ℝ≥0) := by
  have h68 : ((6 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 3/4 := by
    rw [← NNReal.coe_inj]
    push_cast
    norm_num
  have h341 : (3/4 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
    norm_num
  rw [h68, tsub_eq_iff_eq_add_of_le h341]
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- **`MonomialDomination` is FALSE at the boundary row** (conditional on the
probe-measured monomial census): for every crossing agreement `ac ≤ 5`, the surface
`MonomialDomination dom C84 ac` fails — the triangle stack's `7/17` exceeds the
monomial family's `4/17` at agreement `6 > ac`. -/
theorem monomialDomination_refuted_of_monomial_bound (hmono : MonomialBoundaryBound)
    {ac : ℕ} (hac : ac ≤ 5) :
    ¬ ProximityGap.MonomialDominationPin.MonomialDomination dom
      (C84 : Set (Fin 8 → F17)) ac := by
  intro h
  have h6 := h 6 (by omega) (by norm_num)
  rw [quarter_eq_grid] at h6
  have hchain : (7 / 17 : ℝ≥0∞) ≤ 4 / 17 :=
    le_trans epsMCA_quarter_ge_seven (le_trans h6 hmono)
  have h17 : (17 : ℝ≥0∞) ≠ 0 := by norm_num
  have h17' : (17 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h74 : (7 : ℝ≥0∞) ≤ 4 := by
    calc (7 : ℝ≥0∞) = 7 / 17 * 17 := by rw [ENNReal.div_mul_cancel h17 h17']
      _ ≤ 4 / 17 * 17 := mul_le_mul_left hchain 17
      _ = 4 := by rw [ENNReal.div_mul_cancel h17 h17']
  exact absurd h74 (by norm_num)

/-! ## The surviving v4 surface -/

/-- **The corrected domination surface (v4): monomial domination off the boundary rows.**
The agreement row `a` has band `b = n − a + 1`; the row is *off-boundary* when the
code's distance budget clears twice the band (`2b ≤ n − k + 1`, i.e. `k + n + 1 ≤ 2a`).
The refutation above lives exactly on the excluded rows (`a = 6`, `k = 4`, `n = 8`:
`k + n + 1 = 13 > 12 = 2a`).  Off the boundary rows the monomial family has survived
every falsifier run to date (binomial attacks, random stacks, floor bands, the pencil
strip — whose extremal stacks are themselves monomial — and the `3 ∣ n` boundary ties). -/
def MonomialDominationOffBoundary {n : ℕ} (dom : Fin n → F17)
    (C : Set (Fin n → F17)) (k ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ n → k + n + 1 ≤ 2 * a →
    epsMCA (F := F17) (A := F17) C (1 - (a : ℝ≥0) / (n : ℝ≥0))
      ≤ ProximityGap.MonomialDominationPin.monomialEps dom C
          (1 - (a : ℝ≥0) / (n : ℝ≥0))

/-- v4 weakens v3: the off-boundary surface follows from full domination.  (The converse
fails — by this file's refutation — which is precisely the content of the correction.) -/
theorem offBoundary_of_monomialDomination {n k ac : ℕ} (dom : Fin n → F17)
    (C : Set (Fin n → F17))
    (h : ProximityGap.MonomialDominationPin.MonomialDomination dom C ac) :
    MonomialDominationOffBoundary dom C k ac :=
  fun a hac han _ => h a hac han

end ProximityGap.MonomialDominationBoundaryRefuted

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.epsMCA_quarter_ge_seven
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.monomialDomination_refuted_of_monomial_bound
