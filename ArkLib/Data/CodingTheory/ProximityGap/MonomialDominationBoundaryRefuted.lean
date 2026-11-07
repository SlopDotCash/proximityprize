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
production shape.

**The v4 correction is refuted too.**  The v4 surface `MonomialDominationOffBoundary`
restricts domination to rows with `d ≥ 2b` (off the boundary rows).  On the same code it
fails at the off-boundary row `a = 7` (`δ = 1/8`, band `b = 2`, `k + n + 1 = 13 ≤ 14 = 2a`):
`ε_mca(C84, 1/8) = 2/17` (`epsMCA_eighth_eq`) while every monomial pair has at most one bad
scalar, `monomialEps ≤ 1/17` (`monomialEps_eighth_le`, proved unconditionally).  Hence
`monomialDominationOffBoundary_refuted`: v4 is false for every crossing `ac ≤ 6`.  The seven
quarter-radius certificates and the conditional v3 refutation above remain valid.

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

/-! ## The v4 surface (also refuted, see below) -/

/-- **The v4 domination surface: monomial domination off the boundary rows.**
The agreement row `a` has band `b = n − a + 1`; the row is *off-boundary* when the
code's distance budget clears twice the band (`2b ≤ n − k + 1`, i.e. `k + n + 1 ≤ 2a`).
The triangle refutation above lives on the excluded rows (`a = 6`, `k = 4`, `n = 8`:
`k + n + 1 = 13 > 12 = 2a`).  **This surface is false as well**: at the off-boundary row
`a = 7` of the same code the full MCA error is `2/17` while the monomial family reaches only
`1/17` (`monomialDominationOffBoundary_refuted`, for every crossing `ac ≤ 6`). -/
def MonomialDominationOffBoundary {n : ℕ} (dom : Fin n → F17)
    (C : Set (Fin n → F17)) (k ac : ℕ) : Prop :=
  ∀ a : ℕ, ac < a → a ≤ n → k + n + 1 ≤ 2 * a →
    epsMCA (F := F17) (A := F17) C (1 - (a : ℝ≥0) / (n : ℝ≥0))
      ≤ ProximityGap.MonomialDominationPin.monomialEps dom C
          (1 - (a : ℝ≥0) / (n : ℝ≥0))

/-- v4 weakens v3: the off-boundary surface follows from full domination.  (Both surfaces are
refuted on `C84` for small crossings: v3 conditionally on `MonomialBoundaryBound`, v4
unconditionally by `monomialDominationOffBoundary_refuted`.) -/
theorem offBoundary_of_monomialDomination {n k ac : ℕ} (dom : Fin n → F17)
    (C : Set (Fin n → F17))
    (h : ProximityGap.MonomialDominationPin.MonomialDomination dom C ac) :
    MonomialDominationOffBoundary dom C k ac :=
  fun a hac han _ => h a hac han

/-! ## The v4 surface is also refuted: agreement `a = 7`, `δ = 1/8`

On the same code `C84`, the off-boundary row `a = 7` (`k + n + 1 = 13 ≤ 14 = 2a`, band `b = 2`,
distance `5 ≥ 2b = 4`) already separates the full MCA error from the monomial one:

* `ε_mca(C84, 1/8) = 2/17` (the universal second band, `MCABandTwoExact`);
* every monomial pair `(X^s, X^t)` has at most one bad scalar at `δ = 1/8`, so
  `monomialEps dom C84 (1/8) ≤ 1/17` (`monomialEps_eighth_le`).

The monomial upper bound is proved here unconditionally: a monomial line `x^s + γx^t` that agrees
with a cubic codeword on `7` of the `8` points must itself be a codeword, because the
coefficient functionals `φ_j(g) = ∑ᵢ g i · dom i^{8−j}` (`4 ≤ j ≤ 7`) kill cubics, kill the line for
the (at least two) `j ∉ {s, t}`, and are nonzero on the single-point spike.  Two distinct bad
scalars would then put both monomials in the code, contradicting badness. -/

/-- Every point of the domain `⟨2⟩ ⊆ F₁₇` is nonzero. -/
private theorem dom_ne_zero (i : Fin 8) : dom i ≠ 0 := by
  fin_cases i <;> decide

/-- Power sums over `μ₈ = ⟨2⟩`: `∑ᵢ dom i ^ e = 0` for `e < 16` with `8 ∤ e`. -/
private theorem psum_dom_eq_zero (e : ℕ) (he : e < 16) (h8 : e % 8 ≠ 0) :
    ∑ i : Fin 8, dom i ^ e = 0 := by
  interval_cases e <;> first | omega | decide

/-- The coefficient functionals `φ_j`, `4 ≤ j ≤ 7`, vanish on every codeword of `C84`. -/
private theorem phi_codeword_eq_zero {w : Fin 8 → F17} (hw : w ∈ C84) {j : ℕ}
    (hj4 : 4 ≤ j) (hj7 : j ≤ 7) :
    ∑ i, w i * dom i ^ (8 - j) = 0 := by
  obtain ⟨P, hP, rfl⟩ := hw
  have hnat : P.natDegree < 4 := by
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero]; norm_num
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
  have hexp : ∀ i, P.eval (dom i) * dom i ^ (8 - j)
      = ∑ m ∈ Finset.range 4, P.coeff m * dom i ^ (m + (8 - j)) := by
    intro i
    rw [Polynomial.eval_eq_sum_range' hnat, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pow_add]; ring
  show ∑ i, P.eval (dom i) * dom i ^ (8 - j) = 0
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [← Finset.mul_sum, psum_dom_eq_zero _ (by omega) (by omega), mul_zero]

/-- For `4 ≤ j ≤ 7` with `j ∉ {s, t}`, the functional `φ_j` vanishes on the monomial line. -/
private theorem phi_monomialLine_eq_zero (s t : Fin 8) (γ : F17) {j : ℕ}
    (hj4 : 4 ≤ j) (hj7 : j ≤ 7) (hjs : j ≠ (s : ℕ)) (hjt : j ≠ (t : ℕ)) :
    ∑ i, (dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) * dom i ^ (8 - j) = 0 := by
  have hs := s.isLt
  have ht := t.isLt
  have hexp : ∀ i, (dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) * dom i ^ (8 - j)
      = dom i ^ ((s : ℕ) + (8 - j)) + γ * dom i ^ ((t : ℕ) + (8 - j)) := by
    intro i; rw [pow_add, pow_add]; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    psum_dom_eq_zero _ (by omega) (by omega), psum_dom_eq_zero _ (by omega) (by omega),
    mul_zero, add_zero]

/-- **Seven-point closeness forces a monomial line into the code.**  If the line
`x ↦ x^s + γ·x^t` agrees with a codeword of `C84` on at least `7` of the `8` positions, then the
line itself is a codeword. -/
private theorem monomialLine_mem_of_seven {s t : Fin 8} {γ : F17} {S : Finset (Fin 8)}
    (hS : 7 ≤ S.card) {w : Fin 8 → F17} (hw : w ∈ C84)
    (hag : ∀ i ∈ S, w i = dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) :
    (fun i => dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) ∈ C84 := by
  suffices h : (fun i => dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) = w by rw [h]; exact hw
  funext r
  by_cases hr : r ∈ S
  · exact (hag r hr).symm
  · have hother : ∀ i, i ≠ r → i ∈ S := by
      intro i hir
      by_contra hiS
      have hsub : S ⊆ (Finset.univ.erase r).erase i := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun h => hiS (h ▸ hx), fun h => hr (h ▸ hx), Finset.mem_univ x⟩
      have hc := Finset.card_le_card hsub
      have h6 : ((Finset.univ.erase r).erase i).card = 6 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hir, Finset.mem_univ i⟩),
          Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, hj4, hj7, hjs, hjt⟩ :
        ∃ j : ℕ, 4 ≤ j ∧ j ≤ 7 ∧ j ≠ (s : ℕ) ∧ j ≠ (t : ℕ) := by
      by_cases h4 : (4 : ℕ) ≠ s ∧ (4 : ℕ) ≠ t
      · exact ⟨4, by omega, by omega, h4.1, h4.2⟩
      · by_cases h5 : (5 : ℕ) ≠ s ∧ (5 : ℕ) ≠ t
        · exact ⟨5, by omega, by omega, h5.1, h5.2⟩
        · exact ⟨6, by omega, by omega, by omega, by omega⟩
    set g : Fin 8 → F17 := fun i => (dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) - w i with hg
    have hgz : ∀ i, i ≠ r → g i = 0 := by
      intro i hir
      rw [hg]
      simp only []
      rw [hag i (hother i hir), sub_self]
    have hphi : ∑ i, g i * dom i ^ (8 - j) = 0 := by
      have hsplit : ∑ i, g i * dom i ^ (8 - j)
          = ∑ i, (dom i ^ (s : ℕ) + γ * dom i ^ (t : ℕ)) * dom i ^ (8 - j)
            - ∑ i, w i * dom i ^ (8 - j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg]; ring
      rw [hsplit, phi_monomialLine_eq_zero s t γ hj4 hj7 hjs hjt,
        phi_codeword_eq_zero hw hj4 hj7, sub_zero]
    have hsingle : ∑ i, g i * dom i ^ (8 - j) = g r * dom r ^ (8 - j) :=
      Finset.sum_eq_single r (fun i _ hir => by rw [hgz i hir, zero_mul])
        (fun h => absurd (Finset.mem_univ r) h)
    rw [hsingle] at hphi
    have hgr : g r = 0 := by
      rcases mul_eq_zero.mp hphi with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ (dom_ne_zero r))
    exact sub_eq_zero.mp hgr

/-- The size clause at `δ = 1/8`, `n = 8`: a witness has at least `7` positions. -/
private theorem seven_le_of_card_clause {S : Finset (Fin 8)}
    (hS : (S.card : ℝ≥0) ≥ (1 - (1/8 : ℝ≥0)) * (Fintype.card (Fin 8) : ℝ≥0)) :
    7 ≤ S.card := by
  have h18 : (1/8 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  have h78 : (1 - (1/8 : ℝ≥0)) * (Fintype.card (Fin 8) : ℝ≥0) = 7 := by
    rw [Fintype.card_fin, ← NNReal.coe_inj, NNReal.coe_mul, NNReal.coe_sub h18]
    push_cast
    norm_num
  have h7 : (7 : ℝ≥0) ≤ S.card := by
    rw [← h78]
    exact hS
  exact_mod_cast h7

open Classical in
/-- **At most one bad scalar per monomial pair at `δ = 1/8`.** -/
private theorem monomial_badScalar_card_le_one (s t : Fin 8) :
    (Finset.filter (fun γ : F17 => mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/8)
        (fun i => dom i ^ (s : ℕ)) (fun i => dom i ^ (t : ℕ)) γ) Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, ⟨w, hwmem, hweq⟩, hno⟩ := hγ.2
  obtain ⟨S', hS', ⟨w', hwmem', hweq'⟩, _⟩ := hγ'.2
  have m1 := monomialLine_mem_of_seven (s := s) (t := t) (γ := γ)
    (seven_le_of_card_clause hS) hwmem (fun i hi => by simpa [smul_eq_mul] using hweq i hi)
  have m2 := monomialLine_mem_of_seven (s := s) (t := t) (γ := γ')
    (seven_le_of_card_clause hS') hwmem' (fun i hi => by simpa [smul_eq_mul] using hweq' i hi)
  by_contra hne
  have hsub : (γ - γ') • (fun i : Fin 8 => dom i ^ (t : ℕ)) ∈ C84 := by
    have h := C84.sub_mem m1 m2
    convert h using 1
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hu1 : (fun i : Fin 8 => dom i ^ (t : ℕ)) ∈ C84 := by
    have h := C84.smul_mem (γ - γ')⁻¹ hsub
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h
  have hu0 : (fun i : Fin 8 => dom i ^ (s : ℕ)) ∈ C84 := by
    have h := C84.sub_mem m1 (C84.smul_mem γ hu1)
    convert h using 1
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  exact hno ⟨_, hu0, _, hu1, fun i _ => ⟨rfl, rfl⟩⟩

open Classical in
/-- **The monomial census at agreement `7`:** `monomialEps dom C84 (1/8) ≤ 1/17`. -/
theorem monomialEps_eighth_le :
    ProximityGap.MonomialDominationPin.monomialEps dom (C84 : Set (Fin 8 → F17)) (1/8)
      ≤ 1 / 17 := by
  unfold ProximityGap.MonomialDominationPin.monomialEps
  refine iSup_le fun s => iSup_le fun t => ?_
  calc _ ≤ 1 / (Fintype.card F17 : ℝ≥0∞) := by
        rw [prob_uniform_eq_card_filter_div_card]
        simp only [ENNReal.coe_natCast]
        gcongr
        exact_mod_cast monomial_badScalar_card_le_one s t
    _ = 1 / 17 := by
        rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
        norm_num

/-- **The full MCA error at agreement `7`:** `ε_mca(C84, 1/8) = 2/17` (universal second band). -/
theorem epsMCA_eighth_eq :
    epsMCA (F := F17) (A := F17) (C84 : Set (Fin 8 → F17)) (1/8) = 2 / 17 := by
  have h8 : (1/8 : ℝ≥0) * (Fintype.card (Fin 8) : ℝ≥0) = 1 := by
    rw [Fintype.card_fin]
    norm_num
  rw [ProximityGap.MCABandTwoExact.epsMCA_eq_two_div_card_of_dist4 C84
    ProximityGap.DeltaStarSecondPin.C84_noLowWeight (by rw [Fintype.card_fin]; norm_num)
    (le_of_eq h8.symm) (by rw [h8]; norm_num)
    (show (0 : Fin 8) ≠ 1 by decide) (show (1 : F17) ≠ 0 by decide)]
  rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
  norm_num

/-- The radius `1/8` is the grid radius of agreement `a = 7` at `n = 8`. -/
private theorem eighth_eq_grid :
    (1 - ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0)) = (1/8 : ℝ≥0) := by
  have h78 : ((7 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) = 7/8 := by
    rw [← NNReal.coe_inj]
    push_cast
    norm_num
  have h781 : (7/8 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  rw [h78, tsub_eq_iff_eq_add_of_le h781]
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- **The corrected v4 surface `MonomialDominationOffBoundary` is FALSE on `C84`** for every
crossing `ac ≤ 6` (unconditionally): the off-boundary row `a = 7` (`k + n + 1 = 13 ≤ 14 = 2a`)
has `ε_mca = 2/17` while the monomial family only reaches `1/17`. -/
theorem monomialDominationOffBoundary_refuted {ac : ℕ} (hac : ac ≤ 6) :
    ¬ MonomialDominationOffBoundary dom (C84 : Set (Fin 8 → F17)) 4 ac := by
  intro h
  have h7 := h 7 (by omega) (by norm_num) (by norm_num)
  rw [eighth_eq_grid, epsMCA_eighth_eq] at h7
  have hchain : (2 / 17 : ℝ≥0∞) ≤ 1 / 17 := le_trans h7 monomialEps_eighth_le
  have h17 : (17 : ℝ≥0∞) ≠ 0 := by norm_num
  have h17' : (17 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h21 : (2 : ℝ≥0∞) ≤ 1 := by
    calc (2 : ℝ≥0∞) = 2 / 17 * 17 := by rw [ENNReal.div_mul_cancel h17 h17']
      _ ≤ 1 / 17 * 17 := mul_le_mul_left hchain 17
      _ = 1 := by rw [ENNReal.div_mul_cancel h17 h17']
  exact absurd h21 (by norm_num)

end ProximityGap.MonomialDominationBoundaryRefuted

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.epsMCA_quarter_ge_seven
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.monomialDomination_refuted_of_monomial_bound
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.monomialEps_eighth_le
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.epsMCA_eighth_eq
#print axioms ProximityGap.MonomialDominationBoundaryRefuted.monomialDominationOffBoundary_refuted
