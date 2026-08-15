/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusLowerBound

/-!
# In-window saturation: the first unconditional exact `ε_mca` value inside the window
# for a smooth-domain RS code

For `RS[F₁₇, μ₈, 2]` (the smooth domain `μ₈ = ⟨2⟩`, rate `ρ = 1/4`, Johnson radius
`1/2`, capacity `3/4`) at the in-window grid radius `δ = 5/8 ∈ (1/2, 3/4)`:

  **`ε_mca(C, 5/8) = 1` exactly** (`epsMCA_window_saturates`).

The lower half is fully explicit: the monomial pair `(X⁴, X²)` is MCA-bad at **every**
scalar `λ ∈ F₁₇` — seventeen kernel-checked certificates (`event_of_cert` + the table),
each a 3-point witness with an affine explanation of the line and one row affinely
inexplicable there. The upper half is trivial (`Pr ≤ 1`).

**What this is.** The small-field saturation phenomenon — measured by the O139 probes
("the `a = k+1` window row saturates the field"), consumed as folklore in every
"the prize must fix `|F|` large" remark — as a two-sided theorem at a genuine smooth
instance, strictly inside the open Johnson–capacity window. Companion to the sibling's
`mcaDeltaStar_window_interior_eq` (the `F₁₁` interior pin on a *non-smooth* domain):
this is the smooth-domain side of the boundary map.

Ledger corollary (`mcaDeltaStar_le_of_window_saturation`): for **every** target
`ε* < 1` — in particular any cryptographic target — this smooth code's threshold is
capped mid-window: `δ*(C, ε*) ≤ 5/8`, unconditionally.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (O139 saturation; the window cartography); `TakeoverCountermodel.lean`
  (the certificate pattern), `CensusLowerBound.lean` (`evalCode`),
  `CensusConditionalPin.lean` (the `agreeOf` bridge).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.SmoothWindowSaturation

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound

instance primeFact_SmoothWindowSaturation_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

abbrev F17 := ZMod 17

/-- The smooth domain `μ₈ = ⟨2⟩ ⊆ F₁₇ˣ` in generator order. -/
def dom8 : Fin 8 → F17 := ![1, 2, 4, 8, 16, 15, 13, 9]

theorem dom8_injective : Function.Injective dom8 := by decide

/-- Row 0 of the saturating stack: `x ↦ x⁴` (the order-4 coset indicator). -/
def urow : Fin 8 → F17 := fun i => dom8 i ^ 4

/-- Row 1: `x ↦ x²`. -/
def vrow : Fin 8 → F17 := fun i => dom8 i ^ 2

/-- An affine function is a codeword of the degree-`< 2` evaluation code. -/
theorem affine_mem (c₁ c₀ : F17) :
    (fun i => c₁ * dom8 i + c₀) ∈ (evalCode dom8 2 : Set (Fin 8 → F17)) := by
  refine (mem_evalCode _).mpr ⟨C c₁ * X + C c₀, ?_, fun i => ?_⟩
  · show (C c₁ * X + C c₀).natDegree ≤ 1
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans natDegree_mul_le ?_
      simp [natDegree_C, natDegree_X]
    · simp [natDegree_C]
  · simp [eval_add, eval_mul, eval_C, eval_X]

/-- The certificate builder: a `≥ 3`-point witness, an affine explanation of the line,
and one row affinely inexplicable on the witness (kills any joint explanation). -/
theorem event_of_cert (lam c₁ c₀ : F17) (T : Finset (Fin 8)) (row : Fin 8 → F17)
    (hrow : row = urow ∨ row = vrow)
    (hcard : 3 ≤ T.card)
    (hagree : ∀ i ∈ T, c₁ * dom8 i + c₀ = urow i + lam * vrow i)
    (hfail : ∀ d₁ d₀ : F17, ¬ ∀ i ∈ T, row i = d₁ * dom8 i + d₀) :
    mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) urow vrow lam := by
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; norm_num)]
  refine ⟨T, hcard, ⟨fun i => c₁ * dom8 i + c₀, affine_mem c₁ c₀, fun i hi => ?_⟩, ?_⟩
  · rw [smul_eq_mul]
    exact hagree i hi
  · rintro ⟨w₀, hw₀, w₁, hw₁, hag⟩
    -- the failing row's joint codeword would be an affine function agreeing on T
    rcases hrow with hr | hr
    · obtain ⟨q', hq', hw₀'⟩ := (mem_evalCode w₀).mp hw₀
      obtain ⟨d₁, d₀, hq_eq⟩ := exists_eq_X_add_C_of_natDegree_le_one hq'
      refine hfail d₁ d₀ fun i hi => ?_
      rw [hr]
      show urow i = d₁ * dom8 i + d₀
      have h1 : w₀ i = urow i := (hag i hi).1
      have h2 : w₀ i = q'.eval (dom8 i) := hw₀' i
      rw [← h1, h2, hq_eq]
      simp [eval_add, eval_mul, eval_C, eval_X]
    · obtain ⟨q', hq', hw₁'⟩ := (mem_evalCode w₁).mp hw₁
      obtain ⟨d₁, d₀, hq_eq⟩ := exists_eq_X_add_C_of_natDegree_le_one hq'
      refine hfail d₁ d₀ fun i hi => ?_
      rw [hr]
      show vrow i = d₁ * dom8 i + d₀
      have h1 : w₁ i = vrow i := (hag i hi).2
      have h2 : w₁ i = q'.eval (dom8 i) := hw₁' i
      rw [← h1, h2, hq_eq]
      simp [eval_add, eval_mul, eval_C, eval_X]

/-- **Every scalar is bad** for `(X⁴, X²)` at the in-window radius `5/8`: the seventeen
probe-extracted certificates, each kernel-checked. -/
theorem all_bad (lam : F17) :
    mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) urow vrow lam := by
  have h : lam = 0 ∨ lam = 1 ∨ lam = 2 ∨ lam = 3 ∨ lam = 4 ∨ lam = 5 ∨ lam = 6 ∨
      lam = 7 ∨ lam = 8 ∨ lam = 9 ∨ lam = 10 ∨ lam = 11 ∨ lam = 12 ∨ lam = 13 ∨
      lam = 14 ∨ lam = 15 ∨ lam = 16 := by
    revert lam
    decide
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact event_of_cert _ 0 1 {0, 2, 4} vrow (Or.inr rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 14 5 {0, 6, 7} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 10 10 {0, 2, 5} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 0 4 {0, 3, 4} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 10 12 {0, 1, 7} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 0 13 {2, 3, 6} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 16 8 {0, 1, 6} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 2 6 {0, 1, 3} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 12 7 {1, 3, 6} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 3 7 {0, 3, 5} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 2 9 {0, 5, 7} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 4 8 {0, 2, 3} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 0 13 {0, 1, 4} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 11 12 {1, 2, 3} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 0 4 {1, 2, 5} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 6 10 {0, 3, 6} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)
  · exact event_of_cert _ 12 5 {0, 1, 2} urow (Or.inl rfl) (by decide) (by decide)
      (by decide)

open Classical in
/-- **In-window saturation, exact:** `ε_mca(RS[F₁₇, μ₈, 2], 5/8) = 1` — the first
unconditional exact in-window `ε_mca` value for a smooth-domain RS code. The radius
`5/8` lies strictly inside the window `(1/2, 3/4) = (1 − √ρ, 1 − ρ)`. -/
theorem epsMCA_window_saturates :
    epsMCA (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) = 1 := by
  refine le_antisymm (iSup_le fun u => Pr_le_one _ _) ?_
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F17) (A := F17) _ _ ![urow, vrow])
  have h0 : (![urow, vrow] : WordStack F17 (Fin 2) (Fin 8)) 0 = urow := rfl
  have h1 : (![urow, vrow] : WordStack F17 (Fin 2) (Fin 8)) 1 = vrow := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card,
    Finset.filter_true_of_mem (fun lam _ => all_bad lam), Finset.card_univ]
  rw [ENNReal.coe_natCast]
  exact le_of_eq (ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero)
    (by simp)).symm

open Classical in
/-- **Ledger corollary:** for every target `ε* < 1`, the smooth code's threshold is
capped mid-window: `δ*(C, ε*) ≤ 5/8`, unconditionally. -/
theorem mcaDeltaStar_le_of_window_saturation {εstar : ℝ≥0∞} (hε : εstar < 1) :
    mcaDeltaStar (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17)) εstar
      ≤ 1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _ (by rw [epsMCA_window_saturates]; exact hε)

/-- The radius is strictly inside the window: `1/2 < 5/8 < 3/4`. -/
theorem radius_in_window :
    (1 - ((3 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0) : ℝ≥0) = 5/8 := by
  rw [Fintype.card_fin]
  have h38 : ((3 : ℕ) : ℝ≥0) / ((8 : ℕ) : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < ((8 : ℕ) : ℝ≥0))]
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 8)
  apply NNReal.coe_injective
  rw [NNReal.coe_sub h38]
  push_cast
  norm_num

/-! ## Source audit -/

#print axioms all_bad
#print axioms epsMCA_window_saturates
#print axioms mcaDeltaStar_le_of_window_saturation

end ProximityGap.SmoothWindowSaturation
