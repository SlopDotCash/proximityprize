/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothWindowSaturation

/-!
# The exact MCA census AT the Johnson radius: two-sided, kernel-checked

The half-pair's exact census is known at the UDR (`HalfPairSliceExact`) and the window
saturates at `5/8` (`SmoothWindowSaturation`). The remaining radius of the structured
regime at `(F₁₇, μ₈, 2)` is **the Johnson radius itself**, `δ = 1/2` (agreement 4) —
where the pure-agreement census saturates and only the MCA event (with the no-joint
clause) is the meaningful object. This file pins it, two-sided:

* `bad_of_mem` — the eight scalars of `μ₈` fire the event (probe-extracted size-4
  certificates through the saturation builder).
* `not_bad_of_notMem` — **the converse**: the nine other scalars do not. The brute
  decide is infeasible (the witness scan × affine scan blows up); the proof goes
  through the **agreement-set maximality reduction** (`coreJ_of_mcaEvent`): any witness
  `T` can be grown to the full agreement set `S` of the affine fit through two of its
  points — line agreement is automatic and the no-joint clause is *monotone* under
  growth (a joint explanation on `S` restricts to `T`). The event therefore implies a
  fit-indexed core (`coreJ`) with **no set quantifier**, and `¬coreJ` for the nine
  scalars is a feasible kernel `decide`.
* `johnson_badSet_eq` — the MCA-bad set of `(X⁵, X⁴)` at the Johnson radius is
  **exactly `μ₈`**, count `8 = n` (`johnson_badCount`).

With this, the half-pair's exact census is machine-checked at **all three structured
radii** of this instance — UDR (law level), Johnson (MCA level, this file), and the
in-window `5/8` (where a different pair saturates) — and the flat-`n` law on
`[UDR, Johnson]` is a closed two-sided theorem here.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357; `HalfPairSliceExact.lean`, `SmoothWindowSaturation.lean` (the builder),
  `TakeoverCountermodel.lean` (the certificate pattern).
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityGap.JohnsonExactPoint

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial Finset
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothWindowSaturation

/-- The domain as a Finset (`μ₈`). -/
def mu8 : Finset F17 := {1, 2, 4, 8, 16, 15, 13, 9}

/-- Row 0 of the Johnson stack: `x ↦ x⁵`. -/
def u5 : Fin 8 → F17 := fun i => dom8 i ^ 5

/-- Row 1: `x ↦ x⁴`. -/
def v4 : Fin 8 → F17 := fun i => dom8 i ^ 4

/-- The line word at scalar `λ`. -/
def lineW (lam : F17) : Fin 8 → F17 := fun i => u5 i + lam * v4 i

/-- The slope of the affine fit through points `i, j` of a word. -/
def fitC1 (w : Fin 8 → F17) (i j : Fin 8) : F17 :=
  (w j - w i) * (dom8 j - dom8 i)⁻¹

/-- The intercept of the affine fit. -/
def fitC0 (w : Fin 8 → F17) (i j : Fin 8) : F17 :=
  w i - fitC1 w i j * dom8 i

/-- The full agreement set of the fit through `i, j`. -/
def fitSet (w : Fin 8 → F17) (i j : Fin 8) : Finset (Fin 8) :=
  Finset.univ.filter (fun l => w l = fitC1 w i j * dom8 l + fitC0 w i j)

/-- A word is fit-affine on `S`: trivial small sets, or some internal fit covers `S`. -/
def affFit (w : Fin 8 → F17) (S : Finset (Fin 8)) : Prop :=
  S.card ≤ 1 ∨ ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
    ∀ l ∈ S, w l = fitC1 w i j * dom8 l + fitC0 w i j

instance (w : Fin 8 → F17) (S : Finset (Fin 8)) : Decidable (affFit w S) := by
  unfold affFit
  infer_instance

/-- The fit-indexed core: **no set quantifier** — some fit of the line has an agreement
set of size `≥ 4` on which the rows are not jointly fit-affine. -/
def coreJ (lam : F17) : Prop :=
  ∃ i j : Fin 8, i ≠ j ∧ 4 ≤ (fitSet (lineW lam) i j).card ∧
    ¬ (affFit u5 (fitSet (lineW lam) i j) ∧ affFit v4 (fitSet (lineW lam) i j))

instance (lam : F17) : Decidable (coreJ lam) := by
  unfold coreJ
  infer_instance

/-! ## The maximality bridge: the event implies the fit core -/

/-- An affine function agreeing with `w` on two distinct points is reproduced by the
fit through them (the domain is injective, so the denominator is a unit). -/
theorem fit_reproduces {w : Fin 8 → F17} {i j : Fin 8} (hij : i ≠ j)
    {c₁ c₀ : F17} (hi : w i = c₁ * dom8 i + c₀) (hj : w j = c₁ * dom8 j + c₀) :
    fitC1 w i j = c₁ ∧ fitC0 w i j = c₀ := by
  have hd : dom8 j - dom8 i ≠ 0 := by
    intro h0
    exact hij (dom8_injective (by linear_combination -h0))
  have hc1 : fitC1 w i j = c₁ := by
    unfold fitC1
    rw [hi, hj]
    field_simp
    ring
  refine ⟨hc1, ?_⟩
  unfold fitC0
  rw [hc1, hi]
  ring

/-- A fit-affine word on `S` is explained by a codeword of the degree-`< 2` code. -/
theorem codeword_of_affFit {w : Fin 8 → F17} {S : Finset (Fin 8)}
    (h : affFit w S) :
    ∃ c ∈ (evalCode dom8 2 : Set (Fin 8 → F17)), ∀ l ∈ S, c l = w l := by
  rcases h with hsmall | ⟨i, hi, j, hj, hij, hfit⟩
  · -- |S| ≤ 1: a constant explains it
    have hempty := Finset.card_le_one.mp hsmall
    by_cases hS : S.Nonempty
    · obtain ⟨l₀, hl₀⟩ := hS
      refine ⟨fun l => 0 * dom8 l + w l₀, affine_mem 0 (w l₀), fun l hl => ?_⟩
      have hll : l = l₀ := hempty l hl l₀ hl₀
      rw [hll]
      ring
    · refine ⟨fun l => 0 * dom8 l + 0, affine_mem 0 0,
        fun l hl => absurd ⟨l, hl⟩ hS⟩
  · exact ⟨fun l => fitC1 w i j * dom8 l + fitC0 w i j,
      affine_mem (fitC1 w i j) (fitC0 w i j), fun l hl => (hfit l hl).symm⟩

/-- **The maximality bridge:** the MCA event at the Johnson radius implies the fit
core — any witness grows to the full agreement set of one of its internal fits, and
the no-joint clause survives the growth (restriction monotonicity). -/
theorem coreJ_of_mcaEvent {lam : F17}
    (h : mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u5 v4 lam) :
    coreJ lam := by
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; norm_num)] at h
  obtain ⟨T, hcard, ⟨w, hw, hag⟩, hno⟩ := h
  -- the explanation is affine
  obtain ⟨q, hq, hw_eq⟩ := (mem_evalCode w).mp hw
  obtain ⟨c₁, c₀, hq_aff⟩ := exists_eq_X_add_C_of_natDegree_le_one hq
  have hline : ∀ l ∈ T, lineW lam l = c₁ * dom8 l + c₀ := by
    intro l hl
    have h1 : w l = lineW lam l := by
      rw [hag l hl]
      unfold lineW u5 v4
      rw [smul_eq_mul]
    have h2 : w l = c₁ * dom8 l + c₀ := by
      rw [hw_eq l, hq_aff]
      simp [eval_add, eval_mul, eval_C, eval_X]
    rw [← h1, h2]
  -- pick two distinct points of T
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (by omega : 1 < T.card)
  obtain ⟨hc1, hc0⟩ := fit_reproduces hij (hline i hi) (hline j hj)
  refine ⟨i, j, hij, ?_, ?_⟩
  · -- T sits inside the fit's agreement set
    refine le_trans hcard (Finset.card_le_card ?_)
    intro l hl
    rw [fitSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hc1, hc0]; exact hline l hl⟩
  · -- no-joint survives the growth
    rintro ⟨hu, hv⟩
    obtain ⟨cu, hcu_mem, hcu⟩ := codeword_of_affFit hu
    obtain ⟨cv, hcv_mem, hcv⟩ := codeword_of_affFit hv
    have hTsub : T ⊆ fitSet (lineW lam) i j := by
      intro l hl
      rw [fitSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hc1, hc0]; exact hline l hl⟩
    exact hno ⟨cu, hcu_mem, cv, hcv_mem, fun l hl =>
      ⟨hcu l (hTsub hl), hcv l (hTsub hl)⟩⟩

/-! ## The two sides -/

/-- The nine non-`μ₈` scalars do not satisfy the fit core (kernel `decide`). -/
theorem notCoreJ : ∀ lam : F17, lam ∉ mu8 → ¬ coreJ lam := by decide

/-- The eight `μ₈` scalars fire the event (probe-extracted certificates through the
saturation builder, adapted to the `(X⁵, X⁴)` stack at agreement 4). -/
theorem event_of_cert5 (lam c₁ c₀ : F17) (T : Finset (Fin 8))
    (hcard : 4 ≤ T.card)
    (hagree : ∀ i ∈ T, c₁ * dom8 i + c₀ = u5 i + lam * v4 i)
    (hfail : ∀ d₁ d₀ : F17, ¬ ∀ i ∈ T, u5 i = d₁ * dom8 i + d₀) :
    mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u5 v4 lam := by
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; norm_num)]
  refine ⟨T, hcard, ⟨fun i => c₁ * dom8 i + c₀, affine_mem c₁ c₀, fun i hi => ?_⟩, ?_⟩
  · rw [smul_eq_mul]
    exact hagree i hi
  · rintro ⟨w₀, hw₀, w₁, _, hag⟩
    obtain ⟨q', hq', hw₀'⟩ := (mem_evalCode w₀).mp hw₀
    obtain ⟨d₁, d₀, hq_eq⟩ := exists_eq_X_add_C_of_natDegree_le_one hq'
    refine hfail d₁ d₀ fun i hi => ?_
    have h1 : w₀ i = u5 i := (hag i hi).1
    have h2 : w₀ i = q'.eval (dom8 i) := hw₀' i
    rw [← h1, h2, hq_eq]
    simp [eval_add, eval_mul, eval_C, eval_X]

theorem bad_of_mem : ∀ lam ∈ mu8,
    mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
      (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u5 v4 lam := by
  intro lam hlam
  fin_cases hlam
  · exact event_of_cert5 1 16 16 {1, 3, 4, 5} (by decide) (by decide) (by decide)
  · exact event_of_cert5 2 1 2 {0, 2, 4, 5} (by decide) (by decide) (by decide)
  · exact event_of_cert5 4 16 13 {1, 3, 5, 6} (by decide) (by decide) (by decide)
  · exact event_of_cert5 8 1 8 {0, 2, 4, 7} (by decide) (by decide) (by decide)
  · exact event_of_cert5 16 16 1 {0, 1, 3, 5} (by decide) (by decide) (by decide)
  · exact event_of_cert5 15 1 15 {0, 1, 2, 4} (by decide) (by decide) (by decide)
  · exact event_of_cert5 13 16 4 {1, 2, 3, 5} (by decide) (by decide) (by decide)
  · exact event_of_cert5 9 1 9 {0, 2, 3, 4} (by decide) (by decide) (by decide)

/-! ## The exact point -/

open Classical in
/-- **The exact MCA census at the Johnson radius:** the bad set of `(X⁵, X⁴)` at
`δ = 1/2 = 1 − √ρ` is exactly `μ₈`. -/
theorem johnson_badSet_eq :
    (Finset.univ.filter (fun lam : F17 =>
      mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
        (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u5 v4 lam)) = mu8 := by
  apply Finset.Subset.antisymm
  · intro lam hlam
    rw [Finset.mem_filter] at hlam
    by_contra hnot
    exact notCoreJ lam hnot (coreJ_of_mcaEvent hlam.2)
  · intro lam hlam
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bad_of_mem lam hlam⟩

open Classical in
/-- The count is exactly `n = 8`: the flat-`n` law at the Johnson radius, two-sided. -/
theorem johnson_badCount :
    (Finset.univ.filter (fun lam : F17 =>
      mcaEvent (F := F17) (A := F17) (evalCode dom8 2 : Set (Fin 8 → F17))
        (1 - ((4 : ℕ) : ℝ≥0) / (Fintype.card (Fin 8) : ℝ≥0)) u5 v4 lam)).card = 8 := by
  rw [johnson_badSet_eq]
  decide

/-! ## Source audit -/

#print axioms coreJ_of_mcaEvent
#print axioms notCoreJ
#print axioms johnson_badSet_eq
#print axioms johnson_badCount

end ProximityGap.JohnsonExactPoint
