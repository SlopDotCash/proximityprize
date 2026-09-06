/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize

/-!
# B2 — the structured close-set budget brick (issue #466, lane W1)

**The named target.** Dossier v3 §6 Tier 3 and `Frontier/README.md` both point at a brick named
`curveDecodable_of_structured_close_set_budget` as the Lean-actionable step of the folded-RS
capacity pin ([JLR] 2601.10047 Lemma 5.12 + [GG25] 2025/2054); until this file that name existed
only in documentation. This file supplies it, as a strict generalization of the in-tree
pigeonhole `curveDecodable_of_curveListSize` (`GG25CurveDecodFromListSize.lean`):

* `CurveCoverBudget C ℓ δ m e` — **the structured close-set budget**: for every admissible
  instance `(u, f)` there are at most `m` codeword curves explaining all but at most `e` of the
  close seeds. Unlike `CurveListSizeLe` (a per-seed total assignment, defect `e = 0`), the
  budget tolerates an *unexplained defect* `e` — the shape a capacity-style list-recovery /
  subspace-design argument actually outputs (an `η`-fraction of seeds may escape the list).
* `curveDecodable_of_structured_close_set_budget` — **the brick**: a budget `(m, e)` gives
  `(ℓ, δ, a, b)`-curve-decodability whenever `m·b + e ≤ a`. Lossless pigeonhole on the
  explained part of the close set.
* `curveCoverBudget_of_curveListSize` — the recovery: a curve list-size `≤ m` is exactly a
  budget `(m, 0)` (for submodule codes), so the new brick strictly generalizes
  `curveDecodable_of_curveListSize` (re-derived as `curveDecodable_of_curveListSize'`).
* `CurveCoverBudget.mono_defect` — structural API: budgets weaken in the defect `e`.
* `mca_of_structured_close_set_budget` — **the end-to-end chain**: budget `(m, e)` with
  `m·b + e ≤ a` and `ℓ < b` gives the [GG25] Theorem 3.3 mutual-correlated-agreement
  conclusion (a single codeword curve within `(b/(b−ℓ))·δ` at *every* seed), by composing with
  the proven `all_seeds_relClose_of_curveDecodable`.
* `GG25ListRecoveryBudget` + `mca_of_gg25ListRecoveryBudget` — the **named-hypothesis wrapper**
  for the folded/multiplicity/random-RS input: [GG25] (ePrint 2025/2054, NOT on this checkout —
  see `/PAPERS_NEEDED.md`) proves the list-recovery/subspace-design step for those families with
  `m = O(1/η)` and field size `≳ 1/η²`; the wrapper is that step abstracted to its numerical
  content `(m, e)`, stated as an explicit named `Prop` per the residual convention. Discharging
  it for the interleaved/folded code (via `rowwiseCode`, `GG25ExactPreservation.lean`) is the
  remaining producer work of the folded pin; discharging it for **explicit plain RS above
  Johnson** is the open wall (`RSCurveListSizeResidual` / BCHKS Conj 1.12 — DISPROOF_LOG C43).

**Honest scope.** Everything proven here is unconditional pigeonhole/plumbing, axiom-clean
`[propext, Classical.choice, Quot.sound]`. Nothing here advances the open plain-RS list-size;
the brick makes the *defect-tolerant* producer interface exist so the [GG25]/[JLR] folded input
can land against it as a single named hypothesis.

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7 / §5.
* [JLR] arXiv 2601.10047, Lemma 5.12 (folded-RS capacity). Issue #466 lane W1 (B2).
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.B2Budget

open ProximityGap ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The structured close-set budget -/

/-- **The structured close-set budget.** `C` admits an `(m, e)`-budget at `(ℓ, δ)` if for every
stack `u` and codeword-valued `f` there are at most `m` codeword curves such that all but at
most `e` seeds of the close set are *explained* (`f α` equals one of the curves at `α`). The
defect `e` is what distinguishes this from `CurveListSizeLe` (`= (m, 0)`,
`curveCoverBudget_of_curveListSize`): a capacity-style list-recovery argument may leave an
`η`-fraction of seeds unexplained, and the budget interface absorbs that loss. -/
def CurveCoverBudget (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (m e : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
    ∃ curves : Fin m → Fin (ℓ + 1) → ι → A, (∀ t j, curves t j ∈ C) ∧
      (curveCloseSet δ u f).card ≤
        ((curveCloseSet δ u f).filter
          (fun α => ∃ t : Fin m,
            f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • curves t j i)).card + e

/-- Budgets weaken in the defect: an `(m, e)`-budget is an `(m, e')`-budget for any `e ≤ e'`. -/
theorem CurveCoverBudget.mono_defect {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {m e e' : ℕ}
    (h : CurveCoverBudget (F := F) C ℓ δ m e) (he : e ≤ e') :
    CurveCoverBudget (F := F) C ℓ δ m e' := by
  intro u f hf
  obtain ⟨curves, hmem, hcover⟩ := h u f hf
  exact ⟨curves, hmem, le_trans hcover (by omega)⟩

/-! ### The brick: curve decodability from a budget -/

/-- **The structured close-set budget brick** (the named target of dossier v3 §6 Tier 3 /
`Frontier/README.md`). An `(m, e)`-budget at `(ℓ, δ)` gives `(ℓ, δ, a, b)`-curve-decodability
whenever `m·b + e ≤ a`: at least `a − e ≥ m·b` close seeds are explained by one of the `m`
curves, so some single curve explains `≥ b` of them — lossless pigeonhole, tolerating the
defect `e`. At `e = 0` this is exactly `curveDecodable_of_curveListSize`'s budget. -/
theorem curveDecodable_of_structured_close_set_budget {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {m e a b : ℕ} (hm : 1 ≤ m) (hab : m * b + e ≤ a)
    (h : CurveCoverBudget (F := F) C ℓ δ m e) :
    CurveDecodable (F := F) C ℓ δ a b := by
  classical
  intro u f hf hclose
  obtain ⟨curves, hmem, hcover⟩ := h u f hf
  set S := curveCloseSet δ u f with hS
  set E := S.filter (fun α => ∃ t : Fin m,
    f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • curves t j i) with hE
  -- The explained-seed selector: at explained seeds, a chosen explaining curve index.
  set g : F → Fin m := fun α =>
    if hα : ∃ t : Fin m, f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • curves t j i
    then hα.choose else ⟨0, hm⟩ with hg
  have hmaps : ∀ α ∈ E, g α ∈ (univ : Finset (Fin m)) := fun α _ => mem_univ _
  have hne : (univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, mem_univ _⟩
  -- Pigeonhole: `m·b ≤ |E|` since `m·b + e ≤ a ≤ |S| ≤ |E| + e`.
  have hmul : (univ : Finset (Fin m)).card * b ≤ E.card := by
    have h1 : a ≤ E.card + e := le_trans hclose hcover
    have h2 : m * b ≤ E.card := by omega
    simpa [Finset.card_univ, Fintype.card_fin] using h2
  obtain ⟨t, _, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hne hmul
  refine ⟨curves t, fun j => hmem t j, ?_⟩
  refine le_trans hfiber (Finset.card_le_card ?_)
  intro α hα
  rw [Finset.mem_filter] at hα
  obtain ⟨hαE, hgt⟩ := hα
  rw [hE, Finset.mem_filter] at hαE
  obtain ⟨hαS, hex⟩ := hαE
  rw [Finset.mem_filter]
  refine ⟨hαS, ?_⟩
  have hspec := hex.choose_spec
  rw [hg] at hgt
  simp only [dif_pos hex] at hgt
  rw [hgt] at hspec
  exact hspec

/-! ### The recovery: a curve list-size is a zero-defect budget -/

/-- **A curve list-size `≤ m` is exactly an `(m, 0)`-budget** (submodule codes): enumerate the
`≤ m` distinct curves of the assignment's image; every close seed is explained by its own
assigned curve. Hence the budget brick strictly generalizes the list-size route. -/
theorem curveCoverBudget_of_curveListSize (C : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0} {m : ℕ}
    (h : CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ m) :
    CurveCoverBudget (F := F) (C : Set (ι → A)) ℓ δ m 0 := by
  classical
  intro u f hf
  obtain ⟨asgn, hcard⟩ := h u f hf
  set L := (curveCloseSet δ u f).image asgn.chooseCurve with hL
  set curves : Fin m → Fin (ℓ + 1) → ι → A := fun t =>
    if ht : (t : ℕ) < L.card then ((L.equivFin.symm ⟨(t : ℕ), ht⟩ : L) : Fin (ℓ + 1) → ι → A)
    else 0 with hcurves
  have hcurves_mem : ∀ t j, curves t j ∈ (C : Set (ι → A)) := by
    intro t j
    rw [hcurves]
    by_cases ht : (t : ℕ) < L.card
    · simp only [dif_pos ht]
      have hmem : ((L.equivFin.symm ⟨(t : ℕ), ht⟩ : L) : Fin (ℓ + 1) → ι → A)
          ∈ (curveCloseSet δ u f).image asgn.chooseCurve :=
        (L.equivFin.symm ⟨(t : ℕ), ht⟩).2
      obtain ⟨α₀, _, hα₀⟩ := Finset.mem_image.mp hmem
      rw [← hα₀]
      exact asgn.mem_code α₀ j
    · simp only [dif_neg ht]
      exact C.zero_mem
  refine ⟨curves, hcurves_mem, ?_⟩
  rw [Nat.add_zero]
  apply Finset.card_le_card
  intro α hα
  rw [Finset.mem_filter]
  refine ⟨hα, ?_⟩
  have hmemL : asgn.chooseCurve α ∈ L := by rw [hL]; exact Finset.mem_image_of_mem _ hα
  set i := L.equivFin ⟨asgn.chooseCurve α, hmemL⟩ with hi
  have hlt : (i : ℕ) < m := lt_of_lt_of_le i.isLt hcard
  refine ⟨⟨(i : ℕ), hlt⟩, ?_⟩
  have hct : curves ⟨(i : ℕ), hlt⟩ = asgn.chooseCurve α := by
    have hval : ((⟨(i : ℕ), hlt⟩ : Fin m) : ℕ) < L.card := i.isLt
    rw [hcurves]
    simp only [dif_pos hval]
    have hfin : (⟨((⟨(i : ℕ), hlt⟩ : Fin m) : ℕ), hval⟩ : Fin L.card) = i := by
      apply Fin.ext
      rfl
    rw [hfin, hi, Equiv.symm_apply_apply]
  rw [hct]
  exact asgn.passes_through α hα

/-- Sanity re-derivation: the in-tree `curveDecodable_of_curveListSize` is the `e = 0` corner
of the budget brick (for submodule codes) — the generalization is conservative. -/
theorem curveDecodable_of_curveListSize' (C : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {m a b : ℕ} (hm : 1 ≤ m) (hmb : m * b ≤ a)
    (h : CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ m) :
    CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_structured_close_set_budget hm (by omega)
    (curveCoverBudget_of_curveListSize C h)

/-! ### The end-to-end chain: budget ⟹ mutual correlated agreement -/

/-- **The budget-to-MCA chain** ([GG25] Theorem 3.3 fed by the budget brick). An `(m, e)`-budget
with `m·b + e ≤ a` and `ℓ < b`: every instance whose close set reaches `a` admits a *single*
codeword curve within relative Hamming distance `(b/(b−ℓ))·δ` of the tested curve at **every**
seed — the mutual-correlated-agreement conclusion. This is the consumer shape the folded-RS
capacity pin needs; its producer input is exactly the budget hypothesis. -/
theorem mca_of_structured_close_set_budget {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {m e a b : ℕ} (hm : 1 ≤ m) (hab : m * b + e ≤ a) (hlt : ℓ < b)
    (h : CurveCoverBudget (F := F) C ℓ δ m e)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
            ≤ ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ :=
  all_seeds_relClose_of_curveDecodable hlt
    (curveDecodable_of_structured_close_set_budget hm hab h) hf hclose

/-! ### The named [GG25] producer input (folded / multiplicity / random RS) -/

/-- **The [GG25] list-recovery input, as a named hypothesis** (residual convention; the paper
ePrint 2025/2054 is not on this checkout — `/PAPERS_NEEDED.md`). For folded-RS / multiplicity /
random-RS / subspace-design codes, [GG25] proves the list-recovery/subspace-design step with
`m = O(1/η)` at field size `≳ 1/η²`; this `Prop` is that step abstracted to its numerical
content: an `(m, e)` structured close-set budget for the code. Discharging it for the
interleaved (`rowwiseCode`) folded code is the remaining producer work of the Tier-3 folded
capacity pin; for explicit plain RS above Johnson it is the open wall (BCHKS Conj 1.12,
DISPROOF_LOG C43). -/
def GG25ListRecoveryBudget (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (m e : ℕ) : Prop :=
  CurveCoverBudget (F := F) C ℓ δ m e

/-- The folded-pin conditional, in one theorem: the named [GG25] input ⟹ mutual correlated
agreement at spread radius `(b/(b−ℓ))·δ`. The *only* open antecedent is the named budget. -/
theorem mca_of_gg25ListRecoveryBudget {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {m e a b : ℕ} (hm : 1 ≤ m) (hab : m * b + e ≤ a) (hlt : ℓ < b)
    (h : GG25ListRecoveryBudget (F := F) C ℓ δ m e)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
            ≤ ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ :=
  mca_of_structured_close_set_budget hm hab hlt h hf hclose

end ProximityGap.B2Budget

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.B2Budget.curveDecodable_of_structured_close_set_budget
#print axioms ProximityGap.B2Budget.curveCoverBudget_of_curveListSize
#print axioms ProximityGap.B2Budget.curveDecodable_of_curveListSize'
#print axioms ProximityGap.B2Budget.mca_of_structured_close_set_budget
#print axioms ProximityGap.B2Budget.mca_of_gg25ListRecoveryBudget
#print axioms ProximityGap.B2Budget.CurveCoverBudget.mono_defect
