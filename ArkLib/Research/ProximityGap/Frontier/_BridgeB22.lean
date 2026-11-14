/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B22 (target E4): windows of constraints CUT the bad-γ set

**Spec B22 / target E4.** The empirical cascade `D*(m)` (the worst-direction over-determined
far-line incidence at over-determination depth `m`) is *decreasing* in `m`:
adding a window of constraints can only shrink the bad-γ set.  The empirical decay
`D*(1) ≈ n³ → … → budget` (issue #444 KB `deltastar-444-empirical-formulas-and-bridges`, E4)
is, at the *structural* level, an instance of the elementary fact that an intersection of
affine/ratio conditions has cardinality monotone in the number of conditions.

This file makes that structural skeleton precise and axiom-clean, building directly on the
substrate `IncidencePeriodBridge.lineIncidence` (P2 / face F1 of the open core).

## Model

A *window* is a predicate `p i : F → Prop` (decidable) — the `i`-th over-determination
constraint a candidate direction must satisfy.  The **depth-`W` bad set** is the set of
scalars `γ` satisfying *every* window in a finite index set `W`:

  `multiWindowBad p W = { γ : F | ∀ i ∈ W, p i γ }`,   `D(p, W) = #(multiWindowBad p W)`.

The empirical `D*(m)` is `D(p, W)` for the worst direction and a depth-`m` window set
`W = Finset.range m`.  The two facts B22 asserts:

* **`multiWindow_anti`** — *windows cut the set.*  `W ⊆ W' ⟹ D(p, W') ≤ D(p, W)`:
  more windows (a deeper over-determination) gives a smaller-or-equal count.  Specializing
  to `W = ∅ ⊆ Finset.range m` recovers the leading-value bound
  `D*(m) ≤ D*(0) = #F` and to `Finset.range m ⊆ Finset.range m'` (`m ≤ m'`) recovers
  the cascade monotonicity `D*(m') ≤ D*(m)`.

* **`multiWindow_le_ratio_count`** — *codimension count.*  The depth-`W` bad set is a
  *subset* of the solution set of any one of its windows, so `D(p, W)` is bounded by the
  count of `γ` solving the corresponding ratio equation; in particular it is bounded by the
  count solving *all* `m` ratio equations (which is the set itself).

* **`multiWindow_single_eq_lineIncidence`** — *reconnection to the substrate.*  A single
  window whose predicate is the membership constraint `s₀ + γ·s₁ ∈ G` reproduces the far-line
  incidence `lineIncidence G s₀ s₁` of `IncidencePeriodBridge` exactly.  So the multi-window
  count is a genuine refinement of the period-spectrum incidence object, and the `m = 1` rung
  of the cascade is the proven F1 = F2 incidence.

Everything is finite-combinatorial (`Finset.card` monotonicity of filters); axiom-clean.
Issue #444, target E4.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB22

open ArkLib.ProximityGap.IncidencePeriodBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The depth-`W` bad set.** Scalars `γ` satisfying every window predicate `p i` for
`i ∈ W`. `W` indexes the over-determination windows; `p i` is the `i`-th ratio/affine
constraint. -/
noncomputable def multiWindowBad {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] (W : Finset ι) : Finset F :=
  Finset.univ.filter (fun γ : F => ∀ i ∈ W, p i γ)

/-- **The depth-`W` bad-γ count** `D(p, W)`. The empirical `D*(m)` is this for the worst
direction and `W = Finset.range m`. -/
noncomputable def multiWindowCount {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] (W : Finset ι) : ℕ :=
  (multiWindowBad p W).card

/-! ### Windows cut the set: monotonicity in the window index set -/

/-- **Windows cut the bad set (set form).** A larger window family carves out a smaller bad
set: the depth-`W'` bad set is contained in the depth-`W` bad set whenever `W ⊆ W'`. -/
theorem multiWindowBad_subset {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] {W W' : Finset ι} (hWW' : W ⊆ W') :
    multiWindowBad p W' ⊆ multiWindowBad p W := by
  classical
  intro γ hγ
  simp only [multiWindowBad, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
  intro i hi
  exact hγ i (hWW' hi)

/-- **Windows cut the bad-γ count (E4 monotonicity).** `W ⊆ W' ⟹ D(p, W') ≤ D(p, W)`:
adding windows (deeper over-determination) can only shrink the count.  This is the structural
content of the empirical cascade decay `D*(1) ≥ D*(2) ≥ …` (E4). -/
theorem multiWindow_anti {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] {W W' : Finset ι} (hWW' : W ⊆ W') :
    multiWindowCount p W' ≤ multiWindowCount p W :=
  Finset.card_le_card (multiWindowBad_subset p hWW')

/-- **Leading-value bound `D*(m) ≤ #F`.** The depth-`m` bad-γ count never exceeds the field
size — the trivial top of the cascade (E4: `D*(0) = #F`, `D*(1) ≈ n³`, decaying to budget). -/
theorem multiWindow_le_card {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] (W : Finset ι) :
    multiWindowCount p W ≤ Fintype.card F := by
  classical
  simpa [multiWindowCount, multiWindowBad] using
    (Finset.card_filter_le Finset.univ (fun γ : F => ∀ i ∈ W, p i γ)).trans
      (le_of_eq (Finset.card_univ))

/-- **Cascade monotonicity in depth** (the `W = Finset.range m` specialization of
`multiWindow_anti`).  A deeper over-determination `m ≤ m'` gives a smaller-or-equal count:
`D*(m') ≤ D*(m)`. -/
theorem multiWindow_range_anti (p : ℕ → F → Prop) [∀ i, DecidablePred (p i)]
    {m m' : ℕ} (hmm' : m ≤ m') :
    multiWindowCount p (Finset.range m') ≤ multiWindowCount p (Finset.range m) :=
  multiWindow_anti p (Finset.range_subset_range.mpr hmm')

/-! ### Codimension count: each window is a ratio equation the bad γ must solve -/

/-- **Codimension bound (single ratio equation).** The depth-`W` bad set is contained in the
solution set `{γ : p i γ}` of any *single* window `i ∈ W`.  Hence the depth-`W` count is
bounded by the count of `γ` solving that one ratio equation. -/
theorem multiWindow_le_single {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] {W : Finset ι} {i : ι} (hi : i ∈ W) :
    multiWindowCount p W ≤ (Finset.univ.filter (fun γ : F => p i γ)).card := by
  classical
  refine Finset.card_le_card ?_
  intro γ hγ
  simp only [multiWindowBad, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hγ i hi

/-- **Codimension count (the bad set IS the m-ratio-equation solution set).** The depth-`W`
bad-γ count equals the count of `γ` solving *all* the window ratio equations simultaneously
(the depth-`W` count is literally the cardinality of that intersection).  This is the
"intersection of affine conditions; codimension count" form of E4. -/
theorem multiWindow_eq_ratio_count {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] (W : Finset ι) :
    multiWindowCount p W = (Finset.univ.filter (fun γ : F => ∀ i ∈ W, p i γ)).card := rfl

/-! ### Reconnection to the substrate: one window = far-line incidence -/

/-- **The single membership window reproduces the far-line incidence.** Taking one window
whose predicate is `γ ↦ s₀ + γ·s₁ ∈ G`, the depth-`{i}` bad-γ count is exactly the substrate
incidence `lineIncidence G s₀ s₁` of `IncidencePeriodBridge`.  So the `m = 1` rung of the
cascade is the proven F1 = F2 incidence object, and the multi-window count is a faithful
refinement of it (deeper rungs intersect more such constraints). -/
theorem multiWindow_single_eq_lineIncidence {ι : Type*} [DecidableEq ι]
    (G : Finset F) (s₀ s₁ : F) (i : ι) :
    multiWindowCount (fun (_ : ι) (γ : F) => s₀ + γ * s₁ ∈ G) {i}
      = lineIncidence G s₀ s₁ := by
  classical
  simp only [multiWindowCount, multiWindowBad, lineIncidence]
  congr 1
  apply Finset.filter_congr
  intro γ _
  constructor
  · intro h; exact h i (Finset.mem_singleton_self i)
  · intro h j hj; exact h

/-- **Cascade upper bound from the incidence (combining the two faces).** When window `i` is
the membership constraint `s₀ + γ·s₁ ∈ G`, the deep (depth-`W`, `i ∈ W`) bad-γ count is
bounded by the proven far-line incidence `lineIncidence G s₀ s₁`.  This is the bridge B22
deliverable: *more windows ≤ the substrate incidence*, the structural skeleton of the E4 decay
toward budget. -/
theorem multiWindow_le_lineIncidence {ι : Type*} [DecidableEq ι]
    (G : Finset F) (s₀ s₁ : F) {W : Finset ι} {i : ι} (hi : i ∈ W) :
    multiWindowCount (fun (_ : ι) (γ : F) => s₀ + γ * s₁ ∈ G) W
      ≤ lineIncidence G s₀ s₁ := by
  classical
  calc multiWindowCount (fun (_ : ι) (γ : F) => s₀ + γ * s₁ ∈ G) W
      ≤ (Finset.univ.filter (fun γ : F => s₀ + γ * s₁ ∈ G)).card :=
        multiWindow_le_single _ hi
    _ = lineIncidence G s₀ s₁ := rfl

/-! ### The honest quantitative gap to E4 (explicit named reduction)

Everything above is *structural*: monotonicity of a filter-intersection and its reconnection to
the proven substrate `lineIncidence`.  The empirical E4 content — `D*(1) ≈ n³` and the geometric
decay to budget so that some depth-`m*` window family cuts the count below the prize budget — is
NOT proved by the skeleton.  It requires the concrete *algebraic* ratio equations (the
over-determination constraints of RS-closeness) and a count of their common solutions.  We state
that exact remaining obligation as a named `Prop` and discharge the E4 budget-crossing *modulo*
it.  This is the project's modularity convention (a REDUCED bridge: the target follows from one
explicitly named hypothesis), not a closure. -/

/-- **The named quantitative obligation (E4 budget-crossing input).**  At a binding depth-`m`
window family `W` there is a single window `i ∈ W` whose *concrete ratio-equation* solution set
`{γ : p i γ}` already has at most `budget` solutions.  This is the algebraic heart of E4 — that
the over-determination ratio equations are genuinely low-degree / sparse enough to cut the count
to the prize budget — and is exactly the part the skeleton does NOT establish. -/
def RatioBudgetWitness {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] (W : Finset ι) (budget : ℕ) : Prop :=
  ∃ i ∈ W, (Finset.univ.filter (fun γ : F => p i γ)).card ≤ budget

/-- **E4 budget-crossing, REDUCED to `RatioBudgetWitness`.**  Given the named obligation that
some window in `W` already has `≤ budget` ratio-equation solutions, the depth-`W` bad-γ count is
`≤ budget`.  Combined with `multiWindow_anti` this is the structural form of E4: the cascade
`D*(m)` is monotone (skeleton, proved unconditionally above) and *crosses* the budget once the
named ratio-equation count does (the algebraic input, named here, not proved). -/
theorem multiWindow_le_budget_of_witness {ι : Type*} (p : ι → F → Prop)
    [∀ i, DecidablePred (p i)] {W : Finset ι} {budget : ℕ}
    (h : RatioBudgetWitness p W budget) :
    multiWindowCount p W ≤ budget := by
  classical
  obtain ⟨i, hi, hcard⟩ := h
  exact (multiWindow_le_single p hi).trans hcard

end ArkLib.ProximityGap.BridgeB22

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindowBad_subset
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_anti
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_le_card
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_range_anti
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_le_single
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_eq_ratio_count
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_single_eq_lineIncidence
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_le_lineIncidence
#print axioms ArkLib.ProximityGap.BridgeB22.multiWindow_le_budget_of_witness
