/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# Door IV window-concentration is energy-blind: the single-window small-ball functional only
# yields the trivial linear ceiling `|η_b| ≤ n`

This file records the axiom-clean arithmetic kernel behind the probe
`scripts/probes/probe_dooriv_phaseset_anticoncentration.py` and its discriminator follow-up
`scripts/probes/probe_dooriv_smallball_vs_energy.py`.

## The probed object

For a worst frequency `b`, the period is `η_b = Σ_{y ∈ μ_n} e_p(b·y)`, a sum of `n` unit-modulus
complex numbers. A natural door-(iv) anti-concentration hope is that the additive **spread** of the
phase set `A_b = { b·y mod p }` carries the √-cancellation: if `A_b` were forced to concentrate in
a short arc (small-ball), one would read off a sup-norm bound *without* a moment/completion.

## The probe verdict (reproducible, in the prize regime, proper `μ_n`, p ≫ n³, incl. Fermat 65537)

The coarse window-concentration functional
`C_b = max over arcs W of length p/n of #{ y : b·y mod p ∈ W }`
**fails on both axes**:

* `C_worst / √n → 0` (measured 3.0, 1.59, 1.50, 1.06, 0.625 at n = 16,32,64,128,256): the worst
  window count is *sub*-√n, essentially flat (~10–12 points) — it is far **below** the √n scale, so
  it cannot be the prize object.
* `C_b` **decorrelates from `|η_b|`**: Spearman(|η|, C) collapses (0.49, 0.19, 0.11, 0.07, 0.046)
  and the argmax of `C` decouples from the argmax of `|η|` — at the actual worst `b` for `|η|`, `C`
  is *not* maximal. So `C_b` is not a repackaging of the sup-norm; coarse spatial clustering is **not**
  the mechanism producing a large `|η_b|` (that mechanism is fine phase coherence = the energy object).

## The formalizable kernel (this file)

The reason a single-window concentration count cannot bound the cancellation is purely the triangle
inequality with unit-modulus terms: splitting the `n` summands into the `C` lying in the chosen
window and the `n − C` outside, **each** out-of-window term still has modulus `1`, so the only bound a
single window yields is `|η_b| ≤ C·1 + (n − C)·1 = n` — the **trivial linear ceiling**, independent of
`C`. No choice of window (no matter how concentrated) lowers this below `n`. This is the constraint
lemma: the single-window small-ball functional is energy-blind in the cancellation direction.

This proves *nothing* about CORE and uses no moment/completion; it is a no-go pin saying the
single-window phase-concentration route gives only `n`, matching the probe's `C/√n → 0` degeneracy.
-/

namespace ProximityGap.Frontier.DoorIVWindowConcentrationTrivial

open Finset

variable {ι : Type*}

/-- A "phase vector": each summand has modulus exactly one (the values `e_p(b·y)` on `μ_n`). -/
def IsPhaseVector (f : ι → ℂ) (s : Finset ι) : Prop := ∀ i ∈ s, ‖f i‖ = 1

/-- The triangle bound for the in/out-window split of a unit-modulus character sum.

`W` is the in-window index set (those `i` with `b·y_i mod p` in the chosen short arc); the rest of
`s` is out-of-window. Each term has modulus `1`, so the partial sum over the window has modulus
`≤ |W|` and the out-of-window remainder has modulus `≤ |s \ W|`, giving the total bound `|s|`.

This is the **single-window concentration ceiling**: the only thing a window count buys is the
trivial split `|W| + |s \ W| = |s|`. -/
theorem norm_sum_le_card_of_phase
    {f : ι → ℂ} {s : Finset ι} (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) := by
  calc ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ = ∑ _i ∈ s, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi; exact hf i hi
    _ = (s.card : ℝ) := by simp

/-- The in/out-window decomposition makes the energy-blindness explicit: choosing **any** window
`W ⊆ s` and bounding each block by its cardinality recovers exactly the trivial ceiling `|s|`,
*independently of `|W|`*. So the single-window concentration count `|W|` cannot lower the bound. -/
theorem window_split_bound_is_trivial [DecidableEq ι]
    {f : ι → ℂ} {s W : Finset ι} (hW : W ⊆ s) (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤ (W.card : ℝ) + ((s \ W).card : ℝ) := by
  have hnat : W.card + (s \ W).card = s.card := by
    rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hW
  have hcard : (W.card : ℝ) + ((s \ W).card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hnat
  rw [hcard]
  exact norm_sum_le_card_of_phase hf


/-- Even splitting into **two** disjoint windows is still energy-blind: the triangle decomposition into
`W₁`, `W₂`, and the complement of their union recovers exactly the same trivial ceiling `|s|`.
Thus replacing a single coarse arc by two coarse arcs does not create a cancellation bound; only
additional phase information inside the pieces could improve the estimate. -/
theorem two_window_split_rhs_constant [DecidableEq ι]
    {s W₁ W₂ : Finset ι} (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂) :
    (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) = (s.card : ℝ) := by
  have hU : W₁ ∪ W₂ ⊆ s := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx₁ | hx₂
    · exact h₁ hx₁
    · exact h₂ hx₂
  have hnatU : (W₁ ∪ W₂).card = W₁.card + W₂.card := by
    exact Finset.card_union_of_disjoint hdis
  have hnatS : (s \ (W₁ ∪ W₂)).card + (W₁ ∪ W₂).card = s.card := by
    exact Finset.card_sdiff_add_card_eq_card hU
  have hnat : W₁.card + W₂.card + (s \ (W₁ ∪ W₂)).card = s.card := by
    rw [← hnatU, add_comm, hnatS]
  exact_mod_cast hnat

/-- Two-window version of `window_split_bound_is_trivial`: after splitting a unit-modulus sum into two
chosen windows and the outside remainder, the triangle bound is still just `|s|`. This is the formal
no-go for a two-window small-ball certificate of door-(iv) cancellation. -/
theorem two_window_split_bound_is_trivial [DecidableEq ι]
    {f : ι → ℂ} {s W₁ W₂ : Finset ι}
    (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂) (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤
      (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) := by
  rw [two_window_split_rhs_constant h₁ h₂ hdis]
  exact norm_sum_le_card_of_phase hf

/-- Arbitrarily many disjoint coarse windows are still triangle-blind: if a finite family `Ω` of
windows is pairwise disjoint and every window lies inside `s`, then the total split into all windows
plus the outside complement has cardinality exactly `|s|`.  This is the finite-partition version of
the small-ball no-go: adding more coarse arcs cannot by itself improve the linear ceiling. -/
theorem multi_window_split_rhs_constant [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id) :
    (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) = (s.card : ℝ) := by
  have hU : Ω.biUnion id ⊆ s := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨W, hW, hxW⟩
    exact hsub W hW hxW
  have hcardU : (Ω.biUnion id).card = ∑ W ∈ Ω, W.card := by
    simpa using (Finset.card_biUnion hdis : (Ω.biUnion id).card = ∑ W ∈ Ω, (id W).card)
  have hnatS : (s \ Ω.biUnion id).card + (Ω.biUnion id).card = s.card := by
    exact Finset.card_sdiff_add_card_eq_card hU
  have hnat : (∑ W ∈ Ω, W.card) + (s \ Ω.biUnion id).card = s.card := by
    rw [← hcardU]
    exact Nat.add_comm _ _ ▸ hnatS
  exact_mod_cast hnat

/-- Multi-window version of `window_split_bound_is_trivial`: a disjoint finite partition of the
summands into any number of coarse windows plus the complement still yields only `|s|` under the
unit-modulus triangle inequality.  Thus a door-(iv) certificate based solely on finitely many
occupancy counts remains trivial unless it proves cancellation within or between pieces. -/
theorem multi_window_split_bound_is_trivial [DecidableEq ι]
    {f : ι → ℂ} {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id) (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤
      (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) := by
  rw [multi_window_split_rhs_constant hsub hdis]
  exact norm_sum_le_card_of_phase hf

/-- Sharper statement of "the window count is irrelevant": the right-hand side of the window split
equals `|s|` for *every* admissible window `W`, so it carries no information about the concentration
`|W|`. This is the formal content of the probe's `C/√n → 0` + Spearman→0 degeneracy: a single window
count is energy-blind. -/
theorem window_split_rhs_constant [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) :
    (W.card : ℝ) + ((s \ W).card : ℝ) = (s.card : ℝ) := by
  have hnat : W.card + (s \ W).card = s.card := by
    rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hW
  exact_mod_cast hnat

/-- Strict-budget obstruction for single-window certificates: since the split right-hand side is
identically `|s|`, no admissible window can make the triangle certificate fit under any strict budget
`B < |s|`.  Thus a claimed single-window small-ball improvement must use information beyond the
occupancy split itself. -/
theorem no_window_split_rhs_le_strict_budget [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) {B : ℝ} (hB : B < (s.card : ℝ)) :
    ¬ (W.card : ℝ) + ((s \ W).card : ℝ) ≤ B := by
  intro hle
  have hconst := window_split_rhs_constant (s := s) (W := W) hW
  linarith

/-- Strict-budget obstruction for two-window certificates: even two disjoint coarse arcs plus the
outside complement have split right-hand side exactly `|s|`, so they cannot fit under any budget
strictly below `|s|` without extra phase-cancellation information. -/
theorem no_two_window_split_rhs_le_strict_budget [DecidableEq ι]
    {s W₁ W₂ : Finset ι} (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂)
    {B : ℝ} (hB : B < (s.card : ℝ)) :
    ¬ (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) ≤ B := by
  intro hle
  have hconst := two_window_split_rhs_constant (s := s) (W₁ := W₁) (W₂ := W₂) h₁ h₂ hdis
  linarith

/-- Budget-forcing form for single-window certificates: if the purely occupancy-based in/out split
fits under some budget `B`, then the total number of summands already satisfies `|s| ≤ B`.  This is
the probe-facing contrapositive of the strict-budget obstruction: a small-ball window cannot certify
any sublinear door-(iv) estimate unless it uses genuine phase cancellation beyond occupancy counts. -/
theorem window_budget_forces_card_le [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) {B : ℝ}
    (hbudget : (W.card : ℝ) + ((s \ W).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B := by
  have hconst := window_split_rhs_constant (s := s) (W := W) hW
  linarith

/-- Budget-forcing form for two-window certificates: if two disjoint coarse windows plus the outside
complement fit under a budget `B`, then `|s| ≤ B` already.  Thus two-window occupancy bookkeeping
cannot be the missing anti-concentration input for door-(iv); any improvement below the linear budget
must prove cancellation inside or between the pieces. -/
theorem two_window_budget_forces_card_le [DecidableEq ι]
    {s W₁ W₂ : Finset ι} (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂)
    {B : ℝ}
    (hbudget : (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B := by
  have hconst := two_window_split_rhs_constant (s := s) (W₁ := W₁) (W₂ := W₂) h₁ h₂ hdis
  linarith

/-- Budget-forcing form for finite multi-window certificates: if the purely occupancy-based split
fits under some budget `B`, then the total number of summands already satisfies `|s| ≤ B`.  Thus
any such certificate below the linear budget would contradict the exact split identity; occupancy
bookkeeping alone cannot be the missing door-(iv) anti-concentration input. -/
theorem multi_window_budget_forces_card_le [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s) (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ}
    (hbudget : (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B := by
  have hconst := multi_window_split_rhs_constant (s := s) (Ω := Ω) hsub hdis
  linarith

/-- Strict-budget obstruction for finite multi-window certificates: any disjoint finite family of
occupancy windows plus the outside complement still has right-hand side exactly `|s|`.  Therefore
no purely occupancy-based multi-window small-ball certificate can beat the trivial linear ceiling;
a strict improvement must prove cancellation within or between pieces. -/
theorem no_multi_window_split_rhs_le_strict_budget [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s) (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ} (hB : B < (s.card : ℝ)) :
    ¬ (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B := by
  intro hle
  have hconst := multi_window_split_rhs_constant (s := s) (Ω := Ω) hsub hdis
  linarith

end ProximityGap.Frontier.DoorIVWindowConcentrationTrivial

#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.norm_sum_le_card_of_phase
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_split_bound_is_trivial
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_split_rhs_constant
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.no_window_split_rhs_le_strict_budget
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.no_two_window_split_rhs_le_strict_budget
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_budget_forces_card_le
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.two_window_budget_forces_card_le
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.multi_window_budget_forces_card_le
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.no_multi_window_split_rhs_le_strict_budget
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.two_window_split_rhs_constant
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.two_window_split_bound_is_trivial
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.multi_window_split_rhs_constant
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.multi_window_split_bound_is_trivial
