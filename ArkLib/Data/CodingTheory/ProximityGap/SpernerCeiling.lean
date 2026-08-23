/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainEngine
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# The Sperner ceiling: a radius-free upper bound for every linear code (#357, item 26)

Item 26 of the 26-thread review: the general-δ extension of the antichain/LYM engine,
registered in the antichain round ("the general-δ LYM extension … would subsume …")
and never executed.  The LYM ceiling `C(n,t)/q` requires `t ≥ n/2` (`δ ≤ 1/2`).  This
file removes the restriction with Sperner's theorem:

* `badScalar_card_le_sperner` — for **every** linear code, **every** radius `δ`, and
  every stack, the bad-scalar count is at most the middle binomial
  `C(n, ⌊n/2⌋)`: chosen witnesses of distinct bad scalars form an antichain
  (`bad_scalar_eq_of_witness_subset`, the nesting collapse), and Sperner bounds every
  antichain by the middle layer.
* `epsMCA_le_sperner_div` — hence `ε_mca(C, δ) ≤ C(n, ⌊n/2⌋)/|F|`, radius-free.

This is the first ceiling valid at ALL radii — in particular above `δ = 1/2`, where
the LYM engine is silent.  At production scale it is vacuous (`C(n, n/2) ≫ q`), but
it completes the structural picture: the witness-antichain mechanism caps badness at
the Sperner number *no matter the radius*, so every super-Sperner phenomenon must
come from the field, never the combinatorics.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.AntichainEngine

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The Sperner bad-scalar bound.**  Every stack of every linear code, at every
radius, has at most `C(n, ⌊n/2⌋)` bad scalars: witnesses of distinct bad scalars
cannot nest, so chosen witnesses form an antichain. -/
theorem badScalar_card_le_sperner (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ (Fintype.card ι).choose (Fintype.card ι / 2) := by
  set G := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) with hG
  -- choose a witness per bad scalar
  have hch : ∀ γ ∈ G, ∃ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        (∃ w ∈ (C : Set (ι → A)), ∀ i ∈ S, w i = u₀ i + γ • u₁ i)) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
    intro γ hγ
    obtain ⟨S, hsz, hline, hno⟩ := (Finset.mem_filter.mp hγ).2
    exact ⟨S, ⟨hsz, hline⟩, hno⟩
  choose! S hS hno using hch
  -- the nesting collapse: distinct bad scalars have non-nesting witnesses
  have hnest : ∀ γ ∈ G, ∀ γ' ∈ G, S γ ⊆ S γ' → γ = γ' := by
    intro γ hγ γ' hγ' hsub
    exact ProximityGap.MCAAntichainEngine.bad_scalar_eq_of_witness_subset C hsub (hS γ hγ).2 (hno γ hγ)
      (hS γ' hγ').2
  -- injectivity of the witness choice
  have hinj : Set.InjOn S ↑G := by
    intro γ hγ γ' hγ' hSS
    exact hnest γ (Finset.mem_coe.mp hγ) γ' (Finset.mem_coe.mp hγ')
      (le_of_eq hSS)
  -- the image is an antichain
  have hanti : IsAntichain (· ⊆ ·) ((G.image S : Finset (Finset ι)) :
      Set (Finset ι)) := by
    intro a ha b hb hab hsub
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    exact hab (congrArg S (hnest γ hγ γ' hγ' hsub))
  calc G.card = (G.image S).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Fintype.card ι).choose (Fintype.card ι / 2) := hanti.sperner

open Classical in
/-- **The Sperner ceiling** — radius-free: `ε_mca(C, δ) ≤ C(n, ⌊n/2⌋)/|F|` for every
linear code at every radius (the first ceiling valid above `δ = 1/2`). -/
theorem epsMCA_le_sperner_div (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι).choose (Fintype.card ι / 2) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast badScalar_card_le_sperner C δ (u 0) (u 1)

end ProximityGap.AntichainEngine

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.AntichainEngine.badScalar_card_le_sperner
#print axioms ProximityGap.AntichainEngine.epsMCA_le_sperner_div
