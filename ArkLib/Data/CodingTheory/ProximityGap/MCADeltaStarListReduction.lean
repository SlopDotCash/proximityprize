/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadScalarSingleWord
import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Two one-way links between list sizes and `δ*` (#389)

This file proves two **separate, one-directional** statements relating Reed–Solomon list
sizes and bad-scalar counts to the MCA threshold `mcaDeltaStar`.  It does **not** prove an
equivalence between `δ*` and a list-size bound.

* `mcaBad_card_le_singleWordList` — a **specialized link**: for the single direction
  `u₁ = xᵏ` only (on a domain avoiding `0`, with `k < n` and `a ≤ (1-δ)·n`),
  `mcaBad ⊆ {δ-close scalars}`, so its size is at most the single-word list count
  `#{Q ∈ rsCode dom (k+1) : agree(Q,u₀) ≥ a} · ⌊n/a⌋`.  Other directions `u₁` are not
  covered.
* `mcaDeltaStar_ge_of_uniform_mcaBad` — a **general assembly**: a bad-scalar bound `B` assumed
  *uniformly over all stacks* `(u 0, u 1)` with `B/|F| ≤ ε*` forces `δ ≤ mcaDeltaStar`.

The first theorem does not discharge the second theorem's uniform hypothesis: that would need
an all-direction normalization (reducing an arbitrary `u₁` to the `xᵏ` case, or bounding it
directly), which is not proved here.  Neither theorem gives the converse (an MCA or `δ*` bound
implying a list-size bound).  So "pinning `δ*` is exactly bounding one list" is **not** a
theorem of this file; the two statements are only sufficient-direction ingredients.
Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap ProximityGap.SpikeFloor ProximityGap.MCAThresholdLedger Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The specialized link: `mcaBad ⊆ δ-close scalars`, hence bounded by the single-word list.**
Only for the direction `u₁ = xᵏ` on a zero-avoiding domain; it bounds the bad scalars of that one
stack shape and does not by itself give the uniform all-stack bound used by
`mcaDeltaStar_ge_of_uniform_mcaBad`. -/
theorem mcaBad_card_le_singleWordList (dom : Fin n ↪ F) {k a : ℕ} (ha : 1 ≤ a)
    (hk : k < n) (hdom : ∀ i, dom i ≠ 0) {δ : ℝ≥0} (u₀ : Fin n → F)
    (haδ : (a : ℝ≥0) ≤ (1 - δ) * Fintype.card (Fin n)) :
    (mcaBad (F := F) (↑(rsCode dom k) : Set (Fin n → F)) δ u₀
        (fun i => (dom i) ^ k)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun Q => Q ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F))
            ∧ a ≤ (agreeSet Q u₀).card)).card * (n / a) := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (badScalar_card_le_codeword_list_mul dom k a ha hk u₀ hdom)
  intro γ hγ
  rw [mcaBad, Finset.mem_filter] at hγ
  obtain ⟨S, hScard, ⟨w, hw, hwS⟩, -⟩ := hγ.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, ?_⟩
  have hSsub : S ⊆ agreeSet w (fun i => u₀ i + γ • (dom i) ^ k) := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwS i hi⟩
  have ha_le_S : a ≤ S.card := by
    have h : (a : ℝ≥0) ≤ (S.card : ℝ≥0) := le_trans haδ hScard
    exact_mod_cast h
  exact le_trans ha_le_S (Finset.card_le_card hSsub)

open Classical in
/-- **The assembly: a uniform bad-scalar bound pushes `δ*` up.** The bound `hcard` is an
independent hypothesis over *all* stacks; it is not derived from
`mcaBad_card_le_singleWordList`, which covers only the direction `xᵏ`. -/
theorem mcaDeltaStar_ge_of_uniform_mcaBad
    (C : Set (Fin n → F)) {δ : ℝ≥0} (hδ : δ ≤ 1) {εstar : ℝ≥0∞} {B : ℝ}
    (hcard : ∀ u : WordStack F (Fin 2) (Fin n),
        ((mcaBad (F := F) C δ (u 0) (u 1)).card : ℝ) ≤ B)
    (hε : ENNReal.ofReal (B / Fintype.card F) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F) C εstar :=
  le_mcaDeltaStar_of_good C εstar hδ
    (le_trans (epsMCA_le_ofReal_of_forall_mcaBad_card_le C δ hcard) hε)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mcaBad_card_le_singleWordList
#print axioms ProximityGap.Ownership.mcaDeltaStar_ge_of_uniform_mcaBad
