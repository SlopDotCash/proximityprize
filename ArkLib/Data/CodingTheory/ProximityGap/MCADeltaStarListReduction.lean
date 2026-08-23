/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadScalarSingleWord
import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The δ* ⟺ list-size reduction, assembled (#389)

Every face of the δ* problem (MCA error, line–ball incidence, bad scalars) collapses to
the **sub-Johnson list size** of explicit Reed–Solomon.  This file makes that a theorem.

* `mcaBad_card_le_singleWordList` — the **link**: for the canonical MCA direction `u₁ = xᵏ`
  (domain avoiding `0`), `mcaBad ⊆ {δ-close scalars}`, so its size is at most the
  single-word list `#{Q ∈ rsCode dom (k+1) : agree(Q,u₀) ≥ a} · ⌊n/a⌋`.
* `mcaDeltaStar_ge_of_uniform_mcaBad` — the **assembly**: a uniform per-stack bad-scalar
  bound `B` with `B/|F| ≤ ε*` forces `δ ≤ mcaDeltaStar`.

Pinning δ* is exactly bounding that one list — the open core.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap ProximityGap.SpikeFloor ProximityGap.MCAThresholdLedger Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The link: `mcaBad ⊆ δ-close scalars`, hence bounded by the single-word list.** -/
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
/-- **The assembly: a uniform bad-scalar bound pushes `δ*` up.** -/
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
