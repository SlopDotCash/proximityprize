/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.Folding

/-!
# Reduction of ABF26 Theorem 4.20 to named per-round events

`Fold.folding_listdecoding_if_genMutualCorrAgreement` (`Whir/Folding.lean`, ABF26
Theorem 4.20) is a statement-only `def : Prop`: the probabilistic list-decoding
equivalence of the `k`-fold fold, with failure probability strictly below the summed
per-round `errStar` budget `∑ i, errStar i`.

This file **discharges that capstone given exactly the per-round event data** that the
single-step lemmas (L4.21–L4.23, proven in `Folding.lean` as implications) are designed
to produce. Concretely, `folding_listdecoding_of_round_events` consumes:

* `Q f i αs` — a family of per-round "bad events" (round `i ∈ [0,k]` fails on folding
  randomness `αs`), one per fold level;
* `h_imp` — the *telescoping* hypothesis: if the end-to-end fold list-set differs from
  the level-`k` Hamming list, some round's bad event fired (this is the deterministic
  k-fold composite of the L4.22 forward inclusions with the L4.23 reverse-failure
  events);
* `h_le` / `h_lt` — the per-round probability bounds: every round's bad event has
  probability `≤ errStar i`, and at least one round is strictly below its budget
  (the strictness the paper's `<` conclusion requires; the MCA hypothesis `params.h i`
  is what delivers these bounds via the L4.21 bridge
  `folding_preserves_listdecoding_base_of_mca_bridge`).

The capstone then follows from the proven union-bound backbone
`Pr_le_finset_sum_of_implies` plus a strict finite-sum comparison in `ℝ≥0∞`
(`sum_lt_sum_of_le_of_lt_of_ne_top` below, using that probabilities are `≤ 1`, hence
finite).

**Honest scope.** This is a *reduction*, not a closure: exhibiting the per-round events
`Q` and discharging `h_imp`/`h_le`/`h_lt` from `params.h` is the remaining ABF26 §4
inductive content (the per-level block-list data `S_i, φ_i, C_i` and the
reverse-inclusion → `proximityCondition` bridge are not derivable from the loose
`indexPowT` data — see the documented statement repairs on L4.21/4.22 in `Folding.lean`).
What this file removes from the open surface is the entire probabilistic accounting
layer: union bound, strictness bookkeeping, and the exact existential/`max`-free shape
of the Theorem 4.20 conclusion.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

namespace Fold

open BlockRelDistance MutualCorrAgreement ListDecodable NNReal ReedSolomon
     ProbabilityTheory Finset

variable {F : Type} [Field F] [DecidableEq F] {ι : Type} [Pow ι ℕ]

/-- **Strict comparison of finite `ℝ≥0∞` sums**: if `a ≤ b` pointwise on `s`, the
inequality is strict at some `i₀ ∈ s`, and every `a i` is finite, then
`∑ i ∈ s, a i < ∑ i ∈ s, b i`. (The finiteness hypothesis is needed: in `ℝ≥0∞`,
`⊤ + a < ⊤ + b` fails.) -/
theorem sum_lt_sum_of_le_of_lt_of_ne_top {β : Type*} [DecidableEq β] {s : Finset β}
    {a b : β → ENNReal}
    (hle : ∀ i ∈ s, a i ≤ b i) {i₀ : β} (hi₀ : i₀ ∈ s) (hlt : a i₀ < b i₀)
    (hfin : ∀ i ∈ s, a i ≠ ⊤) :
    ∑ i ∈ s, a i < ∑ i ∈ s, b i := by
  classical
  have hsplit_a : ∑ i ∈ s, a i = a i₀ + ∑ i ∈ s.erase i₀, a i :=
    (Finset.add_sum_erase s a hi₀).symm
  have hsplit_b : ∑ i ∈ s, b i = b i₀ + ∑ i ∈ s.erase i₀, b i :=
    (Finset.add_sum_erase s b hi₀).symm
  have hrest_le : ∑ i ∈ s.erase i₀, a i ≤ ∑ i ∈ s.erase i₀, b i :=
    Finset.sum_le_sum fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have hrest_ne : ∑ i ∈ s.erase i₀, a i ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    exact fun i hi => hfin i (Finset.mem_of_mem_erase hi)
  calc ∑ i ∈ s, a i = a i₀ + ∑ i ∈ s.erase i₀, a i := hsplit_a
    _ < b i₀ + ∑ i ∈ s.erase i₀, a i := ENNReal.add_lt_add_right hrest_ne hlt
    _ ≤ b i₀ + ∑ i ∈ s.erase i₀, b i := add_le_add le_rfl hrest_le
    _ = ∑ i ∈ s, b i := hsplit_b.symm

omit [Pow ι ℕ] in
/-- **ABF26 Theorem 4.20, discharged from per-round event data.**

Given per-round bad events `Q f i αs` with (i) the telescoping implication — end-to-end
list mismatch forces some round's event — and (ii) per-round probability bounds
`Pr[Q f i] ≤ errStar i` with strictness at some round, the Theorem 4.20 capstone
`folding_listdecoding_if_genMutualCorrAgreement` HOLDS.

The proof is the union bound `Pr_le_finset_sum_of_implies` (proven in `Folding.lean`)
followed by the strict finite-sum comparison (probabilities are `≤ 1`, hence finite).
The open ABF26 §4 content lives entirely in the three named hypotheses; see the module
docstring. -/
theorem folding_listdecoding_of_round_events
    [Fintype F] {S : Finset ι} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ] {k m : ℕ}
    {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
    [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
    [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
    [∀ i : ℕ, Neg (indexPowT S φ i)]
    {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ' m) (hLe : k ≤ m)
    {δ : ℝ≥0}
    {params : GenMutualCorrParams S φ k}
    (Q : ((indexPowT S φ 0) → F) → Fin (k + 1) → (Fin k → F) → Prop)
    -- telescoping: an end-to-end list mismatch forces some round's bad event
    (h_imp :
      let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
      let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
      ∀ (f : (indexPowT S φ 0) → F),
      (0 < δ ∧ δ < 1 - Finset.univ.sup
        (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)) →
      ∀ αs : Fin k → F,
        fold_k_set (Λᵣ(0, k, f, S', C, hcode, δ)) αs hLe
          ≠ closeCodewordsRel ((params.Gen_α ⟨k, Nat.lt_succ_self k⟩).C)
              (fold_k f αs hLe) δ →
        ∃ i : Fin (k + 1), Q f i αs)
    -- per-round budget: every round's bad event is within its `errStar` budget
    (h_le :
      let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
      let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
      ∀ (f : (indexPowT S φ 0) → F),
      (0 < δ ∧ δ < 1 - Finset.univ.sup
        (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)) →
      ∀ i : Fin (k + 1),
        Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs]
          ≤ params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ)
    -- strictness: at least one round is strictly below its budget
    (h_lt :
      let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
      let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
      ∀ (f : (indexPowT S φ 0) → F),
      (0 < δ ∧ δ < 1 - Finset.univ.sup
        (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)) →
      ∃ i : Fin (k + 1),
        Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs]
          < params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ) :
    folding_listdecoding_if_genMutualCorrAgreement (S' := S') (φ' := φ')
      hcode hLe (δ := δ) (params := params) := by
  unfold folding_listdecoding_if_genMutualCorrAgreement
  intro _inst1 _inst2 f hδ
  classical
  -- union bound over the `k + 1` rounds (`Pr_le_finset_sum_of_implies`, proven)
  have hUnion :
      Pr_{let αs ←$ᵖ (Fin k → F)}[
        fold_k_set (Λᵣ(0, k, f, S', C, hcode, δ)) αs hLe
          ≠ closeCodewordsRel ((params.Gen_α ⟨k, Nat.lt_succ_self k⟩).C)
              (fold_k f αs hLe) δ ]
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))),
          Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs] := by
    refine Pr_le_finset_sum_of_implies ($ᵖ (Fin k → F)) _ (Q f) Finset.univ ?_
    intro αs hP
    obtain ⟨i, hi⟩ := h_imp f hδ αs hP
    exact ⟨i, Finset.mem_univ i, hi⟩
  -- strict comparison of the per-round sums (probabilities are finite)
  obtain ⟨i₀, hi₀lt⟩ := h_lt f hδ
  have hfin : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
      Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs] ≠ ⊤ := fun i _ =>
    (lt_of_le_of_lt (ProximityGap.Pr_le_one _ _) ENNReal.one_lt_top).ne
  have hSum :
      ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))),
          Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs]
        < ∑ i : Fin (k + 1),
            params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ :=
    sum_lt_sum_of_le_of_lt_of_ne_top (fun i _ => h_le f hδ i)
      (Finset.mem_univ i₀) hi₀lt hfin
  exact lt_of_le_of_lt hUnion hSum

omit [Pow ι ℕ] in
/-- All-strict corollary: if **every** round's bad event is strictly below its budget,
the Theorem 4.20 capstone holds (specializes `folding_listdecoding_of_round_events`;
the witness round for strictness is round `0`). -/
theorem folding_listdecoding_of_round_events_strict
    [Fintype F] {S : Finset ι} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ] {k m : ℕ}
    {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
    [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
    [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
    [∀ i : ℕ, Neg (indexPowT S φ i)]
    {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ' m) (hLe : k ≤ m)
    {δ : ℝ≥0}
    {params : GenMutualCorrParams S φ k}
    (Q : ((indexPowT S φ 0) → F) → Fin (k + 1) → (Fin k → F) → Prop)
    (h_imp :
      let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
      let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
      ∀ (f : (indexPowT S φ 0) → F),
      (0 < δ ∧ δ < 1 - Finset.univ.sup
        (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)) →
      ∀ αs : Fin k → F,
        fold_k_set (Λᵣ(0, k, f, S', C, hcode, δ)) αs hLe
          ≠ closeCodewordsRel ((params.Gen_α ⟨k, Nat.lt_succ_self k⟩).C)
              (fold_k f αs hLe) δ →
        ∃ i : Fin (k + 1), Q f i αs)
    (h_lt :
      let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
      let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2
      ∀ (f : (indexPowT S φ 0) → F),
      (0 < δ ∧ δ < 1 - Finset.univ.sup
        (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)) →
      ∀ i : Fin (k + 1),
        Pr_{let αs ←$ᵖ (Fin k → F)}[Q f i αs]
          < params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ) :
    folding_listdecoding_if_genMutualCorrAgreement (S' := S') (φ' := φ')
      hcode hLe (δ := δ) (params := params) :=
  folding_listdecoding_of_round_events hcode hLe Q h_imp
    (fun f hδ i => (h_lt f hδ i).le)
    (fun f hδ => ⟨0, h_lt f hδ 0⟩)

end Fold

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Fold.sum_lt_sum_of_le_of_lt_of_ne_top
#print axioms Fold.folding_listdecoding_of_round_events
#print axioms Fold.folding_listdecoding_of_round_events_strict
