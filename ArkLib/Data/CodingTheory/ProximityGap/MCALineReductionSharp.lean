/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALineReduction

/-!
# The sharp MCA reduction: `ε_mca ≤ N_accidental · M / q`

`MCALineReduction` bounds `Pr[mcaEvent] ≤ N_line·M/q`, but `N_line` counts *all* nearby codewords
and so is `≥ q` on joint-structured stacks (`(u₀,u₁) ∈ C²`), even though `Pr[mcaEvent] = 0` there.
This file sharpens the reduction to the correct object:

  `N_accidental(C, δ, u₀, u₁) := #{w ∈ C : w *witnesses* a bad MCA event at some γ}`,

i.e. codewords for which some `S` of size `≥ (1−δ)n` carries `w = u₀+γ•u₁` **and** breaks joint
agreement (`¬ pairJointAgreesOn`).  On a joint-structured stack `N_accidental = 0` (the joint pair
agrees with itself, so no codeword witnesses), matching `Pr[mcaEvent] = 0`.

  `Pr_{γ}[mcaEvent C δ u₀ u₁ γ] ≤ N_accidental · M / q`.            (`mcaEvent_pr_le_Nacc`)

This is the *sharp* form of the proximity-gap dichotomy reduction: it is non-vacuous on both
structured and accidental stacks, and `ε_mca(C, δ) ≤ ⨆_u N_accidental(u)·M(u)/q`.  The conjecture is
now exactly `⨆_u N_accidental(u)·M(u) ≤ poly(n)` — the **accidental** line list-decoding count, which
is the genuine BCIKS20 / GG25 object (Johnson up to `1 − √ρ`, capacity `1 − ρ` open).

## Main results

* `witnessesAt` — `w` witnesses a bad MCA event at `γ`.
* `dist_le_of_agree_on` / `witnessesAt_imp_close` — a witness is `δ`-close to the line.
* `card_mcaEvent_le_Nacc` — `#{γ : mcaEvent} ≤ N_accidental · M`.
* `mcaEvent_pr_le_Nacc` — `Pr_{γ}[mcaEvent] ≤ N_accidental · M / q`.
-/

set_option linter.style.longLine false


open scoped BigOperators NNReal ENNReal ProbabilityTheory
open Finset Code

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- If `w = u₀+γ•u₁` on a set `S` of size `≥ (1−δ)n`, then `Δ₀(u₀+γ•u₁, w) ≤ ⌊δ·n⌋`. -/
theorem dist_le_of_agree_on (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ w : ι → F) (γ : F) (S : Finset ι)
    (hScard : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hweq : ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    hammingDist (u₀ + γ • u₁) w ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  classical
  have hsub : univ.filter (fun i => (u₀ + γ • u₁) i ≠ w i) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_filter] at hi; rw [Finset.mem_compl]
    exact fun hiS => hi.2 (hweq i hiS).symm
  have hdist : hammingDist (u₀ + γ • u₁) w ≤ Fintype.card ι - S.card := by
    change (univ.filter (fun i => (u₀ + γ • u₁) i ≠ w i)).card ≤ Fintype.card ι - S.card
    rw [← Finset.card_compl]; exact Finset.card_le_card hsub
  have hsum1 : (1 - δ) + δ = 1 := tsub_add_cancel_of_le hδ
  have hn_le : (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) + δ * (Fintype.card ι : ℝ≥0) :=
    calc (Fintype.card ι : ℝ≥0)
        = ((1 - δ) + δ) * (Fintype.card ι : ℝ≥0) := by rw [hsum1, one_mul]
      _ = (1 - δ) * (Fintype.card ι : ℝ≥0) + δ * (Fintype.card ι : ℝ≥0) := by rw [add_mul]
      _ ≤ (S.card : ℝ≥0) + δ * (Fintype.card ι : ℝ≥0) := by gcongr
  have hSle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  rw [Nat.le_floor_iff (by positivity)]
  have hnr : (Fintype.card ι : ℝ) ≤ (S.card : ℝ) + (δ : ℝ) * (Fintype.card ι : ℝ) := by
    have := hn_le; push_cast at this ⊢; exact_mod_cast this
  have hkey : ((Fintype.card ι - S.card : ℕ) : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by
    rw [Nat.cast_sub hSle]; linarith
  exact le_trans (by exact_mod_cast Nat.cast_le.mpr hdist) hkey

/-- `w` witnesses the bad MCA event at `γ`: some large `S` carries `w = u₀+γ•u₁` and breaks joint
agreement. `mcaEvent ↔ ∃ w ∈ C, witnessesAt w`. -/
def witnessesAt (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧ ¬ pairJointAgreesOn C S u₀ u₁

theorem mcaEvent_iff_exists_witnessesAt (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F) :
    mcaEvent C δ u₀ u₁ γ ↔ ∃ w ∈ C, witnessesAt C δ u₀ u₁ w γ := by
  constructor
  · rintro ⟨S, hS, ⟨w, hwC, hweq⟩, hno⟩; exact ⟨w, hwC, S, hS, hweq, hno⟩
  · rintro ⟨w, hwC, S, hS, hweq, hno⟩; exact ⟨S, hS, ⟨w, hwC, hweq⟩, hno⟩

theorem witnessesAt_imp_close (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ w : ι → F) (γ : F)
    (h : witnessesAt C δ u₀ u₁ w γ) :
    hammingDist (u₀ + γ • u₁) w ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  obtain ⟨S, hS, hweq, _⟩ := h
  exact dist_le_of_agree_on δ hδ u₀ u₁ w γ S hS hweq

open Classical in
/-- `N_accidental · M`: the count of *witness* codewords times the line-ball factor.  On a
joint-structured stack this is `0` (no codeword witnesses a bad event). -/
noncomputable def NaccMul (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) : ℕ :=
  (C.filter (fun w => (univ.filter (fun γ : F =>
      witnessesAt (↑C) δ u₀ u₁ w γ)).card ≠ 0)).card
    * ((univ.filter (fun i => u₁ i ≠ 0)).card
        / ((univ.filter (fun i => u₁ i ≠ 0)).card - ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊))

set_option maxHeartbeats 2000000 in
-- The nested `Finset.filter`/`biUnion` over `witnessesAt` (an existential `Prop`) elaborates
-- through several `Classical.dec` instances, so the default heartbeat budget is raised.
open Classical in
/-- **Sharp reduction count.** `#{γ : mcaEvent} ≤ N_accidental · M`.  Unlike `N_line`, `N_accidental`
counts only codewords that witness a bad event, so it is `0` on joint-structured stacks. -/
theorem card_mcaEvent_le_Nacc (C : Finset (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → F)
    (hR : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    (univ.filter (fun γ : F => mcaEvent (↑C) δ u₀ u₁ γ)).card ≤ NaccMul C δ u₀ u₁ := by
  classical
  set R := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊
  have hgM : ∀ w, (univ.filter (fun γ : F => witnessesAt (↑C) δ u₀ u₁ w γ)).card
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card / ((univ.filter (fun i => u₁ i ≠ 0)).card - R) := by
    intro w
    refine le_trans (Finset.card_le_card ?_) (card_close_gamma_le_div u₀ u₁ w R hR)
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    exact ⟨mem_univ _, witnessesAt_imp_close (↑C) δ hδ u₀ u₁ w γ hγ.2⟩
  calc (univ.filter (fun γ : F => mcaEvent (↑C) δ u₀ u₁ γ)).card
      ≤ (C.biUnion (fun w => univ.filter (fun γ : F => witnessesAt (↑C) δ u₀ u₁ w γ))).card := by
        refine Finset.card_le_card (fun γ hγ => ?_)
        rw [Finset.mem_filter] at hγ
        obtain ⟨w, hwC, hwit⟩ := (mcaEvent_iff_exists_witnessesAt (↑C) δ u₀ u₁ γ).mp hγ.2
        rw [Finset.mem_biUnion]
        exact ⟨w, Finset.mem_coe.mp hwC, Finset.mem_filter.mpr ⟨mem_univ _, hwit⟩⟩
    _ ≤ ∑ w ∈ C, (univ.filter (fun γ : F => witnessesAt (↑C) δ u₀ u₁ w γ)).card :=
        Finset.card_biUnion_le
    _ ≤ NaccMul C δ u₀ u₁ :=
        sum_le_card_support_mul C
          (fun w => (univ.filter (fun γ : F => witnessesAt (↑C) δ u₀ u₁ w γ)).card) _
          (fun w _ => hgM w)

open Classical in
/-- **Sharp per-stack MCA reduction.**  `Pr_{γ}[mcaEvent C δ u₀ u₁ γ] ≤ N_accidental · M / q`.
Non-vacuous on both structured (`N_accidental = 0`) and accidental stacks.  Taking `⨆` over stacks
bounds `ε_mca(C, δ)`; the conjecture is exactly `⨆_u N_accidental(u)·M(u) ≤ poly(n)`. -/
theorem mcaEvent_pr_le_Nacc (C : Finset (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → F)
    (hR : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (↑C) δ u₀ u₁ γ]
      ≤ (NaccMul C δ u₀ u₁ : ENNReal) / (Fintype.card F : ENNReal) :=
  mcaEvent_pr_le C δ u₀ u₁ _ (card_mcaEvent_le_Nacc C δ hδ u₀ u₁ hR)

end ProximityGap
