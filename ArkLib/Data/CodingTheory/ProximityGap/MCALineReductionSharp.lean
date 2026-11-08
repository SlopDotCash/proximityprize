/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
structured and accidental stacks.

**The support hypothesis `hR` is essential (audit finding PG-147).** Both theorems require
`hR : ⌊δ·n⌋ < |supp u₁|`. The factor `M = |supp u₁| / (|supp u₁| − ⌊δ·n⌋)` in `NaccMul` is a
natural-number quotient, and when `hR` fails the denominator is `0`, so `NaccMul = 0`
(`NaccMul_eq_zero_of_support_le`) even though `Pr[mcaEvent]` can be positive. Example (checked by
exact enumeration in the audit, not kernel-checked here): the length-4 constant code over `F₁₇` on
its proper `μ₄` domain, `δ = 1/4`, `u₀ = u₁ = (1,0,0,0)`: at `γ = −1` the line is `0`, explained on
the full domain while `u₀` has no constant explanation, and this is the only bad scalar, so
`Pr[mcaEvent] = 1/17`; yet `|supp u₁| = ⌊δ·n⌋ = 1`, so `NaccMul = 0`. Hence the **unrestricted**
reduction `ε_mca(C, δ) ≤ ⨆_u N_accidental(u)·M(u)/q` does **not** follow from these theorems: the
supremum may only range over stacks satisfying `hR`, and low-support directions
(`|supp u₁| ≤ ⌊δ·n⌋`) must be handled separately. Moreover, a uniform bound
`⨆_{u : hR} N_accidental(u)·M(u) ≤ poly(n)` is a *sufficient* (union-bound) certificate for the
corresponding part of the MCA conjecture, not an equivalent characterization of it. The
accidental line list-decoding count is the BCIKS20 / GG25 object (Johnson up to `1 − √ρ`,
capacity `1 − ρ` open).

## Main results

* `witnessesAt` — `w` witnesses a bad MCA event at `γ`.
* `dist_le_of_agree_on` / `witnessesAt_imp_close` — a witness is `δ`-close to the line.
* `card_mcaEvent_le_Nacc` — `#{γ : mcaEvent} ≤ N_accidental · M`.
* `mcaEvent_pr_le_Nacc` — `Pr_{γ}[mcaEvent] ≤ N_accidental · M / q` (under `hR`).
* `NaccMul_eq_zero_of_support_le` — without `hR`, `NaccMul` degenerates to `0`.
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
joint-structured stack this is `0` (no codeword witnesses a bad event).  The factor `M` is a
natural-number quotient by `|supp u₁| − ⌊δ·n⌋`; it is meaningful only when
`⌊δ·n⌋ < |supp u₁|`, and is `0` otherwise (`NaccMul_eq_zero_of_support_le`). -/
noncomputable def NaccMul (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) : ℕ :=
  (C.filter (fun w => (univ.filter (fun γ : F =>
      witnessesAt (↑C) δ u₀ u₁ w γ)).card ≠ 0)).card
    * ((univ.filter (fun i => u₁ i ≠ 0)).card
        / ((univ.filter (fun i => u₁ i ≠ 0)).card - ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊))

open Classical in
/-- **`NaccMul` degenerates without the support hypothesis.**  If `|supp u₁| ≤ ⌊δ·n⌋` (i.e. the
hypothesis `hR` of `card_mcaEvent_le_Nacc` fails), the natural-number denominator of the
line-ball factor is `0`, so `NaccMul C δ u₀ u₁ = 0` regardless of how many scalars are bad.
Hence no bound on `ε_mca` can be read off `NaccMul` for such low-support directions. -/
theorem NaccMul_eq_zero_of_support_le (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (h : (univ.filter (fun i => u₁ i ≠ 0)).card ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊) :
    NaccMul C δ u₀ u₁ = 0 := by
  unfold NaccMul
  rw [Nat.sub_eq_zero_of_le h, Nat.div_zero, Nat.mul_zero]

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
Non-vacuous on both structured (`N_accidental = 0`) and accidental stacks.  The hypothesis `hR`
cannot be dropped (`NaccMul_eq_zero_of_support_le`; see the module docstring for a stack with
`Pr = 1/17` but `NaccMul = 0`), so taking `⨆` bounds only the part of `ε_mca(C, δ)` coming from
stacks with `⌊δ·n⌋ < |supp u₁|`; low-support directions need a separate argument, and a uniform
bound on `N_accidental·M` is a sufficient certificate, not an equivalent form of the conjecture. -/
theorem mcaEvent_pr_le_Nacc (C : Finset (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → F)
    (hR : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (↑C) δ u₀ u₁ γ]
      ≤ (NaccMul C δ u₀ u₁ : ENNReal) / (Fintype.card F : ENNReal) :=
  mcaEvent_pr_le C δ u₀ u₁ _ (card_mcaEvent_le_Nacc C δ hδ u₀ u₁ hR)

end ProximityGap
