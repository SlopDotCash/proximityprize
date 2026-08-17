/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.LineBallIntersection
import ArkLib.Data.Probability.Instances

/-!
# Reducing the MCA grand-challenge conjecture to the line list-decoding count `N_line`

This file carries out, end-to-end and machine-checked, the reduction of the ABF26 §4.5 MCA
conjecture (`ProximityGap.mcaConjecture`) to a single list-decoding count.  Writing `R = ⌊δ·n⌋`,
`q = |F|`, `M = |supp u₁|/(|supp u₁| − R)`, and

  `N_line(C, u₀, u₁) := #{w ∈ C : the line γ ↦ u₀+γ•u₁ is δ-close to w for some γ}`,

we prove, for every word-stack `u = (u₀, u₁)` with a **non-degenerate** second row (`R < |supp u₁|`):

  `Pr_{γ}[mcaEvent C δ u₀ u₁ γ] ≤ (N_line · M) / q`.        (`mcaEvent_pr_le_Nline`)

Hence `ε_mca(C, δ) = ⨆_u Pr_{γ}[mcaEvent] ≤ ⨆_u (N_line(u)·M(u))/q`.  Since `M = O(1/ρ)` below
capacity, **the conjecture reduces to** the uniform list-decoding bound `N_line ≤ poly(n)`.

## The chain

1. `exists_close_of_mcaEvent` — the bad event forces *some* codeword `δ`-close to the line.
2. `card_close_gamma_le` (`LineBallIntersection`) — a *fixed* codeword is close to the line for few
   `γ` (the `1/q` mechanism).
3. `sum_close_le_Nline_mul` / `card_exists_close_le` — union bound over codewords ⟹ `#{bad γ} ≤
   N_line·M`.
4. `mcaEvent_pr_le_Nline` — divide by `q` (uniform `Pr = count/q`).

## What remains (precise)

The reduction `Pr[mcaEvent] ≤ N_line·M/q` is a *valid* upper bound, but on its own it does **not**
close the conjecture, because `N_line` (counting *all* nearby codewords) is **not** uniformly
`poly(n)`:

* **Joint-structured stacks.** If `(u₀,u₁) = (v₀,v₁) ∈ C²` (a genuine joint pair), every line point
  `v₀+γ•v₁` is itself a codeword, so `N_line ≥ q`.  But for such stacks `Pr[mcaEvent] = 0` exactly,
  since `pairJointAgreesOn` holds on *every* `S` (so `¬pairJointAgreesOn` fails).  The bound here drops
  the `¬pairJointAgreesOn` clause of `mcaEvent`, hence is *vacuous* (`0 ≤ M`) on structured stacks.

Therefore the proof splits (the proximity-gap dichotomy):
* **Accidental stacks** (no joint structure): the reduction is sharp; `N_line ≤ poly(n)` is the real
  content — Johnson gives it up to `1 − √ρ` (bivariate / Polishchuk–Spielman, `#232`), capacity
  `1 − ρ` is open.
* **Structured stacks**: `Pr[mcaEvent]` is small for the *complementary* reason (`¬pairJointAgreesOn`
  fails for most `γ`); this is what the dropped clause must recover.

The **degenerate** case `|supp u₁| ≤ R` (second row `δ`-close to `0`) is also not covered by the
line-ball lemma and is part of the structured analysis.
-/

set_option linter.style.longLine false


open scoped BigOperators NNReal ENNReal ProbabilityTheory
open Finset Code

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

section Combinatorial

variable {α : Type*} [DecidableEq α]

/-- A sum of `g` over `C`, where each `g a ≤ M`, is at most `(#support of g in C)·M`. -/
theorem sum_le_card_support_mul (C : Finset α) (g : α → ℕ) (M : ℕ) (hg : ∀ a ∈ C, g a ≤ M) :
    ∑ a ∈ C, g a ≤ (C.filter (fun a => g a ≠ 0)).card * M := by
  classical
  rw [show ∑ a ∈ C, g a = ∑ a ∈ C.filter (fun a => g a ≠ 0), g a from
    (Finset.sum_filter_ne_zero C).symm]
  calc ∑ a ∈ C.filter (fun a => g a ≠ 0), g a
      ≤ ∑ _a ∈ C.filter (fun a => g a ≠ 0), M :=
        Finset.sum_le_sum (fun a ha => hg a (Finset.mem_of_mem_filter a ha))
    _ = (C.filter (fun a => g a ≠ 0)).card * M := by rw [Finset.sum_const, smul_eq_mul]

end Combinatorial

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `N_line · M` written out: the list-decoding count along the line times the line-ball factor. -/
noncomputable def NlineMul (C : Finset (ι → F)) (u₀ u₁ : ι → F) (R : ℕ) : ℕ :=
  (C.filter (fun w => (univ.filter (fun γ : F =>
      hammingDist (u₀ + γ • u₁) w ≤ R)).card ≠ 0)).card
    * ((univ.filter (fun i => u₁ i ≠ 0)).card / ((univ.filter (fun i => u₁ i ≠ 0)).card - R))

/-- **Union-bound count.** `#{γ : some w ∈ C is δ-close to the line} ≤ N_line · M`. -/
theorem card_exists_close_le (C : Finset (ι → F)) (u₀ u₁ : ι → F) (R : ℕ)
    (hR : R < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    (univ.filter (fun γ : F => ∃ w ∈ C, hammingDist (u₀ + γ • u₁) w ≤ R)).card
      ≤ NlineMul C u₀ u₁ R := by
  classical
  calc (univ.filter (fun γ : F => ∃ w ∈ C, hammingDist (u₀ + γ • u₁) w ≤ R)).card
      ≤ (C.biUnion (fun w => univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R))).card := by
        refine Finset.card_le_card (fun γ hγ => ?_)
        rw [Finset.mem_filter] at hγ
        obtain ⟨w, hwC, hclose⟩ := hγ.2
        rw [Finset.mem_biUnion]
        exact ⟨w, hwC, Finset.mem_filter.mpr ⟨mem_univ _, hclose⟩⟩
    _ ≤ ∑ w ∈ C, (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card :=
        Finset.card_biUnion_le
    _ ≤ NlineMul C u₀ u₁ R :=
        sum_le_card_support_mul C
          (fun w => (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card) _
          (fun w _ => card_close_gamma_le_div u₀ u₁ w R hR)

/-- **mcaEvent ⟹ some codeword is δ-close to the line.** The witness set `S` (size `≥ (1−δ)n`, where
the line equals a codeword on `S`) forces `Δ₀(u₀+γ•u₁, w) ≤ ⌊δ·n⌋`. -/
theorem exists_close_of_mcaEvent (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (u₀ u₁ : ι → F) (γ : F) (h : mcaEvent C δ u₀ u₁ γ) :
    ∃ w ∈ C, hammingDist (u₀ + γ • u₁) w ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  classical
  obtain ⟨S, hScard, ⟨w, hwC, hweq⟩, _⟩ := h
  refine ⟨w, hwC, ?_⟩
  have hsub : univ.filter (fun i => (u₀ + γ • u₁) i ≠ w i) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_compl]
    exact fun hiS => hi.2 (hweq i hiS).symm
  have hdist : hammingDist (u₀ + γ • u₁) w ≤ Fintype.card ι - S.card := by
    change (univ.filter (fun i => (u₀ + γ • u₁) i ≠ w i)).card ≤ Fintype.card ι - S.card
    rw [← Finset.card_compl]
    exact Finset.card_le_card hsub
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

open Classical in
/-- **Count of bad `γ` ≤ N_line · M.** Combining `exists_close_of_mcaEvent` (bad event ⟹ some
codeword close) with `card_exists_close_le` (union bound + line-ball). -/
theorem card_mcaEvent_le (C : Finset (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → F)
    (hR : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    (Finset.univ.filter (fun γ : F => mcaEvent (↑C) δ u₀ u₁ γ)).card
      ≤ NlineMul C u₀ u₁ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (card_exists_close_le C u₀ u₁ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ hR)
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  refine ⟨mem_univ _, ?_⟩
  obtain ⟨w, hwC, hclose⟩ := exists_close_of_mcaEvent (↑C) δ hδ u₀ u₁ γ hγ.2
  exact ⟨w, Finset.mem_coe.mp hwC, hclose⟩

open Classical in
/-- Per-stack `Pr` bound: `Pr_{γ}[mcaEvent] ≤ B / q` whenever `#{γ : mcaEvent} ≤ B`. -/
theorem mcaEvent_pr_le (C : Finset (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (B : ℕ)
    (hB : (Finset.univ.filter (fun γ : F => mcaEvent (↑C) δ u₀ u₁ γ)).card ≤ B) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (↑C) δ u₀ u₁ γ]
      ≤ (B : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr

open Classical in
/-- **MCA grand-challenge reduction (per non-degenerate stack).**
For a word-stack `(u₀, u₁)` with non-degenerate second row (`⌊δ·n⌋ < |supp u₁|`),

  `Pr_{γ}[mcaEvent C δ u₀ u₁ γ] ≤ (N_line · M) / q`.

Taking `⨆` over stacks bounds `ε_mca(C, δ)`; the conjecture then follows from any uniform
`N_line ≤ poly(n)` (the open list-decoding-up-to-capacity input). -/
theorem mcaEvent_pr_le_Nline (C : Finset (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → F)
    (hR : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (↑C) δ u₀ u₁ γ]
      ≤ (NlineMul C u₀ u₁ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ : ENNReal)
          / (Fintype.card F : ENNReal) :=
  mcaEvent_pr_le C δ u₀ u₁ _ (card_mcaEvent_le C δ hδ u₀ u₁ hR)

/-- **Structured stacks give no bad event.** If both rows are codewords (`u₀, u₁ ∈ C`), then the pair
jointly agrees with itself on *every* `S`, so `¬pairJointAgreesOn` always fails and `mcaEvent` is
impossible — the complementary half of the dichotomy, exact case. -/
theorem not_mcaEvent_of_mem (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F)
    (h₀ : u₀ ∈ C) (h₁ : u₁ ∈ C) : ¬ mcaEvent C δ u₀ u₁ γ := by
  rintro ⟨S, _, _, hno⟩
  exact hno ⟨u₀, h₀, u₁, h₁, fun i _ => ⟨rfl, rfl⟩⟩

open Classical in
/-- Hence `Pr_{γ}[mcaEvent] = 0` for structured stacks: the reduction's vacuity (`0 ≤ M`) on these
stacks is matched by the true probability being `0`. -/
theorem mcaEvent_pr_zero_of_mem (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (h₀ : u₀ ∈ C) (h₁ : u₁ ∈ C) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ u₀ u₁ γ] = 0 := by
  rw [prob_uniform_eq_card_filter_div_card]
  have hempty : (univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun γ _ => not_mcaEvent_of_mem C δ u₀ u₁ γ h₀ h₁
  rw [hempty, Finset.card_empty]
  simp

end ProximityGap
