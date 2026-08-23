/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleSubspaceDesign
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanBoundBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ABF26 C3.5 reduction (deep sub-lemma stack), standalone

We prove the **genuine reduction** that the in-tree `frs_list_decoding_capacity_cz25`
`sorry` claims without proof:

> "this is a COROLLARY of T3.4 via T2.18 … Once T3.4 and T2.18 are proven, C3.5 closes by
>  instantiating T3.4 at the FRS τ(r)=sρ/(s-r+1) and simplifying with 1/η<s."

The two genuinely-external ingredients (the in-tree admits) are taken as **explicit
hypotheses**, with their exact in-tree shapes:

* `hT34` — ABF26 T3.4 [CZ25 B.5] (`subspaceDesign_list_decoding_cz25`).
* `hT218` — ABF26 T2.18 [GK16] (`frs_is_subspaceDesign_gk16`).

Everything *else* — the τ-substitution, the bound algebra, the floor/real reconciliation —
is proved here with no `sorry` and no new axioms.  This pins precisely where the genuine
gap lives (inside `hT34`/`hT218`) and discharges the corollary's own content.

The headline result `frs_list_decoding_capacity_cz25_of_T34_T218` derives the **exact**
in-tree C3.5 statement (modulo the documented floor-vs-real subtlety, which we surface as
an explicit, provable hypothesis `hηnat : 1/η = ⌊1/η⌋`).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

/-- **Arithmetic bridge.**  For FRS with `τ(t) = ρ·s/(s-t+1)`, the T3.4 bound
`(1 - τ(t))/η` equals the C3.5 closed form `(s(1-ρ)+1-t)/(η(s+1-t))`, given
`η ≠ 0` and `t ≤ s` (so the denominator is positive). -/
theorem frs_bound_simplify
    (s t : ℕ) (ρ η : ℝ) (hη : η ≠ 0) (ht : t ≤ s) :
    (1 - (s : ℝ) * ρ / ((s : ℝ) - t + 1)) / η
      = ((s : ℝ) * (1 - ρ) + 1 - t) / (η * ((s : ℝ) + 1 - t)) := by
  have htR : (t : ℝ) ≤ s := by exact_mod_cast ht
  have hden : (s : ℝ) - t + 1 ≠ 0 := by linarith
  have hsden : (s : ℝ) + 1 - t = (s : ℝ) - t + 1 := by ring
  rw [hsden]
  field_simp
  ring

/-- If the C3.5 slack is the reciprocal of a positive natural number, then the documented
floor/real reconciliation `1 / η = ⌊1 / η⌋` holds. -/
theorem one_div_eta_eq_natFloor_of_eta_eq_one_div_nat
    {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : η = 1 / (m : ℝ)) :
    (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ) := by
  subst η
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hdiv : (1 : ℝ) / (1 / (m : ℝ)) = (m : ℝ) := by
    field_simp [hm_ne]
  rw [hdiv]
  norm_num

/-- **FRS floor-to-real C3.5 algebra from an instantiated T3.4-style bound.**

This is the shared arithmetic core of the C3.5 reduction: once the folded-RS τ-profile is
already known to satisfy the floor-faithful `Λ` bound at `Nat.floor (1 / η)`, the result is
the real-parameter C3.5 statement, provided `1 / η` is integral.  No T3.4/T2.18 content is
used here; this helper only performs the τ-substitution, bound algebra, and floor/real
reconciliation. -/
theorem frs_list_decoding_capacity_cz25_of_T34_instance
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hInst :
      (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
          (1 - (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
            (Nat.floor (1 / η)) - η) : ENNReal) ≤
        ENNReal.ofReal
          ((1 - (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
            (Nat.floor (1 / η))) / η))
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  intro n ρ δ bound
  set t : ℕ := Nat.floor (1 / η) with ht_def
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have ht_le_s : t ≤ s := by
    have : (t : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
    have hts : (t : ℝ) < s := lt_of_le_of_lt this hη_lt_s
    exact_mod_cast (le_of_lt hts)
  have hηt : (1 : ℝ) / η = (t : ℝ) := by rw [ht_def]; exact hηnat
  set τt : ℝ := (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - t + 1) with hτt_def
  have hρ : ρ = (k : ℝ) / n := rfl
  have hn : n = (Fintype.card ι : ℝ) := rfl
  have hδ_eq : δ = 1 - τt - η := by
    change 1 - ρ * s / (s - 1 / η + 1) - η = 1 - τt - η
    rw [hηt, hρ, hn, hτt_def]
    have : (k : ℝ) / (Fintype.card ι : ℝ) * (s : ℝ)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) := by ring
    rw [this]
  have hbound_eq : bound = (1 - τt) / η := by
    change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η)) = (1 - τt) / η
    rw [hηt]
    rw [hτt_def, hρ, hn]
    have hbridge := frs_bound_simplify s t ((k : ℝ) / (Fintype.card ι : ℝ)) η hη_ne ht_le_s
    have halign : (s : ℝ) * ((k : ℝ) / (Fintype.card ι : ℝ)) / ((s : ℝ) - t + 1)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) / ((s : ℝ) - t + 1) := by ring
    rw [halign] at hbridge
    rw [← hbridge]
  by_cases ht1 : 1 ≤ t
  · have htmem : t ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨ht1, ht_le_s⟩
    have hτeval : (fun r ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (Nat.floor (1 / η)) = τt := by
      rw [← ht_def]
      simp only [htmem, if_true]
      rfl
    rw [hτeval] at hInst
    rw [hδ_eq, hbound_eq]
    exact hInst
  · exfalso
    have ht0 : t = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp ht1)
    have : (1 : ℝ) / η = 0 := by rw [hηt, ht0]; norm_num
    rw [one_div, inv_eq_zero] at this
    exact hη_ne this

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — reduction form.**

Given the two genuine external ingredients (T3.4 and T2.18) **as hypotheses**, folded RS
codes are list-decodable up to capacity with the explicit C3.5 bound.  We use the
floor-faithful radius/bound (the integer `t := ⌊1/η⌋` that T3.4 actually evaluates τ at);
the surfaced hypothesis `hηnat` says `1/η` is integral, reconciling with the in-tree
real-`1/η` statement.  All steps except `hT34`/`hT218` are `sorry`-free here. -/
theorem frs_list_decoding_capacity_cz25_of_T34_T218
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    -- T2.18 instance (external admit `frs_is_subspaceDesign_gk16`), as a hypothesis:
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    -- T3.4 (external admit `subspaceDesign_list_decoding_cz25`) in its GENERAL in-tree
    -- shape: quantified over EVERY τ-subspace-design code.  The reduction feeds it the
    -- T2.18 instance `hT218`, so `hT218` is load-bearing.
    (hT34 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ η' : ℝ, 0 < η' →
        (Lambda ((C : Set (ι → Fin s → F)))
            (1 - τ (Nat.floor (1 / η')) - η') : ENNReal) ≤
          ENNReal.ofReal ((1 - τ (Nat.floor (1 / η'))) / η'))
    -- The documented floor/real reconciliation: `1/η` is integral (so the real-`1/η`
    -- C3.5 statement coincides with the floor-faithful T3.4 instance).  Provable whenever
    -- `η = 1/m`; surfaced explicitly so the reduction is faithful to the in-tree statement.
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  -- Abbreviations.
  intro n ρ δ bound
  set t : ℕ := Nat.floor (1 / η) with ht_def
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  -- `t = ⌊1/η⌋ ≤ s` from `1/η < s` (so the FRS denominator is positive and the τ branch
  -- is the `Icc 1 s` one when `t ≥ 1`).
  have ht_le_s : t ≤ s := by
    have : (t : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
    have hts : (t : ℝ) < s := lt_of_le_of_lt this hη_lt_s
    exact_mod_cast (le_of_lt hts)
  -- `1/η = t` (the surfaced reconciliation).
  have hηt : (1 : ℝ) / η = (t : ℝ) := by rw [ht_def]; exact hηnat
  -- The FRS τ at `t` (the `Icc` branch), as a real value `τt`.
  set τt : ℝ := (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - t + 1) with hτt_def
  -- Rewrite the C3.5 radius `δ` to the floor form `1 - τt - η`.
  have hρ : ρ = (k : ℝ) / n := rfl
  have hn : n = (Fintype.card ι : ℝ) := rfl
  -- `ρ * s / (s - 1/η + 1) = τt`.
  have hδ_eq : δ = 1 - τt - η := by
    change 1 - ρ * s / (s - 1 / η + 1) - η = 1 - τt - η
    rw [hηt, hρ, hn, hτt_def]
    have : (k : ℝ) / (Fintype.card ι : ℝ) * (s : ℝ)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) := by ring
    rw [this]
  -- Rewrite the C3.5 bound to `(1 - τt)/η`.
  have hbound_eq : bound = (1 - τt) / η := by
    change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η)) = (1 - τt) / η
    rw [hηt]
    -- Now bound is in terms of integer `t`; use the arithmetic bridge in reverse.
    rw [hτt_def, hρ, hn]
    -- `(s*(1-ρ)+1-t)/(η(s+1-t)) = (1 - s*ρ/(s-t+1))/η` with ρ = k/n.
    have hbridge := frs_bound_simplify s t ((k : ℝ) / (Fintype.card ι : ℝ)) η hη_ne ht_le_s
    -- align `s * (k/n) / (s-t+1)` with `(s * k / n) / (s-t+1)`
    have halign : (s : ℝ) * ((k : ℝ) / (Fintype.card ι : ℝ)) / ((s : ℝ) - t + 1)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) / ((s : ℝ) - t + 1) := by ring
    rw [halign] at hbridge
    rw [← hbridge]
  -- Instantiate the GENERAL T3.4 at the FRS τ-profile + the T2.18 design instance `hT218`.
  have hT34_inst := hT34
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) hT218 η hη_pos
  -- Now reduce `hT34_inst` to this form.
  -- The τ-function applied at `t`, with `t ∈ Icc 1 s` (need `1 ≤ t`).
  by_cases ht1 : 1 ≤ t
  · -- `t ∈ Icc 1 s`, so the τ-branch is the `Icc` formula and equals `τt`.
    have htmem : t ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨ht1, ht_le_s⟩
    have hτeval : (fun r ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (Nat.floor (1 / η)) = τt := by
      rw [← ht_def]
      simp only [htmem, if_true]
      rfl
    rw [hτeval] at hT34_inst
    rw [hδ_eq, hbound_eq]
    exact hT34_inst
  · -- `t = 0`.  Then `1/η = 0`, contradicting `η > 0` (since `1/η > 0`).
    exfalso
    have ht0 : t = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp ht1)
    have : (1 : ℝ) / η = 0 := by rw [hηt, ht0]; norm_num
    rw [one_div, inv_eq_zero] at this
    exact hη_ne this

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — unique-list/T2.18 easy slice.**

If the folded-RS close list at the floor-faithful capacity radius has at most one codeword for
every received word, then the guarded span residual is discharged by
`cz25SpanBound'_of_le_one`; combined with the supplied T2.18 subspace-design instance and the
floor/real reconciliation, this yields the C3.5 bound.  This is useful for sub-Johnson or
unique-decoding regimes and does not use the deep coordinate-fiber cap residual. -/
theorem frs_list_decoding_capacity_cz25_of_T218_le_one
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel
          ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) f
          (1 - (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
            (Nat.floor (1 / η)) - η)).ncard ≤ 1)
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  refine frs_list_decoding_capacity_cz25_of_T34_instance
    domain k s ω hs_pos η hη_pos hη_lt_s ?_ hηnat
  exact subspaceDesign_list_decoding_cz25_of_spanBound' s
    (fun r ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
    (ReedSolomon.Folded.frsCode domain k s ω) hT218 η hη_pos
    (cz25SpanBound'_of_le_one s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) hT218 η hη_pos hle)

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — from coordinate-fiber cap.**
The folded RS code is list-decodable up to capacity, reduced to the single named residual
`CZ25CoordFiberCap` (the Guruswami–Wang affine-flat coordinate-fiber cap) plus the FRS
subspace-design theorem `hT218`. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  apply frs_list_decoding_capacity_cz25_of_T34_T218 domain k s ω hs_pos η hη_pos hη_lt_s hT218 _ hηnat
  intro τ' C' h' η' hη'_pos
  exact subspaceDesign_list_decoding_cz25_of_coordFiberCap s τ' C' h' η' hη'_pos (hCap τ' C' h' η' hη'_pos)

#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_T218

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — coordinate-fiber cap plus injective GK16 FRS.**
Composes the coordinate-fiber-cap reduction with the checked C3.5-compatible FRS profile
bridge from the injective GK16 FRS side conditions. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_injective
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hEinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos η hη_pos hη_lt_s
    (frs_is_subspaceDesign_cz25Profile_of_injective domain k s ω hEinj hω_sep)
    hCap hηnat

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — coordinate-fiber cap plus admissible GK16 FRS.**
Composes the coordinate-fiber-cap reduction with the checked C3.5-compatible FRS profile
bridge from standard folded-RS admissibility and its arithmetic side conditions. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos η hη_pos hη_lt_s
    (frs_is_subspaceDesign_cz25Profile_of_admissible
      domain k s ω L hL_dom hω0 hadm hkLs hkord)
    hCap hηnat

/-- Coordinate-fiber-cap route with the documented reciprocal-natural slack convention
`η = 1 / m`.  This discharges the floor side condition `hηnat` at the call site. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  subst η
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hη_pos : 0 < (1 : ℝ) / (m : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast hm)
  have hη_lt_s : (1 : ℝ) / (1 / (m : ℝ)) < (s : ℝ) := by
    have hdiv : (1 : ℝ) / (1 / (m : ℝ)) = (m : ℝ) := by
      field_simp [hm_ne]
    rw [hdiv]
    exact_mod_cast hms
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos (1 / (m : ℝ)) hη_pos hη_lt_s hT218 hCap
    (one_div_eta_eq_natFloor_of_eta_eq_one_div_nat hm rfl)

/-- Unique-list/T2.18 route with the documented reciprocal-natural slack convention
`η = 1 / m`.  This discharges the floor side condition at the call site. -/
theorem frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel
          ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) f
          (1 - (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
            (Nat.floor (1 / η)) - η)).ncard ≤ 1) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  subst η
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hη_pos : 0 < (1 : ℝ) / (m : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast hm)
  have hη_lt_s : (1 : ℝ) / (1 / (m : ℝ)) < (s : ℝ) := by
    have hdiv : (1 : ℝ) / (1 / (m : ℝ)) = (m : ℝ) := by
      field_simp [hm_ne]
    rw [hdiv]
    exact_mod_cast hms
  exact frs_list_decoding_capacity_cz25_of_T218_le_one
    domain k s ω hs_pos (1 / (m : ℝ)) hη_pos hη_lt_s hT218 hle
    (one_div_eta_eq_natFloor_of_eta_eq_one_div_nat hm rfl)

/-- Injective-GK16 route with the documented reciprocal-natural slack convention
`η = 1 / m`.  This discharges the floor side condition `hηnat` at the call site. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (hEinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms
    (frs_is_subspaceDesign_cz25Profile_of_injective domain k s ω hEinj hω_sep)
    hCap

/-- Admissible-GK16 route with the documented reciprocal-natural slack convention
`η = 1 / m`.  This discharges the floor side condition `hηnat` at the call site. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms
    (frs_is_subspaceDesign_cz25Profile_of_admissible
      domain k s ω L hL_dom hω0 hadm hkLs hkord)
    hCap

/-- Coordinate-fiber-cap route from the discharged T2.18 order/inter front door.  This avoids
requiring callers to manually assemble `ReedSolomon.Folded.Admissible L s ω`. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos η hη_pos hη_lt_s
    (frs_is_subspaceDesign_cz25Profile_of_gk16Profile domain k s ω
      (frs_is_subspaceDesign_gk16_of_orderOf_ge_of_inter
        domain k s ω L hL_dom hL_zero hω0 hs_order hinter hkLs hkord))
    hCap hηnat

/-- Reciprocal-natural version of
`frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter`. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms
    (frs_is_subspaceDesign_cz25Profile_of_gk16Profile domain k s ω
      (frs_is_subspaceDesign_gk16_of_orderOf_ge_of_inter
        domain k s ω L hL_dom hL_zero hω0 hs_order hinter hkLs hkord))
    hCap

/-- Coordinate-fiber-cap route from the discharged T2.18 order/coset-separation front door.
This packages the inter-orbit condition via `admissible_of_orderOf_ge_of_cosetSep`. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos η hη_pos hη_lt_s
    (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
      domain k s ω L hL_dom hL_zero hω0 hs_order hcoset hkLs hkord)
    hCap hηnat

/-- Reciprocal-natural version of
`frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep`. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ)) (hms : m < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms
    (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
      domain k s ω L hL_dom hL_zero hω0 hs_order hcoset hkLs hkord)
    hCap

#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_injective
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible
#print axioms one_div_eta_eq_natFloor_of_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_T34_instance
#print axioms frs_list_decoding_capacity_cz25_of_T218_le_one
#print axioms frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter
#print axioms
  frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat
#print axioms frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep
#print axioms
  frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat

end CodingTheory
