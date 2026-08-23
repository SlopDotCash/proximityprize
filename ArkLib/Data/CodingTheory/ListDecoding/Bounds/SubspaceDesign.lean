/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds.RandomAndReedSolomon

/-!
# List-decoding bounds from ABF26 §3 — subspace-design upper bounds

The subspace-design upper bounds and the CZ25 folded-RS capacity endpoints. Part 3 of
the `Bounds` split; see the `Bounds.lean` umbrella for the full overview.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ListDecodable

section SubspaceDesignUpperBounds

/-- **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable
up to capacity, conditional on the corrected guarded span residual.

  `|Λ(C, 1 - τ(1/η) - η)| ≤ (1 - τ(1/η)) / η`

Combined with `IsSubspaceDesign` (ABF26 D2.16) and `subspaceDesign_tau_lower`
(L2.17), this gives a list-decoding bound up to capacity for any subspace-design code.

This is discharged from the corrected residual `CZ25SpanBound'`, which keeps the real
Guruswami-Wang agreement-budget theorem explicit while the `Λ` packaging is checked here. -/
theorem subspaceDesign_list_decoding_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη_pos : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη_pos) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_spanBound' s τ C h η hη_pos hSB

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — honest reduction form.**

The *full in-tree-provable content* of C3.5, with the two genuinely-external ingredients
surfaced as explicit hypotheses (never faked):

* `hT218` — ABF26 T2.18 [GK16] (`frs_is_subspaceDesign_gk16`): FRS is τ-subspace-design.
* `hT34` — ABF26 T3.4 [CZ25 B.5] (`subspaceDesign_list_decoding_cz25`), in its *general*
  in-tree shape (quantified over every τ-subspace-design code).
* `hηnat` — the documented floor/real reconciliation `1/η = ⌊1/η⌋` (provable whenever
  `η = 1/m`), reconciling the real-`1/η` C3.5 statement with the floor-faithful T3.4
  instance T3.4 actually evaluates τ at.

Everything else (the τ-substitution at `τ(r) = sρ/(s-r+1)`, the bound algebra
`(1-τ)/η = (s(1-ρ)+1-t)/(η(s+1-t))`, the floor/real reconciliation) is **proven with no
`sorry` and no new axioms** in `CZ25CapacityReduction.frs_list_decoding_capacity_cz25_of_T34_T218`,
to which this is a direct wrapper. This pins the genuine residual precisely inside
`hT218`/`hT34` and discharges the corollary's own content honestly. -/
theorem frs_list_decoding_capacity_cz25_of_residuals
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hT34 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ η' : ℝ, 0 < η' →
        (Lambda ((C : Set (ι → Fin s → F)))
            (1 - τ (Nat.floor (1 / η')) - η') : ENNReal) ≤
          ENNReal.ofReal ((1 - τ (Nat.floor (1 / η'))) / η'))
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_T34_T218
    domain k s ω hs_pos η hη_pos hη_lt_s hT218 hT34 hηnat

/-- **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are
list-decodable up to capacity. Let `C := FRS[F, L, k, s, ω]` be a folded RS code of
rate `ρ`. For any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))`

When `η ≥ √(3/s)`, the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`. Derives from
T3.4 + T2.18 (FRS is τ-subspace-design). Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [CZ25 Cor 2.21] is the *corrected, provable* folded-RS
capacity list-decodability result via subspace designs — NOT the disproven up-to-capacity
conjecture for plain Reed-Solomon proximity gaps / DEEP-FRI list-decodability (those are
FALSE per eprint.iacr.org/2025/2046 and live elsewhere). Folded RS attains capacity by the
subspace-design argument (arXiv 2601.10047). It is unformalized: mathlib has no folded-RS /
subspace-design / list-decoding API, so the `sorry` is a ground-up formalization task, not
a port, and follows once T3.4 + T2.18 are formalized.
See `research/formal/arklib-proof-research-2026-06.md`.

**HONEST REDUCTION AVAILABLE.** The corollary's *own* content (τ-substitution + bound
algebra + floor/real reconciliation) is fully proven, `sorry`-free and axiom-clean, in
`frs_list_decoding_capacity_cz25_of_residuals` (above), which derives this exact
conclusion from T2.18, the general T3.4, and `hηnat : 1/η = ⌊1/η⌋` as explicit
hypotheses. The bare `sorry` below remains only because the *unhypothesized* in-tree
statement cannot supply those two external admits; it is the documented spec, and any
caller with the residuals in hand should route through `_of_residuals` instead. -/
def frs_list_decoding_capacity_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) : Prop :=
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound
  -- ABF26-C3.5; external statement [CZ25 Cor 2.21].
  -- Missing ingredient: this is a COROLLARY of T3.4 via T2.18 (frs_is_subspaceDesign_gk16:
  -- FRS is τ-subspace-design). Once T3.4 and T2.18 are proven, C3.5 closes by instantiating
  -- T3.4 at the FRS τ(r)=sρ/(s-r+1) and simplifying with 1/η<s. Blocked on T3.4 (above) +
  -- T2.18 (external admit in SubspaceDesign.lean). No independent external content.

/-- Prop-level wrapper for ABF26 C3.5.

This closes the external statement `frs_list_decoding_capacity_cz25` directly from the checked
residual bundle.  It is useful for downstream assembly code that targets the named `Prop`
statement rather than its unfolded inequality body. -/
theorem frs_list_decoding_capacity_cz25_of_residuals_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hT34 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ η' : ℝ, 0 < η' →
        (Lambda ((C : Set (ι → Fin s → F)))
            (1 - τ (Nat.floor (1 / η')) - η') : ENNReal) ≤
          ENNReal.ofReal ((1 - τ (Nat.floor (1 / η'))) / η'))
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_residuals
    domain k s ω hs_pos η hη_pos hη_lt_s hT218 hT34 hηnat

/-- Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice.

This wraps the unfolded reduction `frs_list_decoding_capacity_cz25_of_T218_le_one`, so callers
with a T2.18 folded-RS subspace-design instance and a per-word `ncard ≤ 1` close-list hypothesis
can target the named external `frs_list_decoding_capacity_cz25` proposition directly. -/
theorem frs_list_decoding_capacity_cz25_of_T218_le_one_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_T218_le_one
    domain k s ω hs_pos η hη_pos hη_lt_s hT218 hle hηnat

/-- Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice, using the documented
reciprocal-natural slack convention `η = 1 / m` to discharge the floor side condition. -/
theorem frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms hT218 hle

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18.
This wraps the unfolded reduction
`frs_list_decoding_capacity_cz25_of_coordFiberCap_T218`, so callers can target the named
external `frs_list_decoding_capacity_cz25` proposition directly. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218
    domain k s ω hs_pos η hη_pos hη_lt_s hT218 hCap hηnat

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_injective
    domain k s ω hs_pos η hη_pos hη_lt_s hEinj hω_sep hCap hηnat

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible
    domain k s ω hs_pos η hη_pos hη_lt_s L hL_dom hω0 hadm hkLs hkord hCap hηnat

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18, using the documented
reciprocal-natural slack convention `η = 1 / m` to discharge the floor side condition. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms hT218 hCap

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge, using
the reciprocal-natural slack convention `η = 1 / m` to discharge the floor side condition. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (hEinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms hEinj hω_sep hCap

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge, using
the reciprocal-natural slack convention `η = 1 / m` to discharge the floor side condition. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms L hL_dom hω0 hadm hkLs hkord hCap

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door.
This keeps the inter-orbit separation hypothesis explicit and avoids constructing
`ReedSolomon.Folded.Admissible L s ω` at call sites. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter
    domain k s ω hs_pos η hη_pos hη_lt_s L hL_dom hL_zero hω0 hs_order
    hinter hkLs hkord hCap hηnat

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door,
using the reciprocal-natural slack convention `η = 1 / m` to discharge the floor side condition. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms L hL_dom hL_zero hω0 hs_order
    hinter hkLs hkord hCap

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18
front door. This packages the inter-orbit side condition through coset separation. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_prop
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
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep
    domain k s ω hs_pos η hη_pos hη_lt_s L hL_dom hL_zero hω0 hs_order
    hcoset hkLs hkord hCap hηnat

/-- Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18
front door, using the reciprocal-natural slack convention `η = 1 / m` to discharge the floor
side condition. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25 domain k s ω hs_pos η hη_pos hη_lt_s := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h_one_div : (1 : ℝ) / η = (m : ℝ) := by
    rw [hη]
    field_simp [hm_ne]
  have hms : m < s := by
    have hmsR : (m : ℝ) < (s : ℝ) := by
      rwa [h_one_div] at hη_lt_s
    exact_mod_cast hmsR
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat
    domain k s ω hs_pos η hm hη hms L hL_dom hL_zero hω0 hs_order
    hcoset hkLs hkord hCap

end SubspaceDesignUpperBounds

-- Axiom audit on the ABF26 §3 headline front doors and narrowed residual bridges.  These are the
-- source-level regression anchors for #74 and #79: BKR06 and GHSZ02 isolate their
-- geometric/asymptotic cores, CZ25/FRS expose the design-dimension and FRS-subspace-design
-- residuals, and GLMRSW22 now exposes the random-generator-matrix probability surface without
-- turning the external paper statements into fake theorems.
#print axioms CodingTheory.large_alphabet_barrier_bdg24_agl23
#print axioms CodingTheory.random_linear_lambda_lower_glmrsw22
#print axioms CodingTheory.uniformRandomLinearGeneratorMatrix
#print axioms CodingTheory.support_uniformRandomLinearGeneratorMatrix
#print axioms CodingTheory.mem_support_uniformRandomLinearGeneratorMatrix
#print axioms CodingTheory.randomLinearCodeOfGeneratorMatrix
#print axioms CodingTheory.uniformRandomLinearCode
#print axioms CodingTheory.randomLinearLambdaLowerEvent
#print axioms CodingTheory.randomLinearLambdaLowerProbability
#print axioms CodingTheory.randomLinearLambdaLowerFirstMomentResidual
#print axioms CodingTheory.exists_randomLinearLambdaLowerEvent_of_probability_pos
#print axioms CodingTheory.randomLinearLambdaLowerProbability_pos_of_exists_event
#print axioms CodingTheory.randomLinearLambdaLowerFirstMomentResidual_of_exists_event
#print axioms CodingTheory.exists_code_of_randomLinearLambdaLowerEvent
#print axioms CodingTheory.exists_code_of_randomLinearLambdaLowerFirstMomentResidual
#print axioms CodingTheory.random_linear_lambda_lower_glmrsw22_random_generator_matrix
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06
#print axioms CodingTheory.rs_lambda_large_prime_ghsz02
#print axioms CodingTheory.subspaceDesign_list_decoding_cz25
#print axioms CodingTheory.frs_list_decoding_capacity_cz25
#print axioms CodingTheory.random_linear_lambda_lower_glmrsw22_of_random_generator_matrix
#print axioms random_linear_lambda_lower_glmrsw22_random_generator_matrix_of_first_moment_residual
#print axioms random_linear_lambda_lower_glmrsw22_of_first_moment_residual
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06_of_residuals
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06_of_injection
#print axioms CodingTheory.rs_lambda_large_prime_ghsz02_of_residuals
#print axioms CodingTheory.rs_lambda_large_prime_ghsz02_of_injection
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_residuals
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_residuals_prop
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat_prop
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_prop
#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop

end CodingTheory
