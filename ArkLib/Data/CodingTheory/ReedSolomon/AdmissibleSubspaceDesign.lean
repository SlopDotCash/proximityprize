/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleDischarge
import ArkLib.Data.CodingTheory.SubspaceDesign

/-!
# FRS subspace-design front doors from order-bounded admissibility

This file composes the order-theoretic and coset-separation discharges for
`ReedSolomon.Folded.Admissible` with the existing folded-Reed-Solomon subspace-design front
doors. `SubspaceDesign.lean` exposes the GK16 explicit inter-orbit wrapper; this file adds the
coset-separation convenience form and the CZ25-profile companions.
-/

namespace CodingTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **GK16/T2.18 FRS profile from order and coset separation.** This packages the full
`ReedSolomon.Folded.Admissible` discharge from `0 ∉ L`, `s ≤ orderOf ω`, and separation of
the selected domain points by `ω`-cosets. -/
theorem frs_is_subspaceDesign_gk16_of_orderOf_ge_of_cosetSep
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_gk16_of_admissible domain k s ω L hL_dom hω0
    (ReedSolomon.Folded.admissible_of_orderOf_ge_of_cosetSep L s ω h0 hs_order hcoset)
    hkLs hkord

/-- **C3.5-compatible FRS profile from order-bounded admissibility.** The intra-orbit part of
`ReedSolomon.Folded.Admissible` is discharged by `s ≤ orderOf ω` and `0 ∉ L`; callers still
provide the genuine inter-orbit separation condition. -/
theorem frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_cz25Profile_of_admissible domain k s ω L hL_dom hω0
    (ReedSolomon.Folded.admissible_of_orderOf_ge_of_inter L s ω h0 hs_order hinter)
    hkLs hkord

/-- **C3.5-compatible FRS profile from order and coset separation.** This is the CZ25-profile
companion to `frs_is_subspaceDesign_gk16_of_orderOf_ge_of_cosetSep`, routing through the
existing profile-monotonicity bridge. -/
theorem frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_cz25Profile_of_admissible domain k s ω L hL_dom hω0
    (ReedSolomon.Folded.admissible_of_orderOf_ge_of_cosetSep L s ω h0 hs_order hcoset)
    hkLs hkord

end CodingTheory

#print axioms CodingTheory.frs_is_subspaceDesign_gk16_of_orderOf_ge_of_cosetSep
#print axioms CodingTheory.frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
#print axioms CodingTheory.frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
