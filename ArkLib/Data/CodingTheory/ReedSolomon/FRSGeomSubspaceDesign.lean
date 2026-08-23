/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleDischarge
import ArkLib.Data.CodingTheory.SubspaceDesign

/-!
# Unconditional FRS τ-subspace-design on the canonical geometric domain (ABF26 T2.18)

`SubspaceDesign.lean` proves `frs_is_subspaceDesign_gk16_of_admissible`: the folded Reed-Solomon
code is a τ-subspace-design **given** `ReedSolomon.Folded.Admissible L s ω` (plus the order
bounds). `AdmissibleDischarge.lean` discharges that `Admissible` predicate unconditionally on the
canonical GR08 geometric domain `L = {γ^{s·i}}`, `ω = γ` (`geomDomain_admissible`).

This file composes the two into a **fully unconditional** FRS subspace-design instance — no
remaining admit — for any nonzero `γ` of multiplicative order `≥ s·n`. This upgrades the T2.18
family of ABF26 §4 from an external `Prop` admit to a proved in-tree theorem on the canonical
domain.
-/

namespace ReedSolomon.Folded

open scoped Classical
open CodingTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 2.18 on the canonical geometric domain — unconditional.** For `γ ≠ 0` of
multiplicative order `≥ s·n`, with `0 < s`, `0 < n`, `k ≤ s·n`, `k ≤ orderOf γ`, the folded
Reed-Solomon code over the geometric domain `{γ^{s·i} : i ∈ Fin n}` with folding element `γ` is a
τ-subspace-design for `τ(r) = (k-1)/n` on `r ∈ [s]` (and `1` otherwise). No `Admissible` admit
remains: it is discharged by `geomDomain_admissible`. -/
theorem frs_geomDomain_isSubspaceDesign
    (γ : F) (k s n : ℕ)
    (hs : 0 < s) (hn : 0 < n) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ) :
    CodingTheory.IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card (Fin n) else 1)
      (frsCode (geomDomainEmb γ s n hs hsn) k s γ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hkLs' : k ≤ s * Fintype.card (Fin n) := by simpa using hkLs
  have hadm : Admissible (Finset.image (geomDomainEmb γ s n hs hsn) Finset.univ) s γ := by
    have := geomDomain_admissible γ s n hs hn hγ hsn
    -- `geomDomainEmb` has the same underlying function as `geomDomainFn`.
    simpa [geomDomainEmb] using this
  have hL_dom : ∀ i : Fin n, geomDomainEmb γ s n hs hsn i ∈
      Finset.image (geomDomainEmb γ s n hs hsn) Finset.univ := by
    intro i; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  exact CodingTheory.frs_is_subspaceDesign_gk16_of_admissible
    (geomDomainEmb γ s n hs hsn) k s γ
    (Finset.image (geomDomainEmb γ s n hs hsn) Finset.univ)
    hL_dom hγ hadm hkLs' hkord

set_option linter.unusedFintypeInType false in
/-- **CZ25-profile T2.18 on the canonical geometric domain.**

This is the C3.5-compatible profile companion to `frs_geomDomain_isSubspaceDesign`, obtained by
monotonically widening the proved GK16 profile to
`τ(r) = s * k / n / (s - r + 1)` on `r ∈ [s]`. No additional geometric side condition is
introduced beyond the canonical-domain order bound. -/
theorem frs_geomDomain_isSubspaceDesign_cz25Profile
    (γ : F) (k s n : ℕ)
    (hs : 0 < s) (hn : 0 < n) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card (Fin n) / ((s : ℝ) - r + 1) else 1)
      (frsCode (geomDomainEmb γ s n hs hsn) k s γ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact frs_is_subspaceDesign_cz25Profile_of_gk16Profile
    (geomDomainEmb γ s n hs hsn) k s γ
    (frs_geomDomain_isSubspaceDesign γ k s n hs hn hγ hsn hkLs hkord)

end ReedSolomon.Folded

#print axioms ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
