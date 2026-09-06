/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.RestrictedSumsetGeneral
import Research.ProximityPrize.SubsetSumRadiusOne

/-!
## Reed–Solomon MCA Corollary at General Degree $k$

Combining the general Erdős–Heilbronn / Dias da Silva–Hamidoune bound ($h = k + 1$) with the
unconditional subset-sum lower bound `ProximityGap.epsMCA_one_ge_card_subsetSums` yields a
lower bound for the maximum correlation agreement
$\varepsilon_{\text{mca}}(\text{RS}[\mathbb{F}, \text{domain}, k], 1)$
with explicit additive content.
-/

namespace ProximityGap

open scoped BigOperators ENNReal

/- Suppress unused variable linters for the localized bridge variables. -/
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section EHGeneral

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The restricted `(k+1)`-sumset of an injective evaluation domain's image is contained in the
`(k+1)`-subset-sum set of the domain. -/
lemma restrictedSumset_subset_subsetSumsKplus1 (domain : ι ↪ F) (k : ℕ) :
    MvPolynomial.restrictedSumset (Finset.image (fun i => domain i) Finset.univ) (k + 1)
      ⊆ subsetSumsKplus1 domain k := by
  classical
  intro γ hγ
  rw [MvPolynomial.restrictedSumset, Finset.mem_image] at hγ
  obtain ⟨S, hS, rfl⟩ := hγ
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  -- Each element of `S` is `domain i` for a unique `i`; pull `S` back to a subset `T ⊆ ι`.
  set T : Finset ι := Finset.univ.filter (fun i => domain i ∈ S) with hT
  have hTimage : T.image (fun i => domain i) = S := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [hT, Finset.mem_filter] at hi
      exact hi.2
    · intro x hx
      have := hSsub hx
      rw [Finset.mem_image] at this
      obtain ⟨i, -, rfl⟩ := this
      rw [Finset.mem_image]
      exact ⟨i, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hTcard : T.card = k + 1 := by
    have : (T.image (fun i => domain i)).card = T.card :=
      Finset.card_image_of_injective _ domain.injective
    rw [hTimage] at this
    omega
  rw [subsetSumsKplus1, Finset.mem_image]
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hTcard⟩
  · rw [← hTimage, Finset.sum_image (fun a _ b _ hab => domain.injective hab)]

/-- The image of an injective `domain` has cardinality `n := |ι|`. -/
lemma card_image_domain' (domain : ι ↪ F) :
    (Finset.image (fun i => domain i) Finset.univ).card = Fintype.card ι := by
  rw [Finset.card_image_of_injective _ domain.injective, Finset.card_univ]

/-- **Erdős–Heilbronn / Dias da Silva–Hamidoune floor for `ε_mca(RS, 1)` at general `k`.**
For `RS[F, domain, k]` over a finite field `F` of prime characteristic `p`, with `n := |ι|`,
`k + 1 ≤ n ≤ p`, and `(k+1)(n - (k+1)) < p`:

  `ε_mca(RS[F, domain, k], 1) ≥ ((k+1)(n - k - 1) + 1) / q`. -/
theorem epsMCA_one_ge_erdos_heilbronn_general (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hchar : ringChar F = p) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι) (hnp : Fintype.card ι ≤ p)
    (hsmall : (k + 1) * (Fintype.card ι - (k + 1)) < p) :
    (((k + 1) * (Fintype.card ι - (k + 1)) + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  classical
  set n := Fintype.card ι with hn_def
  set A : Finset F := Finset.image (fun i => domain i) Finset.univ with hA
  have hAcard : A.card = n := card_image_domain' domain
  -- the general Erdős–Heilbronn bound at `h = k + 1`
  have hEH : (k + 1) * (n - (k + 1)) + 1
      ≤ (MvPolynomial.restrictedSumset A (k + 1)).card := by
    have := MvPolynomial.erdos_heilbronn (F := F) hp hchar A (k + 1) (by omega)
      (by rw [hAcard]; exact hk) (by rw [hAcard]; exact hnp) (by rw [hAcard]; exact hsmall)
    rwa [hAcard] at this
  have hsubset : (k + 1) * (n - (k + 1)) + 1 ≤ (subsetSumsKplus1 domain k).card :=
    le_trans hEH (Finset.card_le_card (restrictedSumset_subset_subsetSumsKplus1 domain k))
  have hfloor := epsMCA_one_ge_card_subsetSums (F := F) domain (k := k) (by omega)
  refine le_trans ?_ hfloor
  have hnum : (((k + 1) * (n - (k + 1)) + 1 : ℕ) : ENNReal)
      ≤ ((subsetSumsKplus1 domain k).card : ENNReal) := by exact_mod_cast hsubset
  exact ENNReal.div_le_div_right hnum _

end EHGeneral

end ProximityGap
