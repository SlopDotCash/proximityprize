/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeFirstMomentExists
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# GLMRSW22 message → codeword count bridge (issue #79)

The GLMRSW22 random-linear-code list-size lower bound (ABF26 T3.11 / [GLMRSW22 Thm 4.1])
runs a first-moment argument that counts **messages** `m` whose codeword `m ᵥ* G` lands in a
target set, while the list size `|Λ(C, δ)|` counts distinct **codewords**. These two counts
disagree in general: a non-injective generator matrix `G` (deficient row rank) sends several
messages to the same codeword, so the message count *over-counts* codewords. A naive
"message count = codeword count" identity is therefore **false** without a rank hypothesis —
this is the subtlety that makes the GLMRSW22 reduction delicate.

This file isolates and proves the exact resolution: **when the message-to-codeword map
`m ↦ m ᵥ* G` is injective (the generator matrix has full row rank), the over-count collapses
to an equality.** Concretely, the set of close codewords of `fromRowGenMat G` to a center `y`
is the *image*, under the injective map `m ↦ m ᵥ* G`, of the set of messages whose codeword
is close to `y`; hence the two cardinalities coincide (`ncard`).

Combined with `closeCodewordsRel C 0 δ ⊆ Λ(C, δ)` (the per-center lower bound on `Lambda`),
this converts the proven deterministic message-count lower bound
(`exists_generator_count_ge_average`) into a *codeword*-count lower bound at the full-rank
generator matrices — the correct direction for bounding `Lambda` from below.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `mem_fromRowGenMat_iff` — `c ∈ fromRowGenMat G ↔ ∃ m, m ᵥ* G = c`.
* `closeCodewordsRel_eq_image` — the close-codeword set is the image of the close-message set
  under `m ↦ m ᵥ* G` (holds for every `G`).
* `ncard_closeCodewordsRel_eq_of_injective` — for injective `m ↦ m ᵥ* G` (full row rank), the
  close-codeword count equals the close-message count (the over-count collapses to equality).
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix
open ListDecodable

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in the row-generated code is exactly being `m ᵥ* G` for some message `m`. -/
theorem mem_fromRowGenMat_iff {G : Matrix (Fin k) ι F} (c : ι → F) :
    c ∈ (LinearCode.fromRowGenMat G : Set (ι → F)) ↔ ∃ m : Fin k → F, m ᵥ* G = c := by
  unfold LinearCode.fromRowGenMat
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hm]; rfl⟩
  · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hm]; rfl⟩

/-- **Codeword/message bridge (the GLMRSW22 over-counting set identity).**
The set of codewords of `fromRowGenMat G` close to a center `y` (within relative radius `δ`)
is exactly the *image*, under the message-to-codeword map `m ↦ m ᵥ* G`, of the set of
messages whose codeword is close to `y`. (This set identity holds for every `G`; injectivity
of the map is what upgrades it to an equality of *cardinalities* below — without it the image
collapses several messages onto the same codeword.) -/
theorem closeCodewordsRel_eq_image
    {G : Matrix (Fin k) ι F}
    (y : ι → F) (δ : ℝ) :
    closeCodewordsRel (LinearCode.fromRowGenMat G : Set (ι → F)) y δ
      = (fun m : Fin k → F => m ᵥ* G) '' {m | m ᵥ* G ∈ relHammingBall y δ} := by
  ext c
  simp only [closeCodewordsRel, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hcCode, hcBall⟩
    rw [mem_fromRowGenMat_iff] at hcCode
    obtain ⟨m, hm⟩ := hcCode
    exact ⟨m, by rw [hm]; exact hcBall, hm⟩
  · rintro ⟨m, hmBall, hmc⟩
    refine ⟨?_, by rw [← hmc]; exact hmBall⟩
    rw [mem_fromRowGenMat_iff]; exact ⟨m, hmc⟩

/-- **Codeword count = message count for full-rank generator matrices.**
The `ncard` of the close-codeword set equals the `ncard` of the close-message set: the
over-count collapses to an equality precisely when `m ↦ m ᵥ* G` is injective. This is the
identity the GLMRSW22 first moment needs in order to read its message-count lower bound as a
*codeword*-count (hence `Λ`) lower bound. -/
theorem ncard_closeCodewordsRel_eq_of_injective
    {G : Matrix (Fin k) ι F}
    (hinj : Function.Injective (fun m : Fin k → F => m ᵥ* G))
    (y : ι → F) (δ : ℝ) :
    (closeCodewordsRel (LinearCode.fromRowGenMat G : Set (ι → F)) y δ).ncard
      = {m : Fin k → F | m ᵥ* G ∈ relHammingBall y δ}.ncard := by
  rw [closeCodewordsRel_eq_image y δ]
  exact Set.ncard_image_of_injective _ hinj

end ArkLib.RandomLinearCode

-- Axiom audit: every public result must reduce to the standard kernel axioms only.
#print axioms ArkLib.RandomLinearCode.mem_fromRowGenMat_iff
#print axioms ArkLib.RandomLinearCode.closeCodewordsRel_eq_image
#print axioms ArkLib.RandomLinearCode.ncard_closeCodewordsRel_eq_of_injective
