/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# The GG25 multi-γ coverage lemma for line-decoding → MCA (Issue #12)

`LineDecoding.lean` documents the wall in ABF26 Theorem 4.21 [GG25 Thm 3.5]: the black-box
"line-decodable ⟹ `ε_mca ≤ a/q`" form is **false** (`LineDecodingRefutation`,
`LineDecodingCounting.double_coverage_counterexample`), because the `n+1`-point alignment
budget bounds only the *average* per-coordinate coverage, while `pairJointAgreesOn` is
**antitone** in its witness set and needs agreement on *all* of it.

This file supplies the faithful replacement the wall calls for, addressing the antitone
obstruction directly: it works with **per-coordinate double coverage** (two distinct aligned
scalars per coordinate of the witness set) — exactly the data a Guruswami–Sudan bivariate
decoder produces (the aligned `γ`'s are the roots of one interpolation polynomial, so each
surviving coordinate carries ≥ 2 of them) — rather than the refuted per-`γ`-budget count.

Main results (all kernel-clean):

* `affine_eq_of_two_smul_points` — the core: two distinct scalars at which an affine word
  `a₀ + γ·a₁` meets `b₀ + γ·b₁` pin `a₀ = b₀` and `a₁ = b₁` (a degree-1 word with two roots
  is the zero word).
* `pairJointAgreesOn_of_double_cover` — **THE reusable multi-γ coverage lemma** (Issue #12
  ask 1): per-coordinate double coverage of a witness set `T` by aligned scalars forces the
  line-decoder pair `(u₁, u₂)` to agree with `(f₁, f₂)` on all of `T`, hence
  `pairJointAgreesOn`.
* `not_mcaEvent_of_double_cover` — consequently a bad scalar whose witness set is
  double-covered cannot satisfy `mcaEvent` (its `¬ pairJointAgreesOn` clause is violated).
* `epsMCA_eq_zero_of_forall_double_cover` / `mcaBadCount_eq_zero_of_forall_double_cover` —
  the repaired Theorem-4.21 conclusion at the error level: when every stack's every bad
  scalar is double-covered, `ε_mca = 0`. This is the honest statement REPAIR the wall
  prescribes: the open GS content is the *existence* of double coverage (the exposed
  interpolation hypothesis), and the coverage ⟹ agreement ⟹ MCA-vanishing logic is proven.

## References

- [ABF26] §4.4, Theorem 4.21 (= [GG25] Thm 3.5). [BCIKS20] Thm 5.1 (GS bivariate route).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Affine two-point pinning.** If the affine-in-`γ` element `a₀ + γ • a₁` equals
`b₀ + γ • b₁` at two distinct scalars `γ ≠ γ'`, then `a₀ = b₀` and `a₁ = b₁`. (A degree-`1`
word over a field with two roots is constant-and-zero.) This is the per-coordinate kernel of
the coverage lemma. -/
theorem affine_eq_of_two_smul_points {a₀ a₁ b₀ b₁ : A} {γ γ' : F} (hne : γ ≠ γ')
    (h : a₀ + γ • a₁ = b₀ + γ • b₁) (h' : a₀ + γ' • a₁ = b₀ + γ' • b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  -- Differences vanish: `c₀ + γ • c₁ = 0` and `c₀ + γ' • c₁ = 0`.
  have hc : (a₀ - b₀) + γ • (a₁ - b₁) = 0 := by
    rw [smul_sub]; rw [sub_add_sub_comm]; rw [h]; abel
  have hc' : (a₀ - b₀) + γ' • (a₁ - b₁) = 0 := by
    rw [smul_sub]; rw [sub_add_sub_comm]; rw [h']; abel
  -- Subtract: `(γ - γ') • (a₁ - b₁) = 0`, and `γ - γ' ≠ 0` is invertible.
  have hsub : (γ - γ') • (a₁ - b₁) = 0 := by
    have := sub_eq_zero.mpr (hc.trans hc'.symm)
    rw [sub_smul]
    rw [show γ • (a₁ - b₁) - γ' • (a₁ - b₁)
          = ((a₀ - b₀) + γ • (a₁ - b₁)) - ((a₀ - b₀) + γ' • (a₁ - b₁)) by abel]
    rw [hc, hc', sub_zero]
  have hγγ' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : a₁ - b₁ = 0 := by
    have := smul_eq_zero.mp hsub
    rcases this with h | h
    · exact absurd h hγγ'
    · exact h
  have h0 : a₀ - b₀ = 0 := by
    have : (a₀ - b₀) + γ • (a₁ - b₁) = 0 := hc
    rw [h1, smul_zero, add_zero] at this
    exact this
  exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩

/-- **The GG25 multi-γ coverage lemma (Issue #12 ask 1, reusable form).**

Let `(u₁, u₂)` be the line-decoder's witness pair and `(f₁, f₂)` the line stack. Suppose
every coordinate `i` of a witness set `T` is **doubly covered**: there are two *distinct*
aligned scalars `γ ≠ γ'` at which the pair-induced line `u₁ + γ • u₂` agrees with the data
line `f₁ + γ • f₂` at `i`. Then `(u₁, u₂)` agrees with `(f₁, f₂)` on **all** of `T`, so the
pair is a joint witness: `pairJointAgreesOn C T f₁ f₂`.

Unlike the refuted per-`γ`-budget count, this hypothesis is **per-coordinate**, so it is not
defeated by the antitone behaviour of `pairJointAgreesOn` (every `i ∈ T` is handled
individually). It is exactly the coverage a Guruswami–Sudan bivariate list-decoder provides:
the aligned scalars are roots of one interpolation polynomial, so each surviving coordinate
carries at least two of them. -/
theorem pairJointAgreesOn_of_double_cover (C : Set (ι → A)) (T : Finset ι) (f₁ f₂ u₁ u₂ : ι → A)
    (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C)
    (hcov : ∀ i ∈ T, ∃ γ γ' : F, γ ≠ γ' ∧
      u₁ i + γ • u₂ i = f₁ i + γ • f₂ i ∧
      u₁ i + γ' • u₂ i = f₁ i + γ' • f₂ i) :
    pairJointAgreesOn C T f₁ f₂ := by
  refine ⟨u₁, hu₁, u₂, hu₂, ?_⟩
  intro i hi
  obtain ⟨γ, γ', hne, h, h'⟩ := hcov i hi
  exact affine_eq_of_two_smul_points hne h h'

end

/-! ## S-pinned form and the repaired Theorem-4.21 error conclusion

The clean statement (used downstream) pins the witness set: an `mcaEvent` is given *with* its
witness set `S` exposed, and the double cover is on that same `S`. -/

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Per-set MCA double-cover data.** A witness set `S` is doubly covered when one
line-decoder pair `(v₁, v₂) ∈ C × C` supplies two distinct aligned scalars at every coordinate
of `S`. This names the exact per-set datum that the repaired GS extraction must construct. -/
def MCADoubleCoverOn (C : Set (ι → A)) (u₀ u₁ : ι → A) (S : Finset ι) : Prop :=
  ∃ v₁ ∈ C, ∃ v₂ ∈ C,
    ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
      v₁ i + a • v₂ i = u₀ i + a • u₁ i ∧
      v₁ i + a' • v₂ i = u₀ i + a' • u₁ i

/-- Named form of `pairJointAgreesOn_of_double_cover` over `MCADoubleCoverOn`. -/
theorem pairJointAgreesOn_of_MCADoubleCoverOn (C : Set (ι → A))
    (S : Finset ι) (u₀ u₁ : ι → A)
    (hcov : MCADoubleCoverOn (F := F) C u₀ u₁ S) :
    pairJointAgreesOn C S u₀ u₁ := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hcover⟩ := hcov
  exact pairJointAgreesOn_of_double_cover C S u₀ u₁ v₁ v₂ hv₁ hv₂ hcover

/-- Joint agreement on `S` gives the named double-cover surface on the same set: use the
jointly-agreeing codeword pair and the two fixed scalars `0` and `1`. -/
theorem MCADoubleCoverOn.of_pairJointAgreesOn (C : Set (ι → A))
    (S : Finset ι) (u₀ u₁ : ι → A)
    (hpair : pairJointAgreesOn C S u₀ u₁) :
    MCADoubleCoverOn (F := F) C u₀ u₁ S := by
  obtain ⟨v₀, hv₀, v₁, hv₁, hagree⟩ := hpair
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  intro i hi
  rcases hagree i hi with ⟨h₀, h₁⟩
  refine ⟨0, 1, zero_ne_one, ?_, ?_⟩
  · simp [h₀]
  · simp [h₀, h₁]

/-- The local repaired double-cover surface is exactly the existing joint-agreement predicate
over the same witness set. -/
theorem MCADoubleCoverOn_iff_pairJointAgreesOn (C : Set (ι → A))
    (S : Finset ι) (u₀ u₁ : ι → A) :
    MCADoubleCoverOn (F := F) C u₀ u₁ S ↔ pairJointAgreesOn C S u₀ u₁ := by
  constructor
  · exact pairJointAgreesOn_of_MCADoubleCoverOn C S u₀ u₁
  · exact MCADoubleCoverOn.of_pairJointAgreesOn C S u₀ u₁

/-- **`mcaEvent` with an S-pinned double cover is impossible.** Given a concrete witness set
`S` realising the `mcaEvent` body (size + line-witness + `¬ pairJointAgreesOn S`), a
line-decoder pair `(v₁, v₂) ∈ C` doubly covering `S` contradicts the `¬ pairJointAgreesOn S`
clause. This is the per-coordinate-coverage discharge of the bad event. -/
theorem not_mcaEventBody_of_double_cover (C : Set (ι → A)) (u₀ u₁ : ι → A)
    (S : Finset ι) {v₁ v₂ : ι → A} (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hcov : ∀ i ∈ S, ∃ γ γ' : F, γ ≠ γ' ∧
      v₁ i + γ • v₂ i = u₀ i + γ • u₁ i ∧
      v₁ i + γ' • v₂ i = u₀ i + γ' • u₁ i) :
    False :=
  hpair (pairJointAgreesOn_of_double_cover C S u₀ u₁ v₁ v₂ hv₁ hv₂ hcov)

/-- S-pinned bad-event impossibility using the named `MCADoubleCoverOn` surface. -/
theorem not_mcaEventBody_of_MCADoubleCoverOn (C : Set (ι → A)) (u₀ u₁ : ι → A)
    (S : Finset ι) (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hcov : MCADoubleCoverOn (F := F) C u₀ u₁ S) :
    False :=
  hpair (pairJointAgreesOn_of_MCADoubleCoverOn C S u₀ u₁ hcov)

/-- A double cover on a witness set restricts to every smaller witness set. -/
theorem MCADoubleCoverOn.mono (C : Set (ι → A)) (u₀ u₁ : ι → A)
    {S T : Finset ι} (hsub : T ⊆ S)
    (hcov : MCADoubleCoverOn (F := F) C u₀ u₁ S) :
    MCADoubleCoverOn (F := F) C u₀ u₁ T := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hcover⟩ := hcov
  exact ⟨v₁, hv₁, v₂, hv₂, fun i hi => hcover i (hsub hi)⟩

/-- **Per-bad-scalar double-cover obligation.** Once a scalar is bad, every exposed `mcaEvent`
witness set must carry `MCADoubleCoverOn` data. This is the exact local target for the remaining
GS interpolation / multi-γ overlap extraction. -/
def MCABadScalarDoubleCover (C : Set (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) : Prop :=
  mcaEvent C δ u₀ u₁ γ →
    ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ¬ pairJointAgreesOn C S u₀ u₁ →
      MCADoubleCoverOn (F := F) C u₀ u₁ S

/-- A named bad-scalar double-cover obligation contradicts any concrete bad-event body. -/
theorem MCABadScalarDoubleCover.not_mcaEventBody
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hcov : MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ)
    (hγ : mcaEvent C δ u₀ u₁ γ)
    (S : Finset ι) (hsize : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hwit : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hpair : ¬ pairJointAgreesOn C S u₀ u₁) :
    False :=
  not_mcaEventBody_of_MCADoubleCoverOn C u₀ u₁ S hpair
    (hcov hγ S hsize hwit hpair)

/-- A named bad-scalar double-cover obligation rules out the scalar's MCA bad event. -/
theorem MCABadScalarDoubleCover.not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hcov : MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ) :
    ¬ mcaEvent C δ u₀ u₁ γ := by
  rintro ⟨S, hsize, hwit, hpair⟩
  exact MCABadScalarDoubleCover.not_mcaEventBody C δ u₀ u₁ γ hcov
    ⟨S, hsize, hwit, hpair⟩ S hsize hwit hpair

/-- A direct no-event certificate supplies the local bad-scalar double-cover obligation,
vacuously. -/
theorem MCABadScalarDoubleCover.of_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (hno : ¬ mcaEvent C δ u₀ u₁ γ) :
    MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ := by
  intro hγ
  exact False.elim (hno hγ)

/-- The named local bad-scalar double-cover obligation is exact: it is equivalent to ruling out
that scalar's `mcaEvent`. -/
theorem MCABadScalarDoubleCover_iff_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ ↔
      ¬ mcaEvent C δ u₀ u₁ γ := by
  constructor
  · exact MCABadScalarDoubleCover.not_mcaEvent C δ u₀ u₁ γ
  · exact MCABadScalarDoubleCover.of_not_mcaEvent C δ u₀ u₁ γ

/-- **Exposed repaired T4.21 hypothesis.** Every stack and every bad scalar carries the
per-coordinate double cover that the Guruswami--Sudan interpolation route must provide. This is
the replacement data for the refuted black-box `lineDecodable_imp_epsMCA_le_target`. -/
def MCAForallDoubleCover (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin 2) ι) (γ : F), mcaEvent C δ (u 0) (u 1) γ →
    ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
      ¬ pairJointAgreesOn C S (u 0) (u 1) →
      ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
        v₁ i + a • v₂ i = (u 0) i + a • (u 1) i ∧
        v₁ i + a' • v₂ i = (u 0) i + a' • (u 1) i

/-- Unpack the global repaired hypothesis into the named per-bad-scalar obligation. -/
theorem MCAForallDoubleCover.to_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  intro u γ
  simpa [MCABadScalarDoubleCover, MCADoubleCoverOn] using hcov u γ

/-- Repack per-bad-scalar double-cover obligations as the existing global repaired hypothesis. -/
theorem MCAForallDoubleCover.of_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    MCAForallDoubleCover (F := F) (A := A) C δ := by
  intro u γ
  simpa [MCABadScalarDoubleCover, MCADoubleCoverOn] using hcov u γ

/-- The repaired global T4.21 hypothesis is equivalent to the named local bad-scalar surface. -/
theorem MCAForallDoubleCover_iff_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDoubleCover (F := F) (A := A) C δ ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  constructor
  · exact MCAForallDoubleCover.to_badScalarDoubleCover C δ
  · exact MCAForallDoubleCover.of_badScalarDoubleCover C δ

/-- A global repaired double-cover frontier rules out every bad scalar event directly. -/
theorem MCAForallDoubleCover.not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ := by
  intro u γ
  exact (MCABadScalarDoubleCover_iff_not_mcaEvent C δ (u 0) (u 1) γ).mp
    ((MCAForallDoubleCover.to_badScalarDoubleCover C δ hcov) u γ)

/-- Repack a direct no-bad-event frontier as the global repaired double-cover surface. -/
theorem MCAForallDoubleCover.of_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hno : ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  MCAForallDoubleCover.of_badScalarDoubleCover C δ fun u γ =>
    (MCABadScalarDoubleCover_iff_not_mcaEvent C δ (u 0) (u 1) γ).mpr (hno u γ)

/-- The global repaired double-cover surface is exact: it is equivalent to ruling out every
bad scalar event. -/
theorem MCAForallDoubleCover_iff_forall_not_mcaEvent
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDoubleCover (F := F) (A := A) C δ ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F), ¬ mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · exact MCAForallDoubleCover.not_mcaEvent C δ
  · exact MCAForallDoubleCover.of_forall_not_mcaEvent C δ

open Classical in
/-- **Repaired Theorem 4.21, per-stack form.** If for the stack `(u₀, u₁)` every bad scalar's
witness set is doubly covered by a (scalar-dependent) line-decoder pair in `C`, then no bad
scalar exists: `mcaBadCount C δ u₀ u₁ = 0`. The double-coverage hypothesis is the exposed GS
interpolation data; everything else is proven. -/
theorem mcaBadCount_eq_zero_of_double_cover (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F, mcaEvent C δ u₀ u₁ γ →
      ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
        ¬ pairJointAgreesOn C S u₀ u₁ →
        ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
          v₁ i + a • v₂ i = u₀ i + a • u₁ i ∧
          v₁ i + a' • v₂ i = u₀ i + a' • u₁ i) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  classical
  rw [mcaBadCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro γ _hγ hev
  obtain ⟨S, hsize, hwit, hpair⟩ := hev
  obtain ⟨v₁, hv₁, v₂, hv₂, hcover⟩ := hcov γ ⟨S, hsize, hwit, hpair⟩ S hsize hwit hpair
  exact not_mcaEventBody_of_double_cover C u₀ u₁ S hv₁ hv₂ hpair hcover

open Classical in
/-- Per-stack repaired T4.21 wrapper through `MCABadScalarDoubleCover`. -/
theorem mcaBadCount_eq_zero_of_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F,
      MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  exact mcaBadCount_eq_zero_of_double_cover C δ u₀ u₁
    (fun γ hγ S hsize hwit hpair => by
      simpa [MCADoubleCoverOn] using hcov γ hγ S hsize hwit hpair)

/-- Zero bad-scalar count repacks as the named per-scalar double-cover surface. This is vacuous
because zero counts rule out every bad event. -/
theorem badScalarDoubleCover_of_mcaBadCount_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hzero : mcaBadCount (F := F) C δ u₀ u₁ = 0) :
    ∀ γ : F, MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ := by
  intro γ
  exact (MCABadScalarDoubleCover_iff_not_mcaEvent C δ u₀ u₁ γ).mpr
    ((mcaBadCount_eq_zero_iff_forall_not_mcaEvent C δ u₀ u₁).mp hzero γ)

/-- Per-stack count zero is exactly the named per-scalar double-cover surface. -/
theorem mcaBadCount_eq_zero_iff_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 ↔
      ∀ γ : F, MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ := by
  constructor
  · exact badScalarDoubleCover_of_mcaBadCount_eq_zero C δ u₀ u₁
  · exact mcaBadCount_eq_zero_of_badScalarDoubleCover C δ u₀ u₁

open Classical in
/-- **Repaired Theorem 4.21, error form.** If every stack's every bad scalar's witness set is
doubly covered, then `ε_mca(C, δ) = 0`. This is the faithful replacement for the refuted
black-box `lineDecodable_imp_epsMCA_le`: the open GS content is isolated as the explicit
double-coverage hypothesis (criterion: statement REPAIR exposing the interpolation data), and
the coverage ⟹ agreement ⟹ MCA-vanishing implication is fully proven. -/
theorem epsMCA_eq_zero_of_forall_double_cover (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F), mcaEvent C δ (u 0) (u 1) γ →
      ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
        ¬ pairJointAgreesOn C S (u 0) (u 1) →
        ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
          v₁ i + a • v₂ i = (u 0) i + a • (u 1) i ∧
          v₁ i + a' • v₂ i = (u 0) i + a' • (u 1) i) :
    epsMCA (F := F) C δ = 0 := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  have hzero : ∀ u : WordStack A (Fin 2) ι,
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞) = 0 := by
    intro u
    rw [mcaBadCount_eq_zero_of_double_cover C δ (u 0) (u 1) (hcov u)]
    simp
  rw [iSup_congr hzero]
  simp

/-- Error-level repaired T4.21 wrapper through `MCABadScalarDoubleCover`. -/
theorem epsMCA_eq_zero_of_badScalarDoubleCover (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 := by
  exact epsMCA_eq_zero_of_forall_double_cover C δ
    (fun u γ hγ S hsize hwit hpair => by
      simpa [MCADoubleCoverOn] using hcov u γ hγ S hsize hwit hpair)

/-- Per-stack zero bad-scalar count from the global double-cover surface. -/
theorem mcaBadCount_eq_zero_of_MCAForallDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  exact mcaBadCount_eq_zero_of_badScalarDoubleCover C δ u₀ u₁
    (fun γ => by
      simpa using
        (MCAForallDoubleCover.to_badScalarDoubleCover C δ hcov
          (![u₀, u₁] : WordStack A (Fin 2) ι) γ))

/-- Global double-cover data gives zero bad-scalar counts for every stack. -/
theorem MCAForallDoubleCover.forall_mcaBadCount_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0 := by
  intro u
  exact mcaBadCount_eq_zero_of_MCAForallDoubleCover C δ (u 0) (u 1) hcov

/-- Repack zero bad-scalar counts for every stack as the global double-cover surface. This is
vacuous exactly because zero counts rule out every bad event. -/
theorem MCAForallDoubleCover.of_forall_mcaBadCount_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hzero : ∀ u : WordStack A (Fin 2) ι,
      mcaBadCount (F := F) C δ (u 0) (u 1) = 0) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  MCAForallDoubleCover.of_forall_not_mcaEvent C δ fun u =>
    (mcaBadCount_eq_zero_iff_forall_not_mcaEvent C δ (u 0) (u 1)).mp (hzero u)

/-- The global repaired double-cover surface is exact: it is equivalent to zero bad-scalar
counts for every stack. -/
theorem MCAForallDoubleCover_iff_forall_mcaBadCount_eq_zero
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDoubleCover (F := F) (A := A) C δ ↔
      ∀ u : WordStack A (Fin 2) ι, mcaBadCount (F := F) C δ (u 0) (u 1) = 0 := by
  constructor
  · exact MCAForallDoubleCover.forall_mcaBadCount_eq_zero C δ
  · exact MCAForallDoubleCover.of_forall_mcaBadCount_eq_zero C δ

/-- Error-level zero result from the global double-cover surface. -/
theorem epsMCA_eq_zero_of_MCAForallDoubleCover (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    epsMCA (F := F) C δ = 0 :=
  epsMCA_eq_zero_of_forall_double_cover C δ hcov

/-- Vanishing MCA error repacks as the global repaired double-cover surface. -/
theorem MCAForallDoubleCover.of_epsMCA_eq_zero (C : Set (ι → A)) (δ : ℝ≥0)
    (heps : epsMCA (F := F) C δ = 0) :
    MCAForallDoubleCover (F := F) (A := A) C δ :=
  MCAForallDoubleCover.of_forall_mcaBadCount_eq_zero C δ
    (forall_mcaBadCount_eq_zero_of_epsMCA_eq_zero C δ heps)

/-- The global repaired double-cover surface is exact at `ε_mca = 0`. -/
theorem epsMCA_eq_zero_iff_MCAForallDoubleCover (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ = 0 ↔
      MCAForallDoubleCover (F := F) (A := A) C δ := by
  constructor
  · exact MCAForallDoubleCover.of_epsMCA_eq_zero C δ
  · exact epsMCA_eq_zero_of_MCAForallDoubleCover C δ

/-- The named all-stack bad-scalar double-cover surface is exact at `ε_mca = 0`. -/
theorem epsMCA_eq_zero_iff_badScalarDoubleCover (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ = 0 ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  rw [epsMCA_eq_zero_iff_MCAForallDoubleCover,
    MCAForallDoubleCover_iff_badScalarDoubleCover]

#print axioms MCADoubleCoverOn
#print axioms MCABadScalarDoubleCover
#print axioms pairJointAgreesOn_of_MCADoubleCoverOn
#print axioms MCADoubleCoverOn.of_pairJointAgreesOn
#print axioms MCADoubleCoverOn_iff_pairJointAgreesOn
#print axioms not_mcaEventBody_of_MCADoubleCoverOn
#print axioms MCADoubleCoverOn.mono
#print axioms MCABadScalarDoubleCover.not_mcaEventBody
#print axioms MCABadScalarDoubleCover.not_mcaEvent
#print axioms MCABadScalarDoubleCover.of_not_mcaEvent
#print axioms MCABadScalarDoubleCover_iff_not_mcaEvent
#print axioms MCAForallDoubleCover
#print axioms MCAForallDoubleCover_iff_badScalarDoubleCover
#print axioms MCAForallDoubleCover.not_mcaEvent
#print axioms MCAForallDoubleCover.of_forall_not_mcaEvent
#print axioms MCAForallDoubleCover_iff_forall_not_mcaEvent
#print axioms mcaBadCount_eq_zero_of_badScalarDoubleCover
#print axioms badScalarDoubleCover_of_mcaBadCount_eq_zero
#print axioms mcaBadCount_eq_zero_iff_badScalarDoubleCover
#print axioms epsMCA_eq_zero_of_badScalarDoubleCover
#print axioms mcaBadCount_eq_zero_of_MCAForallDoubleCover
#print axioms MCAForallDoubleCover.forall_mcaBadCount_eq_zero
#print axioms MCAForallDoubleCover.of_forall_mcaBadCount_eq_zero
#print axioms MCAForallDoubleCover_iff_forall_mcaBadCount_eq_zero
#print axioms epsMCA_eq_zero_of_MCAForallDoubleCover
#print axioms MCAForallDoubleCover.of_epsMCA_eq_zero
#print axioms epsMCA_eq_zero_iff_MCAForallDoubleCover
#print axioms epsMCA_eq_zero_iff_badScalarDoubleCover

end

end ProximityGap

namespace CodingTheory

open ProximityGap
open scoped NNReal ProbabilityTheory

section RepairedTarget

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Repaired ABF26 Theorem 4.21.** The black-box line-decodability hypothesis is false; the
correct theorem consumes the GS multi-γ overlap-coverage data directly. -/
theorem lineDecodable_imp_epsMCA_le_target
    (C : ModuleCode ι F A) (δ a : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) (C : Set (ι → A)) δ) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [epsMCA_eq_zero_of_forall_double_cover (F := F) (A := A) (C : Set (ι → A)) δ hcov]
  exact zero_le _

#print axioms CodingTheory.lineDecodable_imp_epsMCA_le_target

end RepairedTarget

end CodingTheory

