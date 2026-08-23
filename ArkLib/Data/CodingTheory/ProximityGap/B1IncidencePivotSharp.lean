/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.B1IncidenceInjectionBridge

/-!
# The SHARP common-pivot incidence bound: distinct pivot-VALUE count, not listing size (#444)

`B1IncidenceInjectionBridge.lean` discharges the open object
`WorstCaseFarIncidenceBounded` on the *common-pivot* sub-case via the injection
`γ ↦ (witness codeword value at the pivot i₀)`.  Its sharp intermediate lemma

  `farIncidence_le_pivotValueCount :
     farIncidence C δ u₀ u₁ ≤ (Cv.image (fun c => c i₀)).card`

bounds the far-line incidence by the number of **distinct pivot VALUES**.  But its
downstream consumer `worstCaseFarIncidenceBounded_of_commonPivot` immediately
*discards* this sharpness, going through `Finset.card_image_le` to the **listing
size** `Cv.card` and requiring `Cv.card ≤ B`.  That is wasteful: the listing `Cv` can
be arbitrarily large (many codewords, few distinct values at one coordinate), while the
distinct pivot-value count is bounded by the **alphabet** `Fintype.card A`.

This file threads the sharp intermediate all the way to the open object, giving a
**strictly stronger** discharge of the common-pivot sub-case, plus the unconditional
alphabet ceiling that the listing-size form cannot supply.

## What is proved (all axiom-clean `{propext, Classical.choice, Quot.sound}`)

* `worstCaseFarIncidenceBounded_of_commonPivot_sharp` — the open obligation
  `WorstCaseFarIncidenceBounded C δ B` holds whenever every far stack admits a common
  pivot whose **distinct pivot-value count** `(Cv.image (· i₀)).card ≤ B`.  The
  hypothesis is **weaker** than the listing-size form `Cv.card ≤ B`
  (since `(Cv.image f).card ≤ Cv.card` always), so this theorem **subsumes**
  `worstCaseFarIncidenceBounded_of_commonPivot`.

* `commonPivot_sharp_le_listing` — the sharp hypothesis is implied by the old one:
  the distinct-value count never exceeds the listing size, so any `B` that works for the
  listing-size form also works for the sharp form (the formal subsumption witness).

* `farIncidence_le_card_alphabet` — UNCONDITIONAL alphabet ceiling: under a common
  pivot (with the cover), the far-line incidence is at most `Fintype.card A`, because the
  pivot values live in `A`.  No listing-size hypothesis at all.

* `worstCaseFarIncidenceBounded_alphabet` — consequently the open object holds with
  `B = Fintype.card A` on the entire common-pivot sub-case, with NO per-stack
  cardinality side-condition.  This is the cleanest possible discharge: the incidence is
  capped by the alphabet whenever a common pivot exists.

## Honest scope (what this does NOT do)

It does **not** prove a common pivot always exists (the file header of
`B1IncidenceInjectionBridge.lean` exhibits the explicit `9,13,89 / 8,12,16` separation
showing it can fail) — so the **prize core** `WorstCaseFarIncidenceBounded` in *full*
generality is UNTOUCHED.  It also makes no moment/energy/census/orbit claim, no
beyond-Johnson / capacity / growth-law claim, and leaves the cliff-at-`n/2` untouched.
It is a strict SHARPENING of an already-proven incidence-geometry sub-case discharge,
on a NON-MOMENT structural (pencil/incidence) lever, extending proven theorems.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.IncidenceInjection

open ProximityGap.FarCosetExplosion
open ProximityGap.WireB1ToIncidence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

set_option linter.unusedSectionVars false in
/-- **The distinct-value count never exceeds the listing size.**  This is the formal
witness that the sharp hypothesis below is *weaker* than the listing-size hypothesis of
`worstCaseFarIncidenceBounded_of_commonPivot`, i.e. the sharp discharge SUBSUMES the old
one. -/
theorem commonPivot_sharp_le_listing
    (Cv : Finset (ι → A)) (i₀ : ι) :
    (Cv.image (fun c => c i₀)).card ≤ Cv.card :=
  Finset.card_image_le

/-- **The SHARP common-pivot discharge of the open object.**  If, at radius `δ`, *every*
far stack with a far direction admits a common pivot coordinate `i₀` and a finite cover
`Cv ⊆ C` whose **distinct pivot-value count** `(Cv.image (· i₀)).card ≤ B`, then
`WorstCaseFarIncidenceBounded C δ B` holds.

This strictly strengthens `worstCaseFarIncidenceBounded_of_commonPivot`: its gate
requires only the *distinct value* count `≤ B`, which is `≤ Cv.card`
(`commonPivot_sharp_le_listing`), so every instance of the old gate is an instance of
this one.  It threads the sharp `farIncidence_le_pivotValueCount` (the injection
`γ ↦ pivot value`) directly, never losing to the listing size. -/
theorem worstCaseFarIncidenceBounded_of_commonPivot_sharp
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hgate : ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ →
      ∃ (i₀ : ι) (Cv : Finset (ι → A)),
        (∀ c ∈ Cv, c ∈ C) ∧ CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀ ∧
        (∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
          ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
        (Cv.image (fun c => c i₀)).card ≤ B) :
    WorstCaseFarIncidenceBounded (F := F) C δ B := by
  intro u₀ u₁ hfar
  obtain ⟨i₀, Cv, hCv, hpiv, hcover, hValCard⟩ := hgate u₀ u₁ hfar
  exact le_trans (farIncidence_le_pivotValueCount C δ u₀ u₁ i₀ hpiv Cv hCv hcover) hValCard

/-- **The UNCONDITIONAL alphabet ceiling on the far-line incidence.**  Under a common
pivot (with cover), the far-line incidence is at most the alphabet size `Fintype.card A`,
because every pivot value `u₀ i₀ + γ • u₁ i₀` lies in `A`, so the distinct pivot-value
count is `≤ Fintype.card A`.  No listing-size hypothesis whatsoever. -/
theorem farIncidence_le_card_alphabet
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (i₀ : ι)
    (hpiv : CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀)
    (Cv : Finset (ι → A)) (hCv : ∀ c ∈ Cv, c ∈ C)
    (hcover : ∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    farIncidence (F := F) C δ u₀ u₁ ≤ Fintype.card A := by
  refine le_trans
    (farIncidence_le_pivotValueCount C δ u₀ u₁ i₀ hpiv Cv hCv hcover) ?_
  -- distinct pivot values form a subset of `A`, so their count is `≤ #A`.
  exact le_trans (Finset.card_le_univ _) (le_of_eq rfl)

/-- **The open object holds with `B = Fintype.card A` on the whole common-pivot
sub-case.**  No per-stack cardinality side-condition: as soon as every far stack admits a
common pivot (with cover), the far-line incidence is capped by the alphabet.  This is the
cleanest discharge of `WorstCaseFarIncidenceBounded` available on the common-pivot face. -/
theorem worstCaseFarIncidenceBounded_alphabet
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hgate : ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ →
      ∃ (i₀ : ι) (Cv : Finset (ι → A)),
        (∀ c ∈ Cv, c ∈ C) ∧ CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀ ∧
        (∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
          ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)) :
    WorstCaseFarIncidenceBounded (F := F) C δ (Fintype.card A) := by
  intro u₀ u₁ hfar
  obtain ⟨i₀, Cv, hCv, hpiv, hcover⟩ := hgate u₀ u₁ hfar
  exact farIncidence_le_card_alphabet C δ u₀ u₁ i₀ hpiv Cv hCv hcover

/-- **THE CONSTRAINT (the lever's reach, contrapositive).**  If the worst-case far-line
incidence STRICTLY EXCEEDS the available pivot-value count `(Cv.image (· i₀)).card`, then
**no common pivot at `i₀` with cover `Cv` exists** for that stack.  This delineates exactly
where the common-pivot discharge can and cannot reach: it is INAPPLICABLE precisely at the
worst-case incidence binder.

Concretely, `B1IncidenceBridge.lean`'s own `probe_farline_incidence_exact` enumeration
(p-independent) records the worst-case far-incidence binders `9, 13, 89` at `n = 8, 12, 16`,
which EXCEED the readout value-count `n` (`8, 12, 16`) — and those binders occur at
agreement-set size past Johnson and direction `b = k` (not the top `b = n-1`).  So whenever
the pivot values are confined to a set of size `≤ n` (e.g. the top-direction readout, whose
values lie in `μ_n`), this constraint shows the common pivot **provably fails at the binder**:
the injection `γ ↦ pivot value` cannot be onto more than `n` values, but the binder needs
`9 > 8`, `13 > 12`, `89 > 16` distinct bad `γ`.  The common-pivot discharge therefore covers
only the sub-binder (sub-Johnson) face; the prize `δ*` binder lives strictly outside it. -/
theorem no_commonPivot_of_incidence_gt_pivotValueCount
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (i₀ : ι)
    (Cv : Finset (ι → A)) (hCv : ∀ c ∈ Cv, c ∈ C)
    (hcover : CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀ →
      ∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
        ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hgt : (Cv.image (fun c => c i₀)).card < farIncidence (F := F) C δ u₀ u₁) :
    ¬ CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀ := by
  intro hpiv
  have hle := farIncidence_le_pivotValueCount C δ u₀ u₁ i₀ hpiv Cv hCv (hcover hpiv)
  exact absurd (lt_of_lt_of_le hgt hle) (lt_irrefl _)

end ProximityGap.IncidenceInjection

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.commonPivot_sharp_le_listing
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.worstCaseFarIncidenceBounded_of_commonPivot_sharp
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.farIncidence_le_card_alphabet
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.worstCaseFarIncidenceBounded_alphabet
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.no_commonPivot_of_incidence_gt_pivotValueCount
