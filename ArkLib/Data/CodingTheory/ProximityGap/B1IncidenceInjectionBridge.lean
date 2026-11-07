/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.CodingTheory.ProximityGap.B1IncidenceBridge

/-!
# The far-line incidence ↦ value-count injection bridge (#407)

This file attacks **the open object** of `B1IncidenceBridge.lean`:
`worstCaseIncidence_is_the_open_object` — the missing step
"value-count ⟹ far-line incidence ≤ f(value-count)".

The header of `B1IncidenceBridge.lean` is explicit that, *in full generality*, the value
count `= n` does NOT bound the worst-case far-line incidence (the numeric witnesses
`9, 13, 89` vs `8, 12, 16` separate them). The generality-killer is that different bad
scalars `γ` can be explained by witness agreement sets `S` that need not share a common
coordinate — so there is no single point at which `γ` is uniquely recoverable.

**What this file proves, axiom-clean, is the SHARP sub-case where the bridge IS provable:**
when there is a *fixed* coordinate `i₀` with `u₁ i₀ ≠ 0` that lies in **every** bad witness
agreement set, the map

  `γ  ↦  (witness codeword value at `i₀`)  =  u₀ i₀ + γ • u₁ i₀`

is **injective on bad scalars** (over a field, `(γ - γ') • a = 0 ∧ a ≠ 0 ⟹ γ = γ'`), so the
far-line incidence is bounded by the number of distinct codeword values at `i₀`:

  `farIncidence C δ u₀ u₁  ≤  #{ c i₀ : c ∈ C }`.

This is precisely the "agreement set forces `γ` uniquely per value = an injection `γ ↦ value`"
sub-case requested. It is a *positive* counterpart to the `B1IncidenceBridge.lean` header's
negative fact: a common pivot coordinate is **sufficient** for the incidence to be bounded by
the value count at that pivot. It is **not necessary**: over `F₅`, with the constant code on
coordinates `{0,1,2}`, `u₀ i = i²`, `u₁ i = i` and `δ = 1/3`, the three close scalars
`−1, −2, −3` are witnessed (uniquely) by the pairs `{0,1}`, `{0,2}`, `{1,2}`, which share no
coordinate, yet the incidence is `3 ≤ 5` = the codeword value count at every coordinate (and
`u₁` is `δ`-far from the constant code). So the theorems below prove only the implication
"common pivot ⟹ incidence ≤ value count", not an equivalence. The B1 readout value-count
`= n` then plugs in directly (the top-direction coordinate), reducing the open object, on the
common-pivot sub-case, to the explicit geometric `Prop` `CommonPivotCoordinate` named below.

Nothing here is conditional on an unproved lemma: the injection and the card bound are
unconditional consequences of the common-pivot hypothesis (together with the covering
hypothesis `hcover`), which are fully explicit `Prop`s. Note that the proof of the injection
uses only `u₁ i₀ ≠ 0` from `CommonPivotCoordinate` and the pivot-containing witnesses supplied
by `hcover`; the existential half of `CommonPivotCoordinate` and the hypothesis `hCv` are not
used by the proof (interface simplification tracked under audit finding PG-008).
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.IncidenceInjection

open ProximityGap.FarCosetExplosion
open ProximityGap.WireB1ToIncidence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **A sufficient (not necessary) geometric hypothesis.**  There is a *fixed*
coordinate `i₀` with `u₁ i₀ ≠ 0` such that every bad scalar admits *some* witness agreement
set containing `i₀`.  This is a structural condition under which `γ` is uniquely
recoverable from the witness codeword value at `i₀`, which suffices to turn the value count
at `i₀` into an incidence bound.  It is not necessary for such a bound: the module docstring
gives an `F₅` example with no common pivot in which the incidence (`3`) is still at most the
value count (`5`).  (The `9, 13, 89` vs `8, 12, 16` witnesses of `B1IncidenceBridge.lean`
show only that the value count does not bound the incidence in full generality.) -/
def CommonPivotCoordinate (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (i₀ : ι) : Prop :=
  u₁ i₀ ≠ 0 ∧
    ∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i

open Classical in
/-- **THE INJECTION (the heart of the bridge).**  Under `CommonPivotCoordinate`, the bad-scalar
filter injects into the codeword *value set at `i₀`*, `{ c i₀ : c ∈ C }`, via
`γ ↦ u₀ i₀ + γ • u₁ i₀` (the witness codeword's value at `i₀`).  Injectivity is the field
cancellation `(γ - γ') • u₁ i₀ = 0 ∧ u₁ i₀ ≠ 0 ⟹ γ = γ'`.

Consequently the far-line incidence is bounded by the value-count at the pivot:

  `farIncidence C δ u₀ u₁ ≤ #{ c i₀ : c ∈ C }`.

This is the requested injection lemma: `γ ↦ value` is injective on bad scalars, so
`incidence ≤ value-count`. -/
theorem farIncidence_le_pivotValueCount
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (i₀ : ι)
    (hpiv : CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀)
    (Cv : Finset (ι → A)) (hCv : ∀ c ∈ Cv, c ∈ C)
    (hcover : ∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    farIncidence (F := F) C δ u₀ u₁ ≤ (Cv.image (fun c => c i₀)).card := by
  obtain ⟨hu₁, _⟩ := hpiv
  classical
  -- The bad-scalar filter.
  set badF : Finset F := Finset.univ.filter (fun γ : F =>
      ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) with hbadF
  show badF.card ≤ (Cv.image (fun c => c i₀)).card
  -- Map each bad `γ` to the value `u₀ i₀ + γ • u₁ i₀` (the pivot value).
  refine Finset.card_le_card_of_injOn (fun γ => u₀ i₀ + γ • u₁ i₀) ?_ ?_
  · -- The image lands in the codeword value set at `i₀`.
    intro γ hγ
    rw [Finset.mem_coe, hbadF, Finset.mem_filter] at hγ
    obtain ⟨S, hSsz, w, hwC, hwS⟩ := hγ.2
    obtain ⟨S', hi₀S', _, w', hw'Cv, hw'S'⟩ := hcover γ ⟨S, hSsz, w, hwC, hwS⟩
    -- `w' i₀ = u₀ i₀ + γ • u₁ i₀`, and `w' ∈ Cv`.
    have hval : w' i₀ = u₀ i₀ + γ • u₁ i₀ := hw'S' i₀ hi₀S'
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨w', hw'Cv, hval⟩
  · -- Injectivity: the pivot map is affine-injective in `γ` since `u₁ i₀ ≠ 0`.
    intro γ₁ _ γ₂ _ heq
    have : γ₁ • u₁ i₀ = γ₂ • u₁ i₀ := by
      have := heq
      simpa using add_left_cancel this
    have hsub : (γ₁ - γ₂) • u₁ i₀ = 0 := by rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hu₁

open Classical in
/-- **THE BRIDGE, as a clean `Prop` on the field's value-count.**  Under
`CommonPivotCoordinate` with a finite codeword listing `Cv ⊆ C` covering all bad witnesses,
the far-line incidence is at most the value-count at the pivot — and in particular at most the
size of the listing `Cv`.  This is a positive (sufficient-condition) form of the open object:
incidence is bounded by a *value count* whenever a common pivot exists.  It does not claim the
bound fails without a common pivot; it can hold without one (see the module docstring). -/
theorem farIncidence_le_listing_card
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (i₀ : ι)
    (hpiv : CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀)
    (Cv : Finset (ι → A)) (hCv : ∀ c ∈ Cv, c ∈ C)
    (hcover : ∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    farIncidence (F := F) C δ u₀ u₁ ≤ Cv.card :=
  le_trans (farIncidence_le_pivotValueCount C δ u₀ u₁ i₀ hpiv Cv hCv hcover)
    (Finset.card_image_le)

open Classical in
/-- **The discharged sub-case of the open object.**  If, at radius `δ`, *every* far stack with
a far direction admits a common pivot coordinate whose codeword value-count at the pivot is
`≤ B`, then `WorstCaseFarIncidenceBounded C δ B` holds — the open obligation of
`B1IncidenceBridge.lean` is discharged on this sub-case.  This is the genuine
"value-count ⟹ incidence ≤ value-count" step, valid wherever a common pivot exists. -/
theorem worstCaseFarIncidenceBounded_of_commonPivot
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hgate : ∀ u₀ u₁ : ι → A, FarFromCode C δ u₁ →
      ∃ (i₀ : ι) (Cv : Finset (ι → A)),
        (∀ c ∈ Cv, c ∈ C) ∧ CommonPivotCoordinate (F := F) C δ u₀ u₁ i₀ ∧
        (∀ γ : F, (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
          ∃ S : Finset ι, i₀ ∈ S ∧ (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∃ w ∈ Cv, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
        Cv.card ≤ B) :
    WorstCaseFarIncidenceBounded (F := F) C δ B := by
  intro u₀ u₁ hfar
  obtain ⟨i₀, Cv, hCv, hpiv, hcover, hBcard⟩ := hgate u₀ u₁ hfar
  exact le_trans (farIncidence_le_listing_card C δ u₀ u₁ i₀ hpiv Cv hCv hcover) hBcard

end ProximityGap.IncidenceInjection

set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.farIncidence_le_pivotValueCount
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.farIncidence_le_listing_card
set_option linter.style.longLine false in
#print axioms ProximityGap.IncidenceInjection.worstCaseFarIncidenceBounded_of_commonPivot
