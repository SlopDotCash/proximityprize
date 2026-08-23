/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumOmegaConcentration

/-!
# Round 8 (Issue #232, ABF26) — the QUARTIC DESCENT: the surviving coordinate of the order-4
# `⟨ω⟩`-closure is a subset-sum count one level down.

`SubsetSumOmegaConcentration` (order-4 `⟨ω⟩`-closure, `ω² = −1`) concentrates **both** `∑x` and `∑x²`
at `0` for every `omega4Closure ω P`, leaving the surviving symmetric coordinate `∑x⁴`. For the
closure of a transversal subset, `∑_{x ∈ omega4Closure ω P} x⁴ = 4·∑_{g∈P} g⁴` (each `⟨ω⟩`-orbit
`{g, ωg, ω²g, ω³g}` contributes `g⁴·(1+ω⁴+ω⁸+ω¹²) = 4g⁴` since `ω⁴ = 1`). This file resolves that
surviving coordinate exactly as `SubsetSumSquaringBijection` did for the `±` (order-2) case.

## The key new fact: the 4th-power map is injective on an `OmegaFree` transversal

`g ↦ g⁴` is **injective on `T`** when `OmegaFree ω T` (`pow4_injOn_of_omegaFree`). The factorisation
`a⁴ − b⁴ = (a−b)(a+b)(a−ωb)(a+ωb)` (using `ω² = −1`) shows `a⁴ = b⁴` forces `a = ω^i b` for some
`i ∈ {0,1,2,3}`; each non-trivial `i` puts `a ∈ T ∩ ωⁱT`, contradicting the free-action hypothesis.
(The 4th roots of unity are exactly `⟨ω⟩ = {1, ω, ω², ω³}`.)

## Consequence — the descent (`psum4_count_eq_subsetSumCount_pow4Set`)

Because `g ↦ g⁴` is injective on `T`, the map `P ↦ P.image (·⁴)` is a bijection between the
`s`-subsets of `T` with `∑_{g∈P} g⁴ = c` and the `s`-subsets of the 4th-power ground set
`T.image (·⁴)` with `∑_{y∈P'} y = c`. Hence the two counts are equal: the surviving order-4
coordinate fiber count is literally a first-coordinate subset-sum count over the 4th-power image
`{g⁴ : g ∈ T}`, one level down (for a smooth `2^k`-subgroup transversal, `{g⁴}` is the index-4
subgroup — the order-4 step of the self-similar descent down the `2`-power tower).

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). This is the order-4 analogue
of `SubsetSumSquaringBijection` (order-2). It does **NOT** resolve whether the subset-sum count
concentrates — the prize core (`δ*`) stays open; the descent only exhibits the self-similarity.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round8QuarticDescent

open ArkLib.CodingTheory.Round8OmegaConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The 4th-power map is injective on an `OmegaFree` transversal. -/

/-- **`g ↦ g⁴` is injective on an `OmegaFree` transversal `T`** (`ω² = −1`). From
`a⁴ = b⁴` the factorisation `(a−b)(a+b)(a−ωb)(a+ωb) = 0` gives `a = ω^i b` for some `i`; the three
non-trivial cases each force `a ∈ T ∩ ωⁱT`, contradicting `OmegaFree`. -/
theorem pow4_injOn_of_omegaFree {ω : F} {T : Finset F}
    (hω2 : ω ^ 2 = -1) (hfree : OmegaFree ω T) :
    Set.InjOn (fun g => g ^ 4) (↑T : Set F) := by
  obtain ⟨d01, d02, d03, _, _, _⟩ := hfree
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  have hab4 : a ^ 4 = b ^ 4 := hab
  have hfac : (a - b) * (a + b) * (a - ω * b) * (a + ω * b) = 0 := by
    have hx : (a - b) * (a + b) * (a - ω * b) * (a + ω * b) = a ^ 4 - b ^ 4 := by
      linear_combination (b ^ 2 * (b ^ 2 - a ^ 2)) * hω2
    rw [hx, hab4, sub_self]
  rcases mul_eq_zero.mp hfac with h123 | h4
  · rcases mul_eq_zero.mp h123 with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · -- `a - b = 0`
        linear_combination h1
      · -- `a + b = 0` ⟹ `a = ω²·b` ⟹ `a ∈ T ∩ ω²T`
        exfalso
        have ha2 : a = ω ^ 2 * b := by linear_combination h2 - b * hω2
        exact (Finset.disjoint_left.mp d02 ha) (Finset.mem_image.mpr ⟨b, hb, ha2.symm⟩)
    · -- `a - ω·b = 0` ⟹ `a = ω·b` ⟹ `a ∈ T ∩ ωT`
      exfalso
      have ha1 : a = ω * b := by linear_combination h3
      exact (Finset.disjoint_left.mp d01 ha) (Finset.mem_image.mpr ⟨b, hb, ha1.symm⟩)
  · -- `a + ω·b = 0` ⟹ `a = ω³·b` ⟹ `a ∈ T ∩ ω³T`
    exfalso
    have ha3 : a = ω ^ 3 * b := by linear_combination h4 - ω * b * hω2
    exact (Finset.disjoint_left.mp d03 ha) (Finset.mem_image.mpr ⟨b, hb, ha3.symm⟩)

/-- The 4th-power map is injective on any subset `P ⊆ T` of an `OmegaFree` transversal. -/
theorem pow4_injOn_subset {ω : F} {T : Finset F}
    (hω2 : ω ^ 2 = -1) (hfree : OmegaFree ω T) {P : Finset F} (hP : P ⊆ T) :
    Set.InjOn (fun g => g ^ 4) (↑P : Set F) :=
  (pow4_injOn_of_omegaFree hω2 hfree).mono (by exact_mod_cast hP)

/-! ## 2. The descent: the `∑x⁴` fiber count equals a subset-sum count over `{g⁴ : g ∈ T}`. -/

/-- **The surviving order-4 coordinate fiber count is a subset-sum count one level down.**
For an `OmegaFree` transversal `T` (`ω² = −1`), `P ↦ P.image (·⁴)` is a bijection between the
`s`-subsets of `T` with `∑_{g∈P} g⁴ = c` and the `s`-subsets of `T.image (·⁴)` with `∑_{y∈P'} y = c`.
Hence the two counts are equal. -/
theorem psum4_count_eq_subsetSumCount_pow4Set {ω : F} {T : Finset F}
    (hω2 : ω ^ 2 = -1) (hfree : OmegaFree ω T) (s : ℕ) (c : F) :
    ((T.powersetCard s).filter (fun P => (∑ g ∈ P, g ^ 4) = c)).card =
      (((T.image (fun g => g ^ 4)).powersetCard s).filter (fun P' => (∑ y ∈ P', y) = c)).card := by
  classical
  apply Finset.card_nbij' (fun P => P.image (fun g => g ^ 4))
    (fun P' => T.filter (fun g => g ^ 4 ∈ P'))
  · -- forward maps in
    intro P hP
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hP
    obtain ⟨⟨hPsub, hPcard⟩, hPsum⟩ := hP
    have hinjP : Set.InjOn (fun g => g ^ 4) (↑P : Set F) := pow4_injOn_subset hω2 hfree hPsub
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.image_subset_image hPsub, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injOn hinjP, hPcard]
    · rw [Finset.sum_image (fun x hx y hy h =>
        hinjP (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)]
      exact hPsum
  · -- backward maps in
    intro P' hP'
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hP'
    obtain ⟨⟨hP'sub, hP'card⟩, hP'sum⟩ := hP'
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    have himg : (T.filter (fun g => g ^ 4 ∈ P')).image (fun g => g ^ 4) = P' := by
      apply Finset.Subset.antisymm
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨g, hg, rfl⟩ := hy
        exact (Finset.mem_filter.mp hg).2
      · intro y hy
        have hyT := hP'sub hy
        rw [Finset.mem_image] at hyT
        obtain ⟨g, hg, rfl⟩ := hyT
        rw [Finset.mem_image]
        exact ⟨g, Finset.mem_filter.mpr ⟨hg, hy⟩, rfl⟩
    have hinjPre : Set.InjOn (fun g => g ^ 4)
        (↑(T.filter (fun g => g ^ 4 ∈ P')) : Set F) :=
      pow4_injOn_subset hω2 hfree (Finset.filter_subset _ _)
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · have hcard : (T.filter (fun g => g ^ 4 ∈ P')).card = P'.card := by
        rw [← Finset.card_image_of_injOn hinjPre, himg]
      rw [hcard]; exact hP'card
    · have hsi : (∑ y ∈ (T.filter (fun g => g ^ 4 ∈ P')).image (fun g => g ^ 4), y) =
          ∑ g ∈ T.filter (fun g => g ^ 4 ∈ P'), g ^ 4 :=
        Finset.sum_image (fun x hx y hy h =>
          hinjPre (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)
      have hsum : (∑ g ∈ T.filter (fun g => g ^ 4 ∈ P'), g ^ 4) = ∑ y ∈ P', y := by
        rw [← hsi, himg]
      rw [hsum]; exact hP'sum
  · -- left inverse
    intro P hP
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hP
    obtain ⟨⟨hPsub, _⟩, _⟩ := hP
    apply Finset.Subset.antisymm
    · intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨hgT, hgimg⟩ := hg
      rw [Finset.mem_image] at hgimg
      obtain ⟨p, hp, hpe⟩ := hgimg
      have : g = p := pow4_injOn_of_omegaFree hω2 hfree
        (Finset.mem_coe.mpr hgT) (Finset.mem_coe.mpr (hPsub hp)) hpe.symm
      rwa [this]
    · intro p hp
      rw [Finset.mem_filter]
      exact ⟨hPsub hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  · -- right inverse
    intro P' hP'
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hP'
    obtain ⟨⟨hP'sub, _⟩, _⟩ := hP'
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact (Finset.mem_filter.mp hg).2
    · intro y hy
      have hy' := hP'sub hy
      rw [Finset.mem_image] at hy'
      obtain ⟨g, hg, rfl⟩ := hy'
      rw [Finset.mem_image]
      exact ⟨g, Finset.mem_filter.mpr ⟨hg, hy⟩, rfl⟩

end ArkLib.CodingTheory.Round8QuarticDescent

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round8QuarticDescent.pow4_injOn_of_omegaFree
#print axioms ArkLib.CodingTheory.Round8QuarticDescent.psum4_count_eq_subsetSumCount_pow4Set
