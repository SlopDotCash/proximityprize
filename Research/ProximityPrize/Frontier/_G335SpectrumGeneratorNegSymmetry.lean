/-
Copyright (c) 2026 Nathan Fox (nathanjfoxwork-bot). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Nathan Fox (nathanjfoxwork-bot)
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G335: the spectrum value set is invariant under `g ↦ -g`

Every negative spectrum result in the G331–G334 lane (PRs #292 / #319 / #321) is a
statement about **one** generator `g` at a given rung.  The census question ("does the
rung attain the law `∑ 2^a C(h,a)`?") is about **every** primitive `2h`-th root, so none
of those theorems answers it alone.  This file lands the first half of that gap: the
spectrum **value set** is invariant under the unit action `g ↦ -g = g^(h+1)`, and
injectivity of `spectrumVal` transfers across that action.

## Mechanism

Write a signed datum as a coefficient function on `range h`.  For `a = h + 1` the unit
`a ∈ (ZMod (2h))^*` acts as the identity on indices and as `(-1)^i` on coefficients, so
`(-g)^i = (-1)^i g^i` flips exactly the odd powers.  The involution `flipT` on the
positive part of a datum realises that sign flip, and the signed-sum identity
`sVal (-g) ⟨U, T⟩ = sVal g ⟨U, flipT U T⟩` follows by a pure ring calculation.  Extending
to spectrum data and taking images gives set equality of the two value sets; injectivity
transfers because `flipE` is an involution of the data set.

## Named prize claim advanced

`ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(`ArkLib/Data/CodingTheory/ProximityGap/TwoPowerSubsetSumSpectrum.lean`).  Its hypothesis
`hinj : Set.InjOn (spectrumVal g) (spectrumData h A)` becomes a property of the rung
`(p, h, A)`, not of a particular generator: once `hinj` fails (or holds) at one `g`, the
same statement is true at `-g`.  Combined with G331–G334 this upgrades each single-`g`
caveat to a two-generator (and, after the remaining odd-`a` cases, a full-rung) claim.

Honest scope:
* Lands the `a = h + 1` instance of the general statement "the value set is invariant
  under `g ↦ g^a` for every unit `a` of `ZMod (2h)`".  The remaining odd-`a` cases (true
  index permutation) are a separate brick; they are **not** claimed here.
* Does **not** contradict any in-tree theorem.  Does not pin δ\*, does not give a
  field-uniform census, and does not replace G331–G334 (those still supply the concrete
  collision witnesses).
* Distinct from open PRs #292 / #319 / #321: those are per-`(p, g)` caveats; this file is
  the generator-symmetry transfer that turns any one of them into a rung property.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G335SpectrumGeneratorNegSymmetry

open ArkLib.ProximityGap.KKH26

/-- The signed coefficient of a signed datum `(U, T)`: `+1` on `T`, `-1` on `U \ T`, `0`
off the support `U`.  (Same object as `G330SpectrumExactBoundary.sigCoeff`, restated
locally so this file does not depend on the G330 Frontier module.) -/
def lcoeff (d : (_ : Finset ℕ) × Finset ℕ) (i : ℕ) : ℤ :=
  (if i ∈ d.2 then 1 else 0) - (if i ∈ d.1 \ d.2 then 1 else 0)

/-- **`sVal` as a coefficient sum.**  On the window `range h` the signed sum is the
coefficient sum `∑ cᵢ gⁱ` with `cᵢ = lcoeff`. -/
lemma sVal_eq_sum_coeff {F : Type*} [CommRing F] (g : F) {h : ℕ} {U T : Finset ℕ}
    (hU : U ⊆ range h) (hT : T ⊆ U) :
    sVal g ⟨U, T⟩ = ∑ i ∈ range h, ((lcoeff ⟨U, T⟩ i : ℤ) : F) * g ^ i := by
  have hTr : T ⊆ range h := hT.trans hU
  have hDr : U \ T ⊆ range h := Finset.sdiff_subset.trans hU
  have h1 : ∑ i ∈ T, g ^ i = ∑ i ∈ range h, if i ∈ T then g ^ i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTr]
  have h2 : ∑ i ∈ U \ T, g ^ i = ∑ i ∈ range h, if i ∈ U \ T then g ^ i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hDr]
  have hpt : ∀ i ∈ range h,
      ((if i ∈ T then g ^ i else 0) - (if i ∈ U \ T then g ^ i else 0)) =
        ((lcoeff ⟨U, T⟩ i : ℤ) : F) * g ^ i := by
    intro i _
    simp only [lcoeff, Int.cast_sub, apply_ite (fun z : ℤ => (z : F)), Int.cast_one,
      Int.cast_zero]
    split_ifs <;> ring
  rw [sVal, h1, h2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hpt]

/-- **The even/odd sign flip** on the positive part of a signed datum.  This is the index
action of the unit `h + 1 ∈ (ZMod (2h))^*`: `g ↦ g^(h+1) = -g` flips the sign of every
odd power and fixes every even power, leaving the index set alone. -/
def flipT (U T : Finset ℕ) : Finset ℕ :=
  T.filter (fun i => i % 2 = 0) ∪ (U \ T).filter (fun i => i % 2 = 1)

lemma flipT_subset {U T : Finset ℕ} (hT : T ⊆ U) : flipT U T ⊆ U := by
  intro i hi
  simp only [flipT, Finset.mem_union, Finset.mem_filter] at hi
  rcases hi with ⟨hiT, -⟩ | ⟨hiUT, -⟩
  · exact hT hiT
  · exact (Finset.mem_sdiff.mp hiUT).1

/-- The flip is an involution on the positive part (inside `U`). -/
lemma flipT_invol {U T : Finset ℕ} (hT : T ⊆ U) : flipT U (flipT U T) = T := by
  ext i
  obtain he | he := Nat.mod_two_eq_zero_or_one i
  · by_cases hU : i ∈ U
    · by_cases hT' : i ∈ T <;>
        simp [flipT, hU, hT', he, Finset.mem_sdiff, Finset.mem_filter]
    · have h1 : i ∉ T := fun h => hU (hT h)
      simp [flipT, hU, h1, he, Finset.mem_sdiff, Finset.mem_filter]
  · by_cases hU : i ∈ U
    · by_cases hT' : i ∈ T <;>
        simp [flipT, hU, hT', he, Finset.mem_sdiff, Finset.mem_filter]
    · have h1 : i ∉ T := fun h => hU (hT h)
      simp [flipT, hU, h1, he, Finset.mem_sdiff, Finset.mem_filter]

/-- **The coefficient identity** behind the symmetry: flipping the signs of the odd
coefficients. -/
lemma lcoeff_flipT {U T : Finset ℕ} (hT : T ⊆ U) (i : ℕ) :
    lcoeff ⟨U, flipT U T⟩ i = lcoeff ⟨U, T⟩ i * (if i % 2 = 0 then 1 else -1) := by
  obtain he | he := Nat.mod_two_eq_zero_or_one i
  · by_cases hU : i ∈ U
    · by_cases hT' : i ∈ T <;>
        simp [lcoeff, flipT, hU, hT', he, Finset.mem_sdiff, Finset.mem_filter]
    · have h1 : i ∉ T := fun h => hU (hT h)
      simp [lcoeff, flipT, hU, h1, he, Finset.mem_sdiff, Finset.mem_filter]
  · by_cases hU : i ∈ U
    · by_cases hT' : i ∈ T <;>
        simp [lcoeff, flipT, hU, hT', he, Finset.mem_sdiff, Finset.mem_filter]
    · have h1 : i ∉ T := fun h => hU (hT h)
      simp [lcoeff, flipT, hU, h1, he, Finset.mem_sdiff, Finset.mem_filter]

/-- `(-1)^i` in a commutative ring matches the integer sign
`if i % 2 = 0 then 1 else -1`. -/
lemma neg_one_pow_eq_intCast_sign {F : Type*} [CommRing F] (i : ℕ) :
    ((-1 : F) ^ i) = (((if i % 2 = 0 then 1 else -1) : ℤ) : F) := by
  rcases Nat.even_or_odd i with hi | hi
  · rw [hi.neg_one_pow, if_pos (Nat.even_iff.mp hi), Int.cast_one]
  · rw [hi.neg_one_pow, if_neg (by have := Nat.odd_iff.mp hi; omega), Int.cast_neg,
      Int.cast_one]

/-- **The `g ↦ -g` value identity.**  Evaluating the signed sum at `-g` is the same as
evaluating the sign-flipped datum at `g`. -/
theorem sVal_neg {F : Type*} [CommRing F] (g : F) {h : ℕ} {U T : Finset ℕ}
    (hU : U ⊆ range h) (hT : T ⊆ U) :
    sVal (-g) ⟨U, T⟩ = sVal g ⟨U, flipT U T⟩ := by
  rw [sVal_eq_sum_coeff (h := h) (-g) hU hT,
    sVal_eq_sum_coeff (h := h) g hU (flipT_subset hT)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow, neg_one_pow_eq_intCast_sign, lcoeff_flipT hT]
  push_cast
  ring

/-- The same flip on a full spectrum datum (the weight tag is untouched). -/
def flipE (e : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)) :
    (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) :=
  ⟨e.1, ⟨e.2.1, flipT e.2.1 e.2.2⟩⟩

lemma flipE_mem {h : ℕ} {A : Finset ℕ} {e : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)}
    (he : e ∈ spectrumData h A) : flipE e ∈ spectrumData h A := by
  obtain ⟨a, U, T⟩ := e
  rw [spectrumData, Finset.mem_sigma] at he ⊢
  exact ⟨he.1, mem_sigData.mpr ⟨(mem_sigData.mp he.2).1,
    flipT_subset (mem_sigData.mp he.2).2⟩⟩

lemma flipE_invol {h : ℕ} {A : Finset ℕ} {e : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)}
    (he : e ∈ spectrumData h A) : flipE (flipE e) = e := by
  obtain ⟨a, U, T⟩ := e
  rw [spectrumData, Finset.mem_sigma] at he
  have hT : T ⊆ U := (mem_sigData.mp he.2).2
  simp only [flipE, flipT_invol hT]

/-- **The value identity on spectrum data.** -/
lemma spectrumVal_neg_eq {F : Type*} [CommRing F] (g : F) {h : ℕ} {A : Finset ℕ}
    {e : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ)} (he : e ∈ spectrumData h A) :
    spectrumVal (-g) e = spectrumVal g (flipE e) := by
  obtain ⟨a, U, T⟩ := e
  rw [spectrumData, Finset.mem_sigma] at he
  obtain ⟨⟨hU, -⟩, hT⟩ := mem_sigData.mp he.2
  simp only [spectrumVal, flipE, sVal_neg g hU hT]

/-- **G335 headline: the spectrum value set is invariant under `g ↦ -g`.** -/
theorem image_spectrumVal_neg {F : Type*} [CommRing F] [DecidableEq F] (g : F) (h : ℕ)
    (A : Finset ℕ) :
    ((spectrumData h A).image (spectrumVal (-g))) =
      ((spectrumData h A).image (spectrumVal g)) := by
  classical
  have hfix : (spectrumData h A).image flipE = spectrumData h A := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact flipE_mem he
    · intro x hx
      exact Finset.mem_image.mpr ⟨flipE x, flipE_mem hx, flipE_invol hx⟩
  have hstep : (spectrumData h A).image (spectrumVal (-g)) =
      (spectrumData h A).image (spectrumVal g ∘ flipE) :=
    Finset.image_congr (fun e he => spectrumVal_neg_eq g he)
  rw [hstep, ← Finset.image_image, hfix]

/-- **Injectivity is generator-symmetric (`g ↦ -g`).** -/
theorem injOn_neg_iff {F : Type*} [CommRing F] (g : F) (h : ℕ) (A : Finset ℕ) :
    Set.InjOn (spectrumVal (-g)) ↑(spectrumData h A) ↔
      Set.InjOn (spectrumVal g) ↑(spectrumData h A) := by
  have key : ∀ e ∈ spectrumData h A, spectrumVal (-g) (flipE e) = spectrumVal g e := by
    intro e he
    rw [spectrumVal_neg_eq g (flipE_mem he), flipE_invol he]
  constructor
  · intro hinj e₁ he₁ e₂ he₂ heq
    have hmem₁ := Finset.mem_coe.mp he₁
    have hmem₂ := Finset.mem_coe.mp he₂
    have hne : spectrumVal (-g) (flipE e₁) = spectrumVal (-g) (flipE e₂) := by
      rw [key e₁ hmem₁, key e₂ hmem₂, heq]
    have h3 := hinj (Finset.mem_coe.mpr (flipE_mem hmem₁))
      (Finset.mem_coe.mpr (flipE_mem hmem₂)) hne
    rw [← flipE_invol hmem₁, ← flipE_invol hmem₂, h3]
  · intro hinj e₁ he₁ e₂ he₂ heq
    have hmem₁ := Finset.mem_coe.mp he₁
    have hmem₂ := Finset.mem_coe.mp he₂
    have hne : spectrumVal g (flipE e₁) = spectrumVal g (flipE e₂) := by
      rw [← spectrumVal_neg_eq g hmem₁, ← spectrumVal_neg_eq g hmem₂, heq]
    have h3 := hinj (Finset.mem_coe.mpr (flipE_mem hmem₁))
      (Finset.mem_coe.mpr (flipE_mem hmem₂)) hne
    rw [← flipE_invol hmem₁, ← flipE_invol hmem₂, h3]

end ArkLib.ProximityGap.Frontier.G335SpectrumGeneratorNegSymmetry
