/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderSpectrumFusion

/-!
# The ladder–spectrum fusion, II (#371): the EXACT subset-sum count

The converse of Part I: every signed datum of realizable weight IS an `m`-fold
subset sum — pad the lifted datum (positives stay low, negatives shift high)
with `(m−a)/2` antipodal pairs chosen outside the support; the pairs cancel.
Hence the two images coincide and, under the in-tree injectivity input,

  **`#{ m-fold subset sums of an antipodally closed domain }
      = ∑_{a ∈ A(h,m)} 2^a · C(h,a)`**,

`A(h,m) = {a ≤ m : a ≡ m (2), m + a ≤ 2h}` — the exact closed-form count of the
boundary-slice ladder bad set (`boundary_slice_ladder_badSet_eq_unconditional`),
generalizing the in-tree single-stratum `kkh26` count to the full spectrum and
matching the probe-measured `N(3,3) = 40` at `h = 4, m = 3`.
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- Shifted sums flip sign over an antipodally closed domain. -/
theorem sum_image_shift {g : F} {h : ℕ} (hh : g ^ h = -1) (X : Finset ℕ) :
    ∑ j ∈ X.image (· + h), g ^ j = -∑ x ∈ X, g ^ x := by
  rw [Finset.sum_image fun a _ b _ hab => by omega]
  calc ∑ x ∈ X, g ^ (x + h) = ∑ x ∈ X, -(g ^ x) :=
        Finset.sum_congr rfl fun x _ => antipodal_pow hh x
    _ = -∑ x ∈ X, g ^ x := by rw [Finset.sum_neg_distrib]

/-- **The spectrum lift**: realize a signed datum as a subset of exponents —
positives stay low, negatives shift high, padded with antipodal pairs `P`. -/
def spectrumLift (h : ℕ) (P : Finset ℕ) (d : (_ : Finset ℕ) × Finset ℕ) :
    Finset ℕ :=
  ((d.2 ∪ (d.1 \ d.2).image (· + h)) ∪ P) ∪ P.image (· + h)

section Lift

variable {h : ℕ} {P : Finset ℕ} {d : (_ : Finset ℕ) × Finset ℕ}

theorem spectrumLift_subset (hU : d.1 ⊆ range h) (hT : d.2 ⊆ d.1)
    (hP : P ⊆ range h) :
    spectrumLift h P d ⊆ range (2 * h) := by
  intro x hx
  rw [spectrumLift] at hx
  rw [Finset.mem_range]
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · have := Finset.mem_range.mp (hU (hT hx))
        omega
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        have := Finset.mem_range.mp (hU (Finset.mem_sdiff.mp hu).1)
        omega
    · have := Finset.mem_range.mp (hP hx)
      omega
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_range.mp (hP hu)
    omega

theorem spectrumLift_card (hU : d.1 ⊆ range h) (hT : d.2 ⊆ d.1)
    (hP : P ⊆ range h) (hPU : Disjoint P d.1) :
    (spectrumLift h P d).card = d.1.card + 2 * P.card := by
  have hTlow : ∀ x ∈ d.2, x < h := fun x hx =>
    Finset.mem_range.mp (hU (hT hx))
  have hPlow : ∀ x ∈ P, x < h := fun x hx => Finset.mem_range.mp (hP hx)
  have hd1 : Disjoint d.2 ((d.1 \ d.2).image (· + h)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx'
    have := hTlow _ hx
    omega
  have hd2 : Disjoint (d.2 ∪ (d.1 \ d.2).image (· + h)) P := by
    rw [Finset.disjoint_left]
    intro x hx hxP
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.disjoint_left.mp hPU hxP) (hT hx)
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      have := hPlow _ hxP
      omega
  have hd3 : Disjoint ((d.2 ∪ (d.1 \ d.2).image (· + h)) ∪ P)
      (P.image (· + h)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx'
    have huh := hPlow _ hu
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · have := hTlow _ hx
        omega
      · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hx
        have hvU : v ∈ d.1 := (Finset.mem_sdiff.mp hv).1
        have : v = u := by omega
        subst this
        exact (Finset.disjoint_left.mp hPU hu) hvU
    · have := hPlow _ hx
      omega
  rw [spectrumLift, Finset.card_union_of_disjoint hd3,
    Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_image_of_injective _ (add_left_injective h),
    Finset.card_image_of_injective _ (add_left_injective h),
    Finset.card_sdiff_of_subset hT]
  have hTle : d.2.card ≤ d.1.card := Finset.card_le_card hT
  omega

theorem sum_spectrumLift {g : F} (hh : g ^ h = -1) (hU : d.1 ⊆ range h)
    (hT : d.2 ⊆ d.1) (hP : P ⊆ range h) (hPU : Disjoint P d.1) :
    ∑ i ∈ spectrumLift h P d, g ^ i = sVal g d := by
  have hTlow : ∀ x ∈ d.2, x < h := fun x hx =>
    Finset.mem_range.mp (hU (hT hx))
  have hPlow : ∀ x ∈ P, x < h := fun x hx => Finset.mem_range.mp (hP hx)
  have hd1 : Disjoint d.2 ((d.1 \ d.2).image (· + h)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx'
    have := hTlow _ hx
    omega
  have hd2 : Disjoint (d.2 ∪ (d.1 \ d.2).image (· + h)) P := by
    rw [Finset.disjoint_left]
    intro x hx hxP
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.disjoint_left.mp hPU hxP) (hT hx)
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      have := hPlow _ hxP
      omega
  have hd3 : Disjoint ((d.2 ∪ (d.1 \ d.2).image (· + h)) ∪ P)
      (P.image (· + h)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx'
    have huh := hPlow _ hu
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · have := hTlow _ hx
        omega
      · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hx
        have hvU : v ∈ d.1 := (Finset.mem_sdiff.mp hv).1
        have : v = u := by omega
        subst this
        exact (Finset.disjoint_left.mp hPU hu) hvU
    · have := hPlow _ hx
      omega
  rw [spectrumLift, Finset.sum_union hd3, Finset.sum_union hd2,
    Finset.sum_union hd1, sum_image_shift hh, sum_image_shift hh, sVal]
  ring

end Lift

/-- **The converse inclusion**: every spectrum value of realizable weight is an
`m`-fold subset sum. -/
theorem spectrum_subset_subsetSum_image (g : F) {h : ℕ} (hh : g ^ h = -1)
    (m : ℕ) :
    (spectrumData h (validWeights h m)).image (spectrumVal g)
      ⊆ ((range (2 * h)).powersetCard m).image (fun S => ∑ i ∈ S, g ^ i) := by
  intro x hx
  obtain ⟨⟨a, d⟩, hmem, rfl⟩ := Finset.mem_image.mp hx
  rw [spectrumData, Finset.mem_sigma] at hmem
  obtain ⟨haA, hd⟩ := hmem
  rw [mem_sigData] at hd
  obtain ⟨⟨hU, hUcard⟩, hT⟩ := hd
  rw [validWeights, Finset.mem_filter, Finset.mem_range] at haA
  obtain ⟨ham, hpar, hreach⟩ := haA
  -- choose the padding pairs outside the support
  have hcomp : (m - a) / 2 ≤ (range h \ d.1).card := by
    have hUcard' : d.1.card = a := hUcard
    have ham' : a < m + 1 := ham
    have hpar' : a % 2 = m % 2 := hpar
    have hreach' : m + a ≤ 2 * h := hreach
    rw [Finset.card_sdiff_of_subset hU, Finset.card_range, hUcard']
    omega
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hcomp
  have hP : P ⊆ range h := hPsub.trans Finset.sdiff_subset
  have hPU : Disjoint P d.1 := by
    rw [Finset.disjoint_left]
    intro x hxP hxU
    exact (Finset.mem_sdiff.mp (hPsub hxP)).2 hxU
  refine Finset.mem_image.mpr ⟨spectrumLift h P d, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨spectrumLift_subset hU hT hP, ?_⟩
    have hUcard' : d.1.card = a := hUcard
    have ham' : a < m + 1 := ham
    have hpar' : a % 2 = m % 2 := hpar
    have hreach' : m + a ≤ 2 * h := hreach
    rw [spectrumLift_card hU hT hP hPU, hUcard', hPcard]
    omega
  · rw [sum_spectrumLift hh hU hT hP hPU]
    rfl

/-- **THE IMAGE EQUALITY**: the `m`-fold subset-sum image over an antipodally
closed domain IS the spectrum image over the realizable weights. -/
theorem subsetSum_image_eq_spectrum (g : F) {h : ℕ} (hh : g ^ h = -1)
    (m : ℕ) :
    ((range (2 * h)).powersetCard m).image (fun S => ∑ i ∈ S, g ^ i)
      = (spectrumData h (validWeights h m)).image (spectrumVal g) :=
  Finset.Subset.antisymm (subsetSum_image_subset_spectrum g hh m)
    (spectrum_subset_subsetSum_image g hh m)

/-- **THE EXACT SUBSET-SUM COUNT**: under the in-tree injectivity input, the
number of distinct `m`-fold subset sums of an antipodally closed domain is
exactly the spectrum mass `∑_{a ∈ A(h,m)} 2^a · C(h,a)`. -/
theorem subsetSum_image_card_eq (g : F) {h : ℕ} (hh : g ^ h = -1) (m : ℕ)
    (hinj : Set.InjOn (spectrumVal g) (spectrumData h (validWeights h m))) :
    (((range (2 * h)).powersetCard m).image (fun S => ∑ i ∈ S, g ^ i)).card
      = ∑ a ∈ validWeights h m, 2 ^ a * h.choose a := by
  rw [subsetSum_image_eq_spectrum g hh m,
    subsetSumSpectrum_card g h (validWeights h m) hinj]

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.sum_spectrumLift
#print axioms ArkLib.ProximityGap.KKH26.subsetSum_image_eq_spectrum
#print axioms ArkLib.ProximityGap.KKH26.subsetSum_image_card_eq
