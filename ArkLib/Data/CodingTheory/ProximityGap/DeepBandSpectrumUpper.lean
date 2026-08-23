/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The antipodal-pairing UPPER bound on the deep-band subset-sum spectrum (#389)

For a *negation-closed* domain `A = P ⊔ (-P)` (i.e. `-p ∉ P` for `p ∈ P`), every `r`-subset-sum
of `A` is a **signed** sum over a subset `J ⊆ P` with `|J| ≤ r` and `|J| ≡ r (mod 2)`: pairing
`p` with `-p`, a subset `S ⊆ A` contributes `0` from every antipodal pair it contains in full,
`+p` (resp. `-p`) from the singletons.  Hence the `r`-subset-sum spectrum embeds into the finite
set of signed sums `signedSpectrum P r`, giving the closed-form cardinality ceiling

  `|spectrum_r|  ≤  ∑_{ℓ≤r, ℓ≡r (2)}  C(|P|,ℓ)·2^ℓ`.

For `μ = μ_{2^m}` (`-ζ^j = ζ^{j+2^{m-1}}`, `P` the lower half, `|P| = 2^{m-1}`) this is exactly
the verified deep-band subset-sum spectrum cardinality `∑_{ℓ≤r, ℓ≡r (2)} 2^ℓ·C(2^{m-1},ℓ)` —
here proven as a universal UPPER bound from the antipodal pairing **alone** (no cyclotomic
power-basis independence), strictly below the trivial `C(2^m, r)`.  This is the sharper upper
bracket flagged by `DeepBandSubsetSumSpectrum` as "the remaining obstruction (the EXACT spectrum
cardinality)"; the matching lower bracket `2^r·C(2^{m-1}, r) ≤ |spectrum|` is `kkh26_lemma1`.

## Main results
* `subset_sum_eq_signed` — the antipodal sum-decomposition `∑_{a∈S} a = ∑_{p∈J} ±p`.
* `spectrum_subset_signedSpectrum` — the spectrum embeds in `signedSpectrum P r`.
* `signedSpectrum_card_le_choose_sum` — the closed-form ceiling `∑ C(|P|,ℓ)·2^ℓ`.
* `deepband_spectrum_card_le_choose_sum` — the bound applied to the `-∑` deep-band spectrum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.SpectrumUpper

variable {F : Type*} [Field F] [DecidableEq F]

/-- The signed-sum index image: `J ⊆ P` with `|J| ≤ r`, `|J| ≡ r (mod 2)`, mapped to `∑_{j∈J} ±j`. -/
noncomputable def signedSpectrum (P : Finset F) (r : ℕ) : Finset F := by
  classical
  exact (P.powerset.filter (fun J => J.card ≤ r ∧ J.card % 2 = r % 2)).biUnion
    (fun J => (Finset.univ : Finset (J → Bool)).image
      (fun s => ∑ j : J, (if s j then (j : F) else -(j : F))))

/-- **Antipodal sum-decomposition.** `∑_{a∈S} a = ∑_{p∈J}(if p∈S then p else -p)`,
`J = {p∈P : exactly one of p,−p ∈ S}`, for `S ⊆ P ⊔ (-P)`. -/
theorem subset_sum_eq_signed
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    {S : Finset F} (hSsub : ↑S ⊆ ↑P ∪ ↑(P.image (fun p => -p))) :
    (∑ a ∈ S, a)
      = ∑ p ∈ P.filter (fun p => (p ∈ S) ≠ (-p ∈ S)), (if p ∈ S then p else -p) := by
  classical
  set NP := P.image (fun p => -p) with hNP
  have hPNPdisj : Disjoint P NP := by
    rw [Finset.disjoint_left]; intro x hxP hxN
    rw [hNP, Finset.mem_image] at hxN; obtain ⟨p, hp, rfl⟩ := hxN; exact hPneg p hp hxP
  have hScover : S = (S ∩ P) ∪ (S ∩ NP) := by
    rw [← Finset.inter_union_distrib_left]
    refine (Finset.inter_eq_left.mpr ?_).symm
    intro x hx; have := hSsub hx; simpa [Finset.mem_union] using this
  have hSdisj : Disjoint (S ∩ P) (S ∩ NP) :=
    hPNPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsplit : (∑ a ∈ S, a) = (∑ a ∈ S ∩ P, a) + (∑ a ∈ S ∩ NP, a) := by
    rw [← Finset.sum_union hSdisj, ← hScover]
  set T := P.filter (fun p => -p ∈ S) with hT
  set U := P.filter (fun p => p ∈ S) with hU
  have hNPsum : (∑ a ∈ S ∩ NP, a) = - ∑ p ∈ T, p := by
    have hbij : S ∩ NP = T.image (fun p => -p) := by
      ext x; constructor
      · intro hx; rw [Finset.mem_inter, hNP, Finset.mem_image] at hx
        obtain ⟨hxS, p, hp, rfl⟩ := hx
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hxS⟩, rfl⟩
      · intro hx; rw [Finset.mem_image] at hx; obtain ⟨p, hp, rfl⟩ := hx
        rw [Finset.mem_filter] at hp
        exact Finset.mem_inter.mpr ⟨hp.2, by rw [hNP]; exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩⟩
    rw [hbij, Finset.sum_image (fun a _ b _ h => neg_injective h), ← Finset.sum_neg_distrib]
  have hPsum : (∑ a ∈ S ∩ P, a) = ∑ p ∈ U, p := by
    congr 1; rw [hU]; ext x; rw [Finset.mem_inter, Finset.mem_filter]; tauto
  have hUsum : (∑ p ∈ U, p) = ∑ p ∈ P, (if p ∈ S then p else 0) := by rw [hU, Finset.sum_filter]
  have hTsum : (∑ p ∈ T, p) = ∑ p ∈ P, (if -p ∈ S then p else 0) := by rw [hT, Finset.sum_filter]
  rw [hsplit, hPsum, hNPsum, hUsum, hTsum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ S <;> by_cases hq : -p ∈ S <;> simp [hp, hq]

/-- **Containment**: every `r`-subset-sum of `P ⊔ (-P)` lands in `signedSpectrum P r`. -/
theorem subset_sum_mem_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    {S : Finset F} {r : ℕ} (hScard : S.card = r)
    (hSsub : ↑S ⊆ ↑P ∪ ↑(P.image (fun p => -p))) :
    (∑ a ∈ S, a) ∈ signedSpectrum P r := by
  classical
  set NP := P.image (fun p => -p) with hNP
  set J := P.filter (fun p => (p ∈ S) ≠ (-p ∈ S)) with hJ
  have hdecomp := subset_sum_eq_signed P hPneg (S := S) hSsub
  have hPNPdisj : Disjoint P NP := by
    rw [Finset.disjoint_left]; intro x hxP hxN
    rw [hNP, Finset.mem_image] at hxN; obtain ⟨p, hp, rfl⟩ := hxN; exact hPneg p hp hxP
  set U := P.filter (fun p => p ∈ S) with hU
  set Tt := P.filter (fun p => -p ∈ S) with hTt
  set B := P.filter (fun p => p ∈ S ∧ -p ∈ S) with hB
  have hUcard_add : U.card + Tt.card = J.card + 2 * B.card := by
    simp only [hU, hTt, hJ, hB, Finset.card_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ S <;> by_cases hq : -p ∈ S <;> simp [hp, hq]
  have hScards : S.card = U.card + Tt.card := by
    have hScover : S = (S ∩ P) ∪ (S ∩ NP) := by
      rw [← Finset.inter_union_distrib_left]
      refine (Finset.inter_eq_left.mpr ?_).symm
      intro x hx; have := hSsub hx; simpa [Finset.mem_union] using this
    have hSdisj : Disjoint (S ∩ P) (S ∩ NP) :=
      hPNPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have h1 : S.card = ((S ∩ P) ∪ (S ∩ NP)).card := congrArg Finset.card hScover
    rw [h1, Finset.card_union_of_disjoint hSdisj]
    congr 1
    · rw [hU]; congr 1; ext x; rw [Finset.mem_inter, Finset.mem_filter]; tauto
    · rw [hTt]
      have hbij : S ∩ NP = Tt.image (fun p => -p) := by
        ext x; constructor
        · intro hx; rw [Finset.mem_inter, hNP, Finset.mem_image] at hx
          obtain ⟨hxS, p, hp, rfl⟩ := hx
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hxS⟩, rfl⟩
        · intro hx; rw [Finset.mem_image] at hx; obtain ⟨p, hp, rfl⟩ := hx
          rw [Finset.mem_filter] at hp
          exact Finset.mem_inter.mpr ⟨hp.2, by rw [hNP]; exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩⟩
      rw [hbij, Finset.card_image_of_injective _ neg_injective, hTt]
  have hJle : J.card ≤ r := by omega
  have hJpar : J.card % 2 = r % 2 := by omega
  rw [signedSpectrum, Finset.mem_biUnion]
  refine ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    hJle, hJpar⟩, ?_⟩
  rw [Finset.mem_image]
  refine ⟨fun j => decide ((j : F) ∈ S), Finset.mem_univ _, ?_⟩
  rw [hdecomp, ← Finset.sum_attach J (fun p => if p ∈ S then p else -p)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [decide_eq_true_eq]

/-- **The `r`-subset-sum spectrum is contained in `signedSpectrum`** — hence its cardinality is
bounded by `|signedSpectrum P r|`, the `±`-factoring ceiling. -/
theorem spectrum_subset_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P) (r : ℕ) :
    ((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)
      ⊆ signedSpectrum P r := by
  classical
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_powersetCard] at hS
  refine subset_sum_mem_signedSpectrum P hPneg hS.2 ?_
  exact_mod_cast hS.1

/-- **Card ceiling**: the number of distinct `r`-subset-sums of `P ⊔ (-P)` is at most
`|signedSpectrum P r|`. -/
theorem subset_sum_card_le_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P) (r : ℕ) :
    (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)).card
      ≤ (signedSpectrum P r).card :=
  Finset.card_le_card (spectrum_subset_signedSpectrum P hPneg r)

/-- `|signedSpectrum P r| ≤ ∑_{J ⊆ P, |J|≤r, |J|≡r (2)} 2^{|J|}` — each index `J`
contributes at most `2^{|J|}` signs. -/
theorem signedSpectrum_card_le_sum (P : Finset F) (r : ℕ) :
    (signedSpectrum P r).card
      ≤ ∑ J ∈ P.powerset.filter (fun J => J.card ≤ r ∧ J.card % 2 = r % 2), 2 ^ J.card := by
  classical
  rw [signedSpectrum]
  refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum ?_)
  intro J _
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **The closed-form ceiling** (`#389`): grouping the index sets by cardinality,
`|signedSpectrum P r| ≤ ∑_{ℓ≤r, ℓ≡r (2)} C(|P|,ℓ)·2^ℓ`.  For `P = {ζ^0,…,ζ^{2^{m-1}-1}}`
(`|P| = 2^{m-1}`) this is exactly the verified deep-band subset-sum spectrum cardinality
`∑_{ℓ≤r, ℓ≡r (2)} 2^ℓ·C(2^{m-1},ℓ)` — here proven as a universal UPPER bound from the
antipodal pairing alone, no cyclotomic independence. -/
theorem signedSpectrum_card_le_choose_sum (P : Finset F) (r : ℕ) :
    (signedSpectrum P r).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2),
          P.card.choose ℓ * 2 ^ ℓ := by
  classical
  refine le_trans (signedSpectrum_card_le_sum P r) ?_
  -- regroup the filtered powerset sum by cardinality
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun J => J.card)
        (t := (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2))
        (by
          intro J hJ
          simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le hJ.2.1, hJ.2.2⟩)]
  apply Finset.sum_le_sum
  intro ℓ _
  -- inner fiber: J ⊆ P with J.card = ℓ (and the filter conditions), summand 2^ℓ
  have hbound : ∀ J ∈ (P.powerset.filter
      (fun J => J.card ≤ r ∧ J.card % 2 = r % 2)).filter (fun J => J.card = ℓ),
      2 ^ J.card = 2 ^ ℓ := by
    intro J hJ
    rw [Finset.mem_filter] at hJ
    rw [hJ.2]
  rw [Finset.sum_congr rfl hbound, Finset.sum_const, smul_eq_mul]
  gcongr
  -- count of such J ≤ C(|P|, ℓ)
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_powersetCard ℓ P))
  intro J hJ
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hJ
  exact Finset.mem_powersetCard.mpr ⟨hJ.1.1, hJ.2⟩

/-- **The deep-band bad-scalar bridge** (`#389`).  For the deep-band subset-sum spectrum
`(μ.powersetCard r).image (fun S => -∑_{ζ∈S} ζ)` of a *negation-closed* domain `μ = P ⊔ (-P)`
(the case `μ = μ_{2^m}`, `P` the lower half, `-ζ^j = ζ^{j+2^{m-1}}`), the antipodal-pairing
ceiling applies verbatim:

  `|spectrum_r| ≤ ∑_{ℓ≤r, ℓ≡r (2)} C(|P|,ℓ)·2^ℓ`.

This is the *sharper upper bracket* the `DeepBandSubsetSumSpectrum` docstring flags as "the
remaining obstruction (the EXACT spectrum cardinality)": for `|P| = 2^{m-1}` the bound is
`∑_{ℓ≤r, ℓ≡r (2)} C(2^{m-1},ℓ)·2^ℓ`, which is exactly the verified closed-form spectrum
cardinality — here proven as a universal ceiling from antipodal pairing alone (no cyclotomic
power-basis independence), strictly below the trivial `C(2^m, r)`. -/
theorem deepband_spectrum_card_le_choose_sum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    (μ : Finset F) (hμ : μ = P ∪ P.image (fun p => -p)) (r : ℕ) :
    ((μ.powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2),
          P.card.choose ℓ * 2 ^ ℓ := by
  classical
  subst hμ
  -- the `-∑` spectrum has the same cardinality as the `+∑` spectrum (negation is injective)
  have hcard : (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      = (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)).card := by
    rw [show (fun S => -∑ a ∈ S, a) = (fun x : F => -x) ∘ (fun S => ∑ a ∈ S, a) from rfl,
      ← Finset.image_image, Finset.card_image_of_injective _ neg_injective]
  rw [hcard]
  exact le_trans (subset_sum_card_le_signedSpectrum P hPneg r)
    (signedSpectrum_card_le_choose_sum P r)

end ArkLib.ProximityGap.SpectrumUpper
