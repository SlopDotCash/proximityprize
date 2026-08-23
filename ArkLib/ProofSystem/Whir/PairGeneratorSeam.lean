/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGapP

/-!
# #302 — the ℓ-ary pair-generator seam, closed (scratch file)

The pair-generator seam (uniform-over-image PMF pushforward) landed in-tree for the
`Fin 2` affine-line case (`MCAPairSeam.pr_uniform_subtype_image`,
`hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`, commit `9b8b2972f`) and in generic-iff
form (`Claim57.GenSeam.hasMutualCorrAgreement_genRSC_iff_uniform`, commit `6e4c0934f`).
What remained of frontier item (c) at the *seam* layer was the weld at general `parℓ`:
the ℓ-ary `epsMCAP` chain (`ProximityGapP.Pr_proximityConditionP_le_epsMCAP`) ends at the
`F`-uniform probability, while `hasMutualCorrAgreement (genRSC (Fin parℓ) …)` samples the
generator finset `Gen.Gen = image (r ↦ (r^{exp j})ⱼ) univ`. This file proves:

* `pr_uniform_image_of_const_fiber` — the **fiber-counting pushforward**: uniform sampling
  over the image finset of a map all of whose fibers (over the image) have the *same* size
  `c` equals parameter sampling. This is the honest general form of the seam — the
  in-tree injective case is exactly `c = 1`;
* `pr_uniform_image_of_injective` — the injective case, recovered as a corollary
  (independent re-derivation of the in-tree `pr_uniform_subtype_image`);
* `hasMutualCorrAgreement_genRSC_of_epsMCAP_le` — **the ℓ-ary seam, closed**: for the
  power generator `genRSC (Fin parℓ) φ m exp` with some exponent equal to `1`, a bound
  `epsMCAP (smoothCode φ m) exp δ ≤ errStar δ` on the admissible range yields
  `hasMutualCorrAgreement (genRSC (Fin parℓ) φ m exp) BStar errStar`. This is the
  general-`parℓ` analogue of the landed pair seam: after it, the only ℓ-ary obligation
  left in #302's item (c) is the *mathematical* bound on `epsMCAP` (the Hab25 chain at
  `parℓ` words), no sampling or plumbing content;
* `hasMutualCorrAgreement_genRSC_vandermonde_of_epsMCAP_le` — the canonical Vandermonde
  instantiation `exp = Fin.val` (the paper generator `(1, γ, γ², …, γ^{parℓ−1})`);
* `hasMutualCorrAgreement_genRSC_pair_vandermonde_of_epsMCA_le` — sanity weld: at
  `parℓ = 2` the ℓ-ary seam + the in-tree `epsMCAP_two_le_epsMCA` bridge recover the
  landed pair-seam conclusion from the same `epsMCA` hypothesis.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace Whir302B

open NNReal ProbabilityTheory ReedSolomon

attribute [local instance] Classical.propDecidable

/-! ## Fiber counting -/

section Counting

variable {α β : Type} [Fintype α] [DecidableEq β]

/-- Decomposing the count of `{x : E (g x)}` along the fibers of `g`: only image points
satisfying `E` contribute, each with its full fiber. -/
lemma card_filter_comp_eq_sum (g : α → β) (E : β → Prop) :
    (Finset.univ.filter (fun x : α => E (g x))).card =
      ∑ y ∈ (Finset.univ.image g).filter E,
        (Finset.univ.filter (fun x : α => g x = y)).card := by
  classical
  have H : ∀ x ∈ Finset.univ.filter (fun x : α => E (g x)),
      g x ∈ (Finset.univ.image g).filter E := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_image_of_mem g (Finset.mem_univ x), hx.2⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun y hy => ?_
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h2⟩
    exact h2
  · intro h2
    refine ⟨?_, h2⟩
    rw [h2]
    exact (Finset.mem_filter.mp hy).2

/-- The domain size is the sum of the fiber sizes over the image. -/
lemma card_univ_eq_sum_fibers (g : α → β) :
    Fintype.card α = ∑ y ∈ Finset.univ.image g,
      (Finset.univ.filter (fun x : α => g x = y)).card := by
  classical
  rw [← Finset.card_univ]
  exact Finset.card_eq_sum_card_image g Finset.univ

end Counting

/-! ## The fiber-counting pushforward (the seam, general form) -/

section Pushforward

variable {α : Type} [Fintype α] [Nonempty α]

open Classical in
/-- **Uniform-over-image pushforward, fiber-counting form.** If every fiber of
`g : α → β` over its image has the same size `c`, then sampling uniformly from the image
finset and testing `E` equals sampling the parameter uniformly from `α` and testing
`E ∘ g`. The two probabilities are `#(filter E (image g)) / #(image g)` and
`#(filter (E ∘ g) univ) / #α`; constant fibers scale both numerator and denominator of the
second by exactly `c`. The injective case is `c = 1`. (`c > 0` is automatic: fibers over
image points are nonempty.) -/
theorem pr_uniform_image_of_const_fiber {β : Type} [DecidableEq β]
    (g : α → β) (c : ℕ)
    (hfib : ∀ y ∈ Finset.univ.image g,
      (Finset.univ.filter (fun x : α => g x = y)).card = c)
    (E : β → Prop) :
    haveI : Nonempty ↥(Finset.univ.image g) :=
      Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
    (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[E ↑r]) = Pr_{let γ ←$ᵖ α}[E (g γ)] := by
  haveI : Nonempty ↥(Finset.univ.image g) :=
    Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  -- `c` is positive: the fiber over any image point is nonempty
  obtain ⟨y₀, hy₀⟩ := Finset.image_nonempty.mpr (Finset.univ_nonempty (α := α))
  have hc : 0 < c := by
    rw [← hfib y₀ hy₀]
    obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp hy₀
    exact Finset.card_pos.mpr ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card]
  -- the subtype-filter count equals the image-filter count
  have hsub : (Finset.univ.filter
      (fun r : ↥(Finset.univ.image g) => E ↑r)).card =
      ((Finset.univ.image g).filter E).card := by
    refine Finset.card_bij (fun r _ => (r : β)) ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨r.2, hr.2⟩
    · intro r₁ h₁ r₂ h₂ h
      exact Subtype.ext h
    · intro y hy
      rw [Finset.mem_filter] at hy
      exact ⟨⟨y, hy.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2⟩, rfl⟩
  -- the parameter-side count is `c ·` the image-filter count
  have hnum : (Finset.univ.filter (fun x : α => E (g x))).card =
      c * ((Finset.univ.image g).filter E).card := by
    rw [card_filter_comp_eq_sum g E,
      Finset.sum_congr rfl (fun y hy => hfib y ((Finset.mem_filter.mp hy).1)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  -- the domain size is `c ·` the image size
  have hden : Fintype.card α = c * (Finset.univ.image g).card := by
    rw [card_univ_eq_sum_fibers g,
      Finset.sum_congr rfl (fun y hy => hfib y hy),
      Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Fintype.card_coe, hsub, hnum, hden]
  push_cast
  exact (ENNReal.mul_div_mul_left _ _
    (by exact_mod_cast hc.ne') (ENNReal.natCast_ne_top c)).symm

open Classical in
/-- **Injective case of the pushforward** — every fiber over the image is a singleton, so
the fiber-counting form at `c = 1` recovers the in-tree
`MutualCorrAgreement.pr_uniform_subtype_image` (independent derivation). -/
theorem pr_uniform_image_of_injective {β : Type} [DecidableEq β]
    (g : α → β) (hg : Function.Injective g) (E : β → Prop) :
    haveI : Nonempty ↥(Finset.univ.image g) :=
      Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
    (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[E ↑r]) = Pr_{let γ ←$ᵖ α}[E (g γ)] := by
  refine pr_uniform_image_of_const_fiber g 1 ?_ E
  intro y hy
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext x'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => hg h, fun h => by rw [h]⟩

end Pushforward

/-! ## The ℓ-ary seam, closed -/

section Seam

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Classical in
/-- **The ℓ-ary pair-generator seam.** For the power generator
`genRSC (Fin parℓ) φ m exp` (sampling `r = (γ^{exp j})ⱼ` for uniform `γ`), with some
exponent equal to `1` (so the generator map is injective — true for the canonical
Vandermonde exponents and the WHIR pair `(0,1)`), a bound on the general-`parℓ` mutual
correlated agreement error

  `epsMCAP (smoothCode φ m) exp δ ≤ errStar δ` for `0 < δ < 1 − B*`

yields `hasMutualCorrAgreement (genRSC (Fin parℓ) φ m exp) BStar errStar`. Sampling the
generator finset is parameter sampling (`pr_uniform_image_of_injective`), and the
`F`-uniform probability is dominated by `epsMCAP` via the in-tree ℓ-ary chain
(`ProximityGapP.Pr_proximityConditionP_le_epsMCAP`). The general-`parℓ` analogue of the
landed `hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`. -/
theorem hasMutualCorrAgreement_genRSC_of_epsMCAP_le
    (parℓ : ℕ) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin parℓ ↪ ℕ)
    (j₀ : Fin parℓ) (h1 : exp j₀ = 1)
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ProximityGapP.epsMCAP (F := F) (A := F)
        (((RSGenerator.genRSC (Fin parℓ) φ m exp).C : Set (ι → F))) (⇑exp) δ
        ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin parℓ) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin parℓ) φ m exp).hℓ
    MutualCorrAgreement.hasMutualCorrAgreement
      (RSGenerator.genRSC (Fin parℓ) φ m exp) BStar errStar := by
  intro f δ hδ
  -- the radius is below 1
  have hδ1 : δ < 1 := by
    have h2 := hδ.2
    have : (δ : ℝ) < 1 := lt_of_lt_of_le h2 (by linarith)
    exact_mod_cast this
  -- the power map and its injectivity (some exponent is 1)
  set g : F → (Fin parℓ → F) := fun r => fun j => r ^ (exp j) with hg_def
  have hginj : Function.Injective g := by
    intro a b hab
    have h := congrFun hab j₀
    simpa [hg_def, h1] using h
  haveI : Nonempty ↥(Finset.univ.image g) :=
    Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  -- sampling the generator finset is parameter sampling
  have hpr := pr_uniform_image_of_injective g hginj
    (fun r => MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ r
      ((RSGenerator.genRSC (Fin parℓ) φ m exp).C))
  have hmain : (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[
      MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ (↑r)
        ((RSGenerator.genRSC (Fin parℓ) φ m exp).C)]) ≤ errStar δ :=
    calc (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[
        MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ (↑r)
          ((RSGenerator.genRSC (Fin parℓ) φ m exp).C)])
        = Pr_{let γ ←$ᵖ F}[MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ)
            f δ (g γ) ((RSGenerator.genRSC (Fin parℓ) φ m exp).C)] := hpr
      _ ≤ ProximityGapP.epsMCAP (F := F) (A := F)
            (((RSGenerator.genRSC (Fin parℓ) φ m exp).C : Set (ι → F))) (⇑exp) δ :=
          ProximityGapP.Pr_proximityConditionP_le_epsMCAP hδ1 (⇑exp) f
      _ ≤ errStar δ := heps δ hδ.1 hδ.2
  exact hmain

open Classical in
/-- **The Vandermonde instantiation.** The canonical exponents `exp j = j` (the paper
generator `(1, γ, γ², …, γ^{parℓ−1})`) at any `parℓ ≥ 2`: `exp 1 = 1` makes the
generator map injective, so an `epsMCAP` bound closes the MCA obligation. -/
theorem hasMutualCorrAgreement_genRSC_vandermonde_of_epsMCAP_le
    (parℓ : ℕ) (h2 : 2 ≤ parℓ) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ProximityGapP.epsMCAP (F := F) (A := F) (parℓ := parℓ)
        (((RSGenerator.genRSC (Fin parℓ) φ m Fin.valEmbedding).C : Set (ι → F)))
        Fin.val δ ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin parℓ) φ m Fin.valEmbedding).parℓ :=
      (RSGenerator.genRSC (Fin parℓ) φ m Fin.valEmbedding).hℓ
    MutualCorrAgreement.hasMutualCorrAgreement
      (RSGenerator.genRSC (Fin parℓ) φ m Fin.valEmbedding) BStar errStar :=
  hasMutualCorrAgreement_genRSC_of_epsMCAP_le parℓ φ m Fin.valEmbedding
    ⟨1, by omega⟩ rfl BStar hB errStar heps

open Classical in
/-- **Sanity weld (pair case).** At `parℓ = 2` with the Vandermonde exponents, the ℓ-ary
seam composed with the in-tree bridge `ProximityGapP.epsMCAP_two_le_epsMCA` recovers the
landed pair-seam conclusion from the same affine-line `epsMCA` hypothesis — the ℓ-ary
seam strictly subsumes the pair seam at canonical exponents. -/
theorem hasMutualCorrAgreement_genRSC_pair_vandermonde_of_epsMCA_le
    (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      _root_.ProximityGap.epsMCA (F := F) (A := F)
        (((RSGenerator.genRSC (Fin 2) φ m Fin.valEmbedding).C : Set (ι → F))) δ
        ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m Fin.valEmbedding).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m Fin.valEmbedding).hℓ
    MutualCorrAgreement.hasMutualCorrAgreement
      (RSGenerator.genRSC (Fin 2) φ m Fin.valEmbedding) BStar errStar :=
  hasMutualCorrAgreement_genRSC_vandermonde_of_epsMCAP_le 2 le_rfl φ m
    BStar hB errStar
    (fun δ hδ0 hδB => le_trans
      (ProximityGapP.epsMCAP_two_le_epsMCA
        (((RSGenerator.genRSC (Fin 2) φ m Fin.valEmbedding).C : Set (ι → F))) δ)
      (heps δ hδ0 hδB))

end Seam

end Whir302B

/-! ## Axiom audit -/
#print axioms Whir302B.card_filter_comp_eq_sum
#print axioms Whir302B.card_univ_eq_sum_fibers
#print axioms Whir302B.pr_uniform_image_of_const_fiber
#print axioms Whir302B.pr_uniform_image_of_injective
#print axioms Whir302B.hasMutualCorrAgreement_genRSC_of_epsMCAP_le
#print axioms Whir302B.hasMutualCorrAgreement_genRSC_vandermonde_of_epsMCAP_le
#print axioms Whir302B.hasMutualCorrAgreement_genRSC_pair_vandermonde_of_epsMCA_le
