/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# The ladder–spectrum fusion, I (#371): subset sums ARE signed sums

The bridge between the boundary-slice ladder census (bad set = negated
`(k+1)`-fold subset sums of the domain) and the exact subset-sum spectrum
(`TwoPowerSubsetSumSpectrum`): over an antipodally closed domain
(`g^h = −1`, exponents `range (2h)`), every subset sum REDUCES to a signed sum
of exponents `< h` — antipodal pairs inside the subset cancel, lone high
exponents flip sign.

* `antipodalReduce` — the reduction `S ↦ (L Δ H, L ∖ H)` where `L` is the low
  part and `H` the shifted high part of `S`.
* `sVal_antipodalReduce` — the sum identity `∑_{i∈S} g^i = sVal g (reduce S)`.
* `antipodalReduce_mem_sigData` / weight bookkeeping — the reduced datum lives
  in the stratum of weight `a = |S| − 2·(#antipodal pairs)`, with `a ≡ |S| (2)`
  and `|S| + a ≤ 2h`.
* `validWeights` and `subsetSum_image_subset_spectrum` — the forward inclusion:
  the `m`-subset sum image is contained in the spectrum image over the
  realizable weight set `A(h,m) = {a ≤ m : a ≡ m (2), m + a ≤ 2h}`.
* `subsetSum_image_card_le` — the count upper bound
  `#(subset-sum image) ≤ ∑_{a ∈ A(h,m)} 2^a · C(h,a)` under the in-tree
  injectivity input.

Part II (`LadderSpectrumFusionExact`) will add the converse construction
(every realizable signed datum is a subset sum) and the exact count.
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- The low part of a subset of exponents: members `< h`. -/
def lowPart (h : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun i => i < h)

/-- The shifted high part: members `≥ h`, shifted down by `h`. -/
def highPart (h : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (S.filter (fun i => ¬ i < h)).image (fun i => i - h)

/-- **The antipodal reduction** of a subset of exponents: the signed datum
`(L Δ H, L ∖ H)` — support = symmetric difference (antipodal pairs cancel),
positive part = the lone low exponents. -/
def antipodalReduce (h : ℕ) (S : Finset ℕ) : (_ : Finset ℕ) × Finset ℕ :=
  ⟨(lowPart h S \ highPart h S) ∪ (highPart h S \ lowPart h S),
    lowPart h S \ highPart h S⟩

theorem highPart_subset_range {h : ℕ} {S : Finset ℕ} (hS : S ⊆ range (2 * h)) :
    highPart h S ⊆ range h := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  have hiS := (Finset.mem_filter.mp hi).1
  have hih := (Finset.mem_filter.mp hi).2
  have := Finset.mem_range.mp (hS hiS)
  rw [Finset.mem_range]
  omega

theorem lowPart_subset_range {h : ℕ} {S : Finset ℕ} :
    lowPart h S ⊆ range h := by
  intro i hi
  rw [Finset.mem_range]
  exact (Finset.mem_filter.mp hi).2

/-- The shift map is injective on the high filter, so the high part has the
same cardinality. -/
theorem card_highPart {h : ℕ} (S : Finset ℕ) :
    (highPart h S).card = (S.filter (fun i => ¬ i < h)).card := by
  refine Finset.card_image_of_injOn fun i hi j hj hij => ?_
  have h1 := (Finset.mem_filter.mp hi).2
  have h2 := (Finset.mem_filter.mp hj).2
  omega

/-- **The reduction sum identity**: over an antipodally closed domain, the
subset sum equals the signed sum of the reduced datum. -/
theorem sVal_antipodalReduce {g : F} {h : ℕ} (hh : g ^ h = -1)
    {S : Finset ℕ} (hS : S ⊆ range (2 * h)) :
    sVal g (antipodalReduce h S) = ∑ i ∈ S, g ^ i := by
  set L := lowPart h S with hL
  set H := highPart h S with hH
  -- split the sum into low and high parts
  have hsplit : ∑ i ∈ S, g ^ i
      = (∑ i ∈ L, g ^ i) + ∑ i ∈ S.filter (fun i => ¬ i < h), g ^ i := by
    rw [hL, lowPart]
    exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- reindex the high part through the shift, then flip signs
  have hhigh : ∑ i ∈ S.filter (fun i => ¬ i < h), g ^ i
      = -∑ j ∈ H, g ^ j := by
    have hinj : ∀ i ∈ S.filter (fun i => ¬ i < h),
        ∀ j ∈ S.filter (fun i => ¬ i < h), i - h = j - h → i = j := by
      intro i hi j hj hij
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2
      omega
    calc ∑ i ∈ S.filter (fun i => ¬ i < h), g ^ i
        = ∑ i ∈ S.filter (fun i => ¬ i < h), -(g ^ (i - h)) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have h1 := (Finset.mem_filter.mp hi).2
          rw [← antipodal_pow hh (i - h), Nat.sub_add_cancel (by omega)]
      _ = -∑ i ∈ S.filter (fun i => ¬ i < h), g ^ (i - h) := by
          rw [Finset.sum_neg_distrib]
      _ = -∑ j ∈ H, g ^ j := by
          rw [hH, highPart, Finset.sum_image hinj]
  -- cancel the common part of L and H
  have hcancel : (∑ i ∈ L, g ^ i) - ∑ j ∈ H, g ^ j
      = (∑ i ∈ L \ H, g ^ i) - ∑ j ∈ H \ L, g ^ j := by
    have h1 : ∑ i ∈ L ∩ H, g ^ i + ∑ i ∈ L \ H, g ^ i = ∑ i ∈ L, g ^ i :=
      Finset.sum_inter_add_sum_diff L H _
    have h2 : ∑ i ∈ H ∩ L, g ^ i + ∑ i ∈ H \ L, g ^ i = ∑ i ∈ H, g ^ i :=
      Finset.sum_inter_add_sum_diff H L _
    rw [Finset.inter_comm] at h2
    linear_combination h2 - h1
  -- assemble: sVal of the reduced datum
  have hdisj : Disjoint (L \ H) (H \ L) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1
  rw [antipodalReduce, sVal]
  show (∑ i ∈ L \ H, g ^ i)
      - ∑ i ∈ ((L \ H) ∪ (H \ L)) \ (L \ H), g ^ i = _
  rw [Finset.union_sdiff_cancel_left hdisj, hsplit, hhigh]
  linear_combination -hcancel

/-- The reduced datum lies in the stratum of its own support weight. -/
theorem antipodalReduce_mem_sigData {h : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range (2 * h)) :
    antipodalReduce h S ∈ sigData h (antipodalReduce h S).1.card := by
  rw [mem_sigData]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · exact Finset.union_subset
      ((Finset.sdiff_subset).trans lowPart_subset_range)
      ((Finset.sdiff_subset).trans (highPart_subset_range hS))
  · exact Finset.subset_union_left

/-- **Weight bookkeeping**: the reduced weight `a` satisfies `|S| = a + 2p`
(`p` = number of antipodal pairs inside `S`) and `|S| + a ≤ 2h` — the weight
has the parity of `|S|`, is at most `|S|`, and is realizable. -/
theorem antipodalReduce_weight {h : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range (2 * h)) :
    (antipodalReduce h S).1.card + 2 * (lowPart h S ∩ highPart h S).card
        = S.card
      ∧ S.card + (antipodalReduce h S).1.card ≤ 2 * h := by
  set L := lowPart h S with hL
  set H := highPart h S with hH
  have hcardS : S.card = L.card + H.card := by
    rw [hH, card_highPart, hL, lowPart]
    exact (Finset.card_filter_add_card_filter_not _).symm
  have hUcard : (antipodalReduce h S).1.card
      = (L \ H).card + (H \ L).card := by
    rw [antipodalReduce]
    exact Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1)
  have h1 : (L \ H).card + (L ∩ H).card = L.card :=
    Finset.card_sdiff_add_card_inter L H
  have h2 : (H \ L).card + (H ∩ L).card = H.card :=
    Finset.card_sdiff_add_card_inter H L
  have hcomm : (H ∩ L).card = (L ∩ H).card := by rw [Finset.inter_comm]
  -- the union bound: L ∪ H ⊆ range h
  have hunion : (L ∪ H).card ≤ h := by
    calc (L ∪ H).card ≤ (range h).card :=
          Finset.card_le_card (Finset.union_subset lowPart_subset_range
            (highPart_subset_range hS))
      _ = h := Finset.card_range h
  have h3 : (L ∪ H).card + (L ∩ H).card = L.card + H.card :=
    Finset.card_union_add_card_inter L H
  constructor
  · omega
  · omega

/-- **The realizable weight set** `A(h, m)`: weights of the same parity as `m`,
at most `m`, with `m + a ≤ 2h`. -/
def validWeights (h m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun a => a % 2 = m % 2 ∧ m + a ≤ 2 * h)

theorem antipodalReduce_weight_mem_validWeights {h m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range (2 * h)) (hcard : S.card = m) :
    (antipodalReduce h S).1.card ∈ validWeights h m := by
  obtain ⟨h1, h2⟩ := antipodalReduce_weight hS
  rw [validWeights, Finset.mem_filter, Finset.mem_range]
  omega

/-- **The forward inclusion**: the `m`-subset sum image over the antipodally
closed domain is contained in the spectrum image over the realizable weights. -/
theorem subsetSum_image_subset_spectrum (g : F) {h : ℕ} (hh : g ^ h = -1)
    (m : ℕ) :
    ((range (2 * h)).powersetCard m).image (fun S => ∑ i ∈ S, g ^ i)
      ⊆ (spectrumData h (validWeights h m)).image (spectrumVal g) := by
  intro x hx
  obtain ⟨S, hSmem, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_powersetCard] at hSmem
  obtain ⟨hSsub, hScard⟩ := hSmem
  refine Finset.mem_image.mpr
    ⟨⟨(antipodalReduce h S).1.card, antipodalReduce h S⟩, ?_, ?_⟩
  · rw [spectrumData, Finset.mem_sigma]
    exact ⟨antipodalReduce_weight_mem_validWeights hSsub hScard,
      antipodalReduce_mem_sigData hSsub⟩
  · rw [spectrumVal]
    exact sVal_antipodalReduce hh hSsub

/-- **The count upper bound**: under the in-tree injectivity input, the number
of distinct `m`-fold subset sums is at most the spectrum mass
`∑_{a ∈ A(h,m)} 2^a · C(h,a)`. -/
theorem subsetSum_image_card_le (g : F) {h : ℕ} (hh : g ^ h = -1) (m : ℕ)
    (hinj : Set.InjOn (spectrumVal g) (spectrumData h (validWeights h m))) :
    (((range (2 * h)).powersetCard m).image (fun S => ∑ i ∈ S, g ^ i)).card
      ≤ ∑ a ∈ validWeights h m, 2 ^ a * h.choose a := by
  calc (((range (2 * h)).powersetCard m).image
        (fun S => ∑ i ∈ S, g ^ i)).card
      ≤ ((spectrumData h (validWeights h m)).image (spectrumVal g)).card :=
        Finset.card_le_card (subsetSum_image_subset_spectrum g hh m)
    _ = ∑ a ∈ validWeights h m, 2 ^ a * h.choose a :=
        subsetSumSpectrum_card g h (validWeights h m) hinj

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.sVal_antipodalReduce
#print axioms ArkLib.ProximityGap.KKH26.subsetSum_image_subset_spectrum
#print axioms ArkLib.ProximityGap.KKH26.subsetSum_image_card_le
