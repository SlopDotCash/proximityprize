/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.LadderSpectrumFusionExact

/-!
# The ladder–spectrum fusion, III (#371): THE EXACT THRESHOLD COUNT

The capstone of the fusion: combining the unconditional boundary-slice ladder
census (`boundary_slice_ladder_badSet_eq_unconditional`) with the exact
subset-sum count (`subsetSum_image_card_eq`), the number of bad scalars of the
ladder stack `(x^{k+1}, x^k)` over an antipodally closed power domain
(`dom i = g^i`, `n = 2h`, `g^h = −1`) at the boundary radius
`k < (1−δ)n ≤ k+1` is EXACTLY

  **`#badSet = ∑_{a ∈ A(h, k+1)} 2^a · C(h, a)`**,

`A(h,m) = {a ≤ m : a ≡ m (2), m + a ≤ 2h}` — conditional only on the in-tree
signed-sum injectivity input (proven above the prime threshold as
`sVal_injOn`).  This is the first exact bad-scalar COUNT at a radius strictly
above Johnson: the threshold `ε_mca` value for the ladder stack is pinned in
closed form.  At `h = 4, k = 2` the formula gives
`2¹·C(4,1) + 2³·C(4,3) = 8 + 32 = 40`, matching the probe-measured census.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap
open ArkLib.ProximityGap.KKH26 in
open Classical in
/-- **THE EXACT THRESHOLD COUNT** for the ladder stack over an antipodally
closed power domain: at the boundary radius, the number of bad scalars is the
spectrum mass `∑_{a ∈ A(h,k+1)} 2^a · C(h,a)`, conditional only on the in-tree
signed-sum injectivity. -/
theorem boundary_slice_ladder_badSet_card {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n : ℕ} [NeZero n] (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    {g : F} {h : ℕ} (hn : n = 2 * h) (hh : g ^ h = -1)
    (hdom : ∀ i : Fin n, dom i = g ^ (i : ℕ))
    (hinj : Set.InjOn (spectrumVal g)
      (spectrumData h (validWeights h (k + 1)))) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      = ∑ a ∈ validWeights h (k + 1), 2 ^ a * h.choose a := by
  rw [boundary_slice_ladder_badSet_eq_unconditional dom hk hlo hhi]
  -- absorb the negation
  have hneg : (Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) => -∑ i ∈ S, dom i)
      = ((Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).image (fun x => -x) := by
    rw [Finset.image_image]
    rfl
  rw [hneg, Finset.card_image_of_injective _ neg_injective]
  -- reindex subsets of `Fin n` to subsets of exponents
  have himg : (Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)
      = ((range (2 * h)).powersetCard (k + 1)).image
        (fun S => ∑ j ∈ S, g ^ j) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · rintro ⟨S, ⟨-, hcard⟩, rfl⟩
      refine ⟨S.image (fun i : Fin n => (i : ℕ)), ⟨?_, ?_⟩, ?_⟩
      · intro j hj
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
        rw [Finset.mem_range]
        have := i.2
        omega
      · rw [Finset.card_image_of_injective _ Fin.val_injective, hcard]
      · rw [Finset.sum_image fun i _ j _ hij => Fin.val_injective hij]
        exact (Finset.sum_congr rfl fun i _ => hdom i).symm
    · rintro ⟨T, ⟨hTsub, hTcard⟩, rfl⟩
      have hTn : ∀ m ∈ T, m < n := fun m hm => by
        have := Finset.mem_range.mp (hTsub hm)
        omega
      refine ⟨T.attachFin hTn, ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_attachFin, hTcard]
      · have himgval : (T.attachFin hTn).image (fun i : Fin n => (i : ℕ))
            = T := by
          ext j
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact (Finset.mem_attachFin hTn).mp hi
          · intro hj
            exact ⟨⟨j, hTn j hj⟩, (Finset.mem_attachFin hTn).mpr hj, rfl⟩
        calc ∑ i ∈ T.attachFin hTn, dom i
            = ∑ i ∈ T.attachFin hTn, g ^ (i : ℕ) :=
              Finset.sum_congr rfl fun i _ => hdom i
          _ = ∑ j ∈ (T.attachFin hTn).image (fun i : Fin n => (i : ℕ)),
                g ^ j :=
              (Finset.sum_image fun i _ j _ hij => Fin.val_injective hij).symm
          _ = ∑ j ∈ T, g ^ j := by rw [himgval]
  rw [himg]
  exact subsetSum_image_card_eq g hh (k + 1) hinj

open ArkLib.ProximityGap.KKH26 in
open Classical in
/-- Probability form of `boundary_slice_ladder_badSet_card`: the ladder stack's
boundary-slice `mcaEvent` probability is the exact spectrum mass divided by the
field size. -/
theorem boundary_slice_ladder_mcaEvent_prob {F : Type} [Field F] [Fintype F]
    {n : ℕ} [NeZero n] (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    {g : F} {h : ℕ} (hn : n = 2 * h) (hh : g ^ h = -1)
    (hdom : ∀ i : Fin n, dom i = g ^ (i : ℕ))
    (hinj : Set.InjOn (spectrumVal g)
      (spectrumData h (validWeights h (k + 1)))) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ]
      = (((∑ a ∈ validWeights h (k + 1), 2 ^ a * h.choose a : ℕ) : ℝ≥0) :
            ℝ≥0∞)
          / (((Fintype.card F : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  rw [boundary_slice_ladder_badSet_card dom hk hlo hhi hn hh hdom hinj]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_card
#print axioms ProximityGap.Ownership.boundary_slice_ladder_mcaEvent_prob
