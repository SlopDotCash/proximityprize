/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BandPackingLaw

/-!
# Band attainment (#371): the lower construction below the boundary band

The two-sided picture of the `δ*(ε*)` curve at every band: the packing law
(`band_packing_law`) gives `#badSet ≤ C(n,k+1)/C(k+m+1,k+1)`; this file
proves the matching LOWER construction — the **disjoint-blocks stack**:

  **`∃ u₀ : #badSet(u₀, x^k) ≥ r` whenever `r·(k+m+1) ≤ n` and `r ≤ q`**

at any radius reachable by `(k+m+1)`-point witnesses.  Partition (a prefix of)
the domain into `r` blocks of `k+m+1` consecutive indices; on block `j` set
`u₀ := −γⱼ·x^k` for `r` distinct scalars `γⱼ`.  The line `u₀ + γⱼ·x^k`
vanishes identically on block `j` (witnessed by the zero codeword), and no
joint pair exists since `x^k` is strongly far — so every `γⱼ` is bad.

In particular `r = ⌊n/(k+m+1)⌋` is realizable: the band-`m` sup over stacks is
sandwiched between `⌊n/(k+m+1)⌋` (this construction) and
`C(n,k+1)/C(k+m+1,k+1)` (packing); at `m = 0` the two meet the exact solved
value `C(n,k+1)` from the boundary analysis.  Closing the polynomial gap
between them at `m ≥ 1` is a design-existence question, isolated from the
proximity-gap machinery.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE BAND ATTAINMENT CONSTRUCTION**: at any radius reachable by
`(k+m+1)`-point witnesses, the disjoint-blocks stack realizes `r` bad scalars
whenever `r` blocks fit in the domain and `r` distinct scalars exist. -/
theorem band_attainment (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {r : ℕ} (hr : r * (k + m + 1) ≤ n) (hrF : r ≤ Fintype.card F) :
    ∃ u₀ : Fin n → F,
      r ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card := by
  set s := k + m + 1 with hs
  -- r distinct scalars
  obtain ⟨G, -, hGcard⟩ := Finset.exists_subset_card_eq
    (show r ≤ (Finset.univ : Finset F).card by
      rw [Finset.card_univ]; exact hrF)
  set ι : Fin r → F :=
    fun j => (G.equivFin.symm (Fin.cast hGcard.symm j) : F) with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : (G.equivFin.symm (Fin.cast hGcard.symm a))
        = G.equivFin.symm (Fin.cast hGcard.symm b) := Subtype.ext hab
    exact Fin.cast_injective _ (G.equivFin.symm.injective h1)
  -- the disjoint-blocks word
  set u₀ : Fin n → F := fun i =>
    if h : (i : ℕ) / s < r then -(ι ⟨(i : ℕ) / s, h⟩) * (dom i) ^ k else 0
    with hu₀
  refine ⟨u₀, ?_⟩
  -- the direction is strongly far (free)
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k := by
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h
  -- each scalar is bad, witnessed by its block
  have hbadj : ∀ j : Fin r, mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      u₀ (fun i => (dom i) ^ k) (ι j) := by
    intro j
    -- the block
    have hblockfit : (j + 1) * s ≤ n := by
      have hj := j.2
      calc (j + 1) * s ≤ r * s := Nat.mul_le_mul_right s (by omega)
        _ ≤ n := hr
    have hbound : ∀ x ∈ Finset.Ico ((j : ℕ) * s) (((j : ℕ) + 1) * s),
        x < n := by
      intro x hx
      have := (Finset.mem_Ico.mp hx).2
      omega
    set T : Finset (Fin n) :=
      (Finset.Ico ((j : ℕ) * s) (((j : ℕ) + 1) * s)).attachFin hbound
      with hT
    have hTcard : T.card = s := by
      rw [hT, Finset.card_attachFin, Nat.card_Ico]
      have : ((j : ℕ) + 1) * s = (j : ℕ) * s + s := by ring
      omega
    have hTdiv : ∀ i ∈ T, (i : ℕ) / s = (j : ℕ) := by
      intro i hi
      have h := (Finset.mem_Ico.mp ((Finset.mem_attachFin hbound).mp hi))
      exact Nat.div_eq_of_lt_le h.1 h.2
    refine ⟨T, ?_, ⟨0, Submodule.zero_mem _, fun i hi => ?_⟩, ?_⟩
    · -- size
      rw [hTcard]
      exact_mod_cast hhi
    · -- the line vanishes on the block
      have hdiv := hTdiv i hi
      have hlt : (i : ℕ) / s < r := by
        rw [hdiv]
        exact j.2
      show (0 : F) = u₀ i + ι j • (dom i) ^ k
      rw [hu₀]
      simp only [hlt, dif_pos, smul_eq_mul]
      have hval : (⟨(i : ℕ) / s, hlt⟩ : Fin r) = j := by
        apply Fin.ext
        exact hdiv
      rw [hval]
      ring
    · -- no joint pair: the direction is strongly far
      rintro ⟨v₀, -, v₁, hv₁, hagj⟩
      have hsub : T ⊆ agreeSet v₁ (fun i => (dom i) ^ k) := by
        intro i hi
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hagj i hi).2⟩
      have hcard : s ≤ (agreeSet v₁ (fun i => (dom i) ^ k)).card := by
        calc s = T.card := hTcard.symm
          _ ≤ _ := Finset.card_le_card hsub
      have := hμ v₁ hv₁
      omega
  -- collect: the image of the scalars sits inside the bad set
  calc r = ((Finset.univ : Finset (Fin r)).image ι).card := by
        rw [Finset.card_image_of_injective _ hιinj, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ _ := by
        refine Finset.card_le_card fun γ hγ => ?_
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hγ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadj j⟩

open Classical in
/-- **THE TWO-SIDED BAND BRACKET**: at the band radius
`k+m < (1−δ)n ≤ k+m+1`, the sup over stacks with strongly far direction `x^k`
is sandwiched: some stack realizes `⌊n/(k+m+1)⌋` bad scalars, and every such
stack is bounded by the packing law. -/
theorem band_bracket (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : ((k + m : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hrF : n / (k + m + 1) ≤ Fintype.card F) :
    (∃ u₀ : Fin n → F,
      n / (k + m + 1) ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card)
    ∧ ∀ u₀ : Fin n → F,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card * (k + m + 1).choose (k + 1)
        ≤ n.choose (k + 1) := by
  constructor
  · exact band_attainment dom hk hhi
      (Nat.div_mul_le_self n (k + m + 1)) hrF
  · intro u₀
    refine band_packing_law dom hk hlo ?_
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.band_attainment
#print axioms ProximityGap.Ownership.band_bracket
