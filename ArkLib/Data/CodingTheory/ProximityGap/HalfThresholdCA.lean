/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityCA
import ArkLib.Data.CodingTheory.Basic.RelativeDistance

/-!
# Half-Threshold Correlated Agreement (Theorem 5)

This file formalizes the load-bearing linear-algebra lemma of

* Chai–Fan, *FRI Soundness Above the Johnson Bound via Threshold Halving*,
  ePrint 2026/858, **Theorem 5** ("Half-Threshold Correlated Agreement"),
  a classical fact going back to Rothblum–Vadhan–Wigderson 2013 (RVW13).

## Statement

Let `C ⊆ Fⁿ` be an arbitrary **linear** code (a subspace of `ι → F`), and let
`f₁ f₂ : ι → F`.  Write

* `Δ(g, C)`        for the relative Hamming distance from `g` to `C`
  (`Code.relDistFromCode`, notation `δᵣ(g, C)`);
* `Δ_joint`        for the relative Hamming distance from the *paired* word
  `pairWord f₁ f₂ : ι → F × F` to the *pair code*
  `pairCode C = { (c₁, c₂) | c₁, c₂ ∈ C }` (over the product alphabet `F × F`).

**Theorem 5.** For any `δ ∈ [0, 1]`: if `Δ_joint > δ`, then at most one scalar
`γ ∈ F` satisfies `Δ(f₁ + γ • f₂, C) ≤ δ / 2`.  Equivalently the correlated-agreement
error satisfies `ε_ca(C, δ/2, δ) ≤ 1 / |F|` (the bad set of coefficients has size `≤ 1`).

## Proof sketch (the formalized argument)

Suppose `γ₁ ≠ γ₂` both satisfy `Δ(f₁ + γᵢ • f₂, C) ≤ δ/2`.  Pick codewords `hᵢ ∈ C`
with agreement sets `Sᵢ` of size `≥ (1 − δ/2) n`.  By inclusion–exclusion
`|S₁ ∩ S₂| ≥ (1 − δ) n`.  On `S₁ ∩ S₂` both linear equations `f₁ + γᵢ f₂ = hᵢ` hold;
since `γ₁ ≠ γ₂` the `2×2` system is invertible, so pointwise on `S₁ ∩ S₂`
`(f₁, f₂) = (g₁, g₂)` for the codewords
`g₂ = (γ₁ − γ₂)⁻¹ (h₁ − h₂) ∈ C`, `g₁ = h₁ − γ₁ • g₂ ∈ C`
(both in `C` by `F`-linearity).  Hence the joint disagreement is `≤ n − |S₁ ∩ S₂| ≤ δ n`,
i.e. `Δ_joint ≤ δ`, contradicting the hypothesis. ∎

## Implementation notes

The pointwise `2×2`-solve-gives-a-codeword step and the inclusion–exclusion core are
already verified, over **natural-number** thresholds, in
`ArkLib/Data/CodingTheory/ProximityCA.lean` (`ProximityPrizeCA.ca_halved`,
`ca_halved_count_le_one`, adapted from the public IoTeX `rs-proximity-gaps` development).
This file is the *relative-distance (paper `δ ∈ [0,1]`) wrapper*: it relates the joint
relative distance `Δ_joint > δ` and the per-coefficient bound `Δ(·, C) ≤ δ/2` to the
natural-number agreement-count premises consumed by `ca_halved_count_le_one`, via the
distance-realm bridges in `Basic/RelativeDistance.lean`.

The whole-domain threshold uses `d := ⌊(δ/2) · n⌋`.  The key numeric step is
`2 d = 2 ⌊(δ/2) n⌋ ≤ δ n < hammingDist`, where the strict inequality comes from
`Δ_joint > δ`; this yields `(jointAgreeSet …).card + 2 d < n`, the premise of
`ca_halved_count_le_one`.
-/

namespace ProximityPrizeCA

open Finset Code NNReal
open scoped NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The **pair code** of a linear code `C`: the set of paired words `(c₁, c₂)` with
`c₁, c₂ ∈ C`, viewed as words over the product alphabet `F × F`.  This is the code
whose minimum distance defines the joint distance `Δ_joint` of Theorem 5. -/
def pairCode (C : Submodule F (ι → F)) : Set (ι → F × F) :=
  (fun p : (ι → F) × (ι → F) => pairWord p.1 p.2) '' ((C : Set (ι → F)) ×ˢ (C : Set (ι → F)))

/-- Joint relative distance of `(f₁, f₂)` to `C × C`, i.e. `Δ_joint` of Theorem 5:
the relative Hamming distance from the paired word `pairWord f₁ f₂` to the pair code. -/
noncomputable def jointRelDist (f₁ f₂ : ι → F) (C : Submodule F (ι → F)) : ENNReal :=
  δᵣ(pairWord f₁ f₂, pairCode C)

omit [DecidableEq ι] in
/-- If `Δ_joint > δ`, then for every codeword pair `(g₁, g₂)` the paired word
`pairWord f₁ f₂` is strictly more than `⌊δ · n⌋` far (in absolute Hamming distance) from
`pairWord g₁ g₂`.  This is the numeric heart of the reduction; staying in `ℕ` avoids the
`ℚ≥0`/`ℝ≥0` coercion friction. -/
theorem deltaJoint_floor_lt_hammingDist
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hδ : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    {g₁ g₂ : ι → F} (hg₁ : g₁ ∈ C) (hg₂ : g₂ ∈ C) :
    Nat.floor (δ * (Fintype.card ι : ℝ≥0))
      < hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂) := by
  classical
  -- `pairWord g₁ g₂` is a codeword of the pair code.
  have hmem : pairWord g₁ g₂ ∈ pairCode C := ⟨(g₁, g₂), ⟨hg₁, hg₂⟩, rfl⟩
  -- `Δ_joint ≤ δᵣ(pairWord f₁ f₂, pairWord g₁ g₂)`.
  have hle : jointRelDist f₁ f₂ C ≤ δᵣ(pairWord f₁ f₂, pairWord g₁ g₂) :=
    relDistFromCode_le_relDist_to_mem _ _ hmem
  -- Hence `δ < δᵣ(pairWord f₁ f₂, pairWord g₁ g₂)` (pairwise relative distance), in `ENNReal`.
  have hδ' : (δ : ENNReal) < δᵣ(pairWord f₁ f₂, pairWord g₁ g₂) := lt_of_lt_of_le hδ hle
  -- Descend to the `ℝ≥0` pairwise relative distance: `δ < relHammingDist`.
  have hδr : δ < ((relHammingDist (pairWord f₁ f₂) (pairWord g₁ g₂) : ℚ≥0) : ℝ≥0) := by
    have hcoe : ((δ : ℝ≥0) : ENNReal)
        < (((relHammingDist (pairWord f₁ f₂) (pairWord g₁ g₂) : ℚ≥0) : ℝ≥0) : ENNReal) := by
      rwa [ENNReal.coe_NNRat_coe_NNReal] at hδ'
    exact_mod_cast hcoe
  -- Negate the realm bridge `δᵣ(u, v) ≤ δ ↔ Δ₀(u, v) ≤ ⌊δ n⌋`.
  have hbridge := pairRelDist_le_iff_pairDist_le
    (u := pairWord f₁ f₂) (v := pairWord g₁ g₂) δ
  -- `δ < δᵣ(u, v)` means `¬ (δᵣ(u, v) ≤ δ)`, hence `¬ (Δ₀ ≤ ⌊δ n⌋)`, i.e. `⌊δ n⌋ < Δ₀`.
  have hnot : ¬ (δᵣ(pairWord f₁ f₂, pairWord g₁ g₂) ≤ δ) := by
    rw [not_le]
    -- `δᵣ(u, v)` pairwise is `relHammingDist`, coerced to `ℝ≥0` here via the lemma's statement.
    simpa using hδr
  rw [hbridge] at hnot
  exact lt_of_not_ge hnot

/-- **Theorem 5 (Half-Threshold Correlated Agreement; RVW13 / ePrint 2026/858).**

For an arbitrary linear code `C ⊆ Fⁿ` and functions `f₁ f₂ : ι → F`, if the joint
relative distance of `(f₁, f₂)` to the pair code `C × C` exceeds `δ`, then **at most one**
scalar `γ ∈ F` makes the affine line `f₁ + γ • f₂` lie within relative distance `δ/2` of `C`.

Equivalently the correlated-agreement error is `≤ 1 / |F|`: the bad coefficient set is a
subsingleton.  The bound `Δ(f₁ + γ • f₂, C) ≤ δ/2` is expressed via the repo's
`δᵣ(·, C) : ENNReal` relative-distance-to-code. -/
theorem theorem5_halfThreshold_correlatedAgreement [Fintype F]
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C) :
    ((Finset.univ : Finset F).filter
      (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal))).card
      ≤ 1 := by
  classical
  set n : ℕ := Fintype.card ι with hn_def
  set d : ℕ := Nat.floor ((δ / 2 : ℝ≥0) * (n : ℝ≥0)) with hd_def
  -- The whole-domain `δ/2` closeness in `ENNReal`/`δᵣ` form is the `(agreeSet …).card + d`
  -- bad-witness form consumed by `ca_halved_count_le_one`.  We rewrite the filtered set.
  have hset :
      ((Finset.univ : Finset F).filter
        (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal)))
      = ((Finset.univ : Finset F).filter
          (fun γ => ∃ h ∈ (C : Set (ι → F)),
            Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + d)) := by
    apply Finset.filter_congr
    intro γ _
    constructor
    · intro hγ
      -- `δᵣ(u, C) ≤ δ/2  →  Δ₀(u, C) ≤ ⌊(δ/2) n⌋ = d  →  ∃ h ∈ C, agreement ≥ n − d`.
      rw [relDistFromCode_le_iff_distFromCode_le] at hγ
      rw [closeToCode_iff_closeToCodeword_of_minDist] at hγ
      obtain ⟨h, hhC, hdist⟩ := hγ
      refine ⟨h, hhC, ?_⟩
      -- `Δ₀(u, h) ≤ d` gives agreement `≥ n − d`, i.e. `n ≤ agreement + d`.
      have hcard := card_le_agreeSet_card_add_of_hammingDist_le
        (f := linComb f₁ f₂ γ) (g := h) (d := d) (by
          rw [show (Δ₀(linComb f₁ f₂ γ, h)) = (hammingDist (linComb f₁ f₂ γ) h) from rfl] at hdist
          exact_mod_cast hdist)
      simpa [hn_def] using hcard
    · intro hγ
      obtain ⟨h, hhC, hcard⟩ := hγ
      -- Reverse: agreement `≥ n − d`  →  `Δ₀(u, h) ≤ d`  →  `Δ₀(u, C) ≤ d`  →  `δᵣ ≤ δ/2`.
      rw [relDistFromCode_le_iff_distFromCode_le]
      rw [closeToCode_iff_closeToCodeword_of_minDist]
      refine ⟨h, hhC, ?_⟩
      have hham : hammingDist (linComb f₁ f₂ γ) h ≤ Nat.floor ((δ / 2 : ℝ≥0) * (n : ℝ≥0)) := by
        have hpart := agreementCols_card_add_hammingDist (linComb f₁ f₂ γ) h
        have heq : (agreeSet (linComb f₁ f₂ γ) h) = agreementCols (linComb f₁ f₂ γ) h := by
          ext x; simp [agreeSet, agreementCols]
        rw [heq] at hcard
        omega
      -- `Δ₀(u, h) = ↑(hammingDist u h)`; conclude `Δ₀(u, h) ≤ ⌊(δ/2) n⌋`.
      have : (Δ₀(linComb f₁ f₂ γ, h)) ≤ (Nat.floor ((δ / 2 : ℝ≥0) * (n : ℝ≥0)) : ℕ∞) := by
        exact_mod_cast hham
      simpa [hn_def] using this
  rw [hset]
  -- Apply the verified natural-number theorem; supply the joint-distance premise.
  apply ca_halved_count_le_one C f₁ f₂ d
  intro g₁ hg₁ g₂ hg₂
  -- Goal: `(jointAgreeSet f₁ f₂ g₁ g₂).card + 2 * d < n`.
  -- Use `jointAgree.card = n − hammingDist(pair, pair g)` and `2 d ≤ δ n < hammingDist`.
  have hpart :
      (jointAgreeSet f₁ f₂ g₁ g₂).card + hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂) = n := by
    -- Direct partition identity: agreement count + Hamming distance = `n`.
    simpa [jointAgreeSet, pairWord, hammingDist, hn_def] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι))
        (p := fun x : ι => f₁ x = g₁ x ∧ f₂ x = g₂ x))
  -- `⌊δ n⌋ < hammingDist` from the joint-distance premise.
  have hstrict := deltaJoint_floor_lt_hammingDist C f₁ f₂ hjoint hg₁ hg₂
  -- `2 d ≤ δ n` in `ℝ≥0`, hence `2 d ≤ ⌊δ n⌋` in `ℕ`.
  have hdle_real : ((2 * d : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
    have hfloor : (d : ℝ≥0) ≤ (δ / 2 : ℝ≥0) * (n : ℝ≥0) := by
      rw [hd_def]; exact Nat.floor_le (by positivity)
    have htwo : (2 : ℝ≥0) * ((δ / 2 : ℝ≥0) * (n : ℝ≥0)) = δ * (n : ℝ≥0) := by
      have : (2 : ℝ≥0) * (δ / 2 : ℝ≥0) = δ := by
        rw [mul_div_assoc']
        rw [mul_comm]
        exact mul_div_cancel_right₀ δ (by norm_num : (2 : ℝ≥0) ≠ 0)
      rw [← mul_assoc, this]
    calc ((2 * d : ℕ) : ℝ≥0) = (2 : ℝ≥0) * (d : ℝ≥0) := by push_cast; ring
      _ ≤ (2 : ℝ≥0) * ((δ / 2 : ℝ≥0) * (n : ℝ≥0)) := by gcongr
      _ = δ * (Fintype.card ι : ℝ≥0) := by rw [htwo, hn_def]
  have h2d_le_floor : 2 * d ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) :=
    Nat.le_floor hdle_real
  -- Chain `2 d ≤ ⌊δ n⌋ < hammingDist` and combine with the partition identity.
  omega

-- Axiom audit: the main theorem and its numeric kernel are axiom-clean
-- (`propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`).
#print axioms theorem5_halfThreshold_correlatedAgreement
#print axioms deltaJoint_floor_lt_hammingDist

end ProximityPrizeCA
