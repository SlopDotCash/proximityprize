/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseMaster

/-!
# Round 5 (#357): the defect-line kill — common-core patterns die in the time domain

The strip-cell sweep (issue record) found the global-core pattern's syndrome kernels
supported on the shared point alone — and the death mechanism is not rank but the **defect
line**: for a stack whose rows are codewords away from one point `x`,

  `u₀ = V₀ + d₀·δ_x`, `u₁ = V₁ + d₁·δ_x`  (`V₀, V₁ ∈ C`),

a bad scalar `γ` forces `d₀ + γ·d₁ = 0` (`defect_line_of_bad`): a witness avoiding `x` is
explained by `(V₀, V₁)` outright, and a witness containing `x` pins the on-line codeword to
`V₀ + γV₁` by distance, evaluating to the defect-line equation at `x`. Hence
(`badScalar_card_le_one_of_core`) such stacks have **at most one bad scalar** — two
distinct roots kill both defects and then `(V₀, V₁)` explains everything.

The hypotheses are strikingly weak: `NoWeightLE C b` (distance `≥ b + 1`) — far below the
strip, let alone the `3b − 2` master threshold. In the strip demolition this lemma retires
every common-core overlap pattern at every band; the remaining patterns are the
small-triple-union shapes (landed cored machinery) and the fully-disjoint triples (the
certificate branch).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCADefectLineKill

open ProximityGap.MCAStaircaseMaster

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The defect line.** For a stack whose rows are codewords away from the single point
`x`, every bad scalar is a root of the defect line: `d₀ + γ·d₁ = 0`. -/
theorem defect_line_of_bad (C : Submodule F (ι → A)) {b : ℕ} (hb : 2 ≤ b)
    (hC : NoWeightLE C b) (hnb : b ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0))
    {V₀ V₁ : ι → A} (hV₀ : V₀ ∈ C) (hV₁ : V₁ ∈ C) (d₀ d₁ : A) (x : ι) {γ : F}
    (hev : mcaEvent (F := F) (C : Set (ι → A)) δ
      (V₀ + Pi.single x d₀) (V₁ + Pi.single x d₁) γ) :
    d₀ + γ • d₁ = 0 := by
  obtain ⟨S, hScard, ⟨w, hw, hag⟩, hno⟩ := hev
  by_cases hxS : x ∈ S
  case neg =>
    -- the witness avoids x: (V₀, V₁) explains the stack on S — contradiction
    refine absurd (?_ : pairJointAgreesOn (C : Set (ι → A)) S
      (V₀ + Pi.single x d₀) (V₁ + Pi.single x d₁)) hno
    refine ⟨V₀, hV₀, V₁, hV₁, fun j hj => ?_⟩
    have hjx : j ≠ x := fun h => hxS (h ▸ hj)
    constructor
    · show V₀ j = ((V₀ + Pi.single x d₀ : ι → A)) j
      show V₀ j = V₀ j + (Pi.single x d₀ : ι → A) j
      rw [Pi.single_eq_of_ne hjx, add_zero]
    · show V₁ j = ((V₁ + Pi.single x d₁ : ι → A)) j
      show V₁ j = V₁ j + (Pi.single x d₁ : ι → A) j
      rw [Pi.single_eq_of_ne hjx, add_zero]
  case pos =>
    -- the witness contains x: the on-line codeword is pinned to V₀ + γ•V₁ by distance
    set W : ι → A := V₀ + γ • V₁ with hW
    have hWmem : W ∈ C := C.add_mem hV₀ (C.smul_mem γ hV₁)
    -- the missed-set bound: |univ \ S| ≤ b − 1
    have hmiss : (Finset.univ \ S).card ≤ b - 1 := by
      have hδ1 : δ < 1 := by
        by_contra hge
        push Not at hge
        have hcast : ((b : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hnb
        have : ((b : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
          calc ((b : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := hcast
            _ = 1 * (Fintype.card ι : ℝ≥0) := (one_mul _).symm
            _ ≤ δ * (Fintype.card ι : ℝ≥0) := by gcongr
        exact absurd hδ (not_lt.mpr this)
      have hSR : ((1 : ℝ) - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
        have hcast : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast hScard
        rwa [NNReal.coe_sub hδ1.le, NNReal.coe_one] at hcast
      have hδR : (δ : ℝ) * (Fintype.card ι : ℝ) < (b : ℝ) := by exact_mod_cast hδ
      have hsplit : (Finset.univ \ S).card + S.card = Fintype.card ι := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
        rwa [Finset.card_univ] at h
      have hlt : Fintype.card ι < S.card + b := by
        exact_mod_cast (by nlinarith : (Fintype.card ι : ℝ) < (S.card : ℝ) + (b : ℝ))
      omega
    -- w − W vanishes on S \ {x}, hence is supported on ≤ b points — zero by distance
    have hwW : w = W := by
      have hzero : w - W = 0 := by
        refine hC (w - W) (C.sub_mem hw hWmem)
          ⟨insert x (Finset.univ \ S), ?_, fun j hj => ?_⟩
        · refine le_trans (Finset.card_insert_le _ _) ?_
          omega
        · have hjS : j ∈ S := by
            by_contra hjS
            exact hj (Finset.mem_insert_of_mem
              (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjS⟩))
          have hjx : j ≠ x := by
            intro h
            rw [h] at hj
            exact hj (Finset.mem_insert_self x _)
          have hagj := hag j hjS
          show w j - W j = 0
          rw [sub_eq_zero]
          calc w j = ((V₀ + Pi.single x d₀ : ι → A)) j
                + γ • ((V₁ + Pi.single x d₁ : ι → A)) j := hagj
            _ = V₀ j + γ • V₁ j := by
                show V₀ j + (Pi.single x d₀ : ι → A) j
                  + γ • (V₁ j + (Pi.single x d₁ : ι → A) j) = _
                rw [Pi.single_eq_of_ne hjx, Pi.single_eq_of_ne hjx, add_zero, add_zero]
            _ = W j := rfl
      have h := sub_eq_zero.mp hzero
      exact h
    -- evaluate the agreement at x
    have hagx := hag x hxS
    rw [hwW] at hagx
    have hWx : W x = V₀ x + γ • V₁ x := rfl
    have hux : ((V₀ + Pi.single x d₀ : ι → A)) x + γ • ((V₁ + Pi.single x d₁ : ι → A)) x
        = V₀ x + γ • V₁ x + (d₀ + γ • d₁) := by
      show V₀ x + (Pi.single x d₀ : ι → A) x + γ • (V₁ x + (Pi.single x d₁ : ι → A) x) = _
      rw [Pi.single_eq_same, Pi.single_eq_same]
      module
    rw [hux, hWx] at hagx
    have h0 : V₀ x + γ • V₁ x + (d₀ + γ • d₁) = V₀ x + γ • V₁ x + 0 := by
      rw [add_zero]
      exact hagx.symm
    exact add_left_cancel h0

open Classical in
/-- **The common-core kill**: a stack whose rows are codewords away from a single point has
at most one bad scalar — two distinct defect-line roots annihilate both defects, after
which `(V₀, V₁)` explains every witness. Retires every global-core overlap pattern at every
band, at distance `≥ b + 1`. -/
theorem badScalar_card_le_one_of_core (C : Submodule F (ι → A)) {b : ℕ} (hb : 2 ≤ b)
    (hC : NoWeightLE C b) (hnb : b ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0))
    {V₀ V₁ : ι → A} (hV₀ : V₀ ∈ C) (hV₁ : V₁ ∈ C) (d₀ d₁ : A) (x : ι) :
    (Finset.filter (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ
      (V₀ + Pi.single x d₀) (V₁ + Pi.single x d₁) γ) Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  by_contra hne
  -- two distinct roots of the defect line kill both defects
  have h1 := defect_line_of_bad C hb hC hnb hδ hV₀ hV₁ d₀ d₁ x hγ.2
  have h2 := defect_line_of_bad C hb hC hnb hδ hV₀ hV₁ d₀ d₁ x hγ'.2
  have hd1 : d₁ = 0 := by
    have hsub : (γ - γ') • d₁ = 0 := by
      have := sub_eq_zero.mpr (h1.trans h2.symm)
      calc (γ - γ') • d₁ = (d₀ + γ • d₁) - (d₀ + γ' • d₁) := by module
        _ = 0 := by rw [h1, h2, sub_zero]
    rcases smul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hd0 : d₀ = 0 := by
    have := h1
    rw [hd1, smul_zero, add_zero] at this
    exact this
  -- defects gone: (V₀, V₁) explains γ's witness — contradiction with its obstruction
  obtain ⟨S, hScard, hclose, hno⟩ := hγ.2
  refine hno ⟨V₀, hV₀, V₁, hV₁, fun j hj => ?_⟩
  rw [hd0, hd1, Pi.single_zero]
  exact ⟨by rw [add_zero], by rw [add_zero]⟩

/-! ## Source audit -/

#print axioms defect_line_of_bad
#print axioms badScalar_card_le_one_of_core

end ProximityGap.MCADefectLineKill
