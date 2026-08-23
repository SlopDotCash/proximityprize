/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainEngine
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# LYM antichain bounds for MCA witness families (#357)

`MCAAntichainEngine.lean` proves that witnesses of distinct MCA-bad scalars form an
antichain and uses the elementary granularity case to get the sharp `n/q` first-jump
upper bound. This file starts the registered general-`δ` extension by importing the
Mathlib LYM inequality and proving the reusable large-layer antichain bound:

  if every set in an antichain has size at least `t` and `t ≥ n/2`, then the family has
  at most `Nat.choose n t` members.

This is the combinatorial core of the planned universal staircase ceiling
`ε_mca ≤ C(n,⌈(1−δ)n⌉)/q` in the half-radius regime.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCAWitnessCountEngine
open ProximityGap.MCAAntichainEngine

namespace ProximityGap.MCAAntichainLYM

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Binomial coefficients are monotone on the left half of a fixed row. -/
theorem nat_choose_mono_of_le_half_right {a b n : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction hab using Nat.decreasingInduction with
  | self => rfl
  | of_succ k hk ih =>
      exact (Nat.choose_le_succ_of_lt_half_left (hk.trans_le hb)).trans ih

/-- Binomial coefficients are antitone on the right half of a fixed row. -/
theorem nat_choose_anti_of_half_le_left {t k n : ℕ} (hhalf : n ≤ 2 * t)
    (htk : t ≤ k) (hk : k ≤ n) :
    n.choose k ≤ n.choose t := by
  have ht : t ≤ n := htk.trans hk
  rw [← Nat.choose_symm hk, ← Nat.choose_symm ht]
  refine nat_choose_mono_of_le_half_right (Nat.sub_le_sub_left htk n) ?_
  exact Nat.le_div_iff_mul_le (by norm_num : 0 < 2) |>.2 (by omega)

open Classical in
/-- **Large-layer LYM bound.** If an antichain of subsets of a finite `n`-set lies entirely
in layers of size at least `t`, and `t ≥ n/2`, then it has at most `C(n,t)` members. -/
theorem antichain_card_le_choose_of_forall_card_ge
    (𝒜 : Finset (Finset ι))
    (hanti : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset ι)))
    {t : ℕ} (hhalf : Fintype.card ι ≤ 2 * t)
    (hlarge : ∀ S ∈ 𝒜, t ≤ S.card) :
    𝒜.card ≤ (Fintype.card ι).choose t := by
  by_cases ht : t ≤ Fintype.card ι
  · have hchoose_pos : 0 < (((Fintype.card ι).choose t : ℕ) : ℚ≥0) :=
      Nat.cast_pos.2 (Nat.choose_pos ht)
    have hsum :
        ∑ S ∈ 𝒜, (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹ ≤ 1 := by
      calc
        ∑ S ∈ 𝒜, (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹
            ≤ ∑ S ∈ 𝒜, (((Fintype.card ι).choose S.card : ℕ) : ℚ≥0)⁻¹ := by
              gcongr with S hS
              · exact Nat.cast_pos.2 (Nat.choose_pos S.card_le_univ)
              · exact nat_choose_anti_of_half_le_left hhalf (hlarge S hS) S.card_le_univ
        _ ≤ 1 := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
          (𝕜 := ℚ≥0) hanti
    simpa [mul_inv_le_iff₀' hchoose_pos] using hsum
  · have hempty : 𝒜 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro S hS
      exact not_lt_of_ge (hlarge S hS) (lt_of_le_of_lt S.card_le_univ (lt_of_not_ge ht))
    simp [hempty]

open Classical in
/-- **LYM bad-scalar cap from a large-witness threshold.** If every legal witness at radius
`δ` has size at least `t`, and `t ≥ n/2`, then every stack has at most `C(n,t)` bad scalars.

The proof chooses one witness for each bad scalar. The nesting-collapse lemma makes the chosen
witnesses an antichain, and the large-layer LYM bound counts that antichain. -/
theorem badScalar_card_le_choose_of_forced_large_witness
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t)
    (hforce : ∀ S : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) →
        t ≤ S.card)
    (u : WordStack A (Fin 2) ι) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)).card
      ≤ (Fintype.card ι).choose t := by
  let G : Finset F := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
  let event : G → Prop := fun γ =>
    mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) (γ : F)
  have event_spec : ∀ γ : G, event γ := by
    intro γ
    exact (Finset.mem_filter.mp γ.property).2
  let W : G → Finset ι := fun γ => Classical.choose (event_spec γ)
  have W_spec : ∀ γ : G,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ ((W γ).card : ℝ≥0) ∧
      (∃ w ∈ C, ∀ i ∈ W γ, w i = u 0 i + (γ : F) • u 1 i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (W γ) (u 0) (u 1) := by
    intro γ
    exact Classical.choose_spec (event_spec γ)
  let 𝒲 : Finset (Finset ι) := Finset.univ.image W
  have hWinj : Function.Injective W := by
    intro γ γ' hW
    apply Subtype.ext
    have hlineγ : ∃ w ∈ C, ∀ i ∈ W γ', w i = u 0 i + (γ : F) • u 1 i := by
      obtain ⟨w, hwC, hw⟩ := (W_spec γ).2.1
      exact ⟨w, hwC, fun i hi => hw i (by simpa [hW] using hi)⟩
    exact unique_bad_gamma_common_witness C (W γ') (u 0) (u 1)
      (W_spec γ').2.2 hlineγ (W_spec γ').2.1
  have hcard : G.card = 𝒲.card := by
    rw [← Fintype.card_coe G]
    exact (Finset.card_image_of_injective _ hWinj).symm
  have hanti : IsAntichain (· ⊆ ·) (𝒲 : Set (Finset ι)) := by
    intro S hS T hT hne hsub
    rw [Finset.mem_coe, Finset.mem_image] at hS hT
    obtain ⟨γ, -, rfl⟩ := hS
    obtain ⟨γ', -, rfl⟩ := hT
    have hscalar : (γ : F) = (γ' : F) :=
      bad_scalar_eq_of_witness_subset C hsub (W_spec γ).2.1 (W_spec γ).2.2
        (W_spec γ').2.1
    have hγ : γ = γ' := Subtype.ext hscalar
    exact hne (by rw [hγ])
  have hlarge : ∀ S ∈ 𝒲, t ≤ S.card := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨γ, -, rfl⟩ := hS
    exact hforce (W γ) (W_spec γ).1
  calc
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)).card
        = G.card := rfl
    _ = 𝒲.card := hcard
    _ ≤ (Fintype.card ι).choose t :=
      antichain_card_le_choose_of_forall_card_ge 𝒲 hanti hhalf hlarge

/-- The natural MCA witness ceiling lies in the upper half of the Boolean lattice whenever
`δ ≤ 1/2`. -/
theorem mcaWitnessCeil_half_large (δ : ℝ≥0) (hδ : δ ≤ (1 / 2 : ℝ≥0)) :
    Fintype.card ι
      ≤ 2 * ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by
  set t : ℕ := ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hceil : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (t : ℝ≥0) := by
    rw [htdef]
    exact Nat.le_ceil _
  have hδ1 : δ ≤ 1 := le_trans hδ (by norm_num)
  have hceilR :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (t : ℝ) := by
    have hcoe := NNReal.coe_le_coe.mpr hceil
    rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one, NNReal.coe_natCast,
      NNReal.coe_natCast] at hcoe
  have hδR : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ
  have hnR : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hR : (Fintype.card ι : ℝ) ≤ 2 * (t : ℝ) := by nlinarith
  exact_mod_cast hR

open Classical in
/-- **Ceiling LYM bad-scalar cap.** If the natural witness ceiling is in the upper half of
the Boolean lattice, every stack has at most `C(n,⌈(1−δ)n⌉)` MCA-bad scalars. -/
theorem badScalar_card_le_choose_ceil
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hhalf :
      Fintype.card ι
        ≤ 2 * ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (u : WordStack A (Fin 2) ι) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)).card
      ≤ (Fintype.card ι).choose
          ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ :=
  badScalar_card_le_choose_of_forced_large_witness C δ hhalf
    (by
      intro S hS
      exact Nat.ceil_le.mpr hS)
    u

open Classical in
/-- **LYM MCA upper bound.** A radius whose legal witnesses all lie in layers `≥ t ≥ n/2`
has `ε_mca(C,δ) ≤ C(n,t)/|F|` for every linear code. This is the general half-radius
antichain ceiling promised by the granularity theorem. -/
theorem epsMCA_le_choose_div_of_forced_large_witness
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {t : ℕ}
    (hhalf : Fintype.card ι ≤ 2 * t)
    (hforce : ∀ S : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) →
        t ≤ S.card) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι).choose t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_choose_of_forced_large_witness C δ hhalf hforce u

open Classical in
/-- **Ceiling LYM MCA upper bound.** In the upper-half regime, the universal MCA error is
bounded by the size of the threshold layer divided by the field size:
`ε_mca(C,δ) ≤ C(n,⌈(1−δ)n⌉)/|F|`. -/
theorem epsMCA_le_choose_ceil_div
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hhalf :
      Fintype.card ι
        ≤ 2 * ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι).choose
          ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_choose_div_of_forced_large_witness C δ hhalf
    (by
      intro S hS
      exact Nat.ceil_le.mpr hS)

open Classical in
/-- **Half-radius LYM MCA upper bound.** For every `δ ≤ 1/2`, the ceiling layer is in the
upper half of the Boolean lattice, so the universal LYM ceiling applies directly. -/
theorem epsMCA_le_choose_ceil_div_of_delta_le_half
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ (1 / 2 : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι).choose
          ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_choose_ceil_div C δ (mcaWitnessCeil_half_large δ hδ)

#print axioms nat_choose_mono_of_le_half_right
#print axioms nat_choose_anti_of_half_le_left
#print axioms antichain_card_le_choose_of_forall_card_ge
#print axioms badScalar_card_le_choose_of_forced_large_witness
#print axioms mcaWitnessCeil_half_large
#print axioms badScalar_card_le_choose_ceil
#print axioms epsMCA_le_choose_div_of_forced_large_witness
#print axioms epsMCA_le_choose_ceil_div
#print axioms epsMCA_le_choose_ceil_div_of_delta_le_half

end ProximityGap.MCAAntichainLYM
