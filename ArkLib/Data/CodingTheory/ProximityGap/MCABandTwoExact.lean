/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoCollapse
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Round 2 (#357): the universal second band — `ε_mca = 2/|F|` exactly on `[1/n, 2/n)`

Companion to `MCABandTwoCollapse` (the `≤ 2/|F|` upper half): this file supplies the
matching **lower** construction and concludes the exact value. For **every** linear code
with no nonzero codeword supported on `≤ 3` points (distance `≥ 4`), every nonzero alphabet
element, and every radius in the second granularity band (`1 ≤ δ·n < 2`):

  `epsMCA_eq_two_div_card_of_dist4` : `ε_mca(C, δ) = 2 / |F|`.

With R1's `epsMCA_eq_inv_card_of_small_radius` (`= 1/|F|` on `δ·n < 1`), the first **two
steps of the MCA staircase are now exact theorems for every distance-`≥ 4` linear code** —
in particular for the production-scale Reed–Solomon codes of the prize statement. The
staircase opens *linearly* (the spike values `1/q, 2/q`), and the discovered trichotomy
shows the linear opening is conditional on distance: at `d = 3` the second step jumps to
`n/q`, at `d = 2` it does not jump at all.

**The lower construction** (`mcaEvent` at `γ = 0` and `γ = 1`). Take distinct positions
`i₁ ≠ i₂` and the double-spike stack `u₀ := single i₁ a`, `u₁ := single i₂ a − single i₁ a`:

* at `γ = 0` the line point is `single i₁ a`, which agrees with the codeword `0` off `i₁`;
* at `γ = 1` the line point is `single i₂ a`, which agrees with `0` off `i₂`;
* neither has a joint explanation on its punctured universe: an explaining `v₁` would
  satisfy `v₁ = single i₂ a` off `i₁` (resp. symmetric), i.e. `v₁` is a codeword supported
  on `{i₁, i₂}` — weight `≤ 2 < d` forces `v₁ = 0`, contradicting the spike value `a ≠ 0`
  at the surviving position.

So both scalars are bad and `Pr_γ[mcaEvent] ≥ 2/|F|`; the collapse theorem gives `≤ 2/|F|`.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 2 — the staircase program), `MCABandTwoCollapse.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandTwoExact

open ProximityGap.MCABandTwoCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The double-spike stack: `u₀ = single i₁ a`, `u₁ = single i₂ a − single i₁ a`. -/
def spike (i : ι) (a : A) : ι → A := Pi.single i a

theorem spike_apply_self (i : ι) (a : A) : spike i a i = a := by
  unfold spike
  simp

theorem spike_apply_ne (i j : ι) (a : A) (h : j ≠ i) : spike i a j = 0 := by
  unfold spike
  simp [Pi.single_eq_of_ne h]

/-- The witness-size clause holds for a punctured universe whenever `δ·n ≥ 1`. -/
theorem punctured_card_clause {δ : ℝ≥0} (hδ : 1 ≤ δ * (Fintype.card ι : ℝ≥0)) (i : ι) :
    (((Finset.univ.erase i).card : ℝ≥0))
      ≥ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ≥0) = (Fintype.card ι : ℝ≥0) - 1 := by
    have h : ((Fintype.card ι - 1 : ℕ) : ℝ≥0) + 1 = (Fintype.card ι : ℝ≥0) := by
      exact_mod_cast (by omega : Fintype.card ι - 1 + 1 = Fintype.card ι)
    exact eq_tsub_of_add_eq h
  rw [ge_iff_le, hcast]
  calc (1 - δ) * (Fintype.card ι : ℝ≥0)
      ≤ (Fintype.card ι : ℝ≥0) - δ * (Fintype.card ι : ℝ≥0) := by
        rw [tsub_mul, one_mul]
    _ ≤ (Fintype.card ι : ℝ≥0) - 1 := tsub_le_tsub_left hδ _

/-- A codeword supported on two points is zero (distance `≥ 4 ⟹ ≥ 3`). -/
theorem codeword_two_support_zero (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    {v : ι → A} (hv : v ∈ C) (i₁ i₂ : ι) (hsupp : ∀ j, j ≠ i₁ → j ≠ i₂ → v j = 0) :
    v = 0 := by
  refine hC v hv ⟨{i₁, i₂}, ?_, fun j hj => ?_⟩
  · refine le_trans (Finset.card_insert_le _ _) ?_
    rw [Finset.card_singleton]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    push Not at hj
    exact hsupp j hj.1 hj.2

/-- **The `γ = 0` bad event** for the double-spike stack. -/
theorem mcaEvent_spike_zero (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    {δ : ℝ≥0} (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0))
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) {a : A} (ha : a ≠ 0) :
    mcaEvent (F := F) (C : Set (ι → A)) δ
      (spike i₁ a) (spike i₂ a - spike i₁ a) 0 := by
  refine ⟨Finset.univ.erase i₁, punctured_card_clause hδ1 i₁,
    ⟨0, C.zero_mem, fun j hj => ?_⟩, ?_⟩
  · -- the zero codeword equals the γ=0 line point off i₁
    obtain ⟨hji₁, _⟩ := Finset.mem_erase.mp hj
    show (0 : A) = spike i₁ a j + (0 : F) • (spike i₂ a - spike i₁ a) j
    rw [zero_smul, add_zero, spike_apply_ne i₁ j a hji₁]
  · rintro ⟨v₀, _, v₁, hv₁, hag⟩
    -- v₁ agrees with single i₂ a − single i₁ a off i₁, so v₁ is supported on {i₁, i₂}
    have hv₁supp : ∀ j, j ≠ i₁ → j ≠ i₂ → v₁ j = 0 := by
      intro j hj1 hj2
      have h := (hag j (Finset.mem_erase.mpr ⟨hj1, Finset.mem_univ j⟩)).2
      show v₁ j = 0
      rw [h]
      show spike i₂ a j - spike i₁ a j = 0
      rw [spike_apply_ne i₂ j a hj2, spike_apply_ne i₁ j a hj1, sub_zero]
    have hzero := codeword_two_support_zero C hC hv₁ i₁ i₂ hv₁supp
    -- but v₁ i₂ should be the spike value a ≠ 0
    have h := (hag i₂ (Finset.mem_erase.mpr ⟨(Ne.symm hne), Finset.mem_univ i₂⟩)).2
    rw [hzero] at h
    have hval : (0 : A) = a := by
      have := h
      show (0 : A) = a
      calc (0 : A) = (0 : ι → A) i₂ := rfl
        _ = spike i₂ a i₂ - spike i₁ a i₂ := this
        _ = a - 0 := by rw [spike_apply_self, spike_apply_ne i₁ i₂ a (Ne.symm hne)]
        _ = a := sub_zero a
    exact ha hval.symm

/-- **The `γ = 1` bad event** for the double-spike stack. -/
theorem mcaEvent_spike_one (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    {δ : ℝ≥0} (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0))
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) {a : A} (ha : a ≠ 0) :
    mcaEvent (F := F) (C : Set (ι → A)) δ
      (spike i₁ a) (spike i₂ a - spike i₁ a) 1 := by
  refine ⟨Finset.univ.erase i₂, punctured_card_clause hδ1 i₂,
    ⟨0, C.zero_mem, fun j hj => ?_⟩, ?_⟩
  · -- the γ=1 line point is single i₂ a, which is 0 off i₂
    obtain ⟨hji₂, _⟩ := Finset.mem_erase.mp hj
    show (0 : A) = spike i₁ a j + (1 : F) • (spike i₂ a - spike i₁ a) j
    rw [one_smul]
    show (0 : A) = spike i₁ a j + (spike i₂ a j - spike i₁ a j)
    have htel : spike i₁ a j + (spike i₂ a j - spike i₁ a j) = spike i₂ a j := by abel
    rw [htel, spike_apply_ne i₂ j a hji₂]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    -- v₀ agrees with single i₁ a off i₂, so v₀ is supported on {i₁, i₂}
    have hv₀supp : ∀ j, j ≠ i₁ → j ≠ i₂ → v₀ j = 0 := by
      intro j hj1 hj2
      have h := (hag j (Finset.mem_erase.mpr ⟨hj2, Finset.mem_univ j⟩)).1
      rw [h]
      exact spike_apply_ne i₁ j a hj1
    have hzero := codeword_two_support_zero C hC hv₀ i₁ i₂ hv₀supp
    have h := (hag i₁ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩)).1
    rw [hzero] at h
    have hval : (0 : A) = a := by
      calc (0 : A) = (0 : ι → A) i₁ := rfl
        _ = spike i₁ a i₁ := h
        _ = a := spike_apply_self i₁ a
    exact ha hval.symm

open Classical in
/-- **Lower half:** the double-spike stack has (at least) the two bad scalars `0` and `1`,
so `ε_mca ≥ 2/|F|` throughout the band. -/
theorem epsMCA_ge_two_div_card (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    {δ : ℝ≥0} (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0))
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) {a : A} (ha : a ≠ 0) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
    ![spike i₁ a, spike i₂ a - spike i₁ a])
  have h0 : (![spike i₁ a, spike i₂ a - spike i₁ a] : WordStack A (Fin 2) ι) 0
      = spike i₁ a := rfl
  have h1 : (![spike i₁ a, spike i₂ a - spike i₁ a] : WordStack A (Fin 2) ι) 1
      = spike i₂ a - spike i₁ a := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  · -- 2 ≤ #bad scalars: {0, 1} are bad and distinct
    have hsub : ({0, 1} : Finset F) ⊆ Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ
          (spike i₁ a) (spike i₂ a - spike i₁ a) γ) Finset.univ := by
      intro γ hγ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
      rcases hγ with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_spike_zero C hC hδ1 hne ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_spike_one C hC hδ1 hne ha⟩
    have hcard2 : ({0, 1} : Finset F).card = 2 := by
      rw [Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact zero_ne_one), Finset.card_singleton]
    calc ((2 : ℕ) : ℝ≥0∞) = (({0, 1} : Finset F).card : ℝ≥0∞) := by rw [hcard2]
      _ ≤ _ := by
          exact_mod_cast Finset.card_le_card hsub

open Classical in
/-- **THE UNIVERSAL SECOND BAND:** for every linear code of distance `≥ 4` (support form),
every pair of distinct positions, every nonzero alphabet value, and every radius in the
band `1 ≤ δ·n < 2`:

  `ε_mca(C, δ) = 2 / |F|`.

Together with the sub-granularity band (`= 1/|F|` on `δ·n < 1`): the first two steps of the
MCA staircase are exact for every such code — including production-scale Reed–Solomon. -/
theorem epsMCA_eq_two_div_card_of_dist4 (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0)) (hδ2 : δ * (Fintype.card ι : ℝ≥0) < 2)
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) {a : A} (ha : a ≠ 0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = 2 / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_le_two_div_card_of_dist4 C hC hn hδ2)
    (epsMCA_ge_two_div_card C hC hδ1 hne ha)

/-! ## Source audit -/

#print axioms mcaEvent_spike_zero
#print axioms mcaEvent_spike_one
#print axioms epsMCA_ge_two_div_card
#print axioms epsMCA_eq_two_div_card_of_dist4

end ProximityGap.MCABandTwoExact
