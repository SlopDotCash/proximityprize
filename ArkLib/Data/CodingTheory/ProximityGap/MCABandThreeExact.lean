/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandThreeAssembly
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoExact
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Round 4 (#357): the universal third band — `ε_mca = 3/|F|` exactly on `[2/n, 3/n)`

Companion to the band-3 collapse (`MCABandThreeAssembly`, the `≤ 3/|F|` half): the matching
**triple-spike** lower bound, and the exact value. For every linear code with no nonzero
codeword on `≤ 6` points (distance `≥ 7`), any three distinct positions, any three distinct
scalars, any nonzero alphabet value, and every radius in the third band (`2 ≤ δ·n < 3`):

  `epsMCA_eq_three_div_card_of_dist7` : `ε_mca(C, δ) = 3/|F|`.

**The construction.** The affine pencil through three prescribed vanishing slots:

  `u₁ = −(single i₁ a + single i₂ a + single i₃ a)`,
  `u₀ = γ₁ • single i₁ a + γ₂ • single i₂ a + γ₃ • single i₃ a`,

so `u₀ + γ • u₁ = Σ_x (γ_x − γ) • single i_x a`. At `γ = γ_x` the `x`-th spike vanishes:
the line point agrees with the codeword `0` off the other two slots — a band-3 witness. No
joint explanation exists there: an explaining `v₁` agrees with `u₁` off two slots, so it is
a codeword supported in the three slots (weight `≤ 3 ≤ 6`), hence zero — contradicting the
surviving spike value `−a ≠ 0`. So all three scalars are bad, and the collapse theorem
closes the sandwich.

With bands 1 and 2 (`MCADeltaStarExactPoint`, `MCABandTwoExact`): **the first three steps of
the MCA staircase are exact theorems for every distance-`≥ 7` linear code** — in particular
for every production-scale Reed–Solomon code (where `d = n − k + 1 ≥ 7` at all prize rates
and scales).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandThreeExact

open ProximityGap.MCABandTwoCollapse ProximityGap.MCABandThreeInfra
open ProximityGap.MCABandThreeAssembly ProximityGap.MCABandTwoExact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The triple-spike second row. -/
def trow (i₁ i₂ i₃ : ι) (a : A) : ι → A :=
  -(spike i₁ a + spike i₂ a + spike i₃ a)

/-- The triple-spike first row. -/
def zrow (i₁ i₂ i₃ : ι) (a : A) (γ₁ γ₂ γ₃ : F) : ι → A :=
  γ₁ • spike i₁ a + γ₂ • spike i₂ a + γ₃ • spike i₃ a

/-- The line point at `γ`: `Σ_x (γ_x − γ) • single i_x a`, pointwise. -/
theorem line_point (i₁ i₂ i₃ : ι) (a : A) (γ₁ γ₂ γ₃ γ : F) (j : ι) :
    zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃ j + γ • trow i₁ i₂ i₃ a j
      = (γ₁ - γ) • spike i₁ a j + (γ₂ - γ) • spike i₂ a j + (γ₃ - γ) • spike i₃ a j := by
  show (γ₁ • spike i₁ a + γ₂ • spike i₂ a + γ₃ • spike i₃ a) j
      + γ • (-(spike i₁ a + spike i₂ a + spike i₃ a)) j = _
  show γ₁ • spike i₁ a j + γ₂ • spike i₂ a j + γ₃ • spike i₃ a j
      + γ • (-(spike i₁ a j + spike i₂ a j + spike i₃ a j)) = _
  module

/-- The band-3 witness-size clause: a doubly-punctured universe works when `δ·n ≥ 2`. -/
theorem doubly_punctured_card_clause {δ : ℝ≥0}
    (hδ : 2 ≤ δ * (Fintype.card ι : ℝ≥0)) {i j : ι} (hij : i ≠ j) :
    ((((Finset.univ.erase i).erase j).card : ℝ≥0))
      ≥ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hn2 : 2 ≤ Fintype.card ι := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then i else j)
      (by
        intro x y hxy
        cases x <;> cases y <;> simp at hxy <;>
          first | rfl | exact absurd hxy.symm hij | exact absurd hxy hij)
    simpa using this
  have hcast : ((Fintype.card ι - 1 - 1 : ℕ) : ℝ≥0) = (Fintype.card ι : ℝ≥0) - 2 := by
    have h : ((Fintype.card ι - 1 - 1 : ℕ) : ℝ≥0) + 2 = (Fintype.card ι : ℝ≥0) := by
      exact_mod_cast (by omega : Fintype.card ι - 1 - 1 + 2 = Fintype.card ι)
    exact eq_tsub_of_add_eq h
  rw [ge_iff_le, hcast]
  calc (1 - δ) * (Fintype.card ι : ℝ≥0)
      ≤ (Fintype.card ι : ℝ≥0) - δ * (Fintype.card ι : ℝ≥0) := by
        rw [tsub_mul, one_mul]
    _ ≤ (Fintype.card ι : ℝ≥0) - 2 := tsub_le_tsub_left hδ _

/-- An explaining second row at a doubly-punctured witness is a codeword supported in the
three spike slots — dead by distance. -/
theorem trow_blocks (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    {a : A} (ha : a ≠ 0) {ib ic : ι} (hb : ib ≠ i₁) (hc : ic ≠ i₁)
    {v₁ : ι → A} (hv₁ : v₁ ∈ C)
    (hag : ∀ y ∈ (Finset.univ.erase ib).erase ic, v₁ y = trow i₁ i₂ i₃ a y) :
    False := by
  -- v₁ − trow vanishes off {ib, ic}; trow is supported in the slots; so v₁ is supported in
  -- the union, but we only need: v₁ is zero off {i₁,i₂,i₃} ∪ {ib,ic} and nonzero at i₁.
  have htrow_supp : ∀ y : ι, y ≠ i₁ → y ≠ i₂ → y ≠ i₃ → trow i₁ i₂ i₃ a y = 0 := by
    intro y hy1 hy2 hy3
    show -(spike i₁ a y + spike i₂ a y + spike i₃ a y) = 0
    rw [spike_apply_ne i₁ y a hy1, spike_apply_ne i₂ y a hy2, spike_apply_ne i₃ y a hy3]
    simp
  have hv₁supp : ∀ y : ι, y ≠ i₁ → y ≠ i₂ → y ≠ i₃ → y ≠ ib → y ≠ ic → v₁ y = 0 := by
    intro y hy1 hy2 hy3 hyb hyc
    have hmem : y ∈ (Finset.univ.erase ib).erase ic :=
      Finset.mem_erase.mpr ⟨hyc, Finset.mem_erase.mpr ⟨hyb, Finset.mem_univ y⟩⟩
    rw [hag y hmem]
    exact htrow_supp y hy1 hy2 hy3
  have hzero : v₁ = 0 := by
    refine hC v₁ hv₁ ⟨{i₁, i₂, i₃, ib, ic}, ?_, fun y hy => ?_⟩
    · refine le_trans (Finset.card_insert_le _ _) ?_
      refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
      refine le_trans (Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1) ?_
      have h2 : ({ib, ic} : Finset ι).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      push Not at hy
      exact hv₁supp y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
  -- but v₁ i₁ = trow i₁ = −a ≠ 0
  have hi₁mem : i₁ ∈ (Finset.univ.erase ib).erase ic :=
    Finset.mem_erase.mpr ⟨Ne.symm hc, Finset.mem_erase.mpr ⟨Ne.symm hb, Finset.mem_univ i₁⟩⟩
  have hval := hag i₁ hi₁mem
  rw [hzero] at hval
  have htrow_i₁ : trow i₁ i₂ i₃ a i₁ = -a := by
    show -(spike i₁ a i₁ + spike i₂ a i₁ + spike i₃ a i₁) = -a
    rw [spike_apply_self, spike_apply_ne i₂ i₁ a h12, spike_apply_ne i₃ i₁ a h13]
    simp
  rw [htrow_i₁] at hval
  apply ha
  have : (0 : A) = -a := hval
  rw [← neg_neg a, ← this, neg_zero]

/-- **The spike scalar `γ₁` is bad**: witness `univ \ {i₂, i₃}`, on-line codeword `0`. -/
theorem mcaEvent_tspike (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    {δ : ℝ≥0} (hδ : 2 ≤ δ * (Fintype.card ι : ℝ≥0))
    {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    {a : A} (ha : a ≠ 0) (γ₁ γ₂ γ₃ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ
      (zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃) (trow i₁ i₂ i₃ a) γ₁ := by
  refine ⟨(Finset.univ.erase i₂).erase i₃, doubly_punctured_card_clause hδ h23,
    ⟨0, C.zero_mem, fun y hy => ?_⟩, ?_⟩
  · -- the γ₁ line point vanishes off {i₂, i₃}
    obtain ⟨hy3, hy2'⟩ := Finset.mem_erase.mp hy
    obtain ⟨hy2, _⟩ := Finset.mem_erase.mp hy2'
    show (0 : A) = zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃ y + γ₁ • trow i₁ i₂ i₃ a y
    rw [line_point]
    by_cases hy1 : y = i₁
    · rw [hy1, spike_apply_self, spike_apply_ne i₂ i₁ a h12, spike_apply_ne i₃ i₁ a h13]
      simp
    · rw [spike_apply_ne i₁ y a hy1, spike_apply_ne i₂ y a hy2,
        spike_apply_ne i₃ y a hy3]
      simp
  · rintro ⟨v₀, _, v₁, hv₁, hag⟩
    exact trow_blocks C hC h12 h13 h23 ha (Ne.symm h12) (Ne.symm h13) hv₁
      fun y hy => (hag y hy).2

open Classical in
/-- **Lower half:** the triple-spike stack has three bad scalars, so `ε_mca ≥ 3/|F|`. -/
theorem epsMCA_ge_three_div_card (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    {δ : ℝ≥0} (hδ : 2 ≤ δ * (Fintype.card ι : ℝ≥0))
    {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    {a : A} (ha : a ≠ 0) {γ₁ γ₂ γ₃ : F} (g12 : γ₁ ≠ γ₂) (g13 : γ₁ ≠ γ₃) (g23 : γ₂ ≠ γ₃) :
    (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  -- the three events: by symmetry of the construction under permuting the slots
  have hev1 : mcaEvent (F := F) (C : Set (ι → A)) δ
      (zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃) (trow i₁ i₂ i₃ a) γ₁ :=
    mcaEvent_tspike C hC hδ h12 h13 h23 ha γ₁ γ₂ γ₃
  have hev2 : mcaEvent (F := F) (C : Set (ι → A)) δ
      (zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃) (trow i₁ i₂ i₃ a) γ₂ := by
    have h := mcaEvent_tspike C hC hδ (Ne.symm h12) h23 h13 ha γ₂ γ₁ γ₃
      (i₁ := i₂) (i₂ := i₁) (i₃ := i₃)
    have hz : zrow i₂ i₁ i₃ a γ₂ γ₁ γ₃ = zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃ := by
      unfold zrow
      abel
    have ht : trow i₂ i₁ i₃ a = trow i₁ i₂ i₃ a := by
      unfold trow
      abel
    rwa [hz, ht] at h
  have hev3 : mcaEvent (F := F) (C : Set (ι → A)) δ
      (zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃) (trow i₁ i₂ i₃ a) γ₃ := by
    have h := mcaEvent_tspike C hC hδ (Ne.symm h13) (Ne.symm h23) h12 ha γ₃ γ₁ γ₂
      (i₁ := i₃) (i₂ := i₁) (i₃ := i₂)
    have hz : zrow i₃ i₁ i₂ a γ₃ γ₁ γ₂ = zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃ := by
      unfold zrow
      abel
    have ht : trow i₃ i₁ i₂ a = trow i₁ i₂ i₃ a := by
      unfold trow
      abel
    rwa [hz, ht] at h
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
    ![zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃, trow i₁ i₂ i₃ a])
  have h0 : (![zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃, trow i₁ i₂ i₃ a] :
      WordStack A (Fin 2) ι) 0 = zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃ := rfl
  have h1 : (![zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃, trow i₁ i₂ i₃ a] :
      WordStack A (Fin 2) ι) 1 = trow i₁ i₂ i₃ a := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  have hsub : ({γ₁, γ₂, γ₃} : Finset F) ⊆ Finset.filter (fun γ : F =>
      mcaEvent (F := F) (C : Set (ι → A)) δ
        (zrow i₁ i₂ i₃ a γ₁ γ₂ γ₃) (trow i₁ i₂ i₃ a) γ) Finset.univ := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev3⟩
  have hcard3 : ({γ₁, γ₂, γ₃} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨g12, g13⟩), Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact g23), Finset.card_singleton]
  calc ((3 : ℕ) : ℝ≥0∞) = (({γ₁, γ₂, γ₃} : Finset F).card : ℝ≥0∞) := by rw [hcard3]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

open Classical in
/-- **THE UNIVERSAL THIRD BAND:** `ε_mca(C, δ) = 3/|F|` exactly on `2 ≤ δ·n < 3` for every
linear code of distance `≥ 7` with at least three positions, three field scalars, and a
nonzero alphabet value. With bands 1–2: the first three steps of the MCA staircase are
exact theorems for every such code, including production-scale Reed–Solomon. -/
theorem epsMCA_eq_three_div_card_of_dist7 (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ2 : 2 ≤ δ * (Fintype.card ι : ℝ≥0)) (hδ3 : δ * (Fintype.card ι : ℝ≥0) < 3)
    {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    {a : A} (ha : a ≠ 0) {γ₁ γ₂ γ₃ : F} (g12 : γ₁ ≠ γ₂) (g13 : γ₁ ≠ γ₃) (g23 : γ₂ ≠ γ₃) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = 3 / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_le_three_div_card_of_dist7 C hC hn hδ3)
    (epsMCA_ge_three_div_card C hC hδ2 h12 h13 h23 ha g12 g13 g23)

/-! ## Source audit -/

#print axioms trow_blocks
#print axioms mcaEvent_tspike
#print axioms epsMCA_ge_three_div_card
#print axioms epsMCA_eq_three_div_card_of_dist7

end ProximityGap.MCABandThreeExact
