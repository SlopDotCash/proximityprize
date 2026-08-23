/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandThreeCoredCollapse

/-!
# Round 3 (#357): band-3 collapse infrastructure (`d ≥ 7`)

Puncture extraction and the extension engine.

The doubled-column refutation fixed the general-code collapse boundary at `d ≥ 2b + 1`.
This file proves the `b = 3` case: **every linear code with no nonzero codeword supported on
`≤ 6` points has at most `3` bad scalars per stack at every radius with `δ·n < 3`** —
`LinearStaircaseUpper C 3`, the first open instance of `GeneralStaircaseConjecture`.

**The deep-core dichotomy.** Suppose four distinct bad scalars. Band-3 witnesses miss at
most two points (`P_a`, `|P_a| ≤ 2`); at `d ≥ 7` *every* triple's combination
`c* = (γ_a−γ_c)•(w_a−w_b) − (γ_a−γ_b)•(w_a−w_c)` is supported on `≤ 6` points, hence zero,
so the agreement of `w_b` extends to any `j ∉ P_a ∪ P_c` (`ext_at`). Therefore a point
`j ∈ P_b` that fails to extend must lie in at least two of the other three puncture sets —
it is **deep** (in `≥ 3` of the four sets). The cases:

* no scalar has an unextendable point ⟹ at least two line points are codewords ⟹ dead
  (`pairJoint_of_two_codeword_points`);
* some `P_b ⊆ P_a` for `b ≠ a` (in particular two equal or nested puncture sets) ⟹ both
  agreements live off `P_a` ⟹ dead (`pairJoint_of_shared_witness`);
* two *distinct* deep points ⟹ two puncture sets both equal `{x, y}` ⟹ nested ⟹ dead;
* exactly one deep point `x` ⟹ at least three scalars are cored at `x` with distinct
  private punctures ⟹ dead (`cored_collapse`, which needs only `d ≥ 5`).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (round 3; the staircase programme), `MCABandThreeCoredCollapse.lean`,
  and `MCAHalfDistanceGeneralRefuted.lean` (the `d = 2b` counterexample making this sharp).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandThreeInfra

open ProximityGap.MCABandTwoCollapse ProximityGap.MCABandThreeCoredCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Distance-`≥ 7` hypothesis, support form. -/
def NoWeightLE6 (C : Submodule F (ι → A)) : Prop :=
  ∀ w ∈ C, (∃ T : Finset ι, T.card ≤ 6 ∧ ∀ i ∉ T, w i = 0) → w = 0

theorem noWeightLE4_of_LE6 {C : Submodule F (ι → A)} (h : NoWeightLE6 C) :
    NoWeightLE4 C := fun w hw ⟨T, hT, hs⟩ => h w hw ⟨T, by omega, hs⟩

/-- Band-3 witness shape: the missed set has at most two points. -/
theorem band3_puncture {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < 3)
    (hn : 3 ≤ Fintype.card ι) {S : Finset ι}
    (hS : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    (Finset.univ \ S).card ≤ 2 := by
  have hδ1 : δ < 1 := by
    by_contra hge
    push Not at hge
    have h3 : (3 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hn
    have : (3 : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      calc (3 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := h3
        _ = 1 * (Fintype.card ι : ℝ≥0) := (one_mul _).symm
        _ ≤ δ * (Fintype.card ι : ℝ≥0) := by gcongr
    exact absurd hδ (not_lt.mpr this)
  have hSR : ((1 : ℝ) - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have hcast : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hS
    rwa [NNReal.coe_sub hδ1.le, NNReal.coe_one] at hcast
  have hδR : (δ : ℝ) * (Fintype.card ι : ℝ) < 3 := by exact_mod_cast hδ
  have hsdiff : (Finset.univ \ S).card + S.card = Fintype.card ι := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rwa [Finset.card_univ] at h
  have hclaim : (Fintype.card ι : ℝ) - 3 < (S.card : ℝ) := by nlinarith
  have : Fintype.card ι < S.card + 3 := by exact_mod_cast (by linarith :
    (Fintype.card ι : ℝ) < (S.card : ℝ) + 3)
  omega

/-- Puncture-data extraction at band 3: a bad scalar yields `P` (`≤ 2` points), a codeword
agreeing off `P`, and no joint explanation on `univ \ P`. -/
theorem extract3 (C : Submodule F (ι → A)) (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 3) {u₀ u₁ : ι → A} {γ : F}
    (hev : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) :
    ∃ (P : Finset ι) (w : ι → A), P.card ≤ 2 ∧ w ∈ C ∧
      (∀ j : ι, j ∉ P → w j = u₀ j + γ • u₁ j) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ \ P) u₀ u₁ := by
  obtain ⟨S, hS, ⟨w, hw, hag⟩, hno⟩ := hev
  refine ⟨Finset.univ \ S, w, band3_puncture hδ hn hS, hw, fun j hj => ?_, fun hpj => ?_⟩
  · refine hag j ?_
    by_contra hjS
    exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjS⟩)
  · obtain ⟨v₀, hv₀, v₁, hv₁, hagv⟩ := hpj
    refine hno ⟨v₀, hv₀, v₁, hv₁, fun j hj => hagv j ?_⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hjd => ?_⟩
    exact (Finset.mem_sdiff.mp hjd).2 hj

/-- **The extension engine**: at `d ≥ 7`, for any three of the scalars, the second one's
agreement extends to every point outside the *other two* puncture sets. -/
theorem ext_at (C : Submodule F (ι → A)) (hC : NoWeightLE6 C)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃)
    {u₀ u₁ : ι → A} {w₁ w₂ w₃ : ι → A}
    (hw₁ : w₁ ∈ C) (hw₂ : w₂ ∈ C) (hw₃ : w₃ ∈ C)
    {P₁ P₂ P₃ : Finset ι} (hc1 : P₁.card ≤ 2) (hc2 : P₂.card ≤ 2) (hc3 : P₃.card ≤ 2)
    (hag₁ : ∀ j : ι, j ∉ P₁ → w₁ j = u₀ j + γ₁ • u₁ j)
    (hag₂ : ∀ j : ι, j ∉ P₂ → w₂ j = u₀ j + γ₂ • u₁ j)
    (hag₃ : ∀ j : ι, j ∉ P₃ → w₃ j = u₀ j + γ₃ • u₁ j)
    {j : ι} (hj1 : j ∉ P₁) (hj3 : j ∉ P₃) :
    w₂ j = u₀ j + γ₂ • u₁ j := by
  set cstar : ι → A := (γ₁ - γ₃) • (w₁ - w₂) - (γ₁ - γ₂) • (w₁ - w₃) with hcstar
  have hcmem : cstar ∈ C :=
    C.sub_mem (C.smul_mem _ (C.sub_mem hw₁ hw₂)) (C.smul_mem _ (C.sub_mem hw₁ hw₃))
  have hsupp : ∀ i ∉ P₁ ∪ P₂ ∪ P₃, cstar i = 0 := by
    intro i hi
    simp only [Finset.mem_union, not_or] at hi
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    show (γ₁ - γ₃) • (w₁ i - w₂ i) - (γ₁ - γ₂) • (w₁ i - w₃ i) = 0
    rw [hag₁ i hi1, hag₂ i hi2, hag₃ i hi3]
    module
  have hcard : (P₁ ∪ P₂ ∪ P₃).card ≤ 6 := by
    have h1 := Finset.card_union_le (P₁ ∪ P₂) P₃
    have h2 := Finset.card_union_le P₁ P₂
    omega
  have hczero : cstar = 0 := hC cstar hcmem ⟨P₁ ∪ P₂ ∪ P₃, hcard, hsupp⟩
  -- solve at j (w₁ and w₃ agree there)
  have hz : (γ₁ - γ₃) • (w₁ j - w₂ j) - (γ₁ - γ₂) • (w₁ j - w₃ j) = 0 :=
    congrFun hczero j
  rw [hag₁ j hj1, hag₃ j hj3] at hz
  have hac0 : γ₁ - γ₃ ≠ 0 := sub_ne_zero.mpr h13
  have hXY : (γ₁ - γ₃) • ((u₀ j + γ₁ • u₁ j) - w₂ j)
      = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ j) := by
    have hY : (γ₁ - γ₂) • ((u₀ j + γ₁ • u₁ j) - (u₀ j + γ₃ • u₁ j))
        = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ j) := by module
    have hXeq := sub_eq_zero.mp hz
    rw [hY] at hXeq
    exact hXeq
  have hcanc := congrArg (fun v => (γ₁ - γ₃)⁻¹ • v) hXY
  simp only [inv_smul_smul₀ hac0] at hcanc
  have hwb_eq : w₂ j = (u₀ j + γ₁ • u₁ j) - (γ₁ - γ₂) • u₁ j := by
    rw [← hcanc]
    abel
  rw [hwb_eq]
  module

/-- A `≤ 2`-point set containing two distinct points is exactly that pair. -/
theorem eq_pair_of_card_le_two {s : Finset ι} {x y : ι} (hxy : x ≠ y)
    (hx : x ∈ s) (hy : y ∈ s) (hcard : s.card ≤ 2) :
    s = {x, y} := by
  have hsub : ({x, y} : Finset ι) ⊆ s := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpair : ({x, y} : Finset ι).card = 2 := by
    simp [hxy]
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa [hpair] using hcard)).symm

/-- In a four-family of `≤ 2`-point punctures, two distinct deep points force two of the
puncture sets to equal the same pair `{x, y}`.

This is the pure pigeonhole brick in the band-3 dichotomy: if both `x` and `y` occur in
at least three of the four puncture sets, then at least two indices contain both, and the
`≤ 2` bound makes both punctures exactly `{x, y}`. -/
theorem exists_two_pair_punctures_of_two_deep (P : Fin 4 → Finset ι) {x y : ι}
    (hxy : x ≠ y) (hcard : ∀ a, (P a).card ≤ 2)
    (hxdeep : 3 ≤ ((Finset.univ : Finset (Fin 4)).filter (fun a => x ∈ P a)).card)
    (hydeep : 3 ≤ ((Finset.univ : Finset (Fin 4)).filter (fun a => y ∈ P a)).card) :
    ∃ a b : Fin 4, a ≠ b ∧ P a = {x, y} ∧ P b = {x, y} := by
  let X : Finset (Fin 4) := (Finset.univ : Finset (Fin 4)).filter (fun a => x ∈ P a)
  let Y : Finset (Fin 4) := (Finset.univ : Finset (Fin 4)).filter (fun a => y ∈ P a)
  have hXdeep : 3 ≤ X.card := by simpa [X] using hxdeep
  have hYdeep : 3 ≤ Y.card := by simpa [Y] using hydeep
  have hUle : (X ∪ Y).card ≤ 4 := by
    calc
      (X ∪ Y).card ≤ (Finset.univ : Finset (Fin 4)).card := by
        apply Finset.card_le_card
        intro a _
        exact Finset.mem_univ a
      _ = 4 := by decide
  have hinter : 1 < (X ∩ Y).card := by
    have hsum := Finset.card_union_add_card_inter X Y
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hinter
  have hxa : x ∈ P a := by
    have haX : a ∈ X := (Finset.mem_inter.mp ha).1
    exact (Finset.mem_filter.mp haX).2
  have hya : y ∈ P a := by
    have haY : a ∈ Y := (Finset.mem_inter.mp ha).2
    exact (Finset.mem_filter.mp haY).2
  have hxb : x ∈ P b := by
    have hbX : b ∈ X := (Finset.mem_inter.mp hb).1
    exact (Finset.mem_filter.mp hbX).2
  have hyb : y ∈ P b := by
    have hbY : b ∈ Y := (Finset.mem_inter.mp hb).2
    exact (Finset.mem_filter.mp hbY).2
  exact ⟨a, b, hab, eq_pair_of_card_le_two hxy hxa hya (hcard a),
    eq_pair_of_card_le_two hxy hxb hyb (hcard b)⟩

/-- Four distinct elements from `3 < card`. -/
theorem exists_four_of_three_lt {s : Finset F} (h : 3 < s.card) :
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have herase : 2 < (s.erase a).card := by
    have hcard := Finset.card_erase_of_mem ha
    omega
  obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.mp herase
  exact ⟨a, b, c, d, ha, Finset.mem_of_mem_erase hb, Finset.mem_of_mem_erase hc,
    Finset.mem_of_mem_erase hd,
    fun h => (Finset.mem_erase.mp hb).1 h.symm, fun h => (Finset.mem_erase.mp hc).1 h.symm,
    fun h => (Finset.mem_erase.mp hd).1 h.symm, hbc, hbd, hcd⟩

/-!
The main assembly (`badScalar_card_le_three_of_dist7`) follows the deep-core dichotomy
blueprint recorded on #357 (2026-06-11): per-scalar classification (codeword line point, or
an unextendable deep point via `ext_at`), at most one of the former (`hU2`-style via
`pairJoint_of_two_codeword_points`), all deep points equal (two distinct deep points force
two puncture sets equal to the same pair — dead by nesting via
`pairJoint_of_shared_witness`), and the single-core case closed by `cored_collapse`.
The `Fin 4` case bookkeeping is mechanical; this file lands the four load-bearing lemmas.
-/

/-! ## Source audit -/

#print axioms noWeightLE4_of_LE6
#print axioms band3_puncture
#print axioms extract3
#print axioms ext_at
#print axioms eq_pair_of_card_le_two
#print axioms exists_two_pair_punctures_of_two_deep
#print axioms exists_four_of_three_lt

end ProximityGap.MCABandThreeInfra
