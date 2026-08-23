/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness

/-!
# The boundary defect bound: `≤ n − 1` bad scalars at `3 ∤ n` on the `d = 5` row (#357)

The defect half of the band-3 boundary law `n − [3 ∤ n]` (closing-audit item 4,
follow-up named in `BoundarySupExactness.lean`): for any linear code with no nonzero
codeword of weight `≤ 4` (distance `≥ 5`) on a domain of size **not divisible by 3**,
every stack carries at most **`n − 1`** bad scalars at band-3 radii
(`boundaryDefect_badScalars_card_le`), hence `ε_mca ≤ (n−1)/|F|`
(`boundaryDefect_epsMCA_le`).

This matches the probe law exhaustively: `(8,4,17) = 7 = n−1`, `(9,5,19) = 9 = n`,
`(12,8,13) = 12 = n` (`probe_boundary_sup_exactness.py`), and the fleet's
boundary-row data (`n = 6: 6`, `n = 8: 7`, `n = 10: 9`, `n = 12: 12`).  Combined with
the in-tree `(F₁₇, μ₈, 4)` seven-certificate (`DeltaStarSecondPinF17Maximal`) the
`n = 8` defect row is **exact**.  Production smooth domains have `n = 2^μ`, so `3 ∤ n`
always — this is the sharp production form of the boundary cap.

**The mechanism (the mod-3 tightness argument).**  The clump induction of
`BoundarySupExactness` bounds `|S| ≤ |⋃ E_γ|`.  Equality requires every recursion step
tight: every frame is a full 3-point clump with 3 absorbed members, consuming its three
points exactly — so `|⋃ E_γ|` is a sum of 3s.  The refined invariant, for families with
all supports of size exactly 2 (which deviance forces after the first step):

  `3 ∤ |⋃_{γ∈S} E_γ|  →  |S| < |⋃_{γ∈S} E_γ|`  (`strict` in the induction below),

because: a partnered step has `|T| = 3` (same-support pairs are killed: the pair's
difference frame would jointly explain both maximal witnesses) and loses nothing only
if the deviant union misses `T` exactly and recursively ties, forcing `3 ∣ u` down the
chain; an isolated step removes a disjoint 2-set, and `3 ∤ u` with `u = u' + 2` and
`3 ∣ u'` still loses one because `|S'| = u'` can only tie, never exceed.  Members with
supports of size `≤ 1` cannot be deviants (deviance forces `|E| = 2`), so they are
swallowed by the first frame, and the all-size-2 invariant propagates.

**Honest scope:** the `≤` half only.  The matching `n−1` certificate family at general
`3 ∤ n` ("two coset triangles + an extra pair") is probe-grade; at `n = 8` it is in-tree
(`DeltaStarSecondPinF17Maximal`), making that row exact.  Bands `b ≥ 4` remain open as
scoped in `BoundarySupExactness.lean`.

## References

Issue #357; `BoundarySupExactness.lean` (the `≤ n` engine this refines),
`DeltaStarSecondPinF17Maximal.lean` (the matching `n = 8` certificate),
`CosetCliqueBoundary.lean` (the `3 ∣ n` certificate).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.BoundaryDefectBound

open scoped NNReal ENNReal ProbabilityTheory
open Finset
open ProximityGap Code
open ProximityGap.SpikeFloor
open ProximityGap.MCAThresholdLedger
open ProximityGap.StripSupExactness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The boundary defect bound.**  For any linear code with no nonzero codeword of
weight `≤ 4` (distance `≥ 5`), on a domain with `3 ∤ n` and `3 ≤ n`, any radius with
`δ·n < 3`, and any stack: at most `n − 1` bad scalars. -/
theorem boundaryDefect_badScalars_card_le (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C 4)
    (h3 : ¬ (3 ∣ Fintype.card ι)) (hn3 : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((3 : ℕ) : ℝ≥0)) (u₀ u₁ : ι → A) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ Fintype.card ι - 1 := by
  set B := Finset.univ.filter
    (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) with hB
  have hex : ∀ γ : F, γ ∈ B → ∃ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2
  choose! T hTsz hwEx hno using hex
  choose! w hwC hwAg using hwEx
  set E : F → Finset ι :=
    fun γ => Finset.univ.filter (fun i => w γ i ≠ u₀ i + γ • u₁ i) with hEdef
  have hagree : ∀ γ, ∀ i, i ∉ E γ → w γ i = u₀ i + γ • u₁ i := by
    intro γ i hi
    by_contra hne
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
  have hEsub : ∀ γ ∈ B, E γ ⊆ (T γ)ᶜ := by
    intro γ hγ i hi
    rw [Finset.mem_compl]
    intro hiT
    exact (Finset.mem_filter.mp hi).2 (hwAg γ hγ i hiT)
  have hEcard : ∀ γ ∈ B, (E γ).card ≤ 2 := by
    intro γ hγ
    have h1 := Finset.card_le_card (hEsub γ hγ)
    have h2 := witness_compl_card_le (j := 3)
      (by exact_mod_cast hδ) (hTsz γ hγ)
    omega
  have hnoE : ∀ γ ∈ B, ¬ pairJointAgreesOn (C : Set (ι → A)) ((E γ)ᶜ) u₀ u₁ := by
    intro γ hγ hjoint
    obtain ⟨v₀, hv₀, v₁, hv₁, hall⟩ := hjoint
    refine hno γ hγ ⟨v₀, hv₀, v₁, hv₁, fun i hi => hall i ?_⟩
    rw [Finset.mem_compl]
    intro hiE
    exact (Finset.mem_filter.mp hiE).2 (hwAg γ hγ i hi)
  -- ===== shared frame machinery (as in BoundarySupExactness, weight budget 4) =====
  -- pinning + absorption + escape, packaged as: the absorbed sub-family of any
  -- partnered pair injects into the pair's support union.
  have hframe : ∀ γ₁ ∈ B, ∀ γ₂ ∈ B, γ₁ ≠ γ₂ →
      ∀ S : Finset F, S ⊆ B →
      (S.filter (fun m => ((E m ∪ (E γ₁ ∪ E γ₂)).card ≤ 4))).card
        ≤ (E γ₁ ∪ E γ₂).card := by
    intro γ₁ hγ₁ γ₂ hγ₂ hne S hSB
    set T₃ := E γ₁ ∪ E γ₂ with hT₃
    set AS := S.filter (fun m => ((E m ∪ T₃).card ≤ 4)) with hAS
    have h12 : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    set D : ι → A := (γ₁ - γ₂)⁻¹ • (w γ₁ - w γ₂) with hD
    have hDC : D ∈ C := C.smul_mem _ (C.sub_mem (hwC γ₁ hγ₁) (hwC γ₂ hγ₂))
    set U : ι → A := w γ₁ - γ₁ • D with hU
    have hUC : U ∈ C := C.sub_mem (hwC γ₁ hγ₁) (C.smul_mem _ hDC)
    have hdiff : (γ₁ - γ₂) • D = w γ₁ - w γ₂ := by
      rw [hD, smul_smul, mul_inv_cancel₀ h12, one_smul]
    have hw₁ : w γ₁ = U + γ₁ • D := by rw [hU]; abel
    have hpin : ∀ x, x ∉ T₃ → u₁ x = D x ∧ u₀ x = U x := by
      intro x hx
      rw [hT₃, Finset.mem_union] at hx
      push Not at hx
      have ha₁ := hagree γ₁ x hx.1
      have ha₂ := hagree γ₂ x hx.2
      have hsub : (γ₁ - γ₂) • u₁ x = (γ₁ - γ₂) • D x := by
        have hDx : (γ₁ - γ₂) • D x = w γ₁ x - w γ₂ x := by
          have := congrFun hdiff x
          simpa using this
        rw [hDx, ha₁, ha₂, sub_smul]
        abel
      have hu₁ : u₁ x = D x := by
        have := congrArg (fun z => (γ₁ - γ₂)⁻¹ • z) hsub
        simpa [smul_smul, inv_mul_cancel₀ h12] using this
      refine ⟨hu₁, ?_⟩
      have hux : u₀ x + γ₁ • u₁ x = U x + γ₁ • D x := by
        rw [← ha₁, hw₁]; simp
      rw [hu₁] at hux
      exact add_right_cancel hux
    have habs : ∀ m ∈ AS, w m = U + m • D := by
      intro m hm
      obtain ⟨hmS, hm4⟩ := Finset.mem_filter.mp hm
      have hmB : m ∈ B := hSB hmS
      refine codeword_eq_of_eq_off C hC (hwC m hmB)
        (C.add_mem hUC (C.smul_mem m hDC)) (B := E m ∪ T₃) hm4 ?_
      intro x hx
      rw [Finset.mem_union] at hx
      push Not at hx
      obtain ⟨hu₁, hu₀⟩ := hpin x hx.2
      rw [hagree m x hx.1, hu₁, hu₀]
      simp
    have hesc : ∀ m : F, m ∈ AS → ∃ x : ι, x ∈ T₃ ∧ u₁ x ≠ D x ∧
        m • (u₁ x - D x) = U x - u₀ x := by
      intro m hm
      have hmB : m ∈ B := hSB (Finset.mem_filter.mp hm).1
      have hfail : ¬ ∀ i ∈ (E m)ᶜ, U i = u₀ i ∧ D i = u₁ i := by
        intro hall
        exact hnoE m hmB ⟨U, hUC, D, hDC, hall⟩
      push Not at hfail
      obtain ⟨x, hxc, hxne⟩ := hfail
      have hxE : x ∉ E m := Finset.mem_compl.mp hxc
      have hlin : u₀ x + m • u₁ x = U x + m • D x := by
        rw [← hagree m x hxE, habs m hm]; simp
      have hu₁ne : u₁ x ≠ D x := by
        intro h
        rw [h] at hlin
        exact hxne (add_right_cancel hlin).symm h.symm
      refine ⟨x, ?_, hu₁ne, ?_⟩
      · by_contra hxT
        exact hu₁ne (hpin x hxT).1
      · calc m • (u₁ x - D x)
            = (u₀ x + m • u₁ x) - u₀ x - m • D x := by rw [smul_sub]; abel
          _ = (U x + m • D x) - u₀ x - m • D x := by rw [hlin]
          _ = U x - u₀ x := by abel
    choose! ξ hξT hξne hξeq using hesc
    have hinj : Set.InjOn ξ AS := by
      intro a ha b hb hab
      by_contra hne'
      have hsubz : (a - b) • (u₁ (ξ a) - D (ξ a)) = 0 := by
        rw [sub_smul, hξeq a ha, hab, hξeq b hb]
        abel
      have hv : u₁ (ξ a) - D (ξ a) ≠ 0 := sub_ne_zero.mpr (hξne a ha)
      have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hne'
      have hz : u₁ (ξ a) - D (ξ a) = 0 := by
        have := congrArg (fun z => (a - b)⁻¹ • z) hsubz
        simpa [smul_smul, inv_mul_cancel₀ hab0] using this
      exact hv hz
    exact Finset.card_le_card_of_injOn ξ (fun m hm => hξT m hm) hinj
  -- ===== the same-support kill: distinct bad scalars have distinct supports =====
  have hkill : ∀ γ₁ ∈ B, ∀ γ₂ ∈ B, γ₁ ≠ γ₂ → E γ₁ ≠ E γ₂ := by
    intro γ₁ hγ₁ γ₂ hγ₂ hne heq
    have h12 : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    set D : ι → A := (γ₁ - γ₂)⁻¹ • (w γ₁ - w γ₂) with hD
    have hDC : D ∈ C := C.smul_mem _ (C.sub_mem (hwC γ₁ hγ₁) (hwC γ₂ hγ₂))
    set U : ι → A := w γ₁ - γ₁ • D with hU
    have hUC : U ∈ C := C.sub_mem (hwC γ₁ hγ₁) (C.smul_mem _ hDC)
    have hdiff : (γ₁ - γ₂) • D = w γ₁ - w γ₂ := by
      rw [hD, smul_smul, mul_inv_cancel₀ h12, one_smul]
    have hw₁ : w γ₁ = U + γ₁ • D := by rw [hU]; abel
    refine hnoE γ₁ hγ₁ ⟨U, hUC, D, hDC, fun x hx => ?_⟩
    have hxE₁ : x ∉ E γ₁ := Finset.mem_compl.mp hx
    have hxE₂ : x ∉ E γ₂ := heq ▸ hxE₁
    have ha₁ := hagree γ₁ x hxE₁
    have ha₂ := hagree γ₂ x hxE₂
    have hsub : (γ₁ - γ₂) • u₁ x = (γ₁ - γ₂) • D x := by
      have hDx : (γ₁ - γ₂) • D x = w γ₁ x - w γ₂ x := by
        have := congrFun hdiff x
        simpa using this
      rw [hDx, ha₁, ha₂, sub_smul]
      abel
    have hu₁ : u₁ x = D x := by
      have := congrArg (fun z => (γ₁ - γ₂)⁻¹ • z) hsub
      simpa [smul_smul, inv_mul_cancel₀ h12] using this
    have hux : u₀ x + γ₁ • u₁ x = U x + γ₁ • D x := by
      rw [← ha₁, hw₁]; simp
    rw [hu₁] at hux
    exact ⟨(add_right_cancel hux).symm, hu₁.symm⟩
  -- ===== the strict (mod-3) induction on all-size-2 sub-families =====
  have key : ∀ m : ℕ, ∀ S : Finset F, S ⊆ B → S.card ≤ m →
      (∀ γ ∈ S, (E γ).card = 2) →
      S.card ≤ (S.biUnion E).card ∧
        (¬ (3 ∣ (S.biUnion E).card) → S.card < (S.biUnion E).card) := by
    intro m
    induction m with
    | zero =>
      intro S _ hS0 _
      have hS : S.card = 0 := by omega
      have hSe : S = ∅ := Finset.card_eq_zero.mp hS
      subst hSe
      simp
    | succ m ih =>
      intro S hSB hScard hall2
      rcases Finset.eq_empty_or_nonempty S with hS0 | ⟨γs, hγs⟩
      · subst hS0; simp
      by_cases hS1 : S.card ≤ 1
      · -- singleton: support has exactly 2 points; 1 < 2
        have hcard1 : S.card = 1 := by
          have : 0 < S.card := Finset.card_pos.mpr ⟨γs, hγs⟩
          omega
        have hsub : E γs ⊆ S.biUnion E :=
          fun x hx => Finset.mem_biUnion.mpr ⟨γs, hγs, hx⟩
        have h2 := hall2 γs hγs
        have hbig := Finset.card_le_card hsub
        constructor
        · omega
        · intro _
          omega
      · push Not at hS1
        by_cases hpart : ∃ γ' ∈ S, γ' ≠ γs ∧ (E γs ∪ E γ').card ≤ 3
        · -- partnered: |T₃| = 3 exactly (same-support kill), dichotomy, telescoping
          obtain ⟨γ', hγ', hne', hsmall⟩ := hpart
          set T₃ := E γs ∪ E γ' with hT₃def
          have hT₃3 : T₃.card = 3 := by
            have hne2 : E γs ≠ E γ' :=
              hkill γs (hSB hγs) γ' (hSB hγ') (Ne.symm hne')
            have h1 := hall2 γs hγs
            have h2 := hall2 γ' hγ'
            have hint := Finset.card_union_add_card_inter (E γs) (E γ')
            rw [← hT₃def] at hint
            -- |∩| ≤ 1: equal-size-2 sets with |∩| = 2 are equal
            have hint1 : (E γs ∩ E γ').card ≤ 1 := by
              by_contra hgt
              push Not at hgt
              have hsub1 : E γs ∩ E γ' ⊆ E γs := Finset.inter_subset_left
              have hsub2 : E γs ∩ E γ' ⊆ E γ' := Finset.inter_subset_right
              have hc1 := Finset.card_le_card hsub1
              have he1 : E γs ∩ E γ' = E γs :=
                Finset.eq_of_subset_of_card_le hsub1 (by omega)
              have he2 : E γs ∩ E γ' = E γ' :=
                Finset.eq_of_subset_of_card_le hsub2 (by omega)
              exact hne2 (he1.symm.trans he2)
            omega
          set AS := S.filter (fun m' => ((E m' ∪ T₃).card ≤ 4)) with hASdef
          have hAcard : AS.card ≤ T₃.card :=
            hframe γs (hSB hγs) γ' (hSB hγ') (Ne.symm hne') S hSB
          have hγsA : γs ∈ AS := by
            refine Finset.mem_filter.mpr ⟨hγs, ?_⟩
            have hcup : E γs ∪ T₃ = T₃ := by
              rw [hT₃def, ← Finset.union_assoc, Finset.union_self]
            rw [hcup]
            omega
          set S' := S \ AS with hS'def
          have hS'sub : S' ⊆ B :=
            fun x hx => hSB (Finset.mem_sdiff.mp hx).1
          have hS'all2 : ∀ γ ∈ S', (E γ).card = 2 :=
            fun γ hγ => hall2 γ (Finset.mem_sdiff.mp hγ).1
          have hAsub : AS ⊆ S := Finset.filter_subset _ _
          have hS'card : S'.card = S.card - AS.card := by
            rw [hS'def, Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub]
          have hA1 : 1 ≤ AS.card := Finset.card_pos.mpr ⟨γs, hγsA⟩
          have hAle : AS.card ≤ S.card := Finset.card_le_card hAsub
          have hih := ih S' hS'sub (by omega) hS'all2
          have hdisj : ∀ x ∈ S'.biUnion E, x ∉ T₃ := by
            intro x hx hxT
            obtain ⟨m', hm'S', hxE⟩ := Finset.mem_biUnion.mp hx
            obtain ⟨hm'S, hm'A⟩ := Finset.mem_sdiff.mp hm'S'
            have hnotA : ¬((E m' ∪ T₃).card ≤ 4) := fun hc =>
              hm'A (Finset.mem_filter.mpr ⟨hm'S, hc⟩)
            apply hnotA
            have hint : 1 ≤ (E m' ∩ T₃).card :=
              Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxE, hxT⟩⟩
            have huni := Finset.card_union_add_card_inter (E m') T₃
            have h1 := hEcard m' (hSB hm'S)
            omega
          have hT₃sub : T₃ ⊆ S.biUnion E := by
            intro x hx
            rw [hT₃def, Finset.mem_union] at hx
            rcases hx with h | h
            · exact Finset.mem_biUnion.mpr ⟨γs, hγs, h⟩
            · exact Finset.mem_biUnion.mpr ⟨γ', hγ', h⟩
          have hsub' : S'.biUnion E ⊆ (S.biUnion E) \ T₃ := by
            intro x hx
            refine Finset.mem_sdiff.mpr ⟨?_, hdisj x hx⟩
            obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp hx
            exact Finset.mem_biUnion.mpr
              ⟨m', (Finset.mem_sdiff.mp hm').1, hxE⟩
          have hcount : (S'.biUnion E).card
              ≤ (S.biUnion E).card - T₃.card := by
            have h1 := Finset.card_le_card hsub'
            rwa [Finset.card_sdiff, Finset.inter_eq_left.mpr hT₃sub] at h1
          have hT₃big : T₃.card ≤ (S.biUnion E).card :=
            Finset.card_le_card hT₃sub
          obtain ⟨hihle, hihstrict⟩ := hih
          constructor
          · omega
          · intro hnd3
            by_cases hd3' : 3 ∣ (S'.biUnion E).card
            · -- tie forbidden: u = u' + 3 would give 3 ∣ u
              by_contra hge
              push Not at hge
              -- S.card = u forces AS = 3, S' = u', and u = u' + 3
              have hu'lt : ¬ (3 ∣ (S.biUnion E).card) := hnd3
              have h1 : S.card ≤ AS.card + S'.card := by omega
              have h2 : S'.card ≤ (S'.biUnion E).card := hihle
              -- u ≥ u' + 3 and S.card ≤ 3 + u'; S.card ≥ u (hge) forces u = u' + 3
              have h3 : (S.biUnion E).card ≤ 3 + (S'.biUnion E).card := by omega
              have h4 : (S'.biUnion E).card + 3 ≤ (S.biUnion E).card := by
                omega
              have hueq : (S.biUnion E).card = (S'.biUnion E).card + 3 := by
                omega
              rw [hueq] at hnd3
              exact hnd3 (by omega : 3 ∣ (S'.biUnion E).card + 3)
            · have := hihstrict hd3'
              omega
        · -- isolated: a fresh disjoint 2-set
          push Not at hpart
          set S' := S.erase γs with hS'def
          have hS'sub : S' ⊆ B :=
            fun x hx => hSB (Finset.mem_of_mem_erase hx)
          have hS'all2 : ∀ γ ∈ S', (E γ).card = 2 :=
            fun γ hγ => hall2 γ (Finset.mem_of_mem_erase hγ)
          have hS'card : S'.card = S.card - 1 :=
            Finset.card_erase_of_mem hγs
          have hih := ih S' hS'sub (by omega) hS'all2
          have hdisj : Disjoint (E γs) (S'.biUnion E) := by
            rw [Finset.disjoint_left]
            intro x hxγ hxU
            obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp hxU
            have hm'ne : m' ≠ γs := Finset.ne_of_mem_erase hm'
            have hbig := hpart m' (Finset.mem_of_mem_erase hm') hm'ne
            have hint : 1 ≤ (E γs ∩ E m').card :=
              Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxγ, hxE⟩⟩
            have huni := Finset.card_union_add_card_inter (E γs) (E m')
            have h1 := hall2 γs hγs
            have h2 := hEcard m' (hS'sub hm')
            omega
          have hsub2 : (E γs) ∪ (S'.biUnion E) ⊆ S.biUnion E := by
            intro x hx
            rcases Finset.mem_union.mp hx with h | h
            · exact Finset.mem_biUnion.mpr ⟨γs, hγs, h⟩
            · obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp h
              exact Finset.mem_biUnion.mpr
                ⟨m', Finset.mem_of_mem_erase hm', hxE⟩
          have hsub3 : S.biUnion E ⊆ (E γs) ∪ (S'.biUnion E) := by
            intro x hx
            obtain ⟨m', hm', hxE⟩ := Finset.mem_biUnion.mp hx
            by_cases hm'γ : m' = γs
            · exact Finset.mem_union.mpr (Or.inl (hm'γ ▸ hxE))
            · exact Finset.mem_union.mpr (Or.inr
                (Finset.mem_biUnion.mpr
                  ⟨m', Finset.mem_erase.mpr ⟨hm'γ, hm'⟩, hxE⟩))
          have hueq : (S.biUnion E).card
              = (E γs).card + (S'.biUnion E).card := by
            rw [Finset.Subset.antisymm hsub3 hsub2,
              Finset.card_union_of_disjoint hdisj]
          have h2 := hall2 γs hγs
          obtain ⟨hihle, hihstrict⟩ := hih
          constructor
          · omega
          · intro hnd3
            by_cases hd3' : 3 ∣ (S'.biUnion E).card
            · -- u = u' + 2, 3 ∣ u', so the landed tie S' = u' still loses one
              omega
            · have := hihstrict hd3'
              omega
    -- ===== assemble the defect bound =====
  by_cases hsmallsup : ∃ γ₀ ∈ B, (E γ₀).card ≤ 1
  · -- a small-support member partners with anyone; everyone with |E ∪ T₃| ≤ 4 absorbs,
    -- deviants are all-size-2 and disjoint from T₃: the strict induction closes.
    obtain ⟨γ₀, hγ₀, hE1⟩ := hsmallsup
    by_cases hone : ∃ γ' ∈ B, γ' ≠ γ₀
    · obtain ⟨γ', hγ', hne'⟩ := hone
      set T₃ := E γ₀ ∪ E γ' with hT₃def
      have hT₃card : T₃.card ≤ 3 := by
        have hu := Finset.card_union_le (E γ₀) (E γ')
        rw [← hT₃def] at hu
        have h2 := hEcard γ' hγ'
        omega
      set AS := B.filter (fun m => ((E m ∪ T₃).card ≤ 4)) with hASdef
      have hAcard : AS.card ≤ T₃.card :=
        hframe γ₀ hγ₀ γ' hγ' (Ne.symm hne') B (Finset.Subset.refl B)
      set S' := B \ AS with hS'def
      have hS'sub : S' ⊆ B := Finset.sdiff_subset
      have hS'all2 : ∀ γ ∈ S', (E γ).card = 2 := by
        intro γ hγ
        obtain ⟨hγB, hγA⟩ := Finset.mem_sdiff.mp hγ
        have hnotA : ¬((E γ ∪ T₃).card ≤ 4) := fun hc =>
          hγA (Finset.mem_filter.mpr ⟨hγB, hc⟩)
        have hu := Finset.card_union_le (E γ) T₃
        have h1 := hEcard γ hγB
        omega
      have hkey := key S'.card S' hS'sub le_rfl hS'all2
      have hcap : (S'.biUnion E).card ≤ Fintype.card ι := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      have hAsub : AS ⊆ B := Finset.filter_subset _ _
      have hsplit : B.card = AS.card + S'.card := by
        rw [hS'def, Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub]
        have := Finset.card_le_card hAsub
        omega
      obtain ⟨hkle, hkstrict⟩ := hkey
      -- if T₃ has < 3 points there are no deviants at all
      by_cases hT3 : T₃.card = 3
      · -- deviants avoid T₃, so their union has ≤ n − 3 points
        have hdisjT : ∀ x ∈ S'.biUnion E, x ∉ T₃ := by
          intro x hx hxT
          obtain ⟨m', hm'S', hxE⟩ := Finset.mem_biUnion.mp hx
          obtain ⟨hm'B, hm'A⟩ := Finset.mem_sdiff.mp hm'S'
          have hnotA : ¬((E m' ∪ T₃).card ≤ 4) := fun hc =>
            hm'A (Finset.mem_filter.mpr ⟨hm'B, hc⟩)
          apply hnotA
          have hint : 1 ≤ (E m' ∩ T₃).card :=
            Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxE, hxT⟩⟩
          have huni := Finset.card_union_add_card_inter (E m') T₃
          have h1 := hEcard m' hm'B
          omega
        have hsubc : S'.biUnion E ⊆ Finset.univ \ T₃ := by
          intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hdisjT x hx⟩
        have hcap3 : (S'.biUnion E).card ≤ Fintype.card ι - 3 := by
          have h1 := Finset.card_le_card hsubc
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr
            (Finset.subset_univ T₃), Finset.card_univ] at h1
          omega
        by_cases hd3 : 3 ∣ (S'.biUnion E).card
        · -- tie case: u' ≡ 0, u' ≤ n−3 with 3∤n means u' < n−3 or the +3 absorbs
          have hne3 : (S'.biUnion E).card ≠ Fintype.card ι - 3 := by
            intro heq
            apply h3
            have h9 : Fintype.card ι = (S'.biUnion E).card + 3 := by omega
            rw [h9]
            omega
          omega
        · have := hkstrict hd3
          omega
      · -- |T₃| ≤ 2: deviance is impossible, B = AS, B.card ≤ 2 ≤ n−1
        have hS'0 : S'.card = 0 := by
          by_contra hne0
          obtain ⟨γ, hγ⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
          obtain ⟨hγB, hγA⟩ := Finset.mem_sdiff.mp hγ
          refine hγA (Finset.mem_filter.mpr ⟨hγB, ?_⟩)
          have hu := Finset.card_union_le (E γ) T₃
          have h1 := hEcard γ hγB
          omega
        omega
    · push Not at hone
      have hsub : B ⊆ {γ₀} := fun x hx => Finset.mem_singleton.mpr (hone x hx)
      have hle1 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle1
      omega
  · -- all supports have exactly 2 points: the strict induction applies directly
    push Not at hsmallsup
    have hall2 : ∀ γ ∈ B, (E γ).card = 2 := by
      intro γ hγ
      have h1 := hEcard γ hγ
      have h2 := hsmallsup γ hγ
      omega
    have hkey := key B.card B (Finset.Subset.refl B) le_rfl hall2
    have hcap : (B.biUnion E).card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    obtain ⟨hkle, hkstrict⟩ := hkey
    by_cases hd3 : 3 ∣ (B.biUnion E).card
    · -- 3 ∣ u and 3 ∤ n force u < n, so even the tie is ≤ n − 1
      have hne : (B.biUnion E).card ≠ Fintype.card ι := by
        intro heq
        exact h3 (heq ▸ hd3)
      omega
    · have := hkstrict hd3
      omega

open Classical in
/-- **The defect form of the boundary collapse:** `ε_mca(C, δ) ≤ (n−1)/|F|` at band-3
radii for distance-`≥ 5` codes on domains with `3 ∤ n` — the sharp production form
(production smooth domains have `n = 2^μ`, never divisible by 3). -/
theorem boundaryDefect_epsMCA_le (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C 4)
    (h3 : ¬ (3 ∣ Fintype.card ι)) (hn3 : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((3 : ℕ) : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Fintype.card ι - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast boundaryDefect_badScalars_card_le C hC h3 hn3 hδ (u 0) (u 1)

end ProximityGap.BoundaryDefectBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BoundaryDefectBound.boundaryDefect_badScalars_card_le
#print axioms ProximityGap.BoundaryDefectBound.boundaryDefect_epsMCA_le
