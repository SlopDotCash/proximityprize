/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListSingletonDefectGeometry

/-!
# Codeword-indexed support-ratio covers for singleton witnesses

`LineListIncidenceMultiplicity.lean` isolates singleton bad scalars by their unique witnessing
codeword.  This file attaches the support-ratio geometry to one fixed codeword: every singleton
scalar has a large support-ratio fiber, hence admits finite subfibers of size
`a - #zeroAgreement(c)`.

The point is not yet a floor proof.  It creates the exact finite object needed by the next
overlap-multiplicity attempt: pairs `(γ, T)` where `γ` is uniquely witnessed by `c` and `T` is a
large moving-support subfiber for that same scalar.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- For one codeword `c`, the finite support-ratio subfiber cover of its singleton-witness
scalars.  A point is a scalar `γ` uniquely witnessed by `c` together with an
`(a - #zeroAgreement(c))`-subset of the moving coordinates whose support-ratio value is `γ`. -/
noncomputable def codewordSingletonSupportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    Finset (F × Finset (Fin n)) :=
  (Finset.univ : Finset (F × Finset (Fin n))).filter
    (fun e => e.1 ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
      e.2 ∈ (supportRatioFiber c u₀ u₁ e.1).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card))

open Classical in
theorem mem_codewordSingletonSupportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (e : F × Finset (Fin n)) :
    e ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c ↔
      e.1 ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
        e.2 ∈ (supportRatioFiber c u₀ u₁ e.1).powersetCard
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rw [codewordSingletonSupportRatioCover, Finset.mem_filter]
  simp

open Classical in
/-- A singleton-witness scalar has enough support-ratio mass to choose the required moving
subfiber. -/
theorem supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    a - (directionZeroAgreementSet c u₀ u₁).card
      ≤ (supportRatioFiber c u₀ u₁ γ).card := by
  have hheavy :
      γ ∈ codewordHeavyScalars (F := F) (n := n) a c u₀ u₁ :=
    codewordSingletonWitnessScalars_subset_codewordHeavyScalars dom k a u₀ u₁ c hγ
  rw [mem_codewordHeavyScalars] at hheavy
  have hcard := agreeSet_line_card_le_zeroAgreement_add_supportRatioFiber c u₀ u₁ γ
  omega

open Classical in
/-- Every singleton-witness scalar has at least one point in the codeword-indexed support-ratio
cover. -/
theorem exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ∃ T : Finset (Fin n),
      T ∈ (supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card) ∧
        (γ, T) ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c := by
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
        dom k a u₀ u₁ c hγ)
  have hTmem :
      T ∈ (supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card) :=
    Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
  refine ⟨T, hTmem, ?_⟩
  rw [mem_codewordSingletonSupportRatioCover]
  exact ⟨hγ, hTmem⟩

open Classical in
/-- The first projection of the codeword-indexed support-ratio cover is exactly the singleton
scalar fiber of that codeword. -/
theorem codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    codewordSingletonWitnessScalars dom k a u₀ u₁ c =
      (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).image Prod.fst := by
  ext γ
  constructor
  · intro hγ
    rcases exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
        dom k a u₀ u₁ c hγ with
      ⟨T, _hT, hpair⟩
    exact Finset.mem_image.mpr ⟨(γ, T), hpair, rfl⟩
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨⟨γ', T⟩, hpair, hfst⟩
    dsimp at hfst
    subst γ'
    exact (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp hpair |>.1

open Classical in
/-- The codeword-indexed support-ratio cover cardinally dominates the singleton scalar fiber. -/
theorem codewordSingletonWitnessScalars_card_le_supportRatioCover_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
      ≤ (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  rw [codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover]
  exact Finset.card_image_le

open Classical in
/-- The fiber of the support-ratio cover over a singleton scalar is exactly the collection of
eligible support-ratio subfibers for that scalar. -/
theorem codewordSingletonSupportRatioCover_fst_fiber_eq
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter (fun e => e.1 = γ) =
      ((supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card)).image (fun T => (γ, T)) := by
  ext e
  rcases e with ⟨γ', T⟩
  constructor
  · intro he
    rw [Finset.mem_filter] at he
    have hγ' : γ' = γ := he.2
    subst γ'
    have hcover :=
      (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp he.1
    exact Finset.mem_image.mpr ⟨T, hcover.2, rfl⟩
  · intro he
    rcases Finset.mem_image.mp he with ⟨T', hT', hpair⟩
    cases hpair
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [mem_codewordSingletonSupportRatioCover]
    exact ⟨hγ, hT'⟩

open Classical in
/-- Cardinality of one scalar fiber of the codeword-indexed support-ratio cover. -/
theorem codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ((codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter (fun e => e.1 = γ)).card =
      (supportRatioFiber c u₀ u₁ γ).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  calc
    ((codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter
        (fun e => e.1 = γ)).card
        = (((supportRatioFiber c u₀ u₁ γ).powersetCard
            (a - (directionZeroAgreementSet c u₀ u₁).card)).image
              (fun T => (γ, T))).card := by
          rw [codewordSingletonSupportRatioCover_fst_fiber_eq dom k a u₀ u₁ c hγ]
    _ = ((supportRatioFiber c u₀ u₁ γ).powersetCard
            (a - (directionZeroAgreementSet c u₀ u₁).card)).card := by
          exact Finset.card_image_of_injOn
            (fun _T _hT _T' _hT' h => by simpa using congrArg Prod.snd h)
    _ = (supportRatioFiber c u₀ u₁ γ).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
          rw [Finset.card_powersetCard]

open Classical in
/-- Exact decomposition of the codeword-indexed support-ratio cover by singleton scalar. -/
theorem codewordSingletonSupportRatioCover_card_eq_sum_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card =
      ∑ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
        (supportRatioFiber c u₀ u₁ γ).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  let C := codewordSingletonSupportRatioCover dom k a u₀ u₁ c
  let S := codewordSingletonWitnessScalars dom k a u₀ u₁ c
  have hmaps : ∀ e ∈ C, e.1 ∈ S := by
    intro e he
    change e ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c at he
    exact (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c e).mp he |>.1
  calc
    C.card = ∑ γ ∈ S, (C.filter fun e => e.1 = γ).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
          (supportRatioFiber c u₀ u₁ γ).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        exact codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
          dom k a u₀ u₁ c (by simpa [S] using hγ)

omit [Fintype F] in
open Classical in
/-- A support-ratio fiber is a subfiber of the moving support. -/
theorem supportRatioFiber_card_le_directionSupportSet_card
    (c u₀ u₁ : Fin n → F) (γ : F) :
    (supportRatioFiber c u₀ u₁ γ).card ≤ (directionSupportSet u₁).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

omit [Fintype F] in
open Classical in
/-- Distinct support-ratio fibers for one fixed codeword are disjoint: every moving coordinate
has exactly one ratio `(c i - u₀ i) / u₁ i`. -/
theorem disjoint_supportRatioFiber_of_ne
    (c u₀ u₁ : Fin n → F) {γ γ' : F} (hne : γ ≠ γ') :
    Disjoint (supportRatioFiber c u₀ u₁ γ) (supportRatioFiber c u₀ u₁ γ') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  have hγ := (mem_supportRatioFiber c u₀ u₁ γ i).mp hi |>.2
  have hγ' := (mem_supportRatioFiber c u₀ u₁ γ' i).mp hi' |>.2
  exact hne (hγ.symm.trans hγ')

open Classical in
/-- The support-ratio fibers of one fixed codeword are pairwise disjoint. -/
theorem pairwiseDisjoint_supportRatioFiber
    (c u₀ u₁ : Fin n → F) :
    ((Finset.univ : Finset F) : Set F).PairwiseDisjoint
      (fun γ => supportRatioFiber c u₀ u₁ γ) := by
  intro γ _hγ γ' _hγ' hne
  exact disjoint_supportRatioFiber_of_ne c u₀ u₁ hne

open Classical in
/-- The moving support is exactly partitioned by the support-ratio fibers of a fixed codeword. -/
theorem directionSupportSet_card_eq_sum_supportRatioFiber
    (c u₀ u₁ : Fin n → F) :
    (directionSupportSet u₁).card =
      ∑ γ : F, (supportRatioFiber c u₀ u₁ γ).card := by
  simpa [supportRatioFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (f := fun i => (c i - u₀ i) / u₁ i)
      (s := directionSupportSet u₁) (t := (Finset.univ : Finset F))
      (fun i _hi => Finset.mem_univ _))

omit [Fintype F] in
open Classical in
/-- Any subfamily of support-ratio fibers has total size at most the moving support. -/
theorem sum_supportRatioFiber_card_le_directionSupportSet_card
    (c u₀ u₁ : Fin n → F) (Γ : Finset F) :
    ∑ γ ∈ Γ, (supportRatioFiber c u₀ u₁ γ).card ≤
      (directionSupportSet u₁).card := by
  have hdisj :
      (Γ : Set F).PairwiseDisjoint (fun γ => supportRatioFiber c u₀ u₁ γ) := by
    intro γ _hγ γ' _hγ' hne
    exact disjoint_supportRatioFiber_of_ne c u₀ u₁ hne
  have hUsub :
      (Γ.biUnion fun γ => supportRatioFiber c u₀ u₁ γ) ⊆ directionSupportSet u₁ := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    rcases hi with ⟨γ, _hγ, hiγ⟩
    exact (mem_supportRatioFiber c u₀ u₁ γ i).mp hiγ |>.1
  calc
    ∑ γ ∈ Γ, (supportRatioFiber c u₀ u₁ γ).card =
        (Γ.biUnion fun γ => supportRatioFiber c u₀ u₁ γ).card := by
      symm
      rw [Finset.card_biUnion hdisj]
    _ ≤ (directionSupportSet u₁).card := Finset.card_le_card hUsub

open Classical in
/-- The singleton-witness scalars for a fixed codeword consume disjoint moving support-ratio
fibers.  This is the exact accounting reason the coordinate-overlap route recovers only the
ordinary support-denominator cap unless it uses additional RS or second-witness structure. -/
theorem codewordSingletonWitnessScalars_card_mul_sub_zeroAgreement_le_support
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card *
        (a - (directionZeroAgreementSet c u₀ u₁).card) ≤
      (directionSupportSet u₁).card := by
  let Γ := codewordSingletonWitnessScalars dom k a u₀ u₁ c
  have hmem :
      ∀ γ ∈ Γ,
        a - (directionZeroAgreementSet c u₀ u₁).card
          ≤ (supportRatioFiber c u₀ u₁ γ).card := by
    intro γ hγ
    exact supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
      dom k a u₀ u₁ c hγ
  have hlb :
      Γ.card * (a - (directionZeroAgreementSet c u₀ u₁).card) ≤
        ∑ γ ∈ Γ, (supportRatioFiber c u₀ u₁ γ).card := by
    calc
      Γ.card * (a - (directionZeroAgreementSet c u₀ u₁).card)
          = ∑ _γ ∈ Γ, (a - (directionZeroAgreementSet c u₀ u₁).card) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ γ ∈ Γ, (supportRatioFiber c u₀ u₁ γ).card :=
        Finset.sum_le_sum hmem
  exact le_trans hlb (sum_supportRatioFiber_card_le_directionSupportSet_card c u₀ u₁ Γ)

open Classical in
/-- Denominator form of the fixed-codeword support-ratio partition bound.  This restates the
old heavy-scalar denominator cap through singleton support-ratio fibers, making clear that
coordinate overlap inside one fixed codeword cannot by itself improve the bound. -/
theorem
    codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement_of_ratioPartition
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hpos : (directionZeroAgreementSet c u₀ u₁).card < a) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
      ≤ (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  have hb : 1 ≤ a - (directionZeroAgreementSet c u₀ u₁).card :=
    Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hpos)
  exact (Nat.le_div_iff_mul_le hb).mpr
    (codewordSingletonWitnessScalars_card_mul_sub_zeroAgreement_le_support
      dom k a u₀ u₁ c)

/-- Elementary comparison between the denominator count and the subset-packing count. -/
theorem support_div_le_choose_of_pos_le {s m : ℕ} (hmpos : 0 < m) (hms : m ≤ s) :
    s / m ≤ s.choose m := by
  cases m with
  | zero => exact (Nat.lt_irrefl 0 hmpos).elim
  | succ m =>
    cases s with
    | zero => exact (Nat.not_succ_le_zero m hms).elim
    | succ s =>
      have hms' : m ≤ s := Nat.succ_le_succ_iff.mp hms
      have hchoose_pos : 0 < s.choose m := Nat.choose_pos hms'
      have hle_lhs : s + 1 ≤ (s + 1) * s.choose m :=
        Nat.le_mul_of_pos_right _ hchoose_pos
      have hidentity := Nat.add_one_mul_choose_eq s m
      have hle_prod :
          s + 1 ≤ (m + 1) * (s + 1).choose (m + 1) := by
        simpa [Nat.mul_comm] using hle_lhs.trans_eq hidentity
      exact (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos m)).mpr
        (le_trans hle_prod (Nat.le_add_right _ _))

open Classical in
/-- On an actual appearing codeword in the zero-safe branch, the denominator scalar cap is no
larger than the support-choose cover cap. -/
theorem support_div_sub_zeroAgreement_le_support_choose_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card) ≤
      (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  have hpos : 0 < a - (directionZeroAgreementSet c u₀ u₁).card :=
    Nat.sub_pos_of_lt (hsafe c hcCode)
  rcases exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
      dom k a u₀ u₁ c hc with ⟨γ, hγ⟩
  have hfiber_le :
      (supportRatioFiber c u₀ u₁ γ).card ≤ (directionSupportSet u₁).card :=
    supportRatioFiber_card_le_directionSupportSet_card c u₀ u₁ γ
  exact support_div_le_choose_of_pos_le hpos (le_trans hγ hfiber_le)

open Classical in
/-- The support-choose cap is a cover-control baseline rather than a scalar improvement: the
older denominator scalar cap already lies below it on every zero-safe appearing codeword. -/
theorem codewordSingletonWitnessScalars_card_le_support_choose_via_denominator
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤
      (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact le_trans
    (codewordSingletonWitnessScalars_card_le_support_div_of_zeroSafe
      dom k a u₀ u₁ c hsafe hcCode)
    (support_div_sub_zeroAgreement_le_support_choose_of_zeroSafe
      dom k a u₀ u₁ c hsafe hc)

open Classical in
/-- Crude scalar-fiber-count control for the codeword-indexed support-ratio cover. -/
theorem codewordSingletonSupportRatioCover_card_le_singletonWitness_card_mul_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card *
        (directionSupportSet u₁).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rw [codewordSingletonSupportRatioCover_card_eq_sum_choose]
  calc
    (∑ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
        (supportRatioFiber c u₀ u₁ γ).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card))
        ≤ ∑ _γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
            (directionSupportSet u₁).card.choose
              (a - (directionZeroAgreementSet c u₀ u₁).card) := by
          refine Finset.sum_le_sum fun γ _hγ => ?_
          exact Nat.choose_le_choose
            (a - (directionZeroAgreementSet c u₀ u₁).card)
            (supportRatioFiber_card_le_directionSupportSet_card c u₀ u₁ γ)
    _ = (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card *
          (directionSupportSet u₁).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
          rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Ambient scalar-times-binomial control for the codeword-indexed support-ratio cover.  This is a
baseline envelope; beating it requires structure beyond fixed-codeword coordinate overlap, since
those ratio fibers are already disjoint. -/
theorem codewordSingletonSupportRatioCover_card_le_field_card_mul_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤
      Fintype.card F * (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) :=
  (codewordSingletonSupportRatioCover_card_le_singletonWitness_card_mul_choose
    dom k a u₀ u₁ c).trans
    (Nat.mul_le_mul_right _
      (Finset.card_le_univ (codewordSingletonWitnessScalars dom k a u₀ u₁ c)))

open Classical in
/-- On a positive moving-support deficit, the selected subfiber `T` determines the scalar `γ`.
This is the exact packing fact behind the codeword-indexed support-ratio cover. -/
theorem codewordSingletonSupportRatioCover_snd_injOn
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hpos : 0 < a - (directionZeroAgreementSet c u₀ u₁).card) :
    Set.InjOn Prod.snd
      (codewordSingletonSupportRatioCover dom k a u₀ u₁ c : Set (F × Finset (Fin n))) := by
  intro e he e' he' hsnd
  rcases e with ⟨γ, T⟩
  rcases e' with ⟨γ', T'⟩
  dsimp at hsnd
  have hcover :=
    (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp he
  have hcover' :=
    (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ', T')).mp he'
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hcover.2
  obtain ⟨hT'sub, _hT'card⟩ := Finset.mem_powersetCard.mp hcover'.2
  have hTpos : 0 < T.card := by
    rw [hTcard]
    exact hpos
  obtain ⟨i, hiT⟩ := Finset.card_pos.mp hTpos
  have hiT' : i ∈ T' := by simpa [hsnd] using hiT
  have hratio := (mem_supportRatioFiber c u₀ u₁ γ i).mp (hTsub hiT)
  have hratio' := (mem_supportRatioFiber c u₀ u₁ γ' i).mp (hT'sub hiT')
  have hγ : γ = γ' := hratio.2.symm.trans hratio'.2
  cases hγ
  cases hsnd
  rfl

open Classical in
/-- The second projection of the codeword-indexed support-ratio cover lands in the ambient
`(a - #zeroAgreement(c))`-subsets of the moving support. -/
theorem codewordSingletonSupportRatioCover_image_snd_subset_support_powerset
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).image Prod.snd ⊆
      (directionSupportSet u₁).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨⟨γ, T'⟩, hpair, hT'⟩
  dsimp at hT'
  subst T'
  have hcover :=
    (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp hpair
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hcover.2
  refine Finset.mem_powersetCard.mpr ⟨?_, hcard⟩
  intro i hi
  exact ((mem_supportRatioFiber c u₀ u₁ γ i).mp (hsub hi)).1

open Classical in
/-- Positive-deficit packing cap for the codeword-indexed support-ratio cover: once `T` is
nonempty, the cover injects into the ambient family of moving-support subsets of that size. -/
theorem codewordSingletonSupportRatioCover_card_le_support_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hpos : 0 < a - (directionZeroAgreementSet c u₀ u₁).card) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤
      (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  have hcardImage :
      ((codewordSingletonSupportRatioCover dom k a u₀ u₁ c).image Prod.snd).card =
        (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
    exact Finset.card_image_of_injOn
      (codewordSingletonSupportRatioCover_snd_injOn dom k a u₀ u₁ c hpos)
  rw [← hcardImage]
  simpa [Finset.card_powersetCard] using
    Finset.card_le_card
      (codewordSingletonSupportRatioCover_image_snd_subset_support_powerset
        dom k a u₀ u₁ c)

open Classical in
/-- Zero-safe line form of the support-choose packing cap. -/
theorem codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤
      (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) :=
  codewordSingletonSupportRatioCover_card_le_support_choose
    dom k a u₀ u₁ c (Nat.sub_pos_of_lt (hsafe c hc))

/-- Uniform cap on the codeword-indexed support-ratio cover attached to every appearing codeword
on every large-zero safe line. -/
def UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤ S

/-- Uniform field-factor-free support-choose cap for the codeword-indexed support-ratio cover. -/
def UniformLargeZeroSafeCodewordSupportChooseBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (directionSupportSet u₁).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) ≤ S

open Classical in
/-- The weighted support-choose cost of all codeword-indexed singleton cover caps on one line.
Unlike the uniform `S` route, this keeps the actual zero-agreement profile of each appearing
codeword. -/
noncomputable def codewordSupportChooseWeight
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : ℕ :=
  ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
    (directionSupportSet u₁).card.choose
      (a - (directionZeroAgreementSet c u₀ u₁).card)

/-- Uniform combined arithmetic budget using the weighted support-choose cost rather than a
single worst per-codeword cap. -/
def UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + codewordSupportChooseWeight dom k a u₀ u₁ ≤ 2 * B

open Classical in
/-- The singleton defect is bounded by the weighted support-choose cost on safe lines. -/
theorem singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ codewordSupportChooseWeight dom k a u₀ u₁ := by
  rw [singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars,
    codewordSupportChooseWeight]
  refine Finset.sum_le_sum ?_
  intro c hc
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact
    (codewordSingletonWitnessScalars_card_le_supportRatioCover_card dom k a u₀ u₁ c).trans
      (codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
        dom k a u₀ u₁ c hsafe hcCode)

open Classical in
/-- The weighted support-choose cost is bounded by the older uniform cap times the number of
appearing codewords. -/
theorem codewordSupportChooseWeight_le_lineAppearingCodewords_card_mul
    (dom : Fin n ↪ F) (k a S : ℕ) (u₀ u₁ : Fin n → F)
    (hchoose : ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
      (directionSupportSet u₁).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) ≤ S) :
    codewordSupportChooseWeight dom k a u₀ u₁
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * S := by
  rw [codewordSupportChooseWeight]
  calc
    ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (directionSupportSet u₁).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card)
        ≤ ∑ _c ∈ lineAppearingCodewords dom k a u₀ u₁, S :=
          Finset.sum_le_sum hchoose
    _ = (lineAppearingCodewords dom k a u₀ u₁).card * S := by
          rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Fixed-line consumer for the weighted support-choose singleton route. -/
theorem lineBadScalars_card_le_of_weight_add_codewordSupportChoose_le_two_mul
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + codewordSupportChooseWeight dom k a u₀ u₁ ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe
    (le_trans
      (Nat.add_le_add_left
        (singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe
          dom k a u₀ u₁ hsafe)
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
      hbudget)

open Classical in
/-- The weighted support-choose budget discharges the large-zero safe residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseWeightBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget :
      UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_codewordSupportChoose_le_two_mul
    dom k a B u₀ u₁ hsafe (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Production wrapper for the weighted support-choose route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseWeightBudget
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget :
      UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseWeightBudget
      dom k a B hbudget)

open Classical in
/-- The older uniform support-choose route implies the weighted support-choose arithmetic budget
whenever its direct appearing-codeword arithmetic budget fits. -/
theorem
    uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_of_codewordSupportChooseBudget
    (dom : Fin n ↪ F) (k a S B : ℕ)
    (hchoose : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact le_trans
    (Nat.add_le_add_left
      (codewordSupportChooseWeight_le_lineAppearingCodewords_card_mul
        dom k a S u₀ u₁ (hchoose u₀ u₁ hnotEligible hsafe))
      (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
    (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Exact failure form for the weighted support-choose arithmetic budget. -/
theorem
    not_uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_iff_exists_weight_gt
    (dom : Fin n ↪ F) (k a B : ℕ) :
    (¬ UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + codewordSupportChooseWeight dom k a u₀ u₁ := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe)) hgt

open Classical in
/-- Scanner for the weighted support-choose route.  Once support-side hypotheses are fixed,
failed production exposes a large-zero safe line where the actual weighted support-choose
arithmetic is above budget. -/
theorem
    exists_largeZero_safe_codewordSupportChooseWeight_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + codewordSupportChooseWeight dom k a u₀ u₁ := by
  have hnotBudget :
      ¬ UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B := by
    intro hbudget
    exact hnot
      (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseWeightBudget
        dom k a L B hSupport hFits hZeroSafe hbudget)
  exact
    (not_uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_iff_exists_weight_gt
      dom k a B).mp hnotBudget

/-- A support-ratio cover cap implies the direct singleton-witness scalar cap for each appearing
codeword. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact le_trans
    (codewordSingletonWitnessScalars_card_le_supportRatioCover_card dom k a u₀ u₁ c)
    (hcover u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Exact failure form for the codeword-indexed support-ratio cover cap. -/
theorem not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
    (dom : Fin n ↪ F) (k a S : ℕ) :
    (¬ UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe c hc)) hgt

open Classical in
/-- A uniform support-choose cap supplies the codeword-indexed support-ratio cover budget on
large-zero safe lines. -/
theorem uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_of_supportChoose
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hchoose : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
        ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          (directionSupportSet u₁).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) ≤ S) :
    UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact
    (codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
      dom k a u₀ u₁ c hsafe hcCode).trans
      (hchoose u₀ u₁ hnotEligible hsafe c hc)

/-- Named-budget form of the support-choose-to-cover bridge. -/
theorem uniformCodewordSupportRatioCoverBudgeted_of_supportChooseBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hchoose : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S) :
    UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S :=
  uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_of_supportChoose
    dom k a S hchoose

open Classical in
/-- If a uniform codeword-indexed support-ratio cover cap fails, then the support-choose packing
envelope is already above that cap for a concrete appearing codeword. -/
theorem exists_largeZero_safe_codewordSupportRatioCoverChoose_gt_of_not_coverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (directionSupportSet u₁).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
    lt_of_lt_of_le hgt
      (codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
        dom k a u₀ u₁ c hsafe hcCode)⟩

open Classical in
/-- Exact failure form for the named support-choose cap. -/
theorem not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_iff_exists_choose_gt
    (dom : Fin n ↪ F) (k a S : ℕ) :
    (¬ UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (directionSupportSet u₁).card.choose
              (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe c hc)) hgt

open Classical in
/-- If a uniform codeword-indexed support-ratio cover cap fails, then the ambient
scalar-times-binomial envelope is already above that cap for a concrete appearing codeword. -/
theorem exists_largeZero_safe_codewordSupportRatioCoverFieldChoose_gt_of_not_coverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < Fintype.card F * (directionSupportSet u₁).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
    lt_of_lt_of_le hgt
      (codewordSingletonSupportRatioCover_card_le_field_card_mul_choose
        dom k a u₀ u₁ c)⟩

open Classical in
/-- If the direct singleton cap fails, then the codeword-indexed support-ratio cover is already
overfull for a concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordSupportRatioCover_gt_of_not_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
    lt_of_lt_of_le hgt
      (codewordSingletonWitnessScalars_card_le_supportRatioCover_card
        dom k a u₀ u₁ c)⟩

/-- The codeword-indexed support-ratio cover cap can be consumed by the direct per-codeword
singleton production route. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonSupportRatioCoverBudget
    (dom : Fin n ↪ F) (k a S B : ℕ)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B :=
  largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget dom k a S B
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
      dom k a S hcover)
    hbudget

/-- The field-factor-free support-choose cap can be consumed by the direct per-codeword
singleton production route. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseBudget
    (dom : Fin n ↪ F) (k a S B : ℕ)
    (hchoose : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B :=
  largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonSupportRatioCoverBudget
    dom k a S B
    (uniformCodewordSupportRatioCoverBudgeted_of_supportChooseBudgeted
      dom k a S hchoose)
    hbudget

/-- Production wrapper for the support-ratio cover route to per-codeword singleton caps. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportRatioCoverBudget
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    dom k a L S B hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
      dom k a S hcover)
    hbudget

/-- Production wrapper for the field-factor-free support-choose route. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseBudget
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hchoose : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportRatioCoverBudget
    dom k a L S B hSupport hFits hZeroSafe
    (uniformCodewordSupportRatioCoverBudgeted_of_supportChooseBudgeted
      dom k a S hchoose)
    hbudget

open Classical in
/-- Scanner for the support-ratio cover route.  Once support-side hypotheses are fixed, failed
production forces either the usual appearing-codeword arithmetic failure or an overfull
codeword-indexed support-ratio cover for a concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordSupportRatioCoverRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card) := by
  by_cases hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S
  · have hperCode :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
        dom k a S hcover
    rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
        dom k a S).mp hcover with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

open Classical in
/-- Scanner for the support-choose route.  Once support-side hypotheses are fixed, failed
production forces either the usual appearing-codeword arithmetic failure or a concrete appearing
codeword whose field-factor-free support-choose cap is too small. -/
theorem exists_largeZero_safe_codewordSupportChooseRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (directionSupportSet u₁).card.choose
              (a - (directionZeroAgreementSet c u₀ u₁).card)) := by
  by_cases hchoose : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S
  · have hcover :
        UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S :=
      uniformCodewordSupportRatioCoverBudgeted_of_supportChooseBudgeted
        dom k a S hchoose
    rcases
      exists_largeZero_safe_codewordSupportRatioCoverRouteFailure_of_not_budgeted
        dom k a L S B hSupport hFits hZeroSafe hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail | hgt⟩
    · exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
    · rcases hgt with ⟨c, hc, hgt⟩
      exact False.elim (not_lt_of_ge (hcover u₀ u₁ hnotEligible hsafe c hc) hgt)
  · rcases
      (not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_iff_exists_choose_gt
        dom k a S).mp hchoose with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A finite scalar set is independent for a binary scalar relation.  The intended relation is a
future interpolation edge: if two singleton scalars are connected, they cannot both stay unique
unless a second witness or an exceptional-pencil certificate appears. -/
def scalarRelationIndependent (R : F → F → Prop) (Γ : Finset F) : Prop :=
  ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → ¬ R γ γ'

omit [Field F] [Fintype F] [DecidableEq F] in
open Classical in
/-- Exact failure form for finite scalar-relation independence. -/
theorem not_scalarRelationIndependent_iff_exists_edge
    (R : F → F → Prop) (Γ : Finset F) :
    (¬ scalarRelationIndependent R Γ) ↔
      ∃ γ ∈ Γ, ∃ γ' ∈ Γ, γ ≠ γ' ∧ R γ γ' := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro γ hγ γ' hγ' hne hR
    exact hnone ⟨γ, hγ, γ', hγ', hne, hR⟩
  · rintro ⟨γ, hγ, γ', hγ', hne, hR⟩ hind
    exact (hind γ hγ γ' hγ' hne) hR

/-- The singleton scalars for every large-zero safe line and appearing codeword form an
independent set for the proposed interpolation relation.  This is the "edge kills coexistence"
half of a future scalar-rigidity theorem. -/
def UniformLargeZeroSafeCodewordSingletonRelationForbidden
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)

open Classical in
/-- Exact failure form for the forbidden-edge half of the singleton scalar graph route. -/
theorem not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) :
    (¬ UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ∃ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
              ∃ γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
                γ ≠ γ' ∧ R u₀ u₁ c γ γ' := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    by_contra hnotInd
    rcases
        (not_scalarRelationIndependent_iff_exists_edge
          (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)).mp hnotInd with
      ⟨γ, hγ, γ', hγ', hne, hR⟩
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, γ', hγ', hne, hR⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, γ', hγ', hne, hR⟩ hforbid
    exact (hforbid u₀ u₁ hnotEligible hsafe c hc γ hγ γ' hγ' hne) hR

/-- Uniform independence-number bound for a proposed codeword-indexed scalar relation.  This is
the "graph has no large independent set" half of a future scalar-rigidity theorem. -/
def UniformLargeZeroSafeCodewordRelationIndependenceBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) (S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ∀ Γ : Finset F,
          scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ →
            Γ.card ≤ S

/-- Witness-local independence-number bound for a proposed codeword-indexed scalar relation.
Unlike `UniformLargeZeroSafeCodewordRelationIndependenceBudgeted`, this only asks to bound
independent sets that are subsets of the actual singleton-witness scalars for the appearing
codeword. -/
def UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) (S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ∀ Γ : Finset F,
          Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c →
            scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ →
              Γ.card ≤ S

/-- A global independence-number theorem is a sufficient condition for the witness-local
independence budget. -/
theorem uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hind : UniformLargeZeroSafeCodewordRelationIndependenceBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S := by
  intro u₀ u₁ hnotEligible hsafe c hc Γ _hsubset hindΓ
  exact hind u₀ u₁ hnotEligible hsafe c hc Γ hindΓ

/-- A direct per-codeword singleton cap supplies every witness-local relation-independence
budget.  Thus a witness-local graph route is only a new route when its independence theorem is
proved without first bounding the whole singleton-witness set. -/
theorem
    uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hbudget : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S := by
  intro u₀ u₁ hnotEligible hsafe c hc Γ hsubset _hindΓ
  exact (Finset.card_le_card hsubset).trans (hbudget u₀ u₁ hnotEligible hsafe c hc)

/-- A forbidden-edge theorem plus an independence-number theorem gives the direct per-codeword
singleton cap. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hind : UniformLargeZeroSafeCodewordRelationIndependenceBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact hind u₀ u₁ hnotEligible hsafe c hc
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
    (hforbid u₀ u₁ hnotEligible hsafe c hc)

/-- A forbidden-edge theorem plus a witness-local independence-number theorem gives the direct
per-codeword singleton cap. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hind :
      UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact hind u₀ u₁ hnotEligible hsafe c hc
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
    (fun _ hγ => hγ)
    (hforbid u₀ u₁ hnotEligible hsafe c hc)

/-- Once the forbidden-edge half is known, the witness-local graph budget is extensionally
equivalent to the direct per-codeword singleton cap.  The graph formulation can still be a useful
proof method, but it is not a weaker theorem statement. -/
theorem
    relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hind
    exact uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
      dom k a S R hforbid hind
  · intro hbudget
    exact
      uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted
        dom k a S R hbudget

open Classical in
/-- Exact failure form of the previous equivalence: under a forbidden-edge theorem, failing the
witness-local independence budget is exactly failing the original singleton-fiber cardinality
cap on one large-zero safe appearing codeword. -/
theorem
    not_relationWitnessIndependenceBudgeted_iff_exists_singleton_card_gt_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R) :
    (¬ UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  constructor
  · intro hnot
    have hnotSingleton :
        ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
      intro hsingle
      exact hnot
        ((relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden
          dom k a S R hforbid).mpr hsingle)
    exact (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
      dom k a S).mp hnotSingleton
  · intro hex hind
    have hsingle :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      (relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden
        dom k a S R hforbid).mp hind
    exact
      ((not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mpr hex) hsingle

/-- Production wrapper for the relation-independence route to per-codeword singleton caps. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationIndependence
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hind : UniformLargeZeroSafeCodewordRelationIndependenceBudgeted dom k a R S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    dom k a L S B hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationIndependence
      dom k a S R hforbid hind)
    hbudget

/-- Production wrapper for the witness-local relation-independence route to per-codeword
singleton caps. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationWitnessIndependence
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hind :
      UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    dom k a L S B hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
      dom k a S R hforbid hind)
    hbudget

open Classical in
/-- Exact failure form for the witness-local independence budget: if it fails, then some
large-zero safe appearing codeword has an over-cap independent subset of its singleton scalars. -/
theorem
    exists_largeZero_safe_codewordRelationWitnessIndependent_gt_of_not_relationWitnessIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hnot :
      ¬ UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ Γ : Finset F,
          Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
            scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ ∧
              S < Γ.card := by
  by_contra hnone
  apply hnot
  intro u₀ u₁ hnotEligible hsafe c hc Γ hsubset hindΓ
  exact le_of_not_gt
    (fun hgt => hnone
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Γ, hsubset, hindΓ, hgt⟩)

open Classical in
/-- If the direct singleton cap fails but singleton scalars are forbidden to contain relation
edges, then the proposed scalar relation has a concrete independent set above the cap. -/
theorem exists_largeZero_safe_codewordRelationIndependent_gt_of_not_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ')
            (codewordSingletonWitnessScalars dom k a u₀ u₁ c) ∧
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
    hforbid u₀ u₁ hnotEligible hsafe c hc, hgt⟩

open Classical in
/-- Scanner for the relation-independence route.  Once support-side hypotheses and the
forbidden-edge half are fixed, failed production exposes either the usual arithmetic failure or
a concrete overlarge independent set of singleton scalars for one appearing codeword. -/
theorem exists_largeZero_safe_codewordRelationIndependentRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ')
              (codewordSingletonWitnessScalars dom k a u₀ u₁ c) ∧
              S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card) := by
  by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S
  · rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      exists_largeZero_safe_codewordRelationIndependent_gt_of_not_codewordSingletonBudgeted
        dom k a S R hforbid hperCode with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hind, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hind, hgt⟩⟩

open Classical in
/-- Scanner for the witness-local relation-independence route.  Once support-side hypotheses and
the forbidden-edge half are fixed, failed production exposes either the usual arithmetic failure
or a concrete overlarge independent subset of singleton scalars for one appearing codeword. -/
theorem exists_largeZero_safe_codewordRelationWitnessIndependentRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ Γ : Finset F,
            Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
              scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ ∧
                S < Γ.card) := by
  by_cases hind :
      UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S
  · have hperCode :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
        dom k a S R hforbid hind
    rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      exists_largeZero_safe_codewordRelationWitnessIndependent_gt_of_not_relationWitnessIndependence
        dom k a S R hind with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Γ, hsubset, hindΓ, hgt⟩
    exact
      ⟨u₀, u₁, hnotEligible, hsafe, Or.inr
        ⟨c, hc, Γ, hsubset, hindΓ, hgt⟩⟩

open Classical in
/-- Full scanner for the witness-local relation route.  Without assuming the forbidden-edge half,
failed production exposes either an actual relation edge among singleton witnesses, the usual
arithmetic failure, or an over-cap independent subset of singleton scalars. -/
theorem exists_largeZero_safe_codewordRelationWitnessRouteObstruction_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ((∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ∃ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
              ∃ γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
                γ ≠ γ' ∧ R u₀ u₁ c γ γ') ∨
          (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
              + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
            ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ Γ : Finset F,
              Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
                scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ ∧
                  S < Γ.card)) := by
  by_cases hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R
  · rcases
      exists_largeZero_safe_codewordRelationWitnessIndependentRouteFailure_of_not_budgeted
        dom k a L S B R hSupport hFits hZeroSafe hforbid hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr hfail⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge
        dom k a R).mp hforbid with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, γ', hγ', hne, hR⟩
    exact
      ⟨u₀, u₁, hnotEligible, hsafe, Or.inl
        ⟨c, hc, γ, hγ, γ', hγ', hne, hR⟩⟩

section SourceAudit

#print axioms codewordSingletonSupportRatioCover
#print axioms mem_codewordSingletonSupportRatioCover
#print axioms supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
#print axioms exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
#print axioms codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover
#print axioms codewordSingletonWitnessScalars_card_le_supportRatioCover_card
#print axioms codewordSingletonSupportRatioCover_fst_fiber_eq
#print axioms codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
#print axioms codewordSingletonSupportRatioCover_card_eq_sum_choose
#print axioms supportRatioFiber_card_le_directionSupportSet_card
#print axioms disjoint_supportRatioFiber_of_ne
#print axioms pairwiseDisjoint_supportRatioFiber
#print axioms directionSupportSet_card_eq_sum_supportRatioFiber
#print axioms sum_supportRatioFiber_card_le_directionSupportSet_card
#print axioms codewordSingletonWitnessScalars_card_mul_sub_zeroAgreement_le_support
#print axioms
  codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement_of_ratioPartition
#print axioms support_div_le_choose_of_pos_le
#print axioms support_div_sub_zeroAgreement_le_support_choose_of_zeroSafe
#print axioms codewordSingletonWitnessScalars_card_le_support_choose_via_denominator
#print axioms codewordSingletonSupportRatioCover_card_le_singletonWitness_card_mul_choose
#print axioms codewordSingletonSupportRatioCover_card_le_field_card_mul_choose
#print axioms codewordSingletonSupportRatioCover_snd_injOn
#print axioms codewordSingletonSupportRatioCover_image_snd_subset_support_powerset
#print axioms codewordSingletonSupportRatioCover_card_le_support_choose
#print axioms codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
#print axioms UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted
#print axioms UniformLargeZeroSafeCodewordSupportChooseBudgeted
#print axioms codewordSupportChooseWeight
#print axioms UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted
#print axioms singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe
#print axioms codewordSupportChooseWeight_le_lineAppearingCodewords_card_mul
#print axioms lineBadScalars_card_le_of_weight_add_codewordSupportChoose_le_two_mul
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseWeightBudget
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseWeightBudget
#print axioms
  uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_of_codewordSupportChooseBudget
#print axioms
  not_uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_iff_exists_weight_gt
#print axioms
  exists_largeZero_safe_codewordSupportChooseWeight_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
#print axioms
  not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
#print axioms uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_of_supportChoose
#print axioms uniformCodewordSupportRatioCoverBudgeted_of_supportChooseBudgeted
#print axioms
  exists_largeZero_safe_codewordSupportRatioCoverChoose_gt_of_not_coverBudgeted
#print axioms
  not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_iff_exists_choose_gt
#print axioms
  exists_largeZero_safe_codewordSupportRatioCoverFieldChoose_gt_of_not_coverBudgeted
#print axioms
  exists_largeZero_safe_codewordSupportRatioCover_gt_of_not_codewordSingletonBudgeted
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonSupportRatioCoverBudget
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseBudget
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportRatioCoverBudget
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseBudget
#print axioms
  exists_largeZero_safe_codewordSupportRatioCoverRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordSupportChooseRouteFailure_of_not_budgeted
#print axioms scalarRelationIndependent
#print axioms not_scalarRelationIndependent_iff_exists_edge
#print axioms UniformLargeZeroSafeCodewordSingletonRelationForbidden
#print axioms not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge
#print axioms UniformLargeZeroSafeCodewordRelationIndependenceBudgeted
#print axioms UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationIndependence
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted
#print axioms
  relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden
#print axioms
  not_relationWitnessIndependenceBudgeted_iff_exists_singleton_card_gt_of_forbidden
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationIndependence
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationIndependence
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationWitnessIndependence
#print axioms
  exists_largeZero_safe_codewordRelationWitnessIndependent_gt_of_not_relationWitnessIndependence
#print axioms
  exists_largeZero_safe_codewordRelationIndependent_gt_of_not_codewordSingletonBudgeted
#print axioms
  exists_largeZero_safe_codewordRelationIndependentRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordRelationWitnessIndependentRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordRelationWitnessRouteObstruction_of_not_budgeted
end SourceAudit

end ProximityGap.Ownership
