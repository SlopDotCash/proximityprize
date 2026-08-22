/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterProjectiveExtremeZeroSplit
import ArkLib.Data.CodingTheory.ProximityGap.InterleavedListMCACollapse
import ArkLib.Data.CodingTheory.ProximityGap.ScaleBracketFull

/-!
# Joint-witness list and fresh-coordinate charge at the P1 predecessor

The projective extreme-zero split can produce a threshold-size joint explanation of the original
stack.  This file tests the natural next step: bound all such explanations by ordinary Johnson,
then charge every MCA witness to a coordinate outside one known joint-agreement set.

Two parts work cleanly.

* Distinct Reed--Solomon codeword pairs jointly agreeing with a fixed stack on at least the
  predecessor threshold have pairwise agreement at most `k - 1`.  The exact-diagonal Johnson /
  constant-weight Plotkin bound therefore limits the threshold interleaved list to **five**.
* An MCA witness must contain a coordinate outside every known joint-agreement set: otherwise the
  known codeword pair itself contradicts the event's non-joint clause.  An injective choice of
  these escape coordinates would bound the bad family by the complement size.

The combination does not close the prize budget.  The complement of a threshold-size witness has
size `N - predecessorThreshold = 480946858`; two such fibers fit below `N`, but the ordinary
Johnson cap is five and already three fibers exceed `N`.  More importantly, the MCA clauses alone
give existence of an escape coordinate, not injectivity of the scalar-to-coordinate charge.  Thus
this route isolates a real missing rigidity statement rather than proving the exact pin.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ProximityGap.JointWitnessCharge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-- The part of an event witness outside a fixed joint-agreement set. -/
def freshPart (J S : Finset ι) : Finset ι := S \ J

/-- If `(q₀,q₁)` explains the stack on `J`, every set on which the stack is declared not jointly
explainable must contain a coordinate outside `J`. -/
theorem freshPart_nonempty_of_not_pairJointAgreesOn
    (C : Set (ι → A)) {J S : Finset ι} {u₀ u₁ q₀ q₁ : ι → A}
    (hq₀ : q₀ ∈ C) (hq₁ : q₁ ∈ C)
    (hJ : ∀ i ∈ J, q₀ i = u₀ i ∧ q₁ i = u₁ i)
    (hno : ¬ pairJointAgreesOn C S u₀ u₁) :
    (freshPart J S).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hno
  refine ⟨q₀, hq₀, q₁, hq₁, fun i hi ↦ ?_⟩
  apply hJ i
  by_contra hiJ
  have : i ∈ freshPart J S := by
    exact Finset.mem_sdiff.mpr ⟨hi, hiJ⟩
  rw [hempty] at this
  simp at this

/-- A full MCA event exposes an event witness and a fresh coordinate outside any fixed joint
explanation set.  The line codeword and the agreement-size certificate are retained for later
charging arguments. -/
theorem mcaEvent_exists_fresh_coordinate
    (C : Set (ι → A)) {δ : ℝ≥0} {u₀ u₁ q₀ q₁ : ι → A} {γ : F}
    {J : Finset ι} (hq₀ : q₀ ∈ C) (hq₁ : q₁ ∈ C)
    (hJ : ∀ i ∈ J, q₀ i = u₀ i ∧ q₁ i = u₁ i)
    (hev : mcaEvent (F := F) C δ u₀ u₁ γ) :
    ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ∃ i ∈ S, i ∉ J := by
  obtain ⟨S, hScard, hw, hno⟩ := hev
  obtain ⟨i, hiFresh⟩ :=
    freshPart_nonempty_of_not_pairJointAgreesOn C hq₀ hq₁ hJ hno
  exact ⟨S, hScard, hw, i, (Finset.mem_sdiff.mp hiFresh).1,
    (Finset.mem_sdiff.mp hiFresh).2⟩

/-- A genuinely injective escape-coordinate assignment gives the hoped-for complement bound.
This is the exact combinatorial consumer; `mcaEvent_exists_fresh_coordinate` supplies the range
condition but not the injectivity premise. -/
theorem card_le_complement_of_injective_fresh_charge
    (G : Finset F) (J : Finset ι) (charge : { γ // γ ∈ G } → ι)
    (hfresh : ∀ γ, charge γ ∉ J)
    (hinj : Function.Injective charge) :
    G.card ≤ Fintype.card ι - J.card := by
  classical
  have hmap : ∀ γ : { γ // γ ∈ G }, charge γ ∈ (Finset.univ \ J) := by
    intro γ
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfresh γ⟩
  have hcard := Finset.card_le_card_of_injOn
    (f := charge)
    (s := (Finset.univ : Finset { γ // γ ∈ G }))
    (t := Finset.univ \ J)
    (fun γ _ ↦ hmap γ)
    (fun γ _ γ' _ h ↦ hinj h)
  rw [Finset.card_univ, Fintype.card_coe, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ] at hcard
  exact hcard

/-- If the charged family is larger than twice the fresh-coordinate set, some fresh coordinate
receives at least three charges.  This is the useful replacement when injectivity fails. -/
theorem exists_fresh_coordinate_with_three_charges
    (G : Finset F) (J : Finset ι) (charge : { γ // γ ∈ G } → ι)
    (hfresh : ∀ γ, charge γ ∉ J)
    (hbig : 2 * (Fintype.card ι - J.card) < G.card) :
    ∃ i ∈ (Finset.univ \ J),
      2 < ((Finset.univ : Finset { γ // γ ∈ G }).filter
        (fun γ ↦ charge γ = i)).card := by
  classical
  have hmap : ∀ γ ∈ (Finset.univ : Finset { γ // γ ∈ G }),
      charge γ ∈ (Finset.univ \ J) := by
    intro γ _
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfresh γ⟩
  have htcard : (Finset.univ \ J).card = Fintype.card ι - J.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
  rw [htcard, Finset.card_univ, Fintype.card_coe]
  simpa only [Nat.mul_comm] using hbig

end ProximityGap.JointWitnessCharge

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.MCAFloorFactorization
open ProximityGap.SpikeFloor
open ProximityGap.Ownership
open ProximityGap.ExtremeZeroJohnsonBand
open ProximityGap.JointWitnessCharge
open Round17CAPair InterleavedMCACollapse
open P1RateQuarterScaleArithmetic
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterPredecessorGenericSplit

local instance localInstance_P1RateQuarterJointWitnessCharge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterJointWitnessCharge_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-- The finite presentation of the predecessor Reed--Solomon code used by `interleavedList`. -/
noncomputable def predecessorCodeFinset (dom : Fin N ↪ F) : Finset (Fin N → F) :=
  (Set.toFinite (predecessorCode dom : Set (Fin N → F))).toFinset

/-- Codeword pairs jointly agreeing with the stack on at least `a` coordinates. -/
noncomputable def predecessorJointList
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (a : Nat) :
    Finset ((Fin N → F) × (Fin N → F)) :=
  interleavedList (predecessorCodeFinset dom) u₀ u₁ a

theorem mem_predecessorCodeFinset_iff
    (dom : Fin N ↪ F) (c : Fin N → F) :
    c ∈ predecessorCodeFinset dom ↔ c ∈ predecessorCode dom := by
  classical
  rw [predecessorCodeFinset, Set.Finite.mem_toFinset]
  rfl

theorem mem_predecessorJointList_iff
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (a : Nat)
    (p : (Fin N → F) × (Fin N → F)) :
    p ∈ predecessorJointList dom u₀ u₁ a ↔
      p.1 ∈ predecessorCode dom ∧ p.2 ∈ predecessorCode dom ∧
        a ≤ (jointAgreeSet u₀ u₁ p.1 p.2).card := by
  classical
  rw [predecessorJointList, interleavedList]
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpCode := Finset.mem_product.mp hp'.1
    exact ⟨(mem_predecessorCodeFinset_iff dom p.1).mp hpCode.1,
      (mem_predecessorCodeFinset_iff dom p.2).mp hpCode.2, hp'.2⟩
  · rintro ⟨hp₀, hp₁, hagree⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨(mem_predecessorCodeFinset_iff dom p.1).mpr hp₀,
        (mem_predecessorCodeFinset_iff dom p.2).mpr hp₁⟩, hagree⟩

/-- A threshold-size `pairJointAgreesOn` witness is exactly a codeword pair in the threshold
interleaved list which agrees on the specified witness set. -/
theorem pairJointAgreesOn_iff_exists_mem_predecessorJointList
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (S : Finset (Fin N))
    (hScard : predecessorThreshold ≤ S.card) :
    pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁ ↔
      ∃ p ∈ predecessorJointList dom u₀ u₁ predecessorThreshold,
        ∀ i ∈ S, p.1 i = u₀ i ∧ p.2 i = u₁ i := by
  classical
  constructor
  · rintro ⟨q₀, hq₀, q₁, hq₁, hagree⟩
    refine ⟨(q₀, q₁), ?_, hagree⟩
    apply (mem_predecessorJointList_iff dom u₀ u₁ predecessorThreshold _).mpr
    refine ⟨hq₀, hq₁, hScard.trans (Finset.card_le_card ?_)⟩
    intro i hi
    rw [jointAgreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hagree i hi).1.symm, (hagree i hi).2.symm⟩
  · rintro ⟨p, hp, hagree⟩
    have hp' :=
      (mem_predecessorJointList_iff dom u₀ u₁ predecessorThreshold p).mp hp
    exact ⟨p.1, hp'.1, p.2, hp'.2.1, hagree⟩

/-- Distinct predecessor codeword pairs have at most `k - 1` common joint-agreement coordinates
with a fixed received stack. -/
theorem jointAgreeSet_inter_card_le_k_sub_one
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    {p q : (Fin N → F) × (Fin N → F)}
    (hp₀ : p.1 ∈ predecessorCode dom) (hp₁ : p.2 ∈ predecessorCode dom)
    (hq₀ : q.1 ∈ predecessorCode dom) (hq₁ : q.2 ∈ predecessorCode dom)
    (hpq : p ≠ q) :
    ((jointAgreeSet u₀ u₁ p.1 p.2) ∩
      (jointAgreeSet u₀ u₁ q.1 q.2)).card ≤ k - 1 := by
  classical
  by_cases hfirst : p.1 = q.1
  · have hsecond : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfirst h)
    have hsub : (jointAgreeSet u₀ u₁ p.1 p.2) ∩
        (jointAgreeSet u₀ u₁ q.1 q.2) ⊆ agreeSet p.2 q.2 := by
      intro i hi
      rw [Finset.mem_inter, jointAgreeSet, jointAgreeSet,
        Finset.mem_filter, Finset.mem_filter] at hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi.1.2.2.symm.trans hi.2.2.2⟩
    calc
      ((jointAgreeSet u₀ u₁ p.1 p.2) ∩
          (jointAgreeSet u₀ u₁ q.1 q.2)).card
          ≤ (agreeSet p.2 q.2).card := Finset.card_le_card hsub
      _ ≤ k - 1 := by
        apply rsCode_pairwise_agreeSet_card_le dom (by norm_num [k])
        · exact (mem_rsCode_iff_mem_reedSolomonCode dom k p.2).mpr hp₁
        · exact (mem_rsCode_iff_mem_reedSolomonCode dom k q.2).mpr hq₁
        · exact hsecond
  · have hsub : (jointAgreeSet u₀ u₁ p.1 p.2) ∩
        (jointAgreeSet u₀ u₁ q.1 q.2) ⊆ agreeSet p.1 q.1 := by
      intro i hi
      rw [Finset.mem_inter, jointAgreeSet, jointAgreeSet,
        Finset.mem_filter, Finset.mem_filter] at hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi.1.2.1.symm.trans hi.2.2.1⟩
    calc
      ((jointAgreeSet u₀ u₁ p.1 p.2) ∩
          (jointAgreeSet u₀ u₁ q.1 q.2)).card
          ≤ (agreeSet p.1 q.1).card := Finset.card_le_card hsub
      _ ≤ k - 1 := by
        apply rsCode_pairwise_agreeSet_card_le dom (by norm_num [k])
        · exact (mem_rsCode_iff_mem_reedSolomonCode dom k p.1).mpr hp₀
        · exact (mem_rsCode_iff_mem_reedSolomonCode dom k q.1).mpr hq₀
        · exact hfirst

/-- Subtraction-free exact-diagonal Johnson rearranges to the sharp natural-number denominator. -/
theorem johnson_core_to_subtracted {L n a p : Nat}
    (hap : p ≤ a) (hgap : n * p ≤ a ^ 2)
    (hcore : L * a ^ 2 + n * p ≤ n * a + L * (n * p)) :
    L * (a ^ 2 - n * p) ≤ n * (a - p) := by
  have hleft : L * a ^ 2 = L * (a ^ 2 - n * p) + L * (n * p) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hgap]
  have hright : n * a = n * (a - p) + n * p := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hap]
  rw [hleft, hright] at hcore
  omega

theorem predecessor_jointList_plotkin_ratio_eq :
    N * (predecessorThreshold - (k - 1)) /
      (predecessorThreshold ^ 2 - N * (k - 1)) = 5 := by
  norm_num [N, k, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- Ordinary exact-diagonal Johnson bounds the predecessor threshold interleaved list by five. -/
theorem predecessorJointList_card_le_five
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) :
    (predecessorJointList dom u₀ u₁ predecessorThreshold).card ≤ 5 := by
  classical
  let L := predecessorJointList dom u₀ u₁ predecessorThreshold
  let A : ((Fin N → F) × (Fin N → F)) → Finset (Fin N) :=
    fun p ↦ jointAgreeSet u₀ u₁ p.1 p.2
  have hsize : ∀ p ∈ L, predecessorThreshold ≤ (A p).card := by
    intro p hp
    exact (mem_predecessorJointList_iff dom u₀ u₁ predecessorThreshold p).mp hp |>.2.2
  have hpair : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → (A p ∩ A q).card ≤ k - 1 := by
    intro p hp q hq hpq
    have hp' :=
      (mem_predecessorJointList_iff dom u₀ u₁ predecessorThreshold p).mp hp
    have hq' :=
      (mem_predecessorJointList_iff dom u₀ u₁ predecessorThreshold q).mp hq
    exact jointAgreeSet_inter_card_le_k_sub_one dom u₀ u₁
      hp'.1 hp'.2.1 hq'.1 hq'.2.1 hpq
  have hcore := R15Bracket.johnson_core L A predecessorThreshold (k - 1)
    hsize hpair (by
      norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, k, m, r, d])
  simp only [Fintype.card_fin] at hcore
  have hgap : N * (k - 1) ≤ predecessorThreshold ^ 2 := by
    norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, k, N, m, r, d]
  have hsub : L.card * (predecessorThreshold ^ 2 - N * (k - 1)) ≤
      N * (predecessorThreshold - (k - 1)) :=
    johnson_core_to_subtracted
      (L := L.card) (n := N) (a := predecessorThreshold) (p := k - 1)
      (by norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, k, m, r, d])
      hgap hcore
  have hdenPos : 0 < predecessorThreshold ^ 2 - N * (k - 1) := by
    norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, k, N, m, r, d]
  calc
    L.card ≤ N * (predecessorThreshold - (k - 1)) /
        (predecessorThreshold ^ 2 - N * (k - 1)) :=
      (Nat.le_div_iff_mul_le hdenPos).2 hsub
    _ = 5 := predecessor_jointList_plotkin_ratio_eq

/-! ## Exact coefficient audit for fresh-coordinate charging -/

theorem predecessor_fresh_complement_eq :
    N - predecessorThreshold = 480946858 := by
  norm_num [N, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- Two perfectly injective fresh-coordinate fibers would fit under the prize budget. -/
theorem two_fresh_fibers_lt_N :
    2 * (N - predecessorThreshold) < N := by
  norm_num [N, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- Three fresh-coordinate fibers already exceed the prize budget. -/
theorem N_lt_three_fresh_fibers :
    N < 3 * (N - predecessorThreshold) := by
  norm_num [N, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- In particular, multiplying the ordinary Johnson cap `5` by the fresh complement is far above
the desired bound. -/
theorem N_lt_johnsonCap_mul_freshComplement :
    N < 5 * (N - predecessorThreshold) := by
  norm_num [N, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

theorem johnsonCap_mul_freshComplement_eq :
    5 * (N - predecessorThreshold) = 2404734290 := by
  norm_num [N, predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

/-- For a threshold-size known joint set, every over-budget family of selected fresh charges has
three members on one fresh coordinate.  A proof that such a triple is impossible for predecessor
RS MCA witnesses would close this fixed-witness branch. -/
theorem exists_fresh_coordinate_with_three_charges_of_threshold_overBudget
    (G : Finset F) (J : Finset (Fin N))
    (charge : { γ // γ ∈ G } → Fin N)
    (hfresh : ∀ γ, charge γ ∉ J)
    (hJcard : predecessorThreshold ≤ J.card)
    (hover : N < G.card) :
    ∃ i ∈ (Finset.univ \ J),
      2 < ((Finset.univ : Finset { γ // γ ∈ G }).filter
        (fun γ ↦ charge γ = i)).card := by
  apply exists_fresh_coordinate_with_three_charges G J charge hfresh
  have hcomp : N - J.card ≤ N - predecessorThreshold :=
    Nat.sub_le_sub_left hJcard N
  have htwo : 2 * (N - J.card) < N :=
    (Nat.mul_le_mul_left 2 hcomp).trans_lt two_fresh_fibers_lt_N
  simpa only [Fintype.card_fin] using htwo.trans hover

end ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge

/-! ## The bare MCA clause does not supply injectivity -/

namespace ProximityGap.JointWitnessCharge.ClauseOnlyCounterexample

abbrev F3 := ZMod 3
abbrev I2 := Fin 2

def q₀ : I2 → F3 := fun _ ↦ 0
def q₁ : I2 → F3 := fun i ↦ if i = 0 then 0 else 2
def u₀ : I2 → F3 := fun i ↦ if i = 0 then 0 else 1
def u₁ : I2 → F3 := fun i ↦ if i = 0 then 0 else 1

def C : Set (I2 → F3) := {q₀, q₁}
def J : Finset I2 := {0}
def S : Finset I2 := {1}
def G : Finset F3 := {1, 2}

theorem knownJointAgreement : pairJointAgreesOn C J u₀ u₁ := by
  refine ⟨q₀, by simp [C], q₁, by simp [C], ?_⟩
  intro i hi
  fin_cases i <;> simp [J, q₀, q₁, u₀, u₁] at hi ⊢

theorem not_pairJointAgreesOn_S : ¬ pairJointAgreesOn C S u₀ u₁ := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  have hv := (hagree (1 : I2) (by simp [S])).1
  simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hv₀
  rcases hv₀ with rfl | rfl
  · exact (show q₀ (1 : I2) ≠ u₀ 1 by decide) hv
  · exact (show q₁ (1 : I2) ≠ u₀ 1 by decide) hv

theorem half_mass :
    (1 - (1 / 2 : ℝ≥0)) * Fintype.card I2 = 1 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
  norm_num

theorem mcaEvent_one :
    mcaEvent (F := F3) C (1 / 2 : ℝ≥0) u₀ u₁ 1 := by
  refine ⟨S, by rw [half_mass]; norm_num [S], ⟨q₁, by simp [C], ?_⟩,
    not_pairJointAgreesOn_S⟩
  intro i hi
  fin_cases i
  · simp [S] at hi
  · change (2 : F3) = 1 + 1 * 1
    decide

theorem mcaEvent_two :
    mcaEvent (F := F3) C (1 / 2 : ℝ≥0) u₀ u₁ 2 := by
  refine ⟨S, by rw [half_mass]; norm_num [S], ⟨q₀, by simp [C], ?_⟩,
    not_pairJointAgreesOn_S⟩
  intro i hi
  fin_cases i
  · simp [S] at hi
  · change (0 : F3) = 1 + 2 * 1
    decide

theorem every_G_scalar_is_mcaEvent :
    ∀ γ ∈ G, mcaEvent (F := F3) C (1 / 2 : ℝ≥0) u₀ u₁ γ := by
  intro γ hγ
  simp only [G, Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl
  · exact mcaEvent_one
  · exact mcaEvent_two

/-- Both bad scalars have the same only possible fresh coordinate, so no injective fresh charge
exists.  This is a counterexample for arbitrary set codes, not for the predecessor RS code. -/
theorem not_exists_injective_fresh_charge :
    ¬ ∃ charge : { γ // γ ∈ G } → I2,
      (∀ γ, charge γ ∉ J) ∧ Function.Injective charge := by
  rintro ⟨charge, hfresh, hinj⟩
  have hcard := card_le_complement_of_injective_fresh_charge G J charge hfresh hinj
  have hG : G.card = 2 := by decide
  have hJ : J.card = 1 := by decide
  have hI : Fintype.card I2 = 2 := by decide
  rw [hG, hJ, hI] at hcard
  omega

end ProximityGap.JointWitnessCharge.ClauseOnlyCounterexample

/-! ## Axiom audit -/

open ProximityGap.JointWitnessCharge
open ProximityGap.JointWitnessCharge.ClauseOnlyCounterexample
open ArkLib.ProximityGap.Frontier.P1RateQuarterJointWitnessCharge

#print axioms freshPart_nonempty_of_not_pairJointAgreesOn
#print axioms mcaEvent_exists_fresh_coordinate
#print axioms card_le_complement_of_injective_fresh_charge
#print axioms exists_fresh_coordinate_with_three_charges
#print axioms jointAgreeSet_inter_card_le_k_sub_one
#print axioms pairJointAgreesOn_iff_exists_mem_predecessorJointList
#print axioms predecessorJointList_card_le_five
#print axioms N_lt_johnsonCap_mul_freshComplement
#print axioms exists_fresh_coordinate_with_three_charges_of_threshold_overBudget
#print axioms every_G_scalar_is_mcaEvent
#print axioms not_exists_injective_fresh_charge
