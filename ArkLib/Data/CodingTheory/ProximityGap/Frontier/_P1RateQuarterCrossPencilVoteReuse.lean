/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilPairwiseBonferroni
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph
import ArkLib.Data.CodingTheory.ProximityGap.ScaleBracketFull
import ArkLib.Data.CodingTheory.ProximityGap.WindowCrossWitness

/-!
# Cross-pencil vote reuse is necessary at the P1 predecessor

The fixed-pencil vote partition gives disjoint vote sets only among riders of the same
pencil.  This file records the exact extra hypothesis under which those local partitions
can be summed: vote sets belonging to distinct pencils must also be disjoint.

Under that hypothesis every non-joint rider consumes a distinct coordinate, hence there
are at most `N` riders in total.  In particular an `N + 1` bad family cannot be assembled
from private petals.  Any counterexample-scale light-pencil architecture must reuse at
least one coordinate as a vote for two distinct pencils.  The theorem is deliberately
architecture-local: the literal three-pencil construction shows that cross-pencil reuse
is possible, so no global disjointness claim is made here.

Quantitatively, a witness below the nine-rider alignment floor has at least `60,118,357`
off-alignment coordinates.  After fixing one witness as base in a prize-scale `N+1` family,
the remaining `N` partners therefore force a coordinate of load at least `60,118,357`.
The common-base identity proved below says this coordinate is missed by the base and hit by
all those partners.  (With `N+1` partners the load improves by one; that stronger statement
is kept separate so it is not confused with the exact prize-scale count.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 4300
set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

open Finset
open _root_.ProximityGap Code
open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCrossPencilVoteReuse

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ProximityGap.SharedFreshPencil
open ProximityGap.Frontier.PencilPairwiseBonferroni
open R15Bracket
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines

local instance localInstance_P1RateQuarterCrossPencilVoteReuse_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterCrossPencilVoteReuse_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

/-- The part of a chosen witness that is outside its pencil's aligned region.  Unlike the
ambient `voteSet`, this remembers actual witness incidence. -/
noncomputable def witnessVotePetal
    (u0 u1 w0 w1 : Fin N → F) (S : Finset (Fin N)) : Finset (Fin N) :=
  S \ alignedSet u0 u1 w0 w1

theorem mem_witnessVotePetal_iff
    (u0 u1 w0 w1 : Fin N → F) (S : Finset (Fin N)) (x : Fin N) :
    x ∈ witnessVotePetal u0 u1 w0 w1 S ↔
      x ∈ S ∧ x ∉ alignedSet u0 u1 w0 w1 := by
  simp [witnessVotePetal]

/-- Non-jointness makes the actual witness petal nonempty. -/
theorem witnessVotePetal_nonempty
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F) (S : Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hno : ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u0 u1) :
    (witnessVotePetal u0 u1 w0 w1 S).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hno
  refine ⟨w0, hw0, w1, hw1, fun x hx => ?_⟩
  have : x ∉ witnessVotePetal u0 u1 w0 w1 S := by rw [hempty]; simp
  rw [mem_witnessVotePetal_iff] at this
  have hal : x ∈ alignedSet u0 u1 w0 w1 := by
    by_contra hxa
    exact this ⟨hx, hxa⟩
  exact (mem_alignedSet_iff u0 u1 w0 w1 x).mp hal

/-- A family of private, nonempty coordinate petals has at most `N` members. -/
theorem private_petals_card_le_N (J : Finset ι) (V : ι → Finset (Fin N))
    (hne : ∀ j ∈ J, (V j).Nonempty)
    (hdisj : (J : Set ι).PairwiseDisjoint V) :
    J.card ≤ N := by
  calc
    J.card = ∑ _j ∈ J, 1 := by simp
    _ ≤ ∑ j ∈ J, (V j).card := by
      exact Finset.sum_le_sum fun j hj => Finset.card_pos.mpr (hne j hj)
    _ = (J.biUnion V).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = N := Fintype.card_fin N

/-- An over-budget private-petal family necessarily contains a reused coordinate. -/
theorem cross_pencil_reuse_of_N_lt_card (J : Finset ι) (V : ι → Finset (Fin N))
    (hne : ∀ j ∈ J, (V j).Nonempty) (hover : N < J.card) :
    ∃ j ∈ J, ∃ j' ∈ J, j ≠ j' ∧ ¬Disjoint (V j) (V j') := by
  by_contra h
  push Not at h
  have hdisj : (J : Set ι).PairwiseDisjoint V := by
    intro j hj j' hj' hjj'
    exact h j hj j' hj' hjj'
  exact (Nat.not_lt_of_ge (private_petals_card_le_N J V hne hdisj)) hover

/-- Specialized to the vote petals produced by an arbitrary assignment of riders to
pencils.  Once every assigned rider is non-joint (and therefore has a nonempty vote set),
an `N + 1` family forces a coordinate to vote on two distinct assignments. -/
theorem vote_reuse_of_overBudget
    (J : Finset ι)
    (u0 u1 : Fin N → F)
    (w0 w1 : ι → Fin N → F)
    (gamma : ι → F)
    (hne : ∀ j ∈ J,
      (voteSet u0 u1 (w0 j) (w1 j) (gamma j)).Nonempty)
    (hover : N < J.card) :
    ∃ j ∈ J, ∃ j' ∈ J, j ≠ j' ∧
      ¬Disjoint
        (voteSet u0 u1 (w0 j) (w1 j) (gamma j))
        (voteSet u0 u1 (w0 j') (w1 j') (gamma j')) := by
  exact cross_pencil_reuse_of_N_lt_card J
    (fun j => voteSet u0 u1 (w0 j) (w1 j) (gamma j)) hne hover

/-- **Witness-level reuse theorem.**  More than `N` non-joint assignments force two
distinct chosen witnesses to share a coordinate which is outside both pencils' aligned
regions.  Thus the private-petal architecture cannot scale to the predecessor target;
all surviving scale-up attempts must create genuine cross-pencil witness overlap. -/
theorem witness_overlap_outside_both_alignments_of_overBudget
    (dom : Fin N ↪ F)
    (J : Finset ι)
    (u0 u1 : Fin N → F)
    (w0 w1 : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hw0 : ∀ j ∈ J, w0 j ∈ predecessorCode dom)
    (hw1 : ∀ j ∈ J, w1 j ∈ predecessorCode dom)
    (hno : ∀ j ∈ J,
      ¬pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) (S j) u0 u1)
    (hover : N < J.card) :
    ∃ j ∈ J, ∃ j' ∈ J, ∃ x,
      j ≠ j' ∧ x ∈ S j ∧ x ∈ S j' ∧
      x ∉ alignedSet u0 u1 (w0 j) (w1 j) ∧
      x ∉ alignedSet u0 u1 (w0 j') (w1 j') := by
  let V : ι → Finset (Fin N) := fun j =>
    witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  have hne : ∀ j ∈ J, (V j).Nonempty := by
    intro j hj
    exact witnessVotePetal_nonempty dom u0 u1 (w0 j) (w1 j) (S j)
      (hw0 j hj) (hw1 j hj) (hno j hj)
  obtain ⟨j, hj, j', hj', hjj', hnd⟩ :=
    cross_pencil_reuse_of_N_lt_card J V hne hover
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨x, hx, hx'⟩ := hnd
  rw [mem_witnessVotePetal_iff] at hx hx'
  exact ⟨j, hj, j', hj', x, hjj', hx.1, hx'.1, hx.2, hx'.2⟩

/-! ## Quantitative reuse in the sub-nine alignment layer -/

/-- Number of selected petals using a coordinate. -/
noncomputable def petalLoad (J : Finset ι) (V : ι → Finset (Fin N)) (x : Fin N) : ℕ :=
  (J.filter fun j => x ∈ V j).card

/-- Coordinate loads and petal sizes count the same incidences. -/
theorem sum_petalLoad_eq_sum_card (J : Finset ι) (V : ι → Finset (Fin N)) :
    ∑ x : Fin N, petalLoad J V x = ∑ j ∈ J, (V j).card := by
  classical
  simp only [petalLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.sum_ite_mem]

/-- A threshold witness whose pencil alignment has size at most the nine-rider floor has
at least `60,118,357` actual off-alignment coordinates. -/
theorem subNine_witnessVotePetal_card_floor
    (u0 u1 w0 w1 : Fin N → F) (S : Finset (Fin N))
    (hS : predecessorThreshold ≤ S.card)
    (hA : (alignedSet u0 u1 w0 w1).card ≤ 532676609) :
    60118357 ≤ (witnessVotePetal u0 u1 w0 w1 S).card := by
  rw [witnessVotePetal, Finset.card_sdiff]
  have hinter : (alignedSet u0 u1 w0 w1 ∩ S).card ≤ 532676609 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hA
  have hT := predecessorThreshold_eq
  omega

/-- **P1 light-layer load spike.**  For exactly `N+1` threshold witnesses, all lying below
the nine-rider alignment floor, some coordinate belongs to at least `60,118,358` actual
off-alignment petals.  This is the quantitative form of forced cross-pencil reuse: a prize-
scale counterexample cannot hide in sparse pair overlaps. -/
theorem exists_coordinate_petalLoad_ge_60118358
    [Fintype ι]
    (u0 u1 : Fin N → F)
    (w0 w1 : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N + 1)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hA : ∀ j, (alignedSet u0 u1 (w0 j) (w1 j)).card ≤ 532676609) :
    ∃ x : Fin N, 60118358 ≤ petalLoad Finset.univ
      (fun j => witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)) x := by
  classical
  let V : ι → Finset (Fin N) := fun j =>
    witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  by_contra hload
  push Not at hload
  have hupp : (∑ x : Fin N, petalLoad Finset.univ V x) ≤ N * 60118357 := by
    calc
      (∑ x : Fin N, petalLoad Finset.univ V x) ≤ ∑ _x : Fin N, 60118357 := by
        exact Finset.sum_le_sum fun x _hx => by
          have hx : petalLoad Finset.univ V x < 60118358 := by
            simpa only [V] using hload x
          omega
      _ = N * 60118357 := by simp
  have hlow : (N + 1) * 60118357 ≤ ∑ j : ι, (V j).card := by
    calc
      (N + 1) * 60118357 = ∑ _j : ι, 60118357 := by simp [hcard]
      _ ≤ ∑ j : ι, (V j).card := by
        exact Finset.sum_le_sum fun j _hj =>
          subNine_witnessVotePetal_card_floor u0 u1 (w0 j) (w1 j) (S j)
            (hS j) (hA j)
  have heq := sum_petalLoad_eq_sum_card (Finset.univ : Finset ι) V
  simp at heq
  rw [heq] at hupp
  have hpos : 0 < 60118357 := by norm_num
  omega

/-- Exact prize-scale version after choosing one base: `N` sub-nine partners force a
coordinate load of at least the full petal floor `60,118,357`. -/
theorem exists_coordinate_petalLoad_ge_60118357_of_card_N
    [Fintype ι]
    (u0 u1 : Fin N → F)
    (w0 w1 : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hA : ∀ j, (alignedSet u0 u1 (w0 j) (w1 j)).card ≤ 532676609) :
    ∃ x : Fin N, 60118357 ≤ petalLoad Finset.univ
      (fun j => witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)) x := by
  classical
  let V : ι → Finset (Fin N) := fun j =>
    witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  by_contra hload
  push Not at hload
  have hupp : (∑ x : Fin N, petalLoad Finset.univ V x) ≤ N * 60118356 := by
    calc
      (∑ x : Fin N, petalLoad Finset.univ V x) ≤ ∑ _x : Fin N, 60118356 := by
        exact Finset.sum_le_sum fun x _hx => by
          have hx : petalLoad Finset.univ V x < 60118357 := by
            simpa only [V] using hload x
          omega
      _ = N * 60118356 := by simp
  have hlow : N * 60118357 ≤ ∑ j : ι, (V j).card := by
    calc
      N * 60118357 = ∑ _j : ι, 60118357 := by simp [hcard]
      _ ≤ ∑ j : ι, (V j).card := by
        exact Finset.sum_le_sum fun j _hj =>
          subNine_witnessVotePetal_card_floor u0 u1 (w0 j) (w1 j) (S j)
            (hS j) (hA j)
  have heq := sum_petalLoad_eq_sum_card (Finset.univ : Finset ι) V
  simp at heq
  rw [heq] at hupp
  have hNpos : 0 < N := by norm_num [N]
  omega

/-! ## Common-base interpretation of the petals -/

/-- Coordinates where a fixed base witness codeword misses its scalar line word. -/
noncomputable def baseMismatchSet
    (gamma0 : F) (p0 u0 u1 : Fin N → F) : Finset (Fin N) :=
  Finset.univ.filter fun x => p0 x ≠ u0 x + gamma0 * u1 x

theorem mem_baseMismatchSet_iff
    (gamma0 : F) (p0 u0 u1 : Fin N → F) (x : Fin N) :
    x ∈ baseMismatchSet gamma0 p0 u0 u1 ↔
      p0 x ≠ u0 x + gamma0 * u1 x := by
  simp [baseMismatchSet]

/-- At a coordinate where the partner witness agrees, its common-base divided-difference
pencil is aligned exactly when the base witness also agrees. -/
theorem commonBase_aligned_iff_base_agrees
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x) :
    x ∈ alignedSet u0 u1
      (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) ↔
      p0 x = u0 x + gamma0 * u1 x := by
  constructor
  · intro hal
    rw [mem_alignedSet_iff] at hal
    have hrepro := congrFun (pencil_reproduces_first gamma0 gamma p0 p) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
    rw [hal.1, hal.2] at hrepro
    exact hrepro.symm
  · intro hp0
    rw [mem_alignedSet_iff]
    have hinter := pencil_agrees_on_inter hgamma
      (S₁ := {x}) (S₂ := {x}) (u₀ := u0) (u₁ := u1) (p₁ := p0) (p₂ := p)
      (fun y hy => by
        rw [Finset.mem_singleton] at hy
        subst y
        exact hp0)
      (fun y hy => by
        rw [Finset.mem_singleton] at hy
        subst y
        exact hp)
      x (by simp)
    simpa only [smul_eq_mul] using hinter

/-- **Common-base petal identity.**  For a partner witness, the actual off-alignment petal
is exactly the part of that witness lying in the base witness's mismatch set.  In particular,
all cross-pencil petal reuse through one base occurs at coordinates missed by that base. -/
theorem witnessVotePetal_commonBase_eq
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (S : Finset (Fin N))
    (hp : ∀ x ∈ S, p x = u0 x + gamma * u1 x) :
    witnessVotePetal u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) S =
      S ∩ baseMismatchSet gamma0 p0 u0 u1 := by
  ext x
  rw [mem_witnessVotePetal_iff, Finset.mem_inter, mem_baseMismatchSet_iff]
  by_cases hx : x ∈ S
  · simp only [hx, true_and]
    rw [commonBase_aligned_iff_base_agrees hgamma p0 p u0 u1 x (hp x hx)]
  · simp [hx]

/-- At a partner agreement coordinate, the common-base divided-difference direction is a
Möbius function of the partner scalar.  The numerator after subtracting `u1` is exactly the
base mismatch. -/
theorem commonBase_pencilDir_apply
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x) :
    pencilDir gamma0 gamma p0 p x = u1 x +
      (gamma - gamma0)⁻¹ * (u0 x + gamma0 * u1 x - p0 x) := by
  have hne : gamma - gamma0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hgamma)
  simp only [pencilDir, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hp]
  field_simp
  ring

/-- Companion Möbius formula for the pencil base at a partner agreement coordinate. -/
theorem commonBase_pencilBase_apply
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x) :
    pencilBase gamma0 gamma p0 p x = u0 x -
      gamma * (gamma - gamma0)⁻¹ * (u0 x + gamma0 * u1 x - p0 x) := by
  have hrepro := congrFun (pencil_reproduces_second hgamma p0 p) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
  rw [commonBase_pencilDir_apply hgamma p0 p u0 u1 x hp, hp] at hrepro
  linear_combination hrepro

/-- Exact local Vandermonde determinant of two centered common-base pencil evaluations. -/
theorem commonBase_centeredMinor_eq
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x)
    (hp' : p' x = u0 x + gamma' * u1 x) :
    (pencilBase gamma0 gamma p0 p x - u0 x) *
        (pencilDir gamma0 gamma' p0 p' x - u1 x) -
      (pencilBase gamma0 gamma' p0 p' x - u0 x) *
        (pencilDir gamma0 gamma p0 p x - u1 x) =
      (gamma' - gamma) * (gamma - gamma0)⁻¹ * (gamma' - gamma0)⁻¹ *
        (u0 x + gamma0 * u1 x - p0 x) ^ 2 := by
  rw [commonBase_pencilBase_apply hgamma p0 p u0 u1 x hp,
    commonBase_pencilBase_apply hgamma' p0 p' u0 u1 x hp',
    commonBase_pencilDir_apply hgamma p0 p u0 u1 x hp,
    commonBase_pencilDir_apply hgamma' p0 p' u0 u1 x hp']
  ring

/-- At a base-missed coordinate, distinct agreeing partner scalars give a nonzero centered
`2×2` minor. -/
theorem commonBase_centeredMinor_ne_zero
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma') (hgg' : gamma ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x)
    (hp' : p' x = u0 x + gamma' * u1 x)
    (hmiss : p0 x ≠ u0 x + gamma0 * u1 x) :
    (pencilBase gamma0 gamma p0 p x - u0 x) *
        (pencilDir gamma0 gamma' p0 p' x - u1 x) -
      (pencilBase gamma0 gamma' p0 p' x - u0 x) *
        (pencilDir gamma0 gamma p0 p x - u1 x) ≠ 0 := by
  rw [commonBase_centeredMinor_eq hgamma hgamma' p0 p p' u0 u1 x hp hp']
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact sub_ne_zero.mpr (Ne.symm hgg')
      · exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hgamma))
    · exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hgamma'))
  · exact pow_ne_zero 2 (sub_ne_zero.mpr hmiss.symm)

/-- Partners whose chosen witness contains a coordinate. -/
noncomputable def partnerHitSet [Fintype ι]
    (S : ι → Finset (Fin N)) (x : Fin N) : Finset ι :=
  Finset.univ.filter fun j => x ∈ S j

theorem mem_partnerHitSet_iff [Fintype ι]
    (S : ι → Finset (Fin N)) (x : Fin N) (j : ι) :
    j ∈ partnerHitSet S x ↔ x ∈ S j := by
  simp [partnerHitSet]

/-- **Local maximal-minor clique.**  At a coordinate missed by the base, all distinct
partners whose witnesses hit that coordinate have a nonzero centered `2×2` pencil minor. -/
theorem partnerHitSet_pairwise_centeredMinor_ne_zero
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (x : Fin N) (hmiss : x ∈ baseMismatchSet gamma0 p0 u0 u1) :
    ∀ j ∈ partnerHitSet S x, ∀ j' ∈ partnerHitSet S x, j ≠ j' →
      (pencilBase gamma0 (gamma j) p0 (p j) x - u0 x) *
          (pencilDir gamma0 (gamma j') p0 (p j') x - u1 x) -
        (pencilBase gamma0 (gamma j') p0 (p j') x - u0 x) *
          (pencilDir gamma0 (gamma j) p0 (p j) x - u1 x) ≠ 0 := by
  intro j hj j' hj' hjj'
  rw [mem_partnerHitSet_iff] at hj hj'
  rw [mem_baseMismatchSet_iff] at hmiss
  exact commonBase_centeredMinor_ne_zero (hgamma0 j) (hgamma0 j')
    (fun heq => hjj' (hgamma heq)) p0 (p j) (p j') u0 u1 x
    (hp j x hj) (hp j' x hj') hmiss

/-- A base-missed coordinate separates the directions, hence the full pencil keys, of any
two distinct agreeing partner scalars. -/
theorem commonBase_pencilDir_ne_of_baseMismatch
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma') (hgg' : gamma ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x)
    (hp' : p' x = u0 x + gamma' * u1 x)
    (hmiss : p0 x ≠ u0 x + gamma0 * u1 x) :
    pencilDir gamma0 gamma p0 p ≠ pencilDir gamma0 gamma' p0 p' := by
  intro heq
  have hx := congrFun heq x
  rw [commonBase_pencilDir_apply hgamma p0 p u0 u1 x hp,
    commonBase_pencilDir_apply hgamma' p0 p' u0 u1 x hp'] at hx
  have he : u0 x + gamma0 * u1 x - p0 x ≠ 0 := by
    exact sub_ne_zero.mpr hmiss.symm
  have hinv : (gamma - gamma0)⁻¹ = (gamma' - gamma0)⁻¹ := by
    apply mul_right_cancel₀ he
    linear_combination hx
  have hsub : gamma - gamma0 = gamma' - gamma0 := inv_injective hinv
  apply hgg'
  linear_combination hsub

theorem commonBase_pencilKey_ne_of_baseMismatch
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma') (hgg' : gamma ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (x : Fin N)
    (hp : p x = u0 x + gamma * u1 x)
    (hp' : p' x = u0 x + gamma' * u1 x)
    (hmiss : p0 x ≠ u0 x + gamma0 * u1 x) :
    (pencilBase gamma0 gamma p0 p, pencilDir gamma0 gamma p0 p) ≠
      (pencilBase gamma0 gamma' p0 p', pencilDir gamma0 gamma' p0 p') := by
  intro hkey
  exact commonBase_pencilDir_ne_of_baseMismatch hgamma hgamma' hgg'
    p0 p p' u0 u1 x hp hp' hmiss (congrArg Prod.snd hkey)

/-- **Cross-coordinate rank-one identity.**  For one partner agreeing at two coordinates,
the direction deviations are proportional to the two base-mismatch values.  The shared
Möbius denominator cancels. -/
theorem commonBase_directionDeviation_crossCoordinate
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (x y : Fin N)
    (hpx : p x = u0 x + gamma * u1 x)
    (hpy : p y = u0 y + gamma * u1 y) :
    (pencilDir gamma0 gamma p0 p x - u1 x) *
        (u0 y + gamma0 * u1 y - p0 y) =
      (pencilDir gamma0 gamma p0 p y - u1 y) *
        (u0 x + gamma0 * u1 x - p0 x) := by
  rw [commonBase_pencilDir_apply hgamma p0 p u0 u1 x hpx,
    commonBase_pencilDir_apply hgamma p0 p u0 u1 y hpy]
  ring

/-- The companion base deviations obey the same rank-one relation. -/
theorem commonBase_baseDeviation_crossCoordinate
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (x y : Fin N)
    (hpx : p x = u0 x + gamma * u1 x)
    (hpy : p y = u0 y + gamma * u1 y) :
    (pencilBase gamma0 gamma p0 p x - u0 x) *
        (u0 y + gamma0 * u1 y - p0 y) =
      (pencilBase gamma0 gamma p0 p y - u0 y) *
        (u0 x + gamma0 * u1 x - p0 x) := by
  rw [commonBase_pencilBase_apply hgamma p0 p u0 u1 x hpx,
    commonBase_pencilBase_apply hgamma p0 p u0 u1 y hpy]
  ring

/-- Consequently, for any two partners agreeing at both coordinates, the matrix of their
direction deviations across the two coordinates has determinant zero.  This is the precise
rank-one degeneracy of the two-coordinate lift. -/
theorem commonBase_twoPartner_directionDeviation_minor_eq_zero
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (x y : Fin N)
    (hpx : p x = u0 x + gamma * u1 x)
    (hpy : p y = u0 y + gamma * u1 y)
    (hp'x : p' x = u0 x + gamma' * u1 x)
    (hp'y : p' y = u0 y + gamma' * u1 y) :
    (pencilDir gamma0 gamma p0 p x - u1 x) *
        (pencilDir gamma0 gamma' p0 p' y - u1 y) -
      (pencilDir gamma0 gamma' p0 p' x - u1 x) *
        (pencilDir gamma0 gamma p0 p y - u1 y) = 0 := by
  rw [commonBase_pencilDir_apply hgamma p0 p u0 u1 x hpx,
    commonBase_pencilDir_apply hgamma p0 p u0 u1 y hpy,
    commonBase_pencilDir_apply hgamma' p0 p' u0 u1 x hp'x,
    commonBase_pencilDir_apply hgamma' p0 p' u0 u1 y hp'y]
  ring

/-- Functional form: on every coordinate of the partner witness, the whole direction
deviation is the single scalar `(gamma-gamma0)⁻¹` times the fixed base-mismatch function. -/
theorem commonBase_directionDeviation_on_witness
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (S : Finset (Fin N))
    (hp : ∀ x ∈ S, p x = u0 x + gamma * u1 x) :
    ∀ x ∈ S, pencilDir gamma0 gamma p0 p x - u1 x =
      (gamma - gamma0)⁻¹ * (u0 x + gamma0 * u1 x - p0 x) := by
  intro x hx
  rw [commonBase_pencilDir_apply hgamma p0 p u0 u1 x (hp x hx)]
  ring

/-- Two partners' direction deviations are globally proportional on their entire common
witness intersection.  Multiplying by their respective scalar denominators gives the same
base-mismatch function pointwise. -/
theorem commonBase_twoPartner_directionDeviation_proportional_on_inter
    {gamma0 gamma gamma' : F}
    (hgamma : gamma0 ≠ gamma) (hgamma' : gamma0 ≠ gamma')
    (p0 p p' u0 u1 : Fin N → F) (S S' : Finset (Fin N))
    (hp : ∀ x ∈ S, p x = u0 x + gamma * u1 x)
    (hp' : ∀ x ∈ S', p' x = u0 x + gamma' * u1 x) :
    ∀ x ∈ S ∩ S',
      (gamma - gamma0) * (pencilDir gamma0 gamma p0 p x - u1 x) =
        (gamma' - gamma0) * (pencilDir gamma0 gamma' p0 p' x - u1 x) := by
  intro x hx
  obtain ⟨hxS, hxS'⟩ := Finset.mem_inter.mp hx
  rw [commonBase_directionDeviation_on_witness hgamma p0 p u0 u1 S hp x hxS,
    commonBase_directionDeviation_on_witness hgamma' p0 p' u0 u1 S' hp' x hxS']
  have hne : gamma - gamma0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hgamma)
  have hne' : gamma' - gamma0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hgamma')
  simp only [← mul_assoc, mul_inv_cancel₀ hne, mul_inv_cancel₀ hne', one_mul]

/-- Centered base/direction evaluation of a pencil at one coordinate. -/
def centeredPencilEval
    (u0 u1 w0 w1 : Fin N → F) (x : Fin N) : F × F :=
  (w0 x - u0 x, w1 x - u1 x)

/-- **Full tensor factorization on a witness.**  The centered pencil pair is the outer
product of the coordinate mismatch `e(x)` and the scalar-side projective vector
`(-gamma,1)`, with common factor `(gamma-gamma0)⁻¹`. -/
theorem commonBase_centeredPencilEval_factorization_on_witness
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (S : Finset (Fin N))
    (hp : ∀ x ∈ S, p x = u0 x + gamma * u1 x) :
    ∀ x ∈ S,
      centeredPencilEval u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) x =
      let c := (gamma - gamma0)⁻¹ * (u0 x + gamma0 * u1 x - p0 x)
      (-gamma * c, c) := by
  intro x hx
  dsimp only [centeredPencilEval]
  rw [commonBase_pencilBase_apply hgamma p0 p u0 u1 x (hp x hx),
    commonBase_pencilDir_apply hgamma p0 p u0 u1 x (hp x hx)]
  apply Prod.ext <;> simp only
  · ring
  · ring

/-- On two coordinates of the same witness, the full centered pencil evaluations have zero
`2×2` determinant in either component pairing: the coordinate mode has rank one. -/
theorem commonBase_centeredPencilEval_crossCoordinate_rankOne
    {gamma0 gamma : F} (hgamma : gamma0 ≠ gamma)
    (p0 p u0 u1 : Fin N → F) (S : Finset (Fin N))
    (hp : ∀ x ∈ S, p x = u0 x + gamma * u1 x)
    {x y : Fin N} (hx : x ∈ S) (hy : y ∈ S) :
    (centeredPencilEval u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) x).1 *
      (centeredPencilEval u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) y).2 -
    (centeredPencilEval u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) y).1 *
      (centeredPencilEval u0 u1
        (pencilBase gamma0 gamma p0 p) (pencilDir gamma0 gamma p0 p) x).2 = 0 := by
  rw [commonBase_centeredPencilEval_factorization_on_witness hgamma p0 p u0 u1 S hp x hx,
    commonBase_centeredPencilEval_factorization_on_witness hgamma p0 p u0 u1 S hp y hy]
  dsimp only
  ring

/-- **Common-base load spike.**  If `N+1` partner witnesses through one fixed base all have
sub-nine pencil alignment, then the base misses a coordinate on which at least `60,118,358`
partners agree with their respective scalar line words. -/
theorem exists_baseMismatch_hit_by_60118358_partners
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N + 1)
    (hgamma : ∀ j, gamma0 ≠ gamma j)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 532676609) :
    ∃ x ∈ baseMismatchSet gamma0 p0 u0 u1,
      60118358 ≤ (Finset.univ.filter fun j : ι => x ∈ S j).card := by
  classical
  let V : ι → Finset (Fin N) := fun j => witnessVotePetal u0 u1
    (pencilBase gamma0 (gamma j) p0 (p j))
    (pencilDir gamma0 (gamma j) p0 (p j)) (S j)
  obtain ⟨x, hxload⟩ := exists_coordinate_petalLoad_ge_60118358 u0 u1
    (fun j => pencilBase gamma0 (gamma j) p0 (p j))
    (fun j => pencilDir gamma0 (gamma j) p0 (p j)) S hcard hS hA
  have hpetal : ∀ j, V j = S j ∩ baseMismatchSet gamma0 p0 u0 u1 := by
    intro j
    exact witnessVotePetal_commonBase_eq (hgamma j) p0 (p j) u0 u1 (S j) (hp j)
  have hxpos : 0 < petalLoad Finset.univ V x := by
    simpa only [V] using lt_of_lt_of_le (by norm_num : 0 < 60118358) hxload
  obtain ⟨j, hj⟩ : ∃ j, x ∈ V j := by
    have hnempty : (Finset.univ.filter fun j : ι => x ∈ V j).Nonempty := by
      exact Finset.card_pos.mp (by simpa only [petalLoad] using hxpos)
    obtain ⟨j, hj⟩ := hnempty
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  have hxmis : x ∈ baseMismatchSet gamma0 p0 u0 u1 := by
    rw [hpetal j, Finset.mem_inter] at hj
    exact hj.2
  refine ⟨x, hxmis, ?_⟩
  have hloadEq : petalLoad Finset.univ V x =
      (Finset.univ.filter fun j : ι => x ∈ S j).card := by
    simp only [petalLoad]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpetal j, Finset.mem_inter]
    constructor
    · exact fun hj => hj.1
    · intro hj
      exact ⟨hj, hxmis⟩
  rw [← hloadEq]
  simpa only [V] using hxload

/-- **Prize-scale common-base load spike.**  In a family of `N+1` witnesses, fixing one as
base leaves exactly `N` partners.  If all corresponding pencils have sub-nine alignment,
the base misses a coordinate hit by at least `60,118,357` partner witnesses. -/
theorem exists_baseMismatch_hit_by_60118357_of_N_partners
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma : ∀ j, gamma0 ≠ gamma j)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 532676609) :
    ∃ x ∈ baseMismatchSet gamma0 p0 u0 u1,
      60118357 ≤ (Finset.univ.filter fun j : ι => x ∈ S j).card := by
  classical
  let V : ι → Finset (Fin N) := fun j => witnessVotePetal u0 u1
    (pencilBase gamma0 (gamma j) p0 (p j))
    (pencilDir gamma0 (gamma j) p0 (p j)) (S j)
  obtain ⟨x, hxload⟩ := exists_coordinate_petalLoad_ge_60118357_of_card_N u0 u1
    (fun j => pencilBase gamma0 (gamma j) p0 (p j))
    (fun j => pencilDir gamma0 (gamma j) p0 (p j)) S hcard hS hA
  have hpetal : ∀ j, V j = S j ∩ baseMismatchSet gamma0 p0 u0 u1 := by
    intro j
    exact witnessVotePetal_commonBase_eq (hgamma j) p0 (p j) u0 u1 (S j) (hp j)
  have hxpos : 0 < petalLoad Finset.univ V x := by
    simpa only [V] using lt_of_lt_of_le (by norm_num : 0 < 60118357) hxload
  obtain ⟨j, hj⟩ : ∃ j, x ∈ V j := by
    have hnempty : (Finset.univ.filter fun j : ι => x ∈ V j).Nonempty := by
      exact Finset.card_pos.mp (by simpa only [petalLoad] using hxpos)
    obtain ⟨j, hj⟩ := hnempty
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  have hxmis : x ∈ baseMismatchSet gamma0 p0 u0 u1 := by
    rw [hpetal j, Finset.mem_inter] at hj
    exact hj.2
  refine ⟨x, hxmis, ?_⟩
  have hloadEq : petalLoad Finset.univ V x =
      (Finset.univ.filter fun j : ι => x ∈ S j).card := by
    simp only [petalLoad]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpetal j, Finset.mem_inter]
    exact and_iff_left hxmis
  rw [← hloadEq]
  simpa only [V] using hxload

/-- **Prize-scale sub-nine minor clique.**  The common-base load spike can be selected so
that at least `60,118,357` partners form a complete nonzero-minor family at one coordinate. -/
theorem commonBase_subNine_exists_centeredMinorClique_60118357
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 532676609) :
    ∃ x ∈ baseMismatchSet gamma0 p0 u0 u1,
      60118357 ≤ (partnerHitSet S x).card ∧
      ∀ j ∈ partnerHitSet S x, ∀ j' ∈ partnerHitSet S x, j ≠ j' →
        (pencilBase gamma0 (gamma j) p0 (p j) x - u0 x) *
            (pencilDir gamma0 (gamma j') p0 (p j') x - u1 x) -
          (pencilBase gamma0 (gamma j') p0 (p j') x - u0 x) *
            (pencilDir gamma0 (gamma j) p0 (p j) x - u1 x) ≠ 0 := by
  obtain ⟨x, hxmis, hxcard⟩ := exists_baseMismatch_hit_by_60118357_of_N_partners
    gamma0 gamma p0 u0 u1 p S hcard hgamma0 hS hp hA
  refine ⟨x, hxmis, ?_, partnerHitSet_pairwise_centeredMinor_ne_zero
    gamma0 gamma p0 u0 u1 p S hgamma0 hgamma hp x hxmis⟩
  simpa only [partnerHitSet] using hxcard

/-! ## Load injects into distinct pencils -/

/-- If different members of every key fiber have disjoint petals, the members using one
coordinate inject into their keys. -/
theorem petalLoad_le_image_card_of_fiber_disjoint
    {κ : Type*} [DecidableEq κ]
    (J : Finset ι) (V : ι → Finset (Fin N)) (key : ι → κ)
    (hdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → key j = key j' → Disjoint (V j) (V j'))
    (x : Fin N) :
    petalLoad J V x ≤ (J.image key).card := by
  classical
  unfold petalLoad
  refine Finset.card_le_card_of_injOn key ?_ ?_
  · intro j hj
    exact Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩
  · intro j hj j' hj' hkey
    by_contra hjj'
    have hjmem := (Finset.mem_filter.mp hj).2
    have hj'mem := (Finset.mem_filter.mp hj').2
    exact Finset.disjoint_left.mp
      (hdisj j (Finset.mem_filter.mp hj).1 j' (Finset.mem_filter.mp hj').1 hjj' hkey)
      hjmem hj'mem

/-- An actual witness petal is contained in its ambient pencil vote set. -/
theorem witnessVotePetal_subset_voteSet
    (u0 u1 w0 w1 : Fin N → F) (gamma : F) (S : Finset (Fin N))
    (hp : ∀ x ∈ S, w0 x + gamma * w1 x = u0 x + gamma * u1 x) :
    witnessVotePetal u0 u1 w0 w1 S ⊆ voteSet u0 u1 w0 w1 gamma := by
  intro x hx
  rw [mem_witnessVotePetal_iff] at hx
  rw [mem_voteSet_iff]
  exact ⟨hx.2, hp x hx.1⟩

/-- **Prize-scale pencil explosion.**  Fixing one base in an `N+1` family leaves `N`
partners.  If every common-base pencil lies below the nine-rider alignment floor, the
`60,118,357`-fold petal load injects into distinct pencil keys: there are at least
`60,118,357` distinct divided-difference pencils through that base. -/
theorem commonBase_distinctPencils_ge_60118357
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 532676609) :
    60118357 ≤ (Finset.univ.image fun j : ι =>
      (pencilBase gamma0 (gamma j) p0 (p j),
        pencilDir gamma0 (gamma j) p0 (p j))).card := by
  classical
  let w0 : ι → Fin N → F := fun j => pencilBase gamma0 (gamma j) p0 (p j)
  let w1 : ι → Fin N → F := fun j => pencilDir gamma0 (gamma j) p0 (p j)
  let V : ι → Finset (Fin N) := fun j =>
    witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  let key : ι → (Fin N → F) × (Fin N → F) := fun j => (w0 j, w1 j)
  obtain ⟨x, hxload⟩ := exists_coordinate_petalLoad_ge_60118357_of_card_N
    u0 u1 w0 w1 S hcard hS hA
  have hfiber : ∀ j ∈ (Finset.univ : Finset ι), ∀ j' ∈ Finset.univ,
      j ≠ j' → key j = key j' → Disjoint (V j) (V j') := by
    intro j _hj j' _hj' hjj' hkey
    have hgam : gamma j ≠ gamma j' := fun heq => hjj' (hgamma heq)
    have h0 : w0 j = w0 j' := congrArg Prod.fst hkey
    have h1 : w1 j = w1 j' := congrArg Prod.snd hkey
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have hyv := witnessVotePetal_subset_voteSet u0 u1 (w0 j) (w1 j) (gamma j) (S j)
      (fun z hz => by
        have hrepro := congrFun
          (pencil_reproduces_second (hgamma0 j) p0 (p j)) z
        change pencilBase gamma0 (gamma j) p0 (p j) z +
          gamma j * pencilDir gamma0 (gamma j) p0 (p j) z = _
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          hrepro.trans (hp j z hz)) hy
    have hyv' := witnessVotePetal_subset_voteSet u0 u1 (w0 j') (w1 j') (gamma j') (S j')
      (fun z hz => by
        have hrepro := congrFun
          (pencil_reproduces_second (hgamma0 j') p0 (p j')) z
        change pencilBase gamma0 (gamma j') p0 (p j') z +
          gamma j' * pencilDir gamma0 (gamma j') p0 (p j') z = _
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          hrepro.trans (hp j' z hz)) hy'
    rw [← h0, ← h1] at hyv'
    exact Finset.disjoint_left.mp (voteSet_disjoint u0 u1 (w0 j) (w1 j) hgam) hyv hyv'
  have himage := hxload.trans (petalLoad_le_image_card_of_fiber_disjoint
    (Finset.univ : Finset ι) V key hfiber x)
  simpa only [key, w0, w1] using himage

/-- **Unconditional per-base above-sub-nine-or-explosive dichotomy.**  For the `N` partners left
after fixing a base in an exact `N+1` family, either one common-base pencil has alignment at
least `532,676,610`, or there are at least `60,118,357` distinct common-base pencils.  The
first threshold is still below the exact Johnson threshold; this theorem does not call it a
Johnson-heavy branch. -/
theorem commonBase_aboveSubNine_or_distinctPencils_ge_60118357
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x) :
    (∃ j, 532676610 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card) ∨
    60118357 ≤ (Finset.univ.image fun j : ι =>
      (pencilBase gamma0 (gamma j) p0 (p j),
        pencilDir gamma0 (gamma j) p0 (p j))).card := by
  classical
  by_cases hheavy : ∃ j, 532676610 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card
  · exact Or.inl hheavy
  · right
    apply commonBase_distinctPencils_ge_60118357 gamma0 gamma p0 u0 u1 p S
      hcard hgamma0 hgamma hS hp
    intro j
    have hj := hheavy
    push Not at hj
    have := hj j
    omega

/-! ## Exact Johnson-boundary dichotomy -/

/-- Below the exact integral Johnson threshold, every threshold witness retains at least
`55,924,056` off-alignment coordinates. -/
theorem johnsonLight_witnessVotePetal_card_floor
    (u0 u1 w0 w1 : Fin N → F) (S : Finset (Fin N))
    (hS : predecessorThreshold ≤ S.card)
    (hA : (alignedSet u0 u1 w0 w1).card ≤ 536870910) :
    55924056 ≤ (witnessVotePetal u0 u1 w0 w1 S).card := by
  rw [witnessVotePetal, Finset.card_sdiff]
  have hinter : (alignedSet u0 u1 w0 w1 ∩ S).card ≤ 536870910 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hA
  have hT := predecessorThreshold_eq
  omega

/-- With exactly `N` partners, the Johnson-light petal floor forces the same coordinate-load
floor. -/
theorem exists_coordinate_petalLoad_ge_55924056_of_card_N
    [Fintype ι]
    (u0 u1 : Fin N → F)
    (w0 w1 : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hA : ∀ j, (alignedSet u0 u1 (w0 j) (w1 j)).card ≤ 536870910) :
    ∃ x : Fin N, 55924056 ≤ petalLoad Finset.univ
      (fun j => witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)) x := by
  classical
  let V : ι → Finset (Fin N) := fun j =>
    witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  by_contra hload
  push Not at hload
  have hupp : (∑ x : Fin N, petalLoad Finset.univ V x) ≤ N * 55924055 := by
    calc
      (∑ x : Fin N, petalLoad Finset.univ V x) ≤ ∑ _x : Fin N, 55924055 := by
        exact Finset.sum_le_sum fun x _hx => by
          have hx : petalLoad Finset.univ V x < 55924056 := by
            simpa only [V] using hload x
          omega
      _ = N * 55924055 := by simp
  have hlow : N * 55924056 ≤ ∑ j : ι, (V j).card := by
    calc
      N * 55924056 = ∑ _j : ι, 55924056 := by simp [hcard]
      _ ≤ ∑ j : ι, (V j).card := by
        exact Finset.sum_le_sum fun j _hj =>
          johnsonLight_witnessVotePetal_card_floor u0 u1 (w0 j) (w1 j) (S j)
            (hS j) (hA j)
  have heq := sum_petalLoad_eq_sum_card (Finset.univ : Finset ι) V
  simp at heq
  rw [heq] at hupp
  have hNpos : 0 < N := by norm_num [N]
  omega

/-- Exact-Johnson analogue of the common-base load spike: the selected high-load coordinate
is missed by the base and hit by at least `55,924,056` partners. -/
theorem exists_baseMismatch_hit_by_55924056_of_N_partners
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma : ∀ j, gamma0 ≠ gamma j)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 536870910) :
    ∃ x ∈ baseMismatchSet gamma0 p0 u0 u1,
      55924056 ≤ (partnerHitSet S x).card := by
  classical
  let V : ι → Finset (Fin N) := fun j => witnessVotePetal u0 u1
    (pencilBase gamma0 (gamma j) p0 (p j))
    (pencilDir gamma0 (gamma j) p0 (p j)) (S j)
  obtain ⟨x, hxload⟩ := exists_coordinate_petalLoad_ge_55924056_of_card_N u0 u1
    (fun j => pencilBase gamma0 (gamma j) p0 (p j))
    (fun j => pencilDir gamma0 (gamma j) p0 (p j)) S hcard hS hA
  have hpetal : ∀ j, V j = S j ∩ baseMismatchSet gamma0 p0 u0 u1 := by
    intro j
    exact witnessVotePetal_commonBase_eq (hgamma j) p0 (p j) u0 u1 (S j) (hp j)
  have hxpos : 0 < petalLoad Finset.univ V x := by
    simpa only [V] using lt_of_lt_of_le (by norm_num : 0 < 55924056) hxload
  obtain ⟨j, hj⟩ : ∃ j, x ∈ V j := by
    have hnempty : (Finset.univ.filter fun j : ι => x ∈ V j).Nonempty := by
      exact Finset.card_pos.mp (by simpa only [petalLoad] using hxpos)
    obtain ⟨j, hj⟩ := hnempty
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  have hxmis : x ∈ baseMismatchSet gamma0 p0 u0 u1 := by
    rw [hpetal j, Finset.mem_inter] at hj
    exact hj.2
  refine ⟨x, hxmis, ?_⟩
  have hloadEq : petalLoad Finset.univ V x = (partnerHitSet S x).card := by
    simp only [petalLoad, partnerHitSet]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpetal j, Finset.mem_inter]
    exact and_iff_left hxmis
  rw [← hloadEq]
  simpa only [V] using hxload

/-- A supplied common-base petal load injects into distinct common-base pencils. -/
theorem commonBase_petalLoad_le_distinctPencils
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (x : Fin N) :
    petalLoad Finset.univ (fun j => witnessVotePetal u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j)) (S j)) x ≤
    (Finset.univ.image fun j : ι =>
      (pencilBase gamma0 (gamma j) p0 (p j),
        pencilDir gamma0 (gamma j) p0 (p j))).card := by
  classical
  let w0 : ι → Fin N → F := fun j => pencilBase gamma0 (gamma j) p0 (p j)
  let w1 : ι → Fin N → F := fun j => pencilDir gamma0 (gamma j) p0 (p j)
  let V : ι → Finset (Fin N) := fun j => witnessVotePetal u0 u1 (w0 j) (w1 j) (S j)
  let key : ι → (Fin N → F) × (Fin N → F) := fun j => (w0 j, w1 j)
  have hfiber : ∀ j ∈ (Finset.univ : Finset ι), ∀ j' ∈ Finset.univ,
      j ≠ j' → key j = key j' → Disjoint (V j) (V j') := by
    intro j _hj j' _hj' hjj' hkey
    have hgam : gamma j ≠ gamma j' := fun heq => hjj' (hgamma heq)
    have h0 : w0 j = w0 j' := congrArg Prod.fst hkey
    have h1 : w1 j = w1 j' := congrArg Prod.snd hkey
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have hyv := witnessVotePetal_subset_voteSet u0 u1 (w0 j) (w1 j) (gamma j) (S j)
      (fun z hz => by
        have hrepro := congrFun (pencil_reproduces_second (hgamma0 j) p0 (p j)) z
        change pencilBase gamma0 (gamma j) p0 (p j) z +
          gamma j * pencilDir gamma0 (gamma j) p0 (p j) z = _
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          hrepro.trans (hp j z hz)) hy
    have hyv' := witnessVotePetal_subset_voteSet u0 u1 (w0 j') (w1 j') (gamma j') (S j')
      (fun z hz => by
        have hrepro := congrFun (pencil_reproduces_second (hgamma0 j') p0 (p j')) z
        change pencilBase gamma0 (gamma j') p0 (p j') z +
          gamma j' * pencilDir gamma0 (gamma j') p0 (p j') z = _
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          hrepro.trans (hp j' z hz)) hy'
    rw [← h0, ← h1] at hyv'
    exact Finset.disjoint_left.mp (voteSet_disjoint u0 u1 (w0 j) (w1 j) hgam) hyv hyv'
  simpa only [V, key, w0, w1] using
    petalLoad_le_image_card_of_fiber_disjoint (Finset.univ : Finset ι) V key hfiber x

/-- In the exact Johnson-light branch there are at least `55,924,056` distinct pencils
through the base. -/
theorem commonBase_johnsonLight_distinctPencils_ge_55924056
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 536870910) :
    55924056 ≤ (Finset.univ.image fun j : ι =>
      (pencilBase gamma0 (gamma j) p0 (p j),
        pencilDir gamma0 (gamma j) p0 (p j))).card := by
  obtain ⟨x, hx⟩ := exists_coordinate_petalLoad_ge_55924056_of_card_N u0 u1
    (fun j => pencilBase gamma0 (gamma j) p0 (p j))
    (fun j => pencilDir gamma0 (gamma j) p0 (p j)) S hcard hS hA
  exact hx.trans (commonBase_petalLoad_le_distinctPencils
    gamma0 gamma p0 u0 u1 p S hgamma0 hgamma hp x)

/-- **Exact Johnson-or-explosive dichotomy.**  Every prize-scale base either has a partner
pencil whose alignment square exceeds `N*(k-1)`, or emits at least `55,924,056` distinct
Johnson-light pencils. -/
theorem commonBase_johnsonHeavy_or_distinctPencils_ge_55924056
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x) :
    (∃ j, 536870911 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card) ∨
    55924056 ≤ (Finset.univ.image fun j : ι =>
      (pencilBase gamma0 (gamma j) p0 (p j),
        pencilDir gamma0 (gamma j) p0 (p j))).card := by
  classical
  by_cases hheavy : ∃ j, 536870911 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card
  · exact Or.inl hheavy
  · right
    apply commonBase_johnsonLight_distinctPencils_ge_55924056
      gamma0 gamma p0 u0 u1 p S hcard hgamma0 hgamma hS hp
    intro j
    push Not at hheavy
    have := hheavy j
    omega

/-- **Exact Johnson-heavy-or-minor-clique dichotomy.**  Every prize-scale base either has a
genuinely Johnson-heavy partner pencil, or one base-missed coordinate carries at least
`55,924,056` partners with pairwise nonzero centered pencil minors. -/
theorem commonBase_johnsonHeavy_or_centeredMinorClique_55924056
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x) :
    (∃ j, 536870911 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card) ∨
    ∃ x ∈ baseMismatchSet gamma0 p0 u0 u1,
      55924056 ≤ (partnerHitSet S x).card ∧
      ∀ j ∈ partnerHitSet S x, ∀ j' ∈ partnerHitSet S x, j ≠ j' →
        (pencilBase gamma0 (gamma j) p0 (p j) x - u0 x) *
            (pencilDir gamma0 (gamma j') p0 (p j') x - u1 x) -
          (pencilBase gamma0 (gamma j') p0 (p j') x - u0 x) *
            (pencilDir gamma0 (gamma j) p0 (p j) x - u1 x) ≠ 0 := by
  classical
  by_cases hheavy : ∃ j, 536870911 ≤ (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card
  · exact Or.inl hheavy
  · right
    have hA : ∀ j, (alignedSet u0 u1
        (pencilBase gamma0 (gamma j) p0 (p j))
        (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 536870910 := by
      intro j
      push Not at hheavy
      have := hheavy j
      omega
    obtain ⟨x, hxmis, hxcard⟩ := exists_baseMismatch_hit_by_55924056_of_N_partners
      gamma0 gamma p0 u0 u1 p S hcard hgamma0 hS hp hA
    exact ⟨x, hxmis, hxcard, partnerHitSet_pairwise_centeredMinor_ne_zero
      gamma0 gamma p0 u0 u1 p S hgamma0 hgamma hp x hxmis⟩

/-- The heavy threshold used above is exactly beyond the RS Johnson square. -/
theorem exactJohnsonAlignment_square_gt : N * (k - 1) < 536870911 ^ 2 := by
  norm_num [N, k]

/-- At the first integer above the Johnson square, the denominator is exactly one. -/
theorem exactJohnsonMinimal_denominator_eq :
    536870911 ^ 2 - N * (k - 1) = 1 := by
  norm_num [N, k]

/-- Consequently the ordinary Johnson cardinality ratio at the minimal heavy threshold is
astronomical and completely vacuous for an `N`-partner family. -/
theorem exactJohnsonMinimal_ratio_eq :
    N * (536870911 - (k - 1)) /
      (536870911 ^ 2 - N * (k - 1)) = 288230376151711744 := by
  norm_num [N, k]

theorem N_le_exactJohnsonMinimal_ratio :
    N ≤ N * (536870911 - (k - 1)) /
      (536870911 ^ 2 - N * (k - 1)) := by
  rw [exactJohnsonMinimal_ratio_eq]
  norm_num [N]

/-- By contrast, the alignment forced by ten riders has ordinary Johnson ratio `108`; this
quantifies why the ten-rider crossover is useful while the bare square crossing is not. -/
theorem tenRiderAlignment_johnson_ratio_eq :
    N * (539356427 - (k - 1)) /
      (539356427 ^ 2 - N * (k - 1)) = 108 := by
  norm_num [N, k]

/-! ## A single-coordinate minor clique is not itself contradictory -/

/-- The standard affine chart of the projective line. -/
def projectiveMinorModel {L : ℕ} (j : Fin L) : F × F := (-(j.val : F), 1)

/-- Up to the field characteristic, the standard projective-line model has a nonzero minor
for every distinct pair.  Thus pairwise nonzero minors at one coordinate alone cannot cap a
family below the field size. -/
theorem projectiveMinorModel_pairwise_minor_ne_zero
    {L : ℕ} (hLP : L ≤ P) {i j : Fin L} (hij : i ≠ j) :
    (projectiveMinorModel i).1 * (projectiveMinorModel j).2 -
      (projectiveMinorModel j).1 * (projectiveMinorModel i).2 ≠ 0 := by
  have hiP : i.val < P := i.isLt.trans_le hLP
  have hjP : j.val < P := j.isLt.trans_le hLP
  have hcast : (i.val : F) ≠ (j.val : F) := by
    intro heq
    apply hij
    apply Fin.ext
    exact CharP.natCast_injOn_Iio F P hiP hjP heq
  simp only [projectiveMinorModel, mul_one]
  intro hzero
  apply hcast
  linear_combination -hzero

/-- In particular, a `60,118,357`-vertex complete minor graph exists abstractly over the
literal prize field.  Cross-coordinate/degree compatibility is therefore essential. -/
theorem prizeField_supports_projectiveMinorClique_60118357 :
    ∀ i j : Fin 60118357, i ≠ j →
      (projectiveMinorModel i).1 * (projectiveMinorModel j).2 -
        (projectiveMinorModel j).1 * (projectiveMinorModel i).2 ≠ 0 := by
  intro i j hij
  apply projectiveMinorModel_pairwise_minor_ne_zero (L := 60118357) _ hij
  norm_num [P]

/-! ## Two-coordinate concentration arithmetic -/

/-- If `N` petals each have size at least the Johnson-light floor `55,924,056`, their total
unordered coordinate-pair incidence exceeds the capacity obtained by giving every coordinate
pair load at most `2,912,711`.  Hence the exact pigeonhole target is `2,912,712`. -/
theorem johnsonLight_twoCoordinate_concentration_arithmetic :
    N.choose 2 * 2912711 < N * ((55924056).choose 2) := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  norm_num [N]

/-- The corresponding sub-nine target is `3,366,002` common partners on a coordinate pair. -/
theorem subNine_twoCoordinate_concentration_arithmetic :
    N.choose 2 * 3366001 < N * ((60118357).choose 2) := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  norm_num [N]

/-- One below the Johnson-light pair-load target is exactly the last quotient-compatible
integer; this records sharpness of the pigeonhole rounding. -/
theorem johnsonLight_twoCoordinate_floor_pred_satisfiable :
    N * ((55924056).choose 2) ≤ N.choose 2 * 2912712 := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  norm_num [N]

/-- Symbolic transpose second-moment extraction.  Keeping the cardinal parameters abstract
prevents the elaborator from expanding production-scale numerals inside `Fin` types. -/
private theorem exists_two_coordinates_commonPetalLoad
    {r q load cap : ℕ} [Fintype ι]
    (V : ι → Finset (Fin r))
    (hcard : Fintype.card ι = r)
    (hq : 1 ≤ q)
    (hsize : ∀ j, q ≤ (V j).card)
    (hcap : cap = load - 1)
    (harith : r.choose 2 * cap < r * q.choose 2) :
    ∃ x y : Fin r, x < y ∧
      load ≤ (Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j).card := by
  classical
  let C : Fin r → Finset ι := fun x => Finset.univ.filter fun j => x ∈ V j
  let pairs : Finset (Fin r × Fin r) :=
    Finset.univ.filter fun p => p.1 < p.2
  by_contra hnone
  push Not at hnone
  have hinter : ∀ x y : Fin r, x < y →
      (C x ∩ C y).card ≤ cap := by
    intro x y hxy
    have hlt := hnone x y hxy
    have heq : C x ∩ C y = Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j := by
      ext j
      simp [C]
    rw [heq]
    rw [hcap]
    omega
  have hupp : (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) ≤
      r.choose 2 * cap := by
    calc
      (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) ≤ ∑ _p ∈ pairs, cap := by
        exact Finset.sum_le_sum fun (p : Fin r × Fin r) hp => hinter p.1 p.2 (by
          dsimp only [pairs] at hp
          exact (Finset.mem_filter.mp hp).2)
      _ = pairs.card * cap := by simp
      _ = r.choose 2 * cap := by
        have hoff := filter_lt_offDiag_card (Finset.univ : Finset (Fin r))
        have hpairs : pairs =
            (Finset.univ : Finset (Fin r)).offDiag.filter fun p => p.1 < p.2 := by
          ext p
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_offDiag]
          exact ⟨fun h => ⟨ne_of_lt h, h⟩,
            fun h => h.2⟩
        rw [hpairs, hoff, Finset.card_univ, Fintype.card_fin]
  have hU : Finset.univ.biUnion C = (Finset.univ : Finset ι) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    have hpos : (V j).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hq (hsize j))
    obtain ⟨x, hx⟩ := hpos
    rw [Finset.mem_biUnion]
    exact ⟨x, Finset.mem_univ _, by simp [C, hx]⟩
  have hid := sum_inter_eq_sum_choose_two r C
  change (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) = _ at hid
  rw [hU] at hid
  have hlow : r * q.choose 2 ≤ ∑ j : ι, (mult r C j).choose 2 := by
    calc
      r * q.choose 2 = ∑ _j : ι, q.choose 2 := by
        simp [hcard]
      _ ≤ ∑ j : ι, (mult r C j).choose 2 := by
        apply Finset.sum_le_sum
        intro j _hj
        apply Nat.choose_le_choose 2
        have heq : mult r C j = (V j).card := by
          unfold mult
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp [C]
        rw [heq]
        exact hsize j
  rw [← hid] at hlow
  exact (Nat.not_lt_of_ge (hlow.trans hupp)) harith

/-- **Transpose second-moment extraction.**  `N` petals of Johnson-light size force two
distinct coordinates jointly used by at least `2,912,712` petals. -/
theorem exists_two_coordinates_commonPetalLoad_ge_2912712
    [Fintype ι]
    (V : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hsize : ∀ j, 55924056 ≤ (V j).card) :
    ∃ x y : Fin N, x < y ∧
      2912712 ≤ (Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j).card := by
  apply exists_two_coordinates_commonPetalLoad
    (r := N) (q := 55924056) (load := 2912712) (cap := 2912711) V hcard
  · norm_num
  · exact hsize
  · norm_num
  · exact johnsonLight_twoCoordinate_concentration_arithmetic

/-- **Common-base two-coordinate minor certificate.**  In the exact Johnson-light branch,
two distinct coordinates are both missed by the base and both hit by at least `2,912,712`
partners.  Every distinct pair among those partners has a nonzero centered pencil minor at
each of the two coordinates. -/
theorem commonBase_johnsonLight_exists_twoCoordinateMinorClique_2912712
    [Fintype ι]
    (gamma0 : F) (gamma : ι → F)
    (p0 u0 u1 : Fin N → F) (p : ι → Fin N → F)
    (S : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hgamma0 : ∀ j, gamma0 ≠ gamma j)
    (hgamma : Function.Injective gamma)
    (hS : ∀ j, predecessorThreshold ≤ (S j).card)
    (hp : ∀ j, ∀ x ∈ S j, p j x = u0 x + gamma j * u1 x)
    (hA : ∀ j, (alignedSet u0 u1
      (pencilBase gamma0 (gamma j) p0 (p j))
      (pencilDir gamma0 (gamma j) p0 (p j))).card ≤ 536870910) :
    ∃ x y : Fin N, x < y ∧
      x ∈ baseMismatchSet gamma0 p0 u0 u1 ∧
      y ∈ baseMismatchSet gamma0 p0 u0 u1 ∧
      2912712 ≤ (Finset.univ.filter fun j : ι => x ∈ S j ∧ y ∈ S j).card ∧
      ∀ j ∈ (Finset.univ.filter fun j : ι => x ∈ S j ∧ y ∈ S j),
        ∀ j' ∈ (Finset.univ.filter fun j : ι => x ∈ S j ∧ y ∈ S j), j ≠ j' →
          ((pencilBase gamma0 (gamma j) p0 (p j) x - u0 x) *
              (pencilDir gamma0 (gamma j') p0 (p j') x - u1 x) -
            (pencilBase gamma0 (gamma j') p0 (p j') x - u0 x) *
              (pencilDir gamma0 (gamma j) p0 (p j) x - u1 x) ≠ 0) ∧
          ((pencilBase gamma0 (gamma j) p0 (p j) y - u0 y) *
              (pencilDir gamma0 (gamma j') p0 (p j') y - u1 y) -
            (pencilBase gamma0 (gamma j') p0 (p j') y - u0 y) *
              (pencilDir gamma0 (gamma j) p0 (p j) y - u1 y) ≠ 0) := by
  classical
  let V : ι → Finset (Fin N) := fun j => witnessVotePetal u0 u1
    (pencilBase gamma0 (gamma j) p0 (p j))
    (pencilDir gamma0 (gamma j) p0 (p j)) (S j)
  have hVsize : ∀ j, 55924056 ≤ (V j).card := by
    intro j
    exact johnsonLight_witnessVotePetal_card_floor u0 u1 _ _ (S j) (hS j) (hA j)
  obtain ⟨x, y, hxy, hload⟩ :=
    exists_two_coordinates_commonPetalLoad_ge_2912712 V hcard hVsize
  have hpetal : ∀ j, V j = S j ∩ baseMismatchSet gamma0 p0 u0 u1 := by
    intro j
    exact witnessVotePetal_commonBase_eq (hgamma0 j) p0 (p j) u0 u1 (S j) (hp j)
  have hnempty : (Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨j0, hj0⟩ := hnempty
  rw [Finset.mem_filter] at hj0
  have hxV := hj0.2.1
  have hyV := hj0.2.2
  rw [hpetal j0, Finset.mem_inter] at hxV hyV
  have hxmis := hxV.2
  have hymis := hyV.2
  have hsets : (Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j) =
      Finset.univ.filter fun j : ι => x ∈ S j ∧ y ∈ S j := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpetal j, Finset.mem_inter, Finset.mem_inter]
    simp only [hxmis, hymis, and_true]
  refine ⟨x, y, hxy, hxmis, hymis, ?_, ?_⟩
  · rw [← hsets]
    exact hload
  · intro j hj j' hj' hjj'
    rw [Finset.mem_filter] at hj hj'
    refine ⟨commonBase_centeredMinor_ne_zero (hgamma0 j) (hgamma0 j')
        (fun heq => hjj' (hgamma heq)) p0 (p j) (p j') u0 u1 x
        (hp j x hj.2.1) (hp j' x hj'.2.1)
        ((mem_baseMismatchSet_iff gamma0 p0 u0 u1 x).mp hxmis),
      commonBase_centeredMinor_ne_zero (hgamma0 j) (hgamma0 j')
        (fun heq => hjj' (hgamma heq)) p0 (p j) (p j') u0 u1 y
        (hp j y hj.2.2) (hp j' y hj'.2.2)
        ((mem_baseMismatchSet_iff gamma0 p0 u0 u1 y).mp hymis)⟩

/-! ## Equality rigidity of the near-threshold full-fiber obstruction -/

/-- At alignment `T-1`, a maximal rider family saturating the whole complement has exactly
one vote coordinate per rider. -/
theorem saturatedFullFiber_voteSet_card_eq_one
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    ∀ gamma ∈ R, (voteSet u0 u1 w0 w1 gamma).card = 1 := by
  intro gamma hgamma
  have hper : ∀ eta ∈ R, 1 ≤ (voteSet u0 u1 w0 w1 eta).card := by
    intro eta heta
    obtain ⟨hcard, hagree, hno⟩ := hrides eta heta
    have hTpos : 1 ≤ (Sf eta).card := by
      have hT := predecessorThreshold_eq
      omega
    exact Finset.card_pos.mpr
      (voteSet_nonempty_of_rides u0 u1 w0 w1 dom hw0 hw1 hagree hno hTpos)
  have hsum : (∑ eta ∈ R, (voteSet u0 u1 w0 w1 eta).card) ≤ R.card := by
    rw [← card_biUnion_votes u0 u1 w0 w1 R]
    have hbound := votes_biUnion_card_le u0 u1 w0 w1 R
    have hT := predecessorThreshold_eq
    have hN : N = 1073741824 := by norm_num [N]
    omega
  have hrest : (R.erase gamma).card ≤
      ∑ eta ∈ R.erase gamma, (voteSet u0 u1 w0 w1 eta).card := by
    calc
      (R.erase gamma).card = ∑ _eta ∈ R.erase gamma, 1 := by simp
      _ ≤ ∑ eta ∈ R.erase gamma, (voteSet u0 u1 w0 w1 eta).card := by
        exact Finset.sum_le_sum fun eta heta => hper eta (Finset.mem_of_mem_erase heta)
  have hsplit : (∑ eta ∈ R, (voteSet u0 u1 w0 w1 eta).card) =
      (∑ eta ∈ R.erase gamma, (voteSet u0 u1 w0 w1 eta).card) +
        (voteSet u0 u1 w0 w1 gamma).card := by
    exact (Finset.sum_erase_add _ _ hgamma).symm
  have herase : (R.erase gamma).card = R.card - 1 := by simp [hgamma]
  have hnonempty := hper gamma hgamma
  omega

/-- Therefore every threshold witness in the saturated full fiber is exactly the aligned
core plus its unique vote coordinate. -/
theorem saturatedFullFiber_witness_eq_aligned_union_vote
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    ∀ gamma ∈ R,
      Sf gamma = alignedSet u0 u1 w0 w1 ∪ voteSet u0 u1 w0 w1 gamma := by
  intro gamma hgamma
  obtain ⟨hScard, hagree, _hno⟩ := hrides gamma hgamma
  have hsub := witness_subset_aligned_union_votes u0 u1 w0 w1 hagree
  have hvote := saturatedFullFiber_voteSet_card_eq_one dom u0 u1 w0 w1 R Sf
    hw0 hw1 hrides hA hR gamma hgamma
  have hdisj : Disjoint (alignedSet u0 u1 w0 w1) (voteSet u0 u1 w0 w1 gamma) := by
    rw [Finset.disjoint_left]
    intro x hxA hxV
    exact (mem_voteSet_iff u0 u1 w0 w1 gamma x).mp hxV |>.1 hxA
  have hunion : (alignedSet u0 u1 w0 w1 ∪ voteSet u0 u1 w0 w1 gamma).card =
      predecessorThreshold := by
    rw [Finset.card_union_of_disjoint hdisj, hA, hvote]
    have hT := predecessorThreshold_eq
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hunion]
  exact hScard

/-- The singleton vote sets form an exact partition of the aligned core's complement. -/
theorem saturatedFullFiber_votes_partition_complement
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    R.biUnion (fun gamma => voteSet u0 u1 w0 w1 gamma) =
      Finset.univ \ alignedSet u0 u1 w0 w1 := by
  have hsub : R.biUnion (fun gamma => voteSet u0 u1 w0 w1 gamma) ⊆
      Finset.univ \ alignedSet u0 u1 w0 w1 := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨gamma, _hgamma, hxvote⟩ := hx
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, (mem_voteSet_iff u0 u1 w0 w1 gamma x).mp hxvote |>.1⟩
  apply Finset.eq_of_subset_of_card_le hsub
  calc
    (Finset.univ \ alignedSet u0 u1 w0 w1).card =
        N - (predecessorThreshold - 1) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hA]
    _ ≤ (R.biUnion (fun gamma => voteSet u0 u1 w0 w1 gamma)).card := by
      rw [card_biUnion_votes u0 u1 w0 w1 R]
      have hvote : ∀ gamma ∈ R, (voteSet u0 u1 w0 w1 gamma).card = 1 :=
        saturatedFullFiber_voteSet_card_eq_one dom u0 u1 w0 w1 R Sf
          hw0 hw1 hrides hA hR
      rw [Finset.sum_congr rfl hvote]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hR]
      norm_num [N, predecessorThreshold]

/-- Rational scalar label attached to a non-aligned coordinate of a pencil. -/
noncomputable def voteRatio
    (u0 u1 w0 w1 : Fin N → F) (x : Fin N) : F :=
  (u0 x - w0 x) / (w1 x - u1 x)

/-- A voting coordinate has nonzero direction denominator; otherwise its equality equation
would force full alignment. -/
theorem vote_denominator_ne_zero_of_mem
    (u0 u1 w0 w1 : Fin N → F) {gamma : F} {x : Fin N}
    (hx : x ∈ voteSet u0 u1 w0 w1 gamma) :
    w1 x - u1 x ≠ 0 := by
  rw [mem_voteSet_iff] at hx
  intro hzero
  have h1 : w1 x = u1 x := sub_eq_zero.mp hzero
  apply hx.1
  rw [mem_alignedSet_iff]
  refine ⟨?_, h1⟩
  rw [h1] at hx
  exact add_right_cancel hx.2

/-- The vote equation solves uniquely to the rational label. -/
theorem gamma_eq_voteRatio_of_mem
    (u0 u1 w0 w1 : Fin N → F) {gamma : F} {x : Fin N}
    (hx : x ∈ voteSet u0 u1 w0 w1 gamma) :
    gamma = voteRatio u0 u1 w0 w1 x := by
  have hden := vote_denominator_ne_zero_of_mem u0 u1 w0 w1 hx
  rw [mem_voteSet_iff] at hx
  rw [voteRatio, eq_div_iff hden]
  linear_combination hx.2

/-- Under full saturation, every complement coordinate has a unique rider whose vote it is. -/
theorem saturatedFullFiber_existsUnique_rider_at_complement
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    ∀ x ∈ Finset.univ \ alignedSet u0 u1 w0 w1,
      ∃! gamma, gamma ∈ R ∧ x ∈ voteSet u0 u1 w0 w1 gamma := by
  intro x hx
  have hpartition := saturatedFullFiber_votes_partition_complement
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR
  rw [← hpartition, Finset.mem_biUnion] at hx
  obtain ⟨gamma, hgamma, hxvote⟩ := hx
  refine ⟨gamma, ⟨hgamma, hxvote⟩, ?_⟩
  intro gamma' hgamma'
  by_contra hne
  have hd := Finset.disjoint_left.mp (voteSet_disjoint u0 u1 w0 w1 (Ne.symm hne))
  exact hd hxvote hgamma'.2

/-- Consequently the unique rider is exactly the coordinate's rational vote label. -/
theorem saturatedFullFiber_unique_rider_eq_voteRatio
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1)
    {x : Fin N} (hx : x ∈ Finset.univ \ alignedSet u0 u1 w0 w1) :
    Classical.choose (saturatedFullFiber_existsUnique_rider_at_complement
      dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR x hx) =
      voteRatio u0 u1 w0 w1 x := by
  let hex := saturatedFullFiber_existsUnique_rider_at_complement
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR x hx
  exact gamma_eq_voteRatio_of_mem u0 u1 w0 w1
    (Classical.choose_spec hex).1.2

/-- The rational vote labels map the aligned-core complement exactly onto the rider fiber. -/
theorem saturatedFullFiber_voteRatio_image_eq
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    (Finset.univ \ alignedSet u0 u1 w0 w1).image (voteRatio u0 u1 w0 w1) = R := by
  classical
  apply Finset.Subset.antisymm
  · intro gamma hgamma
    rw [Finset.mem_image] at hgamma
    obtain ⟨x, hx, rfl⟩ := hgamma
    let hex := saturatedFullFiber_existsUnique_rider_at_complement
      dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR x hx
    have hmem := (Classical.choose_spec hex).1.1
    have heq := saturatedFullFiber_unique_rider_eq_voteRatio
      dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR hx
    rwa [← heq]
  · intro gamma hgamma
    have hper : (voteSet u0 u1 w0 w1 gamma).Nonempty := by
      obtain ⟨_hcard, hagree, hno⟩ := hrides gamma hgamma
      have hTpos : 1 ≤ (Sf gamma).card := by
        have hT := predecessorThreshold_eq
        omega
      exact voteSet_nonempty_of_rides u0 u1 w0 w1 dom hw0 hw1 hagree hno hTpos
    obtain ⟨x, hxvote⟩ := hper
    have hxcomp : x ∈ Finset.univ \ alignedSet u0 u1 w0 w1 := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, (mem_voteSet_iff u0 u1 w0 w1 gamma x).mp hxvote |>.1⟩
    rw [Finset.mem_image]
    exact ⟨x, hxcomp, (gamma_eq_voteRatio_of_mem u0 u1 w0 w1 hxvote).symm⟩

/-- The rational vote map is injective on the aligned-core complement. -/
theorem saturatedFullFiber_voteRatio_injOn
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hw0 : w0 ∈ predecessorCode dom) (hw1 : w1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    (hA : (alignedSet u0 u1 w0 w1).card = predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1) :
    Set.InjOn (voteRatio u0 u1 w0 w1)
      (↑(Finset.univ \ alignedSet u0 u1 w0 w1) : Set (Fin N)) := by
  intro x hx y hy heq
  have hx' : x ∈ Finset.univ \ alignedSet u0 u1 w0 w1 := hx
  have hy' : y ∈ Finset.univ \ alignedSet u0 u1 w0 w1 := hy
  let ex := saturatedFullFiber_existsUnique_rider_at_complement
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR x hx'
  let ey := saturatedFullFiber_existsUnique_rider_at_complement
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR y hy'
  have hxvote := (Classical.choose_spec ex).1.2
  have hyvoteraw := (Classical.choose_spec ey).1.2
  have hex := saturatedFullFiber_unique_rider_eq_voteRatio
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR hx'
  have hey := saturatedFullFiber_unique_rider_eq_voteRatio
    dom u0 u1 w0 w1 R Sf hw0 hw1 hrides hA hR hy'
  have hlabel : Classical.choose ex = Classical.choose ey := by
    rw [hex, hey]
    exact heq
  rw [hlabel] at hxvote
  have hcard := saturatedFullFiber_voteSet_card_eq_one dom u0 u1 w0 w1 R Sf
    hw0 hw1 hrides hA hR (Classical.choose ey) (Classical.choose_spec ey).1.1
  exact Finset.card_le_one.mp hcard.le _ hxvote _ hyvoteraw

/-- A vote on a pencil through `(gamma0,p0)` obeys a common-numerator equation. -/
theorem commonBase_vote_equation
    {gamma0 gamma1 gamma : F}
    (p0 p1 u0 u1 : Fin N → F) {x : Fin N}
    (hx : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) :
    (gamma - gamma0) *
        (pencilDir gamma0 gamma1 p0 p1 x - u1 x) =
      u0 x + gamma0 * u1 x - p0 x := by
  have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
  have hvote := (mem_voteSet_iff u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma x).mp hx |>.2
  linear_combination hvote - hrepro

/-- Closed form of the rational vote label on a common-base pencil. -/
theorem commonBase_voteRatio_eq
    {gamma0 gamma1 : F}
    (p0 p1 u0 u1 : Fin N → F) {x : Fin N}
    (hden : pencilDir gamma0 gamma1 p0 p1 x - u1 x ≠ 0) :
    voteRatio u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) x =
      gamma0 + (u0 x + gamma0 * u1 x - p0 x) /
        (pencilDir gamma0 gamma1 p0 p1 x - u1 x) := by
  have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
  rw [voteRatio]
  field_simp
  linear_combination -hrepro

/-- Combining the two statements recovers the rider from the common-base mismatch quotient. -/
theorem commonBase_gamma_eq_mismatchQuotient_of_vote
    {gamma0 gamma1 gamma : F}
    (p0 p1 u0 u1 : Fin N → F) {x : Fin N}
    (hx : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) :
    gamma = gamma0 + (u0 x + gamma0 * u1 x - p0 x) /
      (pencilDir gamma0 gamma1 p0 p1 x - u1 x) := by
  rw [gamma_eq_voteRatio_of_mem u0 u1 _ _ hx,
    commonBase_voteRatio_eq p0 p1 u0 u1
      (vote_denominator_ne_zero_of_mem u0 u1 _ _ hx)]

/-- A common non-base rider voting on two common-base pencils forces their directions to
agree at that coordinate. -/
theorem same_nonbase_vote_forces_commonBase_directions_agree
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F) {x : Fin N}
    (hx1 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma)
    (hx2 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma) :
    pencilDir gamma0 gamma1 p0 p1 x = pencilDir gamma0 gamma2 p0 p2 x := by
  have h1 := commonBase_vote_equation p0 p1 u0 u1 hx1
  have h2 := commonBase_vote_equation p0 p2 u0 u1 hx2
  have hmul : (gamma - gamma0) *
      (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact absurd (sub_eq_zero.mp hzero) hgamma
  · exact sub_eq_zero.mp hzero

/-- **Degree-sensitive cross-pencil collision cap.**  For two common-base pencils with
distinct direction codewords, the same non-base scalar can vote on both at at most `k-1`
coordinates. -/
theorem commonBase_sameRider_crossVote_card_le_k_sub_one
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hdir : pencilDir gamma0 gamma1 p0 p1 ≠ pencilDir gamma0 gamma2 p0 p2) :
    (voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
      voteSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma).card ≤
      k - 1 := by
  by_contra hcard
  have hk : k ≤ (voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
      voteSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma).card := by
    omega
  apply hdir
  apply predecessor_sep dom
  · exact pencilDir_mem _ hp0 hp1
  · exact pencilDir_mem _ hp0 hp2
  · exact hk
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact same_nonbase_vote_forces_commonBase_directions_agree hgamma
      p0 p1 p2 u0 u1 hx1 hx2

/-- **Two-label coupling.**  For two distinct common-base pencil directions, the combined
matching overlap for any two non-base rider labels is at most `k-1`.  Both matching pieces
force direction agreement, so they share one RS root budget rather than receiving separate
`k-1` allowances. -/
theorem commonBase_twoRider_matchingOverlap_card_le_k_sub_one
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma delta : F}
    (hgamma : gamma ≠ gamma0) (hdelta : delta ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hdir : pencilDir gamma0 gamma1 p0 p1 ≠ pencilDir gamma0 gamma2 p0 p2) :
    ((voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma) ∪
      (voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) delta ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) delta)).card ≤
      k - 1 := by
  by_contra hcard
  have hk : k ≤ ((voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma) ∪
      (voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) delta ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) delta)).card := by
    omega
  apply hdir
  apply predecessor_sep dom
  · exact pencilDir_mem _ hp0 hp1
  · exact pencilDir_mem _ hp0 hp2
  · exact hk
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      exact same_nonbase_vote_forces_commonBase_directions_agree hgamma
        p0 p1 p2 u0 u1 hx1 hx2
    · obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      exact same_nonbase_vote_forces_commonBase_directions_agree hdelta
        p0 p1 p2 u0 u1 hx1 hx2

/-- **Aligned-plus-rider coupling.**  For two distinct common-base directions, the overlap of
their aligned cores and the overlap of one common non-base rider's vote sets share a single
`k-1` RS root budget. -/
theorem commonBase_alignedAndSameRider_matching_card_le_k_sub_one
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hdir : pencilDir gamma0 gamma1 p0 p1 ≠ pencilDir gamma0 gamma2 p0 p2) :
    ((alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∩
      alignedSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)) ∪
      (voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma)).card ≤
      k - 1 := by
  by_contra hcard
  have hk : k ≤ ((alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∩
      alignedSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)) ∪
      (voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∩
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma)).card := by
    omega
  apply hdir
  apply predecessor_sep dom
  · exact pencilDir_mem _ hp0 hp1
  · exact pencilDir_mem _ hp0 hp2
  · exact hk
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have h1 := (mem_alignedSet_iff u0 u1 _ _ x).mp hx1 |>.2
      have h2 := (mem_alignedSet_iff u0 u1 _ _ x).mp hx2 |>.2
      exact h1.trans h2.symm
    · obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      exact same_nonbase_vote_forces_commonBase_directions_agree hgamma
        p0 p1 p2 u0 u1 hx1 hx2

/-- On a cross-label coordinate, the difference of two common-base directions is a fixed
multiple of the common base mismatch.  This is the oriented quotient identity that the binary
matching abstraction forgets. -/
theorem commonBase_crossVote_directionDiff_identity
    {gamma0 gamma1 gamma2 gamma delta : F}
    (p0 p1 p2 u0 u1 : Fin N → F) {x : Fin N}
    (hx1 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma)
    (hx2 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) delta) :
    (gamma - gamma0) * (delta - gamma0) *
        (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x) =
      (delta - gamma) * (u0 x + gamma0 * u1 x - p0 x) := by
  have h1 := commonBase_vote_equation p0 p1 u0 u1 hx1
  have h2 := commonBase_vote_equation p0 p2 u0 u1 hx2
  linear_combination (delta - gamma0) * h1 - (gamma - gamma0) * h2

/-- Reversing the two labels reverses the sign of the mismatch multiple. -/
theorem commonBase_reverseCrossVote_directionDiff_identity
    {gamma0 gamma1 gamma2 gamma delta : F}
    (p0 p1 p2 u0 u1 : Fin N → F) {x : Fin N}
    (hx1 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) delta)
    (hx2 : x ∈ voteSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma) :
    (gamma - gamma0) * (delta - gamma0) *
        (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x) =
      (gamma - delta) * (u0 x + gamma0 * u1 x - p0 x) := by
  have h1 := commonBase_vote_equation p0 p1 u0 u1 hx1
  have h2 := commonBase_vote_equation p0 p2 u0 u1 hx2
  linear_combination (gamma - gamma0) * h1 - (delta - gamma0) * h2

/-- **Orientation-free mismatch-square law.**  On either cross-label orientation, the squared
direction difference is tied to the square of the same common mismatch word. -/
theorem commonBase_crossVote_directionDiff_square_identity
    {gamma0 gamma1 gamma2 gamma delta : F}
    (p0 p1 p2 u0 u1 : Fin N → F) {x : Fin N}
    (hx :
      (x ∈ voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ∧
        x ∈ voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) delta) ∨
      (x ∈ voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) delta ∧
        x ∈ voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma)) :
    ((gamma - gamma0) * (delta - gamma0)) ^ 2 *
        (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x) ^ 2 =
      (delta - gamma) ^ 2 * (u0 x + gamma0 * u1 x - p0 x) ^ 2 := by
  rcases hx with hx | hx
  · have h := commonBase_crossVote_directionDiff_identity
      p0 p1 p2 u0 u1 hx.1 hx.2
    calc
      _ = ((gamma - gamma0) * (delta - gamma0) *
          (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x)) ^ 2 := by ring
      _ = ((delta - gamma) * (u0 x + gamma0 * u1 x - p0 x)) ^ 2 := by rw [h]
      _ = _ := by ring
  · have h := commonBase_reverseCrossVote_directionDiff_identity
      p0 p1 p2 u0 u1 hx.1 hx.2
    calc
      _ = ((gamma - gamma0) * (delta - gamma0) *
          (pencilDir gamma0 gamma1 p0 p1 x - pencilDir gamma0 gamma2 p0 p2 x)) ^ 2 := by ring
      _ = ((gamma - delta) * (u0 x + gamma0 * u1 x - p0 x)) ^ 2 := by rw [h]
      _ = _ := by ring

/-- A non-base rider can vote only outside the fixed base codeword's agreement carrier. -/
theorem commonBase_nonbase_vote_subset_baseAgree_compl
    {gamma0 gamma1 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 u0 u1 : Fin N → F) :
    voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma ⊆
      Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x) := by
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hxB
  rw [agreeSet, Finset.mem_filter] at hxB
  have heq := commonBase_vote_equation p0 p1 u0 u1 hx
  have hmul : (gamma - gamma0) *
      (pencilDir gamma0 gamma1 p0 p1 x - u1 x) = 0 :=
    heq.trans (sub_eq_zero.mpr hxB.2.symm)
  have hdir : pencilDir gamma0 gamma1 p0 p1 x = u1 x := by
    rcases mul_eq_zero.mp hmul with hg | hd
    · exact absurd (sub_eq_zero.mp hg) hgamma
    · exact sub_eq_zero.mp hd
  exact (mem_voteSet_iff u0 u1 _ _ gamma x).mp hx |>.1
    ((mem_alignedSet_iff u0 u1 _ _ x).mpr ⟨by
      have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
      rw [hdir] at hrepro
      exact add_right_cancel (hrepro.trans hxB.2), hdir⟩)

/-- **Shared-rider uniqueness from complement packing.**  Two common-base pencils cannot carry
the same non-base rider with two vote sets of size at least `s` once inclusion--exclusion inside
the base-carrier complement forces `k` shared coordinates. -/
theorem commonBase_sharedRider_directions_eq_of_complement_packing
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (s : ℕ)
    (hV1 : s ≤ (voteSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma).card)
    (hV2 : s ≤ (voteSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma).card)
    (hpack : (Finset.univ \
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card + k ≤ 2 * s) :
    pencilDir gamma0 gamma1 p0 p1 = pencilDir gamma0 gamma2 p0 p2 := by
  let V1 := voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let V2 := voteSet u0 u1
    (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma
  let C := Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hV1C : V1 ⊆ C :=
    commonBase_nonbase_vote_subset_baseAgree_compl hgamma p0 p1 u0 u1
  have hV2C : V2 ⊆ C :=
    commonBase_nonbase_vote_subset_baseAgree_compl hgamma p0 p2 u0 u1
  have hunion : (V1 ∪ V2).card ≤ C.card :=
    Finset.card_le_card (Finset.union_subset hV1C hV2C)
  have hsum := Finset.card_union_add_card_inter V1 V2
  have hinter : k ≤ (V1 ∩ V2).card := by
    dsimp [V1, V2, C] at hV1 hV2 hpack hunion hsum ⊢
    omega
  apply predecessor_sep dom
  · exact pencilDir_mem _ hp0 hp1
  · exact pencilDir_mem _ hp0 hp2
  · exact hinter
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact same_nonbase_vote_forces_commonBase_directions_agree hgamma
      p0 p1 p2 u0 u1 hx1 hx2

/-- The fixed base scalar's agreement set decomposes exactly into a pencil's aligned core and
the base scalar's vote set. -/
theorem commonBase_agreeSet_eq_aligned_union_baseVote
    (gamma0 gamma1 : F) (p0 p1 u0 u1 : Fin N → F) :
    agreeSet p0 (fun x => u0 x + gamma0 * u1 x) =
      alignedSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∪
        voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma0 := by
  ext x
  rw [agreeSet, Finset.mem_filter]
  simp only [Finset.mem_union, Finset.mem_univ, true_and]
  constructor
  · intro hxagree
    by_cases hal : x ∈ alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
    · exact Or.inl hal
    · right
      rw [mem_voteSet_iff]
      have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
      exact ⟨hal, hrepro.trans hxagree⟩
  · intro hx
    rcases hx with hal | hvote
    · rw [mem_alignedSet_iff] at hal
      have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
      rw [hal.1, hal.2] at hrepro
      exact hrepro.symm
    · rw [mem_voteSet_iff] at hvote
      have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
      exact hrepro.symm.trans hvote.2

/-- **Aligned-core/list-decoding identity.**  For a pencil through the fixed base
`(gamma0,p0)`, alignment is exactly simultaneous membership in the base agreement carrier
and agreement of the direction codeword with the received direction `u1`. -/
theorem commonBase_alignedSet_eq_baseAgree_inter_directionAgree
    (gamma0 gamma1 : F) (p0 p1 u0 u1 : Fin N → F) :
    alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) =
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x) ∩
        agreeSet (pencilDir gamma0 gamma1 p0 p1) u1 := by
  ext x
  rw [mem_alignedSet_iff, Finset.mem_inter, agreeSet, agreeSet,
    Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hal
    have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
    rw [hal.1, hal.2] at hrepro
    exact ⟨hrepro.symm, hal.2⟩
  · rintro ⟨hbase, hdir⟩
    refine ⟨?_, hdir⟩
    have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
    rw [hdir] at hrepro
    exact add_right_cancel (hrepro.trans hbase)

/-- The intersection of two fixed scalar witnesses forces their divided-difference direction to
agree with the received direction `u1`.  This is the global cross-fiber bridge used by moment
arguments across different base pencils. -/
theorem fixedWitness_inter_subset_pencilDir_agreeSet
    {gamma delta : F} (hne : gamma ≠ delta)
    (pGamma pDelta u0 u1 : Fin N → F)
    (Sgamma Sdelta : Finset (Fin N))
    (hgamma : ∀ x ∈ Sgamma, pGamma x = u0 x + gamma * u1 x)
    (hdelta : ∀ x ∈ Sdelta, pDelta x = u0 x + delta * u1 x) :
    Sgamma ∩ Sdelta ⊆ agreeSet (pencilDir gamma delta pGamma pDelta) u1 := by
  intro x hx
  obtain ⟨hxg, hxd⟩ := Finset.mem_inter.mp hx
  rw [agreeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hg := hgamma x hxg
  have hd := hdelta x hxd
  simp only [pencilDir, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hsub : delta - gamma ≠ 0 := sub_ne_zero.mpr hne.symm
  field_simp
  linear_combination hd - hg

/-- Any two threshold witnesses overlap on at least `2T-N = 111848108` coordinates, all of
which are direction-agreement coordinates by the preceding bridge. -/
theorem fixedWitness_pencilDir_agreeSet_card_ge_111848108
    {gamma delta : F} (hne : gamma ≠ delta)
    (pGamma pDelta u0 u1 : Fin N → F)
    (Sgamma Sdelta : Finset (Fin N))
    (hSgamma : predecessorThreshold ≤ Sgamma.card)
    (hSdelta : predecessorThreshold ≤ Sdelta.card)
    (hgamma : ∀ x ∈ Sgamma, pGamma x = u0 x + gamma * u1 x)
    (hdelta : ∀ x ∈ Sdelta, pDelta x = u0 x + delta * u1 x) :
    111848108 ≤ (agreeSet (pencilDir gamma delta pGamma pDelta) u1).card := by
  have hsub := fixedWitness_inter_subset_pencilDir_agreeSet hne
    pGamma pDelta u0 u1 Sgamma Sdelta hgamma hdelta
  have hcard := Finset.card_le_card hsub
  have hunion : (Sgamma ∪ Sdelta).card ≤ N := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (Sgamma ∪ Sdelta)
  have hinc := Finset.card_union_add_card_inter Sgamma Sdelta
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **Five-witness secant extraction.**  Among any five distinct fixed scalars with threshold
witnesses, some divided-difference direction agrees with `u1` on at least `k` coordinates.  This
composes the integral five-set overlap theorem with the fixed-witness direction bridge. -/
theorem fiveFixedWitnesses_exists_pencilDir_agreeSet_card_ge_k
    (gamma : Fin 5 → F) (hgammaInj : Function.Injective gamma)
    (p : Fin 5 → Fin N → F) (S : Fin 5 → Finset (Fin N))
    (u0 u1 : Fin N → F)
    (hsize : ∀ i, predecessorThreshold ≤ (S i).card)
    (hagree : ∀ i, ∀ x ∈ S i, p i x = u0 x + gamma i * u1 x) :
    ∃ i j : Fin 5, i ≠ j ∧
      k ≤ (agreeSet (pencilDir (gamma i) (gamma j) (p i) (p j)) u1).card := by
  have hex :=
    P1RateQuarterAgreementOverlapGraph.exists_pair_inter_card_ge_K_of_five S (fun i => by
      simpa [P1RateQuarterAgreementOverlapGraph.T, predecessorThreshold_eq] using hsize i)
  obtain ⟨i, j, hij, hinter⟩ := hex
  refine ⟨i, j, hij, ?_⟩
  have hsub := fixedWitness_inter_subset_pencilDir_agreeSet
    (hgammaInj.ne hij) (p i) (p j) u0 u1 (S i) (S j) (hagree i) (hagree j)
  have hcard := Finset.card_le_card hsub
  simpa [P1RateQuarterAgreementOverlapGraph.K, k] using hinter.trans hcard

/-- Finite-family interface to the five-witness secant extraction. -/
theorem exists_pinnedSecant_of_five_le_card
    (G : Finset F) (p : F → Fin N → F) (S : F → Finset (Fin N))
    (u0 u1 : Fin N → F)
    (hG : 5 ≤ G.card)
    (hsize : ∀ gamma ∈ G, predecessorThreshold ≤ (S gamma).card)
    (hagree : ∀ gamma ∈ G, ∀ x ∈ S gamma,
      p gamma x = u0 x + gamma * u1 x) :
    ∃ gamma ∈ G, ∃ delta ∈ G, gamma ≠ delta ∧
      k ≤ (agreeSet (pencilDir gamma delta (p gamma) (p delta)) u1).card := by
  classical
  obtain ⟨G5, hG5sub, hG5card⟩ := Finset.exists_subset_card_eq hG
  have he : G5 ≃ Fin 5 := by
    rw [← hG5card]
    exact G5.equivFin
  let gamma : Fin 5 → F := fun i => (he.symm i : F)
  have hgammaInj : Function.Injective gamma := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hmem : ∀ i, gamma i ∈ G := fun i => hG5sub (he.symm i).2
  obtain ⟨i, j, hij, hpinned⟩ :=
    fiveFixedWitnesses_exists_pencilDir_agreeSet_card_ge_k gamma hgammaInj
      (fun i => p (gamma i)) (fun i => S (gamma i)) u0 u1
      (fun i => hsize _ (hmem i)) (fun i => hagree _ (hmem i))
  exact ⟨gamma i, hmem i, gamma j, hmem j, hgammaInj.ne hij, hpinned⟩

/-- **Full combined-set overlap cap.**  For a fixed non-base rider, each pencil's aligned core
lies in `B` and its vote set lies in `Bᶜ`; hence cross terms vanish.  The intersection of the
full combined sets `aligned ∪ vote` is exactly matching-type overlap and has size at most `k-1`
for distinct directions. -/
theorem commonBase_alignedUnionSameRider_inter_card_le_k_sub_one
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hdir : pencilDir gamma0 gamma1 p0 p1 ≠ pencilDir gamma0 gamma2 p0 p2) :
    ((alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∪
      voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) ∩
      (alignedSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) ∪
      voteSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma)).card ≤
      k - 1 := by
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hA1B : alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ⊆ B := by
    rw [commonBase_alignedSet_eq_baseAgree_inter_directionAgree]
    exact Finset.inter_subset_left
  have hA2B : alignedSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) ⊆ B := by
    rw [commonBase_alignedSet_eq_baseAgree_inter_directionAgree]
    exact Finset.inter_subset_left
  have hV1C := commonBase_nonbase_vote_subset_baseAgree_compl (gamma1 := gamma1)
    hgamma p0 p1 u0 u1
  have hV2C := commonBase_nonbase_vote_subset_baseAgree_compl (gamma1 := gamma2)
    hgamma p0 p2 u0 u1
  by_contra hcard
  have hk : k ≤ ((alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∪
      voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) ∩
      (alignedSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) ∪
      voteSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma)).card := by
    omega
  apply hdir
  apply predecessor_sep dom
  · exact pencilDir_mem _ hp0 hp1
  · exact pencilDir_mem _ hp0 hp2
  · exact hk
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hx1 with hxA1 | hxV1 <;>
      rcases Finset.mem_union.mp hx2 with hxA2 | hxV2
    · have h1 := (mem_alignedSet_iff u0 u1 _ _ x).mp hxA1 |>.2
      have h2 := (mem_alignedSet_iff u0 u1 _ _ x).mp hxA2 |>.2
      exact h1.trans h2.symm
    · exact False.elim ((Finset.mem_sdiff.mp (hV2C hxV2)).2 (hA1B hxA1))
    · exact False.elim ((Finset.mem_sdiff.mp (hV1C hxV1)).2 (hA2B hxA2))
    · exact same_nonbase_vote_forces_commonBase_directions_agree hgamma
        p0 p1 p2 u0 u1 hxV1 hxV2

/-- **Fixed-witness charged-rider uniqueness.**  In the actual pencil-count construction the
witness `Sf gamma` is fixed globally.  If two common-base pencils carry the same non-base rider
on that witness, the witness lies in both combined `aligned ∪ vote` sets and has size at least
`T > k-1`; the full combined-overlap cap therefore forces the directions to coincide. -/
theorem commonBase_sameFixedWitnessRider_directions_eq
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 R2 : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf)
    (hgamma1 : gamma ∈ R1) (hgamma2 : gamma ∈ R2) :
    pencilDir gamma0 gamma1 p0 p1 = pencilDir gamma0 gamma2 p0 p2 := by
  by_contra hdir
  have hcap := commonBase_alignedUnionSameRider_inter_card_le_k_sub_one
    dom hgamma p0 p1 p2 u0 u1 hp0 hp1 hp2 hdir
  obtain ⟨hScard, hagree1, _hno1⟩ := hrides1 gamma hgamma1
  obtain ⟨_hScard2, hagree2, _hno2⟩ := hrides2 gamma hgamma2
  have hsub1 := witness_subset_aligned_union_votes u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) hagree1
  have hsub2 := witness_subset_aligned_union_votes u0 u1
    (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) hagree2
  have hinter : Sf gamma ⊆
      (alignedSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∪
        voteSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) ∩
      (alignedSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) ∪
        voteSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) gamma) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hsub1 hx, hsub2 hx⟩
  have hlower := Finset.card_le_card hinter
  have hT := predecessorThreshold_eq
  have hk : k = 268435456 := by norm_num [k]
  omega

/-- Through a fixed base point `(gamma0,p0)`, equality of directions forces equality of pencil
bases. -/
theorem commonBase_pencilBase_eq_of_direction_eq
    {gamma0 gamma1 gamma2 : F} (p0 p1 p2 : Fin N → F)
    (hdir : pencilDir gamma0 gamma1 p0 p1 = pencilDir gamma0 gamma2 p0 p2) :
    pencilBase gamma0 gamma1 p0 p1 = pencilBase gamma0 gamma2 p0 p2 := by
  simp only [pencilBase]
  rw [hdir]

/-- **Complete fixed-witness pencil uniqueness.**  A shared non-base rider on its globally fixed
threshold witness determines the entire common-base pencil pair `(base,direction)`. -/
theorem commonBase_sameFixedWitnessRider_pencils_eq
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 gamma : F} (hgamma : gamma ≠ gamma0)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 R2 : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf)
    (hgamma1 : gamma ∈ R1) (hgamma2 : gamma ∈ R2) :
    (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) =
      (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2) := by
  have hdir := commonBase_sameFixedWitnessRider_directions_eq dom hgamma
    p0 p1 p2 u0 u1 R1 R2 Sf hp0 hp1 hp2 hrides1 hrides2 hgamma1 hgamma2
  exact Prod.ext (commonBase_pencilBase_eq_of_direction_eq p0 p1 p2 hdir) hdir

/-- **Distinct-pencil erased fibers are disjoint.**  Under global fixed witnesses, two distinct
common-base pencils cannot share any non-base rider.  This is the family-level form consumed by
layer-budget sums. -/
theorem commonBase_distinctPencils_nonbaseRiders_disjoint
    (dom : Fin N ↪ F)
    {gamma0 gamma1 gamma2 : F}
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 R2 : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom)
    (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf)
    (hpencils :
      (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) ≠
        (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2)) :
    Disjoint (R1.erase gamma0) (R2.erase gamma0) := by
  rw [Finset.disjoint_left]
  intro gamma hgamma1 hgamma2
  have hne : gamma ≠ gamma0 := (Finset.mem_erase.mp hgamma1).1
  apply hpencils
  exact commonBase_sameFixedWitnessRider_pencils_eq dom hne
    p0 p1 p2 u0 u1 R1 R2 Sf hp0 hp1 hp2 hrides1 hrides2
    (Finset.mem_of_mem_erase hgamma1) (Finset.mem_of_mem_erase hgamma2)

/-- A saturated full fiber containing the base scalar forces the base codeword's agreement
set to have exactly threshold size. -/
theorem saturatedFullFiber_commonBase_agreeSet_card_eq_threshold
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        predecessorThreshold - 1)
    (hR : R.card = N - predecessorThreshold + 1)
    (hgamma0 : gamma0 ∈ R) :
    (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card = predecessorThreshold := by
  rw [commonBase_agreeSet_eq_aligned_union_baseVote]
  have hvote := saturatedFullFiber_voteSet_card_eq_one dom u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf
    (pencilBase_mem _ hp0 hp1) (pencilDir_mem _ hp0 hp1) hrides hA hR gamma0 hgamma0
  have hdisj : Disjoint
      (alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1))
      (voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma0) := by
    rw [Finset.disjoint_left]
    intro x hxA hxV
    exact (mem_voteSet_iff u0 u1 _ _ gamma0 x).mp hxV |>.1 hxA
  rw [Finset.card_union_of_disjoint hdisj, hA, hvote]
  have hT := predecessorThreshold_eq
  omega

/-- Two saturated full-fiber cores through the same base overlap on at least `T-2`
coordinates: each is the fixed base agreement set with only its singleton base vote removed. -/
theorem two_saturatedFullFiber_commonBase_aligned_inter_card_ge_threshold_sub_two
    (dom : Fin N ↪ F) (gamma0 gamma1 gamma2 : F)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 R2 : Finset F) (Sf1 Sf2 : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf1)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf2)
    (hA1 : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        predecessorThreshold - 1)
    (hA2 : (alignedSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card =
        predecessorThreshold - 1)
    (hR1 : R1.card = N - predecessorThreshold + 1)
    (hR2 : R2.card = N - predecessorThreshold + 1)
    (hgamma01 : gamma0 ∈ R1) (hgamma02 : gamma0 ∈ R2) :
    predecessorThreshold - 2 ≤
      (alignedSet u0 u1
          (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) ∩
        alignedSet u0 u1
          (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card := by
  let A1 := alignedSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
  let A2 := alignedSet u0 u1
    (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hB : B.card = predecessorThreshold :=
    saturatedFullFiber_commonBase_agreeSet_card_eq_threshold dom gamma0 gamma1
      p0 p1 u0 u1 R1 Sf1 hp0 hp1 hrides1 hA1 hR1 hgamma01
  have hA1sub : A1 ⊆ B := by
    dsimp only [A1, B]
    rw [commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hA2sub : A2 ⊆ B := by
    dsimp only [A2, B]
    rw [commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hunion : (A1 ∪ A2).card ≤ predecessorThreshold := by
    rw [← hB]
    exact Finset.card_le_card (Finset.union_subset hA1sub hA2sub)
  have hbook := Finset.card_union_add_card_inter A1 A2
  change predecessorThreshold - 2 ≤ (A1 ∩ A2).card
  change A1.card = predecessorThreshold - 1 at hA1
  change A2.card = predecessorThreshold - 1 at hA2
  omega

/-- **Saturated-heavy uniqueness through a base.**  Two full fibers at alignment `T-1`
through the same base codeword must be the same pencil. -/
theorem two_saturatedFullFiber_commonBase_pencils_eq
    (dom : Fin N ↪ F) (gamma0 gamma1 gamma2 : F)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 R2 : Finset F) (Sf1 Sf2 : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf1)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf2)
    (hA1 : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        predecessorThreshold - 1)
    (hA2 : (alignedSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card =
        predecessorThreshold - 1)
    (hR1 : R1.card = N - predecessorThreshold + 1)
    (hR2 : R2.card = N - predecessorThreshold + 1)
    (hgamma01 : gamma0 ∈ R1) (hgamma02 : gamma0 ∈ R2) :
    (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) =
      (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2) := by
  by_contra hne
  have hinter := alignedSet_inter_card_lt_k dom u0 u1
    (pencilBase_mem _ hp0 hp1) (pencilDir_mem _ hp0 hp1)
    (pencilBase_mem _ hp0 hp2) (pencilDir_mem _ hp0 hp2) hne
  have hlower := two_saturatedFullFiber_commonBase_aligned_inter_card_ge_threshold_sub_two
    dom gamma0 gamma1 gamma2 p0 p1 p2 u0 u1 R1 R2 Sf1 Sf2 hp0 hp1 hp2
    hrides1 hrides2 hA1 hA2 hR1 hR2 hgamma01 hgamma02
  have hT := predecessorThreshold_eq
  have hk : k = 268435456 := by norm_num [k]
  omega

/-- **Shared-base rider cap.**  For any pencil through the base, the base scalar's vote set
is the part of the fixed base agreement set outside the aligned core.  Disjoint nonempty votes
then give `riders ≤ N - |baseAgreement| + 1`, independently of the pencil alignment. -/
theorem commonBase_riders_card_le_compl_agreeSet_add_one
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hgamma0 : gamma0 ∈ R) :
    R.card ≤ N - (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card + 1 := by
  let A := alignedSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
  let V := fun gamma => voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hB : B = A ∪ V gamma0 := commonBase_agreeSet_eq_aligned_union_baseVote _ _ _ _ _ _
  have hdisj : Disjoint A (V gamma0) := by
    rw [Finset.disjoint_left]
    intro x hxA hxV
    exact (mem_voteSet_iff u0 u1 _ _ gamma0 x).mp hxV |>.1 hxA
  have hBcard : B.card = A.card + (V gamma0).card := by
    rw [hB, Finset.card_union_of_disjoint hdisj]
  have hper : ∀ gamma ∈ R, 1 ≤ (V gamma).card := by
    intro gamma hgamma
    obtain ⟨hcard, hagree, hno⟩ := hrides gamma hgamma
    have hpos : 1 ≤ (Sf gamma).card := by
      have hT := predecessorThreshold_eq
      omega
    exact Finset.card_pos.mpr (voteSet_nonempty_of_rides u0 u1 _ _ dom
      (pencilBase_mem _ hp0 hp1) (pencilDir_mem _ hp0 hp1) hagree hno hpos)
  have hrest : (R.erase gamma0).card ≤ ∑ gamma ∈ R.erase gamma0, (V gamma).card := by
    calc
      (R.erase gamma0).card = ∑ _gamma ∈ R.erase gamma0, 1 := by simp
      _ ≤ ∑ gamma ∈ R.erase gamma0, (V gamma).card := by
        exact Finset.sum_le_sum fun gamma hgamma => hper gamma (Finset.mem_of_mem_erase hgamma)
  have hsplit : (∑ gamma ∈ R, (V gamma).card) =
      (∑ gamma ∈ R.erase gamma0, (V gamma).card) + (V gamma0).card := by
    exact (Finset.sum_erase_add _ _ hgamma0).symm
  have hsum : (∑ gamma ∈ R, (V gamma).card) ≤ N - A.card := by
    rw [← card_biUnion_votes u0 u1 _ _ R]
    exact votes_biUnion_card_le u0 u1 _ _ R
  have herase : (R.erase gamma0).card = R.card - 1 := by simp [hgamma0]
  have hAN : A.card ≤ N := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ A
  have hBN : B.card ≤ N := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨gamma0, hgamma0⟩
  rw [hBcard]
  omega

/-- Every threshold rider witness forces at least `T-|A|` coordinates in its private vote set. -/
theorem rides_voteSet_card_ge_threshold_sub_aligned
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    {gamma : F} (hgamma : gamma ∈ R) :
    predecessorThreshold - (alignedSet u0 u1 w0 w1).card ≤
      (voteSet u0 u1 w0 w1 gamma).card := by
  obtain ⟨hScard, hagree, _hno⟩ := hrides gamma hgamma
  have hsub := witness_subset_aligned_union_votes u0 u1 w0 w1 hagree
  have hcard := Finset.card_le_card hsub
  have hdisj : Disjoint (alignedSet u0 u1 w0 w1) (voteSet u0 u1 w0 w1 gamma) := by
    rw [Finset.disjoint_left]
    intro x hxA hxV
    exact (mem_voteSet_iff u0 u1 w0 w1 gamma x).mp hxV |>.1 hxA
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  omega

/-- A rider's combined aligned core and private vote set contains its whole threshold witness. -/
theorem rides_alignedUnionVote_card_ge_threshold
    (dom : Fin N ↪ F) (u0 u1 w0 w1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hrides : RidesAll dom u0 u1 w0 w1 R Sf)
    {gamma : F} (hgamma : gamma ∈ R) :
    predecessorThreshold ≤
      (alignedSet u0 u1 w0 w1 ∪ voteSet u0 u1 w0 w1 gamma).card := by
  obtain ⟨hScard, hagree, _hno⟩ := hrides gamma hgamma
  exact hScard.trans (Finset.card_le_card
    (witness_subset_aligned_union_votes u0 u1 w0 w1 hagree))

/-- **Weighted complement capacity for non-base riders.**  If none of a common-base pencil's
riders is the base scalar, every vote set lies in the fixed base-carrier complement.  Since the
vote sets are disjoint and each threshold witness forces at least `T-|A|` votes, their total
weighted demand fits in that complement. -/
theorem commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hnonbase : ∀ gamma ∈ R, gamma ≠ gamma0) :
    R.card * (predecessorThreshold -
      (alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card) ≤
      (Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
  let A := alignedSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
  let V := fun gamma => voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let C := Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hper : ∀ gamma ∈ R, predecessorThreshold - A.card ≤ (V gamma).card := by
    intro gamma hgamma
    obtain ⟨hScard, hagree, _hno⟩ := hrides gamma hgamma
    have hsub := witness_subset_aligned_union_votes u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) hagree
    have hcard := Finset.card_le_card hsub
    have hdisj : Disjoint A (V gamma) := by
      rw [Finset.disjoint_left]
      intro x hxA hxV
      exact (mem_voteSet_iff u0 u1 _ _ gamma x).mp hxV |>.1 hxA
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    omega
  have hlower : R.card * (predecessorThreshold - A.card) ≤
      ∑ gamma ∈ R, (V gamma).card := by
    calc
      R.card * (predecessorThreshold - A.card) =
          ∑ _gamma ∈ R, (predecessorThreshold - A.card) := by simp
      _ ≤ ∑ gamma ∈ R, (V gamma).card :=
        Finset.sum_le_sum fun gamma hgamma => hper gamma hgamma
  have hbiC : R.biUnion V ⊆ C := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨gamma, hgamma, hxV⟩ := hx
    exact commonBase_nonbase_vote_subset_baseAgree_compl
      (hnonbase gamma hgamma) p0 p1 u0 u1 hxV
  calc
    R.card * (predecessorThreshold - A.card) ≤ ∑ gamma ∈ R, (V gamma).card := hlower
    _ = (R.biUnion V).card := card_biUnion_votes u0 u1 _ _ R |>.symm
    _ ≤ C.card := Finset.card_le_card hbiC

/-- A threshold witness explained by the distinguished base codeword is contained in the fixed
base agreement carrier.  This supplies the `|B| ≥ T` premise used by the weighted capacity
argument directly from the global base witness. -/
theorem commonBase_agreeSet_card_ge_threshold_of_baseWitness
    (gamma0 : F) (p0 u0 u1 : Fin N → F) (S0 : Finset (Fin N))
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    predecessorThreshold ≤
      (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
  apply hS0.trans
  apply Finset.card_le_card
  intro x hx
  rw [agreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hagree0 x hx⟩

/-- **Base-rider inclusion through the entire lower three-rider band.**  Once the global
threshold witness for `(gamma0,p0)` is retained, a three-rider common-base pencil with alignment
strictly below the four-rider floor must contain `gamma0`.  Otherwise its three disjoint
non-base vote sets overflow the base-carrier complement. -/
theorem commonBase_threeRiders_lowerBand_base_mem
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 3)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card ≤
        432479346)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    gamma0 ∈ R := by
  by_contra hgamma0
  have hnonbase : ∀ gamma ∈ R, gamma ≠ gamma0 := by
    intro gamma hgamma heq
    exact hgamma0 (heq ▸ hgamma)
  have hcap := commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf hp0 hp1 hrides hnonbase
  have hBT := commonBase_agreeSet_card_ge_threshold_of_baseWitness
    gamma0 p0 u0 u1 S0 hS0 hagree0
  have hCcard : (Finset.univ \
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card =
      N - (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hR, hCcard] at hcap
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **Base-rider inclusion throughout the two-rider band.**  With the global threshold base
witness retained, two non-base riders already overflow the base-carrier complement at every
alignment strictly below the three-rider floor.  Hence every such two-rider pencil contains the
base scalar and has exactly one non-base rider available for charging. -/
theorem commonBase_twoRiders_belowThreeFloor_base_mem
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 2)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card ≤
        352321536)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    gamma0 ∈ R := by
  by_contra hgamma0
  have hnonbase : ∀ gamma ∈ R, gamma ≠ gamma0 := by
    intro gamma hgamma heq
    exact hgamma0 (heq ▸ hgamma)
  have hcap := commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf hp0 hp1 hrides hnonbase
  have hBT := commonBase_agreeSet_card_ge_threshold_of_baseWitness
    gamma0 p0 u0 u1 S0 hS0 hagree0
  have hCcard : (Finset.univ \
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card =
      N - (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hR, hCcard] at hcap
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **Exact carrier saturation at the three-rider floor.**  At minimal three-rider alignment,
the two non-base riders already demand the whole `N-T` complement.  The global base witness
gives the reverse carrier inequality, forcing the fixed base agreement carrier to have exactly
threshold size. -/
theorem commonBase_threeRider_minimal_agreeSet_card_eq_threshold
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 3)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        352321537)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card = predecessorThreshold := by
  have hgamma0 : gamma0 ∈ R := commonBase_threeRiders_lowerBand_base_mem
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR (by omega) hS0 hagree0
  let R' := R.erase gamma0
  have hR' : R'.card = 2 := by
    dsimp [R']
    simp [hgamma0, hR]
  have hrides' : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R' Sf := by
    intro gamma hgamma
    exact hrides gamma (Finset.mem_of_mem_erase hgamma)
  have hnonbase' : ∀ gamma ∈ R', gamma ≠ gamma0 := by
    intro gamma hgamma
    exact (Finset.mem_erase.mp hgamma).1
  have hcap := commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
    dom gamma0 gamma1 p0 p1 u0 u1 R' Sf hp0 hp1 hrides' hnonbase'
  have hBT := commonBase_agreeSet_card_ge_threshold_of_baseWitness
    gamma0 p0 u0 u1 S0 hS0 hagree0
  have hCcard : (Finset.univ \
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card =
      N - (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hR', hA, hCcard] at hcap
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- **Exact carrier saturation at the two-rider floor.**  After the forced base rider is
removed, the unique non-base rider demands `N-T` vote coordinates.  Together with the global
base witness this forces the base agreement carrier to have exactly threshold size. -/
theorem commonBase_twoRider_minimal_agreeSet_card_eq_threshold
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 2)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        111848108)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card = predecessorThreshold := by
  have hgamma0 : gamma0 ∈ R := commonBase_twoRiders_belowThreeFloor_base_mem
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR (by omega) hS0 hagree0
  let R' := R.erase gamma0
  have hR' : R'.card = 1 := by
    dsimp [R']
    simp [hgamma0, hR]
  have hrides' : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R' Sf := by
    intro gamma hgamma
    exact hrides gamma (Finset.mem_of_mem_erase hgamma)
  have hnonbase' : ∀ gamma ∈ R', gamma ≠ gamma0 := by
    intro gamma hgamma
    exact (Finset.mem_erase.mp hgamma).1
  have hcap := commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
    dom gamma0 gamma1 p0 p1 u0 u1 R' Sf hp0 hp1 hrides' hnonbase'
  have hBT := commonBase_agreeSet_card_ge_threshold_of_baseWitness
    gamma0 p0 u0 u1 S0 hS0 hagree0
  have hCcard : (Finset.univ \
      agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card =
      N - (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hR', hA, hCcard] at hcap
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- At the minimal two-rider endpoint, the unique non-base vote set covers the entire complement
of the base agreement carrier.  Thus its mismatch quotient specifies the direction at every
off-carrier coordinate. -/
theorem commonBase_twoRider_minimal_nonbaseVotes_eq_complement
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 2)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        111848108)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    (R.erase gamma0).biUnion (fun gamma => voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) =
      Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x) := by
  let V := fun gamma => voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  let C := Finset.univ \ B
  let R' := R.erase gamma0
  have hgamma0 : gamma0 ∈ R := commonBase_twoRiders_belowThreeFloor_base_mem
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR (by omega) hS0 hagree0
  have hB : B.card = predecessorThreshold :=
    commonBase_twoRider_minimal_agreeSet_card_eq_threshold
      dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR hA hS0 hagree0
  have hC : C.card = 480946858 := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hB]
    norm_num [N, predecessorThreshold]
  have hsub : R'.biUnion V ⊆ C := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨gamma, hgamma, hxV⟩ := hx
    exact commonBase_nonbase_vote_subset_baseAgree_compl
      (Finset.mem_erase.mp hgamma).1 p0 p1 u0 u1 hxV
  have hrides' : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R' Sf := by
    intro gamma hgamma
    exact hrides gamma (Finset.mem_of_mem_erase hgamma)
  have hR' : R'.card = 1 := by
    dsimp [R']
    simp [hgamma0, hR]
  have hlower : 480946858 ≤ ∑ gamma ∈ R', (V gamma).card := by
    calc
      480946858 = ∑ _gamma ∈ R', 480946858 := by simp [hR']
      _ ≤ ∑ gamma ∈ R', (V gamma).card := by
        exact Finset.sum_le_sum fun gamma hgamma => by
          have hv := rides_voteSet_card_ge_threshold_sub_aligned dom u0 u1
            (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
            R' Sf hrides' hgamma
          dsimp [V] at hv ⊢
          rw [hA] at hv
          have hT := predecessorThreshold_eq
          omega
  have hcardLower : C.card ≤ (R'.biUnion V).card := by
    rw [card_biUnion_votes u0 u1 _ _ R', hC]
    exact hlower
  exact Finset.eq_of_subset_of_card_le hsub hcardLower

/-- **Exact two-label complement partition.**  At the minimal three-rider endpoint, erase the
forced base rider.  The remaining two non-base vote sets exactly partition the complement of the
base agreement carrier.  This is the precise binary-label model used by the matching-overlap
reduction. -/
theorem commonBase_threeRider_minimal_nonbaseVotes_partition_complement
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 3)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        352321537)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    (R.erase gamma0).biUnion (fun gamma => voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) =
      Finset.univ \ agreeSet p0 (fun x => u0 x + gamma0 * u1 x) := by
  let V := fun gamma => voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  let C := Finset.univ \ B
  let R' := R.erase gamma0
  have hgamma0 : gamma0 ∈ R := commonBase_threeRiders_lowerBand_base_mem
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR (by omega) hS0 hagree0
  have hR' : R'.card = 2 := by
    dsimp [R']
    simp [hgamma0, hR]
  have hB : B.card = predecessorThreshold :=
    commonBase_threeRider_minimal_agreeSet_card_eq_threshold
      dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR hA hS0 hagree0
  have hC : C.card = N - predecessorThreshold := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hB]
  have hsub : R'.biUnion V ⊆ C := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨gamma, hgamma, hxV⟩ := hx
    exact commonBase_nonbase_vote_subset_baseAgree_compl
      (Finset.mem_erase.mp hgamma).1 p0 p1 u0 u1 hxV
  have hrides' : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R' Sf := by
    intro gamma hgamma
    exact hrides gamma (Finset.mem_of_mem_erase hgamma)
  have hper : ∀ gamma ∈ R', 240473429 ≤ (V gamma).card := by
    intro gamma hgamma
    have hv := rides_voteSet_card_ge_threshold_sub_aligned dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
      R' Sf hrides' hgamma
    dsimp [V] at hv ⊢
    rw [hA] at hv
    have hT := predecessorThreshold_eq
    omega
  have hlower : 480946858 ≤ ∑ gamma ∈ R', (V gamma).card := by
    calc
      480946858 = R'.card * 240473429 := by rw [hR']
      _ = ∑ _gamma ∈ R', 240473429 := by simp
      _ ≤ ∑ gamma ∈ R', (V gamma).card :=
        Finset.sum_le_sum fun gamma hgamma => hper gamma hgamma
  have hcardLower : C.card ≤ (R'.biUnion V).card := by
    rw [card_biUnion_votes u0 u1 _ _ R']
    rw [hC]
    have hN : N = 1073741824 := by norm_num [N]
    have hT := predecessorThreshold_eq
    omega
  exact Finset.eq_of_subset_of_card_le hsub hcardLower

/-- At the minimal three-rider endpoint, each of the two non-base color classes has exactly
`240473429` coordinates.  Thus the complement partition is balanced up to the unavoidable even
block-length split (here exactly half). -/
theorem commonBase_threeRider_minimal_nonbaseVote_card_eq
    (dom : Fin N ↪ F) (gamma0 gamma1 : F)
    (p0 p1 u0 u1 : Fin N → F)
    (R : Finset F) (Sf : F → Finset (Fin N))
    (S0 : Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hrides : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R Sf)
    (hR : R.card = 3)
    (hA : (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card =
        352321537)
    (hS0 : predecessorThreshold ≤ S0.card)
    (hagree0 : ∀ x ∈ S0, p0 x = u0 x + gamma0 * u1 x) :
    ∀ gamma ∈ R.erase gamma0,
      (voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma).card =
        240473429 := by
  let V := fun gamma => voteSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma
  let R' := R.erase gamma0
  have hgamma0 : gamma0 ∈ R := commonBase_threeRiders_lowerBand_base_mem
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR (by omega) hS0 hagree0
  have hR' : R'.card = 2 := by
    dsimp [R']
    simp [hgamma0, hR]
  have hpart := commonBase_threeRider_minimal_nonbaseVotes_partition_complement
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR hA hS0 hagree0
  have hB := commonBase_threeRider_minimal_agreeSet_card_eq_threshold
    dom gamma0 gamma1 p0 p1 u0 u1 R Sf S0 hp0 hp1 hrides hR hA hS0 hagree0
  have hsum : (∑ gamma ∈ R', (V gamma).card) = 480946858 := by
    rw [← card_biUnion_votes u0 u1 _ _ R']
    change ((R.erase gamma0).biUnion (fun gamma => voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma)).card = _
    rw [hpart, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hB]
    norm_num [N, predecessorThreshold]
  have hrides' : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R' Sf := by
    intro gamma hgamma
    exact hrides gamma (Finset.mem_of_mem_erase hgamma)
  have hper : ∀ gamma ∈ R', 240473429 ≤ (V gamma).card := by
    intro gamma hgamma
    have hv := rides_voteSet_card_ge_threshold_sub_aligned dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
      R' Sf hrides' hgamma
    dsimp [V] at hv ⊢
    rw [hA] at hv
    have hT := predecessorThreshold_eq
    omega
  intro gamma hgamma
  have hrestCard : (R'.erase gamma).card = 1 := by
    rw [Finset.card_erase_of_mem hgamma, hR']
  have hrest : 240473429 ≤ ∑ eta ∈ R'.erase gamma, (V eta).card := by
    calc
      240473429 = ∑ _eta ∈ R'.erase gamma, 240473429 := by
        simp [hrestCard]
      _ ≤ ∑ eta ∈ R'.erase gamma, (V eta).card := by
        exact Finset.sum_le_sum fun eta heta => hper eta (Finset.mem_of_mem_erase heta)
  have hsplit : (∑ eta ∈ R', (V eta).card) =
      (∑ eta ∈ R'.erase gamma, (V eta).card) + (V gamma).card :=
    (Finset.sum_erase_add _ _ hgamma).symm
  have hthis := hper gamma hgamma
  rw [hsum] at hsplit
  dsimp only [V] at hrest hsplit hthis ⊢
  omega

/-- Distinct common-base pencils force the fixed base agreement set to contain the union of
their aligned cores. -/
theorem commonBase_agreeSet_card_ge_two_alignments_sub_k_pred
    (dom : Fin N ↪ F) (gamma0 gamma1 gamma2 : F)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hne : (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) ≠
      (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2)) :
    (alignedSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card +
      (alignedSet u0 u1
        (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card -
      (k - 1) ≤ (agreeSet p0 (fun x => u0 x + gamma0 * u1 x)).card := by
  let A1 := alignedSet u0 u1
    (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)
  let A2 := alignedSet u0 u1
    (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)
  let B := agreeSet p0 (fun x => u0 x + gamma0 * u1 x)
  have hA1sub : A1 ⊆ B := by
    dsimp only [A1, B]
    rw [commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hA2sub : A2 ⊆ B := by
    dsimp only [A2, B]
    rw [commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hunion : (A1 ∪ A2).card ≤ B.card :=
    Finset.card_le_card (Finset.union_subset hA1sub hA2sub)
  have hinter : (A1 ∩ A2).card ≤ k - 1 := alignedSet_inter_card_lt_k dom u0 u1
    (pencilBase_mem _ hp0 hp1) (pencilDir_mem _ hp0 hp1)
    (pencilBase_mem _ hp0 hp2) (pencilDir_mem _ hp0 hp2) hne
  have hbook := Finset.card_union_add_card_inter A1 A2
  dsimp only [A1, A2, B] at hunion hinter hbook ⊢
  omega

/-- In the presence of a second distinct near-threshold pencil through the same base, every
fiber has at most `156,587,350` riders (including the base), rather than the crude
`480,946,859` cap. -/
theorem commonBase_nearThreshold_riders_card_le_156587350
    (dom : Fin N ↪ F) (gamma0 gamma1 gamma2 : F)
    (p0 p1 p2 u0 u1 : Fin N → F)
    (R1 : Finset F) (Sf1 : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf1)
    (hgamma0 : gamma0 ∈ R1)
    (hA1 : predecessorThreshold - 1 ≤ (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card)
    (hA2 : predecessorThreshold - 1 ≤ (alignedSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card)
    (hne : (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) ≠
      (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2)) :
    R1.card ≤ 156587350 := by
  have hB := commonBase_agreeSet_card_ge_two_alignments_sub_k_pred
    dom gamma0 gamma1 gamma2 p0 p1 p2 u0 u1 hp0 hp1 hp2 hne
  have hR := commonBase_riders_card_le_compl_agreeSet_add_one
    dom gamma0 gamma1 p0 p1 u0 u1 R1 Sf1 hp0 hp1 hrides1 hgamma0
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  omega

/-- Three distinct near-threshold pencils can contribute at most `469,762,048` scalar slots
after identifying their common base—strictly below the prize budget. -/
theorem three_commonBase_nearThreshold_partner_slots_le_N :
    1 + 3 * (156587350 - 1) = 469762048 ∧ 469762048 ≤ N := by
  constructor <;> norm_num [N]

/-- **Three-heavy channel closed.**  Three pairwise-distinct common-base pencils, each aligned
on at least `T-1` coordinates, have total fiber slots (with their common base counted once)
at most `N`. -/
theorem three_distinct_commonBase_nearThreshold_fibers_sum_le_N
    (dom : Fin N ↪ F) (gamma0 gamma1 gamma2 gamma3 : F)
    (p0 p1 p2 p3 u0 u1 : Fin N → F)
    (R1 R2 R3 : Finset F) (Sf1 Sf2 Sf3 : F → Finset (Fin N))
    (hp0 : p0 ∈ predecessorCode dom) (hp1 : p1 ∈ predecessorCode dom)
    (hp2 : p2 ∈ predecessorCode dom) (hp3 : p3 ∈ predecessorCode dom)
    (hrides1 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) R1 Sf1)
    (hrides2 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2) R2 Sf2)
    (hrides3 : RidesAll dom u0 u1
      (pencilBase gamma0 gamma3 p0 p3) (pencilDir gamma0 gamma3 p0 p3) R3 Sf3)
    (hgamma01 : gamma0 ∈ R1) (hgamma02 : gamma0 ∈ R2) (hgamma03 : gamma0 ∈ R3)
    (hA1 : predecessorThreshold - 1 ≤ (alignedSet u0 u1
      (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1)).card)
    (hA2 : predecessorThreshold - 1 ≤ (alignedSet u0 u1
      (pencilBase gamma0 gamma2 p0 p2) (pencilDir gamma0 gamma2 p0 p2)).card)
    (hA3 : predecessorThreshold - 1 ≤ (alignedSet u0 u1
      (pencilBase gamma0 gamma3 p0 p3) (pencilDir gamma0 gamma3 p0 p3)).card)
    (hne12 : (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) ≠
      (pencilBase gamma0 gamma2 p0 p2, pencilDir gamma0 gamma2 p0 p2))
    (hne13 : (pencilBase gamma0 gamma1 p0 p1, pencilDir gamma0 gamma1 p0 p1) ≠
      (pencilBase gamma0 gamma3 p0 p3, pencilDir gamma0 gamma3 p0 p3)) :
    1 + (R1.card - 1) + (R2.card - 1) + (R3.card - 1) ≤ N := by
  have hR1 := commonBase_nearThreshold_riders_card_le_156587350
    dom gamma0 gamma1 gamma2 p0 p1 p2 u0 u1 R1 Sf1 hp0 hp1 hp2
    hrides1 hgamma01 hA1 hA2 hne12
  have hR2 := commonBase_nearThreshold_riders_card_le_156587350
    dom gamma0 gamma2 gamma1 p0 p2 p1 u0 u1 R2 Sf2 hp0 hp2 hp1
    hrides2 hgamma02 hA2 hA1 (Ne.symm hne12)
  have hR3 := commonBase_nearThreshold_riders_card_le_156587350
    dom gamma0 gamma3 gamma1 p0 p3 p1 u0 u1 R3 Sf3 hp0 hp3 hp1
    hrides3 hgamma03 hA3 hA1 (Ne.symm hne13)
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-! ## Exact Turán-to-star concentration at the over-budget endpoint -/

/-- At exactly one more than the prize budget, the sharp four-part Turán lower bound
is large enough that average large-overlap degree exceeds `k - 1`. -/
theorem overBudget_fourPart_edgeFloor_twice_gt_vertices_mul_k_pred :
    let m := N + 1
    let e := m.choose 2 -
      ((m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2)
    m * (k - 1) < 2 * e := by
  dsimp only
  rw [Nat.choose_two_right]
  norm_num [N, k]

/-- A graph with the exact over-budget four-part Turán edge floor has a vertex of
degree at least `k`.  This is the handshake upgrade from mere existence of pinned
secants to a single scalar incident to `k` of them. -/
theorem exists_degree_ge_k_of_overBudget_fourPart_edgeFloor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hcard : Fintype.card V = N + 1)
    (hedges : (N + 1).choose 2 -
        ((((N + 1) ^ 2 - ((N + 1) % 4) ^ 2) * 3 / 8) +
          ((N + 1) % 4).choose 2) ≤ #G.edgeFinset) :
    ∃ v, k ≤ G.degree v := by
  classical
  by_contra hnot
  push_neg at hnot
  have hkpos : 0 < k := by norm_num [k]
  have hdegree : ∀ v, G.degree v ≤ k - 1 := by
    intro v
    exact Nat.le_pred_of_lt (hnot v)
  have hsum : (∑ v, G.degree v) ≤ Fintype.card V * (k - 1) := by
    calc
      (∑ v, G.degree v) ≤ ∑ _v : V, (k - 1) :=
        Finset.sum_le_sum fun v _hv => hdegree v
      _ = Fintype.card V * (k - 1) := by simp
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have hfloor := overBudget_fourPart_edgeFloor_twice_gt_vertices_mul_k_pred
  dsimp only at hfloor
  rw [hcard] at hsum
  omega

/-! The degree conclusion alone does not consolidate the star.  The following exact
sunflower realizes all presently available core-incidence constraints with `k` distinct
petals: every core has size `k`, while every two distinct cores meet in exactly `k - 1`. -/

/-- The abstract sharp sunflower modelling `k` distinct secant cores through one base. -/
noncomputable def degreeKStarCore (i : Fin k) : Finset Nat :=
  Finset.range (k - 1) ∪ {k - 1 + i.1}

theorem degreeKStarCore_card (i : Fin k) :
    (degreeKStarCore i).card = k := by
  rw [degreeKStarCore, Finset.card_union_of_disjoint]
  · simp [k]
  · rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_range]
    omega

/-- All `k` sunflower cores fit inside a single set of threshold cardinality `T`, so the
actual size of the base agreement set does not rule out the model. -/
theorem degreeKStarCore_subset_thresholdUniverse (i : Fin k) :
    degreeKStarCore i ⊆ Finset.range predecessorThreshold := by
  intro x hx
  simp only [degreeKStarCore, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton] at hx ⊢
  rcases hx with hx | rfl
  · have hk : k = 268435456 := by norm_num [k]
    have hT := predecessorThreshold_eq
    omega
  · have hi : i.1 < k := i.2
    have hk : k = 268435456 := by norm_num [k]
    have hT := predecessorThreshold_eq
    omega

theorem degreeKStarCore_inter_eq (i j : Fin k) (hij : i ≠ j) :
    degreeKStarCore i ∩ degreeKStarCore j = Finset.range (k - 1) := by
  ext x
  simp only [degreeKStarCore, Finset.mem_inter, Finset.mem_union,
    Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hxi | hxi, hxj | hxj⟩
    · exact hxi
    · exact hxi
    · exact hxj
    · exfalso
      apply hij
      apply Fin.ext
      omega
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

theorem degreeKStarCore_inter_card (i j : Fin k) (hij : i ≠ j) :
    (degreeKStarCore i ∩ degreeKStarCore j).card = k - 1 := by
  rw [degreeKStarCore_inter_eq i j hij, Finset.card_range]

theorem degreeKStarCore_injective : Function.Injective degreeKStarCore := by
  intro i j heq
  by_contra hij
  have hinter := congrArg Finset.card
    (congrArg (fun S => S ∩ degreeKStarCore j) heq)
  change (degreeKStarCore i ∩ degreeKStarCore j).card =
    (degreeKStarCore j ∩ degreeKStarCore j).card at hinter
  rw [degreeKStarCore_inter_card i j hij, Finset.inter_self,
    degreeKStarCore_card] at hinter
  have hkpos : 0 < k := by norm_num [k]
  omega

/-- **Common-core rigidity.**  If two degree-`<k` secant directions agree on exactly
`k-1` injected coordinates, their difference is a scalar multiple of the common-core
locator.  Consequently a sunflower star at the interpolation cap is not arbitrary: all
of its directions lie on one affine line in the polynomial space. -/
theorem direction_sub_eq_locator_mul_C_of_commonCore
    (dom : Fin N ↪ F) (Cset : Finset (Fin N)) (r₀ r : F[X])
    (hcard : Cset.card = k - 1)
    (hr₀ : r₀.natDegree < k) (hr : r.natDegree < k)
    (hagree : ∀ x ∈ Cset, r.eval (dom x) = r₀.eval (dom x)) :
    r - r₀ = (Cset.prod fun x => X - C (dom x)) * C (r - r₀).leadingCoeff := by
  let L : F[X] := Cset.prod fun x => X - C (dom x)
  have hLmonic : L.Monic := by
    exact monic_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)
  have hLdeg : L.natDegree = k - 1 := by
    change (Cset.prod fun x => X - C (dom x)).natDegree = k - 1
    rw [natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)]
    simpa using hcard
  have hdiffdeg : (r - r₀).natDegree ≤ k - 1 := by
    exact (natDegree_sub_le r r₀).trans (max_le (by omega) (by omega))
  by_cases hzero : r - r₀ = 0
  · simp [hzero]
  have hdvd : L ∣ r - r₀ := by
    apply ProximityGap.WBPencil.vanishing_prod_dvd dom hzero
    intro x hx
    simp only [eval_sub]
    exact sub_eq_zero.mpr (hagree x hx)
  exact eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    hLmonic hdvd (hLdeg.symm ▸ hdiffdeg)

/-- Affine-line packaging of common-core rigidity.  This is the usable output for a
degree-`k` overlap star: once a common `(k-1)`-core is identified, every incident
direction is parametrized by one field scalar. -/
theorem exists_direction_eq_base_add_locator_mul_C_of_commonCore
    (dom : Fin N ↪ F) (Cset : Finset (Fin N)) (r₀ r : F[X])
    (hcard : Cset.card = k - 1)
    (hr₀ : r₀.natDegree < k) (hr : r.natDegree < k)
    (hagree : ∀ x ∈ Cset, r.eval (dom x) = r₀.eval (dom x)) :
    ∃ c : F, r = r₀ + (Cset.prod fun x => X - C (dom x)) * C c := by
  let c := (r - r₀).leadingCoeff
  refine ⟨c, ?_⟩
  simpa only [c, add_comm] using (sub_eq_iff_eq_add.mp
    (direction_sub_eq_locator_mul_C_of_commonCore
      dom Cset r₀ r hcard hr₀ hr hagree))

/-! ## Locator-coefficient incidence geometry -/

/-- Three affine-locator neighbors agreeing at one coordinate off the locator zero set
force their parameter points `(a, a*c)` to be collinear.  This is the local algebraic
bridge from coordinate agreement multiplicity to a common source pencil. -/
theorem three_affineLocator_agreements_force_parameter_collinear
    (D R L a₁ a₂ a₃ c₁ c₂ c₃ : F)
    (hL : L ≠ 0)
    (h₁ : D + a₁ * (R + c₁ * L) = 0)
    (h₂ : D + a₂ * (R + c₂ * L) = 0)
    (h₃ : D + a₃ * (R + c₃ * L) = 0) :
    (a₁ - a₂) * (a₁ * c₁ - a₃ * c₃) =
      (a₁ - a₃) * (a₁ * c₁ - a₂ * c₂) := by
  have h₁₂ : (a₁ - a₂) * R + (a₁ * c₁ - a₂ * c₂) * L = 0 := by
    linear_combination h₁ - h₂
  have h₁₃ : (a₁ - a₃) * R + (a₁ * c₁ - a₃ * c₃) * L = 0 := by
    linear_combination h₁ - h₃
  have hdet : ((a₁ - a₂) * (a₁ * c₁ - a₃ * c₃) -
      (a₁ - a₃) * (a₁ * c₁ - a₂ * c₂)) * L = 0 := by
    linear_combination (a₁ - a₂) * h₁₃ - (a₁ - a₃) * h₁₂
  have := (mul_eq_zero.mp hdet).resolve_right hL
  exact sub_eq_zero.mp this

/-- Polynomial endpoint represented by an affine-locator parameter point `(a, a*c)`. -/
noncomputable def affineLocatorEndpoint
    (q₀ r₀ L : F[X]) (a c : F) : F[X] :=
  q₀ + C a * (r₀ + C c * L)

/-- Parameter-plane collinearity is exactly source-polynomial collinearity: the three
endpoint polynomials satisfy the denominator-cleared secant identity. -/
theorem endpoint_crossProduct_eq_of_parameter_collinear
    (q₀ r₀ L : F[X]) (a₁ a₂ a₃ c₁ c₂ c₃ : F)
    (hcol : (a₁ - a₂) * (a₁ * c₁ - a₃ * c₃) =
      (a₁ - a₃) * (a₁ * c₁ - a₂ * c₂)) :
    C (a₁ - a₃) *
        (affineLocatorEndpoint q₀ r₀ L a₁ c₁ -
          affineLocatorEndpoint q₀ r₀ L a₂ c₂) =
      C (a₁ - a₂) *
        (affineLocatorEndpoint q₀ r₀ L a₁ c₁ -
          affineLocatorEndpoint q₀ r₀ L a₃ c₃) := by
  have hC := congrArg C hcol.symm
  simp only [map_mul, map_sub] at hC
  unfold affineLocatorEndpoint
  simp only [map_sub]
  ring_nf at hC ⊢
  linear_combination hC * L

/-! ## Exact star-charge closure arithmetic -/

/-- After discarding at most four source lines with at most `215` neighbors each, the
remaining low-core neighbors contribute far more off-base incidences than a universe of
size `N-T` can carry at coordinate load `215`. -/
theorem lowCoreStar_charge_strictly_exceeds_215_capacity :
    215 * (N - predecessorThreshold) <
      (k - 4 * 215) *
        (predecessorThreshold -
          (P1RateQuarterAgreementOverlapGraph.FourLineCoreFloor - 1)) := by
  norm_num [N, k, predecessorThreshold,
    P1RateQuarterAgreementOverlapGraph.FourLineCoreFloor]

/-- Double-counting interface for the upper side of the star charge.  Petals supported
outside a base set `A`, with coordinate load at most `215`, have total size at most
`215 * (N - |A|)`. -/
theorem sum_petal_card_le_215_mul_complement
    {J : Type} [DecidableEq J]
    (B : Finset J) (A : Finset (Fin N)) (petal : J → Finset (Fin N))
    (hsub : ∀ j ∈ B, petal j ⊆ Aᶜ)
    (hload : ∀ x, petalLoad B petal x ≤ 215) :
    (∑ j ∈ B, (petal j).card) ≤ 215 * (N - A.card) := by
  have hzero : ∀ x ∈ A, petalLoad B petal x = 0 := by
    intro x hx
    rw [petalLoad, Finset.card_eq_zero]
    simp only [Finset.filter_eq_empty_iff]
    intro j hj
    exact fun hxpetal => (Finset.mem_compl.mp (hsub j hj hxpetal)) hx
  rw [← sum_petalLoad_eq_sum_card B petal]
  calc
    (∑ x : Fin N, petalLoad B petal x) ≤
        ∑ x : Fin N, if x ∈ A then 0 else 215 := by
      exact Finset.sum_le_sum fun x _hx => by
        split_ifs with hx
        · simp [hzero x hx]
        · exact hload x
    _ = 215 * (N - A.card) := by
      have hcard : (Aᶜ : Finset (Fin N)).card = N - A.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      rw [← hcard]
      calc
        (∑ x : Fin N, if x ∈ A then 0 else 215) =
            ∑ x : Fin N, if x ∈ Aᶜ then 215 else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hx : x ∈ A <;> simp [hx]
        _ = ∑ x ∈ Aᶜ, 215 := Finset.sum_ite_mem_eq _ _
        _ = 215 * (Aᶜ : Finset (Fin N)).card := by simp [mul_comm]

/-- Abstract counting closure for the concentrated star.  Once at most `4*215` exceptional
neighbors are removed, low-core petals of the exact forced size cannot all have total
coordinate capacity at most `215*(N-T)`. -/
theorem lowCoreStar_charge_contradiction
    {J : Type} [DecidableEq J]
    (B E : Finset J) (petal : J → Finset (Fin N))
    (hB : k ≤ B.card)
    (hEsub : E ⊆ B)
    (hE : E.card ≤ 4 * 215)
    (hpetal : ∀ j ∈ B \ E,
      predecessorThreshold -
          (P1RateQuarterAgreementOverlapGraph.FourLineCoreFloor - 1) ≤
        (petal j).card)
    (hcapacity : (∑ j ∈ B \ E, (petal j).card) ≤
      215 * (N - predecessorThreshold)) : False := by
  let s := predecessorThreshold -
    (P1RateQuarterAgreementOverlapGraph.FourLineCoreFloor - 1)
  have hregular : k - 4 * 215 ≤ (B \ E).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hEsub]
    omega
  have hlower : (B \ E).card * s ≤ ∑ j ∈ B \ E, (petal j).card := by
    calc
      (B \ E).card * s = ∑ _j ∈ B \ E, s := by simp
      _ ≤ ∑ j ∈ B \ E, (petal j).card := by
        exact Finset.sum_le_sum fun j hj => hpetal j hj
  have hmono : (k - 4 * 215) * s ≤ (B \ E).card * s :=
    Nat.mul_le_mul_right s hregular
  have harith := lowCoreStar_charge_strictly_exceeds_215_capacity
  dsimp only [s] at hlower hmono
  omega

/-- Ready-to-use star closure: threshold-sized base support, low-core petal floor, and
coordinate load at most `215` are jointly inconsistent for a degree-`k` star after the
four exceptional `215`-point lines are removed. -/
theorem lowCoreStar_load_216_forced
    {J : Type} [DecidableEq J]
    (B E : Finset J) (A : Finset (Fin N)) (petal : J → Finset (Fin N))
    (hB : k ≤ B.card)
    (hEsub : E ⊆ B)
    (hE : E.card ≤ 4 * 215)
    (hA : predecessorThreshold ≤ A.card)
    (hsub : ∀ j ∈ B \ E, petal j ⊆ Aᶜ)
    (hpetal : ∀ j ∈ B \ E,
      predecessorThreshold -
          (P1RateQuarterAgreementOverlapGraph.FourLineCoreFloor - 1) ≤
        (petal j).card) :
    ∃ x, 216 ≤ petalLoad (B \ E) petal x := by
  by_contra hnot
  have hload : ∀ x, petalLoad (B \ E) petal x ≤ 215 := by
    intro x
    exact Nat.le_pred_of_lt (Nat.lt_of_not_ge fun hx => hnot ⟨x, hx⟩)
  have hcapA := sum_petal_card_le_215_mul_complement
    (B \ E) A petal hsub hload
  have hcap : (∑ j ∈ B \ E, (petal j).card) ≤
      215 * (N - predecessorThreshold) := by
    have hcomp : N - A.card ≤ N - predecessorThreshold :=
      Nat.sub_le_sub_left hA N
    exact hcapA.trans (Nat.mul_le_mul_left 215 hcomp)
  exact lowCoreStar_charge_contradiction B E petal hB hEsub hE hpetal hcap

/-! ## One-coordinate consolidation is false -/

/-- Degree-one polynomial endpoints on the parameter parabola. -/
noncomputable def parabolaEndpoint (gamma : F) : F[X] := C (gamma ^ 2) * X

/-- Every parabola endpoint collapses to the same value at coordinate `0`. -/
theorem parabolaEndpoint_eval_zero (gamma : F) :
    (parabolaEndpoint gamma).eval 0 = 0 := by
  simp [parabolaEndpoint]

/-- Three pairwise-distinct parabola parameters are not on one polynomial source line,
despite all agreeing at coordinate `0`.  Thus even enormous one-coordinate load cannot by
itself be upgraded to a polynomial pencil; genuine cross-coordinate matching is necessary. -/
theorem parabolaEndpoint_three_not_source_collinear
    (gamma₀ gamma₁ gamma₂ : F)
    (h₀₁ : gamma₀ ≠ gamma₁)
    (h₀₂ : gamma₀ ≠ gamma₂)
    (h₁₂ : gamma₁ ≠ gamma₂) :
    C (gamma₀ - gamma₂) *
        (parabolaEndpoint gamma₀ - parabolaEndpoint gamma₁) ≠
      C (gamma₀ - gamma₁) *
        (parabolaEndpoint gamma₀ - parabolaEndpoint gamma₂) := by
  intro hcol
  have hc := congrArg (fun p : F[X] => p.eval 1) hcol
  simp [parabolaEndpoint] at hc
  have hprod : (gamma₀ - gamma₁) * (gamma₀ - gamma₂) *
      (gamma₁ - gamma₂) = 0 := by
    linear_combination hc
  rcases mul_eq_zero.mp hprod with hprod | h₁₂zero
  · rcases mul_eq_zero.mp hprod with h₀₁zero | h₀₂zero
    · exact h₀₁ (sub_eq_zero.mp h₀₁zero)
    · exact h₀₂ (sub_eq_zero.mp h₀₂zero)
  · exact h₁₂ (sub_eq_zero.mp h₁₂zero)

/-- **Exact cross-coordinate repair.**  If the same three degree-`<k` endpoint
polynomials are evaluation-collinear on at least `k` injected coordinates, then they are
collinear as polynomial source points.  The parabola countermodel shows that replacing
`k` by one is impossible. -/
theorem source_collinear_of_eval_collinear_on_k
    (dom : Fin N ↪ F) (S : Finset (Fin N))
    (gamma₀ gamma₁ gamma₂ : F) (q₀ q₁ q₂ : F[X])
    (hq₀ : q₀.natDegree < k) (hq₁ : q₁.natDegree < k)
    (hq₂ : q₂.natDegree < k) (hcard : k ≤ S.card)
    (hcol : ∀ x ∈ S,
      (gamma₀ - gamma₂) * (q₀.eval (dom x) - q₁.eval (dom x)) =
        (gamma₀ - gamma₁) * (q₀.eval (dom x) - q₂.eval (dom x))) :
    C (gamma₀ - gamma₂) * (q₀ - q₁) =
      C (gamma₀ - gamma₁) * (q₀ - q₂) := by
  let M := C (gamma₀ - gamma₂) * (q₀ - q₁) -
    C (gamma₀ - gamma₁) * (q₀ - q₂)
  have hMdeg : M.natDegree < k := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · calc
        (C (gamma₀ - gamma₂) * (q₀ - q₁)).natDegree ≤
            (C (gamma₀ - gamma₂)).natDegree + (q₀ - q₁).natDegree := natDegree_mul_le
        _ ≤ 0 + max q₀.natDegree q₁.natDegree :=
          Nat.add_le_add (le_of_eq (natDegree_C _)) (natDegree_sub_le _ _)
        _ < 0 + k := Nat.add_lt_add_left (max_lt hq₀ hq₁) 0
        _ = k := Nat.zero_add k
    · calc
        (C (gamma₀ - gamma₁) * (q₀ - q₂)).natDegree ≤
            (C (gamma₀ - gamma₁)).natDegree + (q₀ - q₂).natDegree := natDegree_mul_le
        _ ≤ 0 + max q₀.natDegree q₂.natDegree :=
          Nat.add_le_add (le_of_eq (natDegree_C _)) (natDegree_sub_le _ _)
        _ < 0 + k := Nat.add_lt_add_left (max_lt hq₀ hq₂) 0
        _ = k := Nat.zero_add k
  have hMzero : M = 0 := by
    by_contra hne
    have hdvd : (S.prod fun x => X - C (dom x)) ∣ M := by
      apply ProximityGap.WBPencil.vanishing_prod_dvd dom hne
      intro x hx
      simp only [M, eval_sub, eval_mul, eval_C]
      exact sub_eq_zero.mpr (hcol x hx)
    have hlocDegree : (S.prod fun x => X - C (dom x)).natDegree = S.card := by
      rw [natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)]
      simp
    have hle := natDegree_le_of_dvd hdvd hne
    rw [hlocDegree] at hle
    omega
  exact sub_eq_zero.mp hMzero

/-- The naive third-moment pigeonhole is millions-fold short: even assigning the forced
average low-core load `1,248,534` to every off-base coordinate does not force one triple
to recur on `k` coordinates.  A successful matching argument must exploit more than the
unstructured triple-incidence moment. -/
theorem uniformTripleMoment_below_crossCoordinate_budget :
    (N - predecessorThreshold) * Nat.choose 1248534 3 <
      (k - 1) * Nat.choose (k - 4 * 215) 3 := by
  norm_num [N, k, predecessorThreshold, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial]

/-! ## Global triple-incidence census -/

/-- Coordinates on which every label of a finite triple is supported. -/
def tripleContainmentCoords
    {X J : Type} [Fintype X] [DecidableEq X] [DecidableEq J]
    (support : X → Finset J) (U : Finset J) : Finset X :=
  Finset.univ.filter fun x => U ⊆ support x

/-- Exact third-incidence double count: choosing three supported labels at each coordinate
is the same as summing the common-coordinate count over all three-label subsets. -/
theorem sum_choose_three_support_eq_sum_tripleContainment
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X → Finset J) :
    (∑ x : X, (support x).card.choose 3) =
      ∑ U ∈ (Finset.univ : Finset J).powersetCard 3,
        (tripleContainmentCoords support U).card := by
  classical
  calc
    (∑ x : X, (support x).card.choose 3) =
        ∑ x : X, ((support x).powersetCard 3).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (Finset.card_powersetCard 3 (support x)).symm
    _ = ∑ x : X, ∑ U ∈ (Finset.univ : Finset J).powersetCard 3,
          if U ⊆ support x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.card_filter]
      congr 1
      ext U
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hsub, hcard⟩
        exact ⟨⟨Finset.subset_univ _, hcard⟩, hsub⟩
      · rintro ⟨⟨_huniv, hcard⟩, hsub⟩
        exact ⟨hsub, hcard⟩
    _ = ∑ U ∈ (Finset.univ : Finset J).powersetCard 3,
          ∑ x : X, if U ⊆ support x then 1 else 0 := Finset.sum_comm
    _ = ∑ U ∈ (Finset.univ : Finset J).powersetCard 3,
          (tripleContainmentCoords support U).card := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [tripleContainmentCoords, Finset.card_filter]

/-- If every three-label set occurs on at most `k-1` coordinates, the whole support design
obeys the corresponding global third-incidence cap. -/
theorem sum_choose_three_support_le_of_triple_cap
    {X J : Type} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    (support : X → Finset J)
    (hcap : ∀ U ∈ (Finset.univ : Finset J).powersetCard 3,
      (tripleContainmentCoords support U).card ≤ k - 1) :
    (∑ x : X, (support x).card.choose 3) ≤
      (Fintype.card J).choose 3 * (k - 1) := by
  rw [sum_choose_three_support_eq_sum_tripleContainment support]
  calc
    (∑ U ∈ (Finset.univ : Finset J).powersetCard 3,
        (tripleContainmentCoords support U).card) ≤
      ∑ _U ∈ (Finset.univ : Finset J).powersetCard 3, (k - 1) := by
        exact Finset.sum_le_sum fun U hU => hcap U hU
    _ = (Fintype.card J).choose 3 * (k - 1) := by simp

/-! ## Rich-family triple root cap -/

/-- Common full-agreement coordinates of three selected rich points. -/
def richFamilyTripleCoords
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma₀ gamma₁ gamma₂ : family.G) : Finset (Fin N) :=
  fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
    fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1) ∩
      fullAgreement dom (u 0) (u 1) gamma₂.1 (family.q gamma₂.1)

/-- Coordinate-side support hypergraph of a rich-point family. -/
def richFamilySupport
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u) (x : Fin N) : Finset family.G :=
  Finset.univ.filter fun gamma =>
    x ∈ fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1)

/-- The abstract containment-coordinate construction specializes exactly to the intersection
of the three selected full-agreement sets. -/
theorem tripleContainmentCoords_richFamilySupport
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma₀ gamma₁ gamma₂ : family.G) :
    tripleContainmentCoords (richFamilySupport family) {gamma₀, gamma₁, gamma₂} =
      richFamilyTripleCoords family gamma₀ gamma₁ gamma₂ := by
  ext x
  rw [richFamilyTripleCoords, Finset.mem_inter, Finset.mem_inter]
  simp only [tripleContainmentCoords, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsub
    have h₀ := hsub (show gamma₀ ∈ ({gamma₀, gamma₁, gamma₂} : Finset family.G) by simp)
    have h₁ := hsub (show gamma₁ ∈ ({gamma₀, gamma₁, gamma₂} : Finset family.G) by simp)
    have h₂ := hsub (show gamma₂ ∈ ({gamma₀, gamma₁, gamma₂} : Finset family.G) by simp)
    simpa only [richFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and] using
      And.intro (And.intro h₀ h₁) h₂
  · rintro ⟨⟨h₀, h₁⟩, h₂⟩ gamma hgamma
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgamma
    rcases hgamma with rfl | rfl | rfl
    · simpa only [richFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    · simpa only [richFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    · simpa only [richFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- In an actual rich-point family, every triple that is not polynomial-source-collinear
has at most `k-1` common support coordinates.  This discharges the abstract cap hypothesis
of the global third-incidence census directly from decoded degree bounds. -/
theorem richFamilyTripleCoords_card_le_k_pred_of_not_sourceCollinear
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma₀ gamma₁ gamma₂ : family.G)
    (hnoncol :
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1)) :
    (richFamilyTripleCoords family gamma₀ gamma₁ gamma₂).card ≤ k - 1 := by
  by_contra hnot
  have hcard : k ≤ (richFamilyTripleCoords family gamma₀ gamma₁ gamma₂).card := by
    omega
  apply hnoncol
  apply source_collinear_of_eval_collinear_on_k dom
    (richFamilyTripleCoords family gamma₀ gamma₁ gamma₂)
    gamma₀.1 gamma₁.1 gamma₂.1
    (family.q gamma₀.1) (family.q gamma₁.1) (family.q gamma₂.1)
    (family.degree_lt gamma₀.1 gamma₀.2)
    (family.degree_lt gamma₁.1 gamma₁.2)
    (family.degree_lt gamma₂.1 gamma₂.2) hcard
  intro x hx
  simp only [richFamilyTripleCoords, Finset.mem_inter, fullAgreement,
    Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨⟨h₀, h₁⟩, h₂⟩
  rw [h₀, h₁, h₂]
  ring

/-- **Integrated rich-family third-moment cap.**  If no three distinct selected decoded
points lie on one polynomial source line, then the actual coordinate support hypergraph
satisfies the global `k-1` triple-recurrence bound. -/
theorem richFamily_thirdMoment_le_of_no_sourceCollinear
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hnoncol : ∀ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ → gamma₀ ≠ gamma₂ → gamma₁ ≠ gamma₂ →
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1)) :
    (∑ x : Fin N, (richFamilySupport family x).card.choose 3) ≤
      family.G.card.choose 3 * (k - 1) := by
  have hcap : ∀ U ∈ (Finset.univ : Finset family.G).powersetCard 3,
      (tripleContainmentCoords (richFamilySupport family) U).card ≤ k - 1 := by
    intro U hU
    have hUcard : U.card = 3 := (Finset.mem_powersetCard.mp hU).2
    obtain ⟨gamma₀, gamma₁, gamma₂, h₀₁, h₀₂, h₁₂, rfl⟩ :=
      Finset.card_eq_three.mp hUcard
    rw [tripleContainmentCoords_richFamilySupport]
    exact richFamilyTripleCoords_card_le_k_pred_of_not_sourceCollinear
      family gamma₀ gamma₁ gamma₂
        (hnoncol gamma₀ gamma₁ gamma₂ h₀₁ h₀₂ h₁₂)
  have hglobal := sum_choose_three_support_le_of_triple_cap
    (richFamilySupport family) hcap
  simpa using hglobal

/-- Consumer form: exceeding the exact third-incidence capacity forces three distinct
decoded points onto one polynomial source line. -/
theorem richFamily_exists_sourceCollinear_of_thirdMoment_gt
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hlarge : family.G.card.choose 3 * (k - 1) <
      ∑ x : Fin N, (richFamilySupport family x).card.choose 3) :
    ∃ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ ∧ gamma₀ ≠ gamma₂ ∧ gamma₁ ≠ gamma₂ ∧
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) =
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1) := by
  by_contra hnot
  push_neg at hnot
  have hcap := richFamily_thirdMoment_le_of_no_sourceCollinear family
    (fun gamma₀ gamma₁ gamma₂ h₀₁ h₀₂ h₁₂ =>
      hnot gamma₀ gamma₁ gamma₂ h₀₁ h₀₂ h₁₂)
  omega

/-- Exact literal-P1 audit of the third-moment consumer.  Distributing the mandatory
`(N+1)*T` incidences as evenly as possible gives load `T+1` on `T` coordinates and `T`
on the others; that convexity floor remains strictly below the no-collinear-triple
capacity.  Hence support sizes alone cannot fire the consumer. -/
theorem uniformFullFamily_thirdMoment_below_sourceCollinear_capacity :
    predecessorThreshold * Nat.choose (predecessorThreshold + 1) 3 +
      (N - predecessorThreshold) * Nat.choose predecessorThreshold 3 <
        Nat.choose (N + 1) 3 * (k - 1) := by
  norm_num [N, k, predecessorThreshold, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial]

/-! ## Fixed-anchor rank-two consolidation -/

/-- The denominator-cleared collinearity identity with a fixed distinct anchor pair places
the third decoded point on the anchors' canonical polynomial secant. -/
theorem mem_pointsOn_anchorSecant_of_crossProduct_eq
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma₀ gamma₁ gamma : F}
    (hgamma : gamma ∈ family.G)
    (h₀₁ : gamma₀ ≠ gamma₁) (h₀gamma : gamma₀ ≠ gamma)
    (hcol : C (gamma₀ - gamma) *
        (family.q gamma₀ - family.q gamma₁) =
      C (gamma₀ - gamma₁) *
        (family.q gamma₀ - family.q gamma)) :
    gamma ∈ pointsOn family (secantParameter family gamma₀ gamma₁) := by
  rw [mem_pointsOn_iff]
  refine ⟨hgamma, ?_⟩
  have hslope : slopePolynomial gamma₀ gamma (family.q gamma₀) (family.q gamma) =
      slopePolynomial gamma₀ gamma₁ (family.q gamma₀) (family.q gamma₁) := by
    simp only [slopePolynomial]
    have h₀gamma' : gamma₀ - gamma ≠ 0 := sub_ne_zero.mpr h₀gamma
    have h₀₁' : gamma₀ - gamma₁ ≠ 0 := sub_ne_zero.mpr h₀₁
    have ha : C (gamma₀ - gamma) * C (gamma₀ - gamma)⁻¹ = (1 : F[X]) := by
      rw [← C_mul, mul_inv_cancel₀ h₀gamma', C_1]
    have hb : C (gamma₀ - gamma₁) * C (gamma₀ - gamma₁)⁻¹ = (1 : F[X]) := by
      rw [← C_mul, mul_inv_cancel₀ h₀₁', C_1]
    have hab : C (gamma₀ - gamma) * C (gamma₀ - gamma₁) ≠ (0 : F[X]) :=
      mul_ne_zero (C_ne_zero.mpr h₀gamma') (C_ne_zero.mpr h₀₁')
    apply mul_left_cancel₀ hab
    calc
      (C (gamma₀ - gamma) * C (gamma₀ - gamma₁)) *
          (C (gamma₀ - gamma)⁻¹ * (family.q gamma₀ - family.q gamma)) =
          (C (gamma₀ - gamma) * C (gamma₀ - gamma)⁻¹) *
            (C (gamma₀ - gamma₁) * (family.q gamma₀ - family.q gamma)) := by ring
      _ = C (gamma₀ - gamma₁) * (family.q gamma₀ - family.q gamma) := by rw [ha, one_mul]
      _ = C (gamma₀ - gamma) * (family.q gamma₀ - family.q gamma₁) := hcol.symm
      _ = (C (gamma₀ - gamma₁) * C (gamma₀ - gamma₁)⁻¹) *
          (C (gamma₀ - gamma) * (family.q gamma₀ - family.q gamma₁)) := by rw [hb, one_mul]
      _ = (C (gamma₀ - gamma) * C (gamma₀ - gamma₁)) *
          (C (gamma₀ - gamma₁)⁻¹ * (family.q gamma₀ - family.q gamma₁)) := by ring
  simpa only [secantParameter] using
    (third_point_on_secant_line_of_slope_eq h₀gamma hslope)

/-- If every selected point satisfies the fixed-anchor cross-product identity, the entire
rich family is exactly the point set of one canonical polynomial source line. -/
theorem pointsOn_anchorSecant_eq_G_of_all_crossProducts
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma₀ gamma₁ : F} (h₀₁ : gamma₀ ≠ gamma₁)
    (hall : ∀ gamma ∈ family.G, gamma₀ ≠ gamma →
      C (gamma₀ - gamma) * (family.q gamma₀ - family.q gamma₁) =
        C (gamma₀ - gamma₁) * (family.q gamma₀ - family.q gamma)) :
    pointsOn family (secantParameter family gamma₀ gamma₁) = family.G := by
  apply Finset.Subset.antisymm (pointsOn_subset_G family _)
  intro gamma hgamma
  by_cases hgamma₀ : gamma = gamma₀
  · subst gamma
    exact first_point_mem_pointsOn_secant family hgamma
  · exact mem_pointsOn_anchorSecant_of_crossProduct_eq family hgamma h₀₁
      (Ne.symm hgamma₀) (hall gamma hgamma (Ne.symm hgamma₀))

/-- **Rank-two branch closed.**  If one selected distinct anchor pair is source-collinear
with every selected decoded point, the bad rich family has cardinality at most the coordinate
domain.  This composes fixed-anchor consolidation with the unconditional line-core packing law. -/
theorem richFamily_card_le_N_of_anchorCrossProducts
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma₀ gamma₁ : F}
    (hgamma₀ : gamma₀ ∈ family.G) (hgamma₁ : gamma₁ ∈ family.G)
    (h₀₁ : gamma₀ ≠ gamma₁)
    (hall : ∀ gamma ∈ family.G, gamma₀ ≠ gamma →
      C (gamma₀ - gamma) * (family.q gamma₀ - family.q gamma₁) =
        C (gamma₀ - gamma₁) * (family.q gamma₀ - family.q gamma)) :
    family.G.card ≤ N := by
  let line := secantParameter family gamma₀ gamma₁
  have hline : line ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma₀ hgamma₁ h₀₁
  have heq : pointsOn family line = family.G :=
    pointsOn_anchorSecant_eq_G_of_all_crossProducts family h₀₁ hall
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  simp only [Fintype.card_fin] at hpack
  rw [heq] at hpack
  have hone : 1 ≤ max 1
      (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
        (jointCore dom (u 0) (u 1) line.1 line.2).card) := le_max_left _ _
  have hmul : family.G.card ≤ family.G.card * max 1
      (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
        (jointCore dom (u 0) (u 1) line.1 line.2).card) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left family.G.card hone
  simp only [Fintype.card_fin] at hmul
  omega

/-- Family-wide rank-two form: if every three distinct selected decoded points are
source-collinear, then one anchor pair consolidates the whole family and the prize budget
follows. -/
theorem richFamily_card_le_N_of_allTriplesSourceCollinear
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (htwo : 2 ≤ family.G.card)
    (hall : ∀ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ → gamma₀ ≠ gamma₂ → gamma₁ ≠ gamma₂ →
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) =
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1)) :
    family.G.card ≤ N := by
  obtain ⟨gamma₀, hgamma₀, gamma₁, hgamma₁, h₀₁⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < family.G.card)
  apply richFamily_card_le_N_of_anchorCrossProducts family hgamma₀ hgamma₁ h₀₁
  intro gamma hgamma h₀gamma
  by_cases hgammaEq₁ : gamma = gamma₁
  · subst gamma
    rfl
  · exact hall ⟨gamma₀, hgamma₀⟩ ⟨gamma₁, hgamma₁⟩ ⟨gamma, hgamma⟩
      (by exact fun h => h₀₁ (Subtype.ext_iff.mp h))
      (by exact fun h => h₀gamma (Subtype.ext_iff.mp h))
      (by exact fun h => hgammaEq₁ (Subtype.ext_iff.mp h).symm)

/-- Every over-budget rich family contains a genuinely rank-three seed: three distinct
decoded points failing the polynomial source-collinearity identity. -/
theorem exists_nonSourceCollinearTriple_of_N_lt_richFamily_card
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card) :
    ∃ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ ∧ gamma₀ ≠ gamma₂ ∧ gamma₁ ≠ gamma₂ ∧
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1) := by
  by_contra hnot
  push_neg at hnot
  have hNtwo : 2 ≤ N := by norm_num [N]
  have hle := richFamily_card_le_N_of_allTriplesSourceCollinear family (by omega)
    (fun gamma₀ gamma₁ gamma₂ h₀₁ h₀₂ h₁₂ =>
      hnot gamma₀ gamma₁ gamma₂ h₀₁ h₀₂ h₁₂)
  omega

/-- Three threshold-size agreement sets force total pair-intersection mass at least
`704,643,074`; hence one of the three secant cores has size at least `234,881,025`. -/
theorem richFamily_three_pairIntersections_one_ge_234881025
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    (gamma₀ gamma₁ gamma₂ : family.G) :
    234881025 ≤
        (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
          fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1)).card ∨
      234881025 ≤
        (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
          fullAgreement dom (u 0) (u 1) gamma₂.1 (family.q gamma₂.1)).card ∨
      234881025 ≤
        (fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1) ∩
          fullAgreement dom (u 0) (u 1) gamma₂.1 (family.q gamma₂.1)).card := by
  let A (i : family.G) := fullAgreement dom (u 0) (u 1) i.1 (family.q i.1)
  have hsize : ∀ i : family.G, predecessorThreshold ≤ (A i).card := fun i =>
    hthreshold.trans (family.threshold_le i.1 i.2)
  have hbon := biUnion_card_ge_sub_pairwise (r := 3)
    (fun i : Fin 3 => ![A gamma₀, A gamma₁, A gamma₂] i)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue] at hbon
  have hpairs : (∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun p => p.1 < p.2),
      (![A gamma₀, A gamma₁, A gamma₂] p.1 ∩
        ![A gamma₀, A gamma₁, A gamma₂] p.2).card) =
      (A gamma₀ ∩ A gamma₁).card + (A gamma₀ ∩ A gamma₂).card +
        (A gamma₁ ∩ A gamma₂).card := by
    have hindices : (Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun p => p.1 < p.2) =
        {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)),
          ((1 : Fin 3), (2 : Fin 3))} := by decide
    rw [hindices]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    omega
  rw [hpairs] at hbon
  change (A gamma₀).card + (A gamma₁).card + (A gamma₂).card ≤
    (A gamma₀ ∩ A gamma₁).card + (A gamma₀ ∩ A gamma₂).card +
      (A gamma₁ ∩ A gamma₂).card +
        (Finset.univ.biUnion
          (fun i : Fin 3 => ![A gamma₀, A gamma₁, A gamma₂] i)).card at hbon
  have hbonA : (A gamma₀).card + (A gamma₁).card + (A gamma₂).card ≤
      (A gamma₀ ∩ A gamma₁).card + (A gamma₀ ∩ A gamma₂).card +
        (A gamma₁ ∩ A gamma₂).card +
          (Finset.univ.biUnion
            (fun i : Fin 3 => ![A gamma₀, A gamma₁, A gamma₂] i)).card := hbon
  clear hbon
  have hunion : (Finset.univ.biUnion
      (fun i : Fin 3 => ![A gamma₀, A gamma₁, A gamma₂] i)).card ≤ N := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ
      (Finset.univ.biUnion (fun i : Fin 3 => ![A gamma₀, A gamma₁, A gamma₂] i))
  by_contra hnot
  change ¬(234881025 ≤ (A gamma₀ ∩ A gamma₁).card ∨
      234881025 ≤ (A gamma₀ ∩ A gamma₂).card ∨
      234881025 ≤ (A gamma₁ ∩ A gamma₂).card) at hnot
  push_neg at hnot
  have hs₀ := hsize gamma₀
  have hs₁ := hsize gamma₁
  have hs₂ := hsize gamma₂
  have hn₀₁ : (A gamma₀ ∩ A gamma₁).card ≤ 234881024 := by omega
  have hn₀₂ : (A gamma₀ ∩ A gamma₂).card ≤ 234881024 := by omega
  have hn₁₂ : (A gamma₁ ∩ A gamma₂).card ≤ 234881024 := by omega
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Combined rank-three seed: an over-budget threshold family contains a non-source-collinear
triple for which at least one pair shares `234,881,025` agreement coordinates. -/
theorem exists_nonSourceCollinearTriple_with_largePairCore
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ∃ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ ∧ gamma₀ ≠ gamma₂ ∧ gamma₁ ≠ gamma₂ ∧
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1) ∧
      (234881025 ≤
          (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
            fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1)).card ∨
        234881025 ≤
          (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
            fullAgreement dom (u 0) (u 1) gamma₂.1 (family.q gamma₂.1)).card ∨
        234881025 ≤
          (fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1) ∩
            fullAgreement dom (u 0) (u 1) gamma₂.1 (family.q gamma₂.1)).card) := by
  obtain ⟨gamma₀, gamma₁, gamma₂, h₀₁, h₀₂, h₁₂, hnoncol⟩ :=
    exists_nonSourceCollinearTriple_of_N_lt_richFamily_card family hover
  exact ⟨gamma₀, gamma₁, gamma₂, h₀₁, h₀₂, h₁₂, hnoncol,
    richFamily_three_pairIntersections_one_ge_234881025
      family hthreshold gamma₀ gamma₁ gamma₂⟩

/-- **Exact global high-pair extraction.**  An over-budget threshold family contains two
agreement sets meeting on at least `327,272,221` coordinates.  This is the sharp integral
Plotkin onset at `N+1` for the literal P1 parameters. -/
theorem exists_richFamily_pair_inter_card_ge_327272221
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ∃ gamma₀ gamma₁ : family.G, gamma₀ ≠ gamma₁ ∧
      327272221 ≤
        (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
          fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1)).card := by
  classical
  by_contra hnot
  push_neg at hnot
  let A : family.G → Finset (Fin N) := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1)
  let A' : family.G → Finset (Fin N) := fun gamma =>
    Classical.choose (Finset.exists_subset_card_eq
      (hthreshold.trans (family.threshold_le gamma.1 gamma.2)))
  have hA'sub : ∀ gamma, A' gamma ⊆ A gamma := fun gamma =>
    (Classical.choose_spec (Finset.exists_subset_card_eq
      (hthreshold.trans (family.threshold_le gamma.1 gamma.2)))).1
  have hA'card : ∀ gamma, (A' gamma).card = predecessorThreshold := fun gamma =>
    (Classical.choose_spec (Finset.exists_subset_card_eq
      (hthreshold.trans (family.threshold_le gamma.1 gamma.2)))).2
  have hpair : ∀ gamma₀ gamma₁, gamma₀ ≠ gamma₁ →
      (A' gamma₀ ∩ A' gamma₁).card ≤ 327272220 := by
    intro gamma₀ gamma₁ hne
    have hle := Finset.card_le_card
      (Finset.inter_subset_inter (hA'sub gamma₀) (hA'sub gamma₁))
    have hlt := hnot gamma₀ gamma₁ hne
    dsimp only [A] at hle
    omega
  have hplot := ConstantWeightPlotkinBound.constantWeight_plotkin
    A' predecessorThreshold 327272220 hA'card hpair
  simp only [Fintype.card_coe, Fintype.card_fin] at hplot
  have hT := predecessorThreshold_eq
  norm_num [N] at hover hplot
  omega

/-- Any fixed distinct selected anchor pair in an over-budget family has a third selected
point that is genuinely noncollinear with it. -/
theorem exists_nonSourceCollinear_third_of_anchorPair_of_overBudget
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (gamma₀ gamma₁ : family.G) (h₀₁ : gamma₀ ≠ gamma₁) :
    ∃ gamma₂ : family.G, gamma₀ ≠ gamma₂ ∧ gamma₁ ≠ gamma₂ ∧
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1) := by
  by_contra hnot
  push_neg at hnot
  have hle := richFamily_card_le_N_of_anchorCrossProducts family
    gamma₀.2 gamma₁.2 (fun h => h₀₁ (Subtype.ext h))
    (fun gamma hgamma h₀gamma => by
      by_cases hgamma₁ : gamma = gamma₁.1
      · subst gamma; rfl
      · exact hnot ⟨gamma, hgamma⟩
          (fun h => h₀gamma (Subtype.ext_iff.mp h))
          (fun h => hgamma₁ (Subtype.ext_iff.mp h).symm))
  omega

/-- **Sharper rank-three seed.**  Every over-budget threshold family contains a
non-source-collinear triple whose chosen anchor pair already shares `327,272,221`
coordinates, exceeding the interpolation dimension by `58,836,765`. -/
theorem exists_nonSourceCollinearTriple_with_interpolationPinnedAnchor
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ∃ gamma₀ gamma₁ gamma₂ : family.G,
      gamma₀ ≠ gamma₁ ∧ gamma₀ ≠ gamma₂ ∧ gamma₁ ≠ gamma₂ ∧
      327272221 ≤
        (fullAgreement dom (u 0) (u 1) gamma₀.1 (family.q gamma₀.1) ∩
          fullAgreement dom (u 0) (u 1) gamma₁.1 (family.q gamma₁.1)).card ∧
      C (gamma₀.1 - gamma₂.1) *
          (family.q gamma₀.1 - family.q gamma₁.1) ≠
        C (gamma₀.1 - gamma₁.1) *
          (family.q gamma₀.1 - family.q gamma₂.1) := by
  obtain ⟨gamma₀, gamma₁, h₀₁, hcore⟩ :=
    exists_richFamily_pair_inter_card_ge_327272221 family hover hthreshold
  obtain ⟨gamma₂, h₀₂, h₁₂, hnoncol⟩ :=
    exists_nonSourceCollinear_third_of_anchorPair_of_overBudget
      family hover gamma₀ gamma₁ h₀₁
  exact ⟨gamma₀, gamma₁, gamma₂, h₀₁, h₀₂, h₁₂,
    hcore, hnoncol⟩

theorem highPairCore_interpolation_margin : 327272221 - k = 58836765 := by
  norm_num [k]

/-- A relevant P1 line containing at least three selected threshold points has joint core
at least `352,321,537`.  This is the exact three-point packing floor
`ceil((3*T-N)/2)`. -/
theorem three_pointsOn_force_core_ge_352321537
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hthree : 3 ≤ (pointsOn family line).card) :
    352321537 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let L := (pointsOn family line).card
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  simp only [Fintype.card_fin] at hpack
  rw [show (pointsOn family line).card = L from rfl,
    show (jointCore dom (u 0) (u 1) line.1 line.2).card = z from rfl] at hpack
  have hpack' : L * max 1
      (⌈(1 - delta) * (N : NNReal)⌉₊ - z) + z ≤ N := by
    exact hpack
  have hthreshold' : predecessorThreshold ≤ ⌈(1 - delta) * (N : NNReal)⌉₊ := by
    simpa only [Fintype.card_fin] using hthreshold
  have hfactor : predecessorThreshold - z ≤ max 1
      (⌈(1 - delta) * (N : NNReal)⌉₊ - z) :=
    (Nat.sub_le_sub_right hthreshold' z).trans (le_max_right _ _)
  have hmul : 3 * (predecessorThreshold - z) ≤
      L * max 1
        (⌈(1 - delta) * (N : NNReal)⌉₊ - z) :=
    Nat.mul_le_mul hthree hfactor
  have hbase : 3 * (predecessorThreshold - z) + z ≤ N :=
    (Nat.add_le_add_right hmul z).trans hpack'
  have hT := predecessorThreshold_eq
  norm_num [N] at hbase ⊢
  omega

/-- Below the three-point core floor, a relevant line contains exactly its determining pair. -/
theorem pointsOn_card_eq_two_of_core_lt_352321537
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : (jointCore dom (u 0) (u 1) line.1 line.2).card < 352321537) :
    (pointsOn family line).card = 2 := by
  have htwo := two_le_pointsOn_card_of_mem_lineParameters family hline
  have hnotthree : ¬ 3 ≤ (pointsOn family line).card := by
    intro hthree
    exact (Nat.not_le_of_lt hcore)
      (three_pointsOn_force_core_ge_352321537 family hthreshold hline hthree)
  omega

/-- A relevant P1 line containing at least four selected threshold points has joint core
at least `432,479,347`, the exact floor `ceil((4*T-N)/3)`. -/
theorem four_pointsOn_force_core_ge_432479347
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hfour : 4 ≤ (pointsOn family line).card) :
    432479347 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let L := (pointsOn family line).card
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  simp only [Fintype.card_fin] at hpack
  rw [show (pointsOn family line).card = L from rfl,
    show (jointCore dom (u 0) (u 1) line.1 line.2).card = z from rfl] at hpack
  have hpack' : L * max 1
      (⌈(1 - delta) * (N : NNReal)⌉₊ - z) + z ≤ N := by
    exact hpack
  have hthreshold' : predecessorThreshold ≤ ⌈(1 - delta) * (N : NNReal)⌉₊ := by
    simpa only [Fintype.card_fin] using hthreshold
  have hfactor : predecessorThreshold - z ≤ max 1
      (⌈(1 - delta) * (N : NNReal)⌉₊ - z) :=
    (Nat.sub_le_sub_right hthreshold' z).trans (le_max_right _ _)
  have hmul : 4 * (predecessorThreshold - z) ≤
      L * max 1
        (⌈(1 - delta) * (N : NNReal)⌉₊ - z) :=
    Nat.mul_le_mul hfour hfactor
  have hbase : 4 * (predecessorThreshold - z) + z ≤ N :=
    (Nat.add_le_add_right hmul z).trans hpack'
  have hT := predecessorThreshold_eq
  norm_num [N] at hbase ⊢
  omega

/-- Below the four-point floor, a relevant threshold line carries at most three points. -/
theorem pointsOn_card_le_three_of_core_lt_432479347
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : (jointCore dom (u 0) (u 1) line.1 line.2).card < 432479347) :
    (pointsOn family line).card ≤ 3 := by
  by_contra hnot
  have hfour : 4 ≤ (pointsOn family line).card := by omega
  exact (Nat.not_le_of_lt hcore)
    (four_pointsOn_force_core_ge_432479347 family hthreshold hline hfour)

/-- First two rungs of the exact P1 line-multiplicity ladder. -/
theorem relevantLine_core_ge_352321537_or_card_eq_two
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    352321537 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∨
      (pointsOn family line).card = 2 := by
  by_cases hcore : 352321537 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  · exact Or.inl hcore
  · exact Or.inr (pointsOn_card_eq_two_of_core_lt_352321537
      family hthreshold hline (by omega))

theorem relevantLine_core_ge_432479347_or_card_le_three
    {dom : Fin N ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : predecessorThreshold ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    432479347 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∨
      (pointsOn family line).card ≤ 3 := by
  by_cases hcore : 432479347 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  · exact Or.inl hcore
  · exact Or.inr (pointsOn_card_le_three_of_core_lt_432479347
      family hthreshold hline (by omega))

#print axioms private_petals_card_le_N
#print axioms cross_pencil_reuse_of_N_lt_card
#print axioms vote_reuse_of_overBudget
#print axioms witnessVotePetal_nonempty
#print axioms witness_overlap_outside_both_alignments_of_overBudget
#print axioms sum_petalLoad_eq_sum_card
#print axioms subNine_witnessVotePetal_card_floor
#print axioms exists_coordinate_petalLoad_ge_60118358
#print axioms exists_coordinate_petalLoad_ge_60118357_of_card_N
#print axioms commonBase_aligned_iff_base_agrees
#print axioms witnessVotePetal_commonBase_eq
#print axioms commonBase_pencilDir_apply
#print axioms commonBase_pencilBase_apply
#print axioms commonBase_centeredMinor_eq
#print axioms commonBase_centeredMinor_ne_zero
#print axioms partnerHitSet_pairwise_centeredMinor_ne_zero
#print axioms commonBase_subNine_exists_centeredMinorClique_60118357
#print axioms commonBase_pencilDir_ne_of_baseMismatch
#print axioms commonBase_pencilKey_ne_of_baseMismatch
#print axioms commonBase_directionDeviation_crossCoordinate
#print axioms commonBase_baseDeviation_crossCoordinate
#print axioms commonBase_twoPartner_directionDeviation_minor_eq_zero
#print axioms commonBase_directionDeviation_on_witness
#print axioms commonBase_twoPartner_directionDeviation_proportional_on_inter
#print axioms commonBase_centeredPencilEval_factorization_on_witness
#print axioms commonBase_centeredPencilEval_crossCoordinate_rankOne
#print axioms exists_baseMismatch_hit_by_60118358_partners
#print axioms exists_baseMismatch_hit_by_60118357_of_N_partners
#print axioms petalLoad_le_image_card_of_fiber_disjoint
#print axioms witnessVotePetal_subset_voteSet
#print axioms commonBase_distinctPencils_ge_60118357
#print axioms commonBase_aboveSubNine_or_distinctPencils_ge_60118357
#print axioms johnsonLight_witnessVotePetal_card_floor
#print axioms exists_coordinate_petalLoad_ge_55924056_of_card_N
#print axioms exists_baseMismatch_hit_by_55924056_of_N_partners
#print axioms commonBase_petalLoad_le_distinctPencils
#print axioms commonBase_johnsonLight_distinctPencils_ge_55924056
#print axioms commonBase_johnsonHeavy_or_distinctPencils_ge_55924056
#print axioms commonBase_johnsonHeavy_or_centeredMinorClique_55924056
#print axioms exactJohnsonAlignment_square_gt
#print axioms exactJohnsonMinimal_denominator_eq
#print axioms exactJohnsonMinimal_ratio_eq
#print axioms N_le_exactJohnsonMinimal_ratio
#print axioms tenRiderAlignment_johnson_ratio_eq
#print axioms projectiveMinorModel_pairwise_minor_ne_zero
#print axioms prizeField_supports_projectiveMinorClique_60118357
#print axioms johnsonLight_twoCoordinate_concentration_arithmetic
#print axioms subNine_twoCoordinate_concentration_arithmetic
#print axioms johnsonLight_twoCoordinate_floor_pred_satisfiable
#print axioms exists_two_coordinates_commonPetalLoad_ge_2912712
#print axioms commonBase_johnsonLight_exists_twoCoordinateMinorClique_2912712
#print axioms saturatedFullFiber_voteSet_card_eq_one
#print axioms saturatedFullFiber_witness_eq_aligned_union_vote
#print axioms saturatedFullFiber_votes_partition_complement
#print axioms vote_denominator_ne_zero_of_mem
#print axioms gamma_eq_voteRatio_of_mem
#print axioms saturatedFullFiber_existsUnique_rider_at_complement
#print axioms saturatedFullFiber_unique_rider_eq_voteRatio
#print axioms saturatedFullFiber_voteRatio_image_eq
#print axioms saturatedFullFiber_voteRatio_injOn
#print axioms commonBase_vote_equation
#print axioms commonBase_voteRatio_eq
#print axioms commonBase_gamma_eq_mismatchQuotient_of_vote
#print axioms same_nonbase_vote_forces_commonBase_directions_agree
#print axioms commonBase_sameRider_crossVote_card_le_k_sub_one
#print axioms commonBase_twoRider_matchingOverlap_card_le_k_sub_one
#print axioms commonBase_alignedAndSameRider_matching_card_le_k_sub_one
#print axioms commonBase_alignedUnionSameRider_inter_card_le_k_sub_one
#print axioms commonBase_sameFixedWitnessRider_directions_eq
#print axioms commonBase_pencilBase_eq_of_direction_eq
#print axioms commonBase_sameFixedWitnessRider_pencils_eq
#print axioms commonBase_distinctPencils_nonbaseRiders_disjoint
#print axioms commonBase_crossVote_directionDiff_identity
#print axioms commonBase_reverseCrossVote_directionDiff_identity
#print axioms commonBase_crossVote_directionDiff_square_identity
#print axioms commonBase_nonbase_vote_subset_baseAgree_compl
#print axioms commonBase_sharedRider_directions_eq_of_complement_packing
#print axioms commonBase_agreeSet_eq_aligned_union_baseVote
#print axioms commonBase_alignedSet_eq_baseAgree_inter_directionAgree
#print axioms fixedWitness_inter_subset_pencilDir_agreeSet
#print axioms fixedWitness_pencilDir_agreeSet_card_ge_111848108
#print axioms fiveFixedWitnesses_exists_pencilDir_agreeSet_card_ge_k
#print axioms exists_pinnedSecant_of_five_le_card
#print axioms saturatedFullFiber_commonBase_agreeSet_card_eq_threshold
#print axioms two_saturatedFullFiber_commonBase_aligned_inter_card_ge_threshold_sub_two
#print axioms two_saturatedFullFiber_commonBase_pencils_eq
#print axioms commonBase_riders_card_le_compl_agreeSet_add_one
#print axioms commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet
#print axioms commonBase_agreeSet_card_ge_threshold_of_baseWitness
#print axioms commonBase_threeRiders_lowerBand_base_mem
#print axioms commonBase_twoRiders_belowThreeFloor_base_mem
#print axioms commonBase_twoRider_minimal_agreeSet_card_eq_threshold
#print axioms commonBase_twoRider_minimal_nonbaseVotes_eq_complement
#print axioms commonBase_threeRider_minimal_agreeSet_card_eq_threshold
#print axioms rides_voteSet_card_ge_threshold_sub_aligned
#print axioms rides_alignedUnionVote_card_ge_threshold
#print axioms commonBase_threeRider_minimal_nonbaseVotes_partition_complement
#print axioms commonBase_threeRider_minimal_nonbaseVote_card_eq
#print axioms commonBase_agreeSet_card_ge_two_alignments_sub_k_pred
#print axioms commonBase_nearThreshold_riders_card_le_156587350
#print axioms three_commonBase_nearThreshold_partner_slots_le_N
#print axioms three_distinct_commonBase_nearThreshold_fibers_sum_le_N
#print axioms overBudget_fourPart_edgeFloor_twice_gt_vertices_mul_k_pred
#print axioms exists_degree_ge_k_of_overBudget_fourPart_edgeFloor
#print axioms degreeKStarCore_card
#print axioms degreeKStarCore_subset_thresholdUniverse
#print axioms degreeKStarCore_inter_eq
#print axioms degreeKStarCore_inter_card
#print axioms degreeKStarCore_injective
#print axioms direction_sub_eq_locator_mul_C_of_commonCore
#print axioms exists_direction_eq_base_add_locator_mul_C_of_commonCore
#print axioms three_affineLocator_agreements_force_parameter_collinear
#print axioms endpoint_crossProduct_eq_of_parameter_collinear
#print axioms lowCoreStar_charge_strictly_exceeds_215_capacity
#print axioms sum_petal_card_le_215_mul_complement
#print axioms lowCoreStar_charge_contradiction
#print axioms lowCoreStar_load_216_forced
#print axioms parabolaEndpoint_eval_zero
#print axioms parabolaEndpoint_three_not_source_collinear
#print axioms source_collinear_of_eval_collinear_on_k
#print axioms uniformTripleMoment_below_crossCoordinate_budget
#print axioms sum_choose_three_support_eq_sum_tripleContainment
#print axioms sum_choose_three_support_le_of_triple_cap
#print axioms richFamilyTripleCoords_card_le_k_pred_of_not_sourceCollinear
#print axioms tripleContainmentCoords_richFamilySupport
#print axioms richFamily_thirdMoment_le_of_no_sourceCollinear
#print axioms richFamily_exists_sourceCollinear_of_thirdMoment_gt
#print axioms uniformFullFamily_thirdMoment_below_sourceCollinear_capacity
#print axioms mem_pointsOn_anchorSecant_of_crossProduct_eq
#print axioms pointsOn_anchorSecant_eq_G_of_all_crossProducts
#print axioms richFamily_card_le_N_of_anchorCrossProducts
#print axioms richFamily_card_le_N_of_allTriplesSourceCollinear
#print axioms exists_nonSourceCollinearTriple_of_N_lt_richFamily_card
#print axioms richFamily_three_pairIntersections_one_ge_234881025
#print axioms exists_nonSourceCollinearTriple_with_largePairCore
#print axioms exists_richFamily_pair_inter_card_ge_327272221
#print axioms exists_nonSourceCollinear_third_of_anchorPair_of_overBudget
#print axioms exists_nonSourceCollinearTriple_with_interpolationPinnedAnchor
#print axioms highPairCore_interpolation_margin
#print axioms three_pointsOn_force_core_ge_352321537
#print axioms pointsOn_card_eq_two_of_core_lt_352321537
#print axioms four_pointsOn_force_core_ge_432479347
#print axioms pointsOn_card_le_three_of_core_lt_432479347
#print axioms relevantLine_core_ge_352321537_or_card_eq_two
#print axioms relevantLine_core_ge_432479347_or_card_le_three

end ArkLib.ProximityGap.Frontier.P1RateQuarterCrossPencilVoteReuse
