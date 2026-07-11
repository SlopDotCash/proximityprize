/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilCountCharge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilPairwiseBonferroni

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
set_option linter.style.longFile 3000
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Finset
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCrossPencilVoteReuse

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ProximityGap.SharedFreshPencil
open ProximityGap.Frontier.PencilPairwiseBonferroni

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
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
  rw [mul_inv_cancel₀ hne, mul_inv_cancel₀ hne', one_mul]

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

/-- **Transpose second-moment extraction.**  `N` petals of Johnson-light size force two
distinct coordinates jointly used by at least `2,912,712` petals. -/
theorem exists_two_coordinates_commonPetalLoad_ge_2912712
    [Fintype ι]
    (V : ι → Finset (Fin N))
    (hcard : Fintype.card ι = N)
    (hsize : ∀ j, 55924056 ≤ (V j).card) :
    ∃ x y : Fin N, x < y ∧
      2912712 ≤ (Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j).card := by
  classical
  let C : Fin N → Finset ι := fun x => Finset.univ.filter fun j => x ∈ V j
  let pairs : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun p => p.1 < p.2
  by_contra hnone
  push Not at hnone
  have hinter : ∀ x y : Fin N, x < y →
      (C x ∩ C y).card ≤ 2912711 := by
    intro x y hxy
    have hlt := hnone x y hxy
    have heq : C x ∩ C y = Finset.univ.filter fun j : ι => x ∈ V j ∧ y ∈ V j := by
      ext j
      simp [C]
    rw [heq]
    omega
  have hupp : (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) ≤
      N.choose 2 * 2912711 := by
    calc
      (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) ≤ ∑ _p ∈ pairs, 2912711 := by
        exact Finset.sum_le_sum fun p hp => hinter p.1 p.2 (by
          simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp)
      _ = pairs.card * 2912711 := by simp
      _ = N.choose 2 * 2912711 := by
        congr 1
        have hoff := filter_lt_offDiag_card (Finset.univ : Finset (Fin N))
        simpa only [pairs, Finset.card_univ, Fintype.card_fin] using hoff
  have hU : Finset.univ.biUnion C = (Finset.univ : Finset ι) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    have hpos : (V j).Nonempty := Finset.card_pos.mp (by
      have := hsize j
      omega)
    obtain ⟨x, hx⟩ := hpos
    rw [Finset.mem_biUnion]
    exact ⟨x, Finset.mem_univ _, by simp [C, hx]⟩
  have hid := sum_inter_eq_sum_choose_two N C
  change (∑ p ∈ pairs, (C p.1 ∩ C p.2).card) = _ at hid
  rw [hU] at hid
  have hlow : N * ((55924056).choose 2) ≤
      ∑ j : ι, (mult N C j).choose 2 := by
    calc
      N * ((55924056).choose 2) = ∑ _j : ι, (55924056).choose 2 := by
        simp [hcard]
      _ ≤ ∑ j : ι, (mult N C j).choose 2 := by
        apply Finset.sum_le_sum
        intro j _hj
        apply Nat.choose_le_choose 2
        have heq : mult N C j = (V j).card := by
          unfold mult
          congr 1
          ext x
          simp [C]
        rw [heq]
        exact hsize j
  rw [← hid] at hlow
  exact (Nat.not_lt_of_ge (hlow.trans hupp))
    johnsonLight_twoCoordinate_concentration_arithmetic

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
    rw [hpetal j, hpetal j, Finset.mem_inter, Finset.mem_inter]
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
    rw [hA, hR]
    have hT := predecessorThreshold_eq
    have hN : N = 1073741824 := by norm_num [N]
    omega
  have hrest : R.erase gamma |>.card ≤
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
  apply Finset.Subset.antisymm hsub
  apply Finset.card_le_card_iff.mp
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
  apply Finset.Subset.antisymm hsub
  apply Finset.card_le_card_iff.mp
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    hA, ← card_biUnion_votes u0 u1 w0 w1 R]
  have hvote : ∀ gamma ∈ R, (voteSet u0 u1 w0 w1 gamma).card = 1 :=
    saturatedFullFiber_voteSet_card_eq_one dom u0 u1 w0 w1 R Sf
      hw0 hw1 hrides hA hR
  rw [Finset.sum_congr rfl hvote]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hR]
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

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
  rw [voteRatio, div_eq_iff hden]
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
  exact Finset.disjoint_left.mp (voteSet_disjoint u0 u1 w0 w1 hne)
    hxvote hgamma'.2

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
  exact Finset.card_le_one.mp hcard.le hxvote hyvoteraw

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
      (pencilDir gamma0 gamma1 p0 p1 x - u1 x) = 0 := by
    rw [hxB.2]
    ring
  have hdir : pencilDir gamma0 gamma1 p0 p1 x = u1 x := by
    rcases mul_eq_zero.mp hmul with hg | hd
    · exact absurd (sub_eq_zero.mp hg) hgamma
    · exact sub_eq_zero.mp hd
  exact (mem_voteSet_iff u0 u1 _ _ gamma x).mp hx |>.1
    ((mem_alignedSet_iff u0 u1 _ _ x).mpr ⟨by
      have hrepro := congrFun (pencil_reproduces_first gamma0 gamma1 p0 p1) x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrepro
      rw [hdir] at hrepro
      linear_combination hxB.2 - hrepro, hdir⟩)

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
    dsimp [V1, V2, C] at hV1 hV2 hpack ⊢
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
    linear_combination hbase - hrepro

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
  have hV1C := commonBase_nonbase_vote_subset_baseAgree_compl
    hgamma p0 p1 u0 u1
  have hV2C := commonBase_nonbase_vote_subset_baseAgree_compl
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
    rw [B, commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hA2sub : A2 ⊆ B := by
    rw [B, commonBase_agreeSet_eq_aligned_union_baseVote]
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
    rw [← card_biUnion_votes u0 u1 _ _ R', hC]
    exact hlower
  apply Finset.Subset.antisymm hsub
  exact Finset.card_le_card_iff.mp hcardLower

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
      480946858 = R'.card * 240473429 := by rw [hR']; norm_num
      _ = ∑ _gamma ∈ R', 240473429 := by simp
      _ ≤ ∑ gamma ∈ R', (V gamma).card :=
        Finset.sum_le_sum fun gamma hgamma => hper gamma hgamma
  have hcardLower : C.card ≤ (R'.biUnion V).card := by
    rw [← card_biUnion_votes u0 u1 _ _ R']
    rw [hC]
    have hN : N = 1073741824 := by norm_num [N]
    have hT := predecessorThreshold_eq
    omega
  apply Finset.Subset.antisymm hsub
  exact Finset.card_le_card_iff.mp hcardLower

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
    change (R.erase gamma0).biUnion (fun gamma => voteSet u0 u1
        (pencilBase gamma0 gamma1 p0 p1) (pencilDir gamma0 gamma1 p0 p1) gamma) |>.card = _
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
  have hrestCard : (R'.erase gamma).card = 1 := by simp [hgamma, hR']
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
    rw [B, commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hA2sub : A2 ⊆ B := by
    rw [B, commonBase_agreeSet_eq_aligned_union_baseVote]
    exact Finset.subset_union_left
  have hunion : (A1 ∪ A2).card ≤ B.card :=
    Finset.card_le_card (Finset.union_subset hA1sub hA2sub)
  have hinter : (A1 ∩ A2).card ≤ k - 1 := alignedSet_inter_card_lt_k dom u0 u1
    (pencilBase_mem _ hp0 hp1) (pencilDir_mem _ hp0 hp1)
    (pencilBase_mem _ hp0 hp2) (pencilDir_mem _ hp0 hp2) hne
  have hbook := Finset.card_union_add_card_inter A1 A2
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
#print axioms commonBase_crossVote_directionDiff_identity
#print axioms commonBase_reverseCrossVote_directionDiff_identity
#print axioms commonBase_crossVote_directionDiff_square_identity
#print axioms commonBase_nonbase_vote_subset_baseAgree_compl
#print axioms commonBase_sharedRider_directions_eq_of_complement_packing
#print axioms commonBase_agreeSet_eq_aligned_union_baseVote
#print axioms commonBase_alignedSet_eq_baseAgree_inter_directionAgree
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

end ArkLib.ProximityGap.Frontier.P1RateQuarterCrossPencilVoteReuse
