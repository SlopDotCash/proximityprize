/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthSevenInjectiveVarianceEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedSectorNewtonAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R348PeriodSquareRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationDoublingLevelSet
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationDoublingMassNoCompose
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NegTransversalCharFree
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumNegSymmConcentration
import Mathlib.Algebra.Order.Chebyshev

/-!
# Centered six-transition contraction: exact consumer and genuine subgroup obstruction

For `a_r(y)` the number of `r`-subsets of `G` with sum `y`, define the denominator-free
centered energy

`V_r = sum_y (q*a_r(y) - C(n,r))^2`

and its source-normalized version `Z_r = V_r / C(n,r)^2`.  An honest one-step flattening
statement with numerator `c_r` is

`n * Z_(r+1) <= c_r * Z_r`.

This file proves the exact six-step consumer.  If the six inequalities for `r=1,...,6` hold,
their nonnegative numerators have product at most `126871`, and the elementary singleton start
obeys `n*Z_1 <= q^2`, then

`(7!)^2 * V_7 <= 126871 * q^2 * n^7`,

which is precisely the remaining injective subset-variance target.  Thus this is a genuinely
stronger, local production socket rather than a restatement of the final estimate.

The strongest unconditional transition retained here is the exact deleted-diagonal Newton law

`D7 = p1*D6 - 6*p2*D5 + 30*p3*D4 - 120*p4*D3
        + 360*p5*D2 - 720*p6*D1 + 720*p7`.

For subgroup phases `p_j=eta_(jb)`.  A seven-term Cauchy bound gives the corresponding centered
nonzero-frequency L2 envelope.  This proves why raw one-colour convolution does not recurse on
`Z_r`: the deleted diagonals couple every lower depth to the independent colours `2b,...,7b`.

There is also a sharp obstruction to making the socket field-uniform.  In `ZMod 17`, the
quadratic-residue subgroup

`H8 = {1,2,4,8,9,13,15,16}`

has order eight and sum zero.  Complementation identifies its one-subset and seven-subset sum
profiles, so `Z_7=Z_1>0`.  Consequently any six transition numerators valid for this genuine
subgroup satisfy

`8^6 <= c_1*...*c_6`.

Since `8^6=262144>126871`, no universal `product <= 126871` contraction theorem is true, even
for actual multiplicative subgroups.  The missing theorem must use production-specific largeness
and the arithmetic joint law of the independent dilation colours `2G,...,7G`; multiplicative
invariance and the `1-G` collapse alone do not suffice.

At production, the first transition is excluded as the distinguished one-unit Wick defect.
Negation closure creates `n/2` distinct two-subsets `{x,-x}` in the zero-sum fiber.  Their forced
off-diagonal collisions imply

`n*Z_2/Z_1 > 3 + 2^-29`.

Thus even Wick `3` is a strict lower bound, and the relaxed selected cap
`2*(501/500)=2.004` is impossible.  The antipodal lower envelope is nevertheless below the
ordinary robust cap `3*(501/500)=3.006`; this only says the forced obstruction fits that margin,
not that the complete first transition has the required upper bound.  The one-unit defect must be
sought at one of transitions two through six.

Finally, the in-tree doubling-level-set theorem supplies one bit on one same-sign cross-mass
slice, while the inverse-neighbour theorem proves that the obvious second slice is identical.
Even granting six independent halvings would be between `2^157` and `2^158` short of the exact
production contraction.  Hence none of the required global `>27` L2 bits per transition is
currently obtained by that result.

Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2048

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKCenteredTrajectoryContraction

open ArkLib.ProximityGap.Round4NewtonVietaUpper
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.CodingTheory.Round7Concentration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The actual subset trajectory -/

/-- Denominator-free centered energy of the `r`-subset sum histogram. -/
noncomputable def subsetDeviationEnergy (G : Finset F) (r : Nat) : Real :=
  ∑ y : F,
    ((Fintype.card F : Real) * (subsetSumCount G r y : Real) -
      (G.card.choose r : Real)) ^ 2

/-- Centered energy normalized by the square of the number of `r`-subsets.  This is `q` times
the usual chi-square divergence of the `r`-subset sum law from uniformity. -/
noncomputable def normalizedSubsetDeviation (G : Finset F) (r : Nat) : Real :=
  subsetDeviationEnergy G r / (G.card.choose r : Real) ^ 2

/-- Every normalized subset discrepancy is nonnegative. -/
theorem normalizedSubsetDeviation_nonneg (G : Finset F) (r : Nat) :
    0 <= normalizedSubsetDeviation G r := by
  unfold normalizedSubsetDeviation subsetDeviationEnergy
  positivity

/-- A singleton subset has sum `y` exactly when `y` belongs to the ground set. -/
theorem subsetSumCount_one (G : Finset F) (y : F) :
    subsetSumCount G 1 y = if y ∈ G then 1 else 0 := by
  classical
  unfold subsetSumCount
  rw [Finset.card_filter, Finset.powersetCard_one, Finset.sum_map]
  simp

/-- Exact denominator-free singleton energy. -/
theorem subsetDeviationEnergy_one (G : Finset F) :
    subsetDeviationEnergy G 1 =
      (Fintype.card F : Real) * G.card *
        ((Fintype.card F : Real) - G.card) := by
  classical
  let q : Real := Fintype.card F
  let n : Real := G.card
  unfold subsetDeviationEnergy
  rw [Nat.choose_one_right]
  simp_rw [subsetSumCount_one]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  change (∑ y : F, (q * (if y ∈ G then (1 : Real) else 0) - n) ^ 2) =
    q * n * (q - n)
  have hpoint : ∀ y : F,
      (q * (if y ∈ G then (1 : Real) else 0) - n) ^ 2 =
        q ^ 2 * (if y ∈ G then (1 : Real) else 0) -
          2 * q * n * (if y ∈ G then (1 : Real) else 0) + n ^ 2 := by
    intro y
    by_cases hy : y ∈ G
    · simp [hy]
      ring
    · simp [hy]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [q, n]
  ring

/-- Exact normalized singleton profile. -/
theorem normalizedSubsetDeviation_one (G : Finset F) (hG : 0 < G.card) :
    normalizedSubsetDeviation G 1 =
      (Fintype.card F : Real) *
        ((Fintype.card F : Real) - G.card) / G.card := by
  unfold normalizedSubsetDeviation
  rw [subsetDeviationEnergy_one, Nat.choose_one_right]
  have hn : (G.card : Real) ≠ 0 := by exact_mod_cast hG.ne'
  field_simp [hn]

/-- The singleton start needed by the six-step consumer is unconditional for every nonempty
ground set. -/
theorem normalizedSubsetDeviation_one_start (G : Finset F) (hG : 0 < G.card) :
    (G.card : Real) * normalizedSubsetDeviation G 1 <=
      (Fintype.card F : Real) ^ 2 := by
  rw [normalizedSubsetDeviation_one G hG]
  have hn : (0 : Real) < G.card := by exact_mod_cast hG
  have hle : (G.card : Real) <= Fintype.card F := by
    exact_mod_cast Finset.card_le_univ G
  have hq : (0 : Real) <= Fintype.card F := by positivity
  field_simp [hn.ne']
  nlinarith

/-! ## The unconditional deleted-diagonal transition -/

/-- Ordered-injective transform at arbitrary depth. -/
noncomputable def orderedInjectiveTransform {I : Type*} [Fintype I]
    (w : I → Complex) (r : Nat) : Complex :=
  (Nat.factorial r : Complex) * (Finset.univ.val.map w).esymm r

/-- The seven deleted-diagonal transition terms.  Unlike raw convolution, the transition is not
one multiplier times the preceding profile: all lower injective depths and all dilation colours
occur. -/
noncomputable def deletedDiagonalTerm {I : Type*} [Fintype I]
    (w : I → Complex) : Fin 7 → Complex
  | 0 => phasePowerSum w 1 * orderedInjectiveTransform w 6
  | 1 => -6 * phasePowerSum w 2 * orderedInjectiveTransform w 5
  | 2 => 30 * phasePowerSum w 3 * orderedInjectiveTransform w 4
  | 3 => -120 * phasePowerSum w 4 * orderedInjectiveTransform w 3
  | 4 => 360 * phasePowerSum w 5 * orderedInjectiveTransform w 2
  | 5 => -720 * phasePowerSum w 6 * orderedInjectiveTransform w 1
  | 6 => 720 * phasePowerSum w 7

/-- **Exact injective Newton transition at depth seven.** -/
theorem injectiveSevenTransform_eq_sum_deletedDiagonalTerm
    {I : Type*} [Fintype I] [DecidableEq I] (w : I → Complex) :
    injectiveSevenTransform w = ∑ j : Fin 7, deletedDiagonalTerm w j := by
  classical
  have h7 := ArkLib.ProximityGap.MomentCollisionRigidity.multiset_newton w 7
  have ha7 : (Finset.antidiagonal 7).filter (fun a => a.1 < 7) =
      {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} := by
    decide
  rw [ha7] at h7
  have he0 : (Finset.univ.val.map w).esymm 0 = (1 : Complex) := by
    simp [Multiset.esymm]
  norm_num [Finset.sum_insert, ArkLib.ProximityGap.MomentCollisionRigidity.psumMs,
    phasePowerSum] at h7
  rw [he0] at h7
  norm_num at h7
  have huniv : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  unfold injectiveSevenTransform
  rw [huniv]
  simp [deletedDiagonalTerm, orderedInjectiveTransform, phasePowerSum, Nat.factorial]
  ring_nf at h7 ⊢
  linear_combination 720 * h7

/-- Seven-term Hilbert-space Cauchy bound, stated for complex scalars. -/
theorem norm_sum_fin7_sq_le (z : Fin 7 → Complex) :
    ‖∑ j, z j‖ ^ 2 <= 7 * ∑ j, ‖z j‖ ^ 2 := by
  have htri : ‖∑ j, z j‖ <= ∑ j, ‖z j‖ := norm_sum_le _ _
  calc
    ‖∑ j, z j‖ ^ 2 <= (∑ j, ‖z j‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ <= ((Finset.univ : Finset (Fin 7)).card : Real) * ∑ j, ‖z j‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = 7 * ∑ j, ‖z j‖ ^ 2 := by norm_num

/-- **Strongest unconditional scalar L2 recursion supplied by Newton.**  It retains all seven
colours and lower depths; collapsing its right-hand side to `c/n` times a single previous energy
is exactly the new arithmetic input still missing. -/
theorem injectiveSevenTransform_norm_sq_le_deletedDiagonalEnergy
    {I : Type*} [Fintype I] [DecidableEq I] (w : I → Complex) :
    ‖injectiveSevenTransform w‖ ^ 2 <=
      7 * ∑ j : Fin 7, ‖deletedDiagonalTerm w j‖ ^ 2 := by
  rw [injectiveSevenTransform_eq_sum_deletedDiagonalTerm]
  exact norm_sum_fin7_sq_le _

/-- Actual subgroup phase family at frequency `b`. -/
noncomputable def subgroupPhase (psi : AddChar F Complex) (G : Finset F) (b : F) :
    {x // x ∈ G} → Complex :=
  fun x => psi (b * x.1)

/-- The `j`-colour in the Newton transition is exactly the period at the independent dilation
`j*b`. -/
theorem phasePowerSum_subgroupPhase (psi : AddChar F Complex)
    (G : Finset F) (b : F) (j : Nat) :
    phasePowerSum (subgroupPhase psi G b) j = eta psi G ((j : F) * b) := by
  classical
  unfold phasePowerSum subgroupPhase eta
  rw [Finset.univ_eq_attach]
  calc
    (∑ i ∈ G.attach, psi (b * (i : F)) ^ j) =
        ∑ x ∈ G, psi (b * x) ^ j :=
      Finset.sum_attach G (fun x : F => psi (b * x) ^ j)
    _ = ∑ x ∈ G, psi ((j : F) * b * x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← AddChar.map_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul (R := F)]
      congr 1
      simp only [smul_eq_mul]
      ring

/-- The exact deleted-diagonal transition on a genuine subgroup phase profile. -/
theorem subgroup_injectiveSeven_exact_colored_transition
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    injectiveSevenTransform (subgroupPhase psi G b) =
      eta psi G b * orderedInjectiveTransform (subgroupPhase psi G b) 6
      - 6 * eta psi G ((2 : F) * b) *
          orderedInjectiveTransform (subgroupPhase psi G b) 5
      + 30 * eta psi G ((3 : F) * b) *
          orderedInjectiveTransform (subgroupPhase psi G b) 4
      - 120 * eta psi G ((4 : F) * b) *
          orderedInjectiveTransform (subgroupPhase psi G b) 3
      + 360 * eta psi G ((5 : F) * b) *
          orderedInjectiveTransform (subgroupPhase psi G b) 2
      - 720 * eta psi G ((6 : F) * b) *
          orderedInjectiveTransform (subgroupPhase psi G b) 1
      + 720 * eta psi G ((7 : F) * b) := by
  rw [injectiveSevenTransform_eq_sum_deletedDiagonalTerm]
  have huniv : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [huniv]
  simp [deletedDiagonalTerm, phasePowerSum_subgroupPhase, mul_comm]
  ring

/-- Summing the genuine pointwise recursion over all nonzero frequencies gives the honest
centered L2 envelope. -/
theorem subgroup_nonzero_injectiveSeven_energy_le_colored_transition
    (psi : AddChar F Complex) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖injectiveSevenTransform (subgroupPhase psi G b)‖ ^ 2) <=
      7 * ∑ b ∈ Finset.univ.erase (0 : F),
        ∑ j : Fin 7, ‖deletedDiagonalTerm (subgroupPhase psi G b) j‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _hb =>
    injectiveSevenTransform_norm_sq_le_deletedDiagonalEnergy (subgroupPhase psi G b)

/-! ## The first Wick step: antipodal pairs force the opposite inequality -/

/-- Collision count of the `r`-subset sum map. -/
noncomputable def subsetCollision (G : Finset F) (r : Nat) : Nat :=
  ∑ y : F, (subsetSumCount G r y) ^ 2

/-- Exact physical-space expansion of the denominator-free centered energy. -/
theorem subsetDeviationEnergy_eq_collision (G : Finset F) (r : Nat) :
    subsetDeviationEnergy G r =
      (Fintype.card F : Real) *
        ((Fintype.card F : Real) * subsetCollision G r -
          (G.card.choose r : Real) ^ 2) := by
  let q : Real := Fintype.card F
  let N : Real := G.card.choose r
  have hsum : (∑ y : F, (subsetSumCount G r y : Real)) = N := by
    dsimp only [N]
    have hsumNat : ∑ y : F, subsetSumCount G r y = G.card.choose r :=
      sum_subsetSumCount_eq_choose (F := F) (G := G) (n := G.card) rfl r
    exact_mod_cast hsumNat
  have hsq : (∑ y : F, (subsetSumCount G r y : Real) ^ 2) =
      (subsetCollision G r : Real) := by
    unfold subsetCollision
    push_cast
    rfl
  unfold subsetDeviationEnergy
  change (∑ y : F, (q * (subsetSumCount G r y : Real) - N) ^ 2) = _
  calc
    (∑ y : F, (q * (subsetSumCount G r y : Real) - N) ^ 2) =
        q ^ 2 * ∑ y : F, (subsetSumCount G r y : Real) ^ 2 -
          2 * q * N * ∑ y : F, (subsetSumCount G r y : Real) +
            (Fintype.card F : Real) * N ^ 2 := by
      have hconst : (Fintype.card F : Real) * N ^ 2 = ∑ _y : F, N ^ 2 := by simp
      rw [Finset.mul_sum, Finset.mul_sum, hconst,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = q * (q * subsetCollision G r - N ^ 2) := by
      rw [hsum, hsq]
      dsimp only [q]
      ring

/-- The collision count contains all diagonal pairs plus the off-diagonal repetitions inside any
one distinguished fiber. -/
theorem subsetCollision_ge_choose_add_fiber_offdiag
    (G : Finset F) (r : Nat) (y0 : F) :
    G.card.choose r + subsetSumCount G r y0 * (subsetSumCount G r y0 - 1) <=
      subsetCollision G r := by
  have hsum := sum_subsetSumCount_eq_choose (G := G) rfl r
  unfold subsetCollision
  have hpoint : ∀ y : F,
      subsetSumCount G r y ^ 2 = subsetSumCount G r y +
        subsetSumCount G r y * (subsetSumCount G r y - 1) := by
    intro y
    by_cases hzero : subsetSumCount G r y = 0
    · simp [hzero]
    · have hone : 1 <= subsetSumCount G r y := Nat.one_le_iff_ne_zero.mpr hzero
      calc
        subsetSumCount G r y ^ 2 =
            subsetSumCount G r y * subsetSumCount G r y := by rw [pow_two]
        _ = subsetSumCount G r y *
            (1 + (subsetSumCount G r y - 1)) := by
          congr 1
          omega
        _ = subsetSumCount G r y +
            subsetSumCount G r y * (subsetSumCount G r y - 1) := by
          rw [mul_add, mul_one]
  simp_rw [hpoint, Finset.sum_add_distrib, hsum]
  exact Nat.add_le_add_left
    (Finset.single_le_sum
      (fun y _ => Nat.zero_le (subsetSumCount G r y * (subsetSumCount G r y - 1)))
      (Finset.mem_univ y0)) _

/-- A fixed-point-free negation-closed subgroup admits a half-transversal.  The arbitrary finite
linear order is used only to choose one representative from each pair. -/
theorem exists_negationHalf_of_mulSubgroup
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0) :
    ∃ H : Finset F,
      Disjoint H (H.image fun x => -x) ∧ (0 : F) ∉ H ∧
        negClosure H = G ∧ G.card = 2 * H.card := by
  classical
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    simpa using hG.mul_mem (-1) hnegOne x hx
  have hG0 : (0 : F) ∉ G := by
    intro hz
    obtain ⟨z, _hz, hzero⟩ := hG.exists_inv 0 hz
    exact zero_ne_one (by simpa only [zero_mul] using hzero)
  obtain ⟨H, hsub, hdisj, hcover, hcard⟩ :=
    NegTransversalCharFree.exists_neg_transversal' G h2 hG0 hneg
  refine ⟨H, hdisj, fun hz => hG0 (hsub hz), ?_, hcard.symm⟩
  exact hcover

/-- Every such subgroup has at least `|G|/2` two-subsets summing to zero. -/
theorem subgroup_half_le_twoSubset_zeroFiber
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0) :
    G.card / 2 <= subsetSumCount G 2 0 := by
  obtain ⟨H, hdisj, hH0, hclosure, hcard⟩ :=
    exists_negationHalf_of_mulSubgroup G hG hnegOne h2
  have h := subsetSumCount_zero_ge_choose_half h2 hdisj hH0 1
  rw [hclosure] at h
  have hhalf : G.card / 2 = H.card := by omega
  rw [hhalf]
  simpa [Round4NewtonVietaUpper.subsetSumCount] using h

/-- Antipodal concentration forces a concrete collision lower bound at depth two. -/
theorem subgroup_twoSubset_collision_antipodal_lower
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0) :
    G.card.choose 2 + (G.card / 2) * (G.card / 2 - 1) <= subsetCollision G 2 := by
  have hfiber := subgroup_half_le_twoSubset_zeroFiber G hG hnegOne h2
  refine le_trans (Nat.add_le_add_left
    (Nat.mul_le_mul hfiber (Nat.sub_le_sub_right hfiber 1)) _) ?_
  exact subsetCollision_ge_choose_add_fiber_offdiag G 2 0

/-- A transition with numerator `c`: after normalizing by the source size, adjoining one new
distinct element contracts centered L2 by at least the factor `n/c`. -/
def TransitionBound (G : Finset F) (r : Nat) (c : Real) : Prop :=
  (G.card : Real) * normalizedSubsetDeviation G (r + 1) <=
    c * normalizedSubsetDeviation G r

/-- The six explicit transition bounds from one-subsets through seven-subsets. -/
def SixTransitionBounds (G : Finset F)
    (c1 c2 c3 c4 c5 c6 : Real) : Prop :=
  TransitionBound G 1 c1 ∧ TransitionBound G 2 c2 ∧
    TransitionBound G 3 c3 ∧ TransitionBound G 4 c4 ∧
    TransitionBound G 5 c5 ∧ TransitionBound G 6 c6

/-- Six nonnegative local transition bounds multiply without loss. -/
theorem sixTransitionBounds_chain (G : Finset F)
    {c1 c2 c3 c4 c5 c6 : Real}
    (hc : SixTransitionBounds G c1 c2 c3 c4 c5 c6)
    (_hc1 : 0 <= c1) (hc2 : 0 <= c2) (hc3 : 0 <= c3)
    (hc4 : 0 <= c4) (hc5 : 0 <= c5) (hc6 : 0 <= c6) :
    (G.card : Real) ^ 6 * normalizedSubsetDeviation G 7 <=
      (c1 * c2 * c3 * c4 * c5 * c6) * normalizedSubsetDeviation G 1 := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩
  unfold TransitionBound at h1 h2 h3 h4 h5 h6
  have hn : (0 : Real) <= G.card := by positivity
  calc
    (G.card : Real) ^ 6 * normalizedSubsetDeviation G 7 =
        (G.card : Real) ^ 5 *
          ((G.card : Real) * normalizedSubsetDeviation G 7) := by ring
    _ <= (G.card : Real) ^ 5 *
          (c6 * normalizedSubsetDeviation G 6) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = c6 * (G.card : Real) ^ 4 *
          ((G.card : Real) * normalizedSubsetDeviation G 6) := by ring
    _ <= c6 * (G.card : Real) ^ 4 *
          (c5 * normalizedSubsetDeviation G 5) :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hc6 (by positivity))
    _ = c6 * c5 * (G.card : Real) ^ 3 *
          ((G.card : Real) * normalizedSubsetDeviation G 5) := by ring
    _ <= c6 * c5 * (G.card : Real) ^ 3 *
          (c4 * normalizedSubsetDeviation G 4) :=
      mul_le_mul_of_nonneg_left h4
        (mul_nonneg (mul_nonneg hc6 hc5) (by positivity))
    _ = c6 * c5 * c4 * (G.card : Real) ^ 2 *
          ((G.card : Real) * normalizedSubsetDeviation G 4) := by ring
    _ <= c6 * c5 * c4 * (G.card : Real) ^ 2 *
          (c3 * normalizedSubsetDeviation G 3) :=
      mul_le_mul_of_nonneg_left h3
        (mul_nonneg (mul_nonneg (mul_nonneg hc6 hc5) hc4) (by positivity))
    _ = c6 * c5 * c4 * c3 * (G.card : Real) *
          ((G.card : Real) * normalizedSubsetDeviation G 3) := by ring
    _ <= c6 * c5 * c4 * c3 * (G.card : Real) *
          (c2 * normalizedSubsetDeviation G 2) :=
      mul_le_mul_of_nonneg_left h2
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc6 hc5) hc4) hc3) hn)
    _ = c6 * c5 * c4 * c3 * c2 *
          ((G.card : Real) * normalizedSubsetDeviation G 2) := by ring
    _ <= c6 * c5 * c4 * c3 * c2 *
          (c1 * normalizedSubsetDeviation G 1) :=
      mul_le_mul_of_nonneg_left h1
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc6 hc5) hc4) hc3) hc2)
    _ = (c1 * c2 * c3 * c4 * c5 * c6) *
          normalizedSubsetDeviation G 1 := by ring

/-! ## Exact coefficient-126871 consumer -/

/-- A production-useful certificate: six genuine local bounds, nonnegative numerators, their
exact product budget, and the elementary depth-one start scale. -/
def ProductionTrajectoryCertificate (G : Finset F)
    (c1 c2 c3 c4 c5 c6 : Real) : Prop :=
  SixTransitionBounds G c1 c2 c3 c4 c5 c6 ∧
    0 <= c1 ∧ 0 <= c2 ∧ 0 <= c3 ∧ 0 <= c4 ∧ 0 <= c5 ∧ 0 <= c6 ∧
    c1 * c2 * c3 * c4 * c5 * c6 <= 126871

/-- **Exact consumer.**  A six-transition certificate proves the remaining depth-seven centered
subset-variance inequality with coefficient `126871`. -/
theorem productionTrajectoryCertificate_closes_injective_target
    (G : Finset F) (hcard : 7 <= G.card)
    {c1 c2 c3 c4 c5 c6 : Real}
    (hcert : ProductionTrajectoryCertificate G c1 c2 c3 c4 c5 c6) :
    (Nat.factorial 7 : Real) ^ 2 * subsetDeviationEnergy G 7 <=
      126871 * (Fintype.card F : Real) ^ 2 * (G.card : Real) ^ 7 := by
  rcases hcert with ⟨hsteps, hc1, hc2, hc3, hc4, hc5, hc6, hprod⟩
  have hchain := sixTransitionBounds_chain G hsteps hc1 hc2 hc3 hc4 hc5 hc6
  have hnpos : (0 : Real) < G.card := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hcard)
  have hz1 := normalizedSubsetDeviation_nonneg G 1
  have hz7 := normalizedSubsetDeviation_nonneg G 7
  have hprod_nonneg : 0 <= c1 * c2 * c3 * c4 * c5 * c6 := by positivity
  have hstart := normalizedSubsetDeviation_one_start G
    (lt_of_lt_of_le (by norm_num) hcard)
  have hseven :
      (G.card : Real) ^ 7 * normalizedSubsetDeviation G 7 <=
        126871 * (Fintype.card F : Real) ^ 2 := by
    calc
      (G.card : Real) ^ 7 * normalizedSubsetDeviation G 7 =
          (G.card : Real) *
            ((G.card : Real) ^ 6 * normalizedSubsetDeviation G 7) := by ring
      _ <= (G.card : Real) *
            ((c1 * c2 * c3 * c4 * c5 * c6) *
              normalizedSubsetDeviation G 1) :=
        mul_le_mul_of_nonneg_left hchain hnpos.le
      _ = (c1 * c2 * c3 * c4 * c5 * c6) *
            ((G.card : Real) * normalizedSubsetDeviation G 1) := by ring
      _ <= (c1 * c2 * c3 * c4 * c5 * c6) *
            (Fintype.card F : Real) ^ 2 :=
        mul_le_mul_of_nonneg_left hstart hprod_nonneg
      _ <= 126871 * (Fintype.card F : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
  have hdescNat : G.card.descFactorial 7 <= G.card ^ 7 :=
    Nat.descFactorial_le_pow G.card 7
  have hdesc : (G.card.descFactorial 7 : Real) ^ 2 <= (G.card : Real) ^ 14 := by
    norm_cast
    calc
      G.card.descFactorial 7 ^ 2 <= (G.card ^ 7) ^ 2 :=
        Nat.pow_le_pow_left hdescNat 2
      _ = G.card ^ 14 := by ring
  have hnorm : (G.card.choose 7 : Real) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hcard
  have hrewrite :
      (Nat.factorial 7 : Real) ^ 2 * subsetDeviationEnergy G 7 =
        (G.card.descFactorial 7 : Real) ^ 2 * normalizedSubsetDeviation G 7 := by
    unfold normalizedSubsetDeviation
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp [hnorm]
  rw [hrewrite]
  calc
    (G.card.descFactorial 7 : Real) ^ 2 * normalizedSubsetDeviation G 7 <=
        (G.card : Real) ^ 14 * normalizedSubsetDeviation G 7 :=
      mul_le_mul_of_nonneg_right hdesc hz7
    _ = (G.card : Real) ^ 7 *
          ((G.card : Real) ^ 7 * normalizedSubsetDeviation G 7) := by ring
    _ <= (G.card : Real) ^ 7 *
          (126871 * (Fintype.card F : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hseven (by positivity)
    _ = 126871 * (Fintype.card F : Real) ^ 2 * (G.card : Real) ^ 7 := by ring

/-! ## Complement symmetry and the order-eight obstruction -/

/-- Complementation preserves the full centered-energy profile after replacing depth `r` by
`n-r`. -/
theorem subsetDeviationEnergy_compl
    (G : Finset F) (hGsum : ∑ x ∈ G, x = 0) {n r : Nat}
    (hcard : G.card = n) (hr : r <= n) :
    subsetDeviationEnergy G r = subsetDeviationEnergy G (n - r) := by
  classical
  unfold subsetDeviationEnergy
  have hchoose : G.card.choose r = G.card.choose (n - r) := by
    rw [hcard, Nat.choose_symm hr]
  rw [hchoose]
  apply Fintype.sum_equiv (Equiv.neg F)
  intro y
  congr 1
  rw [subsetSumCount_compl hGsum hcard r hr]
  simp

/-- The normalized profile has the same complementation symmetry. -/
theorem normalizedSubsetDeviation_compl
    (G : Finset F) (hGsum : ∑ x ∈ G, x = 0) {n r : Nat}
    (hcard : G.card = n) (hr : r <= n) :
    normalizedSubsetDeviation G r = normalizedSubsetDeviation G (n - r) := by
  unfold normalizedSubsetDeviation
  rw [subsetDeviationEnergy_compl G hGsum hcard hr]
  have hchoose : G.card.choose r = G.card.choose (n - r) := by
    rw [hcard, Nat.choose_symm hr]
  rw [hchoose]

/-- The quadratic-residue subgroup of order eight in `ZMod 17`. -/
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

def H8 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

theorem H8_isMulSubgroup : IsMulSubgroup H8 :=
  ⟨by decide, by decide, by decide⟩

theorem H8_card : H8.card = 8 := by decide

theorem H8_sum_zero : ∑ x ∈ H8, x = 0 := by decide

/-- The endpoint profiles agree exactly: a seven-subset is the complement of one element. -/
theorem H8_endpoint_profile_eq :
    normalizedSubsetDeviation H8 7 = normalizedSubsetDeviation H8 1 := by
  have h := normalizedSubsetDeviation_compl H8 H8_sum_zero H8_card (r := 1) (by norm_num)
  norm_num at h ⊢
  exact h.symm

/-- The endpoint profile is nonzero. -/
theorem H8_depthOne_profile_pos : 0 < normalizedSubsetDeviation H8 1 := by
  have hzero : subsetSumCount H8 1 0 = 0 := by
    rw [subsetSumCount_one]
    rw [if_neg (by decide : (0 : ZMod 17) ∉ H8)]
  unfold normalizedSubsetDeviation subsetDeviationEnergy
  rw [H8_card]
  norm_num only [Nat.choose, Nat.cast_ofNat]
  apply div_pos
  · have hterm :
        0 < ((Fintype.card (ZMod 17) : Real) *
          (subsetSumCount H8 1 0 : Real) - 8) ^ 2 := by
        rw [hzero]
        norm_num
    exact hterm.trans_le
      (Finset.single_le_sum (fun y _ => sq_nonneg
        ((Fintype.card (ZMod 17) : Real) *
          (subsetSumCount H8 1 y : Real) - 8)) (Finset.mem_univ 0))
  · norm_num

/-- **Genuine subgroup obstruction.**  Every six-step contraction valid on `H8` has aggregate
numerator at least `8^6`. -/
theorem H8_sixTransition_product_ge_eight_pow_six
    {c1 c2 c3 c4 c5 c6 : Real}
    (hc : SixTransitionBounds H8 c1 c2 c3 c4 c5 c6)
    (hc1 : 0 <= c1) (hc2 : 0 <= c2) (hc3 : 0 <= c3)
    (hc4 : 0 <= c4) (hc5 : 0 <= c5) (hc6 : 0 <= c6) :
    (8 : Real) ^ 6 <= c1 * c2 * c3 * c4 * c5 * c6 := by
  have hchain := sixTransitionBounds_chain H8 hc hc1 hc2 hc3 hc4 hc5 hc6
  rw [H8_card, H8_endpoint_profile_eq] at hchain
  norm_num at hchain ⊢
  exact le_of_mul_le_mul_right hchain H8_depthOne_profile_pos

/-- Therefore the coefficient-`126871` product budget is false as a universal actual-subgroup
statement. -/
theorem H8_no_126871_sixTransition_certificate :
    ¬ ∃ c1 c2 c3 c4 c5 c6 : Real,
      SixTransitionBounds H8 c1 c2 c3 c4 c5 c6 ∧
      0 <= c1 ∧ 0 <= c2 ∧ 0 <= c3 ∧ 0 <= c4 ∧ 0 <= c5 ∧ 0 <= c6 ∧
      c1 * c2 * c3 * c4 * c5 * c6 <= 126871 := by
  rintro ⟨c1, c2, c3, c4, c5, c6, hc, hc1, hc2, hc3, hc4, hc5, hc6, hprod⟩
  have hlower := H8_sixTransition_product_ge_eight_pow_six hc hc1 hc2 hc3 hc4 hc5 hc6
  norm_num at hlower
  linarith

/-! ## The known one-bit slice does not approach the global transition scale -/

def productionN : Nat := 2 ^ 30

def productionQ : Nat := productionN * (2 ^ 128 + 192) + 1

def injectiveCoefficient : Nat := 126871

/-- The normalized depth-two lower envelope forced solely by the `n/2` antipodal zero-sum
subsets. -/
noncomputable def antipodalDepthTwoLower (q n : Nat) : Real :=
  (q : Real) *
    ((q : Real) *
        (n.choose 2 + (n / 2) * (n / 2 - 1) : Nat) -
      (n.choose 2 : Real) ^ 2) /
    (n.choose 2 : Real) ^ 2

/-- The actual normalized depth-two discrepancy dominates the antipodal envelope. -/
theorem normalizedSubsetDeviation_two_ge_antipodalLower
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0) {q n : Nat}
    (hq : Fintype.card F = q) (hn : G.card = n) (hn2 : 2 <= n) :
    antipodalDepthTwoLower q n <= normalizedSubsetDeviation G 2 := by
  have hcoll := subgroup_twoSubset_collision_antipodal_lower G hG hnegOne h2
  rw [hn] at hcoll
  unfold normalizedSubsetDeviation
  rw [subsetDeviationEnergy_eq_collision, hn, hq]
  unfold antipodalDepthTwoLower
  have hchoose : 0 < n.choose 2 := Nat.choose_pos hn2
  have hden : (0 : Real) < (n.choose 2 : Real) ^ 2 := by positivity
  apply (div_le_div_iff_of_pos_right hden).2
  gcongr

/-- Pure production arithmetic: the antipodal lower envelope already exceeds the Wick numerator
`3` on the actual first transition. -/
theorem production_antipodal_first_transition_arithmetic :
    3 * ((productionQ : Real) * (productionQ - productionN) / productionN) <
      (productionN : Real) * antipodalDepthTwoLower productionQ productionN := by
  norm_num [antipodalDepthTwoLower, productionQ, productionN, Nat.choose_two_right]

/-- Quantitative form: the forced antipodal contribution exceeds Wick `3` by more than
`2^-29` (and less than `2^-28` at the level of the lower envelope). -/
theorem production_antipodal_first_ratio_window :
    3 + (2 : Real) ^ (-29 : Int) <
        (productionN : Real) * antipodalDepthTwoLower productionQ productionN /
          ((productionQ : Real) * (productionQ - productionN) / productionN) ∧
      (productionN : Real) * antipodalDepthTwoLower productionQ productionN /
          ((productionQ : Real) * (productionQ - productionN) / productionN) <
        3 + (2 : Real) ^ (-28 : Int) := by
  norm_num [antipodalDepthTwoLower, productionQ, productionN, Nat.choose_two_right,
    zpow_neg]

/-- The forced antipodal excess itself lies well inside the `501/500` ordinary-Wick tolerance,
but the relaxed selected-defect cap `2*(501/500)` is still far below it.  This is only a statement
about the antipodal lower envelope, not an upper bound on the complete first transition. -/
theorem production_antipodal_vs_robust_wick_envelope :
    (2 : Real) * (501 / 500 : Real) < 3 + (2 : Real) ^ (-29 : Int) ∧
      (productionN : Real) * antipodalDepthTwoLower productionQ productionN /
          ((productionQ : Real) * (productionQ - productionN) / productionN) <
        3 * (501 / 500 : Real) := by
  constructor
  · norm_num [zpow_neg]
  · exact lt_trans production_antipodal_first_ratio_window.2 (by norm_num [zpow_neg])

/-- **The actual forward `1 -> 2` transition is strictly worse than Wick `3`.**  In particular
the known one-bit same-sign cross-mass halving cannot be used as a `3 -> 2` improvement for this
trajectory: it is a different slice of the spectrum. -/
theorem production_first_transition_strictly_gt_three
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F = productionQ) (hn : G.card = productionN) :
    3 * normalizedSubsetDeviation G 1 <
      (G.card : Real) * normalizedSubsetDeviation G 2 := by
  have hlower := normalizedSubsetDeviation_two_ge_antipodalLower G hG hnegOne h2
    hq hn (by norm_num [productionN])
  have hone := normalizedSubsetDeviation_one G (by rw [hn]; norm_num [productionN])
  rw [hn, hq] at hone
  calc
    3 * normalizedSubsetDeviation G 1 =
        3 * ((productionQ : Real) * (productionQ - productionN) / productionN) := by
      rw [hone]
    _ < (productionN : Real) * antipodalDepthTwoLower productionQ productionN :=
      production_antipodal_first_transition_arithmetic
    _ <= (G.card : Real) * normalizedSubsetDeviation G 2 := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left hlower (by positivity)

/-- Ratio form of the same exclusion, including the explicit `2^-29` margin. -/
theorem production_first_transition_ratio_gt_three_plus_two_neg29
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F = productionQ) (hn : G.card = productionN) :
    3 + (2 : Real) ^ (-29 : Int) <
      (G.card : Real) * normalizedSubsetDeviation G 2 /
        normalizedSubsetDeviation G 1 := by
  have hlower := normalizedSubsetDeviation_two_ge_antipodalLower G hG hnegOne h2
    hq hn (by norm_num [productionN])
  have hone := normalizedSubsetDeviation_one G (by rw [hn]; norm_num [productionN])
  rw [hn, hq] at hone
  have honepos : 0 < normalizedSubsetDeviation G 1 := by
    rw [hone]
    norm_num [productionQ, productionN]
  have harith := production_antipodal_first_ratio_window.1
  calc
    3 + (2 : Real) ^ (-29 : Int) <
        (productionN : Real) * antipodalDepthTwoLower productionQ productionN /
          ((productionQ : Real) * (productionQ - productionN) / productionN) := harith
    _ = (productionN : Real) * antipodalDepthTwoLower productionQ productionN /
          normalizedSubsetDeviation G 1 := by rw [hone]
    _ <= (G.card : Real) * normalizedSubsetDeviation G 2 /
          normalizedSubsetDeviation G 1 := by
      rw [hn]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlower (by positivity)) honepos.le

/-- Hence neither the one-unit improvement `3 -> 2` nor even the Wick baseline `c₀ <= 3` is
valid for the production forward subset trajectory. -/
theorem production_first_transition_not_wick_three
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F = productionQ) (hn : G.card = productionN) :
    ¬ TransitionBound G 1 3 := by
  intro h
  unfold TransitionBound at h
  exact (not_lt_of_ge h)
    (production_first_transition_strictly_gt_three G hG hnegOne h2 hq hn)

/-- Even the robust selected-defect allowance `2*(501/500)` is impossible at the first step.
Therefore the one-unit Wick defect must be sought at one of the remaining five transitions. -/
theorem production_first_transition_not_robust_selected_defect
    (G : Finset F) (hG : IsMulSubgroup G) (hnegOne : (-1 : F) ∈ G)
    (h2 : (2 : F) ≠ 0)
    (hq : Fintype.card F = productionQ) (hn : G.card = productionN) :
    ¬ TransitionBound G 1 (2 * (501 / 500 : Real)) := by
  intro hselected
  apply production_first_transition_not_wick_three G hG hnegOne h2 hq hn
  unfold TransitionBound at hselected ⊢
  calc
    (G.card : Real) * normalizedSubsetDeviation G 2 <=
        (2 * (501 / 500 : Real)) * normalizedSubsetDeviation G 1 := hselected
    _ <= 3 * normalizedSubsetDeviation G 1 := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (normalizedSubsetDeviation_nonneg G 1)

/-- Even if the genuine one-bit same-sign halving from `DilationDoublingLevelSet` were available
independently at all six colours, the resulting factor `2^6` would still miss the required total
production contraction by strictly between `157` and `158` bits. -/
theorem six_independent_halvings_miss_by_157_158_bits :
    2 ^ 157 * (2 ^ 6 * injectiveCoefficient) < productionN ^ 6 ∧
      productionN ^ 6 < 2 ^ 158 * (2 ^ 6 * injectiveCoefficient) := by
  norm_num [productionN, injectiveCoefficient]

#print axioms normalizedSubsetDeviation_nonneg
#print axioms subsetSumCount_one
#print axioms subsetDeviationEnergy_one
#print axioms normalizedSubsetDeviation_one
#print axioms normalizedSubsetDeviation_one_start
#print axioms injectiveSevenTransform_eq_sum_deletedDiagonalTerm
#print axioms injectiveSevenTransform_norm_sq_le_deletedDiagonalEnergy
#print axioms subgroup_injectiveSeven_exact_colored_transition
#print axioms subgroup_nonzero_injectiveSeven_energy_le_colored_transition
#print axioms subsetDeviationEnergy_eq_collision
#print axioms exists_negationHalf_of_mulSubgroup
#print axioms subgroup_half_le_twoSubset_zeroFiber
#print axioms subgroup_twoSubset_collision_antipodal_lower
#print axioms sixTransitionBounds_chain
#print axioms productionTrajectoryCertificate_closes_injective_target
#print axioms subsetDeviationEnergy_compl
#print axioms normalizedSubsetDeviation_compl
#print axioms H8_isMulSubgroup
#print axioms H8_endpoint_profile_eq
#print axioms H8_depthOne_profile_pos
#print axioms H8_sixTransition_product_ge_eight_pow_six
#print axioms H8_no_126871_sixTransition_certificate
#print axioms production_first_transition_strictly_gt_three
#print axioms production_first_transition_ratio_gt_three_plus_two_neg29
#print axioms production_first_transition_not_wick_three
#print axioms production_first_transition_not_robust_selected_defect
#print axioms six_independent_halvings_miss_by_157_158_bits

end ArkLib.ProximityGap.Frontier.BGKCenteredTrajectoryContraction
