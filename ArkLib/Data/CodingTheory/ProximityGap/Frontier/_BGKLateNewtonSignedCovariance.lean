/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKActualJointPeriodLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCenteredTrajectoryContraction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLaterTransitionDefectLedgers

/-!
# Signed Newton covariance at the two dense subset transitions

For depth `d`, Newton's identity writes the ordered-injective period as

`J_d(b) = (d-1)! * sum_(k=1)^d (-1)^(k-1) p_k(b) e_(d-k)(b)`.

The product `p_k e_(d-k)` has a direct physical-space meaning: it is the Fourier transform of
pairs `(x,S)` with `x in G`, `S` a `(d-k)`-subset of `G`, and phase

`k*x + sum_(y in S) y`.

This file packages those structured pairs into `newtonJoinPeriod`.  A generic cross-Parseval
theorem then turns every covariance of two Newton joins into one exact collision count.  A second
generic coefficient-vector theorem expands the energy of an arbitrary signed sum.  Combining the
two gives the full `L2` energy of `J_6` and `J_7` as one signed quadratic form, without 36 or 49
separate cross-term proofs.  Removing frequency zero subtracts the exact ordered-injective DC
masses `(6! * C(n,6))^2` and `(7! * C(n,7))^2`.

The sign ledger is alternating.  Thus the favorable covariances are exactly the opposite-parity
join pairs: nine unordered pairs at depth six and twelve at depth seven.  Triangle inequality or
Young discards all of this favorable mass.  Finally, factorial scaling cancels the `(r+1)^2`
factor in the compact transition ledgers.  The distributed late obligations become exactly

`1000*n*E_6 <= 10521*(n-5)^2*E_5`,

`1000*n*E_7 <= 12525*(n-6)^2*E_6`,

where `E_r=(r!)^2*Delta_r` is the ordered-injective nonzero energy ledger.  This is an exact
socket, not an estimate of the open favorable covariances.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance

open ArkLib.ProximityGap.Round4CharacterSum
open ArkLib.ProximityGap.MomentCollisionRigidity
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.BGKActualJointPeriodLaw
open ArkLib.ProximityGap.Frontier.BGKCenteredTrajectoryContraction
open ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption

section StructuredCrossParseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Collision count between two arbitrary finite phase families. -/
noncomputable def phaseCrossCollisionCount (phi : X -> F) (chi : Y -> F) : Nat :=
  ∑ x : X, ∑ y : Y, if phi x = chi y then 1 else 0

/-- Fourier transform of an arbitrary finite phase family. -/
noncomputable def phaseFamilyPeriod (psi : AddChar F Complex) (phi : X -> F) (b : F) : Complex :=
  ∑ x : X, psi (b * phi x)

/-- **Cross Parseval for two different structured phase families.** -/
theorem sum_phaseFamilyPeriod_mul_conj_eq_crossCollision
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (phi : X -> F) (chi : Y -> F) :
    (∑ b : F, phaseFamilyPeriod psi phi b *
      (starRingEnd Complex) (phaseFamilyPeriod psi chi b)) =
      (Fintype.card F : Complex) * phaseCrossCollisionCount phi chi := by
  classical
  have hchar : (0 : Nat) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : forall a : F, (starRingEnd Complex) (psi a) = psi (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc
    (∑ b : F, phaseFamilyPeriod psi phi b *
        (starRingEnd Complex) (phaseFamilyPeriod psi chi b)) =
        ∑ b : F, ∑ x : X, ∑ y : Y, psi (b * (phi x - chi y)) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [phaseFamilyPeriod, phaseFamilyPeriod, map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hconj, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ x : X, ∑ y : Y, ∑ b : F, psi (b * (phi x - chi y)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ x : X, ∑ y : Y,
        if phi x = chi y then (Fintype.card F : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [AddChar.sum_mulShift (phi x - chi y) hpsi]
      by_cases h : phi x = chi y <;> simp [h, sub_eq_zero]
    _ = (Fintype.card F : Complex) * phaseCrossCollisionCount phi chi := by
      unfold phaseCrossCollisionCount
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases h : phi x = chi y <;> simp [h]

/-- Cross-collision counts are symmetric after swapping the two phase families. -/
theorem phaseCrossCollisionCount_swap (phi : X -> F) (chi : Y -> F) :
    phaseCrossCollisionCount phi chi = phaseCrossCollisionCount chi phi := by
  classical
  unfold phaseCrossCollisionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases h : phi x = chi y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg]
    exact fun h' => h h'.symm

end StructuredCrossParseval

section NewtonJoins

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The finite type of `m`-subsets of the labelled copy of `G`. -/
abbrev SubsetAt (G : Finset F) (m : Nat) :=
  {S : Finset {x : F // x ∈ G} // S ∈ Finset.univ.powersetCard m}

/-- One marked subgroup point together with an independent `m`-subset. -/
abbrev NewtonJoin (G : Finset F) (m : Nat) := {x : F // x ∈ G} × SubsetAt G m

/-- Physical phase of a Newton join: one point has weight `k`, while the subset has unit weight. -/
noncomputable def newtonJoinPhase (G : Finset F) (k m : Nat) (z : NewtonJoin G m) : F :=
  (k : F) * z.1.1 + ∑ y ∈ z.2.1, y.1

/-- Fourier transform of the structured Newton join. -/
noncomputable def newtonJoinPeriod (psi : AddChar F Complex) (G : Finset F)
    (k m : Nat) (b : F) : Complex :=
  phaseFamilyPeriod psi (newtonJoinPhase G k m) b

/-- Exact collision count between two structured Newton joins. -/
noncomputable def newtonJoinCollisionCount (G : Finset F) (k m ell t : Nat) : Nat :=
  phaseCrossCollisionCount (newtonJoinPhase G k m) (newtonJoinPhase G ell t)

/-- A Newton join factors as `p_k * e_m`. -/
theorem newtonJoinPeriod_eq_powerSum_mul_esymm
    (psi : AddChar F Complex) (G : Finset F) (k m : Nat) (b : F) :
    newtonJoinPeriod psi G k m b =
      phasePowerSum (subgroupPhase psi G b) k *
        (Finset.univ.val.map (subgroupPhase psi G b)).esymm m := by
  classical
  unfold newtonJoinPeriod phaseFamilyPeriod newtonJoinPhase
  rw [Fintype.sum_prod_type]
  rw [Finset.esymm_map_val]
  unfold phasePowerSum
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_subtype (Finset.univ.powersetCard m) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro S _hS
  unfold subgroupPhase
  rw [prod_addChar_eq]
  rw [← AddChar.map_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul (R := F)]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [mul_add, Finset.mul_sum]
  simp only [smul_eq_mul]
  ring

/-- Every Newton-join covariance is one exact structured collision count. -/
theorem sum_newtonJoinPeriod_mul_conj_eq_collision
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (k m ell t : Nat) :
    (∑ b : F, newtonJoinPeriod psi G k m b *
      (starRingEnd Complex) (newtonJoinPeriod psi G ell t b)) =
      (Fintype.card F : Complex) * newtonJoinCollisionCount G k m ell t := by
  exact sum_phaseFamilyPeriod_mul_conj_eq_crossCollision hpsi
    (newtonJoinPhase G k m) (newtonJoinPhase G ell t)

theorem newtonJoinCollisionCount_swap (G : Finset F) (k m ell t : Nat) :
    newtonJoinCollisionCount G k m ell t = newtonJoinCollisionCount G ell t k m :=
  phaseCrossCollisionCount_swap _ _

end NewtonJoins

section CoefficientVector

variable {F : Type*} [Fintype F]

/-- Signed covariance quadratic form of an integer coefficient vector. -/
noncomputable def signedCovarianceForm {d : Nat} (c : Fin d -> Int)
    (A : Fin d -> Fin d -> Complex) : Complex :=
  ∑ i : Fin d, ∑ j : Fin d, (c i : Complex) * (c j : Complex) * A i j

/-- A single coefficient-vector identity expands every `d^2` covariance term. -/
theorem sum_linearCombination_mul_conj_eq_signedCovarianceForm {d : Nat}
    (c : Fin d -> Int) (u : Fin d -> F -> Complex) :
    (∑ b : F, (∑ i : Fin d, (c i : Complex) * u i b) *
      (starRingEnd Complex) (∑ j : Fin d, (c j : Complex) * u j b)) =
      signedCovarianceForm c
        (fun i j => ∑ b : F, u i b * (starRingEnd Complex) (u j b)) := by
  classical
  calc
    (∑ b : F, (∑ i : Fin d, (c i : Complex) * u i b) *
        (starRingEnd Complex) (∑ j : Fin d, (c j : Complex) * u j b)) =
        ∑ b : F, ∑ i : Fin d, ∑ j : Fin d,
          (c i : Complex) * (c j : Complex) *
            (u i b * (starRingEnd Complex) (u j b)) := by
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [map_sum, map_mul, map_intCast]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ b : F,
          (c i : Complex) * (c j : Complex) *
            (u i b * (starRingEnd Complex) (u j b)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = signedCovarianceForm c
        (fun i j => ∑ b : F, u i b * (starRingEnd Complex) (u j b)) := by
      unfold signedCovarianceForm
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.mul_sum]

end CoefficientVector

section LatePackets

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Alternating Newton sign. -/
def newtonSign {d : Nat} (i : Fin d) : Int := if Even i.val then 1 else -1

/-- The `i`th join in the depth-`d` Newton recurrence has marked weight `i+1` and subset depth
`d-1-i`. -/
noncomputable def lateNewtonJoinPeriod (psi : AddChar F Complex) (G : Finset F)
    (d : Nat) (i : Fin d) (b : F) : Complex :=
  newtonJoinPeriod psi G (i.val + 1) (d - 1 - i.val) b

/-- Collision matrix of the depth-`d` Newton joins. -/
noncomputable def lateNewtonCollisionMatrix (G : Finset F) (d : Nat)
    (i j : Fin d) : Int :=
  newtonJoinCollisionCount G (i.val + 1) (d - 1 - i.val)
    (j.val + 1) (d - 1 - j.val)

/-- Alternating structured Newton packet. -/
noncomputable def lateNewtonPacket (psi : AddChar F Complex) (G : Finset F)
    (d : Nat) (b : F) : Complex :=
  (Nat.factorial (d - 1) : Complex) *
    ∑ i : Fin d, (newtonSign i : Complex) * lateNewtonJoinPeriod psi G d i b

/-- Signed structured-collision form at depth `d`. -/
noncomputable def lateNewtonSignedCollisionForm (G : Finset F) (d : Nat) : Int :=
  ∑ i : Fin d, ∑ j : Fin d,
    newtonSign i * newtonSign j * lateNewtonCollisionMatrix G d i j

/-- Same-sign (unfavorable) collision mass. -/
noncomputable def lateNewtonSameSignMass (G : Finset F) (d : Nat) : Int :=
  ∑ i : Fin d, ∑ j : Fin d,
    if newtonSign i = newtonSign j then lateNewtonCollisionMatrix G d i j else 0

/-- Opposite-sign (favorable) collision mass. -/
noncomputable def lateNewtonFavorableMass (G : Finset F) (d : Nat) : Int :=
  ∑ i : Fin d, ∑ j : Fin d,
    if newtonSign i ≠ newtonSign j then lateNewtonCollisionMatrix G d i j else 0

/-- Exact signed split: triangle/Young keeps the first mass and discards the second. -/
theorem lateNewtonSignedCollisionForm_eq_same_sub_favorable (G : Finset F) (d : Nat) :
    lateNewtonSignedCollisionForm G d =
      lateNewtonSameSignMass G d - lateNewtonFavorableMass G d := by
  classical
  unfold lateNewtonSignedCollisionForm lateNewtonSameSignMass lateNewtonFavorableMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold newtonSign
  by_cases hi : Even i.val <;> by_cases hj : Even j.val <;> simp [hi, hj]

/-- Upper-triangular favorable pairs, used only to audit the sign ledger. -/
def favorableUpperPairs (d : Nat) : Finset (Fin d × Fin d) :=
  (Finset.univ ×ˢ Finset.univ).filter
    fun ij => ij.1.val < ij.2.val ∧ newtonSign ij.1 ≠ newtonSign ij.2

theorem depthSix_sign_vector :
    (fun i : Fin 6 => newtonSign i) = ![1, -1, 1, -1, 1, -1] := by
  funext i
  fin_cases i <;> decide

theorem depthSeven_sign_vector :
    (fun i : Fin 7 => newtonSign i) = ![1, -1, 1, -1, 1, -1, 1] := by
  funext i
  fin_cases i <;> decide

/-- There are nine favorable unordered covariances among the six Newton joins. -/
theorem favorableUpperPairs_six_card : (favorableUpperPairs 6).card = 9 := by decide

/-- There are twelve favorable unordered covariances among the seven Newton joins. -/
theorem favorableUpperPairs_seven_card : (favorableUpperPairs 7).card = 12 := by decide

theorem lateNewtonPacket_six_explicit (psi : AddChar F Complex) (G : Finset F) (b : F) :
    lateNewtonPacket psi G 6 b =
      120 * (newtonJoinPeriod psi G 1 5 b - newtonJoinPeriod psi G 2 4 b +
        newtonJoinPeriod psi G 3 3 b - newtonJoinPeriod psi G 4 2 b +
        newtonJoinPeriod psi G 5 1 b - newtonJoinPeriod psi G 6 0 b) := by
  norm_num [lateNewtonPacket, lateNewtonJoinPeriod, newtonSign, Fin.sum_univ_succ]
  ring

theorem lateNewtonPacket_seven_explicit (psi : AddChar F Complex) (G : Finset F) (b : F) :
    lateNewtonPacket psi G 7 b =
      720 * (newtonJoinPeriod psi G 1 6 b - newtonJoinPeriod psi G 2 5 b +
        newtonJoinPeriod psi G 3 4 b - newtonJoinPeriod psi G 4 3 b +
        newtonJoinPeriod psi G 5 2 b - newtonJoinPeriod psi G 6 1 b +
        newtonJoinPeriod psi G 7 0 b) := by
  norm_num [lateNewtonPacket, lateNewtonJoinPeriod, newtonSign, Fin.sum_univ_succ]
  ring

/-- The depth-six structured packet is the existing ordered-injective transform `J_6`. -/
theorem lateNewtonPacket_six_eq_orderedInjectiveTransform
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    lateNewtonPacket psi G 6 b =
      orderedInjectiveTransform (subgroupPhase psi G b) 6 := by
  rw [lateNewtonPacket_six_explicit]
  simp_rw [newtonJoinPeriod_eq_powerSum_mul_esymm]
  let w := subgroupPhase psi G b
  have h6 := multiset_newton w 6
  have ha6 : (Finset.antidiagonal 6).filter (fun a => a.1 < 6) =
      {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1)} := by decide
  rw [ha6] at h6
  have he0 : (G.val.attach.map w).esymm 0 = (1 : Complex) := by
    simp [Multiset.esymm]
  norm_num [Finset.sum_insert, psumMs, phasePowerSum] at h6
  dsimp [w] at h6 he0
  unfold phasePowerSum orderedInjectiveTransform
  simp only [Finset.univ_eq_attach, Finset.sum_eq_multiset_sum, Finset.attach_val] at h6 ⊢
  rw [he0] at h6 ⊢
  norm_num at h6
  ring_nf at h6 ⊢
  linear_combination -120 * h6

/-- The depth-seven structured packet is the existing ordered-injective transform `J_7`. -/
theorem lateNewtonPacket_seven_eq_orderedInjectiveTransform
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    lateNewtonPacket psi G 7 b =
      orderedInjectiveTransform (subgroupPhase psi G b) 7 := by
  rw [lateNewtonPacket_seven_explicit]
  simp_rw [newtonJoinPeriod_eq_powerSum_mul_esymm]
  let w := subgroupPhase psi G b
  have h7 := multiset_newton w 7
  have ha7 : (Finset.antidiagonal 7).filter (fun a => a.1 < 7) =
      {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} := by decide
  rw [ha7] at h7
  have he0 : (G.val.attach.map w).esymm 0 = (1 : Complex) := by
    simp [Multiset.esymm]
  norm_num [Finset.sum_insert, psumMs, phasePowerSum] at h7
  dsimp [w] at h7 he0
  unfold phasePowerSum orderedInjectiveTransform
  simp only [Finset.univ_eq_attach, Finset.sum_eq_multiset_sum, Finset.attach_val] at h7 ⊢
  rw [he0] at h7 ⊢
  norm_num at h7
  ring_nf at h7 ⊢
  linear_combination -720 * h7

/-- At depth seven the structured packet is also definitionally the project-wide
`injectiveSevenTransform`. -/
theorem lateNewtonPacket_seven_eq_injectiveSevenTransform
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    lateNewtonPacket psi G 7 b =
      injectiveSevenTransform (subgroupPhase psi G b) := by
  rw [lateNewtonPacket_seven_eq_orderedInjectiveTransform]
  rfl

/-- The zero-frequency ordered-injective transform is the falling-factorial source mass. -/
theorem orderedInjectiveTransform_subgroupPhase_zero
    (psi : AddChar F Complex) (G : Finset F) (d : Nat) :
    orderedInjectiveTransform (subgroupPhase psi G 0) d =
      (Nat.factorial d * G.card.choose d : Nat) := by
  classical
  unfold orderedInjectiveTransform subgroupPhase
  rw [Finset.esymm_map_val]
  simp [Finset.card_powersetCard]

theorem lateNewtonPacket_six_zero (psi : AddChar F Complex) (G : Finset F) :
    lateNewtonPacket psi G 6 0 = (Nat.factorial 6 * G.card.choose 6 : Nat) := by
  rw [lateNewtonPacket_six_eq_orderedInjectiveTransform,
    orderedInjectiveTransform_subgroupPhase_zero]

theorem lateNewtonPacket_seven_zero (psi : AddChar F Complex) (G : Finset F) :
    lateNewtonPacket psi G 7 0 = (Nat.factorial 7 * G.card.choose 7 : Nat) := by
  rw [lateNewtonPacket_seven_eq_orderedInjectiveTransform,
    orderedInjectiveTransform_subgroupPhase_zero]

/-- Integer ledger of the nonzero-frequency late Newton energy. -/
noncomputable def lateNewtonNonzeroEnergyLedger (G : Finset F) (d : Nat) : Int :=
  (Nat.factorial (d - 1) : Int) ^ 2 *
      (Fintype.card F : Int) * lateNewtonSignedCollisionForm G d -
    ((Nat.factorial d : Int) * G.card.choose d) ^ 2

/-- Generic full-frequency energy law for the alternating Newton packet. -/
theorem sum_lateNewtonPacket_mul_conj_eq_signedCollision
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (d : Nat) :
    (∑ b : F, lateNewtonPacket psi G d b *
      (starRingEnd Complex) (lateNewtonPacket psi G d b)) =
      (Nat.factorial (d - 1) : Complex) ^ 2 *
        (Fintype.card F : Complex) * (lateNewtonSignedCollisionForm G d : Complex) := by
  classical
  unfold lateNewtonPacket
  simp only [map_mul, map_natCast]
  have hquad := sum_linearCombination_mul_conj_eq_signedCovarianceForm
    (F := F) (c := fun i : Fin d => newtonSign i)
    (u := fun i b => lateNewtonJoinPeriod psi G d i b)
  calc
    (∑ b : F,
        ((Nat.factorial (d - 1) : Complex) *
            ∑ i : Fin d, (newtonSign i : Complex) * lateNewtonJoinPeriod psi G d i b) *
          ((Nat.factorial (d - 1) : Complex) *
            (starRingEnd Complex)
              (∑ i : Fin d, (newtonSign i : Complex) * lateNewtonJoinPeriod psi G d i b))) =
        (Nat.factorial (d - 1) : Complex) ^ 2 *
          ∑ b : F, (∑ i : Fin d,
              (newtonSign i : Complex) * lateNewtonJoinPeriod psi G d i b) *
            (starRingEnd Complex) (∑ i : Fin d,
              (newtonSign i : Complex) * lateNewtonJoinPeriod psi G d i b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (Nat.factorial (d - 1) : Complex) ^ 2 *
        signedCovarianceForm (fun i : Fin d => newtonSign i)
          (fun i j => ∑ b : F, lateNewtonJoinPeriod psi G d i b *
            (starRingEnd Complex) (lateNewtonJoinPeriod psi G d j b)) := by
      rw [hquad]
    _ = (Nat.factorial (d - 1) : Complex) ^ 2 *
        (Fintype.card F : Complex) * (lateNewtonSignedCollisionForm G d : Complex) := by
      unfold signedCovarianceForm lateNewtonSignedCollisionForm lateNewtonCollisionMatrix
      push_cast
      rw [mul_assoc]
      apply congrArg (fun z : Complex => (Nat.factorial (d - 1) : Complex) ^ 2 * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      unfold lateNewtonJoinPeriod
      rw [sum_newtonJoinPeriod_mul_conj_eq_collision hpsi]
      ring

/-- Exact nonzero-frequency `J_6` energy, including its DC subtraction. -/
theorem sum_nonzero_lateNewtonPacket_six_eq_ledger
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F), lateNewtonPacket psi G 6 b *
      (starRingEnd Complex) (lateNewtonPacket psi G 6 b)) =
      (lateNewtonNonzeroEnergyLedger G 6 : Complex) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_lateNewtonPacket_mul_conj_eq_signedCollision hpsi,
    lateNewtonPacket_six_zero]
  unfold lateNewtonNonzeroEnergyLedger
  push_cast
  norm_num [Nat.factorial]
  simp [starRingEnd_apply]
  ring

/-- Exact nonzero-frequency `J_7` energy, including its DC subtraction. -/
theorem sum_nonzero_lateNewtonPacket_seven_eq_ledger
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F), lateNewtonPacket psi G 7 b *
      (starRingEnd Complex) (lateNewtonPacket psi G 7 b)) =
      (lateNewtonNonzeroEnergyLedger G 7 : Complex) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_lateNewtonPacket_mul_conj_eq_signedCollision hpsi,
    lateNewtonPacket_seven_zero]
  unfold lateNewtonNonzeroEnergyLedger
  push_cast
  norm_num [Nat.factorial]
  simp [starRingEnd_apply]
  ring

end LatePackets

/-! ## Factorial-scaled transition ledgers -/

section FactorialScaling

/-- Ordered-injective energy ledger corresponding to an unordered collision defect. -/
def factorialScaledEnergy (D : Nat -> Int) (r : Nat) : Int :=
  (Nat.factorial r : Int) ^ 2 * D r

/-- Factorial scaling absorbs the adjacent square `(r+1)^2` exactly. -/
theorem compactTransitionLedger_iff_factorialScaledEnergy
    (n r capNumerator capDenominator : Nat) (D : Nat -> Int) :
    CompactTransitionLedger n r capNumerator capDenominator D <->
      (capDenominator : Int) * n * factorialScaledEnergy D (r + 1) <=
        (capNumerator : Int) * (n - r : Int) ^ 2 * factorialScaledEnergy D r := by
  have hfac : (0 : Int) < (Nat.factorial r : Int) ^ 2 := by positivity
  unfold CompactTransitionLedger factorialScaledEnergy
  constructor
  · intro h
    have hs := mul_le_mul_of_nonneg_left h (le_of_lt hfac)
    convert hs using 1
    · rw [Nat.factorial_succ]
      push_cast
      ring
    · ring
  · intro h
    have hs :
        (Nat.factorial r : Int) ^ 2 *
            ((capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1)) <=
          (Nat.factorial r : Int) ^ 2 *
            ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) := by
      convert h using 1
      · rw [Nat.factorial_succ]
        push_cast
        ring
      · ring
    exact le_of_mul_le_mul_left hs hfac

/-- Consolidated rational transition equivalence in ordered-injective energy coordinates. -/
theorem rationalTransitionAt_iff_factorialScaledEnergy
    (n : Nat) (D : Nat -> Int) {r capNumerator capDenominator : Nat}
    (hr : r + 1 <= n) (hcap : 0 < capDenominator) :
    RationalTransitionAt n r capNumerator capDenominator D <->
      (capDenominator : Int) * n * factorialScaledEnergy D (r + 1) <=
        (capNumerator : Int) * (n - r : Int) ^ 2 * factorialScaledEnergy D r := by
  rw [rationalTransitionAt_iff_compact n D hr hcap,
    compactTransitionLedger_iff_factorialScaledEnergy]

/-- Exact `5 -> 6` distributed-half-unit obligation in ordered-injective energy coordinates. -/
theorem production_halfUnit_five_iff_orderedEnergy (D : Nat -> Int) :
    RationalTransitionAt BGKLaterTransitionDefectLedgers.productionN 5 (21 * 501) 1000 D <->
      (1000 : Int) * BGKLaterTransitionDefectLedgers.productionN *
          factorialScaledEnergy D 6 <=
        10521 * (BGKLaterTransitionDefectLedgers.productionN - 5 : Int) ^ 2 *
          factorialScaledEnergy D 5 := by
  rw [rationalTransitionAt_iff_factorialScaledEnergy
    BGKLaterTransitionDefectLedgers.productionN D
    (by norm_num [BGKLaterTransitionDefectLedgers.productionN]) (by norm_num)]
  norm_num

/-- Exact `6 -> 7` distributed-half-unit obligation in ordered-injective energy coordinates. -/
theorem production_halfUnit_six_iff_orderedEnergy (D : Nat -> Int) :
    RationalTransitionAt BGKLaterTransitionDefectLedgers.productionN 6 (25 * 501) 1000 D <->
      (1000 : Int) * BGKLaterTransitionDefectLedgers.productionN *
          factorialScaledEnergy D 7 <=
        12525 * (BGKLaterTransitionDefectLedgers.productionN - 6 : Int) ^ 2 *
          factorialScaledEnergy D 6 := by
  rw [rationalTransitionAt_iff_factorialScaledEnergy
    BGKLaterTransitionDefectLedgers.productionN D
    (by norm_num [BGKLaterTransitionDefectLedgers.productionN]) (by norm_num)]
  norm_num

end FactorialScaling

/-! ## Axiom audit -/

#print axioms sum_phaseFamilyPeriod_mul_conj_eq_crossCollision
#print axioms newtonJoinPeriod_eq_powerSum_mul_esymm
#print axioms sum_linearCombination_mul_conj_eq_signedCovarianceForm
#print axioms lateNewtonSignedCollisionForm_eq_same_sub_favorable
#print axioms sum_lateNewtonPacket_mul_conj_eq_signedCollision
#print axioms compactTransitionLedger_iff_factorialScaledEnergy
#print axioms production_halfUnit_five_iff_orderedEnergy
#print axioms production_halfUnit_six_iff_orderedEnergy

end ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
