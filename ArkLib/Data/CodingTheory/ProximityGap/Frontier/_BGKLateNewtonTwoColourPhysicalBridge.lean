/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonSignedCovariance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonDominantPairSocket

/-!
# Physical-space bridge for the dominant two-colour Newton packet

At the `r -> r+1` subset transition, the first two Newton joins are

`U1(b) = p1(b) * e_r(b)` and `U2(b) = p2(b) * e_(r-1)(b)`.

The dominant signed packet is `U1-U2`.  This file identifies its full and centered Fourier
energies exactly.  If `C_ij` counts collisions between the physical phase families underlying
`Ui` and `Uj`, then

`sum_b |U1(b)-U2(b)|^2 = q * (C_11 + C_22 - 2 C_12)`,

and deleting frequency zero subtracts

`[n * (choose(n,r) - choose(n,r-1))]^2`.

Equivalently, let `a_i(y)` be the number of physical `Ui` configurations with phase `y`.  The
same signed collision form is the manifestly nonnegative integer

`sum_y (a_1(y)-a_2(y))^2`.

The exact scalar gates at the two production transitions are therefore lower bounds on the one
favourable cross-collision count `C_12`.  The constants are `10500` at `r=5` and `12500` at
`r=6`, with the remaining `21` and `25` reserved for the late-Newton tail by
`_BGKLateNewtonDominantPairSocket`.  No such production-subgroup correlation estimate is asserted
here.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKLateNewtonDominantPairSocket
open ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers
open ArkLib.ProximityGap.Frontier.BGKCenteredTrajectoryContraction
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption

/-! ## Generic signed-fibre identity -/

section SignedFibres

variable {T X Y : Type*} [Fintype T] [DecidableEq T]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Number of members of a finite phase family in one physical fibre. -/
noncomputable def phaseFiberCount (phi : X -> T) (t : T) : Nat :=
  (Finset.univ.filter fun x => phi x = t).card

/-- Signed physical profile of two phase families. -/
noncomputable def signedPhaseFiberProfile (phi : X -> T) (chi : Y -> T) (t : T) : Int :=
  (phaseFiberCount phi t : Int) - phaseFiberCount chi t

/-- Cross collisions are the fibrewise inner product of the two physical histograms. -/
theorem phaseCrossCollisionCount_eq_fiberInner (phi : X -> T) (chi : Y -> T) :
    phaseCrossCollisionCount phi chi =
      ∑ t : T, phaseFiberCount phi t * phaseFiberCount chi t := by
  classical
  unfold phaseCrossCollisionCount phaseFiberCount
  calc
    (∑ x : X, ∑ y : Y, if phi x = chi y then 1 else 0) =
        ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : X × Y => phi p.1 = chi p.2)).card := by
      rw [Finset.card_filter, Finset.sum_product]
    _ = ∑ t : T,
        ((Finset.univ.filter fun x : X => phi x = t) ×ˢ
          (Finset.univ.filter fun y : Y => chi y = t)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion]
        constructor
        · intro h
          exact ⟨phi p.1, rfl, h.symm⟩
        · rintro ⟨t, hphi, hchi⟩
          exact hphi.trans hchi.symm
      · intro a _ha b _hb hab
        apply Finset.disjoint_left.mpr
        intro p hp hq
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        exact hab (hp.1.symm.trans hq.1)
    _ = ∑ t : T,
        (Finset.univ.filter fun x : X => phi x = t).card *
          (Finset.univ.filter fun y : Y => chi y = t).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_product]

/-- The signed collision form is exactly the square mass of the signed physical profile. -/
theorem sum_signedPhaseFiberProfile_sq_eq_crossCollisionForm
    (phi : X -> T) (chi : Y -> T) :
    ∑ t : T, signedPhaseFiberProfile phi chi t ^ 2 =
      (phaseCrossCollisionCount phi phi : Int) +
        phaseCrossCollisionCount chi chi -
          2 * phaseCrossCollisionCount phi chi := by
  have h11 : (phaseCrossCollisionCount phi phi : Int) =
      ∑ t : T, (phaseFiberCount phi t : Int) * phaseFiberCount phi t := by
    rw [phaseCrossCollisionCount_eq_fiberInner]
    push_cast
    rfl
  have h22 : (phaseCrossCollisionCount chi chi : Int) =
      ∑ t : T, (phaseFiberCount chi t : Int) * phaseFiberCount chi t := by
    rw [phaseCrossCollisionCount_eq_fiberInner]
    push_cast
    rfl
  have h12 : (phaseCrossCollisionCount phi chi : Int) =
      ∑ t : T, (phaseFiberCount phi t : Int) * phaseFiberCount chi t := by
    rw [phaseCrossCollisionCount_eq_fiberInner]
    push_cast
    rfl
  unfold signedPhaseFiberProfile
  calc
    (∑ t : T, ((phaseFiberCount phi t : Int) - phaseFiberCount chi t) ^ 2) =
        ∑ t : T, (phaseFiberCount phi t : Int) * phaseFiberCount phi t +
          (phaseFiberCount chi t : Int) * phaseFiberCount chi t -
            2 * (phaseFiberCount phi t : Int) * phaseFiberCount chi t := by
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = (phaseCrossCollisionCount phi phi : Int) +
        phaseCrossCollisionCount chi chi -
          2 * phaseCrossCollisionCount phi chi := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← h11, ← h22,
        ← Finset.mul_sum, ← h12]

end SignedFibres

/-! ## The two-colour Newton packet -/

section TwoColour

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The dominant unscaled two-colour Newton packet at predecessor depth `r`. -/
noncomputable def twoColourPeriod (psi : AddChar F Complex) (G : Finset F)
    (r : Nat) (b : F) : Complex :=
  newtonJoinPeriod psi G 1 r b - newtonJoinPeriod psi G 2 (r - 1) b

/-- Exact weighted collision form `C_11+C_22-2C_12`. -/
noncomputable def twoColourCollisionForm (G : Finset F) (r : Nat) : Int :=
  (newtonJoinCollisionCount G 1 r 1 r : Int) +
    newtonJoinCollisionCount G 2 (r - 1) 2 (r - 1) -
      2 * newtonJoinCollisionCount G 1 r 2 (r - 1)

/-- The signed physical histogram whose Fourier transform is the two-colour packet. -/
noncomputable def twoColourPhysicalProfile (G : Finset F) (r : Nat) (y : F) : Int :=
  signedPhaseFiberProfile (newtonJoinPhase G 1 r)
    (newtonJoinPhase G 2 (r - 1)) y

/-- The DC mass of `U1-U2`, kept in `Int` because the two source cardinalities need not be
ordered at arbitrary parameters. -/
def twoColourDC (G : Finset F) (r : Nat) : Int :=
  (G.card : Int) * (G.card.choose r : Int) -
    (G.card : Int) * (G.card.choose (r - 1) : Int)

/-- Fourier-side product form `p1*e_r-p2*e_(r-1)`. -/
theorem twoColourPeriod_eq_powerSum_esymm
    (psi : AddChar F Complex) (G : Finset F) (r : Nat) (b : F) :
    twoColourPeriod psi G r b =
      phasePowerSum (subgroupPhase psi G b) 1 *
          (Finset.univ.val.map (subgroupPhase psi G b)).esymm r -
        phasePowerSum (subgroupPhase psi G b) 2 *
          (Finset.univ.val.map (subgroupPhase psi G b)).esymm (r - 1) := by
  unfold twoColourPeriod
  rw [newtonJoinPeriod_eq_powerSum_mul_esymm,
    newtonJoinPeriod_eq_powerSum_mul_esymm]

/-- Cardinality of one Newton-join source. -/
theorem card_newtonJoin (G : Finset F) (m : Nat) :
    Fintype.card (NewtonJoin G m) = G.card * G.card.choose m := by
  classical
  simp only [NewtonJoin, SubsetAt, Fintype.card_prod, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]

/-- Exact zero-frequency source imbalance. -/
theorem twoColourPeriod_zero (psi : AddChar F Complex) (G : Finset F) (r : Nat) :
    twoColourPeriod psi G r 0 = (twoColourDC G r : Complex) := by
  classical
  simp [twoColourPeriod, newtonJoinPeriod, phaseFamilyPeriod, twoColourDC,
    card_newtonJoin]

/-- The weighted collision form is the nonnegative physical square mass. -/
theorem twoColourCollisionForm_eq_physicalSquare (G : Finset F) (r : Nat) :
    twoColourCollisionForm G r = ∑ y : F, twoColourPhysicalProfile G r y ^ 2 := by
  unfold twoColourCollisionForm twoColourPhysicalProfile
  rw [sum_signedPhaseFiberProfile_sq_eq_crossCollisionForm]
  rfl

/-- Full-frequency cross Parseval for the dominant pair. -/
theorem sum_twoColourPeriod_mul_conj_eq_collisionForm
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (r : Nat) :
    (∑ b : F, twoColourPeriod psi G r b *
      (starRingEnd Complex) (twoColourPeriod psi G r b)) =
      (Fintype.card F : Complex) * (twoColourCollisionForm G r : Complex) := by
  classical
  unfold twoColourPeriod
  simp only [map_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, sub_mul, mul_sub]
  rw [sum_newtonJoinPeriod_mul_conj_eq_collision hpsi,
    sum_newtonJoinPeriod_mul_conj_eq_collision hpsi,
    sum_newtonJoinPeriod_mul_conj_eq_collision hpsi,
    sum_newtonJoinPeriod_mul_conj_eq_collision hpsi]
  rw [newtonJoinCollisionCount_swap G 2 (r - 1) 1 r]
  unfold twoColourCollisionForm
  push_cast
  ring

/-- **Exact centered two-colour identity.**  Removing frequency zero subtracts the square of the
source-cardinality imbalance and nothing else. -/
theorem sum_nonzero_twoColourPeriod_mul_conj_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (r : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F), twoColourPeriod psi G r b *
      (starRingEnd Complex) (twoColourPeriod psi G r b)) =
      (Fintype.card F : Complex) * (twoColourCollisionForm G r : Complex) -
        (twoColourDC G r : Complex) ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_twoColourPeriod_mul_conj_eq_collisionForm hpsi, twoColourPeriod_zero]
  simp only [map_intCast, starRingEnd_apply]
  rw [map_intCast]
  ring

/-- Integer numerator of the centered dominant-pair energy. -/
noncomputable def centeredTwoColourCollision (G : Finset F) (r : Nat) : Int :=
  (Fintype.card F : Int) * twoColourCollisionForm G r - twoColourDC G r ^ 2

/-- The complex Fourier identity is exactly the cast of the integer physical numerator. -/
theorem sum_nonzero_twoColourPeriod_mul_conj_eq_centeredCollision
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (r : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F), twoColourPeriod psi G r b *
      (starRingEnd Complex) (twoColourPeriod psi G r b)) =
      (centeredTwoColourCollision G r : Complex) := by
  rw [sum_nonzero_twoColourPeriod_mul_conj_eq hpsi]
  unfold centeredTwoColourCollision
  push_cast
  ring

end TwoColour

/-! ## Exact cross-collision gates for the production ledgers -/

section Gates

/-- Generic algebraic form of the dominant-pair budget: it is exactly a lower bound on the
favourable cross collision `C12`. -/
theorem dominantPairBudget_iff_crossCollisionLowerBound
    (n q cap : Int) (previous C11 C22 C12 dc : Int) :
    1000 * n * (q * (C11 + C22 - 2 * C12) - dc ^ 2) <=
        cap * (n - 5) ^ 2 * previous <->
      2000 * n * q * C12 >=
        1000 * n * (q * (C11 + C22) - dc ^ 2) -
          cap * (n - 5) ^ 2 * previous := by
  constructor <;> intro h <;> nlinarith

/-- Exact `r=5` target selected by the dominant-pair socket. -/
theorem fifthDominantPairBudget_iff_crossCollisionLowerBound
    (q previous C11 C22 C12 dc : Int) :
    FifthDominantPairBudget (fun r => if r = 5 then previous else 0)
        (q * (C11 + C22 - 2 * C12) - dc ^ 2) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * q * C12 >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            (q * (C11 + C22) - dc ^ 2) -
          10500 * (BGKLaterTransitionDefectLedgers.productionN - 5 : Int) ^ 2 * previous := by
  unfold FifthDominantPairBudget
  simp only [if_pos]
  constructor <;> intro h <;> nlinarith

/-- Exact `r=6` target selected by the dominant-pair socket. -/
theorem sixthDominantPairBudget_iff_crossCollisionLowerBound
    (q previous C11 C22 C12 dc : Int) :
    SixthDominantPairBudget (fun r => if r = 6 then previous else 0)
        (q * (C11 + C22 - 2 * C12) - dc ^ 2) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * q * C12 >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            (q * (C11 + C22) - dc ^ 2) -
          12500 * (BGKLaterTransitionDefectLedgers.productionN - 6 : Int) ^ 2 * previous := by
  unfold SixthDominantPairBudget
  simp only [if_pos]
  constructor <;> intro h <;> nlinarith

end Gates

/-! ## Axiom audit -/

#print axioms phaseCrossCollisionCount_eq_fiberInner
#print axioms sum_signedPhaseFiberProfile_sq_eq_crossCollisionForm
#print axioms twoColourPeriod_eq_powerSum_esymm
#print axioms twoColourCollisionForm_eq_physicalSquare
#print axioms sum_nonzero_twoColourPeriod_mul_conj_eq_centeredCollision
#print axioms fifthDominantPairBudget_iff_crossCollisionLowerBound
#print axioms sixthDominantPairBudget_iff_crossCollisionLowerBound

end ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge
