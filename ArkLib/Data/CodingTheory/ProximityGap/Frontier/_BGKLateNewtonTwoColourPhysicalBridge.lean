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
        ∑ t : T, ((phaseFiberCount phi t : Int) * phaseFiberCount phi t +
          (phaseFiberCount chi t : Int) * phaseFiberCount chi t -
            2 * (phaseFiberCount phi t : Int) * phaseFiberCount chi t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = (phaseCrossCollisionCount phi phi : Int) +
        phaseCrossCollisionCount chi chi -
          2 * phaseCrossCollisionCount phi chi := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← h11, ← h22]
      have htwo :
          (∑ t : T, 2 * (phaseFiberCount phi t : Int) * phaseFiberCount chi t) =
            2 * ∑ t : T, (phaseFiberCount phi t : Int) * phaseFiberCount chi t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      rw [htwo, ← h12]

/-- A physical fibre partitions exactly into a predicate sector and its complement. -/
theorem phaseFiberCount_eq_subtype_add_compl (phi : X -> T) (p : X -> Prop)
    [DecidablePred p] (t : T) :
    phaseFiberCount phi t =
      phaseFiberCount (fun z : {x : X // p x} => phi z.1) t +
        phaseFiberCount (fun z : {x : X // ¬ p x} => phi z.1) t := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X).filter fun x => phi x = t) p
  have hpos :
      phaseFiberCount (fun z : {x : X // p x} => phi z.1) t =
        ((Finset.univ : Finset X).filter fun x => p x ∧ phi x = t).card := by
    unfold phaseFiberCount
    calc
      ((Finset.univ.filter fun z : {x : X // p x} => phi z.1 = t).card) =
          Fintype.card {z : {x : X // p x} // phi z.1 = t} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card {x : X // p x ∧ phi x = t} :=
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p fun x => phi x = t)
      _ = ((Finset.univ : Finset X).filter fun x => p x ∧ phi x = t).card :=
        Fintype.card_subtype _
  have hneg :
      phaseFiberCount (fun z : {x : X // ¬ p x} => phi z.1) t =
        ((Finset.univ : Finset X).filter fun x => ¬ p x ∧ phi x = t).card := by
    unfold phaseFiberCount
    calc
      ((Finset.univ.filter fun z : {x : X // ¬ p x} => phi z.1 = t).card) =
          Fintype.card {z : {x : X // ¬ p x} // phi z.1 = t} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card {x : X // ¬ p x ∧ phi x = t} :=
        Fintype.card_congr
          (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => ¬ p x) fun x => phi x = t)
      _ = ((Finset.univ : Finset X).filter fun x => ¬ p x ∧ phi x = t).card :=
        Fintype.card_subtype _
  rw [hpos, hneg]
  unfold phaseFiberCount
  simpa only [Finset.filter_filter, Finset.mem_univ, true_and, and_comm] using hpart.symm

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

/-! ### Erase/insert cancellation of the common physical sector -/

/-- Newton joins in which the marked point is already present in the subset. -/
abbrev RepeatedMarkedJoin (G : Finset F) (r : Nat) :=
  {z : NewtonJoin G r // z.1 ∈ z.2.1}

/-- Newton joins in which the marked point is fresh relative to the subset. -/
abbrev FreshMarkedJoin (G : Finset F) (r : Nat) :=
  {z : NewtonJoin G r // z.1 ∉ z.2.1}

/-- Erasing the repeated marked point lowers the subset depth by one and makes it fresh. -/
def eraseRepeatedMarkedJoin (G : Finset F) {r : Nat} (hr : 0 < r) :
    RepeatedMarkedJoin G r -> FreshMarkedJoin G (r - 1) := by
  intro z
  have hcard : z.1.2.1.card = r :=
    (Finset.mem_powersetCard.mp z.1.2.2).2
  have heraseCard : (z.1.2.1.erase z.1.1).card = r - 1 := by
    rw [Finset.card_erase_of_mem z.2, hcard]
  refine ⟨⟨z.1.1, ⟨z.1.2.1.erase z.1.1,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heraseCard⟩⟩⟩, ?_⟩
  simp

/-- Inserting a fresh marked point raises the subset depth by one and makes it repeated. -/
def insertFreshMarkedJoin (G : Finset F) {r : Nat} (hr : 0 < r) :
    FreshMarkedJoin G (r - 1) -> RepeatedMarkedJoin G r := by
  intro z
  have hcard : z.1.2.1.card = r - 1 :=
    (Finset.mem_powersetCard.mp z.1.2.2).2
  have hinsertCard : (insert z.1.1 z.1.2.1).card = r := by
    rw [Finset.card_insert_of_notMem z.2, hcard]
    omega
  refine ⟨⟨z.1.1, ⟨insert z.1.1 z.1.2.1,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hinsertCard⟩⟩⟩, ?_⟩
  exact Finset.mem_insert_self z.1.1 z.1.2.1

/-- **The common-sector bijection.**  Repeated `U1` configurations are exactly fresh `U2`
configurations after erasing the marked point. -/
def repeatedFreshEquiv (G : Finset F) {r : Nat} (hr : 0 < r) :
    RepeatedMarkedJoin G r ≃ FreshMarkedJoin G (r - 1) where
  toFun := eraseRepeatedMarkedJoin G hr
  invFun := insertFreshMarkedJoin G hr
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Finset.insert_erase z.2
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Finset.erase_insert z.2

/-- Restricted phase of the repeated part of `U1`. -/
noncomputable def repeatedOnePhase (G : Finset F) (r : Nat)
    (z : RepeatedMarkedJoin G r) : F :=
  newtonJoinPhase G 1 r z.1

/-- Restricted phase of the fresh part of `U2`. -/
noncomputable def freshTwoPhase (G : Finset F) (r : Nat)
    (z : FreshMarkedJoin G (r - 1)) : F :=
  newtonJoinPhase G 2 (r - 1) z.1

/-- Restricted phase of the fresh part of `U1`. -/
noncomputable def freshOnePhase (G : Finset F) (r : Nat)
    (z : FreshMarkedJoin G r) : F :=
  newtonJoinPhase G 1 r z.1

/-- Restricted phase of the repeated part of `U2`. -/
noncomputable def repeatedTwoPhase (G : Finset F) (r : Nat)
    (z : RepeatedMarkedJoin G (r - 1)) : F :=
  newtonJoinPhase G 2 (r - 1) z.1

/-- Fresh weight-three phase obtained after erasing the marked point from repeated `U2`. -/
noncomputable def freshThreePhase (G : Finset F) (r : Nat)
    (z : FreshMarkedJoin G (r - 2)) : F :=
  newtonJoinPhase G 3 (r - 2) z.1

/-- Erasing a repeated marked point increases its weight by one and preserves the phase. -/
theorem eraseRepeatedMarkedJoin_phase (G : Finset F) {r : Nat} (hr : 0 < r)
    (k : Nat) (z : RepeatedMarkedJoin G r) :
    newtonJoinPhase G (k + 1) (r - 1) (eraseRepeatedMarkedJoin G hr z).1 =
      newtonJoinPhase G k r z.1 := by
  classical
  dsimp only [eraseRepeatedMarkedJoin, newtonJoinPhase]
  rw [← Finset.sum_erase_add _ (fun y : {x : F // x ∈ G} => y.1) z.2]
  push_cast
  ring

/-- The erase/insert bijection preserves the physical phase exactly. -/
theorem repeatedFreshEquiv_phase (G : Finset F) {r : Nat} (hr : 0 < r)
    (z : RepeatedMarkedJoin G r) :
    freshTwoPhase G r (repeatedFreshEquiv G hr z) = repeatedOnePhase G r z := by
  classical
  change freshTwoPhase G r (eraseRepeatedMarkedJoin G hr z) = repeatedOnePhase G r z
  exact eraseRepeatedMarkedJoin_phase G hr 1 z

/-- Consequently the repeated `U1` and fresh `U2` physical histograms agree fibre by fibre. -/
theorem repeatedOneFiber_eq_freshTwoFiber (G : Finset F) {r : Nat} (hr : 0 < r) (y : F) :
    phaseFiberCount (repeatedOnePhase G r) y =
      phaseFiberCount (freshTwoPhase G r) y := by
  classical
  let e : {z : RepeatedMarkedJoin G r // repeatedOnePhase G r z = y} ≃
      {z : FreshMarkedJoin G (r - 1) // freshTwoPhase G r z = y} :=
    (repeatedFreshEquiv G hr).subtypeEquiv fun z => by
      rw [repeatedFreshEquiv_phase G hr z]
  simpa [phaseFiberCount, Fintype.card_subtype] using Fintype.card_congr e

/-- Repeating the same erase/insert argument one level later identifies repeated `U2` with the
fresh weight-three join of depth `r-2`. -/
theorem repeatedTwoFiber_eq_freshThreeFiber
    (G : Finset F) {r : Nat} (hr : 1 < r) (y : F) :
    phaseFiberCount (repeatedTwoPhase G r) y =
      phaseFiberCount (freshThreePhase G r) y := by
  classical
  have hr1 : 0 < r - 1 := by omega
  let e0 := repeatedFreshEquiv G hr1
  have hphase (z : RepeatedMarkedJoin G (r - 1)) :
      freshThreePhase G r (e0 z) = repeatedTwoPhase G r z := by
    dsimp only [e0]
    change newtonJoinPhase G 3 (r - 2) (eraseRepeatedMarkedJoin G hr1 z).1 =
      newtonJoinPhase G 2 (r - 1) z.1
    simpa [Nat.sub_sub] using eraseRepeatedMarkedJoin_phase G hr1 2 z
  let e : {z : RepeatedMarkedJoin G (r - 1) // repeatedTwoPhase G r z = y} ≃
      {z : FreshMarkedJoin G (r - 2) // freshThreePhase G r z = y} :=
    e0.subtypeEquiv fun z => by rw [hphase z]
  simpa [phaseFiberCount, Fintype.card_subtype] using Fintype.card_congr e

/-- The first Newton join splits into its repeated and fresh marked sectors. -/
theorem oneFiber_eq_repeated_add_fresh (G : Finset F) (r : Nat) (y : F) :
    phaseFiberCount (newtonJoinPhase G 1 r) y =
      phaseFiberCount (repeatedOnePhase G r) y +
        phaseFiberCount (freshOnePhase G r) y := by
  simpa only [repeatedOnePhase, freshOnePhase] using
    phaseFiberCount_eq_subtype_add_compl (newtonJoinPhase G 1 r)
      (fun z : NewtonJoin G r => z.1 ∈ z.2.1) y

/-- The second Newton join splits into its repeated and fresh marked sectors. -/
theorem twoFiber_eq_repeated_add_fresh (G : Finset F) (r : Nat) (y : F) :
    phaseFiberCount (newtonJoinPhase G 2 (r - 1)) y =
      phaseFiberCount (repeatedTwoPhase G r) y +
        phaseFiberCount (freshTwoPhase G r) y := by
  simpa only [repeatedTwoPhase, freshTwoPhase] using
    phaseFiberCount_eq_subtype_add_compl (newtonJoinPhase G 2 (r - 1))
      (fun z : NewtonJoin G (r - 1) => z.1 ∈ z.2.1) y

/-- **Exact cancellation theorem.**  After the common repeated-`U1`/fresh-`U2` sector is
cancelled by `repeatedFreshEquiv`, the dominant physical profile is precisely fresh `U1` minus
repeated `U2`. -/
theorem twoColourPhysicalProfile_eq_fresh_sub_repeated
    (G : Finset F) {r : Nat} (hr : 0 < r) (y : F) :
    twoColourPhysicalProfile G r y =
      (phaseFiberCount (freshOnePhase G r) y : Int) -
        phaseFiberCount (repeatedTwoPhase G r) y := by
  unfold twoColourPhysicalProfile signedPhaseFiberProfile
  rw [oneFiber_eq_repeated_add_fresh, twoFiber_eq_repeated_add_fresh,
    repeatedOneFiber_eq_freshTwoFiber G hr y]
  push_cast
  ring

/-- At depths at least two, the residual repeated-`U2` sector is itself the fresh weight-three
join.  Thus the dominant packet is fresh weight one minus fresh weight three. -/
theorem twoColourPhysicalProfile_eq_freshOne_sub_freshThree
    (G : Finset F) {r : Nat} (hr : 1 < r) (y : F) :
    twoColourPhysicalProfile G r y =
      (phaseFiberCount (freshOnePhase G r) y : Int) -
        phaseFiberCount (freshThreePhase G r) y := by
  rw [twoColourPhysicalProfile_eq_fresh_sub_repeated G (by omega) y,
    repeatedTwoFiber_eq_freshThreeFiber G hr y]

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
  simp [pow_two]

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

/-- Generic algebraic form of a depth-`r` dominant-pair budget: it is exactly a lower bound on
the favourable cross collision `C12`. -/
theorem dominantPairBudgetAt_iff_crossCollisionLowerBound
    (n q cap r : Int) (previous C11 C22 C12 dc : Int) :
    1000 * n * (q * (C11 + C22 - 2 * C12) - dc ^ 2) <=
        cap * (n - r) ^ 2 * previous <->
      2000 * n * q * C12 >=
        1000 * n * (q * (C11 + C22) - dc ^ 2) -
          cap * (n - r) ^ 2 * previous := by
  constructor <;> intro h <;> nlinarith

/-- Exact `r=5` target selected by the dominant-pair socket. -/
theorem fifthDominantPairBudget_iff_crossCollisionLowerBound
    (D : Nat -> Int) (q C11 C22 C12 dc : Int) :
    FifthDominantPairBudget D
        (q * (C11 + C22 - 2 * C12) - dc ^ 2) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * q * C12 >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            (q * (C11 + C22) - dc ^ 2) -
          10500 * (BGKLaterTransitionDefectLedgers.productionN - 5 : Int) ^ 2 * D 5 := by
  unfold FifthDominantPairBudget
  constructor <;> intro h <;> nlinarith

/-- Exact `r=6` target selected by the dominant-pair socket. -/
theorem sixthDominantPairBudget_iff_crossCollisionLowerBound
    (D : Nat -> Int) (q C11 C22 C12 dc : Int) :
    SixthDominantPairBudget D
        (q * (C11 + C22 - 2 * C12) - dc ^ 2) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * q * C12 >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            (q * (C11 + C22) - dc ^ 2) -
          12500 * (BGKLaterTransitionDefectLedgers.productionN - 6 : Int) ^ 2 * D 6 := by
  unfold SixthDominantPairBudget
  constructor <;> intro h <;> nlinarith

/-! ### Literal socket integration -/

/-- The remaining centered Newton energy after removing the physical two-colour leading term at
`5 -> 6`.  This definition is exact and makes no sign claim about the tail. -/
noncomputable def fifthTwoColourTail {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) : Int :=
  36 * D 6 - centeredTwoColourCollision G 5

/-- The analogous exact tail at `6 -> 7`. -/
noncomputable def sixthTwoColourTail {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) : Int :=
  49 * D 7 - centeredTwoColourCollision G 6

/-- The actual physical leading term and its complementary tail satisfy the literal fifth socket. -/
theorem fifthNewtonSplit_twoColour {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) :
    FifthNewtonSplit D (centeredTwoColourCollision G 5) (fifthTwoColourTail D G) := by
  unfold FifthNewtonSplit fifthTwoColourTail
  ring

/-- The actual physical leading term and its complementary tail satisfy the literal sixth socket. -/
theorem sixthNewtonSplit_twoColour {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) :
    SixthNewtonSplit D (centeredTwoColourCollision G 6) (sixthTwoColourTail D G) := by
  unfold SixthNewtonSplit sixthTwoColourTail
  ring

/-- **Actual field-data form of the fifth cross-collision gate.** -/
theorem fifthTwoColourBudget_iff_actualCrossCollision
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) :
    FifthDominantPairBudget D (centeredTwoColourCollision G 5) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * (Fintype.card F : Int) *
          (newtonJoinCollisionCount G 1 5 2 4 : Int) >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            ((Fintype.card F : Int) *
                ((newtonJoinCollisionCount G 1 5 1 5 : Int) +
                  newtonJoinCollisionCount G 2 4 2 4) - twoColourDC G 5 ^ 2) -
          10500 * (BGKLaterTransitionDefectLedgers.productionN - 5 : Int) ^ 2 * D 5 := by
  simpa [centeredTwoColourCollision, twoColourCollisionForm] using
    fifthDominantPairBudget_iff_crossCollisionLowerBound D
      (Fintype.card F : Int)
      (newtonJoinCollisionCount G 1 5 1 5 : Int)
      (newtonJoinCollisionCount G 2 4 2 4 : Int)
      (newtonJoinCollisionCount G 1 5 2 4 : Int) (twoColourDC G 5)

/-- **Actual field-data form of the sixth cross-collision gate.** -/
theorem sixthTwoColourBudget_iff_actualCrossCollision
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Nat -> Int) (G : Finset F) :
    SixthDominantPairBudget D (centeredTwoColourCollision G 6) <->
      2000 * BGKLaterTransitionDefectLedgers.productionN * (Fintype.card F : Int) *
          (newtonJoinCollisionCount G 1 6 2 5 : Int) >=
        1000 * BGKLaterTransitionDefectLedgers.productionN *
            ((Fintype.card F : Int) *
                ((newtonJoinCollisionCount G 1 6 1 6 : Int) +
                  newtonJoinCollisionCount G 2 5 2 5) - twoColourDC G 6 ^ 2) -
          12500 * (BGKLaterTransitionDefectLedgers.productionN - 6 : Int) ^ 2 * D 6 := by
  simpa [centeredTwoColourCollision, twoColourCollisionForm] using
    sixthDominantPairBudget_iff_crossCollisionLowerBound D
      (Fintype.card F : Int)
      (newtonJoinCollisionCount G 1 6 1 6 : Int)
      (newtonJoinCollisionCount G 2 5 2 5 : Int)
      (newtonJoinCollisionCount G 1 6 2 5 : Int) (twoColourDC G 6)

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
