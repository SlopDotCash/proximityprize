/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G112FiberCollisionVarianceIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.TwistedLineCollisionParseval
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumCharacterSum

/-!
# The depth-seven injective Fourier residual is exactly subset-sum L2 mixing

For a seven-subset `S` of `G`, let `f(S)=sum S`.  Its Fourier coefficient is

`D7(b) = 7! * sum_S psi(b*f(S)) = 7! * e7({psi(b*x) : x in G})`.

The factor `7!` restores all internal orders, so this is precisely the ordered-injective
depth-seven transform.  Parseval and the exact fiber-square identity give

`sum_b |D7(b)|^2 = (7!)^2 * q * sum_y a_y^2`,

where `a_y=#{S : |S|=7, sum S=y}`.  Removing `b=0` and expanding the centered fiber variance gives

`q * sum_(b != 0) |D7(b)|^2 = (7!)^2 * sum_y (q*a_y-C(n,7))^2`.

Consequently the remaining injective target is **equivalent** to an L2 equidistribution estimate
for seven-subset sums:

`sum_(b != 0)|D7(b)|^2 <= 126871*q*n^7`

iff

`(7!)^2 * sum_y(q*a_y-C(n,7))^2 <= 126871*q^2*n^7`.

Thus exterior-power or sampling-without-replacement language is an exact reparametrization, not a
bypass.  Any saving must use multiplicative-subgroup mixing.  The companion clustered-distinct-
roots probe falsifies a universal phase-only inequality.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKDepthSevenInjectiveVarianceEquivalence

open ArkLib.ProximityGap.Round4CharacterSum
open ArkLib.ProximityGap.TwistedLineCollisionParseval
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fiber-pair double count, included locally to keep this lane independent of the depth-five BGK
weld chain. -/
theorem fiberSquare_eq_collisionPairs {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X -> Y) :
    ∑ y, (fiberCount f y) ^ 2 =
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : X × X => f p.1 = f p.2)).card := by
  classical
  have hfc : ∀ y, fiberCount f y =
      (Finset.univ.filter (fun x => f x = y)).card := by
    intro y
    rw [fiberCount, Fintype.card_subtype]
  calc
    ∑ y, (fiberCount f y) ^ 2 =
        ∑ y, ((Finset.univ.filter (fun x => f x = y)).card *
          (Finset.univ.filter (fun x' => f x' = y)).card) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hfc]
      ring
    _ = ∑ y, ((Finset.univ.filter (fun x => f x = y)) ×ˢ
        (Finset.univ.filter (fun x' => f x' = y))).card := by
      simp [Finset.card_product]
    _ = ∑ y, (Finset.univ.filter
        (fun p : X × X => f p.1 = y ∧ f p.2 = y)).card := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      congr 1
      ext p
      simp [Finset.mem_product]
    _ = ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : X × X => f p.1 = f p.2)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
          Finset.mem_product]
        constructor
        · rintro ⟨y, ⟨h1, h2⟩⟩
          rw [h1, h2]
        · intro h
          exact ⟨f p.2, ⟨h, rfl⟩⟩
      · intro a _ b _ hab
        apply Finset.disjoint_left.mpr
        intro p hp hq
        simp only [Finset.mem_filter] at hp hq
        exact hab (hp.2.1.symm.trans hq.2.1)

/-- The finite type of seven-subsets of `G`. -/
abbrev SevenSubset (G : Finset F) := {S : Finset F // S ∈ G.powersetCard 7}

/-- Coordinate-sum map on seven-subsets. -/
noncomputable def sevenSubsetSum (G : Finset F) (S : SevenSubset G) : F :=
  ∑ x ∈ S.1, x

/-- Fourier transform of the seven-subset sum histogram. -/
noncomputable def sevenSubsetFourier (psi : AddChar F Complex) (G : Finset F) (b : F) : Complex :=
  twistedLineEta psi Finset.univ (sevenSubsetSum G) b

/-- Ordered-injective depth-seven transform: the subset transform with its `7!` internal orders. -/
noncomputable def injectiveD7 (psi : AddChar F Complex) (G : Finset F) (b : F) : Complex :=
  (Nat.factorial 7 : Complex) * sevenSubsetFourier psi G b

/-- Product/exterior-power form: `D7=7!*e7`. -/
theorem injectiveD7_eq_subsetProduct (psi : AddChar F Complex) (G : Finset F) (b : F) :
    injectiveD7 psi G b =
      (Nat.factorial 7 : Complex) *
        ∑ S : SevenSubset G, ∏ x ∈ S.1, psi (b * x) := by
  unfold injectiveD7 sevenSubsetFourier twistedLineEta sevenSubsetSum
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact map_mul_sum_eq_prod psi b S.1

/-- Seven-subset fiber square, the unordered collision census. -/
noncomputable def sevenSubsetFiberSquare (G : Finset F) : Nat :=
  ∑ y, (fiberCount (sevenSubsetSum G) y) ^ 2

/-- The zero frequency is the complete ordered-injective source `(7!)*C(n,7)`. -/
theorem injectiveD7_zero (psi : AddChar F Complex) (G : Finset F) :
    injectiveD7 psi G 0 =
      (Nat.factorial 7 * G.card.choose 7 : Nat) := by
  classical
  unfold injectiveD7 sevenSubsetFourier twistedLineEta sevenSubsetSum
  simp [Finset.card_powersetCard]

/-- **Parseval for the ordered-injective transform.** -/
theorem sum_injectiveD7_norm_sq_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖injectiveD7 psi G b‖ ^ 2 =
      (Nat.factorial 7 : Real) ^ 2 * (Fintype.card F : Real) *
        sevenSubsetFiberSquare G := by
  classical
  have hparseval := twistedLineEnergy_eq_collisionCount hpsi
    (Finset.univ : Finset (SevenSubset G)) (sevenSubsetSum G)
  rw [← fiberSquare_eq_collisionPairs (sevenSubsetSum G)] at hparseval
  unfold injectiveD7 sevenSubsetFourier sevenSubsetFiberSquare
  rw [show (∑ b : F,
      ‖(Nat.factorial 7 : Complex) * twistedLineEta psi Finset.univ (sevenSubsetSum G) b‖ ^ 2) =
      (Nat.factorial 7 : Real) ^ 2 *
        ∑ b : F, ‖twistedLineEta psi Finset.univ (sevenSubsetSum G) b‖ ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [norm_mul, mul_pow]
    norm_num]
  rw [hparseval]
  ring

/-- Exact nonzero-frequency energy after removing the ordered-injective DC source. -/
theorem sum_nonzero_injectiveD7_norm_sq_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖injectiveD7 psi G b‖ ^ 2 =
      (Nat.factorial 7 : Real) ^ 2 *
        ((Fintype.card F : Real) * sevenSubsetFiberSquare G -
          (G.card.choose 7 : Real) ^ 2) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), sum_injectiveD7_norm_sq_eq hpsi,
    injectiveD7_zero]
  norm_num
  ring

/-- Fiber counts total `C(|G|,7)`. -/
theorem sum_sevenSubset_fiberCount (G : Finset F) :
    ∑ y, fiberCount (sevenSubsetSum G) y = G.card.choose 7 := by
  rw [sum_fiberCount, Fintype.card_coe, Finset.card_powersetCard]

/-- Centered L2 variance of the seven-subset sum histogram. -/
noncomputable def sevenSubsetCenteredVariance (G : Finset F) : Int :=
  ∑ y, ((Fintype.card F : Int) * (fiberCount (sevenSubsetSum G) y : Int) -
    (G.card.choose 7 : Int)) ^ 2

/-- **Exact centered-variance bridge.** -/
theorem sevenSubsetCenteredVariance_eq (G : Finset F) :
    sevenSubsetCenteredVariance G =
      (Fintype.card F : Int) *
        ((Fintype.card F : Int) * sevenSubsetFiberSquare G -
          (G.card.choose 7 : Int) ^ 2) := by
  unfold sevenSubsetCenteredVariance sevenSubsetFiberSquare
  rw [centeredFiberSquare_identity_nat _ _ (sum_sevenSubset_fiberCount G)]
  push_cast
  ring

/-- **Exact D7/variance equality.**  This is the promised no-bypass statement. -/
theorem card_mul_nonzero_D7_energy_eq_factorial_sq_mul_variance
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (Fintype.card F : Real) *
        (∑ b ∈ Finset.univ.erase (0 : F), ‖injectiveD7 psi G b‖ ^ 2) =
      (Nat.factorial 7 : Real) ^ 2 * sevenSubsetCenteredVariance G := by
  rw [sum_nonzero_injectiveD7_norm_sq_eq hpsi, sevenSubsetCenteredVariance_eq]
  push_cast
  ring

/-- **The remaining coefficient-126871 target is equivalent to subset-sum L2 mixing.** -/
theorem injectiveD7_target_iff_centeredVariance
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (n : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖injectiveD7 psi G b‖ ^ 2) <=
        126871 * (Fintype.card F : Real) * n ^ 7 ↔
      (Nat.factorial 7 : Real) ^ 2 * sevenSubsetCenteredVariance G <=
        126871 * (Fintype.card F : Real) ^ 2 * n ^ 7 := by
  have hq : (0 : Real) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hid := card_mul_nonzero_D7_energy_eq_factorial_sq_mul_variance hpsi G
  constructor <;> intro h <;> nlinarith

#print axioms injectiveD7_eq_subsetProduct
#print axioms fiberSquare_eq_collisionPairs
#print axioms injectiveD7_zero
#print axioms sum_injectiveD7_norm_sq_eq
#print axioms sum_nonzero_injectiveD7_norm_sq_eq
#print axioms sevenSubsetCenteredVariance_eq
#print axioms card_mul_nonzero_D7_energy_eq_factorial_sq_mul_variance
#print axioms injectiveD7_target_iff_centeredVariance

end ArkLib.ProximityGap.Frontier.BGKDepthSevenInjectiveVarianceEquivalence
