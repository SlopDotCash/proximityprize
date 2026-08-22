/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96ProductionDepthFourFixedEnergy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96DepthMomentWeld
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion

/-!
# G97: weld the mapped core type to subgroup energy at depth four

G88's mapped-alphabet core type is exactly the tuple type counted by `Finset.addREnergy`; G96's
depth–moment weld identifies that count with `rEnergy`.  The existing convolution recursion then
gives `E₄ ≤ n⁴ E₂`.  Consequently the actual depth-four sector is absorbed from the single explicit
fixed-energy input `E₂² ≤ 128 n⁵`. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G97DepthFourEnergyWeld

open scoped BigOperators
open G88EqualSumCorrectedDecoder
open G96ProductionDepthFourFixedEnergy
open G96DepthMomentWeld
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.CharPMomentRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Words over the subtype alphabet `G` are equivalent to ambient words belonging to the
`piFinset` of `G`. -/
def subtypeWordEquiv (G : Finset F) (s : ℕ) :
    (Fin s → {x // x ∈ G}) ≃ ↥(Fintype.piFinset fun _ : Fin s => G) where
  toFun f := ⟨fun i => (f i).1, Fintype.mem_piFinset.mpr (fun i => (f i).2)⟩
  invFun f := fun i => ⟨f.1 i, Fintype.mem_piFinset.mp f.2 i⟩
  left_inv f := rfl
  right_inv f := by ext i; rfl

/-- The equal-sum subtype of the product `piFinset` is equivalent to the coercion type of its
filtered finset. -/
def equalPairFilterEquiv (G : Finset F) (s : ℕ) :
    {x : ↥((Fintype.piFinset fun _ : Fin s => G) ×ˢ
        (Fintype.piFinset fun _ : Fin s => G)) //
      ∑ i, x.1.1 i = ∑ i, x.1.2 i} ≃
      ↥{x ∈ (Fintype.piFinset fun _ : Fin s => G) ×ˢ
          (Fintype.piFinset fun _ : Fin s => G) |
        ∑ i, x.1 i = ∑ i, x.2 i} where
  toFun x := ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
  invFun x :=
    ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
  left_inv x := rfl
  right_inv x := rfl

/-- The corrected decoder's mapped equal-sum core type has cardinality exactly `addREnergy`. -/
theorem card_equalSumCorePair_subtype_eq_addREnergy (G : Finset F) (s : ℕ) :
    Fintype.card (EqualSumCorePair {x // x ∈ G} F (fun x => x.1) s) =
      Finset.addREnergy s G := by
  classical
  let ep : ((Fin s → {x // x ∈ G}) × (Fin s → {x // x ∈ G})) ≃
      ↥((Fintype.piFinset fun _ : Fin s => G) ×ˢ
        (Fintype.piFinset fun _ : Fin s => G)) :=
    { toFun := fun x =>
        ⟨(fun i => (x.1 i).1, fun i => (x.2 i).1), Finset.mem_product.mpr
          ⟨Fintype.mem_piFinset.mpr (fun i => (x.1 i).2),
            Fintype.mem_piFinset.mpr (fun i => (x.2 i).2)⟩⟩
      invFun := fun x =>
        (fun i => ⟨x.1.1 i, Fintype.mem_piFinset.mp (Finset.mem_product.mp x.2).1 i⟩,
          fun i => ⟨x.1.2 i, Fintype.mem_piFinset.mp (Finset.mem_product.mp x.2).2 i⟩)
      left_inv := fun x => rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  let es : EqualSumCorePair {x // x ∈ G} F (fun x => x.1) s ≃
      {x : ↥((Fintype.piFinset fun _ : Fin s => G) ×ˢ
        (Fintype.piFinset fun _ : Fin s => G)) //
          ∑ i, x.1.1 i = ∑ i, x.1.2 i} :=
    Equiv.subtypeEquiv ep (fun x => by
      rfl)
  calc
    Fintype.card (EqualSumCorePair {x // x ∈ G} F (fun x => x.1) s) =
        Fintype.card {x : ↥((Fintype.piFinset fun _ : Fin s => G) ×ˢ
          (Fintype.piFinset fun _ : Fin s => G)) //
            ∑ i, x.1.1 i = ∑ i, x.1.2 i} := Fintype.card_congr es
    _ = Fintype.card ↥{x ∈ (Fintype.piFinset fun _ : Fin s => G) ×ˢ
          (Fintype.piFinset fun _ : Fin s => G) |
        ∑ i, x.1 i = ∑ i, x.2 i} := Fintype.card_congr (equalPairFilterEquiv G s)
    _ = Finset.addREnergy s G := by rw [Fintype.card_coe, Finset.addREnergy_def]

/-- The mapped core count is the production moment carrier `rEnergy`. -/
theorem card_equalSumCorePair_subtype_eq_rEnergy (G : Finset F) (s : ℕ) :
    Fintype.card (EqualSumCorePair {x // x ∈ G} F (fun x => x.1) s) =
      rEnergy G s := by
  rw [card_equalSumCorePair_subtype_eq_addREnergy, rEnergy_eq_addREnergy]

/-- Two applications of the existing convolution recursion give `E₄ ≤ n⁴E₂`. -/
theorem rEnergy_four_le_card_pow_four_mul_two (G : Finset F) :
    rEnergy G 4 ≤ G.card ^ 4 * rEnergy G 2 := by
  calc
    rEnergy G 4 = rEnergy G (3 + 1) := by norm_num
    _ ≤ G.card ^ 2 * rEnergy G 3 := rEnergy_succ_le G 3
    _ ≤ G.card ^ 2 * (G.card ^ 2 * rEnergy G 2) := by
      gcongr
      simpa using rEnergy_succ_le G 2
    _ = G.card ^ 4 * rEnergy G 2 := by ring

/-- **Actual depth-four subgroup consumer.** The only remaining hypothesis is the explicit
fixed-depth second-energy estimate. -/
theorem production_depth_four_of_rEnergy_two
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hsecond : (rEnergy G 2) ^ 2 ≤ 128 * (2 ^ 30) ^ 5) :
    Fintype.card (MaxCancellationCollisionSector {x // x ∈ G} F
      (fun x => x.1) 110 4) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply production_depth_four_finset_of_core_sq F G hcard
  rw [card_equalSumCorePair_subtype_eq_rEnergy]
  calc
    (rEnergy G 4) ^ 2 ≤ (G.card ^ 4 * rEnergy G 2) ^ 2 :=
      Nat.pow_le_pow_left (rEnergy_four_le_card_pow_four_mul_two G) 2
    _ = G.card ^ 8 * (rEnergy G 2) ^ 2 := by ring
    _ ≤ G.card ^ 8 * (128 * (2 ^ 30) ^ 5) := Nat.mul_le_mul_left _ hsecond
    _ = 128 * (2 ^ 30) ^ 13 := by rw [hcard]; ring

end ArkLib.ProximityGap.Frontier.G97DepthFourEnergyWeld

#print axioms
  ArkLib.ProximityGap.Frontier.G97DepthFourEnergyWeld.card_equalSumCorePair_subtype_eq_rEnergy
#print axioms
  ArkLib.ProximityGap.Frontier.G97DepthFourEnergyWeld.rEnergy_four_le_card_pow_four_mul_two
#print axioms
  ArkLib.ProximityGap.Frontier.G97DepthFourEnergyWeld.production_depth_four_of_rEnergy_two
