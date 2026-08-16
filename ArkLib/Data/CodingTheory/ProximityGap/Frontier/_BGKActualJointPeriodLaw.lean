/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyNegClosedLower
import ArkLib.Data.CodingTheory.ProximityGap.REnergyTwoExact

/-!
# The actual seven-colour Gaussian-period joint law

This file studies the joint spectrum

`b ↦ (η_b, η_{2b}, ..., η_{7b})`

for the genuine torsion subgroup, rather than an arbitrary dilation copula.  Its first output is a
weighted mixed-moment Parseval formula: every product of coloured periods and conjugate coloured
periods is exactly `q` times a weighted additive collision count in the subgroup.  At bidegree
`(1,1)` this specializes sharply.  If `r^n != s^n`, the two dilates `r μ_n` and `s μ_n` are
disjoint, so the full-frequency mixed moment is zero and the nonzero-frequency moment is exactly
`-n^2`.  Thus distinct colours are negatively correlated after DC removal.

For both certified production primes we additionally verify, by exact modular arithmetic, that the
seven multipliers `1,...,7` occupy seven different cyclotomic classes.  Consequently their true
nonzero-frequency Gram matrix has diagonal `q*n-n^2` and every off-diagonal entry `-n^2`: the seven
colour profiles form an exact regular-simplex frame.  This rules out aligned-copula behaviour and
pins the first genuinely arithmetic joint constraint.  It does not by itself control the
fourteen-variable collision counts appearing in the squared seventh Newton polynomial; those are
precisely the higher mixed moments exposed by the general formula below.

At the first Newton transition, the exact cross term is instead the midpoint-resonance count
`#{(x,y,z) in G^3 : x+y=2z}`.  The unconditional antipodal energy floor shows that a full one-unit
defect there would require more than `2^59` midpoint triples, whereas a pointwise `2^22`
representation cap gives at most `2^52`.  Thus that classical cap excludes depth one and pushes
the missing higher-order law to one of the later Newton transitions.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKActualJointPeriodLaw

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

/-- Production subgroup order. -/
def productionN : Nat := 2 ^ 30

/-- First certified production prime. -/
def productionP1 : Nat := productionN * (2 ^ 128 + 192) + 1

/-- Second certified production prime. -/
def productionP2 : Nat := productionN * (2 ^ 129 + 13) + 1

/-! ## Exact production colour separation -/

/-- Colour `j` is the field multiplier `j+1`. -/
def colourMultiplier {F : Type*} [NatCast F] (j : Fin 7) : F := (j.1 + 1 : Nat)

/-- Thirty repeated squarings compute the production exponent without a billion recursive
kernel reductions. -/
def squareTower {M : Type*} [Monoid M] (x : M) : Nat -> M
  | 0 => x
  | k + 1 => squareTower x k * squareTower x k

theorem squareTower_eq_pow {M : Type*} [Monoid M] (x : M) (k : Nat) :
    squareTower x k = x ^ (2 ^ k) := by
  induction k with
  | zero => simp [squareTower]
  | succ k ih =>
      rw [squareTower, ih, pow_succ, pow_mul]
      simp [pow_two]

/-- The seven small colours occupy distinct cyclotomic classes at the first production prime. -/
theorem productionP1_colourPowers_injective :
    Function.Injective (fun j : Fin 7 =>
      (colourMultiplier j : ZMod productionP1) ^ productionN) := by
  simpa [productionN, squareTower_eq_pow] using
    (show Function.Injective (fun j : Fin 7 =>
      squareTower (colourMultiplier j : ZMod productionP1) 30) by decide)

/-- The same exact separation holds at the second certified production prime. -/
theorem productionP2_colourPowers_injective :
    Function.Injective (fun j : Fin 7 =>
      (colourMultiplier j : ZMod productionP2) ^ productionN) := by
  simpa [productionN, squareTower_eq_pow] using
    (show Function.Injective (fun j : Fin 7 =>
      squareTower (colourMultiplier j : ZMod productionP2) 30) by decide)

/-- Both named moduli are prime. -/
theorem production_prime_certificates : productionP1.Prime ∧ productionP2.Prime := by
  constructor
  · simpa [productionP1, productionN, ArkLib.ProximityGap.PrizeShapePrimeP30.P] using
      ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P
  · simpa [productionP2, productionN, ArkLib.ProximityGap.PrizeShapePrimeP30Second.P] using
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P

local instance productionP1Prime : Fact productionP1.Prime :=
  ⟨production_prime_certificates.1⟩

local instance productionP2Prime : Fact productionP2.Prime :=
  ⟨production_prime_certificates.2⟩

/-! ## Every mixed coloured moment is a weighted subgroup collision count -/

section MixedMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Weighted sum of a subgroup tuple. -/
def weightedTupleSum (r : I -> F) (v : I -> F) : F := ∑ i, r i * v i

/-- The actual weighted additive-collision count behind a mixed product of coloured periods. -/
noncomputable def mixedDilationCollisionCount (G : Finset F) (r : I -> F) (s : J -> F) : Nat :=
  ∑ v ∈ Fintype.piFinset (fun _ : I => G),
    ∑ w ∈ Fintype.piFinset (fun _ : J => G),
      if weightedTupleSum r v = weightedTupleSum s w then 1 else 0

/-- The same collision census as a literal filtered product. -/
noncomputable def mixedDilationCollisions (G : Finset F) (r : I -> F) (s : J -> F) :
    Finset ((I -> F) × (J -> F)) :=
  ((Fintype.piFinset (fun _ : I => G)) ×ˢ (Fintype.piFinset (fun _ : J => G))).filter
    fun p => weightedTupleSum r p.1 = weightedTupleSum s p.2

theorem mixedDilationCollisionCount_eq_card (G : Finset F) (r : I -> F) (s : J -> F) :
    mixedDilationCollisionCount G r s = (mixedDilationCollisions G r s).card := by
  classical
  unfold mixedDilationCollisionCount mixedDilationCollisions
  rw [Finset.card_filter, Finset.sum_product]

/-- Reversing the two weighted tuple families does not change the collision count. -/
theorem mixedDilationCollisionCount_swap (G : Finset F) (r : I -> F) (s : J -> F) :
    mixedDilationCollisionCount G r s = mixedDilationCollisionCount G s r := by
  classical
  unfold mixedDilationCollisionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : weightedTupleSum r v = weightedTupleSum s w
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg]
    exact fun h' => h h'.symm

/-- A product of arbitrarily coloured periods expands into the character transform of the
corresponding weighted tuple-sum histogram. -/
theorem prod_dilated_eta_eq_weightedTupleSum
    (psi : AddChar F Complex) (G : Finset F) (b : F) (r : I -> F) :
    (∏ i, eta psi G (r i * b)) =
      ∑ v ∈ Fintype.piFinset (fun _ : I => G), psi (b * weightedTupleSum r v) := by
  classical
  have hprod : (∏ i, eta psi G (r i * b)) =
      ∏ i : I, ∑ y ∈ G, psi (b * (r i * y)) := by
    apply Finset.prod_congr rfl
    intro i hi
    unfold eta
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    ring
  rw [hprod, Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [prod_addChar_eq]
  unfold weightedTupleSum
  rw [Finset.mul_sum]

/-- **Weighted mixed-moment Parseval.**  This is an exact expansion for every monomial cross-term
in the squared seventh Newton polynomial. -/
theorem sum_prod_dilated_eta_mul_conj_eq_collisionCount
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (r : I -> F) (s : J -> F) :
    (∑ b : F, (∏ i, eta psi G (r i * b)) *
      (starRingEnd Complex) (∏ j, eta psi G (s j * b))) =
      (Fintype.card F : Complex) * mixedDilationCollisionCount G r s := by
  classical
  have hchar : (0 : Nat) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd Complex) (psi a) = psi (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hconjprod : ∀ b : F, (starRingEnd Complex) (∏ j, eta psi G (s j * b)) =
      ∑ w ∈ Fintype.piFinset (fun _ : J => G),
        psi (-(b * weightedTupleSum s w)) := by
    intro b
    rw [prod_dilated_eta_eq_weightedTupleSum, map_sum]
    exact Finset.sum_congr rfl (fun w _ => hconj _)
  calc
    (∑ b : F, (∏ i, eta psi G (r i * b)) *
        (starRingEnd Complex) (∏ j, eta psi G (s j * b))) =
        ∑ b : F, ∑ v ∈ Fintype.piFinset (fun _ : I => G),
          ∑ w ∈ Fintype.piFinset (fun _ : J => G),
            psi (b * (weightedTupleSum r v - weightedTupleSum s w)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hconjprod, prod_dilated_eta_eq_weightedTupleSum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ v ∈ Fintype.piFinset (fun _ : I => G),
          ∑ w ∈ Fintype.piFinset (fun _ : J => G),
            ∑ b : F, psi (b * (weightedTupleSum r v - weightedTupleSum s w)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
    _ = ∑ v ∈ Fintype.piFinset (fun _ : I => G),
          ∑ w ∈ Fintype.piFinset (fun _ : J => G),
            if weightedTupleSum r v = weightedTupleSum s w then
              (Fintype.card F : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [AddChar.sum_mulShift (weightedTupleSum r v - weightedTupleSum s w) hpsi]
      by_cases h : weightedTupleSum r v = weightedTupleSum s w <;>
        simp [h, sub_eq_zero]
    _ = (Fintype.card F : Complex) * mixedDilationCollisionCount G r s := by
      unfold mixedDilationCollisionCount
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : weightedTupleSum r v = weightedTupleSum s w <;> simp [h]

end MixedMoment

/-! ## A signed Newton-energy component and its exact DC threshold -/

section SepticResonance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Seven source colours of weight one, corresponding to the monomial `eta_b^7`. -/
def septicSourceWeights : Fin 7 -> F := fun _ => 1

/-- One target colour of weight seven, corresponding to `eta_(7b)`. -/
def septicTargetWeights : Fin 1 -> F := fun _ => 7

/-- Collision count behind the cross moment `sum_b eta_b^7 conj(eta_(7b))`. -/
noncomputable def septicResonanceCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G septicSourceWeights septicTargetWeights

/-- The evident diagonal resonances `(y,...,y; y)`, one for every `y` in `G`. -/
noncomputable def septicDiagonalPairs (G : Finset F) :
    Finset ((Fin 7 -> F) × (Fin 1 -> F)) :=
  G.image fun y => ((fun _ : Fin 7 => y), (fun _ : Fin 1 => y))

theorem septicDiagonalPairs_card (G : Finset F) : (septicDiagonalPairs G).card = G.card := by
  classical
  unfold septicDiagonalPairs
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact congrArg (fun p => p.1 (0 : Fin 7)) hxy

/-- Every diagonal resonance is a genuine weighted collision. -/
theorem septicDiagonalPairs_subset_collisions (G : Finset F) :
    septicDiagonalPairs G ⊆
      mixedDilationCollisions G septicSourceWeights septicTargetWeights := by
  classical
  intro p hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
  unfold mixedDilationCollisions
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_product]
    exact ⟨Fintype.mem_piFinset.mpr (fun _ => hy),
      Fintype.mem_piFinset.mpr (fun _ => hy)⟩
  · simp [weightedTupleSum, septicSourceWeights, septicTargetWeights]

/-- There are unconditionally at least `|G|` resonances in the full-frequency
`eta_b^7`--`720 eta_(7b)` cross component. -/
theorem card_le_septicResonanceCount (G : Finset F) :
    G.card ≤ septicResonanceCount G := by
  rw [septicResonanceCount, mixedDilationCollisionCount_eq_card,
    ← septicDiagonalPairs_card G]
  exact Finset.card_le_card (septicDiagonalPairs_subset_collisions G)

/-- Exact full-frequency mixed-moment expansion of that cross component.  Its right side is a
nonnegative integer multiple of `q`. -/
theorem sum_eta_pow_seven_mul_conj_eta_seven_eq_resonanceCount
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (∑ b : F, eta psi G b ^ 7 * (starRingEnd Complex) (eta psi G ((7 : F) * b))) =
      (Fintype.card F : Complex) * septicResonanceCount G := by
  simpa [septicResonanceCount, septicSourceWeights, septicTargetWeights,
    Finset.prod_const] using
    (sum_prod_dilated_eta_mul_conj_eq_collisionCount
      (I := Fin 7) (J := Fin 1) hpsi G septicSourceWeights septicTargetWeights)

/-- The prize-relevant nonzero-frequency component subtracts the exact DC term `|G|^8`.  Its sign
is therefore not determined by full-frequency positivity; it is controlled by whether the actual
weighted collision count lies above or below `|G|^8/q`. -/
theorem sum_nonzero_eta_pow_seven_mul_conj_eta_seven_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F),
      eta psi G b ^ 7 * (starRingEnd Complex) (eta psi G ((7 : F) * b))) =
      (Fintype.card F : Complex) * septicResonanceCount G - (G.card : Complex) ^ 8 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_eta_pow_seven_mul_conj_eta_seven_eq_resonanceCount hpsi]
  simp [eta, AddChar.map_zero_eq_one]
  ring

/-- Exact arithmetic sign criterion for the nonzero-frequency signed component. -/
theorem nonzero_septic_crossMoment_nonnegative_iff
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    0 ≤ (∑ b ∈ Finset.univ.erase (0 : F),
      eta psi G b ^ 7 * (starRingEnd Complex) (eta psi G ((7 : F) * b))).re ↔
      G.card ^ 8 ≤ Fintype.card F * septicResonanceCount G := by
  rw [sum_nonzero_eta_pow_seven_mul_conj_eta_seven_eq hpsi]
  simp?
  norm_cast

/-- Quantitative positivity of the same signed component after taking real parts. -/
theorem septic_crossMoment_real_lower
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) :
    (Fintype.card F : Real) * G.card ≤
      (∑ b : F, eta psi G b ^ 7 *
        (starRingEnd Complex) (eta psi G ((7 : F) * b))).re := by
  rw [sum_eta_pow_seven_mul_conj_eta_seven_eq_resonanceCount hpsi]
  norm_cast
  exact Nat.mul_le_mul_left (Fintype.card F) (card_le_septicResonanceCount G)

end SepticResonance

/-! ## The exact regular-simplex law at bidegree `(1,1)` -/

section PairLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Number of pairs in two weighted dilates which land at the same field point. -/
def dilationCoincidenceCount (G : Finset F) (r s : F) : Nat :=
  ∑ x ∈ G, ∑ y ∈ G, if r * x = s * y then 1 else 0

/-- Exact `(1,1)` mixed moment: the inner product of two colour profiles is `q` times the
intersection multiplicity of their two dilated source sets. -/
theorem sum_dilated_eta_mul_conj_eq_dilationCoincidenceCount
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F) (r s : F) :
    (∑ b : F, eta psi G (r * b) * (starRingEnd Complex) (eta psi G (s * b))) =
      (Fintype.card F : Complex) * dilationCoincidenceCount G r s := by
  classical
  have hchar : (0 : Nat) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd Complex) (psi a) = psi (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hconjeta : ∀ b : F,
      (starRingEnd Complex) (eta psi G (s * b)) = ∑ y ∈ G, psi (-((s * b) * y)) := by
    intro b
    rw [eta, map_sum]
    exact Finset.sum_congr rfl (fun y _ => hconj _)
  calc
    (∑ b : F, eta psi G (r * b) * (starRingEnd Complex) (eta psi G (s * b))) =
        ∑ b : F, ∑ x ∈ G, ∑ y ∈ G, psi (b * (r * x - s * y)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hconjeta]
      unfold eta
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ b : F, psi (b * (r * x - s * y)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ G, ∑ y ∈ G,
          if r * x = s * y then (Fintype.card F : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [AddChar.sum_mulShift (r * x - s * y) hpsi]
      by_cases h : r * x = s * y <;> simp [h, sub_eq_zero]
    _ = (Fintype.card F : Complex) * dilationCoincidenceCount G r s := by
      unfold dilationCoincidenceCount
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : r * x = s * y <;> simp [h]

/-- Different `d`-th powers force the two dilates of the genuine `d`-torsion subgroup to be
disjoint.  This is the first constraint unavailable to an arbitrary dilation copula. -/
theorem dilationCoincidenceCount_torsion_eq_zero {d : Nat} (r s : F)
    (hrs : r ^ d ≠ s ^ d) :
    dilationCoincidenceCount (torsion F d) r s = 0 := by
  classical
  unfold dilationCoincidenceCount
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  rw [if_neg]
  intro heq
  apply hrs
  calc
    r ^ d = r ^ d * x ^ d := by rw [(mem_torsion.mp hx), mul_one]
    _ = (r * x) ^ d := (mul_pow r x d).symm
    _ = (s * y) ^ d := congrArg (fun z : F => z ^ d) heq
    _ = s ^ d * y ^ d := mul_pow s y d
    _ = s ^ d := by rw [(mem_torsion.mp hy), mul_one]

/-- A nonzero multiplier gives exactly one partner in the same dilate for every subgroup point. -/
theorem dilationCoincidenceCount_same (G : Finset F) (r : F) (hr : r ≠ 0) :
    dilationCoincidenceCount G r r = G.card := by
  classical
  unfold dilationCoincidenceCount
  calc
    (∑ x ∈ G, ∑ y ∈ G, if r * x = r * y then 1 else 0) =
        ∑ x ∈ G, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have heq : ∀ y : F, (r * x = r * y ↔ x = y) := by
        intro y
        constructor
        · exact mul_left_cancel₀ hr
        · exact congrArg (fun z : F => r * z)
      simp_rw [heq]
      simp [hx]
    _ = G.card := by simp

/-- Full-field orthogonality of genuinely separated torsion colours. -/
theorem sum_torsion_dilated_eta_mul_conj_eq_zero
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) {d : Nat}
    (r s : F) (hrs : r ^ d ≠ s ^ d) :
    (∑ b : F, eta psi (torsion F d) (r * b) *
      (starRingEnd Complex) (eta psi (torsion F d) (s * b))) = 0 := by
  rw [sum_dilated_eta_mul_conj_eq_dilationCoincidenceCount hpsi,
    dilationCoincidenceCount_torsion_eq_zero r s hrs]
  simp

/-- After deleting the common DC term, two separated actual period profiles have exact covariance
`-|mu_d|^2`. -/
theorem sum_nonzero_torsion_dilated_eta_mul_conj_eq_neg_card_sq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) {d : Nat}
    (r s : F) (hrs : r ^ d ≠ s ^ d) :
    (∑ b ∈ Finset.univ.erase (0 : F),
      eta psi (torsion F d) (r * b) *
        (starRingEnd Complex) (eta psi (torsion F d) (s * b))) =
      -((torsion F d).card : Complex) ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_torsion_dilated_eta_mul_conj_eq_zero hpsi r s hrs]
  simp [eta, AddChar.map_zero_eq_one]
  ring

/-- The diagonal nonzero-frequency energy is `q|mu_d|-|mu_d|^2`. -/
theorem sum_nonzero_torsion_dilated_eta_normSq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) {d : Nat}
    (r : F) (hr : r ≠ 0) :
    (∑ b ∈ Finset.univ.erase (0 : F),
      eta psi (torsion F d) (r * b) *
        (starRingEnd Complex) (eta psi (torsion F d) (r * b))) =
      (Fintype.card F : Complex) * (torsion F d).card -
        ((torsion F d).card : Complex) ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_dilated_eta_mul_conj_eq_dilationCoincidenceCount hpsi,
    dilationCoincidenceCount_same (torsion F d) r hr]
  simp [eta, AddChar.map_zero_eq_one]
  ring

/-- Nonzero-frequency Gram matrix of a family of coloured period profiles. -/
noncomputable def nonzeroColourGram {K : Type*} [Fintype K]
    (psi : AddChar F Complex) (G : Finset F) (c : K -> F) (i j : K) : Complex :=
  ∑ b ∈ Finset.univ.erase (0 : F),
    eta psi G (c i * b) * (starRingEnd Complex) (eta psi G (c j * b))

/-- **Regular-simplex law.**  Any family of nonzero multipliers whose `d`-th powers are distinct
has a completely determined actual Gaussian-period Gram matrix: diagonal `q|mu_d|-|mu_d|^2`,
off diagonal `-|mu_d|^2`. -/
theorem torsion_nonzeroColourGram_eq_regularSimplex
    {K : Type*} [Fintype K] [DecidableEq K]
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) {d : Nat} (c : K -> F)
    (hc0 : ∀ i, c i ≠ 0) (hsep : Function.Injective fun i => c i ^ d) (i j : K) :
    nonzeroColourGram psi (torsion F d) c i j =
      if i = j then
        (Fintype.card F : Complex) * (torsion F d).card -
          ((torsion F d).card : Complex) ^ 2
      else -((torsion F d).card : Complex) ^ 2 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact sum_nonzero_torsion_dilated_eta_normSq hpsi (c i) (hc0 i)
  · rw [if_neg hij]
    apply sum_nonzero_torsion_dilated_eta_mul_conj_eq_neg_card_sq hpsi
    intro hpowers
    exact hij (hsep hpowers)

end PairLaw

/-! ## Exact first trajectory step: the missing midpoint-resonance law -/

section FirstTransition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Two unit weights, encoding the square `eta_b^2`. -/
def pairUnitWeights : Fin 2 -> F := fun _ => 1

/-- One doubled weight, encoding the colour `eta_(2b)`. -/
def pairDoubleWeight : Fin 1 -> F := fun _ => 2

/-- Reindex a one-coordinate constrained function sum. -/
private theorem sum_piFinset_fin1 {M : Type*} [AddCommMonoid M] (G : Finset F)
    (f : (Fin 1 -> F) -> M) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin 1 => G), f v = ∑ a ∈ G, f ![a] := by
  classical
  refine Finset.sum_nbij' (fun v => v 0) (fun a => ![a]) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    exact (Fintype.mem_piFinset.mp hv) 0
  · intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => by fin_cases i; simpa using ha)
  · intro v hv
    funext i
    fin_cases i
    rfl
  · intro a ha
    rfl
  · intro v hv
    congr 1
    funext i
    fin_cases i
    rfl

/-- Reindex a two-coordinate constrained function sum. -/
private theorem sum_piFinset_fin2 {M : Type*} [AddCommMonoid M] (G : Finset F)
    (f : (Fin 2 -> F) -> M) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G), f v =
      ∑ a ∈ G, ∑ b ∈ G, f ![a, b] := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun v => (v 0, v 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    have hmem := Fintype.mem_piFinset.mp hv
    exact Finset.mem_product.mpr ⟨hmem 0, hmem 1⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp0, hp1⟩
    exact Fintype.mem_piFinset.mpr (fun i => by fin_cases i <;> assumption)
  · intro v hv
    funext i
    fin_cases i <;> rfl
  · intro p hp
    rfl
  · intro v hv
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Representation count as an explicit ordered-pair indicator sum. -/
private theorem repCount_eq_double_sum (G : Finset F) (t : F) :
    ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G t =
      ∑ a ∈ G, ∑ b ∈ G, if a + b = t then 1 else 0 := by
  classical
  unfold ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount
  calc
    (G.filter fun a => t - a ∈ G).card =
        ∑ a ∈ G, if t - a ∈ G then 1 else 0 := by
      rw [Finset.card_filter]
    _ = ∑ a ∈ G, ∑ b ∈ G, if a + b = t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hmem : t - a ∈ G
      · rw [if_pos hmem, Finset.sum_eq_single (t - a)]
        · simp
        · intro b hb hne
          rw [if_neg]
          intro hab
          apply hne
          linear_combination hab
        · intro hnot
          exact (hnot hmem).elim
      · rw [if_neg hmem]
        symm
        apply Finset.sum_eq_zero
        intro b hb
        rw [if_neg]
        intro hab
        apply hmem
        have : t - a = b := by
          rw [← hab]
          abel
        exact this.symm ▸ hb

/-- Ordered additive energy of the source, written in the mixed-collision language. -/
noncomputable def pairAdditiveCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G pairUnitWeights pairUnitWeights

/-- The mixed-collision notation agrees with the standard two-fold additive energy. -/
theorem pairAdditiveCollisionCount_eq_rEnergy (G : Finset F) :
    pairAdditiveCollisionCount G = rEnergy G 2 := by
  classical
  unfold pairAdditiveCollisionCount mixedDilationCollisionCount rEnergy
  simp [weightedTupleSum, pairUnitWeights]

/-- Midpoint resonances `x+y=2z`; this is the cross term which deletes the pair diagonal. -/
noncomputable def midpointResonanceCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G pairUnitWeights pairDoubleWeight

/-- Midpoint resonances are the sum of the ordinary representation counts at the targets `2z`. -/
theorem midpointResonanceCount_eq_sum_repCount (G : Finset F) :
    midpointResonanceCount G =
      ∑ z ∈ G, ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G (2 * z) := by
  classical
  unfold midpointResonanceCount mixedDilationCollisionCount
  rw [sum_piFinset_fin2]
  simp only [weightedTupleSum, pairUnitWeights, pairDoubleWeight, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
  simp_rw [sum_piFinset_fin1]
  simp only [Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton,
    Matrix.cons_val_zero, Matrix.head_cons]
  change (∑ x ∈ G, ∑ y ∈ G, ∑ z ∈ G,
      if x + y = 2 * z then 1 else 0) =
    ∑ z ∈ G, ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G (2 * z)
  calc
    (∑ x ∈ G, ∑ y ∈ G, ∑ z ∈ G, if x + y = 2 * z then 1 else 0) =
        ∑ x ∈ G, ∑ z ∈ G, ∑ y ∈ G, if x + y = 2 * z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ z ∈ G, ∑ x ∈ G, ∑ y ∈ G,
          if x + y = 2 * z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ G, ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G (2 * z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [repCount_eq_double_sum]

/-- A pointwise representation bound along the doubled subgroup controls the entire midpoint
cross term.  This is the exact bridge from shifted intersections to the first Newton transition. -/
theorem midpointResonanceCount_le_card_mul_of_repBound (G : Finset F) (R : Nat)
    (hrep : ∀ z ∈ G,
      ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G (2 * z) ≤ R) :
    midpointResonanceCount G ≤ G.card * R := by
  rw [midpointResonanceCount_eq_sum_repCount]
  calc
    (∑ z ∈ G, ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount G (2 * z)) ≤
        ∑ z ∈ G, R := by
      apply Finset.sum_le_sum
      intro z hz
      exact hrep z hz
    _ = G.card * R := by simp

/-- Ordered-injective depth-two Fourier coefficient. -/
noncomputable def orderedDistinctPairPeriod
    (psi : AddChar F Complex) (G : Finset F) (b : F) : Complex :=
  eta psi G b ^ 2 - eta psi G ((2 : F) * b)

/-- **Exact first-step joint-period law.**  The full energy of the deleted-diagonal pair
transform is

`q * (A_2(G) + |G| - 2 M(G))`,

where `M(G)=#{(x,y,z) in G^3 : x+y=2z}`.  Thus colour orthogonality supplies the `+|G|`
term, while an improved transition can only come from a sufficiently large *positive* midpoint
cross correlation. -/
theorem sum_orderedDistinctPairPeriod_mul_conj_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (h2 : (2 : F) ≠ 0) :
    (∑ b : F, orderedDistinctPairPeriod psi G b *
      (starRingEnd Complex) (orderedDistinctPairPeriod psi G b)) =
      (Fintype.card F : Complex) *
        (pairAdditiveCollisionCount G + G.card - 2 * midpointResonanceCount G : Int) := by
  have hA : (∑ b : F, eta psi G b ^ 2 *
      (starRingEnd Complex) (eta psi G b ^ 2)) =
      (Fintype.card F : Complex) * pairAdditiveCollisionCount G := by
    simpa [pairUnitWeights, pairAdditiveCollisionCount, Finset.prod_const] using
      (sum_prod_dilated_eta_mul_conj_eq_collisionCount
        (I := Fin 2) (J := Fin 2) hpsi G pairUnitWeights pairUnitWeights)
  have hM : (∑ b : F, eta psi G b ^ 2 *
      (starRingEnd Complex) (eta psi G ((2 : F) * b))) =
      (Fintype.card F : Complex) * midpointResonanceCount G := by
    simpa [pairUnitWeights, pairDoubleWeight, midpointResonanceCount,
      Finset.prod_const] using
      (sum_prod_dilated_eta_mul_conj_eq_collisionCount
        (I := Fin 2) (J := Fin 1) hpsi G pairUnitWeights pairDoubleWeight)
  have hMrRaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
    (I := Fin 1) (J := Fin 2) hpsi G pairDoubleWeight pairUnitWeights
  rw [mixedDilationCollisionCount_swap G pairDoubleWeight pairUnitWeights] at hMrRaw
  have hMr : (∑ b : F, eta psi G ((2 : F) * b) *
      (starRingEnd Complex) (eta psi G b ^ 2)) =
      (Fintype.card F : Complex) * midpointResonanceCount G := by
    simpa [pairUnitWeights, pairDoubleWeight, midpointResonanceCount,
      Finset.prod_const] using hMrRaw
  have hB := sum_dilated_eta_mul_conj_eq_dilationCoincidenceCount hpsi G (2 : F) 2
  rw [dilationCoincidenceCount_same G 2 h2] at hB
  calc
    (∑ b : F, orderedDistinctPairPeriod psi G b *
        (starRingEnd Complex) (orderedDistinctPairPeriod psi G b)) =
        (∑ b : F, eta psi G b ^ 2 * (starRingEnd Complex) (eta psi G b ^ 2))
        + (∑ b : F, eta psi G ((2 : F) * b) *
            (starRingEnd Complex) (eta psi G ((2 : F) * b)))
        - (∑ b : F, eta psi G b ^ 2 *
            (starRingEnd Complex) (eta psi G ((2 : F) * b)))
        - (∑ b : F, eta psi G ((2 : F) * b) *
            (starRingEnd Complex) (eta psi G b ^ 2)) := by
      unfold orderedDistinctPairPeriod
      simp only [map_sub]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (Fintype.card F : Complex) * pairAdditiveCollisionCount G +
          (Fintype.card F : Complex) * G.card -
          (Fintype.card F : Complex) * midpointResonanceCount G -
          (Fintype.card F : Complex) * midpointResonanceCount G := by
      rw [hA, hB, hM, hMr]
    _ = (Fintype.card F : Complex) *
          (pairAdditiveCollisionCount G + G.card -
            2 * midpointResonanceCount G : Int) := by
      push_cast
      ring

/-- Removing frequency zero subtracts exactly the squared ordered-pair mass
`(|G|*(|G|-1))^2`. -/
theorem sum_nonzero_orderedDistinctPairPeriod_mul_conj_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (h2 : (2 : F) ≠ 0) :
    (∑ b ∈ Finset.univ.erase (0 : F), orderedDistinctPairPeriod psi G b *
      (starRingEnd Complex) (orderedDistinctPairPeriod psi G b)) =
      (Fintype.card F : Complex) *
          (pairAdditiveCollisionCount G + G.card - 2 * midpointResonanceCount G : Int) -
        ((G.card : Complex) * (G.card - 1)) ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_orderedDistinctPairPeriod_mul_conj_eq hpsi G h2]
  simp [orderedDistinctPairPeriod, eta, AddChar.map_zero_eq_one]
  ring

/-- Cleared-denominator form of a one-unit first-step improvement `c_1 <= 2`.  Here `A` is the
ordered additive energy and `M` is the midpoint-resonance count.  The left side is the nonzero
ordered-distinct-pair energy, while `2*(n-1)^2*(q-n)` is exactly twice the normalized singleton
budget after cancelling the common positive factor `n`. -/
def FirstStepOneUnitDefectLedger (q n A M : Int) : Prop :=
  q * (A + n - 2 * M) - (n * (n - 1)) ^ 2 ≤
    2 * (n - 1) ^ 2 * (q - n)

/-- Exact collision-law form of the first-step defect.  It demands a *lower* bound on midpoint
resonances, not an upper bound: the midpoint cross term must cancel enough additive energy. -/
theorem firstStepOneUnitDefectLedger_iff_midpointThreshold (q n A M : Int) :
    FirstStepOneUnitDefectLedger q n A M ↔
      q * (A + n) - (n - 1) ^ 2 * (n ^ 2 + 2 * (q - n)) ≤ 2 * q * M := by
  unfold FirstStepOneUnitDefectLedger
  constructor <;> intro h <;> nlinarith

/-- At the first production prime, even the minimal antipodal-pairing energy
`A >= 3n^2-3n` makes a one-unit first-step defect require more than `2^59` midpoint triples. -/
theorem production_firstStep_defect_forces_midpoint_gt_two_pow_59
    (A M : Int) (hA : 3 * (productionN : Int) ^ 2 - 3 * productionN ≤ A)
    (hdefect : FirstStepOneUnitDefectLedger productionP1 productionN A M) :
    (2 : Int) ^ 59 < M := by
  have ht := (firstStepOneUnitDefectLedger_iff_midpointThreshold
    (productionP1 : Int) productionN A M).mp hdefect
  have hq : (0 : Int) < productionP1 := by
    norm_num [productionP1, productionN]
  have hmono :
      (productionP1 : Int) *
          ((3 * (productionN : Int) ^ 2 - 3 * productionN) + productionN) -
          ((productionN : Int) - 1) ^ 2 *
            ((productionN : Int) ^ 2 + 2 * (productionP1 - productionN)) ≤
        2 * productionP1 * M := by
    calc
      (productionP1 : Int) *
          ((3 * (productionN : Int) ^ 2 - 3 * productionN) + productionN) -
          ((productionN : Int) - 1) ^ 2 *
            ((productionN : Int) ^ 2 + 2 * (productionP1 - productionN)) ≤
          (productionP1 : Int) * (A + productionN) -
            ((productionN : Int) - 1) ^ 2 *
              ((productionN : Int) ^ 2 + 2 * (productionP1 - productionN)) := by
        nlinarith
      _ ≤ 2 * productionP1 * M := ht
  norm_num [productionP1, productionN] at hmono ⊢
  omega

/-- The favorable classical shifted-intersection scale `2^22` would give at most
`n*2^22=2^52` midpoint triples.  Hence, if that cap is available, the first transition is
provably **not** the location of the one-unit Wick defect.  The remaining search must move to one
of depths `2 -> 3`, ..., `6 -> 7`, or distribute smaller savings across several steps. -/
theorem production_firstStep_no_oneUnitDefect_of_shiftedCap
    (A M : Int) (hA : 3 * (productionN : Int) ^ 2 - 3 * productionN ≤ A)
    (hM : M ≤ (productionN : Int) * 2 ^ 22) :
    ¬ FirstStepOneUnitDefectLedger productionP1 productionN A M := by
  intro hdefect
  have hlarge := production_firstStep_defect_forces_midpoint_gt_two_pow_59 A M hA hdefect
  norm_num [productionN] at hM
  omega

end FirstTransition

/-! ## The two production Gram matrices -/

/-- The first production torsion subgroup has exactly `2^30` elements. -/
theorem productionP1_torsion_card :
    (torsion (ZMod productionP1) productionN).card = productionN := by
  apply card_torsion
  · change productionN ∣ Fintype.card (ZMod productionP1) - 1
    simp only [ZMod.card]
    refine ⟨2 ^ 128 + 192, ?_⟩
    simp [productionP1]
  · norm_num [productionN]

/-- The second production torsion subgroup also has exactly `2^30` elements. -/
theorem productionP2_torsion_card :
    (torsion (ZMod productionP2) productionN).card = productionN := by
  apply card_torsion
  · change productionN ∣ Fintype.card (ZMod productionP2) - 1
    simp only [ZMod.card]
    refine ⟨2 ^ 129 + 13, ?_⟩
    simp [productionP2]
  · norm_num [productionN]

/-- The antipodal pairing floor used in the first-transition audit is unconditional for the
actual first production torsion subgroup. -/
theorem productionP1_pairAdditiveCollision_floor :
    3 * productionN ^ 2 - 3 * productionN ≤
      pairAdditiveCollisionCount (torsion (ZMod productionP1) productionN) := by
  let G : Finset (ZMod productionP1) := torsion (ZMod productionP1) productionN
  let psi : AddChar (ZMod productionP1) Complex :=
    AddChar.FiniteField.primitiveChar_to_Complex (ZMod productionP1)
  have hpsi : psi.IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod productionP1)
  have h2 : (2 : ZMod productionP1) ≠ 0 := by
    intro hzero
    have hdvd : productionP1 ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 productionP1).mp hzero
    norm_num [productionP1, productionN] at hdvd
  have h0 : (0 : ZMod productionP1) ∉ G := by
    intro hzero
    exact ne_zero_of_mem_torsion (F := ZMod productionP1)
      (by norm_num [productionN]) hzero rfl
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [mem_torsion] at hx ⊢
    rw [neg_pow]
    have heven : Even productionN := by
      refine ⟨2 ^ 29, ?_⟩
      norm_num [productionN, pow_succ]
    rw [Even.neg_one_pow heven, one_mul, hx]
  have hfloor :=
    ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed
      h2 h0 hneg
  have hGcard : G.card = productionN := by
    simpa only [G] using productionP1_torsion_card
  rw [pairAdditiveCollisionCount_eq_rEnergy,
    ArkLib.ProximityGap.REnergyTwoExact.rEnergy_two_eq_additiveEnergy hpsi]
  change 3 * productionN ^ 2 - 3 * productionN ≤
    ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy G
  rw [← hGcard]
  exact hfloor

/-- A `2^22` representation cap on nonzero shifts yields the advertised `2^52` bound for the
actual production midpoint term. -/
theorem productionP1_midpointResonance_le_of_nonzeroRepCap
    (hrep : ∀ t : ZMod productionP1, t ≠ 0 →
      ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount
        (torsion (ZMod productionP1) productionN) t ≤ 2 ^ 22) :
    midpointResonanceCount (torsion (ZMod productionP1) productionN) ≤
      productionN * 2 ^ 22 := by
  calc
    midpointResonanceCount (torsion (ZMod productionP1) productionN) ≤
        (torsion (ZMod productionP1) productionN).card * 2 ^ 22 := by
      apply midpointResonanceCount_le_card_mul_of_repBound
      intro z hz
      apply hrep
      apply mul_ne_zero
      · intro hzero
        have hdvd : productionP1 ∣ 2 :=
          (ZMod.natCast_eq_zero_iff 2 productionP1).mp hzero
        norm_num [productionP1, productionN] at hdvd
      · exact ne_zero_of_mem_torsion (by norm_num [productionN]) hz
    _ = productionN * 2 ^ 22 := by rw [productionP1_torsion_card]

theorem productionP1_colour_ne_zero (j : Fin 7) :
    (colourMultiplier j : ZMod productionP1) ≠ 0 := by
  fin_cases j <;>
    simp only [colourMultiplier, ne_eq, ZMod.natCast_eq_zero_iff] <;>
    norm_num [productionP1, productionN]

theorem productionP2_colour_ne_zero (j : Fin 7) :
    (colourMultiplier j : ZMod productionP2) ≠ 0 := by
  fin_cases j <;>
    simp only [colourMultiplier, ne_eq, ZMod.natCast_eq_zero_iff] <;>
    norm_num [productionP2, productionN]

/-- Exact seven-colour regular-simplex Gram law at the first production prime. -/
theorem productionP1_actual_seven_colour_gram
    {psi : AddChar (ZMod productionP1) Complex} (hpsi : psi.IsPrimitive) (i j : Fin 7) :
    nonzeroColourGram psi (torsion (ZMod productionP1) productionN)
        (fun k => colourMultiplier k) i j =
      if i = j then
        (productionP1 : Complex) * productionN - (productionN : Complex) ^ 2
      else -(productionN : Complex) ^ 2 := by
  rw [torsion_nonzeroColourGram_eq_regularSimplex hpsi
    (fun k : Fin 7 => (colourMultiplier k : ZMod productionP1))
    productionP1_colour_ne_zero productionP1_colourPowers_injective i j,
    productionP1_torsion_card]
  simp

/-- Exact seven-colour regular-simplex Gram law at the second production prime. -/
theorem productionP2_actual_seven_colour_gram
    {psi : AddChar (ZMod productionP2) Complex} (hpsi : psi.IsPrimitive) (i j : Fin 7) :
    nonzeroColourGram psi (torsion (ZMod productionP2) productionN)
        (fun k => colourMultiplier k) i j =
      if i = j then
        (productionP2 : Complex) * productionN - (productionN : Complex) ^ 2
      else -(productionN : Complex) ^ 2 := by
  rw [torsion_nonzeroColourGram_eq_regularSimplex hpsi
    (fun k : Fin 7 => (colourMultiplier k : ZMod productionP2))
    productionP2_colour_ne_zero productionP2_colourPowers_injective i j,
    productionP2_torsion_card]
  simp

/-! ## Quantitative boundary of the pairwise joint law -/

/-- Exact leakage required to turn the primitive Wick coefficient `135135` into `126871`. -/
def requiredLeakage : Nat := (8264 * productionN + 135135 - 1) / 135135

/-- Required leakage as a fraction of the production subgroup. -/
def requiredLeakageFraction : Rat := requiredLeakage / productionN

/-- Absolute off-diagonal/diagonal ratio of the first production Gram matrix. -/
def productionP1PairCorrelation : Rat := productionN / (productionP1 - productionN)

/-- Absolute off-diagonal/diagonal ratio of the second production Gram matrix. -/
def productionP2PairCorrelation : Rat := productionN / (productionP2 - productionN)

theorem requiredLeakage_exact : requiredLeakage = 65663244 := by
  norm_num [requiredLeakage, productionN]

/-- The needed correlated-placement saving is between `1/17` and `1/16` of all units. -/
theorem requiredLeakageFraction_window :
    (1 : Rat) / 17 < requiredLeakageFraction ∧ requiredLeakageFraction < (1 : Rat) / 16 := by
  norm_num [requiredLeakageFraction, requiredLeakage, productionN]

/-- Pairwise colour correlation is below `2^-128` at P1 and below `2^-129` at P2. -/
theorem productionPairCorrelation_bit_windows :
    productionP1PairCorrelation < (1 : Rat) / 2 ^ 128 ∧
      productionP2PairCorrelation < (1 : Rat) / 2 ^ 129 := by
  norm_num [productionP1PairCorrelation, productionP2PairCorrelation,
    productionP1, productionP2, productionN]

/-- **Pairwise-moment scale boundary.**  The actual coefficient saving is more than `2^123`
times the P1 pair-correlation ratio and more than `2^124` times the P2 ratio.  Thus the exact
regular-simplex law is a strong realizability constraint, but its raw bidegree-`(1,1)` scale is
123--124 bits below the required `65,663,244`-unit placement effect.  Higher weighted collisions
from `sum_prod_dilated_eta_mul_conj_eq_collisionCount` must do the quantitative work. -/
theorem production_pairCorrelation_misses_leakage_by_123_124_bits :
    (2 ^ 123 : Rat) * productionP1PairCorrelation < requiredLeakageFraction ∧
      (2 ^ 124 : Rat) * productionP2PairCorrelation < requiredLeakageFraction := by
  norm_num [productionP1PairCorrelation, productionP2PairCorrelation,
    requiredLeakageFraction, requiredLeakage, productionP1, productionP2, productionN]

/-! ## Axiom audit -/

#print axioms squareTower_eq_pow
#print axioms productionP1_colourPowers_injective
#print axioms productionP2_colourPowers_injective
#print axioms sum_prod_dilated_eta_mul_conj_eq_collisionCount
#print axioms midpointResonanceCount_eq_sum_repCount
#print axioms sum_orderedDistinctPairPeriod_mul_conj_eq
#print axioms production_firstStep_defect_forces_midpoint_gt_two_pow_59
#print axioms productionP1_pairAdditiveCollision_floor
#print axioms productionP1_midpointResonance_le_of_nonzeroRepCap
#print axioms nonzero_septic_crossMoment_nonnegative_iff
#print axioms septic_crossMoment_real_lower
#print axioms torsion_nonzeroColourGram_eq_regularSimplex
#print axioms productionP1_actual_seven_colour_gram
#print axioms productionP2_actual_seven_colour_gram
#print axioms production_pairCorrelation_misses_leakage_by_123_124_bits

end ArkLib.ProximityGap.Frontier.BGKActualJointPeriodLaw
