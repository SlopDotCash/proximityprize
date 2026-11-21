/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmallCubic
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusSections
import ArkLib.Research.ProximityGap.Frontier.OrdinaryPolarCappedGcd
import ArkLib.Research.ProximityGap.Frontier.TerminalFactorCoverage

/-! # Cubic sections in an over-budget family at the named predecessor

The actual quadratic and quartic population caps leave one irreducible cubic. Its
scalar Hessian is proper, and all but at most 130 selected sections are simple.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicWitness
open Polynomial Finset SecondPrimeActualPopulations SecondPrimeScalarChart
open SecondPrimeMobiusSections
open CanonicalQuarticSiteOrder (scalarFieldHessian)
open MovingCubicVanishingBranch (genericEquation)
open scoped NNReal

open _root_.ProximityGap.TerminalFactorCoverage (Supported)

variable {F K I : Type} [Field F] [DecidableEq F] [Field K] [Fintype I] {dom : I ↪ F}
  {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- An actual violation forces an irreducible nonflat cubic with the indicated coordinate
weight, total population, and a separate lower bound on its simple sections. -/
theorem actual_cubic [Finite F] [Nonempty I] [IsAlgClosed K] (fam : Family dom δ u)
    (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 715827884 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q f : Factor K, Q ≠ 0 ∧ Supported Q ∧
      Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧
      SecondPrimeCoordinateWeight.weight 67108863 f < 220000000 ∧
      1431655733 ≤ (population fam φ f).card ∧
      1431655603 ≤ (simplePopulation fam φ f).card ∧
      (¬genericEquation (scalarChart f) ∣ genericEquation (scalarFieldHessian (scalarChart f))) ∧
      2 * 1073741824 + 16 * SecondPrimeCoordinateWeight.weight 67108863 f + 532 <
        3 * SecondPrimeSmallCubic.orders dom u φ f + 35 * 67108863 := by
  classical
  obtain ⟨Q, f, hQ, hs, hi, hd, hy, hpop, hw, hproper, hexcess⟩ :=
    SecondPrimeSmallCubic.actual_exception fam φ hp hn ht hbig
  have hc : (3 : K) ≠ 0 := by
    intro he
    have hh := (CharP.cast_eq_zero_iff K p 3).mp he
    exact (by omega : ¬p ≤ 3) (Nat.le_of_dvd (by decide) hh)
  have total := simple_card fam φ f Q hc hi hy hQ hd (fun j i a ha ↦ (hs j i a ha).2.1)
  exact ⟨Q, f, hQ, hs, hi, hd, hy, hw, hpop, by omega, hproper, hexcess⟩

/-- On the remaining weight interval, squares on the actual simple labels force the
generic polar gcd to contain all but at most 111 orders of the doubled residual. -/
theorem polar_defect (fam : Family dom δ u) (φ : F →+* K) (f : Factor K)
    (hS : 1431655603 ≤ (simplePopulation fam φ f).card)
    (A B : K[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (W : ℕ) (hlo : 201326589 ≤ W) (hhi : W < 220000000)
    (hAD : A.natDegree ≤ 6 * W - 9 * 67108863 - 3)
    (hBD : B.natDegree ≤ 6 * W - 9 * 67108863 - 3)
    (hAH : Bivariate.degreeX A ≤ 195) (hBH : Bivariate.degreeX B ≤ 195)
    (R : F → K[X]) (hsq : ∀ z ∈ simplePopulation fam φ f,
      (R z).natDegree = W - 67108863 ∧
      R z ^ 2 ∣ A.map (evalRingHom (φ z)) ∧ R z ^ 2 ∣ B.map (evalRingHom (φ z))) :
    2 * (W - 67108863) ≤ OrdinaryPolarGcdBudget.genericDegree A B + 111 := by
  classical
  let S := (simplePopulation fam φ f).map ⟨φ, φ.injective⟩
  let q (z : K) := R (Function.invFun φ z)
  have hsq' (z : K) (hz : z ∈ S) :
      q z ≠ 0 ∧ (q z).natDegree = W - 67108863 ∧
      q z ^ 2 ∣ A.map (evalRingHom z) ∧ q z ^ 2 ∣ B.map (evalRingHom z) := by
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
    change R (Function.invFun φ (φ w)) ≠ 0 ∧ _
    simp only [q, Function.Embedding.coeFn_mk, Function.leftInverse_invFun φ.injective w]
    obtain ⟨hdegree, ha, hb⟩ := hsq w hw
    exact ⟨fun h => by rw [h, natDegree_zero] at hdegree; omega, hdegree, ha, hb⟩
  have h := OrdinaryPolarCappedGcd.gcd_budget A B hA hB _ 195 (W - 67108863)
    hAD hBD hAH hBH (by omega) S q hsq'
  have hs : 1431655603 ≤ S.card := by simpa [S] using hS
  have := (Nat.mul_le_mul_right (2 * (W - 67108863) - OrdinaryPolarGcdBudget.genericDegree A B)
    hs).trans h
  omega

section Named
open Code HalfPredecessorBadEventRichPointBridge
open _root_.ProximityGap _root_.ProximityGap.TerminalCollinearHeadCount
open ArkLib.ProximityGap.KKH26 PrizeShapeRateHalfBracket
open scoped ENNReal

private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The one remaining simple-section estimate on the named predecessor domain. -/
def SimpleCubicCap : Prop :=
  ∀ u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ 30)),
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2 ^ 26)
      ((715827881 : ℝ≥0) / 1073741824) u (by decide)
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    ∀ Q f : Factor (AlgebraicClosure (ZMod p)), Q ≠ 0 → Supported Q →
      Irreducible f → f ∣ Q → f.natDegree = 3 →
      SecondPrimeCoordinateWeight.weight 67108863 f < 220000000 →
      (¬genericEquation (scalarChart f) ∣
        genericEquation (scalarFieldHessian (scalarChart f))) →
      2 * 1073741824 + 16 * SecondPrimeCoordinateWeight.weight 67108863 f + 532 <
        3 * SecondPrimeSmallCubic.orders secondDomain u φ f + 35 * 67108863 →
      (simplePopulation fam φ f).card ≤ 1431655602

/-- The single cubic estimate at the predecessor implies the operational radius equality. -/
theorem secondPrime_threshold_of_simple_cubic (h : SimpleCubicCap) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (evalCode g (2 ^ 30) (2 ^ 26 - 1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0) / 1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hsize
  let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  have hc : 2147483648 < fam.G.card := by
    have hs := Finset.card_le_card hG
    omega
  obtain ⟨Q, f, hQ, hs, hi, hd, hy, hw, _, hpopulation, hproper, hexcess⟩ :=
    actual_cubic fam φ (by decide : 715827884 < p) (Fintype.card_fin _)
      (TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)) hc
  exact False.elim ((by decide : ¬1431655603 ≤ 1431655602)
    (hpopulation.trans (h u Q f hQ hs hi hd hy hw hproper hexcess)))

end Named

#print axioms secondPrime_threshold_of_simple_cubic
#print axioms actual_cubic
#print axioms polar_defect
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicWitness
