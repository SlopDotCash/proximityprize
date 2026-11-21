/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeProperCubic
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualCubicCap
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The outstanding low-weight cubic charge at the second prime

At the last safe error count of the written proof, a violation requires a proper
cubic with weight below 220000000 whose actual received multiplicities exceed an
explicit integer bound. The theorem applies to the original received rows.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeSmallCubic
open Finset Polynomial SecondPrimeActualPopulations SecondPrimeScalarChart
open SecondPrimeCoordinateWeight CanonicalQuarticSiteOrder MovingCubicVanishingBranch
open scoped NNReal ENNReal

variable {I F K : Type} [Fintype I] [Nonempty I] [Field F] [Finite F] [DecidableEq F]
  [Field K] [IsAlgClosed K] {p : ℕ} [CharP K p]
  {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- Sum the exact multiplicities at the original received lines over the coordinate domain. -/
noncomputable def orders (D : I ↪ F) (rows : Code.WordStack F (Fin 2) I) (φ : F →+* K)
    (f : Factor K) : ℕ :=
  ∑ i : I, siteOrder (scalarChart f) (RatFunc.C (φ (D i)))
    (C (RatFunc.C (φ (rows 0 i)) + RatFunc.X * RatFunc.C (φ (rows 1 i))))

/-- A budget violation forces a small proper cubic whose genuine multiplicity sum is too high. -/
theorem actual_exception (fam : Family dom δ u) (φ : F →+* K) (hp : 715827884 < p)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ (Q f : Factor K), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧ 1431655733 ≤ (population fam φ f).card ∧
      weight 67108863 f < 220000000 ∧
      (¬ genericEquation (scalarChart f) ∣ genericEquation (scalarFieldHessian (scalarChart f))) ∧
      2 * 1073741824 + 16 * weight 67108863 f + 532 <
        3 * orders dom u φ f + 35 * 67108863 := by
  classical
  obtain ⟨Q,f,hQ,shape,hi,hdiv,h3,hpop,_,hnd⟩ :=
    SecondPrimeProperCubic.actual_cubic fam φ hp hn ht hbig
  have tri (j i a : ℕ) (h : ((Q.coeff j).coeff i).coeff a ≠ 0) : i + j ≤ 34 :=
    (shape j i a h).2.1
  have small : weight 67108863 f < 220000000 := by
    by_contra! large
    have cap := SecondPrimeActualCubicCap.population_cap fam φ hn ht.ge Q f hQ hdiv hi h3
      tri large hnd
    omega
  refine ⟨Q,f,hQ,shape,hi,hdiv,h3,hpop,small,hnd,?_⟩
  by_contra! bound
  have cap := SecondPrimeCubicIntrinsicEscape.actual_cubic_cap φ dom δ u hn ht.ge fam
    Q f hQ hdiv hi h3 tri (population fam φ f) (filter_subset _ _)
    (fun _ hz => (mem_filter.mp hz).2) (Or.inl bound)
  omega

section NamedDomain
open _root_.ProximityGap.TerminalCollinearHeadCount
open HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.KKH26
open PrizeShapeRateHalfBracket

private abbrev P := PrizeShapePrimeP30Second.P
local instance : Fact P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩
private abbrev Kbar := AlgebraicClosure (ZMod P)
private noncomputable abbrev embed := algebraMap (ZMod P) Kbar

/-- The multiplicity inequality on the one remaining class of actual cubic factors.
The inequality is only needed on factors with a large population at the predecessor. -/
def SmallCubicCharge : Prop :=
  ∀ u : Code.WordStack (ZMod P) (Fin 2) (Fin (2^30)),
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
      ((715827881 : ℝ≥0)/1073741824) u (by decide)
    ∀ Q f : Factor Kbar, Q ≠ 0 →
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) →
      Irreducible f → f ∣ Q → f.natDegree = 3 → 1431655733 ≤ (population fam embed f).card →
      weight 67108863 f < 220000000 →
      (¬ genericEquation (scalarChart f) ∣ genericEquation (scalarFieldHessian (scalarChart f))) →
      3 * orders secondDomain u embed f + 35 * 67108863 ≤
        2 * 1073741824 + 16 * weight 67108863 f + 532

/-- Closing the small cubic charge gives the exact operational threshold of this named code.
The independent three-core attack supplies the matching failure at 715827882. -/
theorem threshold_of_small_cubic_charge (hcharge : SmallCubicCharge) :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2^30) (2^26-1)) (_root_.ProximityGap.epsStar : ℝ≥0∞) =
        (715827882 : ℝ≥0)/1073741824 := by
  classical
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hcard
  exfalso
  have hc : G.card ≤ fam.G.card := card_le_card hG
  have ht : ⌈(1 - (715827881 : ℝ≥0)/1073741824) *
      (Fintype.card (Fin (2^30)) : ℝ≥0)⌉₊ = 357913943 := by
    exact TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
  obtain ⟨Q, f, hQ, shape, hi, hdiv, h3, hpop, hw, hproper, hexcess⟩ :=
    actual_exception fam embed (p := P) (by decide) (Fintype.card_fin _) ht (by omega)
  exact (Nat.not_le_of_gt hexcess) (hcharge u Q f hQ shape hi hdiv h3 hpop hw hproper)
end NamedDomain

#print axioms threshold_of_small_cubic_charge
#print axioms actual_exception
end ArkLib.ProximityGap.Frontier.SecondPrimeSmallCubic
