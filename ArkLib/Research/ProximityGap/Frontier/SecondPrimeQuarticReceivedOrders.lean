/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticWeightBound
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder

/-! # Actual received-line multiplicity budget of a terminal quartic component -/

open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeQuarticReceivedOrders

open SecondPrimeScalarChart SecondPrimeCoordinateWeight CanonicalQuarticSiteOrder
open HalfPredecessorBadEventRichPointBridge

variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq F]

/-- Every irreducible quartic carrying enough genuine bad sections has actual total local
order at most 1412316443 on the nondivisible reverse-Hessian branch. No weight, generic
irreducibility, derivative bounds, or local orders are external inputs. -/
theorem actual_order_budget (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f)
    (hb : f.natDegree = 4)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (G : Finset F) (hG : G ⊆ fam.G) (hlarge : 646 < G.card)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0)
    (hnd : ¬ MovingCubicVanishingBranch.genericEquation (scalarChart f) ∣
      MovingCubicVanishingBranch.genericEquation (scalarFieldHessian (scalarChart f))) :
    ∑ i : ι, siteOrder (scalarChart f) (RatFunc.C (φ (dom i)))
      (C (RatFunc.C (φ (u 0 i)) + RatFunc.X * RatFunc.C (φ (u 1 i)))) ≤ 1412316443 := by
  classical
  let D := dom.trans (⟨φ, φ.injective⟩ : F ↪ K)
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn ▸ by decide)
  let inv := Function.invFun D
  have hinv (i : ι) : inv (D i) = i := Function.leftInverse_invFun D.injective i
  have hW := SecondPrimeQuarticWeightBound.actual_quartic_weight φ dom δ u hn ht fam Q f
    hQ hdiv hi hb htri G hG hlarge hroot
  have h := secondPrime_quartic_received_budget (scalarChart f) ((value_degree f).trans hb)
    (generic_irreducible f hi (by omega)) hnd ((chart_weight f _).trans hW)
    (univ.map D) (by simpa using hn) (fun z => φ (u 0 (inv z))) (fun z => φ (u 1 (inv z)))
  change ∑ i : ι, siteOrder (scalarChart f) (RatFunc.C (D i))
    (C (RatFunc.C (φ (u 0 i)) + RatFunc.X * RatFunc.C (φ (u 1 i)))) ≤ _
  simpa only [sum_map, hinv] using h

#print axioms actual_order_budget
end ArkLib.ProximityGap.Frontier.SecondPrimeQuarticReceivedOrders
