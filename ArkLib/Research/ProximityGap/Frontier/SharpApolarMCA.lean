/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChartData
import ArkLib.Research.ProximityGap.Frontier.ApolarGenericCoprime
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarThreshold
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold
import ArkLib.Research.ProximityGap.Frontier.ApolarSpikeBudgetRange

/-! # Reduction of the scalar bad-event count to a normalized chart bound

The normalized polynomial receives its weights from the code. To bound the
number of bad scalars, `family_bound_of_chart` assumes that each qualifying
chart has at most `3 * (l + 1)` bad parameters, where `l` is its height.
-/

set_option autoImplicit false
open Finset Polynomial Code ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarDividedPolynomial
open ProximityGap.ApolarRootTransition ProximityGap.ApolarCoordinateEquations
open ProximityGap.ApolarUnitChartData
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SharpApolarMCA

private theorem specialize_measure {K : Type*} [Field K] (D : Finset K) (w : K → K[X])
    (t : K) (p : K[X]) :
    ((measure D (C : K → K[X]) w) (p.map C)).eval t =
      weighted D (RingHom.id K) (fun i => (w i).eval t) p := by
  classical
  rw [show (measure D C w (p.map C)).eval t = (evalRingHom t) (measure D C w (p.map C)) from rfl,
    ← measure_map]
  have hs : (evalRingHom t).comp (C : K →+* K[X]) = RingHom.id K := by ext x; simp
  simp [weighted, _root_.ProximityGap.ApolarRootTransition.measure, Polynomial.map_map, hs,
    Function.comp_def]

private theorem coprime_data {K : Type*} [Field K] [DecidableEq K] {H S : Finset K}
    {e d r l : ℕ} (A : Data H S e d r l) (hr : 0<r) (hd : r≤d) :
    let φ := algebraMap K[X] (FractionRing K[X])
    IsCoprime (A.f.map φ) ((representative A.D C A.w A.f).map φ) := by
  have hr1 : r-1+1=r := by omega
  have ha : A.f.natDegree=r-1+1 := A.degree.trans hr1.symm
  apply ApolarGenericCoprime.generic_coprime A.D (C : K → K[X]) A.w A.f (r-1) (d-r) ha A.apolar
  simpa only [show d-r+1=d-(r-1) by omega] using A.minimal (r-1) (by omega)

private theorem real_sparse {K : Type*} [Field K] [DecidableEq K] {H S : Finset K}
    {e d r l : ℕ} (A : Data H S e d r l) (hlen : e≤d-r+1) (t : K) (ht : t∈A.G) :
    ∃ E ⊆ A.D, E.card ≤ d-r+1 ∧ ∃ b : K → K, ∀ p : K[X], p.natDegree≤d →
      weighted A.D (RingHom.id K) (fun i => (A.w i).eval t) p =
      weighted E (RingHom.id K) b p := by
  obtain ⟨E,hE,hn,b,hforward,_⟩ := A.sparse t ht
  refine ⟨E,hE,hn.trans hlen,b,?_⟩
  intro p hp
  rw [← specialize_measure]
  exact hforward p hp

open scoped Classical in
private theorem family_bound_of_chart
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hed : e≤d) (hlen : 2*e≤d+1) (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (he : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊)
    (hcoord : Fintype.card ι < 3*(d+2-e)+e)
    (hchart : ∀ {H S : Finset (AlgebraicClosure F)} {r l : ℕ}
      (A : Data H S e d r l), 0<r → 0<l → r≤e → 0<A.G.card →
      A.D.card<3*(d+2-r)+r → A.G.card≤3*(l+1)) :
    bad.card ≤ max (e+1) (3*(e/(d+2-2*e)+1)) := by
  classical
  by_cases hsmall : bad.card≤e+1
  · exact hsmall.trans (le_max_left ..)
  have hlarge : e+1<bad.card := by omega
  let L := AlgebraicClosure F
  let φ := algebraMap F L
  obtain ⟨r,hre,l,hr,hl,hdegree,⟨A⟩⟩ := of_mca_family φ fam bad hsub hlarge hed hlen hk hd he
  have hn : A.D.card=Fintype.card ι := by rw [A.card_sites];simp
  have hg : A.G.card=bad.card := by rw [A.card_parameters];simp
  have hG := hchart A hr hl hre (by omega) (by omega)
  have h' : l*(d+2-2*e)≤e := (Nat.mul_le_mul_left l (by omega : d+2-2*e ≤ d+2-2*r)).trans
    (by simpa only [Nat.mul_comm l] using hdegree.trans hre)
  have hquot := (Nat.le_div_iff_mul_le (by omega : 0<d+2-2*e)).2 h'
  rw [hg] at hG
  exact (hG.trans (by omega)).trans (le_max_right ..)

#print axioms specialize_measure
#print axioms coprime_data
#print axioms real_sparse
#print axioms family_bound_of_chart

end ArkLib.ProximityGap.Frontier.SharpApolarMCA
