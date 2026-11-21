/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarCubicObstruction
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChartData
import ArkLib.Research.ProximityGap.Frontier.ApolarGenericCoprime
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarThreshold
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold
import ArkLib.Research.ProximityGap.Frontier.ApolarSpikeBudgetRange

/-! # Sharp apolar bound on the actual scalar bad event

The normalized polynomial receives its weights from the real code. Its
division obstruction gives the improved rate-half cap at the last Hamming
step preceding one quarter.
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
  simp [weighted,_root_.ProximityGap.ApolarRootTransition.measure,Polynomial.map_map,hs]

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

private theorem family_bound_power_of_chart (power : ℕ) (hpower : 0 < power)
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq (AlgebraicClosure F)]
    {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hed : e≤d) (hlen : 2*e≤d+1) (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (he : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊)
    (hcoord : Fintype.card ι < power *(d+2-e)+e)
    (hchart : ∀ {H S : Finset (AlgebraicClosure F)} {r l : ℕ}
      (A : Data H S e d r l), 0<r → 0<l → r≤e → 0<A.G.card →
      A.D.card<power *(d+2-r)+r → A.G.card≤power *(l+1)) :
    bad.card ≤ max (e+1) (power *(e/(d+2-2*e)+1)) := by
  classical
  by_cases hsmall : bad.card≤e+1
  · exact hsmall.trans (le_max_left ..)
  have hlarge : e+1<bad.card := by omega
  let L := AlgebraicClosure F
  let φ := algebraMap F L
  obtain ⟨r,hre,l,hr,hl,hdegree,⟨A⟩⟩ := of_mca_family φ fam bad hsub hlarge hed hlen hk hd he
  have hn : A.D.card=Fintype.card ι := by rw [A.card_sites];simp
  have hg : A.G.card=bad.card := by rw [A.card_parameters];simp
  have hmul : e-r ≤ power*(e-r) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (e-r) (show 1≤power from hpower)
  have hwidth : d+2-r = d+2-e+(e-r) := by omega
  have hG := hchart A hr hl hre (by omega) (by
    rw [hn,hwidth,Nat.mul_add]
    omega)
  have h' : l*(d+2-2*e)≤e := (Nat.mul_le_mul_left l (by omega : d+2-2*e ≤ d+2-2*r)).trans
    (by simpa only [Nat.mul_comm l] using hdegree.trans hre)
  have hquot := (Nat.le_div_iff_mul_le (by omega : 0<d+2-2*e)).2 h'
  rw [hg] at hG
  exact (hG.trans (Nat.mul_le_mul_left power (by omega))).trans (le_max_right ..)

private theorem cap_of_family {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=1073741824)
    (hFam : ∀ {dom : Fin 1073741824 ↪ ZMod p} {u : WordStack (ZMod p) (Fin 2) (Fin 1073741824)}
      (fam : BadScalarRichPointFamily dom 536870912 ((268435455:ℝ≥0)/1073741824) u),
      fam.G.card ≤ 268435458) : RateHalfApolarThreshold.PredecessorCap g := by
  classical
  let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
  have hc : RateHalfApolarThreshold.code g = (ReedSolomon.code dom 536870912 : Set (Fin 1073741824 → ZMod p)) := by
    exact KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg) 536870911
  intro u
  rw [hc]
  exact hFam (canonicalBadScalarRichPointFamily dom _ u (by decide))

private theorem window_of_cap {p B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = 1073741824)
    (hB : B=p/2^128) (hlo : 268435458≤B) (hhi : B≤536870913) (cap : RateHalfApolarThreshold.PredecessorCap g) :
    let star := fun k => mcaDeltaStar (F := ZMod p) (FourRatePairBudget.code g k) (epsStar:ℝ≥0∞)
    star (2^29)=1/4 ∧ star (2^28)=((min B 402653184:ℕ):ℝ≥0)/1073741824 ∧
    star (2^27)=((min B 469762048:ℕ):ℝ≥0)/1073741824 ∧
    star (2^26)=((min B 503316480:ℕ):ℝ≥0)/1073741824 := by
  refine ⟨RateHalfApolarThreshold.threshold hg (by omega) (by omega) cap,?_,?_,?_⟩
  · exact ApolarSpikeBudgetRange.lower_rate_budget hg (by decide) (by decide) (by decide) hB
      (by omega) (by omega)
  · exact ApolarSpikeBudgetRange.lower_rate_budget hg (by decide) (by decide) (by decide) hB
      (by omega) (by omega)
  · exact ApolarSpikeBudgetRange.lower_rate_budget hg (by decide) (by decide) (by decide) hB
      (by omega) (by omega)

/-- For every positive interpolation power satisfying the coordinate inequality, bound the
number of genuinely bad Reed–Solomon scalars on any finite injective evaluation
domain. -/
theorem family_bound_power (power : ℕ) (hpower : 0 < power)
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hed : e≤d) (hlen : 2*e≤d+1) (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (he : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊)
    (hcoord : Fintype.card ι < power *(d+2-e)+e) :
    bad.card ≤ max (e+1) (power *(e/(d+2-2*e)+1)) := by
  classical
  apply family_bound_power_of_chart power hpower fam bad hsub hed hlen hk hd he hcoord
  intro H S r l A hr hl hre hG hcard
  apply _root_.ProximityGap.ApolarCubicObstruction.card_le_power power hpower A.D A.G A.w A.f hr (by omega) hl
    A.degree A.top_height A.bottom_nonzero A.height A.primitive A.weights_affine A.sites_unit
    A.parameters_unit (Finset.card_pos.mp hG) hcard A.apolar (coprime_data A hr (by omega))
  exact real_sparse A (by omega)

/-- Uniform cubic apolar bound for the actual Reed–Solomon bad scalar family
whenever the coordinate inequality and the distance constraints hold. -/
theorem family_bound
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hed : e≤d) (hlen : 2*e≤d+1) (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (he : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊)
    (hcoord : Fintype.card ι < 3*(d+2-e)+e) :
    bad.card ≤ max (e+1) (3*(e/(d+2-2*e)+1)) :=
  family_bound_power 3 (by decide) fam bad hsub hed hlen hk hd he hcoord

/-- At the rate-half predecessor of length 2³⁰, all received pairs on every
injective evaluation domain have at most 268435458 genuinely bad scalars. -/
theorem rate_half_family {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom 536870912 δ u) (hn : Fintype.card ι=1073741824)
    (hthreshold : 805306369 ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) : fam.G.card ≤ 268435458 := by
  have h := family_bound (e:=268435455) (d:=536870911) fam fam.G Finset.Subset.rfl
    (by decide) (by decide) (by decide) (by rw [hn];decide) (by rw [show Fintype.card ι-268435455=805306369 by omega];exact hthreshold) (by rw [hn];decide)
  exact h

/-- The sharp safe-side predecessor on every smooth production-length subgroup. -/
theorem predecessor_cap {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=1073741824) :
    RateHalfApolarThreshold.PredecessorCap g := by
  apply cap_of_family hg
  intro dom u fam
  apply rate_half_family fam (Fintype.card_fin _)
  exact (TwoCorePackingThreshold.agreement_ceiling 268435455 (by decide)).ge

/-- All four exact official-rate thresholds throughout the half-rate plateau. -/
theorem four_rate_window {p B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=1073741824)
    (hB : B=p/2^128) (hlo : 268435458≤B) (hhi : B≤536870913) :
    let star := fun k => mcaDeltaStar (F := ZMod p) (FourRatePairBudget.code g k) (epsStar:ℝ≥0∞)
    star (2^29)=1/4 ∧ star (2^28)=((min B 402653184:ℕ):ℝ≥0)/1073741824 ∧
    star (2^27)=((min B 469762048:ℕ):ℝ≥0)/1073741824 ∧
    star (2^26)=((min B 503316480:ℕ):ℝ≥0)/1073741824 :=
  window_of_cap hg hB hlo hhi (predecessor_cap hg)

/-- The named lower endpoint of the sharply certified production field range. -/
theorem boundary_prime :
    mcaDeltaStar (F := ZMod RateHalfApolarBudget.Boundary.P)
      (RateHalfApolarThreshold.code RateHalfApolarBudget.Boundary.generator) (epsStar:ℝ≥0∞) = 1/4 :=
  RateHalfApolarThreshold.boundary_prime (predecessor_cap RateHalfApolarBudget.Boundary.generator_order)

/-- The companion prime with a budget one larger has the same threshold. -/
theorem boundary_plus_one :
    mcaDeltaStar (F := ZMod RateHalfApolarBudget.P)
      (RateHalfApolarThreshold.code RateHalfApolarBudget.generator) (epsStar:ℝ≥0∞) = 1/4 :=
  RateHalfApolarThreshold.budget_plus_three (predecessor_cap RateHalfApolarBudget.generator_order)

/-- The rate-half good-radius predicate is strict at one quarter for every
positive finite interleaving width throughout the sharp budget band. -/
theorem interleaved_good_iff {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=1073741824)
    (hlo : 268435458 ≤ p/2^128) (hhi : p/2^128 ≤ 536870913)
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := Fin width → ZMod p)
      ((RateHalfApolarThreshold.code g) ^⋈ (Fin width)) δ ≤ (epsStar:ℝ≥0∞) ↔ δ < 1/4 :=
  RateHalfApolarThreshold.interleaved_good_iff hg hlo hhi (predecessor_cap hg) width δ

#print axioms family_bound_power
#print axioms specialize_measure
#print axioms coprime_data
#print axioms real_sparse
#print axioms family_bound_power_of_chart
#print axioms predecessor_cap
#print axioms family_bound
#print axioms rate_half_family
#print axioms four_rate_window
#print axioms boundary_prime
#print axioms boundary_plus_one
#print axioms interleaved_good_iff

end ArkLib.ProximityGap.Frontier.SharpApolarMCA
