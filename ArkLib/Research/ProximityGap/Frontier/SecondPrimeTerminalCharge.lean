/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeChartPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeOrdinaryPolarCharge
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPolarGcd
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusIrreducible

/-! # The ordinary-polar charge on a common chart of the remaining cubic -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeTerminalCharge
open Finset Polynomial SecondPrimeCoordinateWeight SecondPrimeScalarChart
open SecondPrimeActualPopulations
open SecondPrimeMobiusSections SecondPrimeReceivedJetColumns SecondPrimeOrdinaryPolarCharge
open MovingCubicVanishingBranch CanonicalQuarticSiteOrder HalfPredecessorLineCoreGeometry
open WeightedSylvesterDegree SecondPrimeCubicWindowCount
open scoped NNReal

variable {F K I : Type} [Fintype I] [Nonempty I] [Field F] [DecidableEq F]
  [Field K] [Infinite K] {p : ℕ} [CharP K p] {dom : I ↪ F} {δ : ℝ≥0}
  {u : Code.WordStack F (Fin 2) I}

omit [Infinite K] in
private theorem polar_chart (r a : K) (W d : ℕ) (f : Surface K) :
    polarRes (scalarChart (surfaceChart r W d f)) a =
      IntegralOrdinaryPolars.polarResultant (SecondPrimeActualPolarGcd.fieldChart r W d f)
        (RatFunc.C a) := by
  rfl

omit [Infinite K] [DecidableEq F] in
private theorem common_divisor (φ : F →+* K) (f : Surface K) (r : K) (W : ℕ)
    (hw : W = weight 67108863 f) (hlo : 201326589 ≤ W) (hhi : W ≤ 290805098)
    (hb : f.natDegree = 3) (htr : TotalDegreeLe f 34) (S : Finset F)
    (hs : 1342177085 ≤ S.card) (w : F → K[X])
    (hr : ∀ z ∈ S, (surfaceChart r W 67108863 f).eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hd : ∀ z ∈ S, ((surfaceChart r W 67108863 f).derivative.eval₂
      (evalRingHom (C (φ z))) (w z)).natDegree = W - 67108863) (a b : K) :
    open scoped Classical in
    polarRes (scalarChart (surfaceChart r W 67108863 f)) a ≠ 0 →
      polarRes (scalarChart (surfaceChart r W 67108863 f)) b ≠ 0 →
      2 * (W - 67108863) ≤ (GCDMonoid.gcd
        (polarRes (scalarChart (surfaceChart r W 67108863 f)) a)
        (polarRes (scalarChart (surfaceChart r W 67108863 f)) b)).natDegree + 201 := by
  simp only [polar_chart]
  exact SecondPrimeActualPolarGcd.gcd_of_cubic_chart φ f r W hw hlo hhi hb htr S hs w hr hd a b

omit [Infinite K] [DecidableEq F] in
private theorem common_divisor_of_chart (φ : F →+* K) (f g : Surface K)
    (r : K) (W d : ℕ) (hdim : d = 67108863) (hw : W = weight d f)
    (hg : g = surfaceChart r W d f)
    (hlo : 201326589 ≤ W) (hhi : W ≤ 290805098) (hb : f.natDegree = 3)
    (htr : TotalDegreeLe f 34) (S : Finset F) (hs : 1342177085 ≤ S.card)
    (w : F → K[X])
    (hr : ∀ z ∈ S, g.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hd : ∀ z ∈ S, (g.derivative.eval₂ (evalRingHom (C (φ z))) (w z)).natDegree = W - d) :
    open scoped Classical in
    ∀ a b : K, a ≠ b → polarRes (scalarChart g) a ≠ 0 → polarRes (scalarChart g) b ≠ 0 →
      2 * (W - d) ≤ (GCDMonoid.gcd (polarRes (scalarChart g) a)
        (polarRes (scalarChart g) b)).natDegree + 201 := by
  subst g d
  intro a b _
  exact common_divisor φ f r W hw hlo hhi hb htr S hs w hr hd a b

private theorem compare_gcd {L : Type*} [Field L] (M N : GCDMonoid L[X]) (A B : L[X])
    (hA : A ≠ 0) : (@GCDMonoid.gcd _ _ M A B).natDegree ≤ (@GCDMonoid.gcd _ _ N A B).natDegree :=
  Polynomial.natDegree_le_of_dvd
    (@GCDMonoid.dvd_gcd _ _ N _ _ _ (@GCDMonoid.gcd_dvd_left _ _ M A B)
      (@GCDMonoid.gcd_dvd_right _ _ M A B)) (@gcd_ne_zero_of_left _ _ N A B hA)

omit [DecidableEq F] in
private theorem charge_of_chart_gcd (r : K) (f g : Surface K) (W d : ℕ)
    (hdim : d = 67108863) (hw : W = weight d f) (hg : g = surfaceChart r W d f)
    (φ : F →+* K) (hlo : 201326589 ≤ W) (hhi : W ≤ 290805098) (hb : f.natDegree = 3)
    (htr : TotalDegreeLe f 34) (S : Finset F) (hs : 1342177085 ≤ S.card) (w : F → K[X])
    (hr : ∀ z ∈ S, g.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hd : ∀ z ∈ S, (g.derivative.eval₂ (evalRingHom (C (φ z))) (w z)).natDegree = W - d)
    (hp : 3 < p) (hg3 : (scalarChart g).natDegree = 3) (hpr : (scalarChart g).IsPrimitive)
    (hi : Irreducible (genericEquation (scalarChart g)))
    (hnd : ¬genericEquation (scalarChart g) ∣ genericEquation (scalarFieldHessian (scalarChart g)))
    (hw₀ : 3 * d ≤ W) (hw₁ : Bivariate.natWeightedDegree (scalarChart g) 1 d ≤ W)
    (hchar : 6 * W < p) (D : Finset K) (u v : K → K) :
    3 * (∑ x ∈ D, siteOrder (scalarChart g) (RatFunc.C x)
       (C (RatFunc.C (u x) + RatFunc.X * RatFunc.C (v x)))) + 35 * d ≤
       2 * D.card + 16 * W + 2 * 201 := by
  apply charge_of_persistent_gcd p hp (scalarChart g) hg3 hpr hi hnd d W 201 hw₀ hw₁ hchar D u v
  intro a b hab hA hB
  have h := common_divisor_of_chart φ f g r W d hdim hw hg hlo hhi hb htr S hs w hr hd
    a b hab hA hB
  refine h.trans (Nat.add_le_add_right ?_ _)
  exact compare_gcd _ _ _ _ hA

omit [DecidableEq F] in
private theorem low_weight_chart_charge (r : K) (f g : Surface K) (W d : ℕ)
    (hdim : d = 67108863) (hw : W = weight d f) (hg : g = surfaceChart r W d f)
    (φ : F →+* K) (hlo : 201326589 ≤ W) (hhi : W ≤ 290805098) (hb : f.natDegree = 3)
    (htr : TotalDegreeLe f 34) (S : Finset F) (hs : 1342177085 ≤ S.card) (w : F → K[X])
    (hr : ∀ z ∈ S, g.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hd : ∀ z ∈ S, (g.derivative.eval₂ (evalRingHom (C (φ z))) (w z)).natDegree = W - d)
    (hchar : 1320000000 < p) (hsmall : W < 220000000)
    (hg3 : g.natDegree = 3) (hirr : Irreducible g) (hgw : weight d g = W)
    (hnd : ¬ genericEquation (scalarChart g) ∣
      genericEquation (scalarFieldHessian (scalarChart g))) :
    ∀ (A : Finset K) (u v : K → K), 3 * (∑ x ∈ A, siteOrder (scalarChart g) (RatFunc.C x)
       (C (RatFunc.C (u x) + RatFunc.X * RatFunc.C (v x)))) + 35 * d ≤
       2 * A.card + 16 * W + 2 * 201 := by
  have hpos : 0 < g.natDegree := by rw [hg3]; decide
  have hp₀ := (chart_irreducible g hirr hpos).isPrimitive (by rw [value_degree, hg3]; decide)
  apply charge_of_chart_gcd r f g W d hdim hw hg φ hlo hhi hb htr S hs w hr hd
    ((by decide : 3 ≤ 1320000000).trans_lt hchar) ((value_degree g).trans hg3)
    hp₀ (generic_irreducible g hirr hpos) hnd
  · simpa only [hdim] using hlo
  · exact (chart_weight g d).trans hgw.le
  · exact (Nat.mul_le_mul_left 6 hsmall.le).trans_lt hchar

omit [Infinite K] in
private theorem charge_on_embedding (D : I ↪ K) (a b : I → K) (g : Surface K) (W d : ℕ)
    (hd : d = 67108863) (hw : weight d g = W) (hn : Fintype.card I = 1073741824)
    (h : ∀ (A : Finset K) (u v : K → K),
      3 * (∑ x ∈ A, siteOrder (scalarChart g) (RatFunc.C x)
        (C (RatFunc.C (u x) + RatFunc.X * RatFunc.C (v x)))) + 35 * d ≤
        2 * A.card + 16 * W + 2 * 201) :
    SufficientCharge (SecondPrimeChartPopulation.orders D a b g) (weight d g) := by
  classical
  let inv := Function.invFun D
  have hinv (i : I) : inv (D i) = i := Function.leftInverse_invFun D.injective i
  have hbudget := h (univ.map D) (a ∘ inv) (b ∘ inv)
  simp only [sum_map, Function.comp_apply, hinv, card_map, card_univ, hn] at hbudget
  apply Or.inl
  rw [hw, ← hd]
  exact hbudget.trans (Nat.add_le_add_left (by decide : 2 * 201 ≤ 532) _)

/-- For a populous cubic, the same coordinate chart supplies the common polar divisor,
the received-order budget and the cap on the simple sections. -/
theorem population_cap (fam : Family dom δ u) (φ : F →+* K)
    (hp : 1320000000 < p) (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (Q f : Surface K) (hQ : Q ≠ 0) (hi : Irreducible f) (hdiv : f ∣ Q)
    (hb : f.natDegree = 3)
    (shape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (hsmall : weight 67108863 f < 220000000) :
    (population fam φ f).card < 1342177249 := by
  classical
  by_contra! hbig
  let d := 67108863
  let W := weight d f
  have hc : (3 : K) ≠ 0 := by
    intro he
    have h := (CharP.cast_eq_zero_iff K p 3).mp he
    have := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  have htr := SecondPrimeSectionResultant.factor_triangle hQ hdiv shape
  obtain ⟨r, _, S, hS, hcount, hall⟩ := actual_cubic_chart fam φ f Q hc hi hb hQ hdiv shape
  let g := surfaceChart r W d f
  have hirr : Irreducible g := SecondPrimeMobiusIrreducible.irreducible_surfaceChart r d f hi
    (by omega)
  let w := fun z => chart r d ((fam.q z).map φ)
  let D := SecondPrimeChartPopulation.coordinate (dom.trans (⟨φ, φ.injective⟩ : F ↪ K)) r
  let row := fun j i => (D i) ^ d * φ (u j i)
  have hl : 201326589 ≤ W := by
    have h₁ := leadingCoeff_ne_zero.mpr hi.ne_zero
    have h₂ := leadingCoeff_ne_zero.mpr h₁
    have h := coeff_weight_le d f (leadingCoeff_ne_zero.mpr h₂)
    rw [hb] at h
    dsimp only [W, d] at *
    omega
  change W < 220000000 at hsmall
  have hs : 1342177085 ≤ S.card := by omega
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < S.card by omega)
  have hGW : weight d g = W := surface_weight_eq_of_simple_degree r (φ z) d f (w z)
    (hall z hz).1 (by change d < W; dsimp [d]; omega) (hall z hz).2.2.1
  have hg3 : g.natDegree = 3 := (surface_value_degree r W d f).trans hb
  have hu : W ≤ 290805098 := hsmall.le.trans (by decide)
  have roots (x) (hx : x ∈ S) : g.eval₂ (evalRingHom (C (φ x))) (w x) = 0 :=
    (hall x hx).2.1
  have derivs (x) (hx : x ∈ S) :
      (g.derivative.eval₂ (evalRingHom (C (φ x))) (w x)).natDegree = W - d :=
    (hall x hx).2.2.1
  have charge (hnd : ¬genericEquation (scalarChart g) ∣
      genericEquation (scalarFieldHessian (scalarChart g))) :
      SufficientCharge (SecondPrimeChartPopulation.orders D (row 0) (row 1) g) (weight d g) := by
    apply charge_on_embedding D (row 0) (row 1) g W d rfl hGW hn
    exact low_weight_chart_charge r f g W d rfl rfl rfl φ hl hu hb htr S hs w roots derivs
      hp hsmall hg3 hirr hGW hnd
  have coordinate_eq (i : I) : D i = (φ (dom i) - r)⁻¹ := rfl
  have fit (x : F) (hx : x ∈ S) :
      (w x).natDegree ≤ 67108863 ∧ ∃ T : Finset I, 357913943 ≤ T.card ∧
        ∀ i ∈ T, (w x).eval (D i) = row 0 i + φ x * row 1 i := by
    refine ⟨(hall x hx).1, _, ht.trans (fam.threshold_le x (mem_filter.mp (hS hx)).1), ?_⟩
    intro i hit
    change (w x).eval (D i) =
      D i ^ d * φ (u 0 i) + φ x * (D i ^ d * φ (u 1 i))
    rw [coordinate_eq]
    exact (hall x hx).2.2.2 i hit
  have bound := SecondPrimeChartPopulation.cap φ D (row 0) (row 1) g hirr hg3
    (surface_triangle r W d f 34 htr) hn (hGW.le.trans hu) (p := p)
    ((by decide : 276 ≤ 1320000000).trans_lt hp) charge S w roots fit
  exact (by decide : ¬ 1342177085 ≤ 1200005270) (hs.trans bound)

/-- Every received pair at this predecessor stays within the budget of two labels per site. -/
theorem actual_bad_labels [Finite F] [IsAlgClosed K] (fam : Family dom δ u) (φ : F →+* K)
    (hp : 1320000000 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913943) :
    fam.G.card ≤ 2147483648 := by
  by_contra! hmore
  obtain ⟨Q, f, hQ, hs, hi, hd, hb, hpop, hw, _, _⟩ :=
    SecondPrimeSmallCubic.actual_exception fam φ (p := p) (by omega) hn ht hmore
  have cap := population_cap fam φ hp hn ht.ge Q f hQ hi hd hb
    (fun j i a ha => (hs j i a ha).2.1) hw
  exact cap.not_ge ((by decide : 1342177249 ≤ 1431655733).trans hpop)

section Named
open _root_.ProximityGap.TerminalCollinearHeadCount
open _root_.ProximityGap ArkLib.ProximityGap.KKH26
open HalfPredecessorBadEventRichPointBridge
open scoped ENNReal
private abbrev P := PrizeShapePrimeP30Second.P
local instance : Fact P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- The rate-one-sixteenth MCA boundary at the second named prime is exactly
715827882 errors divided by the length. -/
theorem threshold :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2^30) (2^26-1)) (epsStar : ℝ≥0∞) =
        (715827882 : ℝ≥0)/1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hcard
  have ht : ⌈(1 - (715827881 : ℝ≥0)/1073741824) *
      (Fintype.card (Fin (2^30)) : ℝ≥0)⌉₊ = 357913943 :=
    TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
  have cap := actual_bad_labels fam (algebraMap (ZMod P) (AlgebraicClosure (ZMod P)))
    (p := P) (by decide) (Fintype.card_fin _) ht
  have hbad : 2147483649 ≤ 2147483648 := hcard ▸ (card_le_card hG).trans cap
  exact False.elim ((by decide : ¬ 2147483649 ≤ 2147483648) hbad)
end Named

#print axioms threshold
#print axioms actual_bad_labels
#print axioms population_cap
end ArkLib.ProximityGap.Frontier.SecondPrimeTerminalCharge
