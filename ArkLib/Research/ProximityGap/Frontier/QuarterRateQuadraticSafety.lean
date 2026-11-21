/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier.QuarterRateApolarBracket
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # The exact two-head numerator on a length-$2^{30}$ quarter-rate interval

A degree-34 interpolant of value degree two covers every selected witness at
631612837 agreements. A populous irreducible component is necessarily a secant.
Every sufficiently large subfamily therefore supplies a large joint core.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateQuadraticSafety

open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private theorem interpolation_capacity :
    1073741824 * (34+1) < Fintype.card (Monomials 34 2 268435455 631612837) := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

set_option maxRecDepth 8192 in
/-- The actual bad scalar count is at most twice the number of errors plus two throughout
the quarter-rate interval. The domain may be any injection into a field of large characteristic. -/
theorem family_cap (fam : BadScalarRichPointFamily dom 268435456 δ u) {e t : ℕ}
    (hn : Fintype.card I = 1073741824) (hsum : e + t = 1073741824)
    (he : 402653184 ≤ e) (htmin : 631612837 ≤ t)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = t)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0) :
    fam.G.card ≤ 2 * e + 2 := by
  classical
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m := 478) (t := 631612837) fam (by decide) (by decide)
      _ M hM hm U hn (htmin.trans ht.ge)
    intro c a b l v hc hinc hcover ha hb hl
    omega
  obtain ⟨c, hc, _, witness⟩ := exists_curve (s := 34) (v := 2) (d := 268435455) dom (u 0) (u 1) (by decide : 0 < 631612837)
    (by rw [hn]; exact interpolation_capacity)
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have shape {j i a : ℕ} (h : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 2 ∧ i+j ≤ 34 ∧ a+j*268435455 < 631612837 := surface_support c h
  have scalar (j : ℕ) : (Q.coeff j).natDegree ≤ 34 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext a
    simp only [coeff_zero]
    by_contra h
    have := (shape h).2.1
    omega
  have val : Q.natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (shape h).1
  let φ := RingHom.id F
  let pop (f : F[X][X][X]) := fam.G.filter fun z =>
    f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  have population_eq (f : F[X][X][X])
      (d : DecidablePred fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
      @Finset.filter F _ d fam.G = pop f := by
    ext z
    simp only [pop, mem_filter]
  have roots (z : F) (hz : z ∈ fam.G) :
      Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    simp only [Q, φ, Polynomial.map_id, RingHom.id_apply, surface_eval]
    apply witness _ _ (by have := fam.degree_lt z hz; omega) (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (htmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  obtain ⟨P,E,hP,prim,hPQ,hval,_,hE,after⟩ := SecondPrimePrimitiveSurface.primitive_surface
    φ hQ fam.G (fun z => (fam.q z).map φ) 34 scalar roots
  obtain ⟨U, factors, _, hnum, hits⟩ := SecondPrimePrimitiveSurface.factor_cover P hP prim
  let V := U.toFinset
  have hV : V.card ≤ 2 := U.toFinset_card_le.trans (hnum.trans (hval.le.trans val))
  have cover (z : F) (hz : z ∈ fam.G) (he : z ∉ E) : ∃ f ∈ V, z ∈ pop f := by
    obtain ⟨f, hf, hroot⟩ := hits _ _ (after z hz he)
    exact ⟨f, Multiset.mem_toFinset.mpr hf, mem_filter.mpr ⟨hz,hroot⟩⟩
  let zmin := t - 1048576
  apply TwoLargeCoreCount.card_le_two_mul_add_two fam (zmin := zmin) (by decide) (by omega)
    (hn.trans hsum.symm) ht (by rw [hn]; dsimp [zmin]; omega)
  intro H hH hsize
  have some_large : ∃ f ∈ V, 1024 < (H ∩ pop f).card := by
    by_contra! hall
    have hsub : H ⊆ E ∪ V.biUnion (fun f => H ∩ pop f) := by
      intro z hz
      by_cases ze : z ∈ E
      · exact mem_union_left _ ze
      · obtain ⟨f,hf,hzpop⟩ := cover z (hH hz) ze
        exact mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_inter.mpr ⟨hz,hzpop⟩⟩)
    have htotal := (card_le_card hsub).trans ((card_union_le ..).trans
      (Nat.add_le_add_left card_biUnion_le E.card))
    have hc := sum_le_sum hall
    simp only [sum_const,smul_eq_mul] at hc
    omega
  obtain ⟨f,hf,hbig⟩ := some_large
  obtain ⟨hirr,hpos,hdiv⟩ := factors f (Multiset.mem_toFinset.mp hf)
  have hdivQ := hdiv.trans hPQ
  have hd := (natDegree_le_of_dvd hdivQ hQ).trans val
  have hpop : 1024 < (pop f).card := hbig.trans_le (card_le_card inter_subset_right)
  have htot := factor_totalDegree_le hQ hdivQ (fun _ _ _ h => (shape h).2.1)
  have hlin : f.natDegree = 1 := by
    by_contra hnon
    have hquad : f.natDegree = 2 := by omega
    have hbound := SecondPrimeQuadraticFactor.quadratic_population_of_extraction
      (w := 631612836) (m := 511) fam φ Q f hQ hdivQ hirr hquad
      (fun _ _ _ h => ⟨(shape h).2.1, by have := (shape h).2.2; omega⟩)
      (by decide) hchar extract
    rw [population_eq f] at hbound
    omega
  obtain ⟨p,hp,hcarry⟩ := linear_factor_is_head_of_extraction (m := 511) fam φ f hirr hlin
    htot extract (by rw [population_eq f]; omega)
  rw [population_eq f] at hcarry
  have hcar : H ∩ pop f ⊆ pointsOn fam p := inter_subset_right.trans hcarry
  have hL : 1024 ≤ (pointsOn fam p).card := hbig.le.trans (card_le_card hcar)
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < (H ∩ pop f).card by omega)
  refine ⟨a,(mem_inter.mp ha).1,b,(mem_inter.mp hb).1,hab,?_⟩
  rw [secantParameter_eq_of_mem_pointsOn fam p (hcar ha) (hcar hb) hab]
  have pack := pointsOn_card_mul_max_add_core_le fam hp
  rw [ht,hn] at pack
  let core := (jointCore dom (u 0) (u 1) p.1 p.2).card
  have packed : 1024 * (t-core) ≤ 1073741824 :=
    (Nat.mul_le_mul hL (le_max_right 1 (t-core))).trans (by exact (Nat.le_add_right _ _).trans pack)
  change t - 1048576 ≤ core
  omega

/-- The exact worst-case two-row failure mass at every integer error count in the interval. -/
theorem exact_mass (dom : I ↪ F) (hn : Fintype.card I = 1073741824) {e : ℕ}
    (he : 402653184 ≤ e) (hu : e ≤ 442128987)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) ((e : ℝ≥0) / Fintype.card I)
      = ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let δ : ℝ≥0 := e / Fintype.card I
    let fam := canonicalBadScalarRichPointFamily dom δ u (by decide : 1 ≤ 268435456)
    change fam.G.card ≤ 2*(e+1)
    have hc : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 1073741824-e := by
      dsimp only [δ]
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ hc, ← Nat.cast_tsub, Nat.ceil_natCast, hn]
    simpa only [Nat.mul_add,Nat.mul_one] using
      family_cap fam hn (t := 1073741824-e) (by omega) he (by omega) ht hchar
  · exact TwoHeadLinearBudget.errors dom (by omega) (by omega) (by omega)

open ArkLib.ProximityGap.PrizeShapePrimeP30 P1RateQuarterCanonicalCodeBridge
open P1RateQuarterScaleArithmetic _root_.ProximityGap.MCAThresholdLedger PrizeShapeRateHalfBracket

local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

/-- The first-prime first bad grid point is between 442128988 and 480946859 inclusive. -/
theorem named_bracket :
    let radius := mcaDeltaStar (F := ZMod P) canonicalCode ((((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹)
    (442128988 : ℝ≥0)/1073741824 ≤ radius ∧ radius ≤ 480946859/1073741824 := by
  dsimp only
  refine ⟨?_, QuarterRateApolarBracket.named_bracket.2⟩
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 442128988)
    (by decide) (by decide : 442128988 ≤ N)
  change epsMCA (F := ZMod P) canonicalCode ((442128987 : ℝ≥0) / N) ≤ _
  have mass := exact_mass canonicalDomain (Fintype.card_fin _) (e := 442128987)
    (by decide) (by decide) (by
      intro i hi hj hc
      have hP : 1263225672 < P := by decide
      exact (lt_of_le_of_lt hj hP).not_ge
        (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod P) P i).mp hc)))

  rw [Fintype.card_fin, ZMod.card] at mass
  exact mass.le.trans (natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide) prime_P.pos (by decide))

/-- Across this interval of integer 128-bit budgets every positive-width MCA test
passes precisely below the grid point picked by half the budget. -/
theorem budget_window (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 884257977)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0)
    (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  classical
  let e := B/2
  let r : ℝ≥0 := (e : ℝ≥0)/1073741824
  let r₀ : ℝ≥0 := ((e-1 : ℕ) : ℝ≥0)/1073741824
  let C := (ReedSolomon.code dom 268435456 : Set (I → F))
  have hlo : 402653185 ≤ e := by dsimp [e]; omega
  have hhi : e ≤ 442128988 := by dsimp [e]; omega
  have ratio (m : ℕ) :
      ((m : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞)) ↔ m ≤ B := by
    rw [epsStar_coe_eq_natCast_inv, ← one_div, ← hB]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide)
  have good : epsMCA (F := F) C r₀ ≤ (epsStar : ℝ≥0∞) := by
    have h := exact_mass dom hn (e := e-1) (by omega) (by omega) hchar
    rw [hn] at h
    rw [show epsMCA (F := F) C r₀ = _ from h, ratio]
    dsimp [e]
    omega
  have bad : (epsStar : ℝ≥0∞) < epsMCA (F := F) C r := by
    have h := TwoHeadLinearBudget.errors (k := 268435456) (e := e) dom (by omega) (by omega) (by omega)
    rw [hn] at h
    apply lt_of_lt_of_le _ h
    apply lt_of_not_ge
    rw [ratio]
    dsimp [e]
    omega
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) 268435456
  have radius : mcaDeltaStar (F := F) C (epsStar : ℝ≥0∞) = r := by
    dsimp only [C]
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a := e)
      (by omega) (by omega)
    · rw [← hre]
      exact good
    · rw [← hre]
      exact bad
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact radius, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! hδ
    exact bad.not_ge ((epsMCA_mono C hδ).trans safe)
  · intro hδ
    by_contra! unsafeAt
    have bound := mcaDeltaStar_le_of_bad C (epsStar : ℝ≥0∞) unsafeAt
    rw [radius] at bound
    exact hδ.not_ge bound

/-- The field-order budget on a prime field automatically gives the characteristic bound. -/
theorem prime_budget_window {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I = 1073741824) (hB : p / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 884257977) (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  apply budget_window dom hn (by simpa only [ZMod.card] using hB) hl hu _ width
  intro i hi hj hz
  exact (show ¬p ≤ i by omega) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp hz))

#print axioms budget_window
#print axioms prime_budget_window

#print axioms family_cap
#print axioms exact_mass
#print axioms named_bracket

end ArkLib.ProximityGap.Frontier.QuarterRateQuadraticSafety
