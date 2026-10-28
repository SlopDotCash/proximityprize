/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceTripleMass
import Research.ProximityPrize.Frontier._IncidenceAffineLines
import Research.ProximityPrize.Frontier._IncidenceAverageAnchor

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.IncidenceCanonicalTriples

open ProximityGap.IncidenceTripleMass ProximityGap.IncidenceAffineLines

/-- Triple-incidence mass excludes an over-budget family of canonical bad witnesses.
The support predicate is the unfolded minimum-distance bound for the code. -/
theorem no_bad_witness_family_of_triple_budget
    {F I Coord A : Type} [Field F] [Fintype I] [DecidableEq I]
    [Fintype Coord] [Nonempty Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (C : Submodule F (Coord → A)) (d t s : ℕ) (hs : 2 ≤ s)
    (htn : t ≤ Fintype.card Coord)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → A)
    (hwC : ∀ i, w i ∈ C)
    (hcompl : ∀ i, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (hbig : s * Fintype.card Coord ^ 2 * (d + 1) * Fintype.card I ^ 3 +
        s * (Fintype.card I * (Fintype.card Coord - t)) ^ 3 >
      s * Fintype.card Coord ^ 3 * Fintype.card I ^ 3 +
        Fintype.card Coord ^ 2 * (d + 1) *
          (s * Fintype.card I * (t + 1) ^ 2 + 3 * Fintype.card I ^ 3 +
            s ^ 2 * Fintype.card I ^ 2 + 3 * s * Fintype.card I ^ 2)) : False := by
  classical
  have hpad : ∀ i, ∃ E : Finset Coord, (T i)ᶜ ⊆ E ∧ E.card = t := by
    intro i
    obtain ⟨E,hTE,_,hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ ((T i)ᶜ)) (hcompl i) (by simpa using htn)
    exact ⟨E,hTE,hcard⟩
  choose E hTE hEcard using hpad
  have hlow := bad_witness_triple_mass_lower gamma w hinj Finset.univ C d t s hs
    hC T u0 u1 (fun i _ => hwC i) (fun i _ => hcompl i)
    (fun i _ => hwag i) (fun i _ => hno i)
  simp only [Finset.card_univ] at hlow
  have hmono : (∑ a, ∑ b, ∑ c, (((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ).card) ≤
      ∑ a, ∑ b, ∑ c, (E a ∪ E b ∪ E c).card := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro c _
    exact Finset.card_le_card
      (Finset.union_subset_union (Finset.union_subset_union (hTE a) (hTE b)) (hTE c))
  have hmonoS := Nat.mul_le_mul_left s hmono
  have hlowN := Nat.mul_le_mul_left (Fintype.card Coord ^ 2) hlow
  have hmonoN := Nat.mul_le_mul_left (Fintype.card Coord ^ 2) hmonoS
  have hupp := triple_union_mass_bound E t hEcard
  have huppS := Nat.mul_le_mul_left s hupp
  nlinarith [hlowN,hmonoN,huppS,hbig]

open ProximityGap ProximityGap.SpikeFloor Code
open scoped NNReal ENNReal

/-- Triple incidence bounds the number of canonical MCA-bad scalars. -/
theorem badScalars_card_le_of_triple_budget
    {F Coord A : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Submodule F (Coord → A)) (j d t s : ℕ) (hs : 2 ≤ s)
    (htn : t ≤ Fintype.card Coord) (hC : NoWeightLE C d)
    (hbig : s * Fintype.card Coord ^ 2 * (d + 1) * (j + 1) ^ 3 +
        s * ((j + 1) * (Fintype.card Coord - t)) ^ 3 >
      s * Fintype.card Coord ^ 3 * (j + 1) ^ 3 +
        Fintype.card Coord ^ 2 * (d + 1) *
          (s * (j + 1) * (t + 1) ^ 2 + 3 * (j + 1) ^ 3 +
            s ^ 2 * (j + 1) ^ 2 + 3 * s * (j + 1) ^ 2))
    {δ : ℝ≥0} (hδ : δ * (Fintype.card Coord : ℝ≥0) < t + 1)
    (u0 u1 : Coord → A) :
    (Finset.univ.filter fun γ : F => mcaEvent (C : Set (Coord → A)) δ u0 u1 γ).card ≤ j := by
  classical
  by_contra hgt
  push Not at hgt
  obtain ⟨B,hBsub,hBcard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (fun γ : F => mcaEvent (C : Set (Coord → A)) δ u0 u1 γ))
    (n := j + 1) (by omega)
  let gamma : Fin (j + 1) → F :=
    fun i => (B.equivFin.symm (Fin.cast hBcard.symm i) : F)
  have hinj : Function.Injective gamma := by
    intro a b hab
    have h1 := Subtype.val_injective hab
    have h2 := B.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have hbad : ∀ i, mcaEvent (C : Set (Coord → A)) δ u0 u1 (gamma i) := fun i =>
    (Finset.mem_filter.mp (hBsub (B.equivFin.symm (Fin.cast hBcard.symm i)).2)).2
  choose T hTsz hwEx hno using hbad
  choose w hwC hwag using hwEx
  have hcompl : ∀ i, (T i)ᶜ.card ≤ t := by
    intro i
    simpa using (witness_compl_card_le (j := t + 1) (by simpa using hδ) (hTsz i))
  apply no_bad_witness_family_of_triple_budget gamma w hinj C d t s hs htn
    hC T u0 u1 hwC hcompl hwag hno
  simpa only [Fintype.card_fin] using hbig

open ProximityGap.Ownership
private abbrev sponsorP := ArkLib.ProximityGap.PrizeShapePrimeP30.P
private abbrev sponsorG := ArkLib.ProximityGap.PrizeShapePrimeP30.g
private instance sponsorPrime : Fact sponsorP.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

set_option maxRecDepth 4096 in
/-- Canonical first-sponsor incidence at the integer triple-mass boundary. -/
theorem firstPrime_triple_incidence :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
      (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((210683555 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) (2 ^ 30) := by
  classical
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  let dom : Fin (2 ^ 30) ↪ ZMod sponsorP :=
    smoothDom sponsorG (2 ^ 30) ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  have hcode : ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1) =
      ((rsCode dom (2 ^ 29) : Submodule (ZMod sponsorP) (Fin (2 ^ 30) → ZMod sponsorP)) :
        Set (Fin (2 ^ 30) → ZMod sponsorP)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 29)] using
      (evalCode_eq_rsCode ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g (2 ^ 29 - 1))
  intro u
  rw [hcode]
  apply badScalars_card_le_of_triple_budget
    (j := 2 ^ 30) (d := 2 ^ 29) (t := 210683555) (s := 56755)
  · norm_num
  · norm_num
  · exact rsCode_noWeightLE dom (by norm_num)
  · norm_num
  · norm_num

open ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

/-- The triple-incidence budget yields a canonical unconditional first-sponsor floor. -/
theorem firstPrime_triple_floor :
    ((210683556 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) ≤
      mcaDeltaStar (F := ZMod sponsorP) (A := ZMod sponsorP)
        (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ℝ≥0∞) := by
  classical
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hbudget : ((2 ^ 30 : ℕ) : ℝ≥0∞) / (sponsorP : ℝ≥0∞) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hb := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128) (p := sponsorP)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos
      (by norm_num [sponsorP, ArkLib.ProximityGap.PrizeShapePrimeP30.P])
    rwa [epsStar_coe_eq_natCast_inv]
  have hgood : epsMCA (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) 210683556) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hc := ProximityGap.OpenCoreConditionalPin.epsMCA_le_of_worstCaseIncidence
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((210683555 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) firstPrime_triple_incidence
    rw [ZMod.card] at hc
    have hpred : predecessorRadius (2 ^ 30) 210683556 =
        ((210683555 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) := by
      norm_num [predecessorRadius]
    rw [hpred]
    exact hc.trans hbudget
  have hfloor := latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod sponsorP) (n := 2 ^ 30) (a := 210683556)
    (by norm_num) (by norm_num)
    (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
    (ProximityGap.epsStar : ℝ≥0∞) hgood
  convert hfloor using 1
  norm_num

end ProximityGap.IncidenceCanonicalTriples

#print axioms ProximityGap.IncidenceCanonicalTriples.no_bad_witness_family_of_triple_budget
#print axioms ProximityGap.IncidenceCanonicalTriples.badScalars_card_le_of_triple_budget
#print axioms ProximityGap.IncidenceCanonicalTriples.firstPrime_triple_incidence
#print axioms ProximityGap.IncidenceCanonicalTriples.firstPrime_triple_floor
