/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterEqualSlopeHighCores
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthCombinatorics

/-!
# Johnson closure of the equal-slope half-core-covered branch

At the saturated quarter rate, write `h = 2k`, `n = 4k`, and let `e` be the
number of coordinates where the common high-core slope disagrees with the
received direction.  Every high core lies in the remaining `4k-e`
coordinates, has size at least `2k`, and distinct cores intersect in at most
`k-1` coordinates.

After truncating the cores to size `2k`, the sharp Johnson inequality gives

```text
  L * (4k + e(k-1)) <= (4k-e)(k+1),
```

where `L` is the number of half-core lines.  Since each such line contains at
most `e` selected scalars and `e <= k-1`, the same inequality implies
`L*e <= 4k`.  Thus all scalars covered by half-core lines are domain-bounded;
under a half-core cover of `G`, the equal-slope branch closes completely.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure

attribute [local instance] Classical.propDecidable

/-! ## Exact saturated Johnson arithmetic -/

/-- Rearrangement of the sharp Johnson inequality at
`v=4k-e`, `t=2k`, `s=k-1`.  The multiplication form is exact and avoids a
floor or division. -/
theorem saturated_johnson_denominator_form
    {L k e : Nat} (hL : 1 ≤ L) (hk : 1 ≤ k) (he : e ≤ k - 1)
    (hJ : L * (2 * k) ^ 2 ≤
      (4 * k - e) * (2 * k + (L - 1) * (k - 1))) :
    L * (4 * k + e * (k - 1)) ≤ (4 * k - e) * (k + 1) := by
  let v := 4 * k - e
  let s := k - 1
  let D := 4 * k + e * s
  let N := v * (k + 1)
  have he4 : e ≤ 4 * k := by omega
  have hv : v + e = 4 * k := by
    exact Nat.sub_add_cancel he4
  have hs : s + 1 = k := by
    exact Nat.sub_add_cancel hk
  have hLs : L - 1 + 1 = L := by
    exact Nat.sub_add_cancel hL
  have hDidentity : D + v * s = (2 * k) ^ 2 := by
    dsimp only [D]
    calc
      4 * k + e * s + v * s = 4 * k + (v + e) * s := by ring
      _ = 4 * k + (4 * k) * s := by rw [hv]
      _ = 4 * k * (s + 1) := by ring
      _ = 4 * k * k := by rw [hs]
      _ = (2 * k) ^ 2 := by ring
  have hinner : 2 * k + (L - 1) * s = (k + 1) + L * s := by
    calc
      2 * k + (L - 1) * s = 2 * (s + 1) + (L - 1) * s := by rw [hs]
      _ = (s + 2) + (L - 1 + 1) * s := by ring
      _ = (k + 1) + L * s := by rw [hLs]; omega
  have hleft : L * (2 * k) ^ 2 = L * D + L * v * s := by
    rw [← hDidentity]
    ring
  have hright :
      v * (2 * k + (L - 1) * s) = N + L * v * s := by
    rw [hinner]
    dsimp only [N]
    ring
  have hJ' : L * D + L * v * s ≤ N + L * v * s := by
    rw [← hleft, ← hright]
    simpa only [v, s] using hJ
  have hDN : L * D ≤ N := Nat.le_of_add_le_add_right hJ'
  simpa only [D, N, v, s] using hDN

/-- The exact denominator bound implies the product closure `L*e<=4k` for
every `0<=e<=k-1`, including the `e=0` edge case. -/
theorem saturated_johnson_error_product_le
    {L k e : Nat} (hk : 1 ≤ k) (he : e ≤ k - 1)
    (hden : L * (4 * k + e * (k - 1)) ≤
      (4 * k - e) * (k + 1)) :
    L * e ≤ 4 * k := by
  let D := 4 * k + e * (k - 1)
  let N := (4 * k - e) * (k + 1)
  have hsub : 4 * k - e ≤ 4 * k := Nat.sub_le _ _
  have hNle : N ≤ 4 * k * (k + 1) := by
    exact Nat.mul_le_mul_right (k + 1) hsub
  have htwice : 2 * e ≤ 4 * k := by omega
  have hinner : e * (k + 1) ≤ D := by
    have hkPlus : k + 1 = (k - 1) + 2 := by omega
    have hid : e * (k + 1) = e * (k - 1) + 2 * e := by
      calc
        e * (k + 1) = e * ((k - 1) + 2) := by rw [hkPlus]
        _ = e * (k - 1) + 2 * e := by ring
    rw [hid]
    dsimp only [D]
    simpa only [Nat.add_comm] using
      (Nat.add_le_add_left htwice (e * (k - 1)))
  have heN : e * N ≤ 4 * k * D := by
    calc
      e * N ≤ e * (4 * k * (k + 1)) := Nat.mul_le_mul_left e hNle
      _ = 4 * k * (e * (k + 1)) := by ring
      _ ≤ 4 * k * D := Nat.mul_le_mul_left (4 * k) hinner
  have hmul : (L * e) * D ≤ (4 * k) * D := by
    calc
      (L * e) * D = e * (L * D) := by ring
      _ ≤ e * N := Nat.mul_le_mul_left e (by simpa only [D, N] using hden)
      _ ≤ (4 * k) * D := heN
  have hDpos : 0 < D := by
    dsimp only [D]
    omega
  exact Nat.le_of_mul_le_mul_right hmul hDpos

/-! ## Moving cores to their common direction-agreement universe -/

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Restrict a finite set to a containing finite universe, represented by the
universe subtype. -/
def restrictTo (V A : Finset ι) : Finset V :=
  Finset.univ.filter fun x : V => x.1 ∈ A

/-- Restriction to a containing universe preserves cardinality. -/
theorem card_restrictTo (V A : Finset ι) (hA : A ⊆ V) :
    (restrictTo V A).card = A.card := by
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, hA hx⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

/-- Restriction commutes with intersection. -/
theorem restrictTo_inter (V A B : Finset ι) :
    restrictTo V (A ∩ B) = restrictTo V A ∩ restrictTo V B := by
  ext x
  simp only [restrictTo, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter]

/-! ## Sharp Johnson bound for the equal-slope high-core family -/

/-- **Exact Johnson denominator for equal-slope half cores.**  At `h=2k`,
let `e` be the common direction-error count.  The number `L` of relevant
half-core lines obeys

`L * (4k + e(k-1)) <= (4k-e)(k+1)`.
-/
theorem halfCoreLines_mul_denominator_le_numerator
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    let e := (directionDisagreement dom (u 1) line0.2).card
    (halfCoreLines family h).card * (4 * k + e * (k - 1)) ≤
      (4 * k - e) * (k + 1) := by
  let E := directionDisagreement dom (u 1) line0.2
  let e := E.card
  let V : Finset ι := Finset.univ \ E
  let K := {line // line ∈ halfCoreLines family h}
  have hrate : 2 * k ≤ h := by omega
  have hEcap : e ≤ k - 1 := by
    simpa only [e, E] using
      directionDisagreement_card_le_pred_of_distinct_relevant_equalSlope_halfCores
        family hk hn line0 line1 hline0 hline1 hne hslope hcore0 hcore1
  have hline0Half : line0 ∈ halfCoreLines family h := by
    exact Finset.mem_filter.mpr ⟨hline0, hcore0⟩
  letI : Nonempty K := ⟨⟨line0, hline0Half⟩⟩
  let D : K → Finset ι := fun line =>
    jointCore dom (u 0) (u 1) line.1.1 line.1.2
  have hDsize : ∀ line : K, h ≤ (D line).card := by
    intro line
    exact (Finset.mem_filter.mp line.2).2
  let T : K → Finset ι := fun line =>
    Classical.choose (Finset.exists_subset_card_eq (hDsize line))
  have hTsub : ∀ line : K, T line ⊆ D line := by
    intro line
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hDsize line))).1
  have hTcard : ∀ line : K, (T line).card = h := by
    intro line
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hDsize line))).2
  have hslopeK : ∀ line : K, line.1.2 = line0.2 := by
    intro line
    have hline := (Finset.mem_filter.mp line.2).1
    have hcore := (Finset.mem_filter.mp line.2).2
    exact slope_eq_reference_of_relevant_halfCore_in_equalSlope_cluster
      family hk hn hrate line0 line1 line.1 hline0 hline1 hline
        hne hslope hcore0 hcore1 hcore
  have hDsubV : ∀ line : K, D line ⊆ V := by
    intro line i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiE
    have hiError : line0.2.eval (dom i) ≠ u 1 i := by
      simpa only [E, directionDisagreement, Finset.mem_filter,
        Finset.mem_univ, true_and] using hiE
    have hiCorePair :
        line.1.1.eval (dom i) = u 0 i ∧
          line.1.2.eval (dom i) = u 1 i := by
      simpa only [D, jointCore, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    have hiCore : line.1.2.eval (dom i) = u 1 i := hiCorePair.2
    apply hiError
    rw [← hslopeK line]
    exact hiCore
  have hTsubV : ∀ line : K, T line ⊆ V := by
    intro line
    exact (hTsub line).trans (hDsubV line)
  let S : K → Finset V := fun line => restrictTo V (T line)
  have hScard : ∀ line : K, (S line).card = h := by
    intro line
    rw [show S line = restrictTo V (T line) by rfl,
      card_restrictTo V (T line) (hTsubV line)]
    exact hTcard line
  have hSpair : ∀ a b : K, a ≠ b → (S a ∩ S b).card ≤ k - 1 := by
    intro a b hab
    have habVal : a.1 ≠ b.1 := by
      intro heq
      exact hab (Subtype.ext heq)
    have haLine := (Finset.mem_filter.mp a.2).1
    have hbLine := (Finset.mem_filter.mp b.2).1
    have haDeg := lineParameter_degree_lt family haLine
    have hbDeg := lineParameter_degree_lt family hbLine
    have hintercept : a.1.1 ≠ b.1.1 := by
      intro hintercept
      apply habVal
      exact Prod.ext hintercept (by rw [hslopeK a, hslopeK b])
    rw [show S a ∩ S b = restrictTo V (T a ∩ T b) by
      simpa only [S] using (restrictTo_inter V (T a) (T b)).symm]
    rw [card_restrictTo V (T a ∩ T b)]
    · apply le_trans (Finset.card_le_card
        (Finset.inter_subset_inter (hTsub a) (hTsub b)))
      exact jointCore_inter_card_le_pred_of_intercept_ne
        dom (u 0) (u 1) hk a.1 b.1 hintercept haDeg.1 hbDeg.1
    · exact (Finset.inter_subset_left.trans (hTsubV a))
  have hVcard : V.card = 4 * k - e := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsaturated, E, e]
    ring
  have hJ := sharp_johnson_of_lower_upper_pair S h h (k - 1)
    (fun line => (hScard line).ge) (fun line => (hScard line).le) hSpair
  have hKcard : Fintype.card K = (halfCoreLines family h).card := by
    simp only [K, Fintype.card_coe]
  have hJ0 : (halfCoreLines family h).card * h ^ 2 ≤
      V.card * (h + ((halfCoreLines family h).card - 1) * (k - 1)) := by
    simpa only [hKcard, Fintype.card_coe] using hJ
  have hJ' : (halfCoreLines family h).card * (2 * k) ^ 2 ≤
      (4 * k - e) *
        (2 * k + ((halfCoreLines family h).card - 1) * (k - 1)) := by
    simpa only [hVcard, hsaturated] using hJ0
  have hLpos : 1 ≤ (halfCoreLines family h).card := by
    exact Finset.card_pos.mpr ⟨line0, hline0Half⟩
  exact saturated_johnson_denominator_form hLpos hk hEcap hJ'

/-- The number of half-core lines times the common direction-error count is
at most the domain size `4k`. -/
theorem halfCoreLines_mul_directionDisagreement_card_le_four_mul
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    (halfCoreLines family h).card *
        (directionDisagreement dom (u 1) line0.2).card ≤ 4 * k := by
  let e := (directionDisagreement dom (u 1) line0.2).card
  have hden := halfCoreLines_mul_denominator_le_numerator
    family hk hn hsaturated line0 line1 hline0 hline1 hne hslope
      hcore0 hcore1
  have he : e ≤ k - 1 := by
    simpa only [e] using
      directionDisagreement_card_le_pred_of_distinct_relevant_equalSlope_halfCores
        family hk hn line0 line1 hline0 hline1 hne hslope hcore0 hcore1
  exact saturated_johnson_error_product_le hk he (by
    simpa only [e] using hden)

/-- **Equal-slope covered-population closure.**  All selected scalars lying on
relevant half-core lines number at most the domain size. -/
theorem halfCoreCoveredScalars_card_le_four_mul_of_equalSlope_cluster
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    (halfCoreCoveredScalars family h).card ≤ 4 * k := by
  let e := (directionDisagreement dom (u 1) line0.2).card
  have hrate : 2 * k ≤ h := by omega
  have hperLine : ∀ line ∈ halfCoreLines family h,
      (pointsOn family line).card ≤ e := by
    intro line hline
    have hline' := (Finset.mem_filter.mp hline).1
    have hcore := (Finset.mem_filter.mp hline).2
    have hslopeLine :=
      slope_eq_reference_of_relevant_halfCore_in_equalSlope_cluster
        family hk hn hrate line0 line1 line hline0 hline1 hline'
          hne hslope hcore0 hcore1 hcore
    have hcap := pointsOn_card_le_directionDisagreement_card
      family line hline'
    rw [hslopeLine] at hcap
    simpa only [e] using hcap
  have hcoverCount : (halfCoreCoveredScalars family h).card ≤
      (halfCoreLines family h).card * e := by
    exact Finset.card_biUnion_le_card_mul
      (halfCoreLines family h) (pointsOn family) e hperLine
  exact hcoverCount.trans <|
    halfCoreLines_mul_directionDisagreement_card_le_four_mul
      family hk hn hsaturated line0 line1 hline0 hline1 hne hslope
        hcore0 hcore1

/-- **Equal-slope half-core-covered branch closed.**  If every selected scalar
lies on a relevant half-core line, then `|G| <= 2h`. -/
theorem G_card_le_two_mul_of_equalSlope_halfCore_cover
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hcover : family.G ⊆ halfCoreCoveredScalars family h) :
    family.G.card ≤ 2 * h := by
  have hcovered :=
    halfCoreCoveredScalars_card_le_four_mul_of_equalSlope_cluster
      family hk hn hsaturated line0 line1 hline0 hline1 hne hslope
        hcore0 hcore1
  have hG := (Finset.card_le_card hcover).trans hcovered
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure
#print axioms saturated_johnson_denominator_form
#print axioms saturated_johnson_error_product_le
#print axioms halfCoreLines_mul_denominator_le_numerator
#print axioms halfCoreLines_mul_directionDisagreement_card_le_four_mul
#print axioms halfCoreCoveredScalars_card_le_four_mul_of_equalSlope_cluster
#print axioms G_card_le_two_mul_of_equalSlope_halfCore_cover
