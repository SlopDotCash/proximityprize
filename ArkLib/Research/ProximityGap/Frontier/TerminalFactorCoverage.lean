/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalLinearComponent
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The three nonlinear factor bounds sufficient for the terminal production threshold -/

open Polynomial Finset Code
open scoped NNReal ENNReal
open ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
namespace ProximityGap.TerminalFactorCoverage

variable {F K ι : Type} [Field F] [Field K] [Fintype F] [DecidableEq F] [Fintype ι]
  [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- The monomial support of the terminal quartic interpolation polynomial. -/
def Supported (Q : Polynomial (Polynomial K[X])) : Prop :=
  ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
    j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943

/-- Distinct supplied labels whose chosen polynomials are sections of this component. -/
noncomputable def population (φ : F →+* K) (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (G : Finset F) (f : Polynomial (Polynomial K[X])) : Finset F := by
  classical
  exact G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0

/-- Concrete upper bounds for a nonlinear irreducible factor of a supported interpolant.
The sampled labels and all their chosen sections come from the supplied MCA witness family. -/
def NonlinearCaps (φ : F →+* K) (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (G : Finset F) (e : ℕ) : Prop :=
  ∀ Q f : Polynomial (Polynomial K[X]), Q ≠ 0 → Supported Q → Irreducible f → f ∣ Q →
    (f.natDegree = 2 → (population φ fam G f).card ≤ 4128) ∧
    (f.natDegree = 3 → 34 + (e + 1) + (population φ fam G f).card < G.card) ∧
    (f.natDegree = 4 → 34 + (population φ fam G f).card < G.card)

private theorem distinct_sum_le {A : Type*} [DecidableEq A] (U : Multiset A) (wt : A → ℕ) :
    ∑ a ∈ U.toFinset, wt a ≤ (U.map wt).sum := by
  change (U.toFinset.val.map wt).sum ≤ _
  rw [Multiset.toFinset_val]
  obtain ⟨R, hR⟩ := exists_add_of_le (Multiset.dedup_le U)
  conv_rhs => rw [hR, Multiset.map_add, Multiset.sum_add]
  omega

/-- Under exactly the three nonlinear exclusions, the actual factorization supplies the
four-secants covering condition. Small affine factors, vertical factors and multiplicities
are all included in the exception count. -/
theorem cover (φ : F →+* K) (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (hn : Fintype.card ι = 1073741824) {e : ℕ} (hl : 671088640 ≤ e) (hu : e ≤ 715827881)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 1073741824 - e)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hcaps : NonlinearCaps φ fam G e) :
    ∃ H : Finset (LineParameter F), H ⊆ lineParameters fam ∧ H.card ≤ 4 ∧
      (∀ c ∈ H, 512 < (pointsOn fam c).card) ∧
      (G \ H.biUnion (pointsOn fam)).card ≤ 16546 := by
  classical
  have ht0 : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by omega
  obtain ⟨Q, U, E, hQ, hs, hirr, hsum, hnum, _, hE, hcar⟩ :=
    SecondPrimePrimitiveSurface.actual_components φ dom δ u hn ht0 fam
  let T := U.toFinset
  let W := population φ fam G
  have hT : T.card ≤ 4 := (Multiset.toFinset_card_le _).trans hnum
  have hweight : ∑ f ∈ T, f.natDegree ≤ 4 := (distinct_sum_le U _).trans hsum
  have info (f) (hf : f ∈ T) := hirr f (Multiset.mem_toFinset.mp hf)
  have cap (f) (hf : f ∈ T) := hcaps Q f hQ hs (info f hf).1 (info f hf).2.2
  have hcov : G ⊆ E ∪ T.biUnion W := by
    intro z hz
    by_cases hze : z ∈ E
    · exact mem_union_left _ hze
    · obtain ⟨f, hf, he⟩ := hcar z (hG hz) hze
      exact mem_union_right _ (mem_biUnion.mpr ⟨f, Multiset.mem_toFinset.mpr hf,
        mem_filter.mpr ⟨hz, he⟩⟩)
  have htotal : G.card ≤ 34 + ∑ f ∈ T, (W f).card :=
    (card_le_card hcov).trans ((card_union_le ..).trans (Nat.add_le_add hE card_biUnion_le))
  have head (f) (hf : f ∈ T) (hd : f.natDegree = 1) (hw : 185 ≤ (W f).card) :
      ∃ l ∈ lineParameters fam, W f ⊆ pointsOn fam l :=
    TerminalLinearComponent.actual_linear φ fam hn ht0 Q f hQ (info f hf).1
      (info f hf).2.2 hd hs (W f) ((filter_subset ..).trans hG) hw
      (fun _ hz => (mem_filter.mp hz).2)
  have hlinear (f) (hf : f ∈ T) (hd : f.natDegree = 1) : (W f).card ≤ e + 1 := by
    by_cases hw : 185 ≤ (W f).card
    · obtain ⟨l, hL, hcon⟩ := head f hf hd hw
      exact (card_le_card hcon).trans (TwoLargeCoreCount.line_occupancy_le fam (by omega) ht hL)
    · omega
  have hlow (f) (hf : f ∈ T) : f.natDegree ≤ 2 := by
    by_contra! hhigh
    let V := T.erase f
    have hsplit : ∑ g ∈ V, g.natDegree + f.natDegree ≤ 4 := by
      rw [show V = T.erase f from rfl, sum_erase_add _ _ hf]
      exact hweight
    have hcard : V.card ≤ ∑ g ∈ V, g.natDegree := by
      simpa using (sum_le_sum (s := V) fun g hg =>
        (show 1 ≤ g.natDegree from (info g (mem_of_mem_erase hg)).2.1))
    have hrest (g) (hg : g ∈ V) : g.natDegree = 1 := by
      have h1 := (info g (mem_of_mem_erase hg)).2.1
      have h2 := single_le_sum (s := V) (f := fun g => g.natDegree) (fun _ _ => Nat.zero_le _) hg
      omega
    have hw : ∑ g ∈ V, (W g).card ≤ V.card * (e + 1) := by
      simpa using sum_le_sum (s := V) fun g hg => hlinear g (mem_of_mem_erase hg) (hrest g hg)
    have hadd := sum_erase_add T (fun g => (W g).card) hf
    change ∑ g ∈ V, (W g).card + (W f).card = _ at hadd
    rw [← hadd] at htotal
    rcases (show f.natDegree = 3 ∨ f.natDegree = 4 by omega) with h3 | h4
    · have hc := (cap f hf).2.1 h3
      have small := Nat.mul_le_mul_right (e + 1) (show V.card ≤ 1 by omega)
      change 34 + (e + 1) + (W f).card < G.card at hc
      omega
    · have hc := (cap f hf).2.2 h4
      have hz : V.card = 0 := by omega
      rw [hz, zero_mul] at hw
      change 34 + (W f).card < G.card at hc
      omega
  let B := T.filter fun f => f.natDegree = 1 ∧ 512 < (W f).card
  have exists_line (f : B) := head f (mem_filter.mp f.property).1
    (mem_filter.mp f.property).2.1 (by have := (mem_filter.mp f.property).2.2; omega)
  choose line hline hcon using exists_line
  let H := univ.image line
  have hH : H.card ≤ 4 := card_image_le.trans (by
    simpa [B] using (card_filter_le T _).trans hT)
  have hmember (f : B) : line f ∈ H := mem_image_of_mem _ (mem_univ _)
  refine ⟨H, ?_, hH, ?_, ?_⟩
  · intro l hL
    obtain ⟨f, _, rfl⟩ := mem_image.mp hL
    exact hline f
  · intro l hL
    obtain ⟨f, _, rfl⟩ := mem_image.mp hL
    exact (mem_filter.mp f.property).2.2.trans_le (card_le_card (hcon f))
  · let V := T \ B
    have hsub : G \ H.biUnion (pointsOn fam) ⊆ E ∪ V.biUnion W := by
      intro z hz
      obtain ⟨hzG, hout⟩ := mem_sdiff.mp hz
      rcases mem_union.mp (hcov hzG) with he | hw
      · exact mem_union_left _ he
      · obtain ⟨f, hf, hzf⟩ := mem_biUnion.mp hw
        have hnB : f ∉ B := fun hb => hout (mem_biUnion.mpr
          ⟨line ⟨f, hb⟩, hmember ⟨f, hb⟩, hcon ⟨f, hb⟩ hzf⟩)
        exact mem_union_right _ (mem_biUnion.mpr ⟨f, mem_sdiff.mpr ⟨hf, hnB⟩, hzf⟩)
    have bound (f) (hf : f ∈ V) : (W f).card ≤ 4128 := by
      obtain ⟨hfT, hnB⟩ := mem_sdiff.mp hf
      have hpos := (info f hfT).2.1
      have htwo := hlow f hfT
      rcases (show f.natDegree = 1 ∨ f.natDegree = 2 by omega) with h1 | h2
      · have hsmall : ¬ 512 < (W f).card := fun hh => hnB (mem_filter.mpr ⟨hfT, h1, hh⟩)
        omega
      · exact (cap f hfT).1 h2
    have hV : V.card ≤ 4 := (card_le_card (sdiff_subset ..)).trans hT
    have hnum : (V.biUnion W).card ≤ V.card * 4128 := card_biUnion_le.trans
      ((sum_le_sum bound).trans_eq (by simp))
    exact (card_le_card hsub).trans ((card_union_le ..).trans
      ((Nat.add_le_add hE hnum).trans (by omega)))

/-- Any actual violation forces an exceptionally populated irreducible factor of degree
two, three or four. This alternative starts from the MCA events without a head-cover
or geometric regularity assumption. -/
theorem obstruction (φ : F →+* K) (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (hn : Fintype.card ι = 1073741824) {e : ℕ} (hl : 671088640 ≤ e) (hu : e ≤ 715827881)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 1073741824 - e)
    (G : Finset F) (hG : G ⊆ fam.G) (hbig : 3 * (e + 1) < G.card) :
    ∃ Q f : Polynomial (Polynomial K[X]), Q ≠ 0 ∧ Supported Q ∧ Irreducible f ∧ f ∣ Q ∧
      ((f.natDegree = 2 ∧ 4128 < (population φ fam G f).card) ∨
       (f.natDegree = 3 ∧ G.card ≤ 34 + (e + 1) + (population φ fam G f).card) ∨
       (f.natDegree = 4 ∧ G.card ≤ 34 + (population φ fam G f).card)) := by
  classical
  by_contra h
  have caps : NonlinearCaps φ fam G e := by
    intro Q f hQ hsup hirr hdiv
    have hn := fun hc => h ⟨Q, f, hQ, hsup, hirr, hdiv, hc⟩
    rcases eq_or_ne f.natDegree 2 with h2 | h2
    · exact ⟨fun _ => le_of_not_gt (fun hu => hn (Or.inl ⟨h2, hu⟩)),
        fun he => by omega, fun he => by omega⟩
    · exact ⟨fun he => (h2 he).elim,
        fun he => lt_of_not_ge fun hu => hn (Or.inr (Or.inl ⟨he, hu⟩)),
        fun he => lt_of_not_ge fun hu => hn (Or.inr (Or.inr ⟨he, hu⟩))⟩
  obtain ⟨H, hH, hfour, hlines, hexc⟩ := cover φ fam hn hl hu ht G hG caps
  exact hbig.not_ge (TerminalCollinearHeadCount.selected_card_of_few_heads fam G hG hn rfl
    hl hu ht H hH hfour hlines hexc)

section NamedPrime
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open TerminalCollinearHeadCount

private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The three component populations still to be bounded on the exact over-budget sample
at the named second prime. Coefficients extend to the algebraic closure for factorization. -/
def SecondPrimeNonlinearCaps : Prop :=
  ∀ u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ 30)),
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2 ^ 26)
      ((715827881 : ℝ≥0) / 1073741824) u (by decide)
    ∀ G : Finset (ZMod p), G ⊆ fam.G → G.card = 2147483649 →
      NonlinearCaps (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) fam G 715827881

/-- At the named predecessor an over-budget sample forces 4129 quadratic sections,
1431655733 cubic sections, or 2147483615 quartic sections of a single irreducible factor. -/
theorem secondPrime_factor_obstruction (u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ 30))) :
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2 ^ 26)
      ((715827881 : ℝ≥0) / 1073741824) u (by decide)
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    ∀ G : Finset (ZMod p), G ⊆ fam.G → G.card = 2147483649 →
      ∃ Q f : Polynomial (Polynomial (AlgebraicClosure (ZMod p))[X]),
        Q ≠ 0 ∧ Supported Q ∧ Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 2 ∧ 4129 ≤ (population φ fam G f).card) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population φ fam G f).card) ∨
         (f.natDegree = 4 ∧ 2147483615 ≤ (population φ fam G f).card)) := by
  intro fam φ G hG hsize
  obtain ⟨Q, f, hQ, hs, hirr, hdvd, hdeg⟩ := obstruction φ fam
    (Fintype.card_fin _) (e := 715827881) (by decide) (by decide)
    (TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)) G hG (by omega)
  refine ⟨Q, f, hQ, hs, hirr, hdvd, ?_⟩
  rcases hdeg with ⟨hd, hp⟩ | ⟨hd, hp⟩ | ⟨hd, hp⟩
  · exact Or.inl ⟨hd, hp⟩
  · exact Or.inr (Or.inl ⟨hd, by omega⟩)
  · exact Or.inr (Or.inr ⟨hd, by omega⟩)

/-- The native second-prime threshold follows from only the three nonlinear population
bounds. All remaining transfers from these bounds to actual MCA security are checked. -/
theorem secondPrime_threshold_of_nonlinear_caps (h : SecondPrimeNonlinearCaps) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (evalCode g (2 ^ 30) (2 ^ 26 - 1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0) / 1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hsize
  exact cover (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) fam (Fintype.card_fin _)
    (e := 715827881) (by decide) (by decide)
    (TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide))
    G hG (h u G hG hsize)

end NamedPrime

#print axioms secondPrime_factor_obstruction
#print axioms obstruction
#print axioms secondPrime_threshold_of_nonlinear_caps
#print axioms cover
end ProximityGap.TerminalFactorCoverage
