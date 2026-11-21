/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicPopulation
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier._MCAAdjacentFloorExactPin
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # The operational crossing on arbitrary length-two-to-the-thirtieth domains

The successor has three disjoint cores of cardinality 357913941 and one fresh
site. A finite-field projection separates enough labels to exceed the budget
on any injective evaluation domain. The predecessor cap therefore classifies
every real radius and positive interleaving width in the stated field window.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TerminalDomainSecurity
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger SecondPrimeActualPopulations
open IntrinsicCubicPopulation SecondPrimeCoordinateWeight HalfPredecessorBadEventRichPointBridge
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 67108864
abbrev predecessor : ℝ≥0 := 715827881/1073741824
abbrev boundary : ℝ≥0 := 715827882/1073741824
abbrev tolerance : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128

/-- Unconditional failure at the successor on every injective domain in the
terminal budget class. The proof also applies to any smaller budget. -/
theorem successor_bad (dom : I ↪ F) (hn : Fintype.card I=n)
    (hB : Fintype.card F / 2^128 ≤ 2147483648) :
    tolerance < epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) boundary := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  let x := e.symm.toEmbedding.trans dom
  have hr := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e.symm x dom (fun _ => rfl) k boundary
  rw [hr]
  have hsmall := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  have hq : Fintype.card F ≤ 2^256 := by omega
  exact ManyHeadLocatorMass.over_budget_128 (h:=0) (d:=2) (r:=357913941) x boundary
    (by decide) (by decide) (by decide) (by
      change (1-(715827882:ℝ≥0)/1073741824)*1073741824 ≤ 357913942
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num)]
      exact tsub_le_iff_right.mpr (by norm_num)) hq (by unfold n; omega)

/-- A strict bad endpoint and the good predecessor determine both the supremum
and the full good-radius predicate after arbitrary reindexing and interleaving. -/
theorem classification_of_good (dom : I ↪ F) (hn : Fintype.card I=n)
    (hB : Fintype.card F / 2^128 ≤ 2147483648)
    (hprev : epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) predecessor ≤ tolerance)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance = boundary ∧
    ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ<boundary := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  let x := e.symm.toEmbedding.trans dom
  have hr := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e.symm x dom (fun _ => rfl) k
  have hb := successor_bad dom hn hB
  have heq : mcaDeltaStar (F:=F) (ReedSolomon.code dom k : Set (I → F)) tolerance = boundary := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq e.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a:=715827882) (by decide) (by decide) _ _ (by rw [← hr]; exact hprev) (by rw [← hr]; exact hb)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    have h := mcaDeltaStar_le_of_bad _ _ bad
    rw [heq] at h
    exact hδ.not_ge h

/-- Passage from any literal bad-scalar cap at the predecessor to its security
probability for the entire received-word space. -/
theorem eps_of_family_cap (dom : I ↪ F)
    (hcap : ∀ u : Code.WordStack F (Fin 2) I,
      (canonicalBadScalarRichPointFamily dom (k:=k) predecessor u (by decide)).G.card ≤ 2147483648) :
    epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) predecessor ≤
      (2147483648:ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le
  exact hcap

/-- Every over-budget family would have to violate the received-order bound
on a single actual proper original cubic. -/
theorem family_cap_of_order {K : Type} [Field K] (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 1744830589 < p) (dom : I ↪ F) (hn : Fintype.card I=n) (δ : ℝ≥0)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 357913943) (u : Code.WordStack F (Fin 2) I)
    (fam : Family dom δ u) (h : ∀ f : K[X][X][X], Irreducible f → f.natDegree=3 →
      weight 67108863 f≤290805098 → WeightedSylvesterDegree.TotalDegreeLe f 34 →
      Proper f → 1431655733≤(population fam φ f).card →
      3*totalOrder φ dom u f+35*67108863≤2*Fintype.card I+16*weight 67108863 f+402) :
    fam.G.card≤2147483648 := by
  by_contra! hbig
  obtain ⟨Q,hQ,hs,f,hi,hd,hy,hpop,hw⟩ :=
    SecondPrimeCubicOnly.actual_cubic fam φ (by omega : 715827884 < p) hn ht hbig
  have hshape := fun j i a hj => (hs j i a hj).2.1
  have htotal := SecondPrimeSectionResultant.factor_triangle hQ hd hshape
  have hcap := actual_cubic_population φ (p:=p) (by omega) dom δ u hn ht.ge fam Q f hQ hi hd hy hshape hw (by
    intro hp' hlarge
    have hh := h f hi hy hw htotal hp' hlarge
    rw [hn] at hh
    zify at hh
    change (3:ℤ)*totalOrder φ dom u f ≤ 2*1073741824+16*(weight 67108863 f:ℤ)-35*67108863+532
    omega)
  exact hcap.not_ge hpop

#print axioms successor_bad
#print axioms classification_of_good
#print axioms family_cap_of_order
end ArkLib.ProximityGap.Frontier.TerminalDomainSecurity
