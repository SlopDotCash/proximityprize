/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicOnly
import ArkLib.Research.ProximityGap.Frontier.TerminalDomainSecurity

/-! # The actual cubic throughout the rate-one-sixteenth budget interval

An overfull family forces a positive-value-degree component after removing the
large affine heads. The quadratic and quartic caps are uniform in the agreement
threshold. Thus every violation across the interval yields a single cubic on
at least two entire head capacities minus the scalar-only exceptions.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TerminalCubicBudgetWindow
open _root_.ProximityGap SecondPrimeActualPopulations SecondPrimeCoordinateWeight TerminalDomainSecurity
variable {F I K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- Overfull families anywhere in the terminal error interval force a single
actual cubic bearing at least 1342177249 selected labels. -/
theorem actual_cubic (fam : Family dom δ u) (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 715827884<p) (hn : Fintype.card I=n) {e : ℕ} (hl : 671088640≤e) (hu : e≤715827881)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=n-e) (hbig : 3*(e+1)<fam.G.card) :
    ∃ Q f : Factor K, Q≠0 ∧ TerminalFactorCoverage.Supported Q ∧ Irreducible f ∧ f∣Q ∧
      f.natDegree=3 ∧ 1342177249 ≤ (population fam φ f).card ∧
      2*(e+1)+1-34 ≤ (population fam φ f).card ∧ weight 67108863 f ≤ 290805098 := by
  classical
  obtain ⟨Q,f,hQ,hs,hi,hd,hh⟩ := TerminalFactorCoverage.obstruction φ fam hn hl hu ht fam.G (subset_refl _) hbig
  change (f.natDegree=2 ∧ 4128 < (population fam φ f).card) ∨
    (f.natDegree=3 ∧ fam.G.card≤34+(e+1)+(population fam φ f).card) ∨
    (f.natDegree=4 ∧ fam.G.card≤34+(population fam φ f).card) at hh
  have ht0 : 357913943 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ := by rw [ht]; unfold n; omega
  have htri := fun j i a hh => (hs j i a hh).2.1
  have root (z : F) (hz : z∈population fam φ f) :
      f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ)=0 := (mem_filter.mp hz).2
  rcases hh with ⟨hy,hM⟩ | ⟨hy,hM⟩ | ⟨hy,hM⟩
  · have h := SecondPrimeQuadraticFactor.quadratic_population_le fam φ Q f hQ hd hi hy (by
      intro j i a he
      obtain ⟨_,hs,hw⟩ := hs j i a he
      exact ⟨hs,by omega⟩) (by
        intro i hi hj hz
        exact (show ¬ p ≤ i by omega) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff K p i).mp hz))) hn ht0
    omega
  · refine ⟨Q,f,hQ,hs,hi,hd,hy,by omega,by omega,?_⟩
    exact SecondPrimeCubicWeightBound.actual_cubic_weight φ dom δ u hn ht0 fam Q f hQ hd hi hy htri
      (population fam φ f) (filter_subset ..) (by omega) root
  · have h := ActualTerminalQuartic.actual_quartic_label_cap φ (p:=p) (by omega) dom δ u hn ht0 fam Q f
      hQ hd hi hy htri (population fam φ f) (filter_subset ..) root
    omega

/-- Three heads cross the relevant 128-bit budget on any injective domain
at the first claimed failing index for that budget. -/
theorem successor_bad (dom : I ↪ F) (hn : Fintype.card I=n) {B : ℕ}
    (hB : Fintype.card F/2^128=B) (hl : 2013265923≤B) (hu : B≤2147483648) :
    tolerance < epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) (((B/3:ℕ):ℝ≥0)/n) := by
  classical
  let e := B/3
  let r := n-e-67108863
  let δ : ℝ≥0 := (e:ℝ≥0)/n
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hr := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) k δ
  change tolerance < epsMCA (F:=F) _ δ
  rw [hr]
  have hsmall := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  have hq : Fintype.card F≤2^256 := by omega
  have heL : 671088641≤e := by dsimp [e]; omega
  have heU : e≤715827882 := by dsimp [e]; omega
  refine ManyHeadLocatorMass.over_budget_128 (h:=67108862) (d:=2) (r:=r) x δ ?_ (by decide) ?_ ?_ hq ?_
  · dsimp [r,n]; omega
  · dsimp [k,r,n]; omega
  · change (1-(e:ℝ≥0)/n)*n ≤ ((67108862+r+1:ℕ):ℝ≥0)
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub]
    exact_mod_cast (show n-e ≤ 67108862+r+1 by dsimp [r,n]; omega)
  · rw [hB]
    dsimp [r,e,n]
    omega

/-- A sharp family cap at its immediate predecessor turns the three-head
construction into an exact classification, including every positive width. -/
theorem classification_of_family_bound (dom : I ↪ F) (hn : Fintype.card I=n) {B : ℕ}
    (hB : Fintype.card F/2^128=B) (hl : 2013265923≤B) (hu : B≤2147483648)
    (hcap : ∀ u : Code.WordStack F (Fin 2) I, (HalfPredecessorBadEventRichPointBridge.canonicalBadScalarRichPointFamily dom
      (k:=k) (((B/3-1:ℕ):ℝ≥0)/n) u (by decide)).G.card≤3*((B/3-1)+1))
    (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((B/3:ℕ):ℝ≥0)/n
    MCAThresholdLedger.mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  classical
  let e := B/3
  let t : ℝ≥0 := (e:ℝ≥0)/n
  let t₀ : ℝ≥0 := ((e-1:ℕ):ℝ≥0)/n
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) k
  have hb := successor_bad dom hn hB hl hu
  have hp : epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) t₀≤tolerance := by
    have hcount := epsMCA_le_of_badCount_le (ReedSolomon.code dom k : Set (I → F)) t₀ (3*((e-1)+1)) hcap
    have hratio := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).2
      (show 3*((e-1)+1)≤Fintype.card F/2^128 by dsimp [e]; omega)
    exact hcount.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hratio)
  have heq : MCAThresholdLedger.mcaDeltaStar (F:=F) (ReedSolomon.code dom k : Set (I → F)) tolerance=t := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a:=e) (by dsimp [e]; omega) (by dsimp [e,n]; omega) _ _
      (by rw [← hre]; exact hp) (by rw [← hre]; exact hb)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    have h := MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ bad
    rw [heq] at h
    exact hδ.not_ge h

#print axioms actual_cubic
#print axioms successor_bad
#print axioms classification_of_family_bound
end ArkLib.ProximityGap.Frontier.TerminalCubicBudgetWindow
