/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalCubicBudgetWindow
import ArkLib.Research.ProximityGap.Frontier.UnconditionalCubicPopulation

/-! # An exact rate-one-sixteenth threshold on an interval of finite-field budgets

All polynomial components have unconditional population bounds. Together with
the three-head lower construction they determine the full line-MCA crossing
on every injective domain for each integer budget in the interval.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.UniversalCubicBudgetWindow
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity SecondPrimeActualPopulations HalfPredecessorBadEventRichPointBridge
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- Simultaneous numerator bound for every word pair throughout the error interval. -/
theorem family_cap (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p]
    (hp : 1744830589<p) {e : ℕ} (hl : 671088640≤e) (hu : e≤715827881)
    (δ : ℝ≥0) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=n-e)
    (u : Code.WordStack F (Fin 2) I) (fam : Family dom δ u) : fam.G.card≤3*(e+1) := by
  classical
  by_contra! hlarge
  let φ := algebraMap F (AlgebraicClosure F)
  let _ : CharP (AlgebraicClosure F) p := charP_of_injective_ringHom φ.injective p
  obtain ⟨Q,f,hQ,hs,hi,hd,hy,hpop,_,hw⟩ :=
    TerminalCubicBudgetWindow.actual_cubic fam φ (by omega : 715827884<p) hn hl hu ht hlarge
  have h := UnconditionalCubicPopulation.cap fam φ p hp hn (by rw [ht]; unfold n; omega)
    Q f hQ hi hd hy (fun j i a h => (hs j i a h).2.1) hw
  omega

omit [Nonempty I] [DecidableEq I] in
private theorem agreement (hn : Fintype.card I=n) (e : ℕ) (he : e≤n) :
    ⌈(1-(e:ℝ≥0)/n)*(Fintype.card I:ℝ≥0)⌉₊=n-e := by
  rw [hn]
  have h := TwoCorePackingThreshold.agreement_ceiling e he
  rw [Fintype.card_fin] at h
  exact h

/-- Field-independent normalized cap at every integer error count in the interval,
with the cardinality bound covering the smaller prime fields automatically. -/
theorem eps_upper (dom : I ↪ F) (hn : Fintype.card I=n) {p e : ℕ} [CharP F p]
    (hchar : 1744830589<p ∨ Fintype.card F≤3*(e+1)) (hl : 671088640≤e) (hu : e≤715827881) :
    epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) ((e:ℝ≥0)/n) ≤
      ((3*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (k:=k) ((e:ℝ≥0)/n) u (by decide)
  change fam.G.card≤3*(e+1)
  rcases hchar with hp | hq
  · exact family_cap dom hn hp hl hu _ (agreement hn e (by unfold n; omega)) u fam
  · exact (card_le_univ fam.G).trans hq

/-- The exact operational supremum and all actual good real radii in the budget
interval, for every finite field above the characteristic cutoff and every positive width. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I=n) {p B : ℕ} [CharP F p]
    (hp : 1744830589<p) (hB : Fintype.card F/2^128=B) (hl : 2013265923≤B) (hu : B≤2147483648)
    (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((B/3:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  apply TerminalCubicBudgetWindow.classification_of_family_bound dom hn hB hl hu _ width
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (k:=k) (((B/3-1:ℕ):ℝ≥0)/n) u (by decide)
  exact family_cap dom hn hp (by omega) (by omega) _ (agreement hn _ (by unfold n; omega)) u fam

/-- For prime fields the cardinality budget itself implies the characteristic test. -/
theorem prime_classification {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 2013265923≤B) (hu : B≤2147483648) (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((B/3:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  exact classification dom hn (p:=p) (by omega) (by simpa only [ZMod.card] using hB) hl hu width

/-- The scalar evaluation code itself has the same sharp open good interval. -/
theorem scalar_prime_classification {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 2013265923≤B) (hu : B≤2147483648) :
    let t : ℝ≥0 := ((B/3:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) (ReedSolomon.code dom k : Set (I → ZMod p)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) (ReedSolomon.code dom k : Set (I → ZMod p)) δ≤tolerance ↔ δ<t := by
  simpa only [mcaDeltaStar_interleaved_eq,epsMCA_interleaved_eq] using prime_classification dom hn hB hl hu 1

/-- The exact worst-pair probability at every interior error count, independently
of a prescribed security tolerance. The size hypothesis permits an injective
linear projection on all keys at once. -/
theorem exact_eps (dom : I ↪ F) (hn : Fintype.card I=n) {p e : ℕ} [CharP F p]
    (hp : 1744830589<p) (hl : 671088641≤e) (hu : e≤715827881)
    (hq : (3*(e+1)).choose 2≤Fintype.card F) (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  refine le_antisymm (eps_upper dom hn (.inl hp) (by omega) hu) ?_
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  let r := n-e-67108863
  have h := ManyHeadLocatorMass.mass_over_field (h:=67108862) (d:=2) (r:=r) (k:=k) x ((e:ℝ≥0)/n)
    (by dsimp [r,n]; omega) (by decide) (by dsimp [k,r,n]; omega) (by
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub]
      exact_mod_cast (show n-e ≤ 67108862+r+1 by dsimp [r,n]; omega))
  have hcount : (2+1)*(n-(67108862+r))=3*(e+1) := by dsimp [r,n]; omega
  rw [hcount] at h
  have hret : 3*(e+1) ≤ AveragedPencilProjection.retained (3*(e+1)) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hq),Nat.sub_zero]
    exact le_max_left ..
  exact (ENNReal.div_le_div_right (by exact_mod_cast hret) _).trans h

/-- In all prime fields of the terminal budget class the field-size test for the
exact probability curve is automatic. Larger fields also satisfy it. -/
theorem prime_exact_eps {p e : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hl : 671088641≤e) (hu : e≤715827881) (hB : 2013265923≤p/2^128)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  have hq : (3*(e+1)).choose 2 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    apply (Nat.choose_le_choose 2 (by omega : 3*(e+1)≤2147483648)).trans
    rw [Nat.choose_two_right]
    omega
  simpa only [ZMod.card] using exact_eps dom hn (p:=p) (by omega) hl hu hq width

#print axioms prime_exact_eps
#print axioms family_cap
#print axioms eps_upper
#print axioms prime_classification
#print axioms scalar_prime_classification
#print axioms exact_eps
end ArkLib.ProximityGap.Frontier.UniversalCubicBudgetWindow
