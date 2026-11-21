/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.OnePunctureRetention
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicBudgetWindow
import ArkLib.Research.ProximityGap.Frontier.ExceptionalHeadLocatorMass

/-! # Cubic security thresholds after adding evaluation sites

At fixed dimension and error count, double counting punctures increases a cap
strictly below twice the length by at most one per site. The remainder of the
field budget modulo three pays for these extra sites at the predecessor. The
three-head construction still gives strict failure at the next error count.
-/
set_option autoImplicit false
noncomputable section
open Finset Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.OnePunctureCubicThreshold
open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity HalfPredecessorBadEventRichPointBridge
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- Adding any number of evaluation sites at the same dimension and error
count increases the cubic bound by at most the number of new sites. -/
theorem count {p E : ℕ} [CharP F p] (hp : 1744830589 < p)
    (hl : 671088640 ≤ E) (hu : E ≤ 715827881) (r : ℕ)
    (dom : Fin (n+r) ↪ F) (u v : Fin (n+r) → F) :
    (univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin (n+r) → F))
      ((E : ℝ≥0)/(n+r:ℕ)) u v g).card ≤ 3*(E+1)+r := by
  classical
  induction r with
  | zero =>
    let a : WordStack F (Fin 2) (Fin n) := ![u,v]
    let fam := canonicalBadScalarRichPointFamily dom (k:=k) ((E:ℝ≥0)/n) a (by decide)
    have ht := TwoCorePackingThreshold.agreement_ceiling E (by change E≤1073741824; omega)
    exact UniversalCubicBudgetWindow.family_cap dom (Fintype.card_fin _) hp hl hu _ ht a fam
  | succ r ih =>
    have h := OnePunctureRetention.count (by unfold n; omega : 0<n+r)
      (by unfold k n; omega : k + 2 ≤ (n+r)+1-E) dom u v
      (fun i => ih (punctureDom dom i) (u ∘ i.succAbove) (v ∘ i.succAbove))
    let A := (univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin (n+(r+1)) → F))
      ((E:ℝ≥0)/(n+(r+1):ℕ)) u v g).card
    change A*(n+r) ≤ (n+r+1)*(3*(E+1)+r) at h
    change A ≤ 3*(E+1)+(r+1)
    by_contra! hlarge
    have hmul := Nat.mul_le_mul_right (n+r) (show 3*(E+1)+r+2≤A by omega)
    rw [Nat.add_mul] at hmul h
    rw [Nat.one_mul,mul_comm (n+r) (3*(E+1)+r)] at h
    have hsmall : 3*(E+1)+r<2*(n+r) := by unfold n; omega
    omega

/-- Complete classification on longer domains when the field-budget remainder
covers the added sites and the three locator blocks fit at the successor. -/
theorem classification {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    {p B r : ℕ} [CharP F p] (hp : 1744830589 < p) (dom : I ↪ F)
    (hn : Fintype.card I=n+r) (hB : Fintype.card F/2^128=B)
    (hl : 2013265923≤B) (hu : B≤2147483648) (hr : r≤B%3)
    (hfit : 2*(n+r-k) ≤ 3*(B/3)) (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((B/3:ℕ):ℝ≥0)/(n+r:ℕ)
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  classical
  let : NeZero (n+r) := ⟨by unfold n; omega⟩
  let e := B/3
  let t : ℝ≥0 := (e:ℝ≥0)/(n+r:ℕ)
  let prev : ℝ≥0 := ((e-1:ℕ):ℝ≥0)/(n+r:ℕ)
  let d := Fintype.equivFinOfCardEq hn
  let x := d.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl) k
  have hprev : epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin (n+r) → F)) prev≤tolerance := by
    have cap := epsMCA_le_of_badCount_le (ReedSolomon.code x k : Set (Fin (n+r) → F)) prev
      (3*(e-1+1)+r) (fun u => count hp (by dsimp [e]; omega) (by dsimp [e]; omega) r x (u 0) (u 1))
    have ratio := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).2
      (show 3*(e-1+1)+r ≤ Fintype.card F/2^128 by dsimp [e]; omega)
    exact cap.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ratio)
  have hsmall := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  have hbad : tolerance < epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin (n+r) → F)) t := by
    apply ExceptionalHeadLocatorMass.over_budget_128 x t (m:=3) (t:=n+r-e) (by decide) (by decide)
    · dsimp [e,k,n]; omega
    · omega
    · dsimp [e,k,n] at *; omega
    · dsimp [t]
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n+r)),Nat.cast_tsub]
    · omega
    · dsimp [e,n]; omega
  have heq : mcaDeltaStar (F:=F) (ReedSolomon.code dom k : Set (I → F)) tolerance=t := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a:=e) (by dsimp [e]; omega) (by dsimp [e,n]; omega) _ _ hprev hbad
  rw [← hre] at hbad
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hbad.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    have h := mcaDeltaStar_le_of_bad _ _ bad
    rw [heq] at h
    exact hδ.not_ge h

local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- For the named second prime, both one and two added evaluation coordinates
preserve the first failing error count for every domain and positive width. -/
theorem second_prime {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] {r : ℕ} (hr : r≤2)
    (dom : I ↪ ZMod PrizeShapePrimeP30Second.P) (hn : Fintype.card I=n+r)
    (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := 715827882/(n+r:ℕ)
    mcaDeltaStar (F:=ZMod PrizeShapePrimeP30Second.P) ((ReedSolomon.code dom k : Set (I → ZMod PrizeShapePrimeP30Second.P)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod PrizeShapePrimeP30Second.P) ((ReedSolomon.code dom k : Set (I → ZMod PrizeShapePrimeP30Second.P)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  exact classification (p:=PrizeShapePrimeP30Second.P) (B:=2147483648) (by decide) dom hn
    (by rw [ZMod.card]; decide) (by decide) (by decide) hr (by unfold n k; omega) width

#print axioms count
#print axioms classification
#print axioms second_prime
end ArkLib.ProximityGap.Frontier.OnePunctureCubicThreshold
