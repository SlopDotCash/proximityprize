/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FiveEighthsPlateauThreshold

/-! # Bad-scalar counts on the Hamming steps below the five-eighths plateau

Write x for the number of Hamming steps below the plateau. The determinant bound
forces one of three noncollinear heads to spend at least 3x fresh sites per label,
or forces two heads to spend at least two. This bounds the bad labels for every word pair.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ThreeHeadDeficitWindow
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
open HalfPredecessorBadEventRichPointBridge
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Upper bound on the number of bad scalars for one received pair. -/
def ceiling (e x : ℕ) : ℕ := 2*(e+1)+max 197 (1+e/(3*x))

/-- A single received pair obeys the deficit bound on every injective domain. -/
theorem family_cap (dom : I ↪ F) (hn : Fintype.card I=n) {p e x : ℕ} [CharP F p]
    (hp : 1744830589<p) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (u : Code.WordStack F (Fin 2) I) :
    (canonicalBadScalarRichPointFamily dom (k:=k) ((e:ℝ≥0)/n) u (by decide)).G.card≤ceiling e x := by
  classical
  let fam := canonicalBadScalarRichPointFamily dom (k:=k) ((e:ℝ≥0)/n) u (by decide)
  change fam.G.card≤ceiling e x
  have ht : ⌈(1-(e:ℝ≥0)/n)*(Fintype.card I:ℝ≥0)⌉₊=n-e := by
    rw [hn]
    have h := TwoCorePackingThreshold.agreement_ceiling e (by change e≤1073741824; omega)
    rw [Fintype.card_fin] at h
    exact h
  by_contra! hb
  have h197 := Nat.le_max_left 197 (1+e/(3*x))
  unfold ceiling at hb
  obtain ⟨H,hH,hthree,hbig,hex⟩ := FiveEighthThreeHeadCover.cover_above_budget fam hp hn hl
    (by omega) ht (s:=184) (by decide) (by decide) (by omega)
  exact hb.not_ge (PlateauThreeHeadPredecessor.cap_at_deficit fam hn he hx hl (by rw [ht]; dsimp [n]; omega)
    H hH hthree.le hbig (hex.trans (by omega)))

/-- The normalized bound at every positive interleaving width. -/
theorem eps_upper (dom : I ↪ F) (hn : Fintype.card I=n) {p e x : ℕ} [CharP F p]
    (hp : 1744830589<p) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) ≤
      ((ceiling e x:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  exact epsMCA_le_of_badCount_le _ _ _ (family_cap dom hn hp he hx hl)

/-- In a sufficiently large field the two exceptional heads realize all
2(e+1) different labels simultaneously. -/
theorem eps_interval (dom : I ↪ F) (hn : Fintype.card I=n) {p e x : ℕ} [CharP F p]
    (hp : 1744830589<p) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (hq : (2*(e+1)).choose 2≤Fintype.card F) (width : ℕ) [NeZero width] :
    let v := epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n)
    ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞)≤v ∧
      v≤((ceiling e x:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  refine ⟨?_,eps_upper dom hn hp he hx hl width⟩
  rw [epsMCA_interleaved_eq]
  let eqv := Fintype.equivFinOfCardEq hn
  let domain := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm domain dom (fun _ => rfl)]
  have hmass := ExceptionalHeadLocatorMass.grid_mass (m:=2) (t:=n-e) (k:=k) domain ((e:ℝ≥0)/n)
    (by decide) (by decide) (by dsimp [n,k]; omega) (Nat.sub_le ..) (by dsimp [n,k]; omega)
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub])
  rw [show n-(n-e)=e by dsimp [n]; omega] at hmass
  have hret : 2*(e+1) ≤ AveragedPencilProjection.retained (2*(e+1)) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hq),Nat.sub_zero]
    exact le_max_left ..
  exact (ENNReal.div_le_div_right (by exact_mod_cast hret) _).trans hmass

/-- Two exceptional heads already cause failure when twice the fresh-label count exceeds the budget. -/
theorem two_head_bad (dom : I ↪ F) (hn : Fintype.card I=n) {e : ℕ}
    (hl : 503316480≤e) (hu : e≤671088640) (hB : Fintype.card F/2^128<2*(e+1)) :
    tolerance < epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) ((e:ℝ≥0)/n) := by
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have hs := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  exact ExceptionalHeadLocatorMass.over_budget_128 (m:=2) (t:=n-e) x _
    (by decide) (by decide) (by dsimp [n,k]; omega) (Nat.sub_le ..) (by dsimp [n,k]; omega)
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub]) (by omega)
    (by rw [show n-(n-e)=e by dsimp [n]; omega]; exact hB)

/-- A verified numerator cap below the sponsor budget gives a safe step. Two
exceptional heads or the three-head attack give the stated failing step. -/
theorem prime_bracket_of_cap {p B e M : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I=n) (hB : p/2^128=B) (hlB : 1006632960≤B) (huB : B≤2013265922)
    (width : ℕ) [NeZero width] (hcap : M≤B)
    (hg : epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n)
      ≤ (M:ℝ≥0∞)/(Fintype.card (ZMod p):ℝ≥0∞)) :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    epsMCA (F:=ZMod p) C ((e:ℝ≥0)/n)≤tolerance ∧
      tolerance<epsMCA (F:=ZMod p) C (((min 671088640 (B/2):ℕ):ℝ≥0)/n) := by
  dsimp only
  have hrat := (BoundarySecurityBudget.count_ratio_le_iff (Fintype.card_pos (α:=ZMod p)) (by decide : 0<2^128)).2
    (by simpa only [ZMod.card,hB] using hcap : M≤Fintype.card (ZMod p)/2^128)
  refine ⟨hg.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hrat),?_⟩
  rw [epsMCA_interleaved_eq]
  by_cases hh : B/2≤671088640
  · rw [min_eq_right hh]
    exact two_head_bad dom hn (by omega) hh (by rw [ZMod.card,hB]; omega)
  · rw [min_eq_left (by omega : 671088640≤B/2)]
    have eqn : ((671088640:ℕ):ℝ≥0)/n=5/8 := by norm_num [n]
    rw [eqn]
    exact FiveEighthsPlateauThreshold.endpoint_bad dom hn (by rw [ZMod.card,hB]; omega)

/-- The uniform cap supplies a safe Hamming step; either the two-head attack or
the three-head plateau attack supplies the failing step. -/
theorem prime_bracket {p B e x : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (huB : B≤2013265922)
    (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e) (hbudget : ceiling e x≤B)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    epsMCA (F:=ZMod p) C ((e:ℝ≥0)/n)≤tolerance ∧
      tolerance<epsMCA (F:=ZMod p) C (((min 671088640 (B/2):ℕ):ℝ≥0)/n) := by
  dsimp only
  have hlB : 1220000199≤B := by
    have h197 := Nat.le_max_left 197 (1+e/(3*x))
    unfold ceiling at hbudget
    omega
  exact prime_bracket_of_cap dom hn hB (by omega) huB width hbudget
    (eps_upper dom hn (p:=p) (by omega) he hx hl width)

/-- A safe Hamming step puts the supremum at least one whole step higher. -/
theorem successor_le_supremum (dom : I ↪ F) (hn : Fintype.card I=n) {e : ℕ}
    (he : e<n) (width : ℕ) [NeZero width]
    (hg : epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n)≤tolerance) :
    ((e+1:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance := by
  rw [epsMCA_interleaved_eq] at hg
  rw [mcaDeltaStar_interleaved_eq]
  let eqv := Fintype.equivFinOfCardEq hn
  let domain := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm domain dom (fun _ => rfl)]
  apply MCAAdjacentFloorExactPin.latticeRadius_le_mcaDeltaStar_of_predecessor_good
    (a:=e+1) (by omega) (by omega)
  rw [← MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm domain dom (fun _ => rfl)]
  simpa only [MCAAdjacentFloorExactPin.predecessorRadius, Nat.add_one_sub_one] using hg

/-- The operational supremum lies from the Hamming step immediately after the
verified safe predecessor through the verified failing step. -/
theorem prime_supremum_bracket {p B e x : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (huB : B≤2013265922) (he : e+x=671088640) (hx : 0<x)
    (hl : 610000000≤e) (hbudget : ceiling e x≤B) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    ((e+1:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=ZMod p) C tolerance ∧
      mcaDeltaStar (F:=ZMod p) C tolerance ≤ ((min 671088640 (B/2):ℕ):ℝ≥0)/n := by
  dsimp only
  obtain ⟨hg,hbad⟩ := prime_bracket dom hn hB huB he hx hl hbudget width
  exact ⟨successor_le_supremum dom hn (by dsimp [n]; omega) width hg,mcaDeltaStar_le_of_bad _ _ hbad⟩

/-- On this budget interval the possible first failing counts lie within 99 Hamming steps. -/
theorem two_head_bracket {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 1220000199≤B) (hu : B≤1339910288) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    (((B-197)/2:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=ZMod p) C tolerance ∧
      mcaDeltaStar (F:=ZMod p) C tolerance ≤ ((B/2:ℕ):ℝ≥0)/n := by
  let e := (B-197)/2-1
  let x := 671088640-e
  have he : 610000000≤e := by dsimp [e]; omega
  have heu : e≤669955044 := by dsimp [e]; omega
  have hx : 0<x := by dsimp [x]; omega
  have hr : e / (3*x) < 197 := (Nat.div_lt_iff_lt_mul (by omega : 0<3*x)).2 (by dsimp [x]; omega)
  have hcap : ceiling e x≤B := by
    unfold ceiling
    rw [max_eq_left (by omega : 1+e/(3*x)≤197)]
    dsimp [e]
    omega
  have h := prime_supremum_bracket dom hn hB (by omega) (e:=e) (x:=x) (by dsimp [x]; omega) hx he hcap width
  rw [show e+1=(B-197)/2 by dsimp [e]; omega, min_eq_right (by omega : B/2≤671088640)] at h
  exact h

/-- Over more than 111 million integer budgets below the proven plateau interval,
only its endpoint and its immediate predecessor can be the first failure. -/
theorem two_candidate_window {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hl : 1454025385≤p/2^128) (hu : p/2^128≤1565873493) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    epsMCA (F:=ZMod p) C (((671088638:ℕ):ℝ≥0)/n)≤tolerance ∧
      tolerance<epsMCA (F:=ZMod p) C (((671088640:ℕ):ℝ≥0)/n) := by
  have h := prime_bracket dom hn rfl (by omega) (e:=671088638) (x:=2)
    (by decide) (by decide) (by decide) ((by decide : ceiling 671088638 2≤1454025385).trans hl) width
  simpa only [min_eq_left (by omega : 671088640≤p/2^128/2)] using h

#print axioms two_head_bracket
#print axioms two_candidate_window
#print axioms prime_supremum_bracket
#print axioms eps_interval
#print axioms family_cap
#print axioms prime_bracket
end ArkLib.ProximityGap.Frontier.ThreeHeadDeficitWindow
