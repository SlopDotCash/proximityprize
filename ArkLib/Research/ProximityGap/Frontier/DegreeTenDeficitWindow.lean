/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeficitWindow

/-! # Bad-scalar counts on the Hamming steps below the five-eighths plateau

Write x for the number of Hamming steps below the plateau. The determinant bound
forces one of three noncollinear heads to spend at least 3x fresh sites per label,
or forces two heads to spend at least two. This bounds the bad labels for every word pair.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.DegreeTenDeficitWindow
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
open HalfPredecessorBadEventRichPointBridge
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Upper bound on the number of bad scalars for one received pair. -/
def ceiling (e x : ℕ) : ℕ := 2*(e+1)+max 58 (1+e/(3*x))

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
  have h58 := Nat.le_max_left 58 (1+e/(3*x))
  unfold ceiling at hb
  obtain ⟨H,hH,hthree,hbig,hex⟩ := FiveEighthThreeHeadCover.degree_ten_cover fam hp hn hl
    (by omega) ht (s:=48) (by decide) (by decide) (by omega)
  exact hb.not_ge (PlateauThreeHeadPredecessor.cap_at_small_deficit fam hn he hx hl (by rw [ht]; dsimp [n]; omega)
    H hH hthree.le hbig (Nat.le_max_right ..) (hex.trans (by omega)))

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
  exact ⟨(ThreeHeadDeficitWindow.eps_interval dom hn hp he hx hl hq width).1,eps_upper dom hn hp he hx hl width⟩

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
  have hlB : 1220000060≤B := by
    have h58 := Nat.le_max_left 58 (1+e/(3*x))
    unfold ceiling at hbudget
    omega
  exact ThreeHeadDeficitWindow.prime_bracket_of_cap dom hn hB (by omega) huB width hbudget
    (eps_upper dom hn (p:=p) (by omega) he hx hl width)

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
  exact ⟨ThreeHeadDeficitWindow.successor_le_supremum dom hn (by dsimp [n]; omega) width hg,
    mcaDeltaStar_le_of_bad _ _ hbad⟩

/-- On this budget interval the possible first failing counts lie within 29 Hamming steps. -/
theorem two_head_bracket {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=B) (hl : 1220000060≤B) (hu : B≤1334507755) (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width))
    (((B-58)/2:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=ZMod p) C tolerance ∧
      mcaDeltaStar (F:=ZMod p) C tolerance ≤ ((B/2:ℕ):ℝ≥0)/n := by
  let e := (B-58)/2-1
  let x := 671088640-e
  have he : 610000000≤e := by dsimp [e]; omega
  have heu : e≤667253847 := by dsimp [e]; omega
  have hx : 0<x := by dsimp [x]; omega
  have hr : e / (3*x) < 58 := (Nat.div_lt_iff_lt_mul (by omega : 0<3*x)).2 (by dsimp [x]; omega)
  have hcap : ceiling e x≤B := by
    unfold ceiling
    rw [max_eq_left (by omega : 1+e/(3*x)≤58)]
    dsimp [e]
    omega
  have h := prime_supremum_bracket dom hn hB (by omega) (e:=e) (x:=x) (by dsimp [x]; omega) hx he hcap width
  rw [show e+1=(B-58)/2 by dsimp [e]; omega, min_eq_right (by omega : B/2≤671088640)] at h
  exact h

#print axioms two_head_bracket
#print axioms prime_supremum_bracket
#print axioms eps_interval
#print axioms family_cap
#print axioms prime_bracket
end ArkLib.ProximityGap.Frontier.DegreeTenDeficitWindow
