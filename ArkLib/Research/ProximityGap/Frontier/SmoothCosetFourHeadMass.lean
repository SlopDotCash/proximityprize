/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothCosetCubicSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # A four-head MCA attack on every smooth multiplicative coset -/

set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothCosetFourHeadMass
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger SmoothFourHeadFibers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Number of simultaneously bad scalar labels for the given allocation of sites.
The power domain may be any multiplicative coset in any finite field. -/
theorem mass {s q r : ℕ} [NeZero s] [NeZero q] (hs : 0<s) (hr : 0<r) (hq : q=16*r)
    (dom : Fin (s*q) ↪ F) (c g : F) (hc : c≠0) (hg : orderOf g=s*q) (hd : ∀ i, dom i=c*g^i.val)
    (k G P T S H : ℕ) (δ : ℝ≥0)
    (hpart : ∀ j : Fin 4, s*(univ.filter (fun t : Fin q => bucket r t.val=j)).card =
      (![3*s,3*s,3*s,G+3*P+T] : Fin 4 → ℕ) j)
    (hdeg : G+3*s+1<k) (hkS : S+2 ≤ k) (hS : S ≤ G+3*(3*s)+3*P)
    (hH : H ≤ T) (hkC : k ≤ G+2*(3*s)+P) (hC : G+2*(3*s)+P ≤ S+(T-H))
    (hsize : (1-δ)*(s*q : ℕ) ≤ ((G+2*(3*s)+P+1:ℕ):ℝ≥0))
    (hf : 3*(s*q)<Fintype.card F) (hf16 : 16<Fintype.card F)
    (hfield : (3*(3*s)+3*P+(G+3*(3*s)+3*P-S)+3*(T-H)+4*H).choose 2 ≤ Nat.card F)
    (width : ℕ) [NeZero width] :
    ((3*(3*s)+3*P+(G+3*(3*s)+3*P-S)+3*(T-H)+4*H:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin (s*q) → F)) ^⋈ (Fin width)) δ := by
  rw [epsMCA_interleaved_eq]
  apply SmoothFourHeadFibers.mass dom δ k (3*s) G P T S H (fun x => bucket r x.modNat.val)
    (SmoothCosetCubicSeed.seed s c⁻¹ ((g^s)^r)) ?_ (fun j => SmoothCosetCubicSeed.degree _ _ _ j)
    (SmoothCosetCubicSeed.eval_iff hs hr hq c g hc hg dom hd) hdeg hkS hS hH hkC hC
    (by simpa only [Fintype.card_fin] using hsize) (by simpa only [Fintype.card_fin] using hf) hf16 hfield
  intro j
  rw [count_blocks (fun t : Fin q => bucket r t.val) j]
  exact hpart j

private theorem bucket_card {q : ℕ} (hq : q = 16 ∨ q = 32) (j : Fin 4) :
    (univ.filter (fun t : Fin q => bucket (q/16) t.val=j)).card =
      (![3,3,3,q-9] : Fin 4 → ℕ) j := by
  rcases hq with rfl|rfl <;> fin_cases j <;> decide

/-- At rates 1/4 and 1/8, every admissible defining-core size gives an explicit
four-head numerator, independently of the coset or the field characteristic. -/
theorem coset_mass {s q : ℕ} [NeZero s] [NeZero q] (hs : 2 ≤ s) (hqv : q = 16 ∨ q = 32)
    (dom : Fin (s*q) ↪ F) (c g : F) (hc : c≠0) (hg : orderOf g=s*q)
    (hd : ∀ i, dom i=c*g^i.val) (C : ℕ)
    (hlo : 7*s ≤ C+2) (hhi : 4*C+6 ≤ s*q+15*s)
    (hf : 3*(s*q)<Fintype.card F)
    (hfield : (4*(s*q)+21*s-(7*C+6)).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((4*(s*q)+21*s-(7*C+6):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom (4*s) : Set (Fin (s*q) → F)) ^⋈ (Fin width))
        ((↑(s*q-C-1):ℝ≥0)/(s*q:ℕ)) := by
  let r := q/16
  have hq : q=16*r := by rcases hqv with h|h <;> simp [r,h]
  have hr : 0<r := by rcases hqv with h|h <;> simp [r,h]
  let G := s-2
  let P := C+2-7*s
  let S := 4*s-2
  let T := s*q+11*s-(3*C+4)
  let H := s*q+15*s-(4*C+6)
  have hsn : 16*s ≤ s*q := by rcases hqv with h|h <;> rw [h] <;> omega
  have hhi' : C+1 ≤ s*q := by omega
  have ht : C=G+2*(3*s)+P := by dsimp [G,P]; omega
  have hu : 3*C+4 ≤ s*q+11*s := by omega
  have hcount : 3*(3*s)+3*P+(G+3*(3*s)+3*P-S)+3*(T-H)+4*H=4*(s*q)+21*s-(7*C+6) := by
    dsimp [G,P,S,T,H]; omega
  rw [← hcount]
  refine mass (s:=s) (q:=q) (r:=r) (by omega) hr hq dom c g hc hg hd (4*s) G P T S H _
    (fun j => ?_) (by dsimp [G]; omega) (by dsimp [S]; omega) (by dsimp [G,S,P]; omega)
    (by dsimp [H,T]; omega) (by omega) (by dsimp [H,T,S]; omega) ?_ hf (by omega)
    (hcount.symm ▸ hfield) width
  · change s*(univ.filter (fun t : Fin q => bucket (q/16) t.val=j)).card=_
    rw [bucket_card hqv]
    fin_cases j
    all_goals dsimp [G,P,T]
    all_goals first | omega | (rw [Nat.mul_sub]; omega)
  · rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast (show s*q≠0 by omega)),← Nat.cast_tsub]
    exact_mod_cast (show s*q-(s*q-C-1) ≤ G+2*(3*s)+P+1 by omega)

/-- The production length considered at the second designated prime. -/
abbrev n : ℕ := 1073741824

/-- The sponsor security tolerance. -/
abbrev tolerance : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128

omit [DecidableEq F] in
private theorem budget_lt {a : ℕ} (h : Fintype.card F/2^128<a) :
    tolerance<(a:ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  by_contra! hh
  apply h.not_ge
  exact (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0<2^128)).mp
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh)

/-- Largest admissible defining-core size in the four-head count for budget B. -/
def core (n s B : ℕ) : ℕ := min ((n+15*s-6)/4) ((4*n+21*s-(B+7))/7)

/-- A closed expression for an over-budget radius at both rates and every smooth length.
The size hypotheses separate the simultaneous scalar labels in the field. -/
theorem bad_at_core {s q : ℕ} [NeZero s] [NeZero q] (hs : 2 ≤ s) (hqv : q = 16 ∨ q = 32)
    (dom : Fin (s*q) ↪ F) (c g : F) (hc : c≠0) (hg : orderOf g=s*q) (hd : ∀ i, dom i=c*g^i.val)
    {B : ℕ} (hB : Fintype.card F/2^128 = B) (hrange : B+28*s ≤ 4*(s*q)+7)
    (hf : 3*(s*q)<Fintype.card F)
    (hfield : (4*(s*q)+21*s-(7*core (s*q) s B+6)).choose 2 ≤ Nat.card F)
    (width : ℕ) [NeZero width] :
    tolerance < epsMCA (F:=F) ((ReedSolomon.code dom (4*s) : Set (Fin (s*q) → F)) ^⋈ (Fin width))
      (((s*q-core (s*q) s B-1:ℕ):ℝ≥0)/(s*q:ℕ)) := by
  let C := core (s*q) s B
  have hsq : 16*s ≤ s*q := by rcases hqv with h|h <;> rw [h] <;> omega
  have hlo : 7*s ≤ C+2 := by dsimp [C,core]; omega
  have hhi : 4*C+6 ≤ s*q+15*s := by dsimp [C,core]; omega
  have hm : B < 4*(s*q)+21*s-(7*C+6) := by dsimp [C,core]; omega
  exact (budget_lt (hB ▸ hm)).trans_le (coset_mass hs hqv dom c g hc hg hd C hlo hhi hf hfield width)

/-- At all smooth lengths through 2^62, the positive sponsor budget itself
guarantees the field is large enough for the simultaneous four-head construction. -/
theorem operational_ceiling {s q B : ℕ} [NeZero s] [NeZero q] (hs : 2 ≤ s)
    (hqv : q = 16 ∨ q = 32) (hn : s*q ≤ 2^62) (dom : Fin (s*q) ↪ F)
    (c g : F) (hc : c≠0) (hg : orderOf g=s*q) (hd : ∀ i, dom i=c*g^i.val)
    (hB : Fintype.card F/2^128 = B) (hp : 0<B) (hrange : B+28*s ≤ 4*(s*q)+7)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom (4*s) : Set (Fin (s*q) → F)) ^⋈ (Fin width)) tolerance
      ≤ (((s*q-core (s*q) s B-1:ℕ):ℝ≥0)/(s*q:ℕ)) := by
  apply mcaDeltaStar_le_of_bad
  apply bad_at_core hs hqv dom c g hc hg hd hB hrange (by omega) _ width
  have hsq : 16*s ≤ s*q := by rcases hqv with h|h <;> rw [h] <;> omega
  have hlo : 7*s ≤ core (s*q) s B+2 := by unfold core; omega
  have hmax : 4*(s*q)+21*s-(7*core (s*q) s B+6) ≤ 2^64 := by omega
  rw [Nat.card_eq_fintype_card]
  exact (Nat.choose_le_choose 2 hmax).trans (by rw [Nat.choose_two_right]; omega)

/-- The eighth-rate ceiling and its extension through all dimensions up to the defining core size.
A positive sponsor budget suffices to separate every label. -/
theorem eighth_bad (dom : Fin n ↪ F) (c g : F) (hc : c≠0) (hg : orderOf g=n)
    (hd : ∀ i, dom i=c*g^i.val) {k : ℕ} (hl : 134217728 ≤ k) (hu : k ≤ 394264574)
    (hpos : 0<Fintype.card F/2^128) (hbudget : Fintype.card F/2^128<2239758344)
    (width : ℕ) [NeZero width] :
    tolerance<epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin n → F)) ^⋈ (Fin width))
      (679477249/1073741824) := by
  have hq : 2^128 ≤ Fintype.card F := by omega
  have hb := mass (s:=33554432) (q:=32) (r:=2) (by decide) (by decide) (by decide)
    dom c g hc hg hd k 33554430 159383552 260046850 134217726 2
    (679477249/1073741824) (by intro j; fin_cases j <;> decide)
    (by omega) (by omega) (by decide) (by decide) (by omega) (by decide)
    (by rw [tsub_mul,one_mul]; norm_num [tsub_le_iff_right])
    (by omega) (by omega) (by rw [Nat.card_eq_fintype_card,Nat.choose_two_right]; omega) width
  exact (budget_lt hbudget).trans_le hb

/-- The quarter-rate ceiling and its extension through all dimensions up to the defining core size.
A positive sponsor budget suffices to separate every label. -/
theorem quarter_bad (dom : Fin n ↪ F) (c g : F) (hc : c≠0) (hg : orderOf g=n)
    (hd : ∀ i, dom i=c*g^i.val) {k : ℕ} (hl : 268435456 ≤ k) (hu : k ≤ 508109969)
    (hpos : 0<Fintype.card F/2^128) (hbudget : Fintype.card F/2^128<2147483651)
    (width : ℕ) [NeZero width] :
    tolerance<epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin n → F)) ^⋈ (Fin width))
      (565631854/1073741824) := by
  have hq : 2^128 ≤ Fintype.card F := by omega
  have hb := mass (s:=67108864) (q:=16) (r:=1) (by decide) (by decide) (by decide)
    dom c g hc hg hd k 67108862 38347923 287609417 268435454 47934902
    (565631854/1073741824) (by intro j; fin_cases j <;> decide)
    (by omega) (by omega) (by decide) (by decide) (by omega) (by decide)
    (by rw [tsub_mul,one_mul]; norm_num [tsub_le_iff_right])
    (by omega) (by omega) (by rw [Nat.card_eq_fintype_card,Nat.choose_two_right]; omega) width
  exact (budget_lt hbudget).trans_le hb

#print axioms operational_ceiling
#print axioms bad_at_core
#print axioms coset_mass
#print axioms eighth_bad
#print axioms quarter_bad
end ArkLib.ProximityGap.Frontier.SmoothCosetFourHeadMass
