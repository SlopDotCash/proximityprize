/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SixteenFiberMass
import ArkLib.Research.ProximityGap.Frontier.SmoothOrderedMca
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # A sharp three-secant construction on smooth domains of length 48a+16 or 48a+32

Three secants of the parabola meet in pairs over three quarter fibers. Taking
the off-head center over the fourth fiber supplies all three distinct labels.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothSecantTriangle
open _root_.ProximityGap

private def ends : Fin 3 → Fin 4 × Fin 4 := ![(1,2),(2,0),(0,1)]
private def color (j : Fin 16) : Fin 4 := ⟨j.val % 4, by omega⟩
private def group : Fin 16 → Finset (Fin 3) :=
  ![{1,2},{0,2},{0,1},∅, {1,2},{0,2},{0,1},∅, {1,2},{0,2},{0,1},∅, {1,2},{0,2},{0,1},∅]
private theorem incident : ∀ j i, i ∈ group j ↔ color j = (ends i).1 ∨ color j = (ends i).2 := by decide
private def labels (j : Fin 16) := (group j)ᶜ
private def cut (a b : ℕ) : Fin 16 → ℕ :=
  ![2*a,2*a,2*a,3*a+1+b, 0,0,0,3*a+1+b, 0,0,0,b, 0,0,0,0]
private theorem cut_le (a b : ℕ) (j : Fin 16) : cut a b j ≤ 3*a+1+b := by
  fin_cases j <;> simp [cut] <;> omega

private theorem root_count (a b : ℕ) : (SixteenFiberMass.roots (3*a+1+b) (cut a b)).card = 12*a+2+3*b := by
  rw [SixteenFiberMass.card_roots _ _ (cut_le a b)]
  simp [Fin.sum_univ_succ, cut]
  omega
private theorem core_count (a b : ℕ) (i : Fin 3) :
    (SixteenFiberMass.core (3*a+1+b) (cut a b) group i).card = 32*a+10+11*b := by
  rw [SixteenFiberMass.card_core _ _ _ (cut_le a b)]
  fin_cases i <;> simp [Fin.sum_univ_succ, cut, group] <;> omega
private theorem fresh_count (a b : ℕ) (i : Fin 3) :
    (SixteenFiberMass.fresh (3*a+1+b) (cut a b) labels i).card = 16*a+6+5*b := by
  rw [SixteenFiberMass.fresh, SixteenFiberMass.card_selected _ _ (cut_le a b)]
  fin_cases i <;> simp [Fin.sum_univ_succ, cut, labels, group] <;> omega

variable {F : Type} [Field F]

private def H (p : Fin 4 → F) (i : Fin 3) (t : F) :=
  (p (ends i).1 + p (ends i).2)*t - p (ends i).1*p (ends i).2
private theorem gap (p : Fin 4 → F) (i : Fin 3) (t : F) :
    t^2 - H p i t = (t-p (ends i).1)*(t-p (ends i).2) := by unfold H; ring
private theorem same_product (p : Fin 4 → F) (i : Fin 3) (t : F) :
    (t^2-H p i t)*(t-p i.castSucc) = (t-p 0)*(t-p 1)*(t-p 2) := by
  rw [gap]
  fin_cases i <;> simp [ends] <;> ring

private theorem hit (p : Fin 4 → F) {j i} (h : i ∈ group j) :
    H p i (p (color j)) = (p (color j))^2 := by
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [gap]
  rcases (incident j i).mp h with h|h <;> rw [h] <;> simp

private theorem miss (p : Fin 4 → F) (hp : Function.Injective p) {j i} (h : i ∈ labels j) :
    H p i (p (color j)) ≠ (p (color j))^2 := by
  have hn : ¬(color j = (ends i).1 ∨ color j = (ends i).2) := by
    simpa [labels, incident] using h
  apply Ne.symm
  apply sub_ne_zero.mp
  rw [gap]
  exact mul_ne_zero (sub_ne_zero.mpr (hp.ne fun he => hn (.inl he)))
    (sub_ne_zero.mpr (hp.ne fun he => hn (.inr he)))

private def firstCenter (j : Fin 16) : F := if color j = 3 then 1 else 0

private theorem directions (p : Fin 4 → F) (hp : Function.Injective p) {j i k}
    (hi : i ∈ labels j) (hk : k ∈ labels j) (hik : i ≠ k) :
    (firstCenter j - (0:F))*(H p k (p (color j))-(p (color j))^2) ≠
      (firstCenter j - (0:F))*(H p i (p (color j))-(p (color j))^2) := by
  have hoff : color j = 3 :=
    (by decide : ∀ (j : Fin 16) (i k : Fin 3), i ∈ labels j → k ∈ labels j → i ≠ k → color j = 3)
      j i k hi hk hik
  simp only [firstCenter, ite_eq_left hoff, sub_zero, one_mul, ne_eq, sub_left_inj]
  intro he
  have hi0 := sub_ne_zero.mpr (miss p hp hi).symm
  have eq := (same_product p i (p (color j))).trans (same_product p k (p (color j))).symm
  rw [he] at eq
  exact hik (Fin.castSucc_injective _ (hp (sub_right_injective (mul_left_cancel₀ hi0 eq))))

private def poly (s : ℕ) (u : F) (p : Fin 4 → F) (i : Fin 3) : F[X] :=
  C ((p (ends i).1+p (ends i).2)*u^(4*s))*X^(4*s) - C (p (ends i).1*p (ends i).2)

private theorem poly_deg (s : ℕ) (u : F) (p : Fin 4 → F) (i : Fin 3) :
    (poly s u p i).natDegree ≤ 4*s := by
  unfold poly
  exact (natDegree_sub_le ..).trans (max_le (natDegree_C_mul_X_pow_le ..) (by rw [natDegree_C]; omega))

/-- Every ordered multiplicative coset in either length class has three times
the fresh sites per head in distinct labels at the integer third-length step. -/
theorem mass [Fintype F] (a b : ℕ) (D : Fin (16*(3*a+1+b)) ↪ F)
    (u g : F) (hu : u ≠ 0) (hg : orderOf g = 16*(3*a+1+b))
    (hd : ∀ i, D i = u*g^i.val) {k : ℕ} (hk : 24*a+8+8*b ≤ k) (hc : k ≤ 32*a+10+11*b)
    (hf : (48*a+18+15*b).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((48*a+18+15*b : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F:=F) ((ReedSolomon.code D k : Set (Fin (16*(3*a+1+b)) → F)) ^⋈ (Fin width))
        (((16*a+5+5*b : ℕ) : ℝ≥0) / (16*(3*a+1+b) : ℕ)) := by
  classical
  let s := 3*a+1+b
  let : NeZero s := ⟨by dsimp [s]; omega⟩
  let w := g^(4*s)
  have hw : orderOf w = 4 := by
    change orderOf (g^(4*s)) = 4
    rw [orderOf_pow_of_dvd (by dsimp [s]; omega : 4*s ≠ 0) (by rw [hg]; exact ⟨4,by dsimp [s]; omega⟩), hg]
    change 16*s/(4*s)=4
    rw [show 16*s = 4*(4*s) by omega, Nat.mul_div_cancel _ (by dsimp [s]; omega)]
  let p (v : Fin 4) := w^v.val
  have hp : Function.Injective p := fun i j eq =>
    Fin.ext ((IsPrimitiveRoot.iff_orderOf.mpr hw).pow_inj i.isLt j.isLt eq)
  have power (x : SixteenFiberMass.Grid s) : (u⁻¹*D (SixteenFiberMass.index s x))^(4*s) = p (color x.1) := by
    rw [Nat.mul_comm 4 s, pow_mul, SixteenFiberMass.power s D u g hu hg hd x, ← pow_mul]
    have perm : s*(x.1.val*4) = 4*s*x.1.val := by ac_rfl
    rw [← pow_mul, perm, pow_mul]
    change w^x.1.val = w^(x.1.val%4)
    rw [← hw, pow_mod_orderOf]
  have counts : (∑ i, (SixteenFiberMass.fresh s (cut a b) labels i).card) = 48*a+18+15*b := by
    simp only [s, fresh_count, Fin.sum_univ_succ]
    simp
    omega
  rw [epsMCA_interleaved_eq]
  have result := SixteenFiberMass.selected_mass s (cut a b) group D k (4*s)
    (((16*a+5+5*b : ℕ) : ℝ≥0) / (16*s : ℕ))
    (fun _ => 0) (poly s u⁻¹ p) (fun _ _ => 0) (fun i j => H p i (p (color j)))
    firstCenter (fun j => (p (color j))^2) labels (by simp) (by
      intro i x
      simp only [poly, eval_sub, eval_mul, eval_C, eval_pow, eval_X, H]
      rw [mul_assoc, ← mul_pow, power])
    (by intro j i h; refine ⟨?_,hit p h⟩; have hn :=
          (by decide : ∀ (j : Fin 16) (i : Fin 3), i ∈ group j → color j ≠ 3) j i h
        simp [firstCenter, hn])
    (fun _ _ => miss p hp) (fun _ _ _ => directions p hp)
    (by change (SixteenFiberMass.roots (3*a+1+b) (cut a b)).card + 4*s+1 < k; rw [root_count]; dsimp [s]; omega)
    (by simp) (poly_deg s u⁻¹ p) (by intro i; exact (core_count a b i).symm ▸ hc)
    (by
      intro i
      rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
      change _ ≤ (((SixteenFiberMass.core (3*a+1+b) (cut a b) group i).card+1 : ℕ) : ℝ≥0)
      rw [core_count]
      apply tsub_le_iff_right.mpr
      exact_mod_cast (show 16*(3*a+1+b) ≤ 32*a+10+11*b+1+(16*a+5+5*b) by omega))
    (by rw [counts]; exact hf)
  rwa [counts] at result

/-- Every coordinate ordering on every supplied smooth coset admits the
same three-edge construction. -/
theorem smooth_mass {I : Type} [Fintype F] [DecidableEq F] [Fintype I]
    (a b : ℕ) (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 16*(3*a+1+b))
    {k : ℕ} (hk : 24*a+8+8*b ≤ k) (hc : k ≤ 32*a+10+11*b)
    (hf : (48*a+18+15*b).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((48*a+18+15*b : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F:=F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width))
        (((16*a+5+5*b : ℕ) : ℝ≥0) / (16*(3*a+1+b) : ℕ)) := by
  let _ : NeZero (16*(3*a+1+b)) := ⟨by omega⟩
  apply SmoothOrderedMca.transfer D hn width
  intro E u g hu hg hd
  exact mass a b E u g hu hg hd hk hc hf width

/-- Dyadic lengths at least sixteen have one of the two possible residues
modulo 48, and both choices realize the integer third-length Hamming step. -/
theorem dyadic_parameters (h : ℕ) :
    ∃ a b : ℕ, b ≤ 1 ∧ 2^h = 3*a+1+b ∧
      (16*2^h)/3 = 16*a+5+5*b ∧ 3*((16*2^h)/3+1) = 48*a+18+15*b := by
  have nonzero : (2:ℕ)^h % 3 ≠ 0 := by
    intro he
    exact (by decide : ¬3 ∣ (2:ℕ)) (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero he))
  have small := Nat.mod_lt (2^h) (by decide : 0 < 3)
  exact ⟨2^h/3,2^h%3-1,by omega,by omega,by omega,by omega⟩

/-- At n/3 rounded down, all smooth dyadic domains of length at least 16
admit three times e+1 one-fresh scalars at half rate. -/
theorem dyadic {I : Type} [Fintype F] [DecidableEq F] [Fintype I]
    (h : ℕ) (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 16*2^h)
    (hf : (3*((16*2^h)/3+1)).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((3*((16*2^h)/3+1) : ℕ) : ℝ≥0∞)/Fintype.card F ≤
      epsMCA (F:=F) ((ReedSolomon.code D (8*2^h) : Set (I → F)) ^⋈ (Fin width))
        ((((16*2^h)/3 : ℕ) : ℝ≥0) / (16*2^h : ℕ)) := by
  obtain ⟨a,b,_,hs,he,hm⟩ := dyadic_parameters h
  have bound := smooth_mass a b D (hn.trans (congrArg (16*·) hs)) (k := 8*2^h)
    (by omega) (by omega) (hm ▸ hf) width
  rw [hm,he,hs]
  rw [hs] at bound
  exact bound

/-- The named-length half-rate ceiling applies throughout the 128-bit field
budget window, including its last admissible budget n+1. -/
theorem production {I : Type} [Fintype F] [DecidableEq F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2^30)
    (hf : 2^128 ≤ Fintype.card F) (hb : Fintype.card F / 2^128 < 1073741826)
    (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code D 536870912 : Set (I → F)) ^⋈ (Fin width))
    (1 : ℝ≥0∞)/(2:ℝ≥0∞)^128 < epsMCA (F:=F) code (357913941/1073741824) ∧
      MCAThresholdLedger.mcaDeltaStar (F:=F) code (1/(2:ℝ≥0∞)^128) ≤ 357913941/1073741824 := by
  dsimp only
  have val := smooth_mass 22369621 0 D hn (k := 536870912) (by decide) (by decide)
    (by rw [Nat.card_eq_fintype_card]; exact le_trans (by rw [Nat.choose_two_right]; decide) hf) width
  have below : (1 : ℝ≥0∞)/(2:ℝ≥0∞)^128 < (1073741826 : ℝ≥0∞)/Fintype.card F := by
    by_contra! h
    apply (Nat.not_le.mpr hb)
    apply (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have bad := below.trans_le val
  exact ⟨bad, MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ bad⟩

/-- Four simple secants either form a star or contain a vertex-disjoint
pair. With the incidence bounds in either case their cores miss this step. -/
theorem four_head_limit {a b c r d : ℕ} (hb : b ≤ 1) (hd : r+d+2 ≤ 24*a+8+8*b)
    (history : 4*c ≤ 48*a+16+16*b+3*(r+d) ∨
      (4*c ≤ 48*a+16+16*b+3*r+4*d ∧ 2*c ≤ 48*a+16+16*b+r)) : c < 32*a+10+11*b := by
  rcases history with star | ⟨four,two⟩ <;> omega

#print axioms four_head_limit
#print axioms dyadic
#print axioms smooth_mass
#print axioms production
#print axioms mass
end ArkLib.ProximityGap.Frontier.SmoothSecantTriangle
