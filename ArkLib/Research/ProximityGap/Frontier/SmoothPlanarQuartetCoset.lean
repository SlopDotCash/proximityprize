/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothPlanarQuartetSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import Mathlib.Tactic.ComputeDegree

/-! # Four planar cubics on every smooth quarter-rate evaluation coset -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothPlanarQuartetCoset
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SmoothPlanarQuartetSeed

variable {K : Type} [Field K]


private theorem projection [Fintype K] (z : Fin 16 → Fin 4 → K × K) (hcard : 256<Fintype.card K) :
    ∃ c : K, ∀ r i j, z r i ≠ z r j →
      c*(z r i).1+(z r i).2 ≠ c*(z r j).1+(z r j).2 := by
  classical
  let bad (x : Fin 16 × Fin 4 × Fin 4) :=
    ((z x.1 x.2.2).2-(z x.1 x.2.1).2)/((z x.1 x.2.1).1-(z x.1 x.2.2).1)
  have count : (univ.image bad).card < (univ : Finset K).card := by
    exact card_image_le.trans_lt (by simpa using hcard)
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card count
  refine ⟨c,?_⟩
  intro r i j hz eq
  by_cases hu : (z r i).1=(z r j).1
  · exact hz (Prod.ext hu (by rw [hu] at eq; exact add_left_cancel eq))
  · apply hc
    apply mem_image.mpr
    refine ⟨(r,i,j), mem_univ _, ?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hu)).mpr
    linear_combination -eq

private abbrev S (m : ℕ) := 4*m
private abbrev N (m : ℕ) := 16*S m
private abbrev Grid (m : ℕ) := Σ _ : Fin 16, Fin (S m)
private noncomputable def index (m : ℕ) : Grid m ≃ Fin (N m) :=
  (Equiv.sigmaEquivProd _ _).trans (((Equiv.prodComm _ _).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm (S m) 16)))

private def cut (m : ℕ) (j : Fin 16) : ℕ :=
  if j=1 ∨ j=3 then m-1 else if j=9 ∨ j=11 then m else 0
private theorem cut_le (m : ℕ) (j : Fin 16) : cut m j ≤ S m := by
  unfold cut; split_ifs <;> dsimp [S] <;> omega
private def lower (m : ℕ) (j : Fin 16) : Finset (Fin (S m)) :=
  univ.filter (fun r => r.val < cut m j)
private theorem card_lower (m : ℕ) (j : Fin 16) : (lower m j).card = cut m j := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le m j)]
private abbrev Selection := Fin 16 → Bool → Bool
private def row (m : ℕ) (take : Selection) (j : Fin 16) : Finset (Fin (S m)) :=
  (if take j false then lower m j else ∅) ∪ (if take j true then (lower m j)ᶜ else ∅)
private def selected (m : ℕ) (take : Selection) : Finset (Fin (N m)) :=
  (univ.sigma (row m take)).map (index m).toEmbedding
private theorem card_selected (m : ℕ) (take : Selection) :
    (selected m take).card = ∑ j : Fin 16,
      ((if take j false then cut m j else 0) + (if take j true then S m - cut m j else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro j _
  cases h1 : take j false <;> cases h2 : take j true <;>
    simp [row, h1, h2, card_lower, card_compl, Nat.add_sub_of_le (cut_le m j)]
private theorem mem_selected (m : ℕ) (take : Selection) (u : Grid m) :
    index m u ∈ selected m take ↔ take u.1 (decide (cut m u.1 ≤ u.2.val)) := by
  classical
  change (index m).toEmbedding u ∈ (univ.sigma (row m take)).map (index m).toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut m u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]

private def rootSel : Selection := fun _ high => !high
private def coreSel (i : Fin 4) : Selection := fun r high => !high || decide (i∈group r)
private def roots (m : ℕ) := selected m rootSel
private def core (m : ℕ) (i : Fin 4) := selected m (coreSel i)
private def own (m : ℕ) (x : Fin (N m)) := owner ((index m).symm x).1
private def full (m : ℕ) (u : Grid m) := decide (cut m u.1 ≤ u.2.val)
private theorem origin (m : ℕ) (u : Grid m) : index m u∈roots m ↔ full m u=false := by
  rw [roots,mem_selected]; simp [rootSel,full]
private theorem inside (m : ℕ) (u : Grid m) (i : Fin 4) :
    index m u∈core m i ↔ full m u=false ∨ i∈group u.1 := by
  rw [core,mem_selected]; simp [coreSel,full]
private theorem own_at (m : ℕ) (u : Grid m) : own m (index m u)=owner u.1 := by simp [own]

private theorem root_count (m : ℕ) (hm : 0 < m) : (roots m).card=4*m-2 := by
  rw [roots,card_selected]
  norm_num [Fin.sum_univ_succ,rootSel,cut]
  omega
private theorem core_count (m : ℕ) (hm : 0 < m) (j : Fin 4) :
    (core m j).card=(![31*m-1,31*m-1,31*m-2,31*m-2] : Fin 4 → ℕ) j := by
  rw [core,card_selected]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,coreSel,group,cut,S] <;> omega

private def seed (w : K) (i : Fin 4) : K[X] × K[X] :=
  heads (C (w^2)) (C (w^14)) Polynomial.X i

private def cubic (w c : K) (i : Fin 4) (project : Bool) : K[X] :=
  if project then C c*(seed w i).1+(seed w i).2 else (seed w i).1

private theorem degree (w c : K) (i : Fin 4) (project : Bool) :
    (cubic w c i project).natDegree ≤ 3 := by
  fin_cases i <;> cases project <;> simp [cubic,seed,heads] <;> compute_degree!

private def lift (m : ℕ) (w c u : K) (i : Fin 4) (project : Bool) :=
  (cubic w c i project).comp ((C u*Polynomial.X)^S m)

private theorem lift_degree (m : ℕ) (w c u : K) (i : Fin 4) (project : Bool) :
    (lift m w c u i project).natDegree ≤ 3*S m := by
  apply natDegree_comp_le.trans
  apply Nat.mul_le_mul (degree w c i project)
  simpa using (natDegree_pow_le.trans (Nat.mul_le_mul_left (S m)
    ((natDegree_C_mul_le u (Polynomial.X:K[X])).trans natDegree_X_le)))

private def value (w c t : K) (i : Fin 4) (project : Bool) :=
  let z := heads (w^2) (w^14) t i
  if project then c*z.1+z.2 else z.1

private theorem lift_eval (m : ℕ) (w c u x : K) (i : Fin 4) (project : Bool) :
    (lift m w c u i project).eval x=value w c ((u*x)^S m) i project := by
  rw [lift,eval_comp]
  fin_cases i <;> cases project <;> simp [cubic,seed,heads,value]

private theorem power (m : ℕ) (dom : Fin (N m) ↪ K) (u g : K) (hu : u≠0)
    (hg : orderOf g=N m) (hd : ∀ i, dom i=u*g^i.val) (x : Grid m) :
    (u⁻¹*dom (index m x))^S m = (g^S m)^x.1.val := by
  rw [hd,inv_mul_cancel_left₀ hu]
  change (g^(x.1.val+16*x.2.val))^S m=_
  have h : 16*x.2.val*S m=N m*x.2.val := by dsimp only [N]; ac_rfl
  have hg' : g^N m=1 := hg ▸ pow_orderOf_eq_one g
  have hr : (g^(16*x.2.val))^S m=1 := by rw [← pow_mul,h,pow_mul,hg',one_pow]
  rw [pow_add,mul_pow,hr,mul_one,← pow_mul,Nat.mul_comm,pow_mul]

/-- On a length-`64m` multiplicative coset, four cubics give at least `132m+6` bad
labels at `33m+1` errors. The same received-pair construction covers the whole
dimension interval from quarter rate through the minimum defining core. -/
theorem mass [Fintype K] {m : ℕ} [NeZero m] (dom : Fin (16*(4*m)) ↪ K) (u g : K) (hu : u≠0)
    (hg : orderOf g=16*(4*m)) (hd : ∀ i, dom i=u*g^i.val) {k : ℕ}
    (hk : 16*m ≤ k) (hupper : k≤31*m-2) (hcard : 256<Fintype.card K)
    (hf : (132*m+6).choose 2 ≤ Nat.card K) (width : ℕ) [NeZero width] :
    ((132*m+6 : ℕ):ℝ≥0∞)/(Fintype.card K : ℝ≥0∞) ≤
      epsMCA (F:=K) ((ReedSolomon.code dom k : Set (Fin (16*(4*m)) → K)) ^⋈ (Fin width))
        (((33*m+1:ℕ):ℝ≥0)/(16*(4*m):ℕ)) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let w := g^S m
  have hw : orderOf w=16 := by
    change orderOf (g^S m)=16
    rw [orderOf_pow_of_dvd (by dsimp [S]; omega : S m≠0) (hg ▸ dvd_mul_left (S m) 16),hg]
    exact Nat.mul_div_cancel _ (by omega)
  let z (r : Fin 16) := heads (w^2) (w^14) (w^r.val)
  obtain ⟨c,hc⟩ := projection z hcard
  have noeq (r : Fin 16) (i : Fin 4) (hi : i∉group r) : z r i ≠ z r (owner r) := by
    have other : ∀ q a, a∉group q → ∃ b, b∉group q ∧ a≠b := by decide
    obtain ⟨j,hj,hn⟩ := other r i hi
    have h := (geometry w hw r).2 i j hi hj hn
    change det (z r (owner r)) (z r i) (z r j)≠0 at h
    intro he
    apply h
    rw [he]
    simp [det]
  let poly (i : Fin 4) (pr : Bool) := lift m w c u⁻¹ i pr
  have eval (x : Grid m) (i : Fin 4) (pr : Bool) : (poly i pr).eval (dom (index m x)) =
      (if pr then c*(z x.1 i).1+(z x.1 i).2 else (z x.1 i).1) := by
    change (lift m w c u⁻¹ i pr).eval _=_
    rw [lift_eval,power m dom u g hu hg hd]
    rfl
  have counts : (∑ i, (core m i)ᶜ.card)=132*m+6 := by
    simp only [card_compl,core_count m hm,Fintype.card_fin,Fin.sum_univ_succ]
    change (16*(4*m)-(31*m-1))+(16*(4*m)-(31*m-1)+(16*(4*m)-(31*m-2)+(16*(4*m)-(31*m-2)+0)))=132*m+6
    omega
  have small (i : Fin 4) : 31*m-2 ≤ (core m i).card := by
    rw [core_count m hm]; fin_cases i <;> dsimp <;> omega
  rw [epsMCA_interleaved_eq]
  rw [← counts]
  apply PlanarQuartetMass.mass dom k (3*S m) _ (fun i => poly i false) (fun i => poly i true)
    (roots m) (own m) (core m)
  · rw [root_count m hm]
    dsimp [S]; omega
  · exact fun i => lift_degree ..
  · exact fun i => lift_degree ..
  · intro i x hx
    obtain ⟨y,rfl⟩ := (index m).surjective x
    rw [origin] at hx
    rw [inside]; exact Or.inl hx
  · intro i x hx hr
    obtain ⟨y,rfl⟩ := (index m).surjective x
    rw [origin] at hr
    rw [inside] at hx
    have h := (geometry w hw y.1).1 i (hx.resolve_left hr)
    change z y.1 i=z y.1 (owner y.1) at h
    simp only [eval, own_at, Bool.false_eq_true, ↓reduceIte,h]
    exact ⟨trivial,trivial⟩
  · intro i x hx
    obtain ⟨y,rfl⟩ := (index m).surjective x
    rw [inside] at hx
    simpa only [eval,own_at,↓reduceIte] using hc y.1 i (owner y.1) (noeq y.1 i (fun h => hx (Or.inr h)))
  · intro x i j hi hj hne
    obtain ⟨y,rfl⟩ := (index m).surjective x
    rw [inside] at hi hj
    have h := (geometry w hw y.1).2 i j (fun h => hi (Or.inr h)) (fun h => hj (Or.inr h)) hne
    change det (z y.1 (owner y.1)) (z y.1 i) (z y.1 j)≠0 at h
    simp only [eval,own_at,Bool.false_eq_true,↓reduceIte]
    intro he
    apply h
    unfold det
    linear_combination -he
  · exact fun i => hupper.trans (small i)
  · intro i
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by positivity),← Nat.cast_tsub]
    exact_mod_cast (show 16*(4*m)-(33*m+1)≤(core m i).card+1 by have h:=small i; omega)
  · rwa [counts]

/-- The positive sponsor budget gives label separation throughout the production
length range. Every over-budget instance fails by `33m+1` errors. -/
theorem operational_ceiling [Fintype K] {m : ℕ} [NeZero m] (dom : Fin (16*(4*m)) ↪ K) (u g : K) (hu : u≠0)
    (hg : orderOf g=16*(4*m)) (hd : ∀ i, dom i=u*g^i.val) {k : ℕ}
    (hk : 16*m ≤ k) (hupper : k≤31*m-2) (hn : 16*(4*m)≤2^62)
    (hp : 0<Fintype.card K/2^128) (hb : Fintype.card K/2^128<132*m+6)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=K) ((ReedSolomon.code dom k : Set (Fin (16*(4*m)) → K)) ^⋈ (Fin width))
      (1/(2:ℝ≥0∞)^128) ≤ (((33*m+1:ℕ):ℝ≥0)/(16*(4*m):ℕ)) := by
  have htol : 1/(2:ℝ≥0∞)^128<((132*m+6:ℕ):ℝ≥0∞)/(Fintype.card K : ℝ≥0∞) := by
    by_contra! h
    apply hb.not_ge
    exact (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h)
  apply mcaDeltaStar_le_of_bad
  apply htol.trans_le
  apply mass dom u g hu hg hd hk hupper (by omega) _ width
  rw [Nat.card_eq_fintype_card]
  have small : 132*m+6 ≤ 2^64 := by omega
  exact (Nat.choose_le_choose 2 small).trans (by rw [Nat.choose_two_right]; omega)

#print axioms mass
#print axioms operational_ceiling
end ArkLib.ProximityGap.Frontier.SmoothPlanarQuartetCoset
