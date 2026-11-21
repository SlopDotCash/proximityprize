/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # A noncollinear four-cubic attack at the second production prime -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimePlanarQuartet
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed (F N dom w)
open PrizeShapePrimeP30Second (P prime_P orderOf_g)
local instance : Fact P.Prime := ⟨prime_P⟩
private abbrev S : ℕ := 67108864

/-- First coordinates of the four cubic heads, in ascending power order. -/
def first : Fin 4 → Fin 4 → F := ![![0,
   0,
   0,
   0],
   ![49134505627721923606865019758615710315935050094,
   389457172438003823789244203726959512780796997161,
   292159140599725711705733192872566286745192867945,
   1],
   ![341293646227447635312598212631181997061127918039,
   0,
   243024634972003788098868173113950576429257817851,
   0],
   ![292159140599725711705733192872566286745192867945,
   389457172438003823789244203726959512780796997161,
   681616313037729535494977396599525799525989865107,
   1]]

/-- A second coordinate distinguishing all unequal values of the four planar heads. -/
def second : Fin 4 → Fin 4 → F := ![![0,
   0,
   0,
   0],
   ![49134505627721923606865019758615710315935050094,
   389457172438003823789244203726959512780796997161,
   292159140599725711705733192872566286745192867945,
   1],
   ![341293646227447635312598212631181997061127918040,
   684944486517762849622048856798491974355853664681,
   292159140599725711705733192872566286745192867945,
   1],
   ![341293646227447635312598212631181997061127918039,
   389457172438003823789244203726959512780796997160,
   681616313037729535494977396599525799525989865106,
   684944486517762849622048856798491974355853664682]]

private def val (A : Fin 4 → F) (t : F) : F := A 3*t^3 + A 2*t^2 + A 1*t^1 + A 0
private def f (A : Fin 4 → F) : F[X] :=
  C (A 3)*Polynomial.X^3 + C (A 2)*Polynomial.X^2 + C (A 1)*Polynomial.X^1 + C (A 0)
private def lift (A : Fin 4 → F) : F[X] := (f A).comp (Polynomial.X^S)

private theorem deg (A : Fin 4 → F) : (lift A).natDegree ≤ 3*S := by
  have h : (f A).natDegree ≤ 3 := by
    unfold f
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le ..)
          ((natDegree_C_mul_X_pow_le ..).trans (by decide))
      · exact (natDegree_C_mul_X_pow_le ..).trans (by decide)
    · simp only [natDegree_C, Nat.zero_le]
  exact natDegree_comp_le.trans (Nat.mul_le_mul h (natDegree_X_pow_le S))

private def own : Fin 16 → Fin 4 := ![0,0,0,1,0,0,1,1,2,2,2,3,2,0,0,1]
private def group : Fin 16 → Finset (Fin 4) :=
  ![{0,1},{0},{0,1},{1},{0,1},{0,2},{1,2},{1,3},{2,3},{2},{2,3},{3},{2,3},{0,2},{0,3},{1,3}]

private def V (i : Fin 4) (j : Fin 16) : F := val (second i) (w^j.val)
private def U (i : Fin 4) (j : Fin 16) : F := val (first i) (w^j.val)

private theorem agrees : ∀ j i, i∈group j →
    U i j=U (own j) j ∧ V i j=V (own j) j := by decide
private theorem misses : ∀ j i, i∉group j → V i j≠V (own j) j := by decide
private theorem determinant : ∀ r i j, i∉group r → j∉group r → i≠j →
    (U (own r) r-U i r)*(V j r-V (own r) r)≠(U (own r) r-U j r)*(V i r-V (own r) r) := by
  decide

private abbrev Grid := Σ _ : Fin 16, Fin S
private noncomputable def index : Grid ≃ Fin N :=
  (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans finProdFinEquiv)


private def cut (j : Fin 16) : ℕ :=
  if j=1 ∨ j=3 then 16777215 else if j=9 ∨ j=11 then 16777216 else 0
private theorem cut_le : ∀ j, cut j ≤ S := by decide

private noncomputable def lower (j : Fin 16) : Finset (Fin S) :=
  univ.filter (fun r => r.val < cut j)

private theorem card_lower (j : Fin 16) : (lower j).card = cut j := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le j)]

private abbrev Selection := Fin 16 → Bool → Bool

private noncomputable def row (take : Selection) (j : Fin 16) : Finset (Fin S) :=
  (if take j false then lower j else ∅) ∪ (if take j true then (lower j)ᶜ else ∅)

private noncomputable def selected (take : Selection) : Finset (Fin N) :=
  (univ.sigma (row take)).map index.toEmbedding

private theorem card_selected (take : Selection) :
    (selected take).card = ∑ j : Fin 16,
      ((if take j false then cut j else 0) + (if take j true then S - cut j else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro j _
  cases h1 : take j false <;> cases h2 : take j true <;>
    simp [row, h1, h2, card_lower, card_compl, Nat.add_sub_of_le (cut_le j)]

private theorem mem_selected (take : Selection) (u : Grid) :
    index u ∈ selected take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) := by
  classical
  change index.toEmbedding u ∈ (univ.sigma (row take)).map index.toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]


private def rootSel : Selection := fun _ high => !high
private def coreSel (i : Fin 4) : Selection := fun r high => !high || decide (i∈group r)
private def roots := selected rootSel
private def core (i : Fin 4) := selected (coreSel i)
private def owner (x : Fin N) : Fin 4 := own (index.symm x).1

private theorem root_count : roots.card=67108862 := by
  rw [roots,card_selected]; decide
private theorem core_count (j : Fin 4) : (core j).card=(![520093695,520093695,520093694,520093694] : Fin 4 → ℕ) j := by
  rw [core,card_selected]; fin_cases j <;> decide

private theorem power (u : Grid) : (dom (index u)) ^ S = w ^ u.1.val := by
  change (PrizeShapePrimeP30Second.g ^ (u.1.val + 16*u.2.val)) ^ S=_
  have hg : PrizeShapePrimeP30Second.g ^ N=1 := by
    simpa only [orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30Second.g
  have hr : (PrizeShapePrimeP30Second.g ^ (16*u.2.val)) ^ S=1 := by
    have h : 16*u.2.val*S=N*u.2.val := by change 16*u.2.val*67108864=(16*67108864)*u.2.val; ac_rfl
    rw [← pow_mul,h,pow_mul,hg,one_pow]
  have hw : PrizeShapePrimeP30Second.g ^ S=w := by
    rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]; decide
  rw [pow_add,mul_pow,hr,mul_one,← pow_mul,Nat.mul_comm,pow_mul,hw]

private theorem lifted (A : Fin 4 → F) (u : Grid) :
    (lift A).eval (dom (index u))=val A (w^u.1.val) := by
  rw [lift,eval_comp,eval_pow,eval_X,power]
  simp [f,val]

private def sel (u : Grid) := decide (cut u.1 ≤ u.2.val)
private theorem origin (u : Grid) : index u∈roots ↔ sel u=false := by
  rw [roots,mem_selected]; simp [rootSel,sel]
private theorem inside (u : Grid) (i : Fin 4) : index u∈core i ↔ sel u=false ∨ i∈group u.1 := by
  rw [core,mem_selected]; simp [coreSel,sel]
private theorem owner_at (u : Grid) : owner (index u)=own u.1 := by simp [owner]

/-- Simultaneous bad labels on one received stack. This extends from the quarter-rate
dimension through the smallest defining core at every positive interleaving width. -/
theorem label_mass {k : ℕ} (hk : 268435456 ≤ k) (hc : k ≤ 520093694) (width : ℕ) [NeZero width] :
    (2214592518:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (553648129/1073741824) := by
  have counts : (∑ i, (core i)ᶜ.card)=2214592518 := by
    simp only [card_compl,core_count,Fintype.card_fin,Fin.sum_univ_succ]
    decide
  have count_min (i : Fin 4) : 520093694 ≤ (core i).card := by rw [core_count]; fin_cases i <;> decide
  rw [epsMCA_interleaved_eq]
  have hm := PlanarQuartetMass.mass dom k (3*S) (553648129/1073741824)
    (fun i => lift (first i)) (fun i => lift (second i)) roots owner core
    (by rw [root_count]; dsimp [S]; omega) (fun _ => deg _) (fun _ => deg _)
    (by
      intro i x hx
      let u := index.symm x
      have he : x=index u := (index.apply_symm_apply x).symm
      rw [he,origin] at hx
      rw [he,inside]; exact Or.inl hx)
    (by
      intro i x hx hr
      obtain ⟨u,rfl⟩ := index.surjective x
      rw [inside] at hx
      rw [origin] at hr
      obtain h := agrees u.1 i (hx.resolve_left hr)
      simpa only [lifted,owner_at,U,V] using h)
    (by
      intro i x hx
      obtain ⟨u,rfl⟩ := index.surjective x
      rw [inside] at hx
      simpa only [lifted,owner_at,V] using misses u.1 i (fun h => hx (Or.inr h)))
    (by
      intro x i j hi hj hne
      obtain ⟨u,rfl⟩ := index.surjective x
      rw [inside] at hi hj
      simpa only [lifted,owner_at,U,V] using determinant u.1 i j (fun h => hi (Or.inr h))
        (fun h => hj (Or.inr h)) hne)
    (fun i => hc.trans (count_min i)) (by
      intro i
      rw [Fintype.card_fin]
      apply le_trans (b:=((520093694+1:ℕ):ℝ≥0))
      · rw [tsub_mul,one_mul]; norm_num [N,tsub_le_iff_right]
      · exact_mod_cast Nat.add_le_add_right (count_min i) 1)
    (by rw [counts,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide)
  rw [counts,ZMod.card] at hm
  simpa only [Nat.cast_ofNat] using hm

/-- Strict failure at 553,648,129 errors and the resulting operational upper bound. -/
theorem quarter (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 268435456 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    tol < epsMCA (F:=F) code (553648129/1073741824) ∧
      mcaDeltaStar (F:=F) code tol ≤ 553648129/1073741824 := by
  dsimp only
  have hb : 1/(2:ℝ≥0∞)^128 < (2214592518:ℝ≥0∞)/(P:ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : ((2214592518:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
    exact (by decide : ¬ 2214592518 ≤ P/2^128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad,mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms label_mass
#print axioms quarter
end ArkLib.ProximityGap.Frontier.SecondPrimePlanarQuartet
