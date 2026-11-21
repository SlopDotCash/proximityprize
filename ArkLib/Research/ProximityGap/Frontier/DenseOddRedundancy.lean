/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.OddSmoothPrimeThreshold
import ArkLib.Research.ProximityGap.Frontier.FullFiberMcaLift
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import Mathlib.Combinatorics.Pigeonhole

/-! # Translated pairs attain the odd-redundancy endpoint on dense arbitrary domains

A fixed coordinate sum partitions the participating sites into pairs. Their
products are the values of a quadratic polynomial and distinguish all pairs.
The square-fiber construction on this subdomain survives locator extension.
-/
set_option autoImplicit false
namespace ProximityGap.DenseOddRedundancy
open Polynomial Finset MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Ordered pairs of distinct sites whose images have sum c. -/
def pairs {n : ℕ} (x : Fin n ↪ F) (c : F) :=
  (univ : Finset (Fin n)).offDiag.filter fun w => x w.1+x w.2=c

omit [Fintype F] [DecidableEq F] in
private theorem sum_product {n : ℕ} (x : Fin n ↪ F) {a b i j : Fin n}
    (hs : x a+x b=x i+x j) (hp : x a*x b=x i*x j) :
    (a=i ∧ b=j) ∨ (a=j ∧ b=i) := by
  have eq : (x a-x i)*(x a-x j)=0 := by linear_combination x a*hs-hp
  rcases mul_eq_zero.mp eq with left|right
  · have ai := x.injective (sub_eq_zero.mp left)
    subst i
    exact Or.inl ⟨rfl,x.injective (by linear_combination hs)⟩
  · have aj := x.injective (sub_eq_zero.mp right)
    subst j
    exact Or.inr ⟨rfl,x.injective (by linear_combination hs)⟩

/-- A single coordinate sum with more than h disjoint pairs supplies the h+1
bad scalars, even if every remaining site must be added by locator extension. -/
theorem paired_lower {n k h : ℕ} [NeZero n] (x : Fin n ↪ F) (c : F)
    (length : n=k+2*h-1) (large : 3 ≤ h) (odd : h%2=1) (many : 2*h < (pairs x c).card) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  let H := pairs x c
  let f (w : Fin n × Fin n) := x w.1*x w.2
  let V := H.image f
  let E := Function.Embedding.subtype (·∈V)
  let π (w : H) : V := ⟨f w.val,mem_image_of_mem f w.property⟩
  have total (w : H) : x w.val.1+x w.val.2=c := (mem_filter.mp w.property).2
  have different (w : H) : w.val.1 ≠ w.val.2 := (mem_offDiag.mp (mem_filter.mp w.property).1).2.2
  let swap (w : H) : H := ⟨(w.val.2,w.val.1),mem_filter.mpr
    ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,(different w).symm⟩,(add_comm ..).trans (total w)⟩⟩
  have fibers (y : V) : (univ.filter (fun w : H => π w=y)).card=2 := by
    obtain ⟨w,hw,hwy⟩ := mem_image.mp y.property
    let a : H := ⟨w,hw⟩
    have pa : π a=y := Subtype.ext hwy
    have pb : π (swap a)=y := Subtype.ext ((mul_comm ..).trans hwy)
    have neq : a ≠ swap a := fun eq => different a (congrArg (fun r : H => r.val.1) eq)
    have split : univ.filter (fun w : H => π w=y) = {a,swap a} := by
      ext z
      simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro atY
        have equal := congrArg Subtype.val (atY.trans pa.symm)
        rcases sum_product x ((total z).trans (total a).symm) equal with eq|eq
        · exact Or.inl (Subtype.ext (Prod.ext eq.1 eq.2))
        · exact Or.inr (Subtype.ext (Prod.ext eq.1 eq.2))
      · rintro (rfl|rfl) <;> assumption
    rw [split,card_insert_of_notMem (by simpa using neq),card_singleton]
  have cardSum := card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=π) (fun _ _ => mem_univ _)
  simp only [fibers,sum_const,card_univ,smul_eq_mul] at cardSum
  let m := Fintype.card V
  let N := Fintype.card H
  have hn : N=2*m := by dsimp [N,m];omega
  have threshold : 2*h<N := by simpa only [N,Fintype.card_coe,H] using many
  let : Nonempty V := Fintype.card_pos_iff.mp (by change 0 < m;omega)
  let : Nonempty H := Fintype.card_pos_iff.mp (by change 0 < N;omega)
  let : NeZero N := ⟨by omega⟩
  let old : H ↪ Fin n := ⟨fun w => w.val.1,by
    intro r s eq
    apply Subtype.ext
    apply Prod.ext eq
    apply x.injective
    have h := (total r).trans (total s).symm
    rw [show r.val.1=s.val.1 from eq] at h
    exact add_left_cancel h⟩
  let equiv := (Fintype.equivFin H).symm
  let site : Fin N ↪ Fin n := equiv.toEmbedding.trans old
  let e := (h-1)/2
  let b := m-h+1
  let K := 2*b-1
  have hbase := TwoHeadLinearBudget.errors (k:=b) (e:=e) E
    (by change 2*(e+1) ≤ m;dsimp [e];omega)
    (by change m ≤ b+2*e;dsimp [b,e];omega)
    (by change b+e+1 ≤ m;dsimp [b,e];omega)
  let P : F[X] := -(Polynomial.X*(Polynomial.X-Polynomial.C c))
  have hP : P.natDegree=2 := by
    simp [P,natDegree_mul X_ne_zero (X_sub_C_ne_zero _)]
  have lifted := FullFiberMcaLift.epsMCA_le_band (k:=b) (m:=2) (K:=K) (old.trans x) E π P
    (by decide) (by dsimp [b];omega) (by dsimp [K,b]; omega) (by dsimp [K];omega) hP (by
      intro w
      change (-(Polynomial.X*(Polynomial.X-Polynomial.C c)):F[X]).eval (x w.val.1)=x w.val.1*x w.val.2
      simp only [eval_neg,eval_mul,eval_X,eval_sub,eval_C]
      linear_combination -(x w.val.1)*(total w)) fibers ((e:ℝ≥0)/(Fintype.card V))
  have rad : ((h-1:ℕ):ℝ≥0)/N=(e:ℝ≥0)/(Fintype.card V) := by
    rw [show h-1=2*e by dsimp [e];omega,hn,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_div_mul_left _ _ (by norm_num : (2:ℝ≥0) ≠ 0)
  have transfer := LocatorShortening.eps_le_extension (k:=K) site x (by dsimp [K,b];omega) (h-1)
  have sites := Fintype.card_le_of_embedding site
  simp only [Fintype.card_fin] at sites
  have degree : K+(n-N)=k := by dsimp [K,b];omega
  rw [degree] at transfer
  rw [show h+1=2*(e+1) by dsimp [e];omega]
  refine hbase.trans (lifted.trans ?_)
  rw [←rad,MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq equiv (site.trans x) (old.trans x) (fun _ => rfl)]
  exact transfer

/-- Pair-sum averaging works on every prescribed evaluation domain in a finite
field once the number of ordered distinct-site pairs exceeds 2h times field size. -/
theorem dense_lower {n k h : ℕ} [NeZero n] (x : Fin n ↪ F) (length : n=k+2*h-1)
    (large : 3 ≤ h) (odd : h%2=1) (density : Fintype.card F*(2*h)<n*n-n) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  obtain ⟨c,_,many⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s:=(univ : Finset (Fin n)).offDiag) (t:=(univ : Finset F))
    (f:=fun w => x w.1+x w.2) (fun _ _ => mem_univ _) (n:=2*h)
    (by simpa only [offDiag_card,card_univ,Fintype.card_fin] using density)
  exact paired_lower x c length large odd many

/-- The previously exceptional integer budget is resolved over every prescribed
domain satisfying the pair density test. -/
theorem exceptional {n k h Q : ℕ} [NeZero n] (x : Fin n ↪ F) (hk : 3 ≤ k) (rate : 3*k ≤ n)
    (length : n=k+2*h-1) (large : 4 ≤ h) (odd : h%2=1)
    (density : Fintype.card F*(2*h)<n*n-n) (security : 0 < Q)
    (budget : Fintype.card F/Q=h) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let r := ((h-1:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r :=
  OddRedundancyApolar.exceptional_of_lower x hk rate length large security budget
    (dense_lower x length (by omega) odd density) width

/-- The full prime-field odd-redundancy curve on arbitrary domains. The density
test is needed only at the single potentially exceptional budget. -/
theorem classification {p n k h B Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (large : 65536 ≤ n) (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1)
    (two : 2 ≤ Q) (budget : p/Q=B) (ceiling : B/2+DoubleQuadraticThreshold.agreements n k ≤ n+1)
    (density : B=h → h%2=1 → p*(2*h)<n*n-n) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let r := ((OddSmoothPrimeThreshold.index B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  by_cases ex : B=h ∧ h%2=1
  · rw [OddSmoothPrimeThreshold.index,ite_eq_left ex]
    exact exceptional x hk rate length (by omega) ex.2 (by simpa using density ex.1 ex.2)
      (by omega) (by simpa using budget.trans ex.1) width
  rw [OddSmoothPrimeThreshold.index,ite_eq_right ex]
  by_cases low : B ≤ 2*h+1
  · rw [show ThreeRegimePrimeThreshold.index B h=min B h by unfold ThreeRegimePrimeThreshold.index;omega]
    exact OddRedundancyApolar.classification x hk rate length (by omega) (by omega) (by simpa using budget)
      low (by omega) width
  · rw [show ThreeRegimePrimeThreshold.index B h=B/2 by unfold ThreeRegimePrimeThreshold.index;omega]
    have m := DoubleQuadraticThreshold.margin_le_five n k
    have cap := ceiling
    unfold DoubleQuadraticThreshold.agreements at cap
    exact DoubleQuadraticThreshold.prime_classification x two (by rw [budget]) (by omega) rate large
      (by omega) (by omega) (by omega) width

section Fermat
local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Every 54,001-site evaluation domain in the Fermat field has first failure
21,844 at tolerance one third. The length does not divide the multiplicative group order. -/
theorem fermat_threshold (x : Fin 54001 ↪ ZMod 65537) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x 10312 : Set (Fin 54001 → ZMod 65537)) ^⋈ (Fin width)
    let r := (21844:ℝ≥0)/54001
    mcaDeltaStar (F:=ZMod 65537) C (1/3)=r ∧ ∀ δ, epsMCA (F:=ZMod 65537) C δ ≤ 1/3 ↔ δ<r := by
  have result := exceptional (h:=21845) (Q:=3) x (by decide : 3 ≤ 10312) (by decide)
    (by decide) (by decide) (by decide) (by rw [ZMod.card];decide) (by decide)
    (by rw [ZMod.card]) width
  simpa only [show (21845:ℕ)-1=21844 by decide,Nat.cast_ofNat] using result
end Fermat

end ProximityGap.DenseOddRedundancy
#print axioms ProximityGap.DenseOddRedundancy.paired_lower
#print axioms ProximityGap.DenseOddRedundancy.dense_lower
#print axioms ProximityGap.DenseOddRedundancy.exceptional
#print axioms ProximityGap.DenseOddRedundancy.classification
#print axioms ProximityGap.DenseOddRedundancy.fermat_threshold
