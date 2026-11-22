/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondOrderOriginBlocks
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Finite all-domain prime-field MCA bounds at derivative order two

At half rate the closed length-1024 radius is 324/1024. At length 262144
the strongest row reaches 81984 errors. All three rows clear the 128-bit
budget in every prime field above their stated integer floor.
-/
namespace ProximityGap.SecondOrderPrimeFieldCuts
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential Polynomial Finset
open PartitionOriginCertificate SecondOrderOriginBlocks SecondOrderBlockCounts
open scoped NNReal ENNReal

structure Case where
  n : ℕ
  k : ℕ
  A : ℕ
  m : ℕ
  W : ℕ
  v : ℕ
  H : ℕ
  r : ℕ
  N : ℕ
  fieldFloor : ℕ
  deriving DecidableEq

/-- Exact integer parameters and sufficient prime-field sizes. -/
def cases : Fin 3 → Case
  | 0 => ⟨1024,512,700,112,49,153,287261,2732779,2799856150,
    1226823212894241196195823231457719392856637757449779112842104633314⟩
  | 1 => ⟨262144,131072,180224,54,23,74,25988,156586,41164959316,
    95659773389936704056690147950743995352934741041316019523897604230814834⟩
  | 2 => ⟨262144,131072,180160,58,25,79,25467,209400,55063229494,
    122239999054400338719359108276973937911241042922169913105319470914634302⟩

/-- Balanced replay of an interval sum, with recursion depth bounded by the last argument. -/
def balanced (f : ℕ → ℕ) (start n : ℕ) : ℕ → ℕ
  | 0 => if n=0 then 0 else f start
  | d+1 => if n=0 then 0 else balanced f start (n/2) d + balanced f (start+n/2) (n-n/2) d

private theorem balanced_eq (f : ℕ → ℕ) (d start n : ℕ) (h : n ≤ 2^d) :
    balanced f start n d = ∑ i ∈ range n, f (start+i) := by
  induction d generalizing start n with
  | zero =>
    norm_num at h
    interval_cases n <;> simp [balanced]
  | succ d ih =>
    by_cases hn : n=0
    · simp [hn,balanced]
    · rw [balanced,ite_eq_right hn,ih,ih]
      · conv_rhs => rw [← Nat.add_sub_of_le (Nat.div_le_self n 2),Finset.sum_range_add]
        simp only [Nat.add_assoc]
      · rw [pow_succ] at h; omega
      · rw [pow_succ] at h; omega

/-- The two-dimensional block budget evaluated on balanced interval sums. -/
def blockSum (m W v : ℕ) :=
  balanced (fun t => balanced (fun z =>
    min (countBelow t (W+m-(z+t)) - countBelow t (W-(z+t)))
      (countBelow t (W+1) - countBelow t (W-z))) 0 (W+m) 8) 0 (v+1) 8

theorem blockSum_eq {m W v : ℕ} (hz : W+m ≤ 2^8) (ht : v+1 ≤ 2^8) :
    blockSum m W v = blockBudget m W v := by
  simp only [blockSum,blockBudget,balanced_eq _ 8 _ _ ht,balanced_eq _ 8 _ _ hz,Nat.zero_add]

theorem sourceBudget_eq {D L W v : ℕ} (hv : v+1 ≤ 2^8) :
    sourceBudget D L W v = balanced (fun t => countBelow t (W+1) * (L-D*t)) 0 (v+1) 8 := by
  simp [sourceBudget,balanced_eq _ 8 _ _ hv]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
/-- Kernel evaluations of all three source and rank sums. -/
theorem counts (i : Fin 3) : let c := cases i
    blockBudget c.m c.W c.v = c.r ∧ sourceBudget (c.k-1) (c.m*c.A) c.W c.v = c.N := by
  dsimp only
  rw [←blockSum_eq (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    sourceBudget_eq (by fin_cases i <;> decide)]
  fin_cases i <;> decide

noncomputable def gap (c : Case) : ℝ := ((c.A-c.k:ℕ) : ℝ)/c.n
def scalarCap (c : Case) := c.fieldFloor/2^128

private theorem charge (i : Fin 3) : let c := cases i
    polynomialCurveProductAgreementConstant (gap c) c.v c.H 2 * (c.n:ℝ)^3 < (scalarCap c:ℝ)+1 := by
  fin_cases i <;> norm_num [cases,gap,polynomialCurveProductAgreementConstant,scalarCap]

open Classical in
/-- Full correlated-pair recovery over any field satisfying the degree guard. -/
theorem exact_recovery {F : Type} [Field F] (i : Fin 3)
    (dom : Fin (cases i).n ↪ F) (u w : Fin (cases i).n → F)
    (hchar : ringChar F = 0 ∨ max ((cases i).k-1) (cases i).v < ringChar F) :
    ∃ E : Finset F, E.card ≤ scalarCap (cases i) ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < (cases i).k →
      (cases i).A ≤ (polynomialAgreementSet dom (fun x => u x+z*w x) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) (cases i).k z P := by
  let c := cases i
  have hD : 0 < c.k-1 := by fin_cases i <;> decide
  have hcut : c.m*c.A ≤ (c.k-1)*(c.v+1) := by fin_cases i <;> decide
  have hv := jet_cap (W := c.W) hcut
  have lower := source_card_lower (L := c.m*c.A) (W := c.W) (v := c.v) hD
  have hr := origin_rank (F := F) (m := c.m) hD hv
  rw [(counts i).1] at hr
  rw [(counts i).2] at lower
  have surplus : c.n*c.r < c.N := by fin_cases i <;> decide
  have ht : c.n*c.r*c.v / (c.N-c.n*c.r) ≤ c.H := by fin_cases i <;> decide
  have hH := (Nat.div_le_div_left (Nat.sub_le_sub_right lower (c.n*c.r))
    (show 0 < c.N-c.n*c.r by omega)).trans ht
  obtain ⟨E,he,good⟩ := exact_line_of_origin_rank hD le_rfl
    (show c.k ≤ c.k-1+1 by omega) hv hr (surplus.trans_le lower) hH
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (show 0<gap c by fin_cases i <;> norm_num [c,gap,cases])
    (show (c.k:ℝ)+gap c*c.n≤c.A by fin_cases i <;> norm_num [c,gap,cases]) hchar dom u w
  refine ⟨E,?_,good⟩
  have hlt := he.trans_lt (charge i)
  exact Nat.le_of_lt_succ (by exact_mod_cast hlt)

open Classical in
/-- An integer exact-agreement bound gives the literal sponsor error at every
radius whose real agreement threshold is at least the integer cutoff. -/
theorem eps_of_exact {F : Type} [Field F] [Fintype F] {n k A cap : ℕ} [Nonempty (Fin n)]
    (dom : Fin n ↪ F) (δ : ℝ≥0) (ha : (A : ℝ≥0) ≤ (1-δ)*n)
    (recover : ∀ u w : Fin n → F, ∃ E : Finset F, E.card ≤ cap ∧ ∀ z ∉ E,
      ∀ P : F[X], P.degree < k → A ≤ (polynomialAgreementSet dom (fun x => u x+z*w x) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) k z P) :
    epsMCA (F := F) (A := F) (code dom k : Set (Fin n → F)) δ ≤ (cap : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  classical
  apply epsMCA_le_of_badCount_le
  intro words
  obtain ⟨E,hE,good⟩ := recover (words 0) (words 1)
  apply (card_le_card ?_).trans hE
  intro z hz
  by_contra hbad
  obtain ⟨S,hsize,⟨w,hw,fit⟩,no⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hP,hPw⟩ := mem_code_iff_eval.mp hw
  have hs : S ⊆ polynomialAgreementSet dom (fun x => words 0 x+z*words 1 x) P :=
    fun x hx => mem_filter.mpr ⟨mem_univ _,(hPw x).trans (fit x hx)⟩
  have htag' : (A : ℝ≥0) ≤ (S.card : ℝ≥0) := ha.trans (by simpa using hsize)
  have htag : A ≤ S.card := by exact_mod_cast htag'
  obtain ⟨pair,ha,hb,_,hh⟩ := good z hbad P hP (htag.trans (card_le_card hs))
  apply no
  refine ⟨evalOnPoints dom pair.1,mem_code_iff_eval.mpr ⟨_,ha,fun _ => rfl⟩,
    evalOnPoints dom pair.2,mem_code_iff_eval.mpr ⟨_,hb,fun _ => rfl⟩,?_⟩
  intro x hx
  have hx' : x ∈ commonPolynomialAgreementSet dom (words 0) (words 1) pair.1 pair.2 := by
    rw [← hh]
    exact hs hx
  exact (mem_filter.mp hx').2

/-- Literal sponsor MCA at the closed integer-error radius, with every
received pair and every prime-field domain quantified. -/
theorem eps_bound {p : ℕ} [Fact p.Prime] (i : Fin 3) (hp : (cases i).fieldFloor ≤ p)
    (dom : Fin (cases i).n ↪ ZMod p) :
    epsMCA (F := ZMod p) (A := ZMod p) (code dom (cases i).k : Set (Fin (cases i).n → ZMod p))
      ((((cases i).n-(cases i).A:ℕ):ℝ≥0)/(cases i).n) ≤ 1/((2^128:ℕ):ℝ≥0∞) := by
  classical
  let c := cases i
  let δ : ℝ≥0 := ((c.n-c.A:ℕ):ℝ≥0)/c.n
  have hchar : max (c.k-1) c.v < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]
    calc _ < c.fieldFloor := by fin_cases i <;> decide
         _ ≤ _ := hp
  letI : Nonempty (Fin (cases i).n) := ⟨⟨0,by fin_cases i <;> decide⟩⟩
  have hδ1 : δ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    fin_cases i <;> norm_num [c,δ,cases]
  have hδ : (c.A : ℝ≥0) ≤ (1-δ)*c.n := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_sub hδ1]
    fin_cases i <;> norm_num [c,δ,cases]
  apply (eps_of_exact dom δ hδ (fun u w => exact_recovery i dom u w (Or.inr hchar))).trans
  · rw [ZMod.card]
    exact (BoundarySecurityBudget.count_ratio_le_iff (Fact.out : p.Prime).pos (by decide)).mpr
      (Nat.div_le_div_right hp)

end ProximityGap.SecondOrderPrimeFieldCuts
#print axioms ProximityGap.SecondOrderPrimeFieldCuts.eps_bound
