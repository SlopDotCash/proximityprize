/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMca
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Four arbitrary-domain MCA guarantees strictly beyond Johnson

Explicit first-order symbolic certificates and the canonical squarefree
retained-line theorem bound the literal sponsor MCA error on every length-1024
domain in the 237-bit spectral-witness field.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.ExplicitFirstOrderCutBudgets
open Finset ReedSolomon.HiddenDerivative

/-- Parameters of a first-order interpolation at length 1024. -/
structure Case where
  d : ℕ
  t : ℕ
  m : ℕ
  j : ℕ
  b : ℕ
  h : ℕ
  deriving DecidableEq, Repr

def cases : Fin 4 → Case
  | 0 => ⟨511,706,565,175,780,2167787⟩
  | 1 => ⟨255,479,1328,606,2496,10041169⟩
  | 2 => ⟨127,326,273,151,701,436279⟩
  | 3 => ⟨63,222,232,154,819,398583⟩

/-- Floors of the canonical finite-length MCA envelopes. -/
def scalarCap : Fin 4 → ℕ
  | 0 => 26788941909929469439
  | 1 => 687905649896919903388
  | 2 => 790768777796617278
  | 3 => 397398880011593585

private def triangle (a : ℕ) := a*(a+1)

private theorem triangle_step (a b : ℕ) :
    2*(a-b)+triangle (a-1-b) = triangle (a-b) := by
  by_cases h : b<a
  · obtain ⟨k,hk⟩ : ∃ k, a-b=k+1 := ⟨a-b-1,by omega⟩
    rw [show a-1-b=k by omega,hk]
    unfold triangle
    ring
  · simp [show a-b=0 by omega,show a-1-b=0 by omega]

private theorem triangle_sum (a b c : ℕ) :
    2*(∑ q∈range (c+1), (a+q-b)) + triangle (a-1-b) = triangle (a+c-b) := by
  induction c with
  | zero => simpa using triangle_step a b
  | succ c ih =>
    rw [sum_range_succ,Nat.mul_add]
    have hs := triangle_step (a+(c+1)) b
    rw [show a+(c+1)-1-b=a+c-b by omega] at hs
    omega

private def dimension (D A m M B : ℕ) :=
  ∑ q∈range (B+1),
    (triangle (m*A+min q M-D*q)-triangle (m*A-1-D*q))/2

private theorem dimension_eq (D A m M B : ℕ) : firstOrderDimensionCount D A m M B =
    dimension D A m M B := by
  apply sum_congr rfl
  intro q _
  have hs := triangle_sum (m*A) (D*q) (min q M)
  omega

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
private theorem counts (i : Fin 4) : let c := cases i
    1024 * firstOrderRankCount c.m c.j < firstOrderDimensionCount c.d c.t c.m c.j c.b ∧
    1024 * firstOrderRankCount c.m c.j * c.b /
       (firstOrderDimensionCount c.d c.t c.m c.j c.b - 1024 * firstOrderRankCount c.m c.j) ≤ c.h := by
  simp only [dimension_eq]
  fin_cases i <;> decide

/-- At all four finite points, every pair admits the indicated first-order
symbolic certificate on every prescribed domain. -/
theorem certificates {F : Type} [Field F] (dom : Fin 1024 ↪ F) (u v : Fin 1024 → F)
    (i : Fin 4) : let c := cases i
    Nonempty (FirstOrderSymbolicCertificate.{0,0} (F:=F) c.d c.t c.m c.j c.b (c.d+1) c.h dom u v
      (firstOrderColumns (D:=c.d) (A:=c.t) (m:=c.m) (M:=c.j) (μ:=c.b))) := by
  dsimp only
  have hd : 0 < (cases i).d := by fin_cases i <;> decide
  apply exists_firstOrder_symbolicCertificate_of_rank_and_height le_rfl
  · rw [card_firstOrderExponents hd]
    exact (counts i).1
  · rw [card_firstOrderExponents hd]
    exact (counts i).2

open ReedSolomon ReedSolomon.FirstOrder
open scoped NNReal ENNReal
open Polynomial

private theorem envelope_lt (i : Fin 4) : let c := cases i
    finiteLengthMcaEnvelope (agreementIncidenceRatio 1024 c.d c.t) 1024 c.d c.b c.j c.h <
      (scalarCap i : ℝ)+1 := by
  fin_cases i <;> norm_num [finiteLengthMcaEnvelope,agreementIncidenceRatio,cases,scalarCap]

/-- The bad-scalar count at the indicated agreement threshold is bounded
without a restriction on the geometry of the sites or the received words. -/
theorem exact_recovery {F : Type} [Field F] [DecidableEq F] (dom : Fin 1024 ↪ F)
    (u v : Fin 1024 → F) (i : Fin 4)
    (hchar : ringChar F=0 ∨ max (cases i).d (cases i).j < ringChar F) :
    ∃ E : Finset F, E.card ≤ scalarCap i ∧ ∀ z∉E, ∀ P : F[X], P.degree < (cases i).d+1 →
      (cases i).t ≤ (polynomialAgreementSet dom (fun x => u x+z*v x) P).card →
      HasExactCorrelatedPair dom u v (RingHom.id F) ((cases i).d+1) z P := by
  let c := cases i
  obtain ⟨cert⟩ := certificates dom u v i
  have hc : 2 ≤ c.d+1 ∧ c.d+1 ≤ c.t ∧ c.t ≤ 1024 ∧ 1 ≤ c.j ∧ c.j ≤ c.b := by
    fin_cases i <;> decide
  obtain ⟨E,hn,good⟩ := Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
    dom u v _ cert hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 (by simpa using hchar)
  rw [Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope] at hn
  have hlt := (show (E.card:ℝ) < (scalarCap i : ℝ)+1 from
    hn.trans_lt (by simpa using envelope_lt i))
  exact ⟨E,Nat.le_of_lt_succ (by exact_mod_cast hlt),good⟩

/-- Literal worst-pair sponsor MCA error at the four thresholds, for every
field large enough for first-order recovery. -/
theorem eps_bound {F : Type} [Field F] [Fintype F] [DecidableEq F] (dom : Fin 1024 ↪ F)
    (i : Fin 4) (δ : ℝ≥0) (ht : ((cases i).t : ℝ≥0) ≤ (1-δ)*1024)
    (hchar : ringChar F=0 ∨ max (cases i).d (cases i).j < ringChar F) :
    _root_.ProximityGap.epsMCA (F:=F) (code dom ((cases i).d+1) : Set (Fin 1024 → F)) δ ≤
      (scalarCap i : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  classical
  apply _root_.ProximityGap.epsMCA_le_of_badCount_le
  intro u
  obtain ⟨E,hE,good⟩ := exact_recovery dom (u 0) (u 1) i hchar
  apply (card_le_card ?_).trans hE
  intro z hz
  by_contra he
  obtain ⟨S,hsize,⟨w,hw,fit⟩,bad⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hP,hPw⟩ := mem_code_iff_eval.mp hw
  have sub : S ⊆ polynomialAgreementSet dom (fun x => u 0 x+z*u 1 x) P := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(hPw x).trans (fit x hx)⟩
  have htag' : ((cases i).t : ℝ≥0) ≤ (S.card : ℝ≥0) := ht.trans (by simpa using hsize)
  have htag : (cases i).t ≤ S.card := by exact_mod_cast htag'
  obtain ⟨pair,ha,hb,_,hh⟩ := good z he P hP (htag.trans (card_le_card sub))
  apply bad
  refine ⟨evalOnPoints dom pair.1,mem_code_iff_eval.mpr ⟨_,ha,fun _ => rfl⟩,
    evalOnPoints dom pair.2,mem_code_iff_eval.mpr ⟨_,hb,fun _ => rfl⟩,?_⟩
  intro x hx
  have hx' : x ∈ commonPolynomialAgreementSet dom (u 0) (u 1) pair.1 pair.2 := by
    rw [← hh]
    exact sub hx
  exact (mem_filter.mp hx').2

local instance : Fact DyadicLogWitness237.P.Prime := ⟨DyadicLogWitness237.prime⟩

/-- Through 318, 545, 698, and 802 errors at the four respective sponsor
rates, every 1024-site domain in the spectral-witness field is 128-bit safe. -/
theorem spectral_field_eps (dom : Fin 1024 ↪ ZMod DyadicLogWitness237.P) (i : Fin 4) :
    let c := cases i
    c.t^2 < 1024*c.d ∧ _root_.ProximityGap.epsMCA (F:=ZMod DyadicLogWitness237.P)
      (code dom (c.d+1) : Set (Fin 1024 → ZMod DyadicLogWitness237.P))
      (((1024-c.t : ℕ):ℝ≥0)/1024) ≤ 1/((2^128 : ℕ):ℝ≥0∞) := by
  refine ⟨by fin_cases i <;> decide,?_⟩
  apply (eps_bound dom i _ ?_ (Or.inr ?_)).trans
  · rw [ZMod.card]
    apply (_root_.ProximityGap.BoundarySecurityBudget.count_ratio_le_iff (by decide) (by decide)).mpr
    fin_cases i <;> decide
  · have hd : (((1024-(cases i).t : ℕ):ℝ≥0)/1024) ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : 0 < (1024:ℝ≥0))).mpr
      rw [one_mul]
      exact_mod_cast Nat.sub_le 1024 (cases i).t
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_sub hd,NNReal.coe_div]
    fin_cases i <;> norm_num [cases]
  · rw [ZMod.ringChar_zmod_n]
    fin_cases i <;> decide

#print axioms certificates
#print axioms exact_recovery
#print axioms eps_bound
#print axioms spectral_field_eps
end ArkLib.ProximityGap.Frontier.ExplicitFirstOrderCutBudgets
