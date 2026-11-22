/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237
import ArkLib.Research.ProximityGap.Frontier.FourRateListPrime246
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup

/-! # Field budgets for the general-order product exception estimate

At slack at most `1/s`, the canonical product estimate has a sharp integer
lower bound attained at `1/s`. This determines whether any such slack can
meet a specified finite budget, for arbitrary multiplicity profiles producing
the chosen derivative order, jet degree and challenge height.
-/
namespace ProximityGap.HigherOrderFieldBudget
open ReedSolomon

/-- Canonical product-estimate coefficient at capacity slack `1/s`. -/
def coefficient (s v h d : ℕ) : ℕ :=
  h+(2*s)^d*v^(d+2)*(s*h*(d+1)*(3*d+5)+3)

theorem coefficient_reciprocal {s : ℕ} (hs : 0<s) (v h d : ℕ) :
    polynomialCurveProductAgreementConstant (1/(s:ℝ)) v h d = coefficient s v h d := by
  have ps : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  unfold polynomialCurveProductAgreementConstant coefficient
  push_cast
  rw [one_div_div,div_one,div_div_eq_mul_div,div_one,mul_pow]
  ring

/-- A smaller capacity slack can only raise the prescribed field budget. -/
theorem coefficient_floor {s v h d : ℕ} (hs : 0<s) {g : ℝ} (hg : 0<g)
    (hm : g≤1/(s:ℝ)) : (coefficient s v h d:ℝ) ≤ polynomialCurveProductAgreementConstant g v h d := by
  rw [←coefficient_reciprocal hs]
  unfold polynomialCurveProductAgreementConstant
  have rn : (0:ℝ)<1/s := by positivity
  have hi : 1/(1/(s:ℝ)) ≤ 1/g := one_div_le_one_div_of_le hg hm
  gcongr

/-- Exact finite arithmetic test for some slack through `1/s` to fit the
canonical exception estimate. The test concerns this estimate itself. -/
theorem budget_iff (Q n p v h d : ℕ) {s : ℕ} (hs : 0<s) :
    (∃ g : ℝ, 0<g ∧ g≤1/(s:ℝ) ∧
      (Q:ℝ)*polynomialCurveProductAgreementConstant g v h d*(n:ℝ)^(d+1)≤p) ↔
        Q*coefficient s v h d*n^(d+1)≤p := by
  constructor
  · rintro ⟨g,hg,hm,hp⟩
    have cc := coefficient_floor (v:=v) (h:=h) (d:=d) hs hg hm
    have qr := mul_le_mul_of_nonneg_left cc (Nat.cast_nonneg Q)
    exact_mod_cast (mul_le_mul_of_nonneg_right qr (show (0:ℝ)≤(n:ℝ)^(d+1) by positivity)).trans hp
  · intro hp
    refine ⟨1/(s:ℝ),by positivity,le_rfl,?_⟩
    rw [coefficient_reciprocal hs]
    exact_mod_cast hp

private theorem order_three_floor {d v h : ℕ} (hd : 3≤d) (hv : 0<v) (hh : 0<h) :
    473≤coefficient 1 v h d := by
  unfold coefficient
  have p1 : 8≤(2*1)^d := (Nat.pow_le_pow_right (by decide : 0<2) hd : 2^3≤2^d)
  have p2 : 1≤v^(d+2) := Nat.one_le_pow _ _ hv
  have p3 : 56≤1*h*(d+1)*(3*d+5) := by
    calc 56=1*1*(3+1)*(3*3+5) := by decide
         _≤_ := by gcongr <;> omega
  nlinarith only [hh,Nat.mul_le_mul (Nat.mul_le_mul p1 p2) (Nat.add_le_add_right p3 3)]

/-- At the sponsor block length, every general-order product certificate
whose estimate can fit a sub-256-bit field has derivative order at most two. -/
theorem production_order_le_two {g : ℝ} {v h d p : ℕ} (hg : 0<g) (hg1 : g≤1)
    (hv : 0<v) (hh : 0<h) (hp : p<2^256)
    (hfit : (2:ℝ)^128*polynomialCurveProductAgreementConstant g v h d*((2:ℝ)^30)^(d+1)≤p) :
    d≤2 := by
  have bound := (budget_iff (2^128) (2^30) p v h d (s:=1) (by decide)).mp
    ⟨g,hg,by simpa using hg1,by norm_num at hfit ⊢; exact hfit⟩
  by_contra! hd
  have co := order_three_floor hd hv hh
  have e : (2^30)^4≤(2^30)^(d+1) := Nat.pow_le_pow_right (by decide : 0<2^30) (by omega)
  have huge : 2^128*473*(2^30)^4 ≤ p :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ co) e).trans bound
  omega

/-- At order two and slack at most one quarter, all feasible profiles satisfy
this exact reciprocal-slack height/jet-degree budget. -/
theorem order_two_quarter_budget {g : ℝ} {p v h : ℕ} (hg : 0<g) (hg4 : g≤1/4)
    (hfit : (2:ℝ)^128*polynomialCurveProductAgreementConstant g v h 2*((2:ℝ)^30)^3≤p) :
    2^218*(h+(8448*h+192)*v^4) ≤ p := by
  have b := (budget_iff (2^128) (2^30) p v h 2 (s:=4) (by decide)).mp
    ⟨g,hg,by exact hg4,by norm_num at hfit ⊢; exact hfit⟩
  unfold coefficient at b
  convert b using 1 <;> ring

/-- Measured against the two parameter units `h v⁴`, the order-two necessary
budgets for the three large production primes are explicit integers. -/
theorem named_order_two_caps {g : ℝ} {v h : ℕ} (hg : 0<g) (hg4 : g≤1/4) :
    let cost := (2:ℝ)^128*polynomialCurveProductAgreementConstant g v h 2*((2:ℝ)^30)^3
    (cost≤ArkLib.ProximityGap.Frontier.DyadicLogWitness237.P → h*v^4≤35) ∧
    (cost≤FourRateListPrime246.P → h*v^4≤16135) ∧
    (cost≤BlsScalarSubgroup.P → h*v^4≤14734505) := by
  dsimp only
  have tight {p : ℕ} (hfit : (2:ℝ)^128*polynomialCurveProductAgreementConstant g v h 2*((2:ℝ)^30)^3≤p) :
      (2^218*8448)*(h*v^4)≤p := by
    have est := order_two_quarter_budget hg hg4 hfit
    apply le_trans _ est
    ring_nf
    omega
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  all_goals have ht := tight hx
  · unfold ArkLib.ProximityGap.Frontier.DyadicLogWitness237.P at ht
    omega
  · unfold FourRateListPrime246.P at ht
    omega
  · unfold BlsScalarSubgroup.P at ht
    omega

end ProximityGap.HigherOrderFieldBudget

#print axioms ProximityGap.HigherOrderFieldBudget.budget_iff
#print axioms ProximityGap.HigherOrderFieldBudget.production_order_le_two
#print axioms ProximityGap.HigherOrderFieldBudget.named_order_two_caps
