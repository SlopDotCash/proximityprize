/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HalfRateJetCapacity
import Mathlib.Tactic.Positivity

/-! # A small unrestricted auxiliary at the first half-rate successor -/

set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorSectionBudget

open HalfRateUnrestrictedJetBudget (cap closed six_cap capacity_chord)

private abbrev n : ℤ := 1073741824
private abbrev d : ℤ := 536870911
private abbrev t : ℤ := 805306367
private abbrev m : ℤ := 14
private abbrev mu : ℤ := 15
private abbrev s : ℤ := 1838
private abbrev N : ℕ := 23
private abbrev U : ℤ := mu*t

def budget (b w : ℤ) : ℤ :=
  let q := 6*b-5
  let hb := (6*b-2)*w-3*b^2*d
  q*(6*cap s d U N-6*cap (s-b) d (U-w) N-3*m*n*mu*(mu+1)) -
    3*(s+1-m)*(2*(mu-b+1)*(hb+3*b*(b-1)*n)+q*n*b*(b-1))

private theorem positive_endpoints (b : ℤ) (hb : 2 ≤ b) (hb' : b ≤ 4) :
    0 < budget b (b*d) ∧ 0 < budget b (3*t-1) := by
  interval_cases b <;> constructor <;> unfold budget <;>
    rw [six_cap s d U N N (le_refl _) (by decide) (by decide) (by decide)] <;>
    first
    | rw [six_cap _ _ _ 19 N (by decide) (by decide) (by decide) (by decide)]
    | rw [six_cap _ _ _ 20 N (by decide) (by decide) (by decide) (by decide)]
    | rw [six_cap _ _ _ 21 N (by decide) (by decide) (by decide) (by decide)]
  all_goals norm_num [closed,s,d,U,mu,t,N,m,n]

/-- The strict dimension surplus holds for every possible weight of every irreducible
factor of value degree two through four. The budget is six times the dimension surplus
after multiplication by the positive Hessian denominator. -/
theorem production_budget (b w : ℤ) (hb : 2 ≤ b) (hb' : b ≤ 4)
    (hl : b*d ≤ w) (hr : w ≤ 3*t-1) : 0 < budget b w := by
  let lo := b*d
  let hi := 3*t-1
  have hlt : lo < hi := by dsimp [lo,hi,d,t]; omega
  have hL : 0 ≤ w-lo := sub_nonneg.mpr hl
  have hR : 0 ≤ hi-w := sub_nonneg.mpr hr
  have ch := capacity_chord (s-b) d U lo hi w N (by dsimp [s,N]; omega) hl hr
  have prod := mul_le_mul_of_nonneg_left ch (show 0 ≤ 6*(6*b-5) by omega)
  have hs : (hi-w)*budget b lo+(w-lo)*budget b hi ≤ (hi-lo)*budget b w := by
    unfold budget
    linear_combination prod
  obtain ⟨p,q⟩ := positive_endpoints b hb hb'
  change 0 < budget b lo at p
  change 0 < budget b hi at q
  have h1 := mul_le_mul_of_nonneg_left (show 1 ≤ budget b lo by omega) hR
  have h2 := mul_le_mul_of_nonneg_left (show 1 ≤ budget b hi by omega) hL
  have hpos : 0 < (hi-lo)*budget b w := by linarith only [h1,h2,hs,hlt]
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr hlt)).mp hpos

end ArkLib.ProximityGap.Frontier.HalfSuccessorSectionBudget

namespace ProximityGap.HalfSuccessorSectionCapacity
open ArkLib.ProximityGap.Frontier
open HalfRateUnrestrictedJetBudget (cap)
open HalfSuccessorSectionBudget (production_budget)
open SecondPrimeQuarticInterpolation (Monomials)
open HalfRateJetCapacity (cast_monomials)

private abbrev s : ℕ := 1838
private abbrev n : ℕ := 1073741824
private abbrev d : ℕ := 536870911
private abbrev t : ℕ := 805306367
private abbrev μ : ℕ := 15
private abbrev U : ℕ := μ*t
private abbrev J : ℕ := 22
private abbrev A : ℕ := μ*(μ+1)/2
private abbrev m : ℕ := 14
private abbrev B : ℕ := s+1-m

private def kernelCost (r : ℕ) : ℕ := ((μ-r)*(μ-r+1)/2)*B
private def charge (r : ℕ) : ℕ := r*(3*r-2)

/-- The native window has a nonmultiple jet solution whenever the actual received orders
obey the numerical reverse-Hessian intersection estimate. -/
theorem strict_count {I : Type*} [Fintype I] (r : I → ℕ) (b W : ℕ)
    (hb : 2 ≤ b) (hb' : b ≤ 4) (hn : Fintype.card I = n)
    (hs : ∀ i, r i ≤ b) (hl : b*d ≤ W) (hu : W ≤ 3*t-1)
    (hc : (∑ i, r i * (3*r i-2)) + 3*b^2*d ≤ (6*b-2)*W) :
    n * (A*(s+1)) + Fintype.card (Monomials (s-b) J d (U-W)) <
      Fintype.card (Monomials s J d U) + ∑ i, ((μ-r i)*(μ-r i+1)/2)*B := by
  classical
  have cap₁ := cast_monomials s J d U (by decide)
  have cap₂ := cast_monomials (s-b) J d (U-W) (by dsimp [s,J]; omega)
  have ht : W ≤ U := by dsimp [U,μ,t] at *; omega
  rw [Nat.cast_sub ht, Nat.cast_sub (by dsimp [s]; omega)] at cap₂
  let q := 6*b-5
  have hlocal (i : I) :
      6*q*((s+1)*A) ≤ 6*q*kernelCost (r i) + 6*q*m*A +
        3*B*(2*(μ-b+1)*(charge (r i)+3*b*(b-1)) + q*b*(b-1)) := by
    have hi := hs i
    dsimp only [q]
    interval_cases b <;> interval_cases h : r i <;> decide
  have hsums := sum_le_sum (s := (univ : Finset I)) (fun i _ => hlocal i)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← mul_sum] at hsums
  have hch : (∑ i, charge (r i)) + 3*b^2*d ≤ (6*b-2)*W := hc
  have hbZ := production_budget (b : ℤ) (W : ℤ) (by exact_mod_cast hb) (by exact_mod_cast hb')
    (by change (b : ℤ) * (d : ℕ) ≤ (W : ℤ); exact_mod_cast hl)
    (by change (W : ℤ) ≤ 2415919100; exact_mod_cast hu)
  change 0 < (6*(b:ℤ)-5) * (6*cap s d U (J+1) - 6*cap ((s:ℤ)-b) d ((U:ℤ)-W) (J+1) -
    3*m*n*μ*(μ+1)) - 3*B*(2*((μ:ℤ)-b+1)*((6*b-2)*W-3*b^2*d+3*b*(b-1)*n)+
    (6*b-5)*n*b*(b-1)) at hbZ
  rw [← cap₁, ← cap₂] at hbZ
  change n*(A*(s+1)) + _ < _ + ∑ i, kernelCost (r i)
  dsimp only [q] at hsums
  rw [hn] at hsums
  generalize hp : Fintype.card (Monomials s J d U) = C at hbZ ⊢
  generalize hq : Fintype.card (Monomials (s-b) J d (U-W)) = Q at hbZ ⊢
  generalize hx : (∑ i, charge (r i)) = chargeTotal at hch hsums
  generalize hy : (∑ i, kernelCost (r i)) = kernelTotal at hsums ⊢
  clear hp hq hx hy cap₁ cap₂ hlocal
  interval_cases b <;> norm_num [d, t, U, s, n, μ, A, B, m, J] at hbZ hsums hch ⊢ <;> omega

#print axioms strict_count
end ProximityGap.HalfSuccessorSectionCapacity
