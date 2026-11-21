/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import Mathlib.Tactic.Positivity

/-! # Exact unrestricted interpolation capacities at the half-rate threshold lower bound -/

set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.HalfRateUnrestrictedJetBudget

/-- Count value layers through `N-1`, with a strict weight cutoff and a simultaneous total-degree cap. -/
def cap (r d v : ℤ) (N : ℕ) : ℤ := ∑ j ∈ range N, (r+1-j)*max (v-j*d) 0

/-- Six times the exact polynomial sum when its first `L` value layers have positive weight. -/
def closed (r d v : ℤ) (L : ℕ) : ℤ :=
  6*L*(r+1)*v-3*(v+(r+1)*d)*L*(L-1)+d*L*(L-1)*(2*L-1)

private theorem six_spots (r d v : ℤ) (L : ℕ) :
    6 * (∑ j ∈ range L, (r+1-(j : ℤ))*(v-j*d)) = closed r d v L := by
  induction L with
  | zero => simp [closed]
  | succ L ih =>
    rw [sum_range_succ,mul_add,ih]
    simp only [closed,Nat.cast_succ]
    ring

theorem six_cap (r d v : ℤ) (L N : ℕ) (hLN : L ≤ N) (hd : 0 ≤ d)
    (hlo : (L-1 : ℤ)*d ≤ v) (hhi : v ≤ (L : ℤ)*d) :
    6*cap r d v N = closed r d v L := by
  rw [← six_spots]
  unfold cap
  congr 1
  calc
    _ = ∑ j ∈ range L, (r+1-(j : ℤ))*max (v-j*d) 0 := by
      apply (sum_subset (range_mono hLN) ?_).symm
      intro k hk hkn
      have hl : L ≤ k := by simpa only [mem_range,not_lt] using hkn
      have hh := mul_le_mul_of_nonneg_right (show (L : ℤ) ≤ k by exact_mod_cast hl) hd
      rw [max_eq_right (by omega),mul_zero]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hh : (j : ℤ) ≤ L-1 := by have := mem_range.mp hj; omega
      have he := mul_le_mul_of_nonneg_right hh hd
      rw [max_eq_left (by omega)]

/-- Discrete convexity in the cutoff, written as a denominator-free chord inequality. -/
theorem capacity_chord (s d U lo hi w : ℤ) (N : ℕ) (hN : (N : ℤ) ≤ s+2)
    (hl : lo ≤ w) (hr : w ≤ hi) :
    (hi-lo)*cap s d (U-w) N ≤ (hi-w)*cap s d (U-lo) N+(w-lo)*cap s d (U-hi) N := by
  simp only [cap,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro j hj
  let l := U-lo-(j : ℤ)*d
  let r := U-hi-(j : ℤ)*d
  let c := U-w-(j : ℤ)*d
  have hw : (hi-lo)*c=(hi-w)*l+(w-lo)*r := by dsimp [c,l,r]; ring
  have h1 : (hi-w)*l ≤ (hi-w)*max l 0 := mul_le_mul_of_nonneg_left (le_max_left ..) (by omega)
  have h2 : (w-lo)*r ≤ (w-lo)*max r 0 := mul_le_mul_of_nonneg_left (le_max_left ..) (by omega)
  have hc : (hi-lo)*max c 0 ≤ (hi-w)*max l 0+(w-lo)*max r 0 := by
    by_cases h : 0 ≤ c
    · rw [max_eq_left h,hw]; omega
    · rw [max_eq_right (by omega),mul_zero]
      exact add_nonneg (mul_nonneg (by omega) (le_max_right ..)) (mul_nonneg (by omega) (le_max_right ..))
  have hn : 0 ≤ s+1-(j : ℤ) := by have := mem_range.mp hj; omega
  convert mul_le_mul_of_nonneg_left hc hn using 1 <;> dsimp [l,r,c] <;> ring

private abbrev h : ℤ := 268435456
private abbrev n : ℤ := 1073741824
private abbrev d : ℤ := 536870911
private abbrev t : ℤ := 791228368
private abbrev m : ℤ := 58
private abbrev mu : ℤ := 1712
private abbrev s : ℤ := 536797744
private abbrev N : ℕ := 2524
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
    | rw [six_cap _ _ _ 2519 N (by decide) (by decide) (by decide) (by decide)]
    | rw [six_cap _ _ _ 2520 N (by decide) (by decide) (by decide) (by decide)]
    | rw [six_cap _ _ _ 2521 N (by decide) (by decide) (by decide) (by decide)]
    | rw [six_cap _ _ _ 2522 N (by decide) (by decide) (by decide) (by decide)]
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

/-- The scalar resultant bound compared against the label allocation per value degree. -/
theorem resultant_bound (b : ℤ) (hb : 2 ≤ b) : b*s+m*2523 ≤ b*(2*h) := by
  dsimp [s,m,h]
  omega

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- A genuine quartic containing every rich section at 282,513,456 errors. -/
theorem production_surface {F : Type} [Field F] {ι : Type*} [Fintype ι]
    (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i+j ≤ 58 ∧ a+j*536870911 < 3*791228368) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 536870911 → ∀ S : Finset ι, 791228368 ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x+g*v x) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  have hc : Fintype.card ι * Fintype.card (JetRows 58 3) < Fintype.card (Monomials 58 4 536870911 (3*791228368)) := by
    rw [hn]
    simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    norm_num [Fin.sum_univ_succ]
  obtain ⟨c,hc,_,hall⟩ := exists_surface dom u v (by decide) (by decide) (by decide) hc
  refine ⟨surface c,surface_ne_zero hc,fun _ _ _ hh => surface_support c hh,?_⟩
  intro g q hq S hS hag
  rw [surface_eval]
  exact hall g q hq S hS hag

#print axioms production_budget
#print axioms resultant_bound
#print axioms production_surface
end ArkLib.ProximityGap.Frontier.HalfRateUnrestrictedJetBudget
