/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfRateUnrestrictedJetBudget
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicQuotientWindow

/-! # Exact capacity of the half-rate unrestricted auxiliary and polynomial multiples -/

open Finset Polynomial Module
open ArkLib.ProximityGap.Frontier
open SecondPrimeQuarticInterpolation (Monomials)
open HalfRateUnrestrictedJetBudget (cap budget production_budget)
namespace ProximityGap.HalfRateJetCapacity

private abbrev s : ℕ := 536797744
private abbrev n : ℕ := 1073741824
private abbrev d : ℕ := 536870911
private abbrev t : ℕ := 791228368
private abbrev μ : ℕ := 1712
private abbrev U : ℕ := μ*t
private abbrev J : ℕ := 2523
private abbrev A : ℕ := μ*(μ+1)/2
private abbrev m : ℕ := 58
private abbrev B : ℕ := s+1-m

/-- Exact cardinality of the simultaneous coordinate-weight and scalar/value-degree window. -/
theorem cast_monomials (s b d t : ℕ) (hb : b ≤ s) :
    (Fintype.card (Monomials s b d t) : ℤ) = cap s d t (b+1) := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_sum, Nat.cast_mul, cap, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  have hi : i.val ≤ b := by have := i.isLt; omega
  rw [Nat.cast_sub (by omega : i.val ≤ s+1), Nat.cast_add, Nat.cast_one]
  congr 1
  by_cases h : i.val * d ≤ t
  · rw [Nat.cast_sub h, Nat.cast_mul, max_eq_left]; exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_not_ge h)

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
    (by change (W : ℤ) ≤ 2373685103; exact_mod_cast hu)
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

#print axioms cast_monomials
#print axioms strict_count
end ProximityGap.HalfRateJetCapacity
