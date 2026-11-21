/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Finite multiplicity counts for the second production prime

The local reverse-derivative charge bounds the total multiplicity of the
received lines. The concrete counts compare the size of the intrinsic
interpolation space with all truncated-jet equations and all scalar exceptions.
-/

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.SecondPrimeIntrinsicArithmetic

/-- A double point costs eight in the reverse intersection divisor, compared
with one for a simple point. Higher multiplicities satisfy the same bound. -/
theorem multiplicity_sum {ι : Type*} (D : Finset ι) (ell : ι → ℕ) (H : ℕ)
    (h : ∑ x ∈ D, ell x * (3 * ell x - 2) ≤ H) :
    7 * ∑ x ∈ D, ell x ≤ 6 * D.card + H := by
  have hlocal (r : ℕ) : 7 * r ≤ 6 + r * (3 * r - 2) := by
    obtain rfl | r1 := Nat.eq_zero_or_pos r
    · decide
    obtain rfl | r2 := Nat.eq_or_lt_of_le r1
    · decide
    have hh : 3 * r - 2 + 2 = 3 * r := by omega
    have hp := Nat.zero_le ((r - 2) * (r - 1))
    have ha : r - 2 + 2 = r := by omega
    have hb : r - 1 + 1 = r := by omega
    nlinarith
  have hc := sum_le_sum (s := D) (fun i _ => hlocal (ell i))
  rw [← mul_sum, sum_add_distrib] at hc
  simpa [mul_comm 6] using hc.trans (Nat.add_le_add_left h _)

/-- Exact cubic coefficient and exception counts at 396139582 agreements. -/
theorem cubic_integer_certificate :
    let n := 1073741824
    let d := 67108863
    let t := 396139582
    let w := 230220153
    let eSum := (6*n + 16*w - 27*d)/7
    let μ := 160
    let s := 700000000
    let loss := 256
    let jets := μ*eSum - (eSum-n)
    let src := (s+1)*(3*μ*(t-loss)-3*d)
    let rows := (s+3+7*(μ*(μ+1)/2))*jets
    eSum = 1187719155 ∧ rows + 30336082444 = src ∧
    3*s+2*7 < 2*n+1-22-(7*n/(loss+1)) ∧
    n-t+1 = 677602243 := by decide

/-- At the predecessor, the sharper triangular local pivot gives a strict
dimension surplus for the quartic even with the full number of degree-34 exceptions. -/
theorem quartic_integer_certificate :
    let n := 1073741824
    let d := 67108863
    let t := 357913943
    let w := 302954072
    let eSum := (6*n+22*w-48*d)/7
    let μ := 64
    let s := 67108864
    let loss := 524288
    let jets := μ*eSum - (eSum-n)
    let src := (s+1)*(4*μ*(t-loss)-6*d)
    let rows := (s+4+34*(μ*(μ+1)/2))*jets
    eSum = 1412316443 ∧ rows < src ∧
    4*s+3*34 < 2*n+1-34-(34*n/(loss+1)) := by decide

end ArkLib.ProximityGap.Frontier.SecondPrimeIntrinsicArithmetic
