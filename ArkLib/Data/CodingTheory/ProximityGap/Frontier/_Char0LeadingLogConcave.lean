/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The char-0 LEADING coefficients are LOG-CONCAVE (#444, conj #4 leading-term specialization)

## Context

`_Char0LeadingBinomialEGF` (this campaign) established that the leading (all-distinct) char-0 energy
coefficients are `L_r = (r!)²·C(n,r)`, with generating function `Σ (L_r/(r!)²) t^r = (1+t)ⁿ`. Conjecture
#4 of the 30-conjecture set asks whether `A_r/Wick` is **log-concave** (`A_r² ≥ A_{r−1}·A_{r+1}`) — a
prize-TRUE-side property that would give monotone decay from the base.

For the LEADING term, the normalized coefficient is the binomial `C(n,r)`, and binomial coefficients are
log-concave. This file proves it (`probe_leading_logconcave.py`, PASS), via the clean reduction:
  `C(n,k−1)·C(n,k+1) ≤ C(n,k)²  ⟺  k(n−k) ≤ (n−k+1)(k+1)  ⟺  0 ≤ n+1` (always).
The cross-multiplied integer form uses `Nat.choose_succ_right_eq`: `C(n,k+1)·(k+1) = C(n,k)·(n−k)`.

**Honest scope:** the LEADING-term log-concavity only (conj #4 for the dominant char-0 contribution), NOT
the full energy `A_r` and NOT the prize. No CORE/BGK/capacity claim. Pure binomial-coefficient combinatorics.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Char0LeadingLogConcave

open Nat

/-- **The cross-multiplied log-concavity for binomials (integer form):**
`C(n,k−1)·C(n,k+1)·((k+1)·(n−k+1)) ≤ C(n,k)²·((k+1)·(n−k+1))` is implied by the cleaner
`C(n,k+1)·(k+1)·(C(n,k−1)·(n−k+1)) ≤ C(n,k)·(n−k)·(C(n,k)·k) + ...`. We instead prove the standard
log-concavity directly below; this is the key per-step relation. -/
theorem choose_step (n k : ℕ) : (n.choose (k + 1)) * (k + 1) = (n.choose k) * (n - k) :=
  Nat.choose_succ_right_eq n k

/-- **Binomial log-concavity (the brick): `C(n,k−1)·C(n,k+1) ≤ C(n,k)²`** for `1 ≤ k`. Equivalently the
leading char-0 coefficient sequence is log-concave (conj #4 for the leading term). Proof: cross-multiply by
`(k+1)·(n−k+1) > 0` using `choose_succ_right_eq` twice, reducing to `k(n−k) ≤ (k+1)(n−k+1)`, i.e. `0 ≤ n+1`. -/
theorem choose_logConcave (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose (k - 1)) * (n.choose (k + 1)) ≤ (n.choose k) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  -- now k = j+1, k-1 = j, k+1 = j+2
  simp only [Nat.add_sub_cancel]
  -- relations:
  -- (A) choose (j+1) * (j+1) = choose j * (n - j)              [choose_step n j]
  -- (B) choose (j+2) * (j+2) = choose (j+1) * (n - (j+1))      [choose_step n (j+1)]
  have hA : (n.choose (j + 1)) * (j + 1) = (n.choose j) * (n - j) := choose_step n j
  have hB : (n.choose (j + 2)) * (j + 2) = (n.choose (j + 1)) * (n - (j + 1)) := by
    have := choose_step n (j + 1); simpa using this
  -- Goal: choose j * choose (j+2) ≤ (choose (j+1))^2
  -- Multiply goal by (j+1)*(j+2) > 0 and substitute via hA, hB.
  rcases le_or_gt n j with hnj | hnj
  · -- n ≤ j ⟹ choose n (j+1)=0 etc. Then LHS has choose (j+2) factor; if n ≤ j then j+2 > n so
    -- choose n (j+2) = 0, LHS = 0 ≤ RHS.
    have : n.choose (j + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
  · -- 1 ≤ n - j. Work with the cross-multiplied inequality.
    -- From hA: choose j * (n - j) = choose (j+1) * (j+1).
    -- From hB: choose (j+1) * (n - j - 1) = choose (j+2) * (j+2).
    -- Want: choose j * choose (j+2) ≤ choose (j+1)^2.
    -- Multiply both sides by (j+1)*(j+2):
    --   choose j * choose (j+2) * (j+1)*(j+2)
    --     = [choose j *(j+1)] * [choose(j+2)*(j+2)]   ... not directly hA. Use instead:
    --   (choose j * (n-j)) * (choose (j+2) * (j+2)) = (choose (j+1)*(j+1)) * (choose (j+1)*(n-j-1))
    --   = choose(j+1)^2 * (j+1)*(n-j-1).
    -- And LHS*(n-j)*(j+2) form... cleaner: bound via the products.
    have key : (n.choose j * (n - j)) * (n.choose (j + 2) * (j + 2))
        = (n.choose (j + 1)) ^ 2 * ((j + 1) * (n - (j + 1))) := by
      rw [hB, ← hA]; ring
    -- key: A_j * (n-j) * (choose(j+2)*(j+2)) = choose(j+1)^2 * (j+1)*(n-j-1)
    -- Now (n-j) = (n-j-1)+1 and (j+2) = (j+1)+1. We want choose j * choose(j+2) ≤ choose(j+1)^2.
    -- multiply target by (n-j)*(j+2):  LHS_target*(n-j)*(j+2) = key's LHS = choose(j+1)^2*(j+1)*(n-j-1)
    -- and (j+1)*(n-j-1) ≤ (n-j)*(j+2)  ⟸  (j+1)(n-j-1) ≤ (n-j)(j+2):
    --   (n-j)(j+2) - (j+1)(n-j-1) = ... = n+1 ≥ 0. So choose(j+1)^2*(j+1)(n-j-1) ≤ choose(j+1)^2*(n-j)(j+2).
    -- Hence LHS_target*(n-j)*(j+2) ≤ choose(j+1)^2*(n-j)*(j+2), cancel the positive (n-j)*(j+2).
    have hpos : 0 < (n - j) * (j + 2) := by
      have : 0 < n - j := by omega
      positivity
    have hcross : (n.choose j * n.choose (j + 2)) * ((n - j) * (j + 2))
        ≤ (n.choose (j + 1)) ^ 2 * ((n - j) * (j + 2)) := by
      calc (n.choose j * n.choose (j + 2)) * ((n - j) * (j + 2))
          = (n.choose j * (n - j)) * (n.choose (j + 2) * (j + 2)) := by ring
        _ = (n.choose (j + 1)) ^ 2 * ((j + 1) * (n - (j + 1))) := key
        _ ≤ (n.choose (j + 1)) ^ 2 * ((n - j) * (j + 2)) := by
            apply Nat.mul_le_mul_left
            -- (j+1)*(n-(j+1)) ≤ (n-j)*(j+2)
            have h1 : n - (j + 1) ≤ n - j := by omega
            -- expand: (j+1)*(n-j-1) ≤ (n-j)*(j+2). Since n>j, set m=n-j≥1.
            -- (j+1)(m-1) ≤ m(j+2) ⟺ (j+1)m - (j+1) ≤ m j + 2m ⟺ -(j+1) ≤ m j + 2m - (j+1)m = m(1) ...
            -- ⟺ -(j+1) ≤ m, true since m≥1>0>-(j+1).
            nlinarith [Nat.sub_add_cancel (le_of_lt hnj), Nat.one_le_iff_ne_zero.mpr (by omega : n - j ≠ 0)]
    exact Nat.le_of_mul_le_mul_right hcross hpos

/-- **Leading-coefficient log-concavity (the conj #4 leading-term statement).** With `c r := C(n,r)` the
normalized leading char-0 coefficient (`L_r = (r!)²·c r`), the sequence `c` is log-concave:
`c (k−1)·c (k+1) ≤ (c k)²`. -/
theorem leadingCoeff_logConcave (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose (k - 1)) * (n.choose (k + 1)) ≤ (n.choose k) ^ 2 :=
  choose_logConcave n k hk

end ArkLib.ProximityGap.Char0LeadingLogConcave

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Char0LeadingLogConcave.choose_step
#print axioms ArkLib.ProximityGap.Char0LeadingLogConcave.choose_logConcave
#print axioms ArkLib.ProximityGap.Char0LeadingLogConcave.leadingCoeff_logConcave
