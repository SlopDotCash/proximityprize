/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-!
# The char-0 LEADING term has generating function `(1+t)ⁿ` — exact (#444)

## Context (probe-grounded)

The just-landed `_FallingFactorialDecay` (Shaw, afdd84d8b) and `_Char0LeadingGaussianTailBound` (this
campaign, 28848e11e) established that the **leading (all-distinct) term** of the char-0 generic additive
energy `E_r = #{(a,b)∈Sʳ×Sʳ : Σa = Σb}` is
  `L_r = r!·(n)_r`,   `(n)_r = n(n−1)···(n−r+1) = Nat.descFactorial n r`
(the antipodal-matching / Lam–Leung term with DISTINCT pair-values `(n)_r` rather than `n^r`).

Shaw flagged the binomial EGF `Σ_r (n)_r t^r/r! = (1+t)ⁿ` as a PROMISING structured handle. This file
crystallizes it as an **exact identity tied to the proven leading term `L_r`**
(`probe_leading_egf_exact_identity.py`, PASS, exact + coefficientwise):

  **`L_r = (r!)²·C(n,r)`**   (coefficientwise), hence the generating function
  **`Σ_{r=0}^{n} (L_r / (r!)²)·t^r = (1+t)ⁿ`.**

I.e. the leading char-0 energy contributions ARE the binomial coefficients (rescaled by `(r!)²`), summing
to the clean closed form `(1+t)ⁿ`.

**Honest scope — this is a structural identity for the LEADING TERM only, NOT a prize route.** The
*full-energy* binomial-EGF prize route `Σ_r A_r/(2r−1)‼·t^r/r! ≤ (1+t)ⁿ` was REFUTED (Shaw, 0040d6507):
it requires `A_r/(2r−1)‼ ≤ (n)_r` coefficientwise, machine-FALSE at `r ≥ 3` (the FULL char-0 energy `A_r`
exceeds the falling-factorial leading shape by `O(r²/n)` — the same coefficientwise gap this campaign's
LANE-1 found refuting conj #3 exactness). This file therefore claims ONLY the exact generating function of
the *leading* contribution `L_r` (which equals the binomial theorem `Σ C(n,r) t^r = (1+t)ⁿ`); it makes NO
prize claim. The prize remains the char-`p` transfer of the FULL energy = the BGK wall. No CORE/BGK/capacity
claim. Pure binomial-theorem content (`add_pow`) + the descFactorial/choose bridge; axiom-clean.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Char0LeadingBinomialEGF

open scoped BigOperators
open Finset

/-- The char-0 leading term as a natural number: `L_r = r!·(n)_r` with `(n)_r = Nat.descFactorial n r`. -/
def leadingNat (n r : ℕ) : ℕ := r.factorial * Nat.descFactorial n r

/-- **Coefficientwise identity: `L_r = (r!)²·C(n,r)`.** Uses the Mathlib bridge
`Nat.descFactorial n r = r! · C(n,r)`. -/
theorem leadingNat_eq_factorial_sq_mul_choose (n r : ℕ) :
    leadingNat n r = (r.factorial * r.factorial) * n.choose r := by
  unfold leadingNat
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-- The real-valued normalized leading coefficient `L_r / (r!)² = C(n,r)`. -/
theorem leadingNat_div_factorial_sq (n r : ℕ) :
    (leadingNat n r : ℝ) / ((r.factorial : ℝ) * (r.factorial : ℝ)) = (n.choose r : ℝ) := by
  rw [leadingNat_eq_factorial_sq_mul_choose]
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast r.factorial_pos
  push_cast
  field_simp

/-- **The generating-function identity: `Σ_{r=0}^{n} (L_r/(r!)²)·t^r = (1+t)ⁿ`.** The leading char-0
energy contributions are the binomial coefficients (rescaled by `(r!)²`); their generating function is the
clean closed form `(1+t)ⁿ` (the binomial theorem, `add_pow`). -/
theorem leading_generating_function (n : ℕ) (t : ℝ) :
    (∑ r ∈ range (n + 1),
        ((leadingNat n r : ℝ) / ((r.factorial : ℝ) * (r.factorial : ℝ))) * t ^ r)
      = (1 + t) ^ n := by
  have hcoeff : ∀ r ∈ range (n + 1),
      ((leadingNat n r : ℝ) / ((r.factorial : ℝ) * (r.factorial : ℝ))) * t ^ r
        = t ^ r * 1 ^ (n - r) * (n.choose r : ℝ) := by
    intro r _
    rw [leadingNat_div_factorial_sq]
    simp
    ring
  rw [Finset.sum_congr rfl hcoeff]
  have := add_pow t (1 : ℝ) n
  rw [add_comm (1 : ℝ) t]
  exact this.symm

/-- **Corollary (the `(n)_r/r! = C(n,r)` binomial EGF, Shaw's handle, exact).**
`Σ_{r=0}^{n} ((n)_r/r!)·t^r = (1+t)ⁿ`. The falling-factorial leading shape `(n)_r` (the all-distinct
pair-value count) has the binomial generating function. -/
theorem fallingFactorial_generating_function (n : ℕ) (t : ℝ) :
    (∑ r ∈ range (n + 1), ((Nat.descFactorial n r : ℝ) / (r.factorial : ℝ)) * t ^ r)
      = (1 + t) ^ n := by
  have hcoeff : ∀ r ∈ range (n + 1),
      ((Nat.descFactorial n r : ℝ) / (r.factorial : ℝ)) * t ^ r
        = t ^ r * 1 ^ (n - r) * (n.choose r : ℝ) := by
    intro r _
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    have hfac : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast r.factorial_pos
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hcoeff]
  have := add_pow t (1 : ℝ) n
  rw [add_comm (1 : ℝ) t]
  exact this.symm


/-- At `t = 1`, the normalized leading contributions sum to `2^n`.  This is the
finite mass form of the leading-term binomial EGF, useful as a coefficient-normalized
check that the leading char-0 layer is exactly binomial rather than merely bounded. -/
theorem leading_normalized_mass (n : ℕ) :
    (∑ r ∈ range (n + 1),
        ((leadingNat n r : ℝ) / ((r.factorial : ℝ) * (r.factorial : ℝ))))
      = (2 : ℝ) ^ n := by
  have h := leading_generating_function n (1 : ℝ)
  norm_num at h
  exact h

/-- Equivalently, the falling-factorial coefficients have total binomial mass `2^n`. -/
theorem fallingFactorial_normalized_mass (n : ℕ) :
    (∑ r ∈ range (n + 1), ((Nat.descFactorial n r : ℝ) / (r.factorial : ℝ)))
      = (2 : ℝ) ^ n := by
  have h := fallingFactorial_generating_function n (1 : ℝ)
  norm_num at h
  exact h


/-- At `t = -1`, the normalized leading contributions have zero alternating mass for
positive `n`.  This is the cancellation-side specialization of the same exact
binomial EGF: `Σ (-1)^r L_r/(r!)² = 0`. -/
theorem leading_normalized_alternating_mass_zero {n : ℕ} (hn : 0 < n) :
    (∑ r ∈ range (n + 1),
        ((leadingNat n r : ℝ) / ((r.factorial : ℝ) * (r.factorial : ℝ))) * (-1 : ℝ) ^ r)
      = 0 := by
  have h := leading_generating_function n (-1 : ℝ)
  norm_num at h
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  rw [zero_pow hne] at h
  exact h

/-- Falling-factorial version of the same alternating cancellation:
`Σ (-1)^r (n)_r/r! = 0` for positive `n`. -/
theorem fallingFactorial_alternating_mass_zero {n : ℕ} (hn : 0 < n) :
    (∑ r ∈ range (n + 1),
        ((Nat.descFactorial n r : ℝ) / (r.factorial : ℝ)) * (-1 : ℝ) ^ r)
      = 0 := by
  have h := fallingFactorial_generating_function n (-1 : ℝ)
  norm_num at h
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  rw [zero_pow hne] at h
  exact h

end ArkLib.ProximityGap.Char0LeadingBinomialEGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.leadingNat_eq_factorial_sq_mul_choose
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.leading_generating_function
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.fallingFactorial_generating_function
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.leading_normalized_mass
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.fallingFactorial_normalized_mass
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.leading_normalized_alternating_mass_zero
#print axioms ArkLib.ProximityGap.Char0LeadingBinomialEGF.fallingFactorial_alternating_mass_zero
