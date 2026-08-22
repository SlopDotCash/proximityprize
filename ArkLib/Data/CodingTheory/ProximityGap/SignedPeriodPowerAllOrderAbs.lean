/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodPowerEvenFloor
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodZeroSumBridge

/-!
# The ALL-ORDER (incl. ODD) signed period-power ABSOLUTE bound (#444, #407)

The signed period-power identity (`SignedPeriodZeroSumBridge`) puts the located thinness-essential
prize object into the canonical form

>   `∑_{ψ≠0} η_ψ^r = q · W_r − |S|^r`,    `W_r = zeroSumCount S r`,   `η_ψ = ∑_{x∈S} ψ x`.

`SignedPeriodPowerEvenFloor` exploits this at **EVEN** `r` only: there each `η_ψ^r = (η_ψ.re)^r ≥ 0`
is a nonnegative real, giving the one-sided **floor** `q·W_r − |S|^r ≤ (q−1)·M^r` (and `|S|^r ≤ q·W_r`).
The even route is structurally blind to **odd** `r` — exactly the regime the `OddZeroSumCountVanish`
analysis flags as the locus of the open BGK wall over the finite field `F_q` (over ℂ the odd-order
`W_r` vanishes; the `F_q`-reduction creates the signed odd zero-sum coincidences char 0 forbids).

This file supplies the **ALL-ORDER** (odd `r` included) **two-sided absolute** companion. The plain
absolute bound needs nothing about `S`: by the triangle inequality and `‖η_ψ^r‖ = ‖η_ψ‖^r ≤ M^r`,

>   `‖q·W_r − |S|^r‖  =  ‖∑_{ψ≠0} η_ψ^r‖  ≤  (q−1)·M^r`     (`abs_signedPeriodPow_le_card_mul_max_pow`).

The point of negation-closure (reality) is only that it makes the bounded quantity
`∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r` a genuinely **signed real** number, so the absolute bound becomes a
**two-sided bracket** `−(q−1)M^r ≤ q·W_r − |S|^r ≤ (q−1)M^r` on a real residual. The right inequality
recovers (and extends to ODD `r`) the even-floor's one-sided bound; the left inequality is the new
odd-side content the even file gets free from nonnegativity but cannot *state* at odd `r`.

(Here the residual `q·W_r − |S|^r` is automatically real — `W_r`, `|S|` are naturals — so the complex
norm of the residual is its real absolute value with NO hypothesis; the real-form bracket is therefore
also hypothesis-free. Negation-closure is what makes the *equal* signed sum `∑_{ψ≠0} η_ψ^r` real
term-by-term, but we route through the residual, so the statements are clean and unconditional.)

## HONEST SCOPE

This is still a LOWER constraint on `M` (it bounds the signed residual *by* `M`: a small `M` would
*force* the signed odd residual `q·W_r − n^r` small), NOT an UPPER bound on `M`. So it is **NOT** a
CORE closure and cannot be — bounding `M` from above at `r ≈ log q` is the open BGK wall. Its value:
it extends the even-floor pin to the ODD grade, locating the signed odd residual `q·W_r − n^r`
(which is `≠ 0` over `F_q`, `= 0` over ℂ by `OddZeroSumCountVanish`) inside the `±(q−1)M^r` band, so
the entire all-order signed object is now M-controlled, not just the even one. NON-MOMENT (the bound
is on the SIGNED real residual, not a `|·|^{2r}` energy packaging), field-universal, EXTEND of the
canonical bridge + even floor. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Issues #444, #407.
-/

set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.ProximityGap.SignedPeriodPowerEvenFloor

open Finset SignedPeriodPowerCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`‖η_ψ^r‖ = ‖η_ψ‖^r ≤ M^r` for ANY `r` (odd or even).**
`‖η^r‖ = ‖η‖^r` (multiplicativity of the norm) and `‖η‖ ≤ M`. No parity and no structural hypothesis
on `S`: this is the bare absolute bound on a complex power, and the absolute value is taken, so odd
`r` is included. -/
theorem abs_period_pow_le_max_pow {ψ : AddChar F ℂ} {S : Finset F} (r : ℕ) {M : ℝ}
    (hM : ‖∑ x ∈ S, ψ x‖ ≤ M) :
    ‖(∑ x ∈ S, ψ x) ^ r‖ ≤ M ^ r := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hM r

/-- **THE ALL-ORDER ABSOLUTE BOUND: `‖q·W_r − |S|^r‖ ≤ (q−1)·M^r` for EVERY `r` (odd incl.).**

The triangle inequality over the `q − 1` nonzero characters gives `‖∑_{ψ≠0} η_ψ^r‖ ≤ (q−1)·M^r`
(each `‖η_ψ^r‖ = ‖η_ψ‖^r ≤ M^r`, no parity), and the canonical bridge
`∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r` (`nonzeroSignedPeriodPow_eq`) rewrites the LHS. This is the ODD-order
companion the even floor (which needs `η_ψ^r ≥ 0`) cannot express: only the absolute value is used. -/
theorem abs_signedPeriodPow_le_card_mul_max_pow {S : Finset F} (r : ℕ) {M : ℝ}
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    ‖(Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r‖
      ≤ ((univ.erase (0 : AddChar F ℂ)).card : ℝ) * M ^ r := by
  -- the canonical bridge: q·W_r − |S|^r = ∑_{ψ≠0} η_ψ^r
  have hid : (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r
      = ∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r :=
    (nonzeroSignedPeriodPow_eq S r).symm
  rw [hid]
  -- triangle inequality, then each summand ≤ M^r
  calc ‖∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r‖
      ≤ ∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖(∑ x ∈ S, ψ x) ^ r‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _ψ ∈ (univ.erase (0 : AddChar F ℂ)), M ^ r :=
        Finset.sum_le_sum (fun ψ hψ => abs_period_pow_le_max_pow r (hM ψ hψ))
    _ = ((univ.erase (0 : AddChar F ℂ)).card : ℝ) * M ^ r := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Two-sided REAL form: `|q·W_r − |S|^r| ≤ (q−1)·M^r` for EVERY `r` (odd incl.).**

The residual `q·W_r − |S|^r` is the coercion of a real number (`W_r`, `|S|` are naturals), so its
complex norm is the real absolute value `|·|`. This turns the all-order absolute bound into a genuine
two-sided bracket on a SIGNED real quantity: `−(q−1)M^r ≤ q·W_r − |S|^r ≤ (q−1)M^r`. The right side
extends the even floor's `signedPeriodPow_le_card_mul_max_pow` to ODD `r`; the left side is the new
odd-grade lower bracket (the even file gets it from nonnegativity but cannot state it at odd `r`). -/
theorem signedPeriodPow_re_abs_le {S : Finset F} (r : ℕ) {M : ℝ}
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    |((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r)|
      ≤ ((univ.erase (0 : AddChar F ℂ)).card : ℝ) * M ^ r := by
  have habs := abs_signedPeriodPow_le_card_mul_max_pow (S := S) r hM
  -- the complex residual is the coercion of the real residual q·W_r − |S|^r
  have hcoe : (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r
      = (((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r : ℝ) : ℂ) := by push_cast; ring
  rw [hcoe, Complex.norm_real] at habs
  exact habs

/-- **M-LOWER bound from the SIGNED residual: `M^r ≥ |q·W_r − |S|^r| / (q−1)` for EVERY `r` (odd incl.).**

The consumer form of `signedPeriodPow_re_abs_le`: dividing the two-sided bracket by the positive count
`q − 1` of nonzero characters solves for `M^r` and lower-bounds it by the signed residual. For ODD `r`
this is genuinely new (the even floor's `signedPeriodPow_le_card_mul_max_pow` only reaches even `r`):
any odd-order signed zero-sum residual `q·W_r − n^r` — which is `≠ 0` precisely via the `F_q`-reduction
(`OddZeroSumCountVanish`: it is `0` over ℂ) — FORCES the period max `M` up. So the deep odd `F_q`-only
zero-sum coincidences, the located locus of the BGK wall, are exactly the source of an `M`-lower push.
Honest scope: a LOWER bound on `M` (the prize wants an UPPER bound), NOT a CORE closure. CORE OPEN. -/
theorem max_pow_ge_abs_signed_div {S : Finset F} (r : ℕ) {M : ℝ}
    (hpos : 0 < ((univ.erase (0 : AddChar F ℂ)).card : ℝ))
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    |((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r)|
        / ((univ.erase (0 : AddChar F ℂ)).card : ℝ)
      ≤ M ^ r := by
  rw [div_le_iff₀ hpos]
  have h := signedPeriodPow_re_abs_le (S := S) r hM
  linarith [h]

/-- **The nonzero-character count is exactly `q − 1`.** `#(univ.erase 0) = #(AddChar F ℂ) − 1 = q − 1`
via `AddChar.card_eq` (`#(AddChar F ℂ) = #F = q`). Lets the bracket be read in the BGK `q−1` vocabulary. -/
theorem card_erase_zero_addChar :
    (univ.erase (0 : AddChar F ℂ)).card = Fintype.card F - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq]

/-- **The bracket in the BGK `q−1` vocabulary: `|q·W_r − |S|^r| ≤ (q−1)·M^r`.**
The `q−1`-normalized restatement of `signedPeriodPow_re_abs_le` (rewriting the nonzero-character count
`#(univ.erase 0)` to `q − 1` via `card_erase_zero_addChar`), so it plugs directly into the `q−1`-shaped
BGK / Parseval statements. Holds for EVERY `r` (odd incl.). -/
theorem signedPeriodPow_re_abs_le_qsub_one {S : Finset F} (r : ℕ) {M : ℝ}
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    |((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r)|
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * M ^ r := by
  have h := signedPeriodPow_re_abs_le (S := S) r hM
  rwa [card_erase_zero_addChar] at h

/-- **VANISHING-CASE FLOOR: if `W_r = 0` then `(q−1)·M^r ≥ |S|^r`.**

When the zero-sum count `W_r = zeroSumCount S r` vanishes (no order-`r` additive coincidence at all
— the maximally-Sidon case, e.g. the ODD orders over ℂ by `OddZeroSumCountVanish`, or any depth below
the Sidon depth `ℓ`), the signed residual collapses to its pure diagonal `q·0 − |S|^r = −|S|^r`, so the
bracket `|q·W_r − |S|^r| ≤ (q−1)M^r` becomes the clean floor `|S|^r ≤ (q−1)·M^r`, i.e.
`M^r ≥ |S|^r/(q−1)`. So *absence* of order-`r` zero-sum coincidences FORCES the period max up to
`≈ |S|/q^{1/r}`. This is the sharp endpoint of the all-order bracket: the diagonal term, unopposed by
any off-diagonal cancellation, is itself an `M`-lower push. Holds for EVERY `r` (odd incl.).
Honest scope: an `M`-LOWER bound in the no-coincidence regime; NOT a CORE upper bound. CORE OPEN. -/
theorem card_pow_le_qsub_one_mul_max_pow_of_zeroSumCount_eq_zero {S : Finset F} (r : ℕ) {M : ℝ}
    (hW : ((Fintype.piFinset (fun _ : Fin r => S)).filter (fun t => ∑ i, t i = 0)).card = 0)
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    (S.card : ℝ) ^ r ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * M ^ r := by
  have h := signedPeriodPow_re_abs_le_qsub_one (S := S) r hM
  rw [hW] at h
  -- residual is |q·0 − |S|^r| = |S|^r
  simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg] at h
  rwa [abs_of_nonneg (by positivity)] at h

/-- **`q−1`-normalized M-lower consumer.** This is `max_pow_ge_abs_signed_div` rewritten with
`#(AddChar F ℂ \ {0}) = q−1`, so downstream BGK statements can divide directly by the familiar
nonzero-frequency count. Holds for every order `r`, including odd `r`. Honest scope: still an
`M`-LOWER bound, not a CORE upper bound. -/
theorem max_pow_ge_abs_signed_div_qsub_one {S : Finset F} (r : ℕ) {M : ℝ}
    (hpos : 0 < ((Fintype.card F - 1 : ℕ) : ℝ))
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    |((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r)|
        / ((Fintype.card F - 1 : ℕ) : ℝ)
      ≤ M ^ r := by
  rw [div_le_iff₀ hpos]
  simpa [mul_comm] using signedPeriodPow_re_abs_le_qsub_one (S := S) r hM

/-- **Vanishing-case M-lower floor in divided `q−1` form.** If `W_r=0`, the diagonal term alone
forces `M^r ≥ |S|^r/(q−1)`. This is the divided consumer form of
`card_pow_le_qsub_one_mul_max_pow_of_zeroSumCount_eq_zero`, useful when the
no-coincidence/Sidon-depth hypothesis is the input. Honest scope: a lower bound on `M`, not CORE. -/
theorem max_pow_ge_card_pow_div_qsub_one_of_zeroSumCount_eq_zero {S : Finset F} (r : ℕ) {M : ℝ}
    (hpos : 0 < ((Fintype.card F - 1 : ℕ) : ℝ))
    (hW : ((Fintype.piFinset (fun _ : Fin r => S)).filter (fun t => ∑ i, t i = 0)).card = 0)
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    (S.card : ℝ) ^ r / ((Fintype.card F - 1 : ℕ) : ℝ) ≤ M ^ r := by
  rw [div_le_iff₀ hpos]
  simpa [mul_comm] using
    card_pow_le_qsub_one_mul_max_pow_of_zeroSumCount_eq_zero (S := S) r hW hM

-- Axiom audit (full-env `lean` confirms ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms abs_period_pow_le_max_pow
#print axioms abs_signedPeriodPow_le_card_mul_max_pow
#print axioms signedPeriodPow_re_abs_le
#print axioms max_pow_ge_abs_signed_div
#print axioms card_erase_zero_addChar
#print axioms signedPeriodPow_re_abs_le_qsub_one
#print axioms card_pow_le_qsub_one_mul_max_pow_of_zeroSumCount_eq_zero
#print axioms max_pow_ge_abs_signed_div_qsub_one
#print axioms max_pow_ge_card_pow_div_qsub_one_of_zeroSumCount_eq_zero

end ArkLib.ProximityGap.SignedPeriodPowerEvenFloor
