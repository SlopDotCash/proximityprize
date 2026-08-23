/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodPowerCount
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# The EVEN-order signed period-power DIAGONAL FLOOR (#444, #407)

The signed period-power sum `∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r` (`SignedPeriodPowerCount`, where
`η_ψ = ∑_{x∈S} ψ x` and `W_r = #{t : Fin r → S : ∑_i t i = 0}`) is the located thinness-essential
prize object. The campaign already carries the **UPPER** bounds on `W_r` (the Johnson cap:
`zeroSumCount_le_doubleFactorial`, `(2r−1)!!·n^r`). This file supplies the matching **LOWER**
(diagonal / Parseval) floor, completing the two-sided pin on `W_r`.

## The mechanism (NON-MOMENT, via η-reality — NOT the `|·|^{2r}` energy route)

For a **negation-closed** `S` (`-x ∈ S` whenever `x ∈ S`; always true for `S = μ_n`, `n` even, since
`-1 ∈ μ_n`), every period `η_ψ = ∑_{x∈S} ψ x` is **REAL**: `conj η_ψ = ∑_x ψ(−x) = ∑_x ψ x = η_ψ`
by reindexing `x ↦ −x` (the same `eta_conj_eq_self` mechanism as `_EtaRealNegClosed`, in the
all-character `SignedPeriodPowerCount` indexing). Hence for **EVEN** `r`, each `η_ψ^r = (η_ψ.re)^r ≥ 0`,
so the signed sum is a sum of nonnegatives:

>   `0 ≤ ∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r`   ⟹   `|S|^r ≤ q·W_r`   (the diagonal floor `W_r ≥ n^r/q`).

This is **thinness-essential**: it uses `−1 ∈ S` (negation-closure). It is sign-free at even order
*because* of reality — the same `|·|` that the moment route applies destructively, here is forced by
the group structure, so this is the honest even-order content of the SIGNED identity (not a `|·|^{2r}`
energy packaging).

## The companion: the period-max LOWER bound

The same nonnegativity gives a clean LOWER bound on the period max `M = max_{b≠0} |η_b|`: for even `r`,
each `η_ψ^r = ‖η_ψ‖^r ≤ M^r`, and there are `q − 1` nonzero characters, so

>   `q·W_r − |S|^r = ∑_{ψ≠0} η_ψ^r ≤ (q−1)·M^r`   ⟹   `M^r ≥ (q·W_r − |S|^r)/(q−1)`.

## HONEST SCOPE

These are LOWER bounds on `M` and on `W_r`. The prize wants an **UPPER** bound `M ≤ C√(n log(q/n))`,
so this is **NOT** a CORE closure and cannot be — a floor is the opposite direction. Its value is
two-sided pinning: paired with the in-tree Johnson UPPER cap on `W_r`, the located object now has both
a floor (`n^r/q`) and a ceiling (`(2r−1)!!·n^r`). The floor is `√(q)`-far below the wall, so it is
*consistent* with (does not refute) the prize; it just records that the diagonal contributes a forced
`n^r/q` and the beyond-Johnson signal must live in the off-diagonal signed cancellation `q·W_r − n^r`
at deep `r ≈ log q`. NON-MOMENT, EXTEND-proven (consumes `nonzeroSignedPeriodPow_eq`), field-universal,
thinness-essential. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Probe `scripts/probes/probe_even_signed_energy_floor.py`: `22/22` EXACT over PROPER thin `μ_n`
(`p ≡ 1 mod n`, `(p−1)/n ≥ 2`, multi-prime incl. `p > n³` + Fermat 257, NEVER `n = q−1`) confirms
reality, the floor `W_r ≥ n^r/q`, and the max lower bound for `r ∈ {2,4}`.

Issues #444, #407.
-/
set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.ProximityGap.SignedPeriodPowerEvenFloor

open Finset SignedPeriodPowerCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The period `η_ψ = ∑_{x∈S} ψ x` is conjugation-invariant on a negation-closed `S`.**
`conj η_ψ = ∑_x ψ(−x) = ∑_x ψ x = η_ψ` by reindexing `x ↦ −x` (a bijection `S → S`). The
`SignedPeriodPowerCount` (all-character, untwisted) analogue of `_EtaRealNegClosed.eta_conj_eq_self`. -/
theorem period_conj_eq_self {ψ : AddChar F ℂ} {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) :
    (starRingEnd ℂ) (∑ x ∈ S, ψ x) = ∑ x ∈ S, ψ x := by
  rw [map_sum]
  -- conj(ψ x) = ψ(−x) on a finite field
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hstep : ∀ x ∈ S, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x _
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  rw [Finset.sum_congr rfl hstep]
  -- reindex x ↦ −x (involution on S)
  refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hS x hx
  · intro x hx; exact hS x hx
  · intro x _; exact neg_neg x
  · intro x _; exact neg_neg x
  · intro x _; rfl

/-- **The period has zero imaginary part on a negation-closed `S`.** -/
theorem period_im_eq_zero {ψ : AddChar F ℂ} {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) :
    (∑ x ∈ S, ψ x).im = 0 :=
  Complex.conj_eq_iff_im.mp (period_conj_eq_self hS)

/-- **The period equals the coercion of its real part** on a negation-closed `S`. -/
theorem period_eq_ofReal_re {ψ : AddChar F ℂ} {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) :
    (∑ x ∈ S, ψ x) = (((∑ x ∈ S, ψ x).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [period_im_eq_zero hS]; simp

/-- **Even powers of a real period are nonnegative reals.** For even `r` and negation-closed `S`,
`η_ψ^r = ((η_ψ.re)^r : ℂ)` with `(η_ψ.re)^r ≥ 0`. -/
theorem period_pow_even_eq_ofReal_nonneg {ψ : AddChar F ℂ} {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) {r : ℕ} (hr : Even r) :
    (∑ x ∈ S, ψ x) ^ r = (((∑ x ∈ S, ψ x).re ^ r : ℝ) : ℂ)
    ∧ (0 : ℝ) ≤ (∑ x ∈ S, ψ x).re ^ r := by
  refine ⟨?_, hr.pow_nonneg _⟩
  conv_lhs => rw [period_eq_ofReal_re hS]
  rw [← Complex.ofReal_pow]

/-- **The even-order nonzero signed period-power sum is a nonnegative real.** For even `r` and
negation-closed `S`, `0 ≤ ∑_{ψ≠0} η_ψ^r`, as a real number (each summand is `(η_ψ.re)^r ≥ 0`). -/
theorem nonzeroSignedPeriodPow_even_nonneg {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) {r : ℕ} (hr : Even r) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = (((∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x).re ^ r : ℝ)) : ℂ)
    ∧ (0 : ℝ) ≤ ∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x).re ^ r := by
  constructor
  · rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun ψ _ => (period_pow_even_eq_ofReal_nonneg hS hr).1)
  · refine Finset.sum_nonneg (fun ψ _ => (period_pow_even_eq_ofReal_nonneg hS hr).2)

/-- **THE DIAGONAL FLOOR: `|S|^r ≤ q·W_r` for even `r` on a negation-closed `S`.**

The even-order signed identity `q·W_r − |S|^r = ∑_{ψ≠0} η_ψ^r ≥ 0` (nonnegative because each `η_ψ` is
real on a negation-closed `S`, so `η_ψ^r ≥ 0` at even `r`) forces the diagonal lower bound
`W_r ≥ |S|^r / q`. This is the MATCHING FLOOR to the in-tree Johnson UPPER cap `W_r ≤ (2r−1)!!·|S|^r`.
Thinness-essential: it consumes `−1 ∈ S` (negation-closure). -/
theorem zeroSumCount_ge_diagonal {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) {r : ℕ} (hr : Even r) :
    (S.card : ℝ) ^ r
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card := by
  -- the nonzero signed sum is ≥ 0 (real) and equals q·W_r − |S|^r (complex identity, take re)
  have hid : (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r := nonzeroSignedPeriodPow_eq S r
  obtain ⟨heq, hnn⟩ := nonzeroSignedPeriodPow_even_nonneg (S := S) hS hr
  -- the LHS of hid is a nonnegative real; its real part is the nonneg sum
  have hre : (0 : ℝ) ≤
      ((Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r).re := by
    rw [← hid, heq, Complex.ofReal_re]; exact hnn
  -- compute that real part: q·W − |S|^r (all real coercions)
  have hcompute :
      ((Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r).re
      = (Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r := by
    have h1 : ((Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card)
        = (((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((S.card : ℂ) ^ r) = (((S.card : ℝ) ^ r : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [hcompute] at hre
  linarith

/-- **THE PERIOD-MAX LOWER BOUND: `q·W_r − |S|^r ≤ (q−1)·M^r` for even `r`.**

Companion floor on the period max. For even `r` and negation-closed `S`, each `η_ψ^r = ‖η_ψ‖^r`
(reality ⟹ `η_ψ^r = (η_ψ.re)^r = |η_ψ.re|^r = ‖η_ψ‖^r`), so if `‖η_ψ‖ ≤ M` for every nonzero
character `ψ`, then `∑_{ψ≠0} η_ψ^r ≤ (q−1)·M^r`. Combined with the signed identity
`∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r` this gives the LOWER bound on `M^r`:
`q·W_r − |S|^r ≤ (q−1)·M^r`. The prize wants an UPPER bound on `M`, so this is the opposite
direction — a floor, NOT a CORE bound (honest scope). -/
theorem signedPeriodPow_le_card_mul_max_pow {S : Finset F}
    (hS : ∀ x ∈ S, -x ∈ S) {r : ℕ} (hr : Even r) {M : ℝ}
    (hM : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)), ‖∑ x ∈ S, ψ x‖ ≤ M) :
    (Fintype.card F : ℝ)
        * ((Fintype.piFinset (fun _ : Fin r => S)).filter
            (fun t => ∑ i, t i = 0)).card
      - (S.card : ℝ) ^ r
    ≤ ((univ.erase (0 : AddChar F ℂ)).card : ℝ) * M ^ r := by
  -- 0 ≤ M (some norm ≤ M, norms are ≥ 0); and each real summand (η_ψ.re)^r ≤ M^r
  obtain ⟨heq, hnn⟩ := nonzeroSignedPeriodPow_even_nonneg (S := S) hS hr
  -- the signed identity (complex), take real parts
  have hid : (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r := nonzeroSignedPeriodPow_eq S r
  -- real-part computation of the RHS of hid
  have hcompute :
      ((Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r).re
      = (Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r := by
    have h1 : ((Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card)
        = (((Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((S.card : ℂ) ^ r) = (((S.card : ℝ) ^ r : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  -- the signed sum (as a real number) equals q·W − |S|^r
  have hsum_eq : (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x).re ^ r)
      = (Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r := by
    have := congrArg Complex.re hid
    rw [heq, Complex.ofReal_re, hcompute] at this
    exact this
  -- each summand (η_ψ.re)^r ≤ M^r
  have hbound : ∀ ψ ∈ (univ.erase (0 : AddChar F ℂ)),
      (∑ x ∈ S, ψ x).re ^ r ≤ M ^ r := by
    intro ψ hψ
    -- (η_ψ.re)^r = ‖η_ψ‖^r (reality), and ‖η_ψ‖ ≤ M
    have hreal : ‖∑ x ∈ S, ψ x‖ = |(∑ x ∈ S, ψ x).re| := by
      have him : (∑ x ∈ S, ψ x).im = 0 := period_im_eq_zero hS
      rw [Complex.norm_def, Complex.normSq_apply, him, mul_zero, add_zero,
        ← Real.sqrt_sq_eq_abs, sq]
    have hpow : (∑ x ∈ S, ψ x).re ^ r = ‖∑ x ∈ S, ψ x‖ ^ r := by
      rw [hreal, ← abs_pow, abs_of_nonneg (hr.pow_nonneg _)]
    rw [hpow]
    have hnnnorm : (0 : ℝ) ≤ ‖∑ x ∈ S, ψ x‖ := norm_nonneg _
    exact pow_le_pow_left₀ hnnnorm (hM ψ hψ) r
  -- sum ≤ (q−1)·M^r
  calc (Fintype.card F : ℝ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℝ) ^ r
      = ∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x).re ^ r := hsum_eq.symm
    _ ≤ ∑ _ψ ∈ (univ.erase (0 : AddChar F ℂ)), M ^ r :=
        Finset.sum_le_sum hbound
    _ = ((univ.erase (0 : AddChar F ℂ)).card : ℝ) * M ^ r := by
        rw [Finset.sum_const, nsmul_eq_mul]

-- Axiom audit (full-env `lean` confirms ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms zeroSumCount_ge_diagonal
#print axioms signedPeriodPow_le_card_mul_max_pow
#print axioms nonzeroSignedPeriodPow_even_nonneg
#print axioms period_conj_eq_self

end ArkLib.ProximityGap.SignedPeriodPowerEvenFloor
