/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fold of the KKH26 quotient stack: fixed point + kill-challenge (#357 R2, quotient-stack side)

Probe `probe_kkh26_fold_transport.py` (commit `65901c199`) found that the KKH26
ceiling construction is a **fold fixed point**, and that the terminal fold has a
unique kill-challenge.  This file is the Lean side of both verdicts, as pure field
algebra (no code/probability machinery needed — the geometric content is pointwise).

The FRI fold at challenge `β` evaluates, at `y = x²`,

    Fold_β(f)(x²) = (f(x) + f(−x))/2 + β · (f(x) − f(−x))/(2x).

The KKH26 stack at parameters `(r, m, w)` is `u₀ = x^{rm}/(x^m − w)`,
`u₁ = 1/(x^m − w)`.

**Fixed-point half (even `m`, refuting K1's strict-shrink).**  For even `m` both
components are *fiber-even* (`f(−x) = f(x)`), so the fold is β-independent and equals
the value itself — which is literally the `(r, m/2, w)` instance evaluated at `x²`:

  * `foldAt_of_even` — fiber-even functions fold to themselves, every `β`;
  * `kkhU0_neg`/`kkhU1_neg` — the stack is fiber-even for even `m` (no hypotheses);
  * `foldAt_kkhU0_even`/`foldAt_kkhU1_even` — `Fold_β(u₀^{(r,2m')})(x) = u₀^{(r,m')}(x²)`,
    same `w`, every `β`.  The ceiling construction transports down the smooth tower
    *unchanged*: it neither improves (K1 refuted) nor degrades.

**Terminal half (`m = 1`, the kill-challenge).**  At `m = 1` fiber-evenness fails and
the fold genuinely depends on `β`:

  * `foldAt_kkhU1_one` — `Fold_β(1/(x − w))(x²) = (w + β)/(x² − w²)`;
  * `foldAt_kkhU1_one_eq_zero_iff` — the fold vanishes **iff `β = −w`**.

So a uniformly random terminal challenge destroys the second row of the bad line with
probability exactly `1/|F|` — the bad family is fold-robust until the last level, and
survives even that except for one challenge.  (This is the precise sense in which
fold-based protocols escape the KKH26 family: a `1/q` lottery, not attrition.)
-/

namespace ProximityGap.Issue357.FoldQuotientStack

variable {F : Type*} [Field F]

/-- The FRI fold of `f` at challenge `β`, evaluated at the fiber `{x, −x}` (the value
assigned to `y = x²`). -/
def foldAt (f : F → F) (β x : F) : F :=
  (f x + f (-x)) / 2 + β * ((f x - f (-x)) / (2 * x))

/-- **Fiber-even functions are fold fixed points, β-independently.**  If
`f(−x) = f(x)` then `Fold_β(f)` at that fiber is `f(x)`, for every challenge `β`
(characteristic ≠ 2). -/
theorem foldAt_of_even {f : F → F} {x : F} (hev : f (-x) = f x)
    (h2 : (2 : F) ≠ 0) (β : F) : foldAt f β x = f x := by
  unfold foldAt
  rw [hev]
  field_simp
  ring

/-- The KKH26 numerator row: `u₀ = x^{rm} / (x^m − w)`. -/
def kkhU0 (w : F) (r m : ℕ) (x : F) : F := x ^ (r * m) / (x ^ m - w)

/-- The KKH26 denominator row: `u₁ = 1 / (x^m − w)`. -/
def kkhU1 (w : F) (m : ℕ) (x : F) : F := 1 / (x ^ m - w)

/-- For even exponent parameter the numerator row is fiber-even (no hypotheses:
`(−x)^{2k} = x^{2k}`). -/
theorem kkhU0_neg (w : F) (r m' : ℕ) (x : F) :
    kkhU0 w r (2 * m') (-x) = kkhU0 w r (2 * m') x := by
  unfold kkhU0
  rw [((even_two_mul m').mul_left r).neg_pow, (even_two_mul m').neg_pow]

/-- For even exponent parameter the denominator row is fiber-even. -/
theorem kkhU1_neg (w : F) (m' : ℕ) (x : F) :
    kkhU1 w (2 * m') (-x) = kkhU1 w (2 * m') x := by
  unfold kkhU1
  rw [(even_two_mul m').neg_pow]

/-- **Fold fixed-point, numerator row.**  For even `m = 2m'`, the fold of the KKH26
numerator row at ANY challenge `β` equals the `(r, m')` instance evaluated at `x²` —
the construction is self-similar down the tower, β-independently. -/
theorem foldAt_kkhU0_even (w : F) (r m' : ℕ) (x β : F) (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU0 w r (2 * m')) β x = kkhU0 w r m' (x ^ 2) := by
  rw [foldAt_of_even (kkhU0_neg w r m' x) h2]
  unfold kkhU0
  rw [show r * (2 * m') = (r * m') * 2 by ring, pow_mul', ← pow_mul x 2 m']

/-- **Fold fixed-point, denominator row.** -/
theorem foldAt_kkhU1_even (w : F) (m' : ℕ) (x β : F) (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU1 w (2 * m')) β x = kkhU1 w m' (x ^ 2) := by
  rw [foldAt_of_even (kkhU1_neg w m' x) h2]
  unfold kkhU1
  rw [← pow_mul x 2 m', mul_comm 2 m', mul_comm m' 2]

/-- **β-independence packaged:** the fold of the even-`m` stack does not see the
challenge at all. -/
theorem foldAt_kkh_even_beta_independent (w : F) (r m' : ℕ) (x β β' : F)
    (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU0 w r (2 * m')) β x = foldAt (kkhU0 w r (2 * m')) β' x ∧
    foldAt (kkhU1 w (2 * m')) β x = foldAt (kkhU1 w (2 * m')) β' x := by
  constructor
  · rw [foldAt_kkhU0_even w r m' x β h2, foldAt_kkhU0_even w r m' x β' h2]
  · rw [foldAt_kkhU1_even w m' x β h2, foldAt_kkhU1_even w m' x β' h2]

/-- **Terminal fold of the denominator row (`m = 1`).**  The fold genuinely mixes:
`Fold_β(1/(x − w))(x²) = (w + β)/(x² − w²)` (denominators nonzero). -/
theorem foldAt_kkhU1_one (w x β : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0)
    (hxw : x - w ≠ 0) (hxw' : x + w ≠ 0) :
    foldAt (kkhU1 w 1) β x = (w + β) / (x ^ 2 - w ^ 2) := by
  unfold foldAt kkhU1
  have hx2w2 : x ^ 2 - w ^ 2 ≠ 0 := by
    have : x ^ 2 - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this]
    exact mul_ne_zero hxw hxw'
  have hneg : -x - w ≠ 0 := by
    intro h
    apply hxw'
    linear_combination -h
  field_simp
  ring

/-- **The kill-challenge.**  The terminal fold of the KKH26 denominator row vanishes
**iff** `β = −w`.  Hence a uniformly random terminal fold challenge destroys the bad
line's second row with probability exactly `1/|F|`; for every other challenge the
folded stack keeps the `1/(y − w²)`-type shape and the construction survives. -/
theorem foldAt_kkhU1_one_eq_zero_iff (w x β : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0)
    (hxw : x - w ≠ 0) (hxw' : x + w ≠ 0) :
    foldAt (kkhU1 w 1) β x = 0 ↔ β = -w := by
  rw [foldAt_kkhU1_one w x β h2 hx hxw hxw']
  have hx2w2 : x ^ 2 - w ^ 2 ≠ 0 := by
    have : x ^ 2 - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this]
    exact mul_ne_zero hxw hxw'
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linear_combination h
    · exact absurd h hx2w2
  · intro h
    left
    rw [h]
    ring

end ProximityGap.Issue357.FoldQuotientStack

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Issue357.FoldQuotientStack.foldAt_kkhU0_even
#print axioms ProximityGap.Issue357.FoldQuotientStack.foldAt_kkhU1_even
#print axioms ProximityGap.Issue357.FoldQuotientStack.foldAt_kkhU1_one_eq_zero_iff
