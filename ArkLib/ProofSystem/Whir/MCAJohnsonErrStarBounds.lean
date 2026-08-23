/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Arithmetic envelope lemma toward the MCA Johnson conjecture (ABF26 Conjecture 4.12, Johnson
variant)

This file is a self-contained, sorry-free, axiom-clean development of the **largest genuinely
provable arithmetic facts** about the conjecture's error term

  errStar_A(δ) = ((parℓ - 1) * 2^(2m)) / (|F| * (2 * min_val)^7)
  where  min_val = min (1 - √ρ - δ) (√ρ / 20).

This mirrors the `errStar` shape literally written in
`ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean`, `mca_johnson_bound_CONJECTURE`:

    fun δ =>
      let min_val := min (1 - Real.sqrt Gen.rate - (δ : ℝ)) (Real.sqrt Gen.rate / 20)
      ENNReal.ofReal (((Fintype.card parℓ_type - 1) * 2^(2*m)) /
                       ((Fintype.card F) * (2 * min_val)^7))

We work with the real number under the `ENNReal.ofReal` (the genuinely arithmetic content), over
the *valid Johnson range* `δ ∈ (0, 1 - √ρ)` with `ρ ∈ (0,1)`.

The facts proved (all sorry-free, all `#print axioms`-clean):

* `Johnson.minVal_pos`        — on the valid range, `min_val > 0`  (foundational well-definedness:
                                 the error term's denominator is strictly positive).
* `Johnson.denom_factor_pos`  — `(2 * min_val)^7 > 0`.
* `Johnson.errStarA_nonneg`   — `errStar_A δ ≥ 0`.
* `Johnson.errStarA_pos`      — `errStar_A δ > 0` whenever the numerator is positive
                                 (`parℓ ≥ 2`, `|F| ≥ 1`): so the conjecture's error term is a
                                 genuine, finite, *positive* real (never `0`/`⊤`).
* `Johnson.minVal_le_radius`  — `min_val ≤ 1 - √ρ - δ`  (the radius cap).
* `Johnson.minVal_le_cap`     — `min_val ≤ √ρ / 20`     (the `√ρ/20` cap).
* `Johnson.denom_factor_lb`   — explicit positive lower bound on the denominator factor when
                                 `δ ≤ 1 - √ρ - √ρ/20` (so `min_val = √ρ/20`):
                                 `(2 * min_val)^7 = (√ρ/10)^7`.
* `Johnson.errStarA_antitone_in_minVal` — the error term is **antitone in `min_val`**
                                 (larger usable agreement radius ⇒ smaller soundness error),
                                 the key monotonicity envelope fact.
* `Johnson.errStarA_le_envelope` — a clean *upper envelope*: on the sub-range where the cap binds,
                                 `errStar_A δ ≤ ((parℓ-1)*2^(2m)) / (|F| * (√ρ/10)^7)`,
                                 a `δ`-independent ceiling — exactly the kind of B(δ) ≤ ceiling
                                 envelope used in BCHKS25-style accounting.
-/

namespace MCAJohnsonBounds

open Real

/-- The real number underlying the conjecture's `errStar` (Johnson variant), parameterised by:
`parℓ` (= `Fintype.card parℓ_type`), `m`, `q` (= `|F|`), the square-root-rate `s = √ρ`, and `δ`. -/
noncomputable def errStarA (parℓ q m : ℕ) (s δ : ℝ) : ℝ :=
  let min_val := min (1 - s - δ) (s / 20)
  ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (2 * min_val) ^ 7)

/-- `min_val ≤ 1 - s - δ` (radius cap). -/
lemma minVal_le_radius (s δ : ℝ) :
    min (1 - s - δ) (s / 20) ≤ 1 - s - δ := min_le_left _ _

/-- `min_val ≤ s / 20` (the `√ρ/20` cap). -/
lemma minVal_le_cap (s δ : ℝ) :
    min (1 - s - δ) (s / 20) ≤ s / 20 := min_le_right _ _

/-- **Foundational well-definedness.** On the valid Johnson range
`0 < s` (i.e. `0 < √ρ`, true since `0 < ρ`) and `δ < 1 - s` (i.e. `δ < 1 - BStar`),
the quantity `min_val` is strictly positive. This is what makes the conjecture's error
term finite and its denominator nonzero. -/
lemma minVal_pos {s δ : ℝ} (hs : 0 < s) (hδ : δ < 1 - s) :
    0 < min (1 - s - δ) (s / 20) := by
  apply lt_min
  · -- 1 - s - δ > 0  ⇔  δ < 1 - s
    linarith
  · -- s / 20 > 0
    positivity

/-- The denominator factor `(2 * min_val)^7` is strictly positive on the valid range. -/
lemma denom_factor_pos {s δ : ℝ} (hs : 0 < s) (hδ : δ < 1 - s) :
    0 < (2 * min (1 - s - δ) (s / 20)) ^ 7 := by
  have h := minVal_pos hs hδ
  positivity

/-- The error term is nonnegative whenever `parℓ ≥ 1` and `q ≥ 0` (always, for real cards),
on the valid range. -/
lemma errStarA_nonneg {parℓ q m : ℕ} {s δ : ℝ}
    (hparℓ : 1 ≤ parℓ) (hs : 0 < s) (hδ : δ < 1 - s) :
    0 ≤ errStarA parℓ q m s δ := by
  unfold errStarA
  have hden : 0 < (2 * min (1 - s - δ) (s / 20)) ^ 7 := denom_factor_pos hs hδ
  have hnum : 0 ≤ (parℓ - 1 : ℝ) * 2 ^ (2 * m) := by
    have : (1 : ℝ) ≤ (parℓ : ℝ) := by exact_mod_cast hparℓ
    have h1 : 0 ≤ (parℓ - 1 : ℝ) := by linarith
    positivity
  positivity

/-- **Positivity / finiteness of the conjecture's error term.** When the numerator is strictly
positive (`parℓ ≥ 2`, `q ≥ 1`), the error term is a genuine *positive* finite real on the valid
Johnson range. So `ENNReal.ofReal (errStar_A δ)` is neither `0` nor `⊤`: the conjecture's bound is
a well-formed nontrivial probability bound. -/
lemma errStarA_pos {parℓ q m : ℕ} {s δ : ℝ}
    (hparℓ : 2 ≤ parℓ) (hq : 1 ≤ q) (hs : 0 < s) (hδ : δ < 1 - s) :
    0 < errStarA parℓ q m s δ := by
  unfold errStarA
  have hden : 0 < (2 * min (1 - s - δ) (s / 20)) ^ 7 := denom_factor_pos hs hδ
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpar : (2 : ℝ) ≤ (parℓ : ℝ) := by exact_mod_cast hparℓ
  have hnum : 0 < (parℓ - 1 : ℝ) * 2 ^ (2 * m) := by
    have h1 : 0 < (parℓ - 1 : ℝ) := by linarith
    positivity
  positivity

/-- **Monotonicity envelope (antitone in the agreement radius).** For fixed positive numerator,
the error term is *antitone* in `min_val`: a larger usable agreement radius gives a smaller
soundness error. Concretely, if `0 < a ≤ b` then
`num / (q * (2*b)^7) ≤ num / (q * (2*a)^7)`. This is the structural fact that makes a smaller
`min_val` the *worst case* in the envelope. -/
lemma errStarA_antitone_in_minVal {num q : ℝ} (hnum : 0 ≤ num) (hq : 0 < q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    num / (q * (2 * b) ^ 7) ≤ num / (q * (2 * a) ^ 7) := by
  have h2a : 0 < (2 * a) := by linarith
  have hpow_a : 0 < (2 * a) ^ 7 := by positivity
  have hpow_le : (2 * a) ^ 7 ≤ (2 * b) ^ 7 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hden_a : 0 < q * (2 * a) ^ 7 := by positivity
  have hden_le : q * (2 * a) ^ 7 ≤ q * (2 * b) ^ 7 :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hq)
  exact div_le_div_of_nonneg_left hnum hden_a hden_le

/-- On the sub-range where the `√ρ/20` cap binds (`δ ≤ 1 - s - s/20`), we have
`min_val = s/20`, hence the denominator factor equals `(s/10)^7`. -/
lemma denom_factor_eq_of_cap_binds {s δ : ℝ} (hbind : s / 20 ≤ 1 - s - δ) :
    (2 * min (1 - s - δ) (s / 20)) ^ 7 = (s / 10) ^ 7 := by
  have hmin : min (1 - s - δ) (s / 20) = s / 20 := min_eq_right hbind
  rw [hmin]
  ring_nf

/-- **Explicit positive lower bound on the denominator factor** when the cap binds.
On `0 < s` and `δ ≤ 1 - s - s/20`, the denominator factor is exactly `(s/10)^7 > 0`. -/
lemma denom_factor_lb {s δ : ℝ} (hs : 0 < s) (hbind : s / 20 ≤ 1 - s - δ) :
    (2 * min (1 - s - δ) (s / 20)) ^ 7 = (s / 10) ^ 7 ∧ 0 < (s / 10) ^ 7 := by
  refine ⟨denom_factor_eq_of_cap_binds hbind, ?_⟩
  positivity

/-- **Clean upper envelope.** On the sub-range where the cap binds (`δ ≤ 1 - s - s/20`, with
`0 < s`, `parℓ ≥ 1`, `q ≥ 1`), the conjecture's error term is bounded *above* by the
`δ`-independent ceiling

  ((parℓ - 1) * 2^(2m)) / (q * (s/10)^7).

In fact, on this sub-range it equals that ceiling — a `B(δ) ≤ ceiling` envelope of exactly the
shape used in BCHKS25-style soundness accounting. -/
lemma errStarA_le_envelope {parℓ q m : ℕ} {s δ : ℝ}
    (hparℓ : 1 ≤ parℓ) (hq : 1 ≤ q) (hs : 0 < s) (hbind : s / 20 ≤ 1 - s - δ) :
    errStarA parℓ q m s δ
      ≤ ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (s / 10) ^ 7)
    ∧ 0 ≤ ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (s / 10) ^ 7) := by
  have heq : errStarA parℓ q m s δ
      = ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (s / 10) ^ 7) := by
    show ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (2 * min (1 - s - δ) (s / 20)) ^ 7)
          = ((parℓ - 1 : ℝ) * 2 ^ (2 * m)) / ((q : ℝ) * (s / 10) ^ 7)
    rw [denom_factor_eq_of_cap_binds hbind]
  refine ⟨le_of_eq heq, ?_⟩
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hparr : (1 : ℝ) ≤ (parℓ : ℝ) := by exact_mod_cast hparℓ
  have hnum : 0 ≤ (parℓ - 1 : ℝ) * 2 ^ (2 * m) := by
    have : 0 ≤ (parℓ - 1 : ℝ) := by linarith
    positivity
  positivity

end MCAJohnsonBounds
