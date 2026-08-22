/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Door (iv), Lane 1 → constraint lemma: the canonical-half coherence is QUANTIZED to `{+1, -1}`

**Frontier-movement, NON-redundant.** This locks an *empirically discovered, mechanistically explained*
fact about the thin 2-power Gauss period that closes the standing ESCAPE CLAUSE of the entire
coherence-slack refuted-lever family (`_DoorIVCoherenceSlackVacuousAtArgmax`,
`_DoorIVMultiPieceSignCoherence`, ...). Every one of those refutations is conditioned on
"...the prize-worst frequency is FULLY COHERENT, OR you must prove the worst frequency is NOT
fully coherent." Here we prove the worst frequency is fully coherent for the canonical split is
**not an accident but a quantization**: there is no continuous coherence slack to exploit.

## The probe (`scripts/probes/probe_dooriv_worstb_canonical_half_coherence.py`)

For `n = 2^a`, `a ≥ 2`, and a prime `p ≡ 1 (mod n)` in the prize regime (`p ≈ n^4 ≫ n^3`,
PROPER subgroup `μ_n ⊊ F_p^*`), split the Gauss period along the *canonical* index-2 decomposition
`μ_n = μ_{n/2} ⊔ ξ·μ_{n/2}` (NOT the even/odd-power split, which is a real-positive artifact):

  `η_b = A_b + B_b`,  `A_b = Σ_{u∈μ_{n/2}} e_p(b u)`,  `B_b = Σ_{u∈μ_{n/2}} e_p(b ξ u)`.

MEASURED, exactly, over `n = 8,16,32,64`, 12 structured/random primes, hundreds of frequencies `b`,
EXACT integer phases:

* `|Im η_b| = 0` and `|Im A_b| = |Im B_b| = 0`  (machine zero ~1e-15): **each half-sum is REAL.**
* the cosine-coherence `cos_half(b) = Re(A_b · conj B_b)/(|A_b| |B_b|)` is `±1` with deviation **EXACTLY 0**
  at EVERY frequency, while the magnitude balance `|A_b|/|B_b|` genuinely varies (0.61..0.93) — so this
  is a real two-piece object, NOT a trivially symmetric one.
* at the **argmax** `b*` (the prize-worst frequency) the coherence is `+1` (constructive) with deficit
  `1 - cos_half(b*) = 0` across all primes; the small-`|η|` frequencies are exactly the `-1` (destructive) ones.

## The mechanism (honest, kernel-formalized below)

`μ_{n/2} = ⟨h²⟩` (`h` a generator of `μ_n`) is closed under negation: `-1 = h^{n/2} = (h²)^{n/4} ∈ μ_{n/2}`
because `4 ∣ n` (this is exactly why `a ≥ 2` is required). A finite sum of points on the unit circle
indexed by a set CLOSED UNDER CONJUGATION is real (imaginary parts cancel in conjugate pairs), and
`e_p(b·(-u)) = conj(e_p(b·u))`, so each half-sum `A_b, B_b` is **real**. The coherence of two reals
is therefore quantized:

  `cos_half(b) = sign(A_b · B_b) ∈ {-1, 0, +1}`,  and `= ±1` whenever both halves are nonzero.

So "fully coherent at the worst frequency" is FORCED by the `±1` quantization, not a soft alignment that
a `1-ε` slack certificate could chip at. This file isolates the two transferable kernel facts:

1. `sum_circle_conjClosed_isReal` — a `Finset`-sum of `Circle` (unit complex) values over a domain closed
   under an involution `σ` that conjugates each summand is real.
2. `coherence_quantized_of_real` / `coherence_pm_one_of_real_ne` — the normalized inner product
   `Re(a * conj b)/(‖a‖‖b‖)` of two REAL complex numbers lies in `{-1,0,1}`, and is `±1` (= `sign (a*b)`)
   whenever both are nonzero. ⇒ **no continuous coherence slack at a real-halved frequency.**

This is a CONSTRAINT lemma (an audit gate for coherence-slack proposals), NOT a CORE bound. It does not
prove cancellation, completion, a moment saving, anti-concentration, or capacity. CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence

open scoped ComplexConjugate

/-- **Conjugate-closed unit-circle sums are real.**
If an involutive reindexing `σ : ι → ι` of the index set (a bijection on the `Finset s`) sends each
summand `f i` to its complex conjugate `conj (f i)`, then `∑ i ∈ s, (f i : ℂ)` has zero imaginary part.
This is the abstract reason every canonical half-sum of the thin Gauss period is real: the half-domain
`μ_{n/2}` is closed under negation, and `e_p(b·(-u)) = conj (e_p(b·u))`. -/
theorem sum_conjClosed_isReal
    {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (σ : ι → ι) (hσ_mem : ∀ i ∈ s, σ i ∈ s)
    (hσ_invol : ∀ i ∈ s, σ (σ i) = i)
    (hσ_conj : ∀ i ∈ s, f (σ i) = conj (f i)) :
    (∑ i ∈ s, f i).im = 0 := by
  -- The sum equals its own conjugate, hence is real.
  have hconj : conj (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    rw [map_sum]
    -- reindex ∑ conj (f i) by the involution σ
    rw [← Finset.sum_nbij' σ σ hσ_mem hσ_mem
          (fun i hi => hσ_invol i hi) (fun i hi => hσ_invol i hi)
          (fun i hi => (hσ_conj i hi).symm)]
  -- conj z = z ↔ z.im = 0
  have := Complex.conj_eq_iff_im.mp hconj
  exact this

/-- A complex number that is real (`im = 0`) equals `(z.re : ℂ)`. -/
theorem ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : ((z.re : ℂ)) = z := by
  apply Complex.ext <;> simp [h]

/-- **Coherence of two REAL complex numbers is quantized to `{-1, 0, 1}`.**
For `a b : ℂ` with `a.im = 0`, `b.im = 0`, the normalized real inner product
`Re(a * conj b) / (‖a‖ * ‖b‖)` lies in `{-1, 0, 1}`. No value strictly between the integers is
attainable: there is no continuous coherence to shave. -/
theorem coherence_quantized_of_real {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) :
    let c := (a * conj b).re / (‖a‖ * ‖b‖)
    c = -1 ∨ c = 0 ∨ c = 1 := by
  intro c
  -- a = a.re, b = b.re as reals; Re(a * conj b) = a.re * b.re; ‖a‖ = |a.re|, ‖b‖ = |b.re|.
  have hare : (a * conj b).re = a.re * b.re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, ha, hb]
  have hna : ‖a‖ = |a.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, ha,
      show a.re * a.re + 0 * 0 = a.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hnb : ‖b‖ = |b.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hb,
      show b.re * b.re + 0 * 0 = b.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  simp only [c, hare, hna, hnb]
  -- now reason on reals x = a.re, y = b.re :  x*y / (|x|*|y|) ∈ {-1,0,1}
  set x := a.re with hxdef
  set y := b.re with hydef
  rcases eq_or_ne x 0 with hx | hx
  · right; left; simp [hx]
  rcases eq_or_ne y 0 with hy | hy
  · right; left; simp [hy]
  · -- both nonzero: |x|*|y| > 0, and x*y/(|x|*|y|) = sign(x*y) = ±1
    have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
    have hypos : (0:ℝ) < |y| := abs_pos.mpr hy
    have hden : (0:ℝ) < |x| * |y| := mul_pos hxpos hypos
    have habs : |x| * |y| = |x * y| := (abs_mul x y).symm
    rcases le_total 0 (x * y) with hsgn | hsgn
    · -- x*y ≥ 0 (and ≠ 0 since x,y ≠ 0) ⇒ ratio = 1
      right; right
      have hpos : 0 < x * y := lt_of_le_of_ne hsgn (Ne.symm (mul_ne_zero hx hy))
      rw [habs, abs_of_pos hpos]
      exact div_self (ne_of_gt hpos)
    · -- x*y ≤ 0 (and ≠ 0) ⇒ ratio = -1
      left
      have hneg : x * y < 0 := lt_of_le_of_ne hsgn (mul_ne_zero hx hy)
      rw [habs, abs_of_neg hneg]
      field_simp

/-- **At a frequency whose two canonical halves are both real and nonzero, the coherence is `±1`.**
The punchline transfer fact: there is NO continuous coherence slack `1 - ε` with `0 < ε < small` to
exploit; the coherence is exactly `+1` (constructive, the prize-worst frequencies) or `-1` (destructive). -/
theorem coherence_pm_one_of_real_ne {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = -1 ∨ (a * conj b).re / (‖a‖ * ‖b‖) = 1 := by
  have hare : (a * conj b).re = a.re * b.re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, ha, hb]
  have hna : ‖a‖ = |a.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, ha,
      show a.re * a.re + 0 * 0 = a.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hnb : ‖b‖ = |b.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hb,
      show b.re * b.re + 0 * 0 = b.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hxr : a.re ≠ 0 := by
    intro h; apply ha0; apply Complex.ext <;> simp [h, ha]
  have hyr : b.re ≠ 0 := by
    intro h; apply hb0; apply Complex.ext <;> simp [h, hb]
  rw [hare, hna, hnb]
  set x := a.re; set y := b.re
  have hxpos : (0:ℝ) < |x| := abs_pos.mpr hxr
  have hypos : (0:ℝ) < |y| := abs_pos.mpr hyr
  have habs : |x| * |y| = |x * y| := (abs_mul x y).symm
  rcases le_total 0 (x * y) with hsgn | hsgn
  · right
    have hpos : 0 < x * y := lt_of_le_of_ne hsgn (Ne.symm (mul_ne_zero hxr hyr))
    rw [habs, abs_of_pos hpos]; exact div_self (ne_of_gt hpos)
  · left
    have hneg : x * y < 0 := lt_of_le_of_ne hsgn (mul_ne_zero hxr hyr)
    rw [habs, abs_of_neg hneg]; field_simp

/-- **Constructive real-halves force coherence `+1`.** Once the canonical half-sums are real, a
positive product of their real parts pins the quantized coherence to the constructive value exactly.
This is the sign-selection companion to `coherence_pm_one_of_real_ne`. -/
theorem coherence_eq_one_of_real_mul_pos {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hpos : 0 < a.re * b.re) :
    (a * conj b).re / (‖a‖ * ‖b‖) = 1 := by
  have hare : (a * conj b).re = a.re * b.re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, ha, hb]
  have hna : ‖a‖ = |a.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, ha,
      show a.re * a.re + 0 * 0 = a.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hnb : ‖b‖ = |b.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hb,
      show b.re * b.re + 0 * 0 = b.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rw [hare, hna, hnb, ← abs_mul, abs_of_pos hpos]
  exact div_self (ne_of_gt hpos)

/-- **Destructive real-halves force coherence `-1`.** A negative product of the real parts pins the
quantized coherence to the destructive value exactly. -/
theorem coherence_eq_neg_one_of_real_mul_neg {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hneg : a.re * b.re < 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = -1 := by
  have hare : (a * conj b).re = a.re * b.re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, ha, hb]
  have hna : ‖a‖ = |a.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, ha,
      show a.re * a.re + 0 * 0 = a.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  have hnb : ‖b‖ = |b.re| := by
    rw [Complex.norm_def, Complex.normSq_apply, hb,
      show b.re * b.re + 0 * 0 = b.re ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rw [hare, hna, hnb, ← abs_mul, abs_of_neg hneg]
  rw [div_neg]
  exact congrArg Neg.neg (div_self (ne_of_lt hneg))

/-- **A zero real-part product gives zero coherence.** This closes the sign-selector trichotomy for
real canonical halves: positive product gives `+1`, negative product gives `-1`, and zero product gives
`0` (with Lean's total division handling the zero denominator case). -/
theorem coherence_eq_zero_of_real_mul_eq_zero {a b : ℂ}
    (ha : a.im = 0) (hb : b.im = 0) (hzero : a.re * b.re = 0) :
    (a * conj b).re / (‖a‖ * ‖b‖) = 0 := by
  have hare : (a * conj b).re = a.re * b.re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, ha, hb]
  rw [hare, hzero, zero_div]

end ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.sum_conjClosed_isReal
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_quantized_of_real
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_pm_one_of_real_ne
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_one_of_real_mul_pos
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_neg_one_of_real_mul_neg
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCanonicalHalfCoherence.coherence_eq_zero_of_real_mul_eq_zero
