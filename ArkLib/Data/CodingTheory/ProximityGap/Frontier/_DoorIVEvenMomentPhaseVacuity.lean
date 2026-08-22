/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Door-(iv) Lane-1: the phase-carrying EVEN-order moment escape is VACUOUS (#444)

`_DoorIVFourthMomentEnergyCollapse` showed the period MODULUS 4th moment `E_b|η_b|⁴` collapses to the
additive energy `E₂(μ_n)` — the refuted moment/energy lane. Its closing note left ONE explicit door-(iv)
escape open: *"a surviving crack must be a higher-order functional that does NOT reduce to `E₂` — it must
use the PHASE information that the modulus 4th moment `|η_b|⁴` discards — a 4-point object that is NOT the
additive-quadruple count."*

This module discharges that pointer. The candidate phase-carrying object is the UNMODULATED even moment
`E_b[η_b^{2r}]` (vs the dead modulus moment `E_b[|η_b|^{2r}]`).

## Probe verdict (reproducible; `/tmp/probe_phase4.py`, proper thin `μ_n ⊊ F_p^*`, p ≈ n^{3.2}, never n=q−1)

By character orthogonality over `F_p`, with `S = μ_n`:

* `(1/p) Σ_b |η_b|⁴ = #{(x₁,x₂,x₃,x₄)∈S⁴ : x₁+x₂ = x₃+x₄}`  (`E₂`, modulus, DEAD)
* `(1/p) Σ_b  η_b⁴  = #{(x₁,x₂,x₃,x₄)∈S⁴ : x₁+x₂+x₃+x₄ ≡ 0}`  (`Z₄`, PHASE-carrying)
* `(1/p) Σ_b η_b³ conj η_b = #{x₁+x₂+x₃ = x₄}`  (`T`, mixed)

Measured `Z₄ = E₂ = T` EXACTLY at `n = 8,16,32,64,128`. The phase-carrying moment gives NO new object.

## Mechanism (the formal content of this file)

`μ_n` is **negation-closed**: `n` is even (a 2-power in the prize regime), so the order-`n` multiplicative
subgroup contains the order-2 element `−1`. Hence the involution `x ↦ −x` is a bijection of `μ_n`, pairing
`e_p(b·x)` with its conjugate `e_p(−b·x) = conj e_p(b·x)`. Therefore

    η_b = Σ_{x∈μ_n} e_p(b·x)  is REAL  (its imaginary part cancels in conjugate pairs).

For a REAL complex number `z` (i.e. `z.im = 0`), `z^{2r} = (‖z‖)^{2r}` — *the phase that the modulus
discards is identically ZERO*. So `E_b[η_b^{2r}] = E_b[|η_b|^{2r}]` for every `r`: every even-order
phase-carrying functional collapses onto its (refuted-energy) modulus version. The door-(iv) "go to a
phase-sensitive EVEN-order object" escape is therefore **vacuous, not merely dead** — there is no phase at
even orders to exploit. (Odd orders carry SIGN, not phase; that is the odd/signed object mapped elsewhere.)

This is a **Lane-1 / Lane-3 constraint lemma**. It does NOT discharge CORE; it forecloses the last
explicitly-open higher-order escape route in the tetrachotomy. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVEvenMomentPhaseVacuity

open Complex

/-- **Real numbers carry no phase at any even power.** For `z : ℂ` with `z.im = 0` and any natural `r`,
the unmodulated `2r`-th power equals the modulus `2r`-th power: `z^(2r) = (‖z‖ : ℂ)^(2r)`.

This is the algebraic heart of the vacuity: the "phase the modulus discards" is identically zero on the
real axis, so a phase-carrying even moment of a real-valued field is its own modulus moment. -/
theorem real_even_pow_eq_norm_pow (z : ℂ) (hz : z.im = 0) (r : ℕ) :
    z ^ (2 * r) = ((‖z‖ : ℝ) : ℂ) ^ (2 * r) := by
  -- A real `z` is `±‖z‖`; squaring removes the sign, so even powers agree.
  have hzsq : z ^ 2 = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    -- `‖z‖^2 = normSq z = z.re^2 + z.im^2 = z.re^2`  (using `z.im = 0`)
    have hnorm : (‖z‖ : ℝ) ^ 2 = z.re ^ 2 := by
      have h1 : (‖z‖ : ℝ) ^ 2 = Complex.normSq z := Complex.sq_norm z
      rw [h1, Complex.normSq_apply, hz]; ring
    -- both sides equal `(z.re : ℂ)^2`
    have hreim : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hz]
    have hL : z ^ 2 = ((z.re : ℝ) : ℂ) ^ 2 := by
      conv_lhs => rw [hreim]
    have hR : ((‖z‖ : ℝ) : ℂ) ^ 2 = ((z.re : ℝ) : ℂ) ^ 2 := by
      have : ((‖z‖ : ℝ) : ℂ) ^ 2 = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, hnorm]; push_cast; ring
    rw [hL, hR]
  calc z ^ (2 * r) = (z ^ 2) ^ r := by rw [pow_mul]
    _ = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ r := by rw [hzsq]
    _ = ((‖z‖ : ℝ) : ℂ) ^ (2 * r) := by rw [pow_mul]

/-- **Even-moment phase vacuity (pointwise).** If every value `η b` of the period field is real
(`(η b).im = 0`, which holds for the negation-closed subgroup `μ_n`), then the unmodulated `2r`-th power
of each value equals the modulus `2r`-th power. Consequently the b-AVERAGE of the unmodulated even power
equals the b-average of the modulus even power — the phase-carrying even moment IS the modulus even
moment (the refuted energy object). -/
theorem evenMoment_phase_vacuous
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ b ∈ s, (η b).im = 0) (r : ℕ) :
    ∑ b ∈ s, (η b) ^ (2 * r) = ∑ b ∈ s, ((‖η b‖ : ℝ) : ℂ) ^ (2 * r) := by
  apply Finset.sum_congr rfl
  intro b hb
  exact real_even_pow_eq_norm_pow (η b) (hreal b hb) r

/-- **No new object at even order.** The unmodulated even moment of a real-valued field is literally the
modulus even moment: there is no phase residue to exploit. Stated as the exact equality of the two
averaged functionals (left = phase-carrying candidate, right = refuted modulus/energy object). -/
theorem unmodulated_even_moment_eq_modulus
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ b ∈ s, (η b).im = 0) (r : ℕ) :
    (∑ b ∈ s, (η b) ^ (2 * r)) = (∑ b ∈ s, ((‖η b‖ : ℝ) : ℂ) ^ (2 * r)) :=
  evenMoment_phase_vacuous s η hreal r

/-- **The negation-closure hypothesis discharges reality.** If the field value `η b` is a sum
`Σ_{x∈S} φ b x` over a set `S` carrying an INVOLUTION `neg` (`neg (neg x) = x` on `S`) that maps `S` into
itself, and the summand is conjugate-symmetric under it (`φ b (neg x) = conj (φ b x)`, the additive-
character property `e_p(b·(−x)) = conj e_p(b·x)`), then `η b` is REAL. This packages the source of the
`hreal` hypothesis above so the vacuity is DERIVED from the subgroup's negation-closure, not assumed. -/
theorem field_real_of_negation_closed
    {β γ : Type*} (S : Finset γ) (neg : γ → γ)
    (hbij : ∀ x ∈ S, neg x ∈ S)
    (hinvol : ∀ x ∈ S, neg (neg x) = x)
    (φ : β → γ → ℂ) (b : β)
    (hconj : ∀ x ∈ S, φ b (neg x) = (starRingEnd ℂ) (φ b x)) :
    (∑ x ∈ S, φ b x).im = 0 := by
  -- `Im(Σ φ) = Σ Im(φ)`; pair `x` with `neg x`: `Im(φ (neg x)) = −Im(φ x)`,
  -- so the imaginary-part sum is invariant under the involution while each term negates ⇒ it is `0`.
  have hsum_im : (∑ x ∈ S, φ b x).im = ∑ x ∈ S, (φ b x).im := by
    rw [Complex.im_sum]
  rw [hsum_im]
  -- Reindex `Σ_x Im(φ x)` along the involution `neg`, then rewrite each term with `hconj`.
  have hreindex : (∑ x ∈ S, (φ b x).im) = ∑ x ∈ S, (φ b (neg x)).im := by
    refine (Finset.sum_nbij' neg neg ?_ ?_ ?_ ?_ ?_).symm
    · intro a ha; exact hbij a ha
    · intro a ha; exact hbij a ha
    · intro a ha; exact hinvol a ha
    · intro a ha; exact hinvol a ha
    · intro a _; rfl
  -- Each reindexed term: `Im(φ (neg x)) = Im(conj (φ x)) = -Im(φ x)`.
  have hterm : (∑ x ∈ S, (φ b (neg x)).im) = ∑ x ∈ S, -(φ b x).im := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hconj x hx, Complex.conj_im]
  -- Combine: `Σ Im(φ x) = Σ -Im(φ x) = -Σ Im(φ x)` ⇒ `2 · Σ Im(φ x) = 0` ⇒ `Σ = 0`.
  rw [hterm, Finset.sum_neg_distrib] at hreindex
  linarith [hreindex]

end ArkLib.ProximityGap.Frontier.DoorIVEvenMomentPhaseVacuity
