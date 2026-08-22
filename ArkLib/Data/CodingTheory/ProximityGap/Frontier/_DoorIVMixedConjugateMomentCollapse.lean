/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Door-(iv) Lane-1: the ASYMMETRIC mixed-conjugate moment escape is VACUOUS (#444)

`_DoorIVEvenMomentPhaseVacuity` discharged the *symmetric* even-order phase escape: for the
negation-closed thin subgroup `μ_n`, `η_b` is REAL, so the unmodulated even moment
`E_b[η_b^{2r}]` collapses onto the (refuted) modulus moment `E_b[|η_b|^{2r}] = E_r`.

That left ONE finer escape route the campaign had not explicitly foreclosed: an **asymmetric / mixed
conjugate correlator** — a degree-`2r` functional that distributes the conjugations UNEVENLY across the
monomial, e.g.

    M(a,b) = E_c[ η_c^a · conj(η_c)^b ]   with  a + b = 2r,  a ≠ b.

The hope (the only "different 4-point object" left after the symmetric moment died) is that some
unbalanced split `a ≠ b` — say `η³·conj(η)` (the 3-to-1 functional `T`) — carries arithmetic the
symmetric `η^{2r} = |η|^{2r}` discards. This module proves it does NOT: the entire mixed-conjugate
moment lattice collapses to a SINGLE value, the modulus moment, regardless of the conjugate split.

## Probe verdict (reproducible; `/tmp/probe_mixed_moment_collapse.py`)

Proper thin `μ_n ⊊ F_p^*` (negation-closed, order `n` verified primitive), structured primes
`p = k·n+1 ≈ n^{3.2}`, never `n = q−1`. For every total order `2r ∈ {2,4,6}` and EVERY conjugate split
`(a, 2r−a)`, `a = 0,…,2r`, the averaged mixed correlator `M(a,2r−a)` was measured:

| n  | p      | r=1 E_r | r=2 E_r | r=3 E_r | max |M(a,2r−a) − E_r| over all a |
|----|--------|---------|---------|---------|----------------------------------|
| 8  | 809    | 7.92    | 162.94  | 4795.97 | ≤ 2.4e-12 (FP noise)             |
| 16 | 7121   | 15.96   | 710.80  | 48204.0 | ≤ 3.0e-11                        |
| 32 | 65537  | 31.98   | 3344.0  | 687136. | ≤ 5.1e-10                        |
| 64 | 602689 | 63.99   | 12068.2 | 3.73e6  | ≤ 2.7e-09                        |

`M(a,2r−a) = E_r` EXACTLY for ALL splits `a`, at every tested `n` and order `r`. The max deviation is
floating-point noise and every value is real. **The asymmetric mixed-conjugate moment gives NO new
object at ANY split.**

## Mechanism (the formal content of this file)

`μ_n` is negation-closed, so `η_b` is REAL (proven via `field_real_of_negation_closed` in the companion
even-moment file). For a REAL `z` (`z.im = 0`) and ANY exponents `a, b : ℕ`,

    z^a · conj(z)^b = z^a · z^b = z^(a+b) = (‖z‖)^(a+b),

because `conj z = z` when `z` is real, and a real `z` satisfies `z^(a+b) = (‖z‖ : ℂ)^(a+b)` once `a+b`
is even (the sign is squared away). So EVERY mixed correlator of fixed total even degree equals the
modulus moment of that degree — the refuted energy object. Distributing the conjugates unevenly buys
NOTHING: the conjugation is the identity on the real axis, and an even total power has no phase to carry.

This STRICTLY GENERALISES the even-moment vacuity (the case `b = 0`, or `a = b = r`): now the WHOLE
`(2r+1)`-element conjugate ladder `{M(a,2r−a) : a = 0..2r}` is pinned to one value. The asymmetric
mixed-conjugate door-(iv) escape is therefore vacuous, not merely dead.

This is a **Lane-1 / Lane-3 constraint lemma**. It does NOT discharge CORE; it forecloses the asymmetric
mixed-conjugate higher-order escape in the tetrachotomy. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVMixedConjugateMomentCollapse

open Complex

/-- **Conjugation is the identity on the real axis.** For `z : ℂ` with `z.im = 0`, `conj z = z`. -/
theorem conj_eq_self_of_im_zero (z : ℂ) (hz : z.im = 0) : (starRingEnd ℂ) z = z := by
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im, hz]

/-- **Real even total power equals the modulus power.** For `z : ℂ` with `z.im = 0` and any naturals
`a, b` whose sum is even (`a + b = 2 r`), `z^a · conj(z)^b = (‖z‖ : ℂ)^(a+b)`.

This is the algebraic heart of the *asymmetric* vacuity: the conjugation drops out on the real axis
(`conj z = z`), the two factors merge into `z^(a+b)`, and an even total power of a real `z` is its own
modulus power (the sign is squared away). Hence the conjugate SPLIT `(a,b)` is irrelevant — only the
total degree `a + b` matters, and it lands on the modulus moment. -/
theorem mixed_pow_eq_norm_pow (z : ℂ) (hz : z.im = 0) (a b r : ℕ) (hab : a + b = 2 * r) :
    z ^ a * ((starRingEnd ℂ) z) ^ b = ((‖z‖ : ℝ) : ℂ) ^ (a + b) := by
  -- Step 1: `conj z = z`, so the mixed monomial collapses to `z^(a+b)`.
  have hconj : ((starRingEnd ℂ) z) ^ b = z ^ b := by
    rw [conj_eq_self_of_im_zero z hz]
  have hmerge : z ^ a * ((starRingEnd ℂ) z) ^ b = z ^ (a + b) := by
    rw [hconj, ← pow_add]
  rw [hmerge, hab]
  -- Step 2: even power of a real `z` equals modulus power (sign squared away).
  have hzsq : z ^ 2 = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    have hnorm : (‖z‖ : ℝ) ^ 2 = z.re ^ 2 := by
      have h1 : (‖z‖ : ℝ) ^ 2 = Complex.normSq z := Complex.sq_norm z
      rw [h1, Complex.normSq_apply, hz]; ring
    have hreim : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hz]
    have hL : z ^ 2 = ((z.re : ℝ) : ℂ) ^ 2 := by
      conv_lhs => rw [hreim]
    have hR : ((‖z‖ : ℝ) : ℂ) ^ 2 = ((z.re : ℝ) : ℂ) ^ 2 := by
      have hpc : ((‖z‖ : ℝ) : ℂ) ^ 2 = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hpc, hnorm]; push_cast; ring
    rw [hL, hR]
  calc z ^ (2 * r) = (z ^ 2) ^ r := by rw [pow_mul]
    _ = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ r := by rw [hzsq]
    _ = ((‖z‖ : ℝ) : ℂ) ^ (2 * r) := by rw [pow_mul]

/-- **Mixed-conjugate moment collapse (split-independence, pointwise → averaged).** If every value
`η c` of the period field is real (`(η c).im = 0`, which holds for the negation-closed subgroup `μ_n`),
then for ANY conjugate split `(a, b)` of an even total degree `a + b = 2 r`, the averaged mixed
correlator `Σ_c η_c^a · conj(η_c)^b` equals the modulus moment `Σ_c (‖η_c‖)^(a+b)`.

The right-hand side does NOT depend on the split `(a, b)` — only on the total `a + b`. So the entire
`(2r+1)`-element conjugate ladder `{Σ_c η_c^a · conj(η_c)^{2r−a} : a = 0..2r}` is pinned to the single
modulus / energy value. No asymmetric split carries information the symmetric moment discards. -/
theorem mixedMoment_split_independent
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a b r : ℕ) (hab : a + b = 2 * r) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b
      = ∑ c ∈ s, ((‖η c‖ : ℝ) : ℂ) ^ (a + b) := by
  apply Finset.sum_congr rfl
  intro c hc
  exact mixed_pow_eq_norm_pow (η c) (hreal c hc) a b r hab

/-- **All splits coincide.** For a real-valued field, ANY two conjugate splits `(a₁,b₁)` and `(a₂,b₂)`
of the SAME even total degree (`a₁+b₁ = a₂+b₂ = 2r`) give the SAME averaged mixed correlator. In
particular the asymmetric `3-to-1` functional `Σ η³·conj η` equals the symmetric energy `Σ |η|⁴` equals
the unmodulated `Σ η⁴` — the campaign's measured `T = E₂ = Z₄` identity, now proved split-uniform. -/
theorem mixedMoment_any_two_splits_eq
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a₁ b₁ a₂ b₂ r : ℕ) (h₁ : a₁ + b₁ = 2 * r) (h₂ : a₂ + b₂ = 2 * r) :
    (∑ c ∈ s, (η c) ^ a₁ * ((starRingEnd ℂ) (η c)) ^ b₁)
      = ∑ c ∈ s, (η c) ^ a₂ * ((starRingEnd ℂ) (η c)) ^ b₂ := by
  rw [mixedMoment_split_independent s η hreal a₁ b₁ r h₁,
      mixedMoment_split_independent s η hreal a₂ b₂ r h₂, h₁, h₂]

/-- **The asymmetric mixed moment IS the modulus / energy object (no new object).** Specialised
restatement: the mixed correlator with ANY split equals the refuted modulus even moment
`Σ_c (‖η_c‖)^{2r}`, exhibiting that the asymmetric door-(iv) escape lands on the dead energy lane. -/
theorem mixedMoment_eq_modulusMoment
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a b r : ℕ) (hab : a + b = 2 * r) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b
      = ∑ c ∈ s, ((‖η c‖ : ℝ) : ℂ) ^ (2 * r) := by
  rw [mixedMoment_split_independent s η hreal a b r hab, hab]

/-! ## Full-ladder split-independence (any total degree, even OR odd)

The collapse `z^a·conj(z)^b = (‖z‖)^{a+b}` needs `a+b` even (to square the sign away). But the WEAKER
identity `z^a·conj(z)^b = z^{a+b}` — the conjugation is the identity on the real axis, so the split is
irrelevant — holds at EVERY total degree, even or odd. This pins the mixed-conjugate ladder to a single
value `Σ_c η_c^{a+b}` at every order: even total → the (≥ 0) energy `E_r`, odd total → the SIGNED moment
`A_D = Σ_c η_c^D` (real but sign-sensitive). Probe (`probe_odd_mixed_split.py`, n=8..64) confirmed odd
totals D∈{3,5}: every split collapses to one real signed value (deviation = FP noise). So conjugation is a
complete red herring at ALL orders — no parity of total degree lets an asymmetric split make a new object. -/

/-- **Conjugation is a red herring (any total degree).** For real `z` and ANY exponents `a, b`, the mixed
monomial `z^a·conj(z)^b` equals `z^{a+b}` — the split `(a,b)` is irrelevant, only the total degree matters.
No evenness hypothesis: this is the merge step alone, valid at every order. -/
theorem mixed_pow_eq_total_pow (z : ℂ) (hz : z.im = 0) (a b : ℕ) :
    z ^ a * ((starRingEnd ℂ) z) ^ b = z ^ (a + b) := by
  rw [conj_eq_self_of_im_zero z hz, ← pow_add]

/-- **Full-ladder split-independence (averaged, any total degree).** For a real-valued field and any
split `(a,b)`, the averaged mixed correlator `Σ_c η_c^a·conj(η_c)^b` equals `Σ_c η_c^{a+b}` — depending
ONLY on the total `a+b`, NOT the split, at EVERY total degree (even or odd). Even total lands on the
energy `E_r`; odd total lands on the signed moment `A_{a+b}`. -/
theorem mixedMoment_split_independent_any_degree
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0) (a b : ℕ) :
    ∑ c ∈ s, (η c) ^ a * ((starRingEnd ℂ) (η c)) ^ b = ∑ c ∈ s, (η c) ^ (a + b) := by
  apply Finset.sum_congr rfl
  intro c hc
  exact mixed_pow_eq_total_pow (η c) (hreal c hc) a b

/-- **Any two splits of the same total degree coincide (any parity).** The full-ladder unification: for a
real-valued field, any two conjugate splits with the SAME total degree (`a₁+b₁ = a₂+b₂`, no evenness)
give the same averaged correlator. Subsumes `mixedMoment_any_two_splits_eq` (the even case) and extends
it to ODD totals (the signed moment ladder). -/
theorem mixedMoment_any_two_splits_eq_any_degree
    {β : Type*} (s : Finset β) (η : β → ℂ) (hreal : ∀ c ∈ s, (η c).im = 0)
    (a₁ b₁ a₂ b₂ : ℕ) (h : a₁ + b₁ = a₂ + b₂) :
    (∑ c ∈ s, (η c) ^ a₁ * ((starRingEnd ℂ) (η c)) ^ b₁)
      = ∑ c ∈ s, (η c) ^ a₂ * ((starRingEnd ℂ) (η c)) ^ b₂ := by
  rw [mixedMoment_split_independent_any_degree s η hreal a₁ b₁,
      mixedMoment_split_independent_any_degree s η hreal a₂ b₂, h]

end ArkLib.ProximityGap.Frontier.DoorIVMixedConjugateMomentCollapse
