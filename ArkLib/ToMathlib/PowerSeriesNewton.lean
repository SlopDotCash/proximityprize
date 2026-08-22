/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.ToMathlib.PowerSeriesHenselianA

/-!
# Constructive Newton / Hensel iteration over `k⟦X⟧`

`Mathlib`'s `HenselianLocalRing` machinery (used in `PowerSeriesHenselianA.lean` to
lift a simple root of a polynomial over `k⟦X⟧`) only gives a *non-constructive*
existence statement for the lifted root.  The BCIKS20 Appendix-A.4 argument, however,
needs an *explicit recursive sequence* whose coefficient degrees can be tracked.

This file builds exactly that.  Given a polynomial `f : (k⟦X⟧)[Y]`, an approximate
root `a₀` with `f(a₀) ≡ 0 mod X` and `f'(a₀)` a unit, we define the **Newton sequence**

  `a 0     = a₀`
  `a (n+1) = a n - f(a n) · (f'(a n))⁻¹`     (`⁻¹ = Ring.inverse`).

We prove

* `newtonSeq_deriv_isUnit` : `f'(a n)` is a unit for every `n`;
* `newtonSeq_quadratic`    : `X ^ (2 ^ n) ∣ f(a n)` (**quadratic** convergence);
* `newtonSeq_step_dvd`     : `X ^ (2 ^ n) ∣ a (n+1) - a n` (Cauchy / coherence);
* `newtonSeq_isCoherent`   : the truncations form a coherent (`SModEq`) sequence;
* `newtonSeq_limit`        : an explicit `X`-adic limit `a∞` with `f(a∞) = 0` and
  `a∞ - a₀ ∈ Ideal.span {X}`;
* `powerSeries_newton_root`: the constructive analogue of `powerSeries_hensel_lift`.

Everything is kernel-clean (reusing `ArkLib.powerSeries_isPrecomplete` from
`PowerSeriesHenselianA.lean` for the limit).
-/

set_option linter.style.longLine false

open PowerSeries

namespace ArkLib

variable {k : Type*} [Field k]

/-! ### The Newton step -/

/-- One Newton step: `step f a = a - f(a) · (f'(a))⁻¹`. -/
noncomputable def newtonStep (f : Polynomial (PowerSeries k)) (a : PowerSeries k) :
    PowerSeries k :=
  a - f.eval a * Ring.inverse (f.derivative.eval a)

/-- The Newton sequence with seed `a₀`. -/
noncomputable def newtonSeq (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k) :
    ℕ → PowerSeries k
  | 0 => a₀
  | n + 1 => newtonStep f (newtonSeq f a₀ n)

@[simp] theorem newtonSeq_zero (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k) :
    newtonSeq f a₀ 0 = a₀ := rfl

@[simp] theorem newtonSeq_succ (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k) (n : ℕ) :
    newtonSeq f a₀ (n + 1) = newtonStep f (newtonSeq f a₀ n) := rfl

/-! ### Stability of evaluation modulo `X` -/

/-- If `X ∣ a - b` then `X` divides the difference of evaluations. -/
theorem X_dvd_eval_sub (p : Polynomial (PowerSeries k)) {a b : PowerSeries k}
    (h : (X : PowerSeries k) ∣ (a - b)) : (X : PowerSeries k) ∣ (p.eval a - p.eval b) :=
  dvd_trans h (Polynomial.sub_dvd_eval_sub a b p)

/-- The constant coefficient of `p.eval` is invariant under congruence mod `X`. -/
theorem constantCoeff_eval_eq (p : Polynomial (PowerSeries k)) {a b : PowerSeries k}
    (h : (X : PowerSeries k) ∣ (a - b)) :
    constantCoeff (R := k) (p.eval a) = constantCoeff (R := k) (p.eval b) := by
  have hd : (X : PowerSeries k) ∣ (p.eval a - p.eval b) := X_dvd_eval_sub p h
  rw [X_dvd_iff, map_sub, sub_eq_zero] at hd
  exact hd

/-- Being a unit at `a` is preserved by congruence mod `X`. -/
theorem isUnit_eval_of_X_dvd (p : Polynomial (PowerSeries k)) {a b : PowerSeries k}
    (h : (X : PowerSeries k) ∣ (a - b)) (hu : IsUnit (p.eval a)) : IsUnit (p.eval b) := by
  rw [isUnit_iff_constantCoeff] at hu ⊢
  rwa [← constantCoeff_eval_eq p h]

/-- `φ ∈ (span {X})^n • ⊤ ↔ X^n ∣ φ` (the membership consumed by `IsPrecomplete`). -/
private theorem mem_span_X_pow_smul_top' (n : ℕ) (φ : PowerSeries k) :
    φ ∈ (Ideal.span {(X : PowerSeries k)}) ^ n • (⊤ : Submodule (PowerSeries k) (PowerSeries k))
      ↔ (X : PowerSeries k) ^ n ∣ φ := by
  have hsmul : φ ∈ (Ideal.span {(X : PowerSeries k)}) ^ n •
      (⊤ : Submodule (PowerSeries k) (PowerSeries k))
      ↔ φ ∈ ((Ideal.span {(X : PowerSeries k)}) ^ n : Ideal (PowerSeries k)) := by
    simp
  rw [hsmul, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-! ### The quadratic divisibility for one step -/

/-- **Core Newton estimate.** If `f'(a)` is a unit then `f(a)² ∣ f(step a)`.
This is the algebraic heart of quadratic convergence: by Taylor expansion
`f(a + h) = f(a) + f'(a)·h + c·h²` with `h = -f(a)·(f'(a))⁻¹`, the first-order term
cancels `f(a)` exactly, leaving a multiple of `f(a)²`. -/
theorem newtonStep_sq_dvd (f : Polynomial (PowerSeries k)) (a : PowerSeries k)
    (hu : IsUnit (f.derivative.eval a)) :
    (f.eval a) ^ 2 ∣ f.eval (newtonStep f a) := by
  set u := Ring.inverse (f.derivative.eval a) with hu_def
  set g := f.eval a with hg_def
  set g' := f.derivative.eval a with hg'_def
  obtain ⟨c, hc⟩ := f.binomExpansion a (-(g * u))
  have key : a + -(g * u) = newtonStep f a := by
    simp only [newtonStep, ← hg_def]; ring
  rw [key] at hc
  rw [hc]
  have hgu : g' * u = 1 := Ring.mul_inverse_cancel g' hu
  have expand : g + g' * (-(g * u)) + c * (-(g * u)) ^ 2 = c * u ^ 2 * g ^ 2 := by
    linear_combination (-g) * hgu
  rw [expand]
  exact Dvd.intro_left _ rfl

/-! ### Properties of the Newton sequence -/

/-- The seed satisfies `X ∣ f(a₀)`. -/
theorem newtonSeq_base_dvd (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0) :
    (X : PowerSeries k) ^ (2 ^ 0) ∣ f.eval (newtonSeq f a₀ 0) := by
  have : (X : PowerSeries k) ^ (2 ^ 0) = X := by norm_num
  rw [newtonSeq_zero, this, X_dvd_iff]
  exact h₁

/-- The combined invariant maintained along the Newton sequence:
the derivative stays a unit **and** `X ^ (2 ^ n) ∣ f(aₙ)`.
These two facts are mutually dependent (the divisibility uses the unit to take a
Newton step; the unit is preserved because the step moves `aₙ` by a multiple of `X`,
which needs `X ∣ f(aₙ)`), so we prove them together by a single induction. -/
theorem newtonSeq_invariant (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) (n : ℕ) :
    IsUnit (f.derivative.eval (newtonSeq f a₀ n)) ∧
      (X : PowerSeries k) ^ (2 ^ n) ∣ f.eval (newtonSeq f a₀ n) := by
  induction n with
  | zero => exact ⟨by simpa using h₂, newtonSeq_base_dvd f a₀ h₁⟩
  | succ n ih =>
    obtain ⟨hun, hdvdn⟩ := ih
    -- The unit is preserved: `step aₙ - aₙ = -f(aₙ)·u`, divisible by `X` since `X ∣ f(aₙ)`.
    have hgdvd : (X : PowerSeries k) ∣ f.eval (newtonSeq f a₀ n) :=
      dvd_trans (dvd_pow_self X (n := 2 ^ n) (by positivity)) hdvdn
    have hstep : (X : PowerSeries k) ∣ (newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n) := by
      have : newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n
          = -(f.eval (newtonSeq f a₀ n) * Ring.inverse (f.derivative.eval (newtonSeq f a₀ n))) := by
        simp only [newtonSeq_succ, newtonStep]; ring
      rw [this]
      exact (Dvd.dvd.mul_right hgdvd _).neg_right
    have hstep' : (X : PowerSeries k) ∣ (newtonSeq f a₀ n - newtonSeq f a₀ (n + 1)) := by
      have := hstep.neg_right
      rwa [neg_sub] at this
    refine ⟨isUnit_eval_of_X_dvd f.derivative hstep' hun, ?_⟩
    -- Quadratic step: `(f aₙ)² ∣ f a_{n+1}` and `X^{2^n}|f aₙ` ⇒ `X^{2^{n+1}} ∣ f a_{n+1}`.
    have hsq : (f.eval (newtonSeq f a₀ n)) ^ 2 ∣ f.eval (newtonSeq f a₀ (n + 1)) := by
      rw [newtonSeq_succ]; exact newtonStep_sq_dvd f (newtonSeq f a₀ n) hun
    refine dvd_trans ?_ hsq
    have hpow : ((X : PowerSeries k) ^ (2 ^ n)) ^ 2 ∣ (f.eval (newtonSeq f a₀ n)) ^ 2 :=
      pow_dvd_pow_of_dvd hdvdn 2
    have heq : ((X : PowerSeries k) ^ (2 ^ n)) ^ 2 = (X : PowerSeries k) ^ (2 ^ (n + 1)) := by
      rw [← pow_mul]; ring_nf
    rwa [heq] at hpow

/-- The derivative stays a unit along the whole Newton sequence. -/
theorem newtonSeq_deriv_isUnit (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) (n : ℕ) :
    IsUnit (f.derivative.eval (newtonSeq f a₀ n)) :=
  (newtonSeq_invariant f a₀ h₁ h₂ n).1

/-- **Quadratic convergence**: `X ^ (2 ^ n) ∣ f(aₙ)`. -/
theorem newtonSeq_quadratic (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) (n : ℕ) :
    (X : PowerSeries k) ^ (2 ^ n) ∣ f.eval (newtonSeq f a₀ n) :=
  (newtonSeq_invariant f a₀ h₁ h₂ n).2

/-- Consecutive iterates agree modulo an increasing power of `X`:
`X ^ (2 ^ n) ∣ a (n+1) - a n`. -/
theorem newtonSeq_step_dvd (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) (n : ℕ) :
    (X : PowerSeries k) ^ (2 ^ n) ∣ (newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n) := by
  have hdvd : (X : PowerSeries k) ^ (2 ^ n) ∣ f.eval (newtonSeq f a₀ n) :=
    newtonSeq_quadratic f a₀ h₁ h₂ n
  have : newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n
      = -(f.eval (newtonSeq f a₀ n) * Ring.inverse (f.derivative.eval (newtonSeq f a₀ n))) := by
    simp only [newtonSeq_succ, newtonStep]; ring
  rw [this]
  exact (Dvd.dvd.mul_right hdvd _).neg_right

/-! ### The `X`-adic limit -/

/-- Any iterate is congruent to `a₀` modulo `X`: `X ∣ a n - a₀`. -/
theorem newtonSeq_sub_base_dvd (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) (n : ℕ) :
    (X : PowerSeries k) ∣ (newtonSeq f a₀ n - a₀) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (X : PowerSeries k) ∣ (newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n) := by
      refine dvd_trans ?_ (newtonSeq_step_dvd f a₀ h₁ h₂ n)
      exact dvd_pow_self X (n := 2 ^ n) (by positivity)
    have : newtonSeq f a₀ (n + 1) - a₀
        = (newtonSeq f a₀ (n + 1) - newtonSeq f a₀ n) + (newtonSeq f a₀ n - a₀) := by ring
    rw [this]; exact dvd_add hstep ih

/-- For `p ≤ q`, `X ^ (2 ^ p) ∣ a q - a p`: the tail of the sequence is captured to
high `X`-adic precision. -/
theorem newtonSeq_dvd_of_le (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) {p q : ℕ} (hpq : p ≤ q) :
    (X : PowerSeries k) ^ (2 ^ p) ∣ (newtonSeq f a₀ q - newtonSeq f a₀ p) := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    have hstep : (X : PowerSeries k) ^ (2 ^ p) ∣ (newtonSeq f a₀ (q + 1) - newtonSeq f a₀ q) := by
      refine dvd_trans ?_ (newtonSeq_step_dvd f a₀ h₁ h₂ q)
      exact pow_dvd_pow X (Nat.pow_le_pow_right (by norm_num) hpq)
    have : newtonSeq f a₀ (q + 1) - newtonSeq f a₀ p
        = (newtonSeq f a₀ (q + 1) - newtonSeq f a₀ q) + (newtonSeq f a₀ q - newtonSeq f a₀ p) := by
      ring
    rw [this]; exact dvd_add hstep ih

/-- The Newton sequence is `(X)`-adically coherent (a Cauchy / `SModEq` chain).
We use the coarse modulus `X ^ p ∣ a q - a p`, which is implied by the sharp
quadratic estimate and is exactly what `IsPrecomplete` consumes. -/
theorem newtonSeq_isCoherent (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∀ {p q : ℕ}, p ≤ q →
      newtonSeq f a₀ p ≡ newtonSeq f a₀ q
        [SMOD (Ideal.span {(X : PowerSeries k)}) ^ p • (⊤ : Submodule (PowerSeries k) (PowerSeries k))] := by
  intro p q hpq
  rw [SModEq.sub_mem]
  have hmem : newtonSeq f a₀ p - newtonSeq f a₀ q ∈
      ((Ideal.span {(X : PowerSeries k)}) ^ p : Ideal (PowerSeries k)) := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have hdvd : (X : PowerSeries k) ^ (2 ^ p) ∣ (newtonSeq f a₀ q - newtonSeq f a₀ p) :=
      newtonSeq_dvd_of_le f a₀ h₁ h₂ hpq
    have hle : (X : PowerSeries k) ^ p ∣ (X : PowerSeries k) ^ (2 ^ p) :=
      pow_dvd_pow X (Nat.le_of_lt (Nat.lt_two_pow_self))
    have := dvd_trans hle hdvd
    rw [show newtonSeq f a₀ p - newtonSeq f a₀ q = -(newtonSeq f a₀ q - newtonSeq f a₀ p) by ring]
    exact this.neg_right
  simpa using hmem

/-- **The constructive limit of the Newton sequence.** There is an explicit power
series `a∞` (the `X`-adic limit of `newtonSeq f a₀`) which is an exact root of `f`
and congruent to `a₀` modulo `X`.  The limit is produced by the precompleteness
instance `ArkLib.powerSeries_isPrecomplete`, applied to the coherent Newton chain. -/
theorem newtonSeq_limit (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : constantCoeff (R := k) (f.eval a₀) = 0)
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ aInf : PowerSeries k, f.IsRoot aInf ∧
      aInf - a₀ ∈ Ideal.span {(X : PowerSeries k)} := by
  -- Coherent sequence to feed to precompleteness.
  obtain ⟨aInf, haInf⟩ := (powerSeries_isPrecomplete (k := k)).prec' (newtonSeq f a₀)
    (fun {p q} hpq => newtonSeq_isCoherent f a₀ h₁ h₂ hpq)
  -- `haInf n : newtonSeq f a₀ n ≡ aInf [SMOD I^n • ⊤]`.
  refine ⟨aInf, ?_, ?_⟩
  · -- `f.eval aInf = 0`: show all of its coefficients vanish.
    rw [Polynomial.IsRoot.def]
    ext m
    rw [map_zero]
    -- Pick a stage `N` with `2 ^ N > m` so that `X ^ (2 ^ N) ∣ f(a_N)`, and
    -- `a_N ≡ aInf` to precision `X ^ (N+1)`, hence `f(a_N) ≡ f(aInf)` to that precision.
    -- It is enough to take `N = m + 1` (so `2^N ≥ N+1 > m` and `N+1 > m`).
    set N := m + 1 with hN
    -- `aInf - a_N` divisible by `X^N` (from coherence at index `N`).
    have hdiff : (X : PowerSeries k) ^ N ∣ (aInf - newtonSeq f a₀ N) := by
      have h := haInf N
      rw [SModEq.sub_mem, mem_span_X_pow_smul_top'] at h
      simpa [sub_eq_neg_add] using h.neg_right
    -- `f(aInf) - f(a_N)` divisible by `X^N`.
    have hfdiff : (X : PowerSeries k) ^ N ∣ (f.eval aInf - f.eval (newtonSeq f a₀ N)) := by
      have hbase : (X : PowerSeries k) ∣ (aInf - newtonSeq f a₀ N) :=
        dvd_trans (dvd_pow_self X (n := N) (by omega)) hdiff
      -- Use Taylor: aInf = a_N + h, f(aInf) - f(a_N) = f'(a_N)·h + c·h².
      -- Each term divisible by X^N.
      set aN := newtonSeq f a₀ N with haN
      obtain ⟨c, hc⟩ := f.binomExpansion aN (aInf - aN)
      have hrw : aN + (aInf - aN) = aInf := by ring
      rw [hrw] at hc
      rw [hc]
      have : f.eval aN + f.derivative.eval aN * (aInf - aN) + c * (aInf - aN) ^ 2 - f.eval aN
          = f.derivative.eval aN * (aInf - aN) + c * (aInf - aN) ^ 2 := by ring
      rw [this]
      refine dvd_add ?_ ?_
      · exact Dvd.dvd.mul_left hdiff _
      · -- `X^N ∣ (aInf - aN) ∣ (aInf - aN)^2`, hence divides `c * (aInf - aN)^2`.
        refine Dvd.dvd.mul_left ?_ _
        exact dvd_trans hdiff (dvd_pow_self (aInf - aN) (two_ne_zero))
    -- `X^(2^N) ∣ f(a_N)`, and `2^N > m` so coeff m (f a_N) = 0.
    have hfaN : (X : PowerSeries k) ^ (2 ^ N) ∣ f.eval (newtonSeq f a₀ N) :=
      newtonSeq_quadratic f a₀ h₁ h₂ N
    -- combine: X^N ∣ f(aInf) since X^N ∣ f(a_N) (as N ≤ 2^N) and X^N ∣ f(aInf) - f(a_N).
    have hfaN' : (X : PowerSeries k) ^ N ∣ f.eval (newtonSeq f a₀ N) :=
      dvd_trans (pow_dvd_pow X (Nat.le_of_lt Nat.lt_two_pow_self)) hfaN
    have hfaInf : (X : PowerSeries k) ^ N ∣ f.eval aInf := by
      have : f.eval aInf = (f.eval aInf - f.eval (newtonSeq f a₀ N)) + f.eval (newtonSeq f a₀ N) := by
        ring
      rw [this]; exact dvd_add hfdiff hfaN'
    rw [X_pow_dvd_iff] at hfaInf
    exact hfaInf m (by omega)
  · -- `aInf - a₀ ∈ span {X}`.
    rw [Ideal.mem_span_singleton]
    -- `X ∣ aInf - a₁` (coherence at index 1) and `X ∣ a₁ - a₀`.
    have h1 : (X : PowerSeries k) ∣ (aInf - newtonSeq f a₀ 1) := by
      have h := haInf 1
      rw [SModEq.sub_mem, mem_span_X_pow_smul_top'] at h
      have := h.neg_right
      simpa [sub_eq_neg_add, pow_one] using this
    have h2 : (X : PowerSeries k) ∣ (newtonSeq f a₀ 1 - a₀) :=
      newtonSeq_sub_base_dvd f a₀ h₁ h₂ 1
    have : aInf - a₀ = (aInf - newtonSeq f a₀ 1) + (newtonSeq f a₀ 1 - a₀) := by ring
    rw [this]; exact dvd_add h1 h2

/-! ### The constructive Hensel lift -/

/-- **Constructive Newton/Hensel lift in `k⟦X⟧`.**  This matches
`ArkLib.powerSeries_hensel_lift`, but the root is the *explicit* `X`-adic limit of the
recursive Newton sequence `newtonSeq f a₀`, with the quadratic-convergence estimate
`X ^ (2 ^ n) ∣ f(aₙ)` available (`newtonSeq_quadratic`) for degree tracking — exactly
what the BCIKS20 Appendix-A.4 lift needs.

Hypotheses: `f.eval a₀ ≡ 0 mod X` and `f'(a₀)` a unit.  Monicity is **not** required
(unlike the `HenselianLocalRing` route): the unit derivative is what powers the
construction. -/
theorem powerSeries_newton_root (f : Polynomial (PowerSeries k)) (a₀ : PowerSeries k)
    (h₁ : f.eval a₀ ∈ Ideal.span {(X : PowerSeries k)})
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : PowerSeries k, f.IsRoot a ∧
      a - a₀ ∈ Ideal.span {(X : PowerSeries k)} := by
  have h₁' : constantCoeff (R := k) (f.eval a₀) = 0 := by
    rwa [← X_dvd_iff, ← Ideal.mem_span_singleton]
  exact newtonSeq_limit f a₀ h₁' h₂

end ArkLib
