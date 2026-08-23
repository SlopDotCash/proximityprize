/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The power series ring `k⟦X⟧` is a Henselian local ring

This file supplies the missing completeness instance for the formal power series
ring over a field, and concludes that `k⟦X⟧` is a Henselian local ring.

The main work is `powerSeries_isPrecomplete`: the `X`-adic precompleteness of
`k⟦X⟧`.  The witness limit of a coherent sequence `f : ℕ → k⟦X⟧` is the power
series whose `i`-th coefficient is the (stabilised) `i`-th coefficient of `f (i+1)`.

From precompleteness, together with the Hausdorff instance available for a
Noetherian local ring, we obtain `IsAdicComplete (Ideal.span {X})`, hence
`HenselianRing (k⟦X⟧) (maximalIdeal _)`, and finally `HenselianLocalRing (k⟦X⟧)`.
-/

open PowerSeries

namespace ArkLib

variable {k : Type*} [Field k]

/-- Helper: membership in `(Ideal.span {X})^n • (⊤ : Submodule (k⟦X⟧) (k⟦X⟧))`
is the same as `X^n ∣ ·`. -/
private theorem mem_span_X_pow_smul_top (n : ℕ) (φ : PowerSeries k) :
    φ ∈ (Ideal.span {(X : PowerSeries k)}) ^ n • (⊤ : Submodule (PowerSeries k) (PowerSeries k))
      ↔ (X : PowerSeries k) ^ n ∣ φ := by
  have hsmul : φ ∈ (Ideal.span {(X : PowerSeries k)}) ^ n •
      (⊤ : Submodule (PowerSeries k) (PowerSeries k))
      ↔ φ ∈ ((Ideal.span {(X : PowerSeries k)}) ^ n : Ideal (PowerSeries k)) := by
    simp
  rw [hsmul, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- `k⟦X⟧` is `X`-adically precomplete: every coherent sequence has a limit. -/
theorem powerSeries_isPrecomplete :
    IsPrecomplete (Ideal.span {(PowerSeries.X : PowerSeries k)}) (PowerSeries k) := by
  constructor
  intro f hf
  -- The candidate limit: coefficient `i` is the `i`-th coefficient of `f (i+1)`.
  refine ⟨PowerSeries.mk (fun i => PowerSeries.coeff i (f (i + 1))), ?_⟩
  intro n
  -- Reduce the goal to a divisibility / coefficient statement.
  rw [SModEq.sub_mem, mem_span_X_pow_smul_top, X_pow_dvd_iff]
  intro m hm
  -- We must show `coeff m (f n - L) = 0`, i.e. `coeff m (f n) = coeff m L`.
  rw [map_sub, sub_eq_zero, PowerSeries.coeff_mk]
  -- It suffices to show `coeff m (f n) = coeff m (f (m+1))`, using coherence.
  -- Coherence: for `m + 1 ≤ N`, `f (m+1) ≡ f N [SMOD I^(m+1) • ⊤]`, which gives
  -- agreement of all coefficients of index `< m + 1`, in particular index `m`.
  have key : ∀ {p q : ℕ}, p ≤ q → ∀ {j : ℕ}, j < p →
      PowerSeries.coeff j (f p) = PowerSeries.coeff j (f q) := by
    intro p q hpq j hj
    have h := hf hpq
    rw [SModEq.sub_mem, mem_span_X_pow_smul_top, X_pow_dvd_iff] at h
    have := h j hj
    rw [map_sub, sub_eq_zero] at this
    exact this
  -- `coeff m (f n) = coeff m (f (m+1))`.
  -- Compare both to a common large index `max n (m+1)`.
  have hmn : m < m + 1 := Nat.lt_succ_self m
  have hmltn : m < n := hm
  -- From coherence with `n` and `m+1` both at least `m+1`:
  have e1 : PowerSeries.coeff m (f (m + 1)) = PowerSeries.coeff m (f (max n (m + 1))) :=
    key (le_max_right n (m + 1)) hmn
  have e2 : PowerSeries.coeff m (f n) = PowerSeries.coeff m (f (max n (m + 1))) :=
    key (le_max_left n (m + 1)) hmltn
  rw [e2, e1]

/-- `k⟦X⟧` is `X`-adically complete. -/
instance powerSeries_isAdicComplete_span_X :
    IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries k)}) (PowerSeries k) where
  toIsHausdorff := by
    -- The Hausdorff instance is available for the maximal ideal; rewrite it.
    have h : IsHausdorff (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) :=
      inferInstance
    rwa [PowerSeries.maximalIdeal_eq_span_X] at h
  toIsPrecomplete := powerSeries_isPrecomplete

/-- `k⟦X⟧` is `X`-adically complete with respect to its maximal ideal. -/
instance powerSeries_isAdicComplete_maximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  exact powerSeries_isAdicComplete_span_X

/-- `k⟦X⟧` is a Henselian local ring. -/
instance powerSeries_henselianLocalRing : HenselianLocalRing (PowerSeries k) := by
  -- From adic completeness we get `HenselianRing R (maximalIdeal R)`.
  have hHR : HenselianRing (PowerSeries k) (IsLocalRing.maximalIdeal (PowerSeries k)) :=
    IsAdicComplete.henselianRing (PowerSeries k) (IsLocalRing.maximalIdeal (PowerSeries k))
  constructor
  intro f hf a₀ h₁ h₂
  -- Bridge the simple-root condition: a unit in `R` maps to a unit in the quotient.
  refine hHR.is_henselian f hf a₀ h₁ ?_
  exact h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries k)))

/-- **Simple-root Hensel lift in `k⟦X⟧`** (the concrete `(X)`-adic form of `is_henselian`).
A monic `f` over `k⟦X⟧` with an approximate root `a₀` (`f.eval a₀ ≡ 0 mod X`) whose
derivative is a unit at `a₀` has an exact root `a` congruent to `a₀ mod X`.  This is the
Newton/Hensel step underlying [BCIKS20] Appendix A.4: a power-series lift in the variable `X`
over the coefficient field. -/
theorem powerSeries_hensel_lift (f : Polynomial (PowerSeries k)) (hf : f.Monic)
    (a₀ : PowerSeries k)
    (h₁ : f.eval a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries k)})
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : PowerSeries k, f.IsRoot a ∧
      a - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries k)} := by
  have h₁' : f.eval a₀ ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    rwa [PowerSeries.maximalIdeal_eq_span_X]
  obtain ⟨a, ha_root, ha_sub⟩ := HenselianLocalRing.is_henselian f hf a₀ h₁' h₂
  exact ⟨a, ha_root, by rwa [← PowerSeries.maximalIdeal_eq_span_X]⟩

/-- The power-series ring over the rational function field `F(Z) = RatFunc F` is Henselian.
This is the **exact base ring of the [BCIKS20] Appendix-A.4 Hensel lift** used in the §5
list-decoding argument to extract the curve coefficient polynomials — i.e. the foundation of
"ingredient D" of the proximity-gap keystone: power series in the lift variable `X` over the
coefficient field `K = F(Z)`.  It is a free instance of `powerSeries_henselianLocalRing`. -/
instance ratFunc_powerSeries_henselianLocalRing {F : Type*} [Field F] :
    HenselianLocalRing ((RatFunc F)⟦X⟧) :=
  powerSeries_henselianLocalRing

end ArkLib
