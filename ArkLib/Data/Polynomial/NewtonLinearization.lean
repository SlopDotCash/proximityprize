/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- dedup-audit(#257): intentional mathlib-only origin for coeff_pow_sub_*; copies in Hensel* are deliberate worktree-resilience re-derivations -- do not re-import. See issue #257 A5.
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Newton-step linearization for power-series powers (BCIKS20 App. A.4 — P2 path)

The structural lemma underlying the order-by-order `R(X, γ, Z) = 0` induction of
[BCIKS20] App. A.4. We work over a fixed commutative ring `R` with two power series
`γ₁ γ₂ : R⟦X⟧` that **agree below truncation order `t`** (all coefficients `j < t`,
including the constant term `j = 0` — so in particular `constantCoeff γ₁ = constantCoeff γ₂`).
The point of the induction is to compute, to *first order in the order-`t` perturbation*
`δ := coeff t γ₁ − coeff t γ₂`, the difference of the order-`t` coefficients of the composed
series `P(γ₁)` and `P(γ₂)` for a polynomial `P`.

Three results:

* **`coeff_pow_sub_below`** (LEMMA A, truncation propagation): agreement below `t`
  propagates to every power `γ^i`. Proof: induction on `i`; `coeff_mul` only references
  coefficient indices `a, b` with `a + b = j < t`, hence `a, b < t`.

* **`coeff_pow_sub_at`** (LEMMA B, linearization): under the same hypothesis with `0 < t`,
  writing `c := constantCoeff γ₁`,
  `coeff t (γ₁^(i+1)) − coeff t (γ₂^(i+1)) = (i+1) • (c^i · (coeff t γ₁ − coeff t γ₂))`.
  (The subtraction-free `(i+1)` shape sidesteps the `i − 1` in `ℕ`.) Proof: induction on `i`;
  in the `coeff_mul`/antidiagonal expansion of `γ^(i+1) = γ^i · γ`, every interior antidiagonal
  pair `(a, b)` with `a + b = t` other than the ends `(t, 0)`/`(0, t)` has `a < t` and `b < t`,
  so it agrees between the two series by LEMMA A (`γ^i` factor) and the below-`t` hypothesis
  (`γ` factor) and cancels in the difference; the end terms `(t,0): δ · c^i` and
  `(0,t): c^{i+1} · δ` assemble with the inductive hypothesis into `(i+1) • (c^i δ)`.

* **`coeff_aeval_sub_at`** (COROLLARY, the P2-facing form): for a polynomial `P`,
  `coeff t (aeval γ₁ P) − coeff t (aeval γ₂ P) =
    (eval c (derivative P)) · (coeff t γ₁ − coeff t γ₂)`.
  The composed-series order-`t` coefficient is `P′(c)`-linear in the order-`t` input — exactly
  the Newton/Hensel linearization driving the order-by-order vanishing argument. The
  `aeval`-expansion `coeff t (aeval γ P) = ∑ᵢ Pᵢ · coeff t (γ^i)` is restated locally
  (mirroring `coeff_aeval_powerSeries` of `GammaSubstObstruction.lean`) so this file depends
  only on mathlib.
-/

namespace ProximityPrize.NewtonLinearization

open PowerSeries

variable {R : Type*} [CommRing R]

/-! ## LEMMA A — truncation propagation -/

/-- **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient
`j < t`, then so do `γ₁^i` and `γ₂^i`, for every `i`.

Proof by induction on `i`. The `coeff_mul` antidiagonal sum for `coeff j (γ * γ^i)` only
references coefficient indices `a, b` with `a + b = j < t`, so both `a < t` and `b < t`,
where the hypothesis, respectively the inductive hypothesis, supplies agreement. -/
theorem coeff_pow_sub_below {γ₁ γ₂ : R⟦X⟧} {t : ℕ}
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    ∀ (i : ℕ), ∀ j < t, coeff j (γ₁ ^ i) = coeff j (γ₂ ^ i) := by
  intro i
  induction i with
  | zero =>
      intro j _
      simp
  | succ i ih =>
      intro j hj
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      have h1 : p.1 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_right _ _) hj
      have h2 : p.2 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_left _ _) hj
      rw [ih p.1 h1, h p.2 h2]

/-! ## LEMMA B — Newton linearization at order `t` -/

/-- **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with
`0 < t`, writing `c := constantCoeff γ₁` (`= constantCoeff γ₂`) and
`δ := coeff t γ₁ − coeff t γ₂`, the order-`t` coefficients of the `(i+1)`-th powers differ by

  `coeff t (γ₁^(i+1)) − coeff t (γ₂^(i+1)) = (i+1) • (c^i · δ)`.

(The `(i+1)` shape avoids the `i − 1` of the textbook `i • c^{i-1}` form in `ℕ`.)

Proof by induction on `i`. Expanding `γ^(i+1) = γ^i · γ` via `coeff_mul` over
`Finset.antidiagonal t`, the only antidiagonal pairs `(a, b)` with `a + b = t` carrying the
order-`t` perturbation are the ends `(t, 0)` and `(0, t)`: every other pair has `a < t` and
`b < t`, so the `γ^i`-factor agrees by LEMMA A and the `γ`-factor agrees by hypothesis, and
those interior terms cancel in the difference. The end-term contributions are
`(t,0): (coeff t γ₁^(i+1) − coeff t γ₂^(i+1)) · c` and `(0,t): c^{i+1} · δ`; the inductive
hypothesis rewrites the former as `((i+1) • (c^i δ)) · c = (i+1) • (c^{i+1} δ)`, and the
total is `(i+2) • (c^{i+1} δ)`. -/
theorem coeff_pow_sub_at {γ₁ γ₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    ∀ (i : ℕ), coeff t (γ₁ ^ (i + 1)) - coeff t (γ₂ ^ (i + 1)) =
      (i + 1) • ((constantCoeff γ₁) ^ i * (coeff t γ₁ - coeff t γ₂)) := by
  set c := constantCoeff γ₁ with hc
  have hc2 : constantCoeff γ₂ = c := by
    rw [hc, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (h 0 ht).symm
  intro i
  induction i with
  | zero =>
      simp only [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | succ i ih =>
      have hA : ∀ j < t, coeff j (γ₁ ^ (i + 1)) = coeff j (γ₂ ^ (i + 1)) :=
        coeff_pow_sub_below h (i + 1)
      -- γ^(i+2) = γ^(i+1) · γ; expand both order-`t` coefficients and subtract termwise.
      rw [pow_succ (γ₁) (i + 1), pow_succ (γ₂) (i + 1), coeff_mul, coeff_mul,
        ← Finset.sum_sub_distrib]
      -- Split off the end terms (t, 0) and (0, t); all interior terms vanish.
      have ht0 : (t, 0) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have h0t : (0, t) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have hne : ((t, 0) : ℕ × ℕ) ≠ (0, t) := fun hcontra => ht.ne' (Prod.ext_iff.mp hcontra).1
      rw [Finset.sum_eq_add_of_mem (t, 0) (0, t) ht0 h0t hne ?_]
      · -- End-term assembly with the IH.
        have e0₁ : coeff (0, t).1 (γ₁ ^ (i + 1)) = c ^ (i + 1) := by
          simp only [coeff_zero_eq_constantCoeff_apply, map_pow, ← hc]
        have e0₂ : coeff (0, t).1 (γ₂ ^ (i + 1)) = c ^ (i + 1) := by
          simp only [coeff_zero_eq_constantCoeff_apply, map_pow, hc2]
        have ec₁ : coeff (t, 0).2 γ₁ = c := by
          simp only [coeff_zero_eq_constantCoeff_apply, ← hc]
        have ec₂ : coeff (t, 0).2 γ₂ = c := by
          simp only [coeff_zero_eq_constantCoeff_apply, hc2]
        change (coeff (t, 0).1 (γ₁ ^ (i + 1)) * coeff (t, 0).2 γ₁
                - coeff (t, 0).1 (γ₂ ^ (i + 1)) * coeff (t, 0).2 γ₂)
              + (coeff (0, t).1 (γ₁ ^ (i + 1)) * coeff (0, t).2 γ₁
                - coeff (0, t).1 (γ₂ ^ (i + 1)) * coeff (0, t).2 γ₂)
            = (i + 1 + 1) • (c ^ (i + 1) * (coeff t γ₁ - coeff t γ₂))
        rw [ec₁, ec₂, e0₁, e0₂]
        change (coeff t (γ₁ ^ (i + 1)) * c - coeff t (γ₂ ^ (i + 1)) * c)
              + (c ^ (i + 1) * coeff t γ₁ - c ^ (i + 1) * coeff t γ₂)
            = (i + 1 + 1) • (c ^ (i + 1) * (coeff t γ₁ - coeff t γ₂))
        -- (t,0)-term = (coeff t γ₁^(i+1) − coeff t γ₂^(i+1)) * c = ((i+1) • (c^i δ)) * c.
        rw [← sub_mul, ih]
        -- Convert all `nsmul` to ring multiplication and finish by `ring`.
        simp only [nsmul_eq_mul, pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      · -- Interior terms vanish.
        intro p hp hp'
        rw [Finset.mem_antidiagonal] at hp
        obtain ⟨hpt0, hp0t⟩ := hp'
        have hb_lt : p.2 < t := by
          rcases lt_or_eq_of_le (show p.2 ≤ t from by rw [← hp]; exact Nat.le_add_left _ _)
            with hlt | heq
          · exact hlt
          · exact absurd (Prod.ext (show p.1 = (0, t).1 by simp; omega) (by simpa using heq)) hp0t
        have ha_lt : p.1 < t := by
          rcases lt_or_eq_of_le (show p.1 ≤ t from by rw [← hp]; exact Nat.le_add_right _ _)
            with hlt | heq
          · exact hlt
          · exact absurd (Prod.ext (by simpa using heq) (show p.2 = (t, 0).2 by simp; omega)) hpt0
        rw [hA p.1 ha_lt, h p.2 hb_lt, sub_self]

/-! ## COROLLARY — the `P′(c)`-linear, P2-facing form -/

/-- Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is
`ProximityPrize.coeff_aeval_powerSeries` of `GammaSubstObstruction.lean`, restated here so
the file imports only mathlib): for a polynomial `P` and a power series `γ`,
`coeff n (aeval γ P) = ∑_{i ≤ deg P} P.coeff i · coeff n (γ^i)`. -/
theorem coeff_aeval_eq_sum_range (P : Polynomial R) (γ : R⟦X⟧) (n : ℕ) :
    coeff n (Polynomial.aeval γ P) =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * coeff n (γ ^ i) := by
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_smul, smul_eq_mul]

/-- **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P`
over `R` and power series `γ₁ γ₂` agreeing below order `t` (with `0 < t`), writing
`c := constantCoeff γ₁` (`= constantCoeff γ₂`), the order-`t` coefficient of `P(γ)` is
`P′(c)`-linear in the order-`t` perturbation:

  `coeff t (aeval γ₁ P) − coeff t (aeval γ₂ P) = eval c (derivative P) · (coeff t γ₁ − coeff t γ₂)`.

Proof: expand both sides over `range (natDegree P + 1)` via `coeff_aeval_eq_sum_range`; the
`i`-th difference is `P.coeff i · (coeff t (γ₁^i) − coeff t (γ₂^i))`, which LEMMA B
(`coeff_pow_sub_at`) evaluates to `P.coeff i · (i • (c^{i-1} δ))`. The `i = 0` term is `0`
(empty `c^{-1}` handled by the `(i+1)`-shape: the `i = 0` summand contributes `0` since
`coeff t (γ^0) = coeff t 1 = 0` for `t > 0`). Summing
`∑ i, P.coeff i · i · c^{i-1} = eval c (derivative P)` is `derivative_eval` after reindexing.
-/
theorem coeff_aeval_sub_at (P : Polynomial R) {γ₁ γ₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    coeff t (Polynomial.aeval γ₁ P) - coeff t (Polynomial.aeval γ₂ P) =
      Polynomial.eval (constantCoeff γ₁) (Polynomial.derivative P) * (coeff t γ₁ - coeff t γ₂) := by
  set c := constantCoeff γ₁ with hc
  set δ := coeff t γ₁ - coeff t γ₂ with hδ
  rw [coeff_aeval_eq_sum_range, coeff_aeval_eq_sum_range, ← Finset.sum_sub_distrib]
  -- Termwise: P.coeff i * coeff t (γ₁^i) - P.coeff i * coeff t (γ₂^i)
  --         = P.coeff i * (coeff t (γ₁^i) - coeff t (γ₂^i)).
  have hstep : ∀ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * coeff t (γ₁ ^ i) - P.coeff i * coeff t (γ₂ ^ i)
        = P.coeff i * i * c ^ (i - 1) * δ := by
    intro i _
    rw [← mul_sub]
    rcases i with _ | i
    · -- i = 0: coeff t (γ^0) = coeff t 1 = 0 (t > 0), both terms zero.
      simp only [pow_zero, coeff_one, Nat.cast_zero, mul_zero, zero_mul]
      rw [if_neg (by omega), sub_zero, mul_zero]
    · -- i + 1 ≥ 1: apply LEMMA B.
      rw [coeff_pow_sub_at ht h i, ← hc, ← hδ]
      -- P.coeff (i+1) * ((i+1) • (c^i * δ)) = P.coeff (i+1) * (i+1) * c^((i+1)-1) * δ
      rw [Nat.add_sub_cancel, nsmul_eq_mul]
      push_cast
      ring
  rw [Finset.sum_congr rfl hstep]
  -- ∑ i, P.coeff i * i * c^(i-1) * δ = eval c (derivative P) * δ
  rw [← Finset.sum_mul]
  congr 1
  -- ∑_{i < deg+1} P.coeff i * i * c^(i-1) = eval c (derivative P)
  rw [Polynomial.derivative_eval, Polynomial.sum_over_range' _ (by simp) (P.natDegree + 1)
        (Nat.lt_succ_self _)]

/-! ## Axiom audit (recorded 2026-06-05)

In-file `#print axioms` (run on a temp copy, then removed) confirmed every declaration of this
file — `coeff_pow_sub_below` (LEMMA A), `coeff_pow_sub_at` (LEMMA B),
`coeff_aeval_eq_sum_range` (local `aeval`-expansion), `coeff_aeval_sub_at` (COROLLARY) —
depends only on `[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no `native_decide` /
`Lean.ofReduceBool`. The file is sorry-free and `lake env lean` exits 0. -/

#print axioms ProximityPrize.NewtonLinearization.coeff_pow_sub_below
#print axioms ProximityPrize.NewtonLinearization.coeff_pow_sub_at
#print axioms ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range
#print axioms ProximityPrize.NewtonLinearization.coeff_aeval_sub_at

end ProximityPrize.NewtonLinearization
