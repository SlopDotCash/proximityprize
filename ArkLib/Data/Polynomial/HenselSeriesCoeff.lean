/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- dedup-audit(#257): intentional mathlib-only re-derivation (self-contained, no ArkLib oleans). #257 A5.
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Hensel lifting in the BCIKS20-application shape (series-coefficient polynomials)

`HenselExistence.lean` proves abstract Hensel for a polynomial `P : R[X]` whose coefficients
are *constants* in `R`, lifting a simple root `c : R` to a root `γ : R⟦X⟧`. The BCIKS20
quotienting argument (App. A.4) requires the **application shape**: the polynomial whose root we
lift already has **power-series coefficients**,

  `Q : Polynomial R⟦X⟧`,

with root data prescribed only at **order 0**. Concretely, let

  `Q₀ : R[X] := Q.map (constantCoeff)`        (the order-0 reduction, `constantCoeff` a `RingHom`)

and let `c : R` be a *simple* root of `Q₀`:

* `eval c Q₀ = 0`,
* `IsUnit (eval c (derivative Q₀))`.

**Main theorems.**

* `exists_powerSeries_root_seriesCoeff` (EXISTENCE): there is `γ : R⟦X⟧` with
  `constantCoeff γ = c` and `Polynomial.eval γ Q = 0`. Here the evaluation is the *plain*
  `Polynomial.eval γ Q`: `Q`'s coefficients already live in `R⟦X⟧`, the same ring as `γ`, so
  `eval` (not `aeval`/`eval₂`) is the right and cleanest primitive.
* `root_unique_seriesCoeff` (UNIQUENESS): two roots of `Q` sharing the same constant coefficient
  are equal.

**The new ingredient — generalized linearization with a convolution.** With series coefficients
the order-`t` coefficient of `eval γ Q` expands as a *double* sum (a convolution over each
coefficient series):

  `coeff t (eval γ Q) = ∑ᵢ ∑_{a+b=t} coeff a (Q.coeff i) · coeff b (γ^i)`.

Comparing two series `γ₁, γ₂` that agree below order `t` (`0 < t`): truncation propagation
(`coeff_pow_sub_below`) makes `coeff b (γ₁^i) = coeff b (γ₂^i)` for every `b < t`, so **only the
`b = t` (hence `a = 0`) corner of each convolution survives the difference**. The surviving
`a = 0` factor is `coeff 0 (Q.coeff i) = constantCoeff (Q.coeff i) = Q₀.coeff i`, a *constant*.
Thus the convolution collapses to exactly the constant-coefficient linearization of
`HenselExistence`, but against `Q₀`:

  `coeff t (eval γ₁ Q) − coeff t (eval γ₂ Q) = eval c (derivative Q₀) · (coeff t γ₁ − coeff t γ₂)`.

From there the Newton recursion and order-by-order vanishing are *verbatim* those of
`HenselExistence` (the linear response `eval c (derivative Q₀)` is a unit by hypothesis, and the
order-0 coefficient is `eval c Q₀ = 0`), so the same construction lifts `c` to a root of `Q`.

**Self-containment.** `HenselExistence` / `NewtonLinearization` are on this branch but their
`olean`s are not prebuilt here, and they are stated for `R[X]` (constant coefficients), not the
`R⟦X⟧[X]` shape, so the two power-only lemmas that transfer unchanged — truncation propagation
(LEMMA A) and the Newton power linearization (LEMMA B) — are **restated and reproven locally**
(namespace `HenselSeriesCoeff`), and the file depends only on mathlib.
-/

namespace ProximityPrize.HenselSeriesCoeff

open PowerSeries

variable {R : Type*} [CommRing R]

/-! ## Power-only transfer lemmas (LEMMA A, LEMMA B — identical to the asset proofs) -/

/-- **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power.
Local copy of `NewtonLinearization.coeff_pow_sub_below`; the proof is purely about powers of a
single series, so it transfers to the series-coefficient setting unchanged. -/
theorem coeff_pow_sub_below {γ₁ γ₂ : R⟦X⟧} {t : ℕ}
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    ∀ (i : ℕ), ∀ j < t, coeff j (γ₁ ^ i) = coeff j (γ₂ ^ i) := by
  intro i
  induction i with
  | zero => intro j _; simp
  | succ i ih =>
      intro j hj
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      have h1 : p.1 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_right _ _) hj
      have h2 : p.2 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_left _ _) hj
      rw [ih p.1 h1, h p.2 h2]

/-- **LEMMA B (Newton power linearization).** Local copy of
`NewtonLinearization.coeff_pow_sub_at`. -/
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
  | zero => simp only [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | succ i ih =>
      have hA : ∀ j < t, coeff j (γ₁ ^ (i + 1)) = coeff j (γ₂ ^ (i + 1)) :=
        coeff_pow_sub_below h (i + 1)
      rw [pow_succ (γ₁) (i + 1), pow_succ (γ₂) (i + 1), coeff_mul, coeff_mul,
        ← Finset.sum_sub_distrib]
      have ht0 : (t, 0) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have h0t : (0, t) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have hne : ((t, 0) : ℕ × ℕ) ≠ (0, t) := fun hcontra => ht.ne' (Prod.ext_iff.mp hcontra).1
      rw [Finset.sum_eq_add_of_mem (t, 0) (0, t) ht0 h0t hne ?_]
      · have e0₁ : coeff (0, t).1 (γ₁ ^ (i + 1)) = c ^ (i + 1) := by
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
        rw [← sub_mul, ih]
        simp only [nsmul_eq_mul, pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      · intro p hp hp'
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

/-! ## The order-0 reduction `Q₀` -/

variable (Q : Polynomial R⟦X⟧)

/-- The order-0 reduction `Q₀ := Q.map constantCoeff : R[X]`: replace each power-series
coefficient by its constant term. -/
noncomputable def Q₀ : Polynomial R := Q.map (constantCoeff (R := R))

@[simp] theorem coeff_Q₀ (i : ℕ) : (Q₀ Q).coeff i = constantCoeff (Q.coeff i) := by
  rw [Q₀, Polynomial.coeff_map]

/-- `natDegree Q₀ ≤ natDegree Q`, so `range (natDegree Q + 1)` is a common index range that
covers both `Q` and `Q₀` (extra terms are zero coefficients). -/
theorem natDegree_Q₀_le : (Q₀ Q).natDegree ≤ Q.natDegree :=
  Polynomial.natDegree_map_le

/-! ## Generalized coefficient expansion (the convolution) -/

/-- **Generalized coefficient expansion.** Evaluating a series-coefficient polynomial and
reading off order `t` is a *convolution* over each coefficient series:

  `coeff t (eval γ Q) = ∑_{i ≤ deg Q} coeff t (Q.coeff i · γ^i)`,

with `coeff t (Q.coeff i · γ^i) = ∑_{a+b=t} coeff a (Q.coeff i) · coeff b (γ^i)` available by
`PowerSeries.coeff_mul`. -/
theorem coeff_eval_eq_sum_range (γ : R⟦X⟧) (t : ℕ) :
    coeff t (Polynomial.eval γ Q) =
      ∑ i ∈ Finset.range (Q.natDegree + 1), coeff t (Q.coeff i * γ ^ i) := by
  rw [Polynomial.eval_eq_sum_range, map_sum]

/-! ## Generalized linearization — the order-`t` Newton response is `Q₀′(c)` -/

/-- **Generalized Newton/Hensel linearization (series-coefficient form).** For `γ₁ γ₂ : R⟦X⟧`
agreeing below order `t` (`0 < t`), writing `c := constantCoeff γ₁`, the order-`t` coefficient
of `eval γ Q` is `Q₀′(c)`-linear in the order-`t` perturbation:

  `coeff t (eval γ₁ Q) − coeff t (eval γ₂ Q) = eval c (derivative Q₀) · (coeff t γ₁ − coeff t γ₂)`.

**Proof.** Expand both sides via `coeff_eval_eq_sum_range`; the `i`-th difference is
`coeff t (Q.coeff i · γ₁^i) − coeff t (Q.coeff i · γ₂^i)`. Expanding each
`coeff t (Q.coeff i · γ^i)` over `antidiagonal t` by `coeff_mul` and subtracting, every
antidiagonal pair `(a,b)` with `b < t` cancels (its `γ^i` factor agrees by LEMMA A), leaving only
the corner `(0, t)`:

  `= coeff 0 (Q.coeff i) · (coeff t (γ₁^i) − coeff t (γ₂^i)) = (Q₀.coeff i) · (coeff t γ₁^i − …)`.

LEMMA B (`coeff_pow_sub_at`) evaluates the power difference to `i • (c^{i-1} δ)`, and the sum
`∑ᵢ (Q₀.coeff i) · i · c^{i-1} = eval c (derivative Q₀)` by `derivative_eval` + `sum_over_range'`.
This is exactly the constant-coefficient finish of `HenselExistence`, but against `Q₀`. -/
theorem coeff_eval_sub_at {γ₁ γ₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    coeff t (Polynomial.eval γ₁ Q) - coeff t (Polynomial.eval γ₂ Q) =
      Polynomial.eval (constantCoeff γ₁) (Polynomial.derivative (Q₀ Q)) *
        (coeff t γ₁ - coeff t γ₂) := by
  set c := constantCoeff γ₁ with hc
  set δ := coeff t γ₁ - coeff t γ₂ with hδ
  rw [coeff_eval_eq_sum_range, coeff_eval_eq_sum_range, ← Finset.sum_sub_distrib]
  -- Termwise: the convolution difference collapses to the `(0, t)` corner, then LEMMA B.
  have hstep : ∀ i ∈ Finset.range (Q.natDegree + 1),
      coeff t (Q.coeff i * γ₁ ^ i) - coeff t (Q.coeff i * γ₂ ^ i)
        = constantCoeff (Q.coeff i) * i * c ^ (i - 1) * δ := by
    intro i _
    -- Step 1: collapse the convolution difference to the `(0, t)` corner.
    have hcorner : coeff t (Q.coeff i * γ₁ ^ i) - coeff t (Q.coeff i * γ₂ ^ i)
        = constantCoeff (Q.coeff i) * (coeff t (γ₁ ^ i) - coeff t (γ₂ ^ i)) := by
      rw [coeff_mul, coeff_mul, ← Finset.sum_sub_distrib]
      have h0t : (0, t) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      rw [Finset.sum_eq_single_of_mem (0, t) h0t ?_]
      · -- corner term `(0, t)`: `coeff 0 (Q.coeff i) = constantCoeff (Q.coeff i)`.
        simp only [coeff_zero_eq_constantCoeff_apply, mul_sub]
      · -- every other antidiagonal pair has `b < t`, so its `γ^i` factor agrees and it cancels.
        intro p hp hpne
        rw [Finset.mem_antidiagonal] at hp
        have hb_lt : p.2 < t := by
          rcases lt_or_eq_of_le (show p.2 ≤ t from by rw [← hp]; exact Nat.le_add_left _ _)
            with hlt | heq
          · exact hlt
          · exact absurd (Prod.ext (show p.1 = (0, t).1 by simp; omega) (by simpa using heq)) hpne
        rw [coeff_pow_sub_below h i p.2 hb_lt, sub_self]
    rw [hcorner]
    -- Step 2: LEMMA B on the power difference, in the `(i+1)`-shape (i = 0 handled separately).
    rcases i with _ | i
    · simp only [pow_zero, coeff_one, Nat.cast_zero, mul_zero, zero_mul]
      rw [if_neg (by omega), sub_zero, mul_zero]
    · rw [coeff_pow_sub_at ht h i, ← hc, ← hδ, Nat.add_sub_cancel, nsmul_eq_mul]
      -- `constantCoeff (Q.coeff (i+1)) = Q₀.coeff (i+1)`.
      push_cast
      ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  congr 1
  -- `∑_{i < deg Q + 1} (Q₀.coeff i) · i · c^{i-1} = eval c (derivative Q₀)`, via `derivative_eval`.
  rw [Polynomial.derivative_eval]
  -- Rephrase the summand `constantCoeff (Q.coeff i) = Q₀.coeff i`, then reindex with the
  -- (possibly larger) range `Q.natDegree + 1 > Q₀.natDegree`.
  have hQQ : ∀ i, constantCoeff (Q.coeff i) = (Q₀ Q).coeff i := fun i => (coeff_Q₀ Q i).symm
  simp only [hQQ]
  rw [Polynomial.sum_over_range' _ (by simp) (Q.natDegree + 1)
        (Nat.lt_succ_of_le (natDegree_Q₀_le Q))]

/-! ## Constant-coefficient compatibility -/

/-- `constantCoeff (eval γ Q) = eval (constantCoeff γ) Q₀`: the order-0 part of the evaluated
series is the evaluation of the reduced polynomial at the reduced point. -/
theorem constantCoeff_eval (γ : R⟦X⟧) :
    constantCoeff (Polynomial.eval γ Q) = Polynomial.eval (constantCoeff γ) (Q₀ Q) := by
  -- Expand both over the *common* range `Q.natDegree + 1` (which covers `Q₀` since
  -- `natDegree Q₀ ≤ natDegree Q`), so the sums match termwise.
  rw [Polynomial.eval_eq_sum_range, map_sum,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_Q₀_le Q))]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow, coeff_Q₀]

/-! ## The Newton partial-sum sequence and its diagonal (mirrors `HenselExistence`) -/

variable (c : R)

/-- The Newton partial-sum sequence for `Q`. `S 0 := C c`; at each step we add the order-`(t+1)`
correction monomial whose coefficient is `−u · coeff (t+1) (eval (S t) Q)`, where
`u = Ring.inverse (eval c (derivative Q₀))`. Built by ordinary structural recursion. -/
noncomputable def S : ℕ → R⟦X⟧
  | 0 => PowerSeries.C c
  | (t + 1) =>
      S t + PowerSeries.monomial (t + 1)
        (-(Ring.inverse (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))
          * coeff (t + 1) (Polynomial.eval (S t) Q))

/-- Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged. -/
theorem coeff_S_succ_of_le {t j : ℕ} (hj : j ≤ t) :
    coeff j (S Q c (t + 1)) = coeff j (S Q c t) := by
  rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]

/-- `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes. -/
theorem coeff_S_eq_zero_of_lt : ∀ {t j : ℕ}, t < j → coeff j (S Q c t) = 0 := by
  intro t
  induction t with
  | zero => intro j hj; rw [S, coeff_C, if_neg (by omega)]
  | succ t ih =>
      intro j hj
      rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]
      exact ih (by omega)

/-- Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. -/
theorem coeff_S_stable : ∀ {t j : ℕ}, j ≤ t → coeff j (S Q c t) = coeff j (S Q c j) := by
  intro t
  induction t with
  | zero => intro j hj; rw [Nat.le_zero.mp hj]
  | succ t ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · rw [coeff_S_succ_of_le Q c (Nat.lt_succ_iff.mp hlt), ih (Nat.lt_succ_iff.mp hlt)]
      · rw [heq]

/-- The Newton root: diagonalise the stable partial sums. -/
noncomputable def γ : R⟦X⟧ := PowerSeries.mk fun t => coeff t (S Q c t)

@[simp] theorem coeff_γ (t : ℕ) : coeff t (γ Q c) = coeff t (S Q c t) := by
  rw [γ, coeff_mk]

/-- The constant coefficient of the Newton root is the prescribed root `c`. -/
@[simp] theorem constantCoeff_γ : constantCoeff (γ Q c) = c := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_γ, S, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_C]

/-- `γ` agrees with the `t`-th partial sum below order `t + 1`. -/
theorem coeff_γ_eq_S {t j : ℕ} (hj : j ≤ t) : coeff j (γ Q c) = coeff j (S Q c t) := by
  rw [coeff_γ, ← coeff_S_stable Q c hj]

/-! ## Order-by-order vanishing -/

variable (hc0 : Polynomial.eval c (Q₀ Q) = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))

include hc0 in
/-- Order-0 coefficient of `eval γ Q` vanishes: it is `eval c Q₀ = 0`. -/
theorem coeff_zero_eval_γ : coeff 0 (Polynomial.eval (γ Q c) Q) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_eval, constantCoeff_γ, hc0]

include hu in
/-- Order-`(t+1)` coefficient of `eval γ Q` vanishes, by the generalized linearization: γ agrees
with `S t` below order `t+1`, the `(t+1)`-coefficient of `S (t+1)` was *chosen* to cancel
`coeff (t+1) (eval (S t) Q)` after multiplication by the unit linear response `eval c Q₀′`. -/
theorem coeff_succ_eval_γ (t : ℕ) : coeff (t + 1) (Polynomial.eval (γ Q c) Q) = 0 := by
  set A := Polynomial.eval c (Polynomial.derivative (Q₀ Q)) with hA
  set u := Ring.inverse A with hudef
  set w := coeff (t + 1) (Polynomial.eval (S Q c t) Q) with hw
  have hAu : A * u = 1 := Ring.mul_inverse_cancel A hu
  have hagree : ∀ j < t + 1, coeff j (γ Q c) = coeff j (S Q c t) := fun j hj =>
    coeff_γ_eq_S Q c (Nat.lt_succ_iff.mp hj)
  have hlin := coeff_eval_sub_at Q (γ₁ := γ Q c) (γ₂ := S Q c t) (Nat.succ_pos t) hagree
  rw [constantCoeff_γ, ← hA] at hlin
  have hSt0 : coeff (t + 1) (S Q c t) = 0 := coeff_S_eq_zero_of_lt Q c (Nat.lt_succ_self t)
  have hγcoeff : coeff (t + 1) (γ Q c) = -u * w := by
    rw [coeff_γ, S, map_add, coeff_monomial, if_pos rfl, hSt0, zero_add, ← hA, ← hudef, ← hw]
  rw [hγcoeff, hSt0, ← hw] at hlin
  rw [show A * (-u * w - 0) = -(A * u) * w by ring, hAu, neg_one_mul] at hlin
  have hgoal : coeff (t + 1) (Polynomial.eval (γ Q c) Q) = w + (-w) := by
    rw [← hlin]; ring
  rw [hgoal, add_neg_cancel]

include hc0 hu in
/-- Every coefficient of `eval γ Q` vanishes, hence `eval γ Q = 0`. -/
theorem eval_γ_eq_zero : Polynomial.eval (γ Q c) Q = 0 := by
  ext t
  rw [map_zero]
  rcases t with _ | t
  · exact coeff_zero_eval_γ Q c hc0
  · exact coeff_succ_eval_γ Q c hu t

/-! ## Main existence theorem (application-shaped Hensel for `R⟦X⟧[X]`) -/

variable {Q c}

include hc0 hu in
/-- **Hensel-root existence in the BCIKS20-application shape.** Given `Q : Polynomial R⟦X⟧` whose
order-0 reduction `Q₀ := Q.map constantCoeff` has a *simple* root `c : R`
(`eval c Q₀ = 0` and `IsUnit (eval c (derivative Q₀))`), there is a power series `γ : R⟦X⟧`
lifting `c` (`constantCoeff γ = c`) with `Polynomial.eval γ Q = 0`.

This is the application-shaped analogue of `HenselExistence.exists_powerSeries_root`: there the
polynomial had *constant* coefficients in `R`; here its coefficients already live in `R⟦X⟧`, and
the root data is prescribed only at order 0. -/
theorem exists_powerSeries_root_seriesCoeff :
    ∃ γ : R⟦X⟧, constantCoeff γ = c ∧ Polynomial.eval γ Q = 0 :=
  ⟨γ Q c, constantCoeff_γ Q c, eval_γ_eq_zero Q c hc0 hu⟩

/-! ## Uniqueness -/

/-- **Uniqueness in the application shape.** Two roots of `Q : Polynomial R⟦X⟧` that share a
constant coefficient `c` at which `Q₀ := Q.map constantCoeff` is simple
(`IsUnit (eval c (derivative Q₀))`) coincide.

**Proof.** Suppose `γ₁ ≠ γ₂`; let `t` be minimal with `coeff t γ₁ ≠ coeff t γ₂`. Since both share
the constant coefficient `c = constantCoeff γ₁ = constantCoeff γ₂`, we have `t ≠ 0`, i.e. `0 < t`,
and `γ₁, γ₂` agree below order `t`. Both evaluate to `0`, so the generalized linearization
(`coeff_eval_sub_at`) gives `0 = eval c (derivative Q₀) · (coeff t γ₁ − coeff t γ₂)`. Multiplying
by the inverse of the unit `eval c (derivative Q₀)` forces `coeff t γ₁ = coeff t γ₂`,
contradicting minimality. Hence `γ₁ = γ₂`. -/
theorem root_unique_seriesCoeff {γ₁ γ₂ : R⟦X⟧}
    (hcc : constantCoeff γ₁ = constantCoeff γ₂)
    (hu : IsUnit (Polynomial.eval (constantCoeff γ₁) (Polynomial.derivative (Q₀ Q))))
    (h₁ : Polynomial.eval γ₁ Q = 0) (h₂ : Polynomial.eval γ₂ Q = 0) :
    γ₁ = γ₂ := by
  by_contra hne
  -- There is a least index `t` at which the coefficients differ.
  have hex : ∃ t, coeff t γ₁ ≠ coeff t γ₂ := by
    by_contra hall
    push Not at hall
    exact hne (PowerSeries.ext fun t => hall t)
  classical
  let t := Nat.find hex
  have ht_ne : coeff t γ₁ ≠ coeff t γ₂ := Nat.find_spec hex
  have hbelow : ∀ j < t, coeff j γ₁ = coeff j γ₂ := fun j hj => by
    by_contra hjne; exact absurd (Nat.find_le hjne) (not_le.mpr hj)
  -- `t ≠ 0`, since the constant coefficients agree.
  have ht_pos : 0 < t := by
    refine Nat.pos_of_ne_zero fun ht0 => ht_ne ?_
    rw [ht0, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hcc]
  -- Linearization at order `t`, both roots vanishing.
  have hlin := coeff_eval_sub_at Q (γ₁ := γ₁) (γ₂ := γ₂) ht_pos hbelow
  rw [h₁, h₂] at hlin
  simp only [map_zero, sub_self] at hlin
  -- `0 = (unit) · (coeff t γ₁ − coeff t γ₂)` forces the difference to be `0`.
  set A := Polynomial.eval (constantCoeff γ₁) (Polynomial.derivative (Q₀ Q)) with hA
  have hAu : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hu
  -- `hlin : 0 = A * δ`; multiply by `Ring.inverse A` on the left.
  have hzero : coeff t γ₁ - coeff t γ₂ = 0 := by
    have h2 := congrArg (fun x => Ring.inverse A * x) hlin
    simp only [mul_zero, ← mul_assoc, hAu, one_mul] at h2
    exact h2.symm
  exact ht_ne (sub_eq_zero.mp hzero)

/-! ## Axiom audit

In-file `#print axioms` (run on a temp copy, then removed — see disposition note) is intended to
confirm every declaration depends only on `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`, no `native_decide` / `Lean.ofReduceBool`. -/

end ProximityPrize.HenselSeriesCoeff

-- Axiom audit: every claimed-done declaration rests only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_at
#print axioms ProximityPrize.HenselSeriesCoeff.coeff_S_stable
#print axioms ProximityPrize.HenselSeriesCoeff.eval_γ_eq_zero
#print axioms ProximityPrize.HenselSeriesCoeff.exists_powerSeries_root_seriesCoeff
#print axioms ProximityPrize.HenselSeriesCoeff.root_unique_seriesCoeff
