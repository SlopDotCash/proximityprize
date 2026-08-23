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
# Hensel-root EXISTENCE for power series (abstract Hensel for `R⟦X⟧`)

Companion to the **uniqueness** half (`NewtonLinearization.aeval_root_unique`): we prove the
**existence** half of Hensel's lemma for the power-series ring `R⟦X⟧` over an arbitrary
commutative ring `R`.

**Main theorem (`exists_powerSeries_root`).** Given a polynomial `P : R[X]` and `c : R` with

* `eval c P = 0`            (`c` is a root of the order-0 data),
* `IsUnit (eval c P')`      (the root is *simple*),

there exists `γ : R⟦X⟧` with `constantCoeff γ = c` and `aeval γ P = 0`.

Together with `aeval_root_unique` this gives the full abstract Hensel statement for `R⟦X⟧`:
a simple root `c` of `P` over `R` lifts **uniquely** to a root of `P` over `R⟦X⟧`.

**Route.** Mathlib provides *no* `HenselianLocalRing R⟦X⟧` instance and *no*
`IsAdicComplete (X) R⟦X⟧` instance (the two abstract routes through
`Mathlib/RingTheory/Henselian.lean`), and the `HenselianLocalRing` API would in any case
require `R` local, `P` monic, and only a *residue-field* root — strictly weaker and not our
setting. So we proceed **by explicit Newton construction**, which is also more general (no
locality, no monicity, exact root).

**Construction.** Let `A := eval c P'`, `u := Ring.inverse A` (so `A * u = 1`). Build the
partial-sum sequence `S : ℕ → R⟦X⟧` by ordinary structural recursion:

* `S 0      := C c`                                   (constant series `c`),
* `S (t+1)  := S t + monomial (t+1) (-u * coeff (t+1) (aeval (S t) P))`.

Adding the order-`(t+1)` monomial leaves all coefficients `≤ t` unchanged, so the diagonal
`g t := coeff t (S t)` is *stable*: `coeff j (S t) = g j` for all `j ≤ t`. Define
`γ := mk g`. Then `γ` agrees with `S t` below order `t+1`, and the Newton linearization
(`coeff_aeval_sub_at`, restated locally below) forces `coeff (t+1) (aeval γ P) = 0` order by
order, while the base order-0 coefficient is `eval c P = 0`. Hence `aeval γ P = 0`.

**Self-containment.** The supporting lemmas live in `NewtonLinearization.lean` /
`GammaSubstObstruction.lean`, but their `olean`s are not prebuilt in this worktree, so the
four facts actually consumed — the `aeval`-coefficient expansion, the truncation-propagation
lemma, the order-`t` Newton linearization, and the order-0 evaluation identity — are
**restated and reproven locally** here (with namespace `HenselExistence`), so this file
depends only on mathlib. The proofs are line-for-line the asset proofs.
-/

namespace ProximityPrize.HenselExistence

open PowerSeries

variable {R : Type*} [CommRing R]

/-! ## Locally restated linearization assets (see `NewtonLinearization.lean`) -/

/-- Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`:
`coeff n (aeval γ P) = ∑_{i ≤ deg P} P.coeff i · coeff n (γ^i)`. -/
theorem coeff_aeval_eq_sum_range (P : Polynomial R) (γ : R⟦X⟧) (n : ℕ) :
    coeff n (Polynomial.aeval γ P) =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * coeff n (γ ^ i) := by
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_smul, smul_eq_mul]

/-- Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation). -/
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

/-- Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization). -/
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

/-- Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response).
For `P : R[X]` and `γ₁ γ₂` agreeing below order `t` (`0 < t`), writing `c := constantCoeff γ₁`,
`coeff t (aeval γ₁ P) − coeff t (aeval γ₂ P) = eval c P' · (coeff t γ₁ − coeff t γ₂)`. -/
theorem coeff_aeval_sub_at (P : Polynomial R) {γ₁ γ₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    coeff t (Polynomial.aeval γ₁ P) - coeff t (Polynomial.aeval γ₂ P) =
      Polynomial.eval (constantCoeff γ₁) (Polynomial.derivative P) *
        (coeff t γ₁ - coeff t γ₂) := by
  set c := constantCoeff γ₁ with hc
  set δ := coeff t γ₁ - coeff t γ₂ with hδ
  rw [coeff_aeval_eq_sum_range, coeff_aeval_eq_sum_range, ← Finset.sum_sub_distrib]
  have hstep : ∀ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * coeff t (γ₁ ^ i) - P.coeff i * coeff t (γ₂ ^ i)
        = P.coeff i * i * c ^ (i - 1) * δ := by
    intro i _
    rw [← mul_sub]
    rcases i with _ | i
    · simp only [pow_zero, coeff_one, Nat.cast_zero, mul_zero, zero_mul]
      rw [if_neg (by omega), sub_zero, mul_zero]
    · rw [coeff_pow_sub_at ht h i, ← hc, ← hδ]
      rw [Nat.add_sub_cancel, nsmul_eq_mul]
      push_cast
      ring
  rw [Finset.sum_congr rfl hstep]
  rw [← Finset.sum_mul]
  congr 1
  rw [Polynomial.derivative_eval, Polynomial.sum_over_range' _ (by simp) (P.natDegree + 1)
        (Nat.lt_succ_self _)]

/-- Local copy of `GammaSubstObstruction.constantCoeff_aeval_powerSeries`:
`constantCoeff (aeval γ P) = eval (constantCoeff γ) P`. -/
theorem constantCoeff_aeval_powerSeries (P : Polynomial R) (γ : R⟦X⟧) :
    constantCoeff (Polynomial.aeval γ P) =
      Polynomial.eval (constantCoeff γ) P := by
  rw [Polynomial.aeval_eq_sum_range, map_sum, Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by
    rw [PowerSeries.constantCoeff_smul, map_pow, smul_eq_mul]

/-! ## The Newton partial-sum sequence and its diagonal -/

variable (P : Polynomial R) (c : R)

/-- The Newton partial-sum sequence. `S 0 := C c`, and at each step we add the order-`(t+1)`
correction monomial whose coefficient is `−u · coeff (t+1) (aeval (S t) P)`, where
`u = Ring.inverse (eval c P')`. Built by ordinary structural recursion. -/
noncomputable def S : ℕ → R⟦X⟧
  | 0 => PowerSeries.C c
  | (t + 1) =>
      S t + PowerSeries.monomial (t + 1)
        (-(Ring.inverse (Polynomial.eval c (Polynomial.derivative P)))
          * coeff (t + 1) (Polynomial.aeval (S t) P))

/-- Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged. -/
theorem coeff_S_succ_of_le {t j : ℕ} (hj : j ≤ t) :
    coeff j (S P c (t + 1)) = coeff j (S P c t) := by
  rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]

/-- The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t`
vanishes. (`S t` is `C c` plus correction monomials of orders `1, …, t`.) -/
theorem coeff_S_eq_zero_of_lt : ∀ {t j : ℕ}, t < j → coeff j (S P c t) = 0 := by
  intro t
  induction t with
  | zero => intro j hj; rw [S, coeff_C, if_neg (by omega)]
  | succ t ih =>
      intro j hj
      rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]
      exact ih (by omega)

/-- Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value
is reached at index `j` and never changes afterwards. -/
theorem coeff_S_stable : ∀ {t j : ℕ}, j ≤ t → coeff j (S P c t) = coeff j (S P c j) := by
  intro t
  induction t with
  | zero => intro j hj; rw [Nat.le_zero.mp hj]
  | succ t ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · rw [coeff_S_succ_of_le P c (Nat.lt_succ_iff.mp hlt), ih (Nat.lt_succ_iff.mp hlt)]
      · rw [heq]

/-- The Newton root: diagonalise the stable partial sums. -/
noncomputable def γ : R⟦X⟧ := PowerSeries.mk fun t => coeff t (S P c t)

@[simp] theorem coeff_γ (t : ℕ) : coeff t (γ P c) = coeff t (S P c t) := by
  rw [γ, coeff_mk]

/-- The constant coefficient of the Newton root is the prescribed root `c`. -/
@[simp] theorem constantCoeff_γ : constantCoeff (γ P c) = c := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_γ, S, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_C]

/-- `γ` agrees with the `t`-th partial sum below order `t + 1`. -/
theorem coeff_γ_eq_S {t j : ℕ} (hj : j ≤ t) : coeff j (γ P c) = coeff j (S P c t) := by
  rw [coeff_γ, ← coeff_S_stable P c hj]

/-! ## Order-by-order vanishing -/

variable (hc0 : Polynomial.eval c P = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative P)))

include hc0 in
/-- Order-0 coefficient of `aeval γ P` vanishes: it is `eval c P = 0`. -/
theorem coeff_zero_aeval_γ : coeff 0 (Polynomial.aeval (γ P c) P) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_aeval_powerSeries, constantCoeff_γ, hc0]

include hu in
/-- Order-`(t+1)` coefficient of `aeval γ P` vanishes, by the Newton linearization: γ agrees
with `S t` below order `t+1`, the `(t+1)`-coefficient of `S (t+1)` was *chosen* to cancel
`coeff (t+1) (aeval (S t) P)` after multiplication by `eval c P'`, and `eval c P'` is a unit. -/
theorem coeff_succ_aeval_γ (t : ℕ) : coeff (t + 1) (Polynomial.aeval (γ P c) P) = 0 := by
  set A := Polynomial.eval c (Polynomial.derivative P) with hA
  set u := Ring.inverse A with hudef
  set w := coeff (t + 1) (Polynomial.aeval (S P c t) P) with hw
  -- `A * u = 1` since `A` is a unit.
  have hAu : A * u = 1 := Ring.mul_inverse_cancel A hu
  -- γ and `S t` agree below order `t+1`.
  have hagree : ∀ j < t + 1, coeff j (γ P c) = coeff j (S P c t) := fun j hj =>
    coeff_γ_eq_S P c (Nat.lt_succ_iff.mp hj)
  -- Linearization at order `t+1` comparing γ against `S t`.
  have hlin := coeff_aeval_sub_at P (γ₁ := γ P c) (γ₂ := S P c t) (Nat.succ_pos t) hagree
  rw [constantCoeff_γ, ← hA] at hlin
  -- `coeff (t+1) (S t) = 0`: the partial sum `S t` has no order-`(t+1)` term.
  have hSt0 : coeff (t + 1) (S P c t) = 0 := coeff_S_eq_zero_of_lt P c (Nat.lt_succ_self t)
  -- `coeff (t+1) γ = -u * w`, the chosen Newton correction.
  have hγcoeff : coeff (t + 1) (γ P c) = -u * w := by
    rw [coeff_γ, S, map_add, coeff_monomial, if_pos rfl, hSt0, zero_add, ← hA, ← hudef, ← hw]
  -- Assemble the linearization: `coeff(t+1)(aeval γ P) - w = A * (-u*w - 0)`.
  rw [hγcoeff, hSt0, ← hw] at hlin
  -- The RHS simplifies: `A * (-u*w - 0) = -(A*u)*w = -w`.
  rw [show A * (-u * w - 0) = -(A * u) * w by ring, hAu, neg_one_mul] at hlin
  -- So `coeff(t+1)(aeval γ P) - w = -w`, hence the coefficient is `0`.
  have hgoal : coeff (t + 1) (Polynomial.aeval (γ P c) P) = w + (-w) := by
    rw [← hlin]; ring
  rw [hgoal, add_neg_cancel]

include hc0 hu in
/-- Every coefficient of `aeval γ P` vanishes, hence `aeval γ P = 0`. -/
theorem aeval_γ_eq_zero : Polynomial.aeval (γ P c) P = 0 := by
  ext t
  rw [map_zero]
  rcases t with _ | t
  · exact coeff_zero_aeval_γ P c hc0
  · exact coeff_succ_aeval_γ P c hu t

/-! ## Uniqueness from coefficient linearization -/

/-- **Power-series root uniqueness for `aeval`.** If two power-series roots of `P`
have the same constant coefficient `c`, and `P'` is a unit at `c`, then the two roots
are equal.

This is the uniqueness half matching `exists_powerSeries_root`, proved directly by
coefficient induction from `coeff_aeval_sub_at`: once the roots agree below order `t`,
the order-`t` coefficient difference is killed by multiplication with the unit
`eval c P'`. -/
theorem aeval_root_unique
    {P : Polynomial R} {γ₁ γ₂ : R⟦X⟧} {c : R}
    (hc₁ : constantCoeff γ₁ = c) (hc₂ : constantCoeff γ₂ = c)
    (hroot₁ : Polynomial.aeval γ₁ P = 0)
    (hroot₂ : Polynomial.aeval γ₂ P = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative P))) :
    γ₁ = γ₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | t
      · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hc₁, hc₂]
      · have hagree : ∀ j < t + 1, coeff j γ₁ = coeff j γ₂ := fun j hj =>
          ih j hj
        have hlin := coeff_aeval_sub_at P (γ₁ := γ₁) (γ₂ := γ₂)
          (t := t + 1) (Nat.succ_pos t) hagree
        rw [hc₁] at hlin
        have hmul :
            Polynomial.eval c (Polynomial.derivative P) *
              (coeff (t + 1) γ₁ - coeff (t + 1) γ₂) = 0 := by
          simpa [hroot₁, hroot₂] using hlin.symm
        rw [mul_comm] at hmul
        exact sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hu).1 hmul)

/-! ## Main existence theorem (abstract Hensel for `R⟦X⟧`, existence half) -/

variable {P c}

include hc0 hu in
/-- **Hensel-root existence for power series.** Given a polynomial `P : R[X]` over a
commutative ring `R` and `c : R` with `eval c P = 0` and `IsUnit (eval c P')`, there exists a
power series `γ : R⟦X⟧` lifting `c` (`constantCoeff γ = c`) with `aeval γ P = 0`.

Combined with `NewtonLinearization.aeval_root_unique` (uniqueness), this is the full abstract
Hensel statement for `R⟦X⟧`: a simple root of `P` over `R` lifts **uniquely** to a root over
`R⟦X⟧`. -/
theorem exists_powerSeries_root :
    ∃ γ : R⟦X⟧, constantCoeff γ = c ∧ Polynomial.aeval γ P = 0 :=
  ⟨γ P c, constantCoeff_γ P c, aeval_γ_eq_zero P c hc0 hu⟩

/-! ## Axiom audit (recorded 2026-06-05)

In-file `#print axioms` (run on a temp copy, then removed) confirmed that every declaration of
this file — the locally restated assets (`coeff_aeval_eq_sum_range`, `coeff_pow_sub_below`,
`coeff_pow_sub_at`, `coeff_aeval_sub_at`, `constantCoeff_aeval_powerSeries`), the Newton
construction (`S`, `coeff_S_succ_of_le`, `coeff_S_eq_zero_of_lt`, `coeff_S_stable`, `γ`,
`coeff_γ`, `constantCoeff_γ`, `coeff_γ_eq_S`), the order-by-order vanishing
(`coeff_zero_aeval_γ`, `coeff_succ_aeval_γ`, `aeval_γ_eq_zero`), and the flagship
`exists_powerSeries_root` — depends only on `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`, no `native_decide` / `Lean.ofReduceBool`. The file is sorry-free and `lake env lean`
exits 0. -/

end ProximityPrize.HenselExistence

-- Axiom audit: every claimed-done declaration rests only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ProximityPrize.HenselExistence.coeff_aeval_sub_at
#print axioms ProximityPrize.HenselExistence.aeval_γ_eq_zero
#print axioms ProximityPrize.HenselExistence.exists_powerSeries_root
#print axioms ProximityPrize.HenselExistence.aeval_root_unique
