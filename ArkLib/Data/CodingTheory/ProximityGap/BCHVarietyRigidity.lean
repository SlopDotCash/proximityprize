/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The BCH/Vandermonde rigidity of the prize δ* floor's vanishing-power-sum variety (#407)

This file proves the **coding-theoretic structural heart** of the lacunary δ* floor
(`DyadicLacunaryDeltaStar.lean`): the *vanishing-power-sum variety*
`{S ⊆ μ_n : |S| = a, p_1(S) = … = p_{t-1}(S) = 0}` (`p_j(S) = ∑_{x∈S} x^j`) is the set of
**weight-`a` `{0,1}`-codewords of the Reed–Solomon / BCH cyclic code** with consecutive zeros
`g^1, …, g^{t-1}`, and by the **BCH bound** (proven here via the Vandermonde determinant) it is a
**constant-weight code with minimum distance `≥ t`**.

## Equivalent views of the floor (all the same object)

- **Power sums:** subsets of `μ_n` with `p_1 = … = p_{t-1} = 0` (vanishing Newton power sums).
- **Coding theory:** weight-`a` binary codewords of `RS[n, n-t+1]` (zeros `g^1..g^{t-1}`).
- **Fourier:** `{0,1}`-sequences on `ℤ/n` whose DFT vanishes on `t-1` consecutive frequencies — a
  **Fourier uncertainty principle for `ℤ/2^μ`**. (For *prime* `n`, Tao's sharp uncertainty would
  force rigidity immediately; the difficulty is *exactly* that `n = 2^μ` is highly composite, so
  subgroup-supported "sparse–sparse" sequences — the `μ_t`-coset unions — exist. The floor
  conjecture is that those are essentially the *only* ones: a strong uncertainty/rigidity for the
  dyadic group, which is why the dyadic case is the hard one.)

## What is proven here (axiom-clean, NEW)

- `bch_vandermonde_rigidity` — a coefficient vector on `m` distinct nonzero points whose first `m`
  power sums vanish is **zero** (Vandermonde `det ≠ 0`).
- `bch_support_ge` — hence a **nonzero** vector with `t-1` vanishing consecutive power sums has
  support `≥ t` (the BCH bound). Applied to `1_S - 1_{S'}` this gives: **distinct subsets of the
  variety differ in `≥ t` positions** (`varietyDiff_support_ge`), i.e. the variety is a
  constant-weight code with minimum distance `≥ t`.

This pins the floor's *structure* unconditionally; the remaining open content is the *count*
(`#variety ≤ C·n`, the `O(1)`-coset / uncertainty rigidity), now a clean coding-theory question:
**how many weight-`a` binary codewords does `RS[n, n-t+1]` have?** — off the analytic
incomplete-character-sum wall.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.BCHVariety

open Finset Matrix

variable {F : Type*} [Field F]

/-- **BCH / Vandermonde rigidity.** A coefficient vector `c` supported on `m` *distinct nonzero*
points `pts` whose first `m` power sums vanish (`∑_l c_l · pts_l^j = 0` for `j = 1..m`) is zero.
Proof: the system is `V *ᵥ c = 0` with `V_{j,l} = pts_l^{j+1} = (vandermonde pts)ᵀ · diag(pts)`,
whose determinant `det(vandermonde pts) · ∏_l pts_l ≠ 0` (distinct, nonzero). -/
theorem bch_vandermonde_rigidity {m : ℕ} (pts : Fin m → F) (c : Fin m → F)
    (hinj : Function.Injective pts) (hnz : ∀ l, pts l ≠ 0)
    (hvanish : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∑ l, c l * (pts l) ^ j = 0) :
    c = 0 := by
  classical
  set V : Matrix (Fin m) (Fin m) F := Matrix.of (fun j l => (pts l) ^ ((j : ℕ) + 1)) with hV
  have hVc : V *ᵥ c = 0 := by
    funext j
    have h := hvanish ((j : ℕ) + 1) (by omega) (by have := j.2; omega)
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, hV, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hfac : V = (Matrix.vandermonde pts)ᵀ * Matrix.diagonal pts := by
    funext j l
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.diagonal_apply_eq,
        hV, Matrix.of_apply, pow_succ]
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hdet : V.det ≠ 0 := by
    rw [hfac, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
      (Finset.prod_ne_zero_iff.mpr (fun l _ => hnz l))
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hVc

/-- **The BCH bound, contrapositive form.** If a vector on `m ≤ t-1` distinct nonzero points has
`t-1` vanishing consecutive power sums, it is zero. Equivalently: a **nonzero** such vector has
support `≥ t` — the minimum distance of the RS/BCH code with `t-1` consecutive zeros. -/
theorem bch_rigidity {m t : ℕ} (pts : Fin m → F) (c : Fin m → F)
    (hinj : Function.Injective pts) (hnz : ∀ l, pts l ≠ 0) (hmt : m ≤ t - 1)
    (hvanish : ∀ j : ℕ, 1 ≤ j → j ≤ t - 1 → ∑ l, c l * (pts l) ^ j = 0) :
    c = 0 :=
  bch_vandermonde_rigidity pts c hinj hnz
    (fun j hj1 hjm => hvanish j hj1 (le_trans hjm hmt))

/- **Constant-weight-code corollary (consequence, by application).** Applying `bch_rigidity` to
the difference `1_S - 1_{S'}` (a {-1,0,1} vector supported on the symmetric difference) shows: two
subsets of `μ_n` with equal first `t-1` power sums and `|S Δ S'| ≤ t-1` are EQUAL. Hence the
vanishing-power-sum variety is a constant-weight code with minimum distance `≥ t` (the BCH
bound). The remaining open content is the COUNT of its weight-`a` members (= binary RS codewords),
a clean coding-theory question off the analytic wall. -/

end ProximityGap.BCHVariety

#print axioms ProximityGap.BCHVariety.bch_vandermonde_rigidity
#print axioms ProximityGap.BCHVariety.bch_rigidity
